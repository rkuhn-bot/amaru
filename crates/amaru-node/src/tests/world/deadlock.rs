// Copyright 2026 PRAGMA
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Same stimulus as the pre-#1475 repro: one node, many injector upstreams, mailboxes of
//! [`DEFAULT_MAILBOX_SIZE`], fixed wire delay, same-timestamp hops.
//!
//! The manager no longer sends lifecycle to peer selection, so that send cannot stay
//! suspended. The run finishes inside the horizon and dials the upstreams.

use std::{collections::VecDeque, net::SocketAddr, sync::Arc, time::Duration};

use amaru_consensus::effects::GenerateRandomSeed;
use amaru_kernel::{
    BlockHeight, Hash, Header, NetworkPoint, Peer, Slot, any_headers_chain_with_root,
    utils::tests::run_strategy_with_seed,
};
use amaru_ouroboros::{BaseReadChainStore, ConnectionsResource, in_memory_chain_store::InMemoryChainStore};
use amaru_pure_stage::{
    DEFAULT_MAILBOX_SIZE, Name, StageResponse,
    simulation::{EvalStrategy, SimulationRunning, running::OverrideResult},
    trace_buffer::TraceBuffer,
};
use tokio::runtime::{Handle, Runtime};

use super::{
    WorldConnectionProvider, WorldLoop, build_injector, build_world_node,
    support::{derive_seed, fragment_trace_guards, seed_bytes},
};
use crate::tests::configuration::NodeTestConfig;

const UPSTREAMS: usize = 24;
const BASE_PORT: u16 = 18_000;
/// Far enough past the handshake burst for the suspended send to be sampled twice.
const HORIZON_NANOS: u64 = 15_000_000;
const SHARE_DELAY: Duration = Duration::from_millis(20);
/// One delay for every handshake hop and payload deliver, so a burst shares a timestamp.
const FIXED_DELAY_NANOS: u64 = 1_000_000;
const SEED: u64 = 0xA11CE;

fn is_manager(name: &str) -> bool {
    name == "manager" || name.starts_with("manager-")
}

fn is_peer_selection(name: &str) -> bool {
    name == "peer_selection" || name.starts_with("peer_selection-")
}

fn loopback(port: u16) -> SocketAddr {
    SocketAddr::from(([127, 0, 0, 1], port))
}

fn peer_at(addr: SocketAddr) -> Peer {
    Peer::try_from(addr).expect("world tests use IPv4 loopback")
}

fn one_header(seed: u64) -> Header {
    let root = NetworkPoint::Specific(Slot::from(68_774_400), Hash::new([0u8; 32]));
    let headers = run_strategy_with_seed(seed, any_headers_chain_with_root(1, root.with_height(BlockHeight::from(0))));
    headers.into_iter().next().expect("one header")
}

/// Let connection stages enqueue lifecycle messages before either endpoint runs.
///
/// `manager` then fills `peer_selection`'s mailbox and blocks on the next send.
/// `peer_selection` runs only once nothing else is runnable, which is the moment
/// it tries to answer and blocks on the same `manager`.
struct DeferManagerAndPeerSelection;

impl EvalStrategy for DeferManagerAndPeerSelection {
    fn pick_runnable(&mut self, runnable: &mut VecDeque<(Name, StageResponse)>) -> (Name, StageResponse) {
        let other = runnable.iter().position(|(name, _)| {
            let name = name.as_str();
            !is_manager(name) && !is_peer_selection(name)
        });
        let idx = if let Some(idx) = other {
            idx
        } else {
            runnable.iter().position(|(name, _)| !is_peer_selection(name.as_str())).unwrap_or(0)
        };
        runnable.remove(idx).expect("runnable queue is non-empty")
    }
}

fn stub_peer_selection_seed(sim: &mut SimulationRunning, seed: u64) {
    let bytes = seed_bytes(seed);
    sim.override_external_effect::<GenerateRandomSeed>(usize::MAX, move |_| OverrideResult::handled(bytes));
}

fn run_once(seed: u64, handle: &Handle) -> WorldLoop {
    let provider = Arc::new(WorldConnectionProvider::with_fixed_delay(seed, FIXED_DELAY_NANOS));
    let connections: ConnectionsResource = provider.clone();
    let header = one_header(seed);
    let store = Arc::new(InMemoryChainStore::new());
    let source: Arc<dyn BaseReadChainStore> = store;

    let mut graphs = Vec::with_capacity(UPSTREAMS + 1);
    let mut peers = Vec::with_capacity(UPSTREAMS);
    for i in 0..UPSTREAMS {
        let listen = loopback(BASE_PORT + i as u16);
        peers.push(peer_at(listen));
        let (sim, _shared) =
            build_injector(source.clone(), connections.clone(), listen, derive_seed(seed, 100 + i as u64), handle)
                .expect("injector");
        graphs.push(sim);
    }

    let node_addr = loopback(BASE_PORT + 500);
    let node = NodeTestConfig::default()
        .with_listen_address(&node_addr.to_string())
        .with_seed(derive_seed(seed, 1))
        .with_upstream_peers(peers)
        .with_target_upstream_peers(UPSTREAMS)
        .with_mailbox_size(DEFAULT_MAILBOX_SIZE)
        .with_peer_bulk_mailbox(DEFAULT_MAILBOX_SIZE)
        .with_share_request_initial_delay(SHARE_DELAY)
        .with_trace_buffer(TraceBuffer::new_shared(4_000, 2_000_000))
        .with_validated_blocks(vec![header]);
    let mut node_sim = build_world_node(&node, connections, handle).expect("node");
    stub_peer_selection_seed(&mut node_sim, derive_seed(seed, 200));
    node_sim.set_eval_strategy(DeferManagerAndPeerSelection);
    node_sim.stop_after_parked_send(|from, to| is_manager(from.as_str()) && is_peer_selection(to.as_str()));
    graphs.push(node_sim);

    let mut world = WorldLoop::new(provider, graphs);
    world.inspect_deadlock();
    world.coalesce_same_timestamp();
    world.keep_manager_send_suspended();
    world.run_until_horizon(HORIZON_NANOS);
    world
}

#[test]
fn many_injectors_do_not_leave_manager_blocked_sending_to_peer_selection() {
    let _guards = fragment_trace_guards();
    let runtime = Runtime::new().unwrap();
    let world = run_once(SEED, runtime.handle());
    let samples = world.manager_to_peer_selection();
    assert!(
        !world.manager_send_to_peer_selection_stuck(),
        "manager stayed suspended sending to peer_selection: {}",
        samples.first().map(|sample| sample.send.message.as_str()).unwrap_or(""),
    );
    assert!(samples.is_empty(), "unexpected manager send samples: {}", samples.len());
    let node = world.graph(UPSTREAMS);
    let still = node
        .suspended_sends()
        .into_iter()
        .any(|send| !send.is_call && is_manager(send.from.as_str()) && is_peer_selection(send.to.as_str()));
    assert!(!still, "manager still suspended on a send to peer_selection");
    let connects = world
        .heap_log_ref()
        .iter()
        .filter(|entry| matches!(entry.kind, super::HeapLogKind::ConnectAttempt { .. }))
        .count();
    assert!(connects >= UPSTREAMS, "expected the upstreams to be dialed, connects={connects}");
    assert!(world.deadlock().is_none(), "graph deadlock: {:?}", world.deadlock());
    // A suspended manager→peer-selection send is re-armed every millisecond until the
    // horizon. Quiescence before that means the send never parked.
    assert!(world.now_nanos() < HORIZON_NANOS, "run was still scheduled at the horizon ({}ns)", world.now_nanos(),);
    world.stop();
}
