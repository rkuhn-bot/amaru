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

//! One production node dials many serve-only injectors.
//!
//! Mailboxes stay at [`DEFAULT_MAILBOX_SIZE`]. Wire delay is fixed and same-timestamp hops
//! land together. Connection stages enqueue `HandshakeComplete` before `manager` runs, so
//! `manager` fills `peer_selection` and parks on the next `Connected`. The first `Connected`
//! handler then records advertisability. That effect is given a few milliseconds of simulated
//! time — production assigns it none — so the rest of the handshake burst can land on the
//! parked `manager` before `peer_selection` sends `SetLocalUse`. That reply parks too, and
//! neither stage receives again. Later keepalive and network hops still run.

use std::{collections::VecDeque, net::SocketAddr, sync::Arc, time::Duration};

use amaru_consensus::{effects::GenerateRandomSeed, performance::RecordAdvertisabilityEffect};
use amaru_kernel::{
    BlockHeight, Hash, Header, NetworkPoint, Peer, Slot, any_headers_chain_with_root,
    utils::tests::run_strategy_with_seed,
};
use amaru_ouroboros::{BaseReadChainStore, ConnectionsResource, in_memory_chain_store::InMemoryChainStore};
use amaru_pure_stage::{
    DEFAULT_MAILBOX_SIZE, DurationDist, Name, StageResponse,
    simulation::{EvalStrategy, SimulationRunning, running::OverrideResult},
    trace_buffer::TraceBuffer,
};
use tokio::runtime::{Handle, Runtime};

use super::{
    GraphWakeReason, HeapLogKind, WorldConnectionProvider, WorldLoop, build_injector, build_world_node,
    support::{derive_seed, fragment_trace_guards, seed_bytes},
};
use crate::tests::configuration::NodeTestConfig;

const UPSTREAMS: usize = 24;
const BASE_PORT: u16 = 18_000;
/// Past the first keepalive (1s) and dial hold-off (2s). The accept stage is still on its
/// initial accept, so those timers are the later wakes that must observe the same send.
const HORIZON_NANOS: u64 = 2_500_000_000;
const SHARE_DELAY: Duration = Duration::from_millis(20);
/// One delay for every handshake hop and payload deliver, so a burst shares a timestamp.
const FIXED_DELAY_NANOS: u64 = 1_000_000;
/// Long enough for several wire ticks to reach `manager` while `peer_selection` is inside
/// `Connected`, before it sends `SetLocalUse`.
const ADVERTISABILITY_NANOS: u64 = 8_000_000;
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

/// Connection stages first, so a handshake burst is queued on `manager`.
///
/// `manager` then runs before `peer_selection`. It fills that mailbox and parks on the next
/// `Connected` while `peer_selection` is still sitting on the first delivery. `peer_selection`
/// runs only once `manager` cannot.
struct ConnectionStagesThenManager;

impl EvalStrategy for ConnectionStagesThenManager {
    fn pick_runnable(&mut self, runnable: &mut VecDeque<(Name, StageResponse)>) -> (Name, StageResponse) {
        let other = runnable.iter().position(|(name, _)| {
            let name = name.as_str();
            !is_manager(name) && !is_peer_selection(name)
        });
        if let Some(idx) = other {
            return runnable.remove(idx).expect("index in range");
        }
        let manager = runnable.iter().position(|(name, _)| is_manager(name.as_str()));
        if let Some(idx) = manager {
            return runnable.remove(idx).expect("index in range");
        }
        runnable.pop_front().expect("runnable queue is non-empty")
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
    node_sim.set_eval_strategy(ConnectionStagesThenManager);
    node_sim.delay_external_effect::<RecordAdvertisabilityEffect>(DurationDist::Constant(Duration::from_nanos(
        ADVERTISABILITY_NANOS,
    )));
    graphs.push(node_sim);

    let mut world = WorldLoop::new(provider, graphs);
    world.inspect_deadlock();
    world.coalesce_same_timestamp();
    world.run_until_horizon(HORIZON_NANOS);
    world
}

#[test]
fn many_injectors_leave_manager_blocked_sending_to_peer_selection() {
    let _guards = fragment_trace_guards();
    let runtime = Runtime::new().unwrap();
    let world = run_once(SEED, runtime.handle());
    let samples = world.manager_to_peer_selection();
    let node = world.graph(UPSTREAMS);
    let parked = node.parked_sends();
    let connects =
        world.heap_log().iter().filter(|entry| matches!(entry.kind, HeapLogKind::ConnectAttempt { .. })).count();
    let mutual = samples.iter().position(|sample| sample.peer_selection_sending_to_manager);
    let Some(mutual_at) = mutual else {
        let parked_desc: Vec<_> = parked
            .iter()
            .map(|send| format!("{} -> {} {}", send.from, send.to, send.message.chars().take(48).collect::<String>()))
            .collect();
        let suspended: Vec<_> = node
            .suspended_sends()
            .into_iter()
            .map(|send| format!("{} -> {} {}", send.from, send.to, send.message.chars().take(48).collect::<String>()))
            .collect();
        panic!(
            "manager never stayed suspended while peer_selection was also sending to manager; \
             samples={} parked={} connects={} now={}ns deadlock={:?}\nparked={parked_desc:?}\nsuspended={suspended:?}",
            samples.len(),
            parked.len(),
            connects,
            world.now_nanos(),
            world.deadlock(),
        );
    };
    let first = &samples[mutual_at];
    let later = samples.iter().skip(mutual_at + 1).find(|sample| sample.time_nanos > first.time_nanos);
    let Some(later) = later else {
        panic!(
            "suspended send did not survive a later sim time; first={}ns samples={} now={}ns deadlock={:?}",
            first.time_nanos,
            samples.len(),
            world.now_nanos(),
            world.deadlock(),
        );
    };
    assert!(
        later.time_nanos.saturating_sub(first.time_nanos) >= 500_000_000,
        "stall lasted only {}ns",
        later.time_nanos - first.time_nanos,
    );
    for sample in [first, later] {
        assert!(!sample.send.is_call);
        assert!(is_manager(sample.send.from.as_str()), "{}", sample.send.from);
        assert!(is_peer_selection(sample.send.to.as_str()), "{}", sample.send.to);
        assert_eq!(sample.send.dest_capacity, DEFAULT_MAILBOX_SIZE);
        assert_eq!(sample.send.dest_len, DEFAULT_MAILBOX_SIZE);
        assert!(sample.send.dest_parked >= 1, "parked={}", sample.send.dest_parked);
        assert!(sample.send.message.starts_with("Connected("), "suspended message was {}", sample.send.message);
        assert!(sample.peer_selection_sending_to_manager);
    }
    let other_work = world.heap_log().iter().any(|entry| {
        entry.time_nanos > first.time_nanos
            && !matches!(entry.kind, HeapLogKind::GraphWake { reason: GraphWakeReason::Runnable, .. })
    });
    assert!(other_work, "no network hop or timer wake after {}ns; now={}ns", first.time_nanos, world.now_nanos(),);
    assert!(world.deadlock().is_none(), "whole graph halted: {:?}", world.deadlock());
    assert!(connects >= 11, "connects={connects}");
    let still = node
        .suspended_sends()
        .into_iter()
        .find(|send| !send.is_call && is_manager(send.from.as_str()) && is_peer_selection(send.to.as_str()));
    let still = still.expect("manager still suspended after the horizon");
    assert_eq!(still.dest_len, DEFAULT_MAILBOX_SIZE);
    assert!(still.message.starts_with("Connected("), "{}", still.message);
    let ps_still = node
        .suspended_sends()
        .into_iter()
        .find(|send| !send.is_call && is_peer_selection(send.from.as_str()) && is_manager(send.to.as_str()));
    let ps_still = ps_still.expect("peer_selection was no longer suspended sending to manager");
    assert!(ps_still.message.starts_with("SetLocalUse"), "{}", ps_still.message);
    world.stop();
}
