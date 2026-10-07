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
//! Mailboxes stay at [`DEFAULT_MAILBOX_SIZE`]. Every performance effect occupies a uniform
//! `[0, 1ms]` of simulated time. Wire delay is fixed and same-timestamp hops land together.
//!
//! `Connected`: `manager` runs before `peer_selection`. The dial loop's bookkeeping yields let
//! earlier handshakes complete while `peer_selection` is still sending `AddPeer`. `manager`
//! fills the mailbox and parks on `Connected`; the next `AddPeer` parks too.
//!
//! `Disconnected`: a longer hop lets that dial loop finish and each `Connected` drain. After dial
//! hold-off, one timestamp of `PeerDisconnect` closes most live connections together. `manager`
//! parks on `Disconnected` and the refill `AddPeer` parks on the way back. A later keepalive on
//! a connection the storm left up still runs.

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
    GraphWakeReason, HeapLogKind, WorldConnectionProvider, WorldLoop, build_injector, build_world_node,
    support::{derive_seed, fragment_trace_guards, seed_bytes},
};
use crate::tests::configuration::NodeTestConfig;

const UPSTREAMS: usize = 24;
const BASE_PORT: u16 = 18_000;
/// Past the first keepalive (1s) and dial hold-off (2s). The accept stage is still on its
/// initial accept, so those timers are the later wakes that must observe the same send.
const CONNECTED_HORIZON_NANOS: u64 = 2_500_000_000;
/// First keepalive is +1s, the next is +30s. The close storm is after dial hold-off (2s),
/// and that second keepalive is the later wake that must still see the send.
const DISCONNECT_HORIZON_NANOS: u64 = 35_000_000_000;
const SHARE_DELAY: Duration = Duration::from_millis(20);
/// Hop used by the `Connected` repro. Short enough that handshakes finish during the dial loop.
const CONNECTED_DELAY_NANOS: u64 = 1_000_000;
/// Hop used by the `Disconnected` repro. Longer than the dial loop, so each `Connected` is
/// drained before the next handshake, and the later close burst is the fill.
const DISCONNECT_DELAY_NANOS: u64 = 20_000_000;
const SEED: u64 = 0xA11CE;
/// After dial hold-off (2s), so `peer_selection` may dial again.
///
/// `manager` consumes about one mailbox (10) of `Disconnected` before it parks on the next.
/// The remainder has to leave `manager`'s own mailbox full, or the refill `AddPeer` is admitted
/// and `peer_selection` receives, which clears the park. 22 closes leave that remainder and
/// keep two connections up so their later keepalive still runs.
const DISCONNECT_AT: u64 = 3_000_000_000;
const DISCONNECT_COUNT: u32 = 22;

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

/// Connection stages first. `manager` and `peer_selection` swap order at `manager_first_at`.
///
/// Before that instant, `peer_selection` runs first and drains a single lifecycle message.
/// At and after it, `manager` runs first, fills the mailbox, and parks on the next send
/// while `peer_selection` has not received yet.
struct LifecycleOrder {
    provider: Arc<WorldConnectionProvider>,
    manager_first_at: u64,
}

impl EvalStrategy for LifecycleOrder {
    fn pick_runnable(&mut self, runnable: &mut VecDeque<(Name, StageResponse)>) -> (Name, StageResponse) {
        let other = runnable.iter().position(|(name, _)| {
            let name = name.as_str();
            !is_manager(name) && !is_peer_selection(name)
        });
        if let Some(idx) = other {
            return runnable.remove(idx).expect("index in range");
        }
        let manager_first = self.provider.current_time_nanos() >= self.manager_first_at;
        let preferred = if manager_first { is_manager } else { is_peer_selection };
        let pick = runnable.iter().position(|(name, _)| preferred(name.as_str()));
        if let Some(idx) = pick {
            return runnable.remove(idx).expect("index in range");
        }
        runnable.pop_front().expect("runnable queue is non-empty")
    }
}

fn stub_peer_selection_seed(sim: &mut SimulationRunning, seed: u64) {
    let bytes = seed_bytes(seed);
    sim.override_external_effect::<GenerateRandomSeed>(usize::MAX, move |_| OverrideResult::handled(bytes));
}

fn run_once(
    seed: u64,
    handle: &Handle,
    wire_delay_nanos: u64,
    manager_first_at: u64,
    disconnect_at: Option<u64>,
    horizon_nanos: u64,
) -> WorldLoop {
    let provider = Arc::new(WorldConnectionProvider::with_fixed_delay(seed, wire_delay_nanos));
    if let Some(at) = disconnect_at {
        provider.schedule_peer_disconnects(DISCONNECT_COUNT, at, at, None);
    }
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
    // Other world graphs collapse bookkeeping of at most 1ms. This repro needs those durations.
    node_sim.keep_external_durations();
    stub_peer_selection_seed(&mut node_sim, derive_seed(seed, 200));
    node_sim.set_eval_strategy(LifecycleOrder { provider: provider.clone(), manager_first_at });
    graphs.push(node_sim);

    let mut world = WorldLoop::new(provider, graphs);
    world.inspect_deadlock();
    world.coalesce_same_timestamp();
    world.run_until_horizon(horizon_nanos);
    world
}

fn describe_stuck(world: &WorldLoop) -> String {
    let node = world.graph(UPSTREAMS);
    let parked: Vec<_> = node
        .parked_sends()
        .iter()
        .map(|send| format!("{} -> {} {}", send.from, send.to, send.message.chars().take(64).collect::<String>()))
        .collect();
    let suspended: Vec<_> = node
        .suspended_sends()
        .into_iter()
        .map(|send| format!("{} -> {} {}", send.from, send.to, send.message.chars().take(64).collect::<String>()))
        .collect();
    let connects =
        world.heap_log().iter().filter(|entry| matches!(entry.kind, HeapLogKind::ConnectAttempt { .. })).count();
    let disconnects = world.heap_log().iter().filter(|entry| matches!(entry.kind, HeapLogKind::PeerDisconnect)).count();
    format!(
        "samples={} parked={} connects={connects} disconnects={disconnects} now={}ns deadlock={:?}\nparked={parked:?}\nsuspended={suspended:?}",
        world.manager_to_peer_selection().len(),
        node.parked_sends().len(),
        world.now_nanos(),
        world.deadlock(),
    )
}

/// `manager` stayed parked on a send to `peer_selection` across later sim time, while
/// `peer_selection` was also parked sending to `manager`, and other heap work still ran.
fn assert_mutual_park(world: &WorldLoop, manager_prefix: &str) {
    let samples = world.manager_to_peer_selection();
    let mutual = samples.iter().position(|sample| sample.peer_selection_sending_to_manager);
    let Some(mutual_at) = mutual else {
        let times: Vec<_> = samples
            .iter()
            .map(|sample| {
                format!(
                    "{}ns len={} parked={} {}",
                    sample.time_nanos,
                    sample.send.dest_len,
                    sample.send.dest_parked,
                    sample.send.message.chars().take(24).collect::<String>(),
                )
            })
            .collect();
        panic!(
            "manager never stayed suspended while peer_selection was also sending to manager; times={times:?} {}",
            describe_stuck(world)
        );
    };
    let first = &samples[mutual_at];
    let later = samples
        .iter()
        .skip(mutual_at + 1)
        .filter(|sample| sample.peer_selection_sending_to_manager)
        .find(|sample| sample.time_nanos.saturating_sub(first.time_nanos) >= 500_000_000);
    let Some(later) = later else {
        let times: Vec<_> = samples
            .iter()
            .skip(mutual_at)
            .map(|sample| {
                format!(
                    "{}ns mutual={} {}",
                    sample.time_nanos,
                    sample.peer_selection_sending_to_manager,
                    sample.send.message.chars().take(48).collect::<String>(),
                )
            })
            .collect();
        panic!(
            "suspended send did not stay mutual across 500ms; first={}ns times={times:?} {}",
            first.time_nanos,
            describe_stuck(world)
        );
    };
    for sample in [first, later] {
        assert!(!sample.send.is_call);
        assert!(is_manager(sample.send.from.as_str()), "{}", sample.send.from);
        assert!(is_peer_selection(sample.send.to.as_str()), "{}", sample.send.to);
        assert_eq!(sample.send.dest_capacity, DEFAULT_MAILBOX_SIZE);
        assert_eq!(sample.send.dest_len, DEFAULT_MAILBOX_SIZE);
        assert!(sample.send.dest_parked >= 1, "parked={}", sample.send.dest_parked);
        assert!(
            sample.send.message.starts_with(manager_prefix),
            "suspended message was {}",
            sample.send.message.chars().take(80).collect::<String>(),
        );
        assert!(sample.peer_selection_sending_to_manager);
    }
    let other_work = world.heap_log().iter().any(|entry| {
        entry.time_nanos > first.time_nanos
            && !matches!(entry.kind, HeapLogKind::GraphWake { reason: GraphWakeReason::Runnable, .. })
    });
    assert!(other_work, "no network hop or timer wake after {}ns; {}", first.time_nanos, describe_stuck(world));
    assert!(world.deadlock().is_none(), "whole graph halted: {:?}", world.deadlock());
    let node = world.graph(UPSTREAMS);
    let still = node
        .suspended_sends()
        .into_iter()
        .find(|send| !send.is_call && is_manager(send.from.as_str()) && is_peer_selection(send.to.as_str()));
    let still = still.expect("manager still suspended after the horizon");
    assert_eq!(still.dest_len, DEFAULT_MAILBOX_SIZE);
    assert!(still.message.starts_with(manager_prefix), "{}", still.message.chars().take(80).collect::<String>());
    let ps_still = node.suspended_sends().into_iter().any(|send| {
        !send.is_call
            && is_peer_selection(send.from.as_str())
            && is_manager(send.to.as_str())
            && !send.message.is_empty()
    });
    assert!(ps_still, "peer_selection was no longer suspended sending to manager");
}

#[test]
fn many_injectors_leave_manager_blocked_sending_to_peer_selection() {
    let _guards = fragment_trace_guards();
    let runtime = Runtime::new().unwrap();
    let world = run_once(SEED, runtime.handle(), CONNECTED_DELAY_NANOS, 0, None, CONNECTED_HORIZON_NANOS);
    let connects =
        world.heap_log().iter().filter(|entry| matches!(entry.kind, HeapLogKind::ConnectAttempt { .. })).count();
    assert_mutual_park(&world, "Connected(");
    assert!(connects >= 11, "connects={connects}");
    let node = world.graph(UPSTREAMS);
    let ps_still = node
        .suspended_sends()
        .into_iter()
        .find(|send| !send.is_call && is_peer_selection(send.from.as_str()) && is_manager(send.to.as_str()))
        .expect("peer_selection suspended");
    assert!(ps_still.message.starts_with("AddPeer("), "{}", ps_still.message.chars().take(80).collect::<String>());
    world.stop();
}

#[test]
fn many_injectors_leave_manager_blocked_sending_disconnected() {
    let _guards = fragment_trace_guards();
    let runtime = Runtime::new().unwrap();
    // Drain each Connected before the storm. At `DISCONNECT_AT` (after dial hold-off) manager
    // runs first, so the same-timestamp closes fill peer_selection and park on Disconnected.
    let world = run_once(
        SEED,
        runtime.handle(),
        DISCONNECT_DELAY_NANOS,
        DISCONNECT_AT,
        Some(DISCONNECT_AT),
        DISCONNECT_HORIZON_NANOS,
    );
    let disconnects = world.heap_log().iter().filter(|entry| matches!(entry.kind, HeapLogKind::PeerDisconnect)).count();
    assert!(disconnects >= 11, "disconnects={disconnects} {}", describe_stuck(&world));
    assert_mutual_park(&world, "Disconnected(");
    let node = world.graph(UPSTREAMS);
    let ps_still = node
        .suspended_sends()
        .into_iter()
        .find(|send| !send.is_call && is_peer_selection(send.from.as_str()) && is_manager(send.to.as_str()))
        .expect("peer_selection suspended");
    assert!(ps_still.message.starts_with("AddPeer("), "{}", ps_still.message.chars().take(80).collect::<String>());
    world.stop();
}
