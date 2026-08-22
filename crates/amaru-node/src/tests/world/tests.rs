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

use std::{net::SocketAddr, num::NonZeroUsize, sync::Arc, time::Duration};

use amaru_kernel::{
    BlockHeight, Hash, NetworkPoint, NonEmptyBytes, PREPROD_ERA_HISTORY, PREPROD_GLOBAL_PARAMETERS, Peer, Slot,
    any_headers_chain_with_root, utils::tests::run_strategy,
};
use amaru_ouroboros::{ConnectionId, ConnectionsResource};
use amaru_protocols::{
    network_effects::{
        AcceptEffect, AcceptError, ConnectEffect, ConnectError, ListenEffect, ListenError, Network, NetworkOps,
        ReceiveError, RecvEffect, SendEffect, SendError,
    },
    store_effects::ResourceParameters,
};
use amaru_pure_stage::{
    Effect, Instant, Name, StageGraph, StageResponse, TraceMatch, assert_trace_match_filter,
    register_data_deserializer, register_effect_deserializer,
    simulation::{Fifo, SimulationBuilder},
    tm_clock, tm_effect, tm_external_effect_any, tm_input, tm_resume_external, tm_resume_unit, tm_state,
    trace_buffer::{TraceBuffer, TraceEntry},
};
use parking_lot::Mutex;
use tokio_util::bytes::Bytes;

use super::{
    GraphWakeReason, HONEST_PAYLOAD_DELAY_MAX_NANOS, HONEST_PAYLOAD_DELAY_SLOTS, HeapLogEntry, HeapLogKind,
    LONG_TAIL_PAYLOAD_MIN_NANOS, NetworkEvent, WIRE_DELAY_MAX_NANOS, WIRE_DELAY_MIN_NANOS, WorldConnectionProvider,
    WorldLoop, build_world_node, long_tail_payload_delay_nanos, payload_delay_nanos, wire_delay_nanos,
};
use crate::tests::configuration::NodeTestConfig;

const SEED: u64 = 0xA11CE;

type Observed<T> = Arc<Mutex<Option<T>>>;

fn observed<T>() -> Observed<T> {
    Arc::new(Mutex::new(None))
}

fn set_observed<T>(slot: &Observed<T>, value: T) {
    *slot.lock() = Some(value);
}

fn provider() -> Arc<WorldConnectionProvider> {
    Arc::new(WorldConnectionProvider::new(SEED))
}

fn by_time_seq(mut log: Vec<HeapLogEntry>) -> Vec<HeapLogEntry> {
    log.sort_by_key(|e| (e.time_nanos, e.sequence));
    log
}

fn assert_heap_log(actual: Vec<HeapLogEntry>, expected: Vec<HeapLogEntry>) {
    assert_eq!(by_time_seq(actual), by_time_seq(expected));
}

fn graph_wake(sequence: u64, time_nanos: u64, graph: usize, reason: GraphWakeReason) -> HeapLogEntry {
    HeapLogEntry { sequence, time_nanos, kind: HeapLogKind::GraphWake { graph, reason } }
}

fn pair_ids() -> (ConnectionId, ConnectionId) {
    let mut ids = ConnectionId::initial();
    (ids.get_and_increment(), ids.get_and_increment())
}

fn initiator_addr(initiator: ConnectionId) -> SocketAddr {
    SocketAddr::from(([127, 0, 0, 1], 5000 + initiator.as_u64() as u16))
}

/// Prove one Deliver round-trip under the world loop.
/// Node A listens+accepts+recv, Node B connects+sends. Driven only by WorldLoop.
fn trace_guards() -> amaru_pure_stage::DeserializerGuards {
    let mut guards = amaru_protocols::network_effects::register_deserializers();
    guards.push(register_data_deserializer::<()>().boxed());
    guards.push(register_data_deserializer::<Result<SocketAddr, ListenError>>().boxed());
    guards.push(register_data_deserializer::<Result<ConnectionId, ConnectError>>().boxed());
    guards.push(register_data_deserializer::<Result<(Peer, ConnectionId), AcceptError>>().boxed());
    guards.push(register_data_deserializer::<Result<(), SendError>>().boxed());
    guards.push(register_data_deserializer::<Result<NonEmptyBytes, ReceiveError>>().boxed());
    guards.push(register_effect_deserializer::<ListenEffect>().boxed());
    guards.push(register_effect_deserializer::<AcceptEffect>().boxed());
    guards.push(register_effect_deserializer::<ConnectEffect>().boxed());
    guards.push(register_effect_deserializer::<SendEffect>().boxed());
    guards.push(register_effect_deserializer::<RecvEffect>().boxed());
    guards
}

/// Hydrate production-graph traces as typed chainsync / header-validation values.
fn fragment_trace_guards() -> amaru_pure_stage::DeserializerGuards {
    let mut guards = amaru_protocols::deserializers::register_deserializers();
    guards.push(register_data_deserializer::<amaru_consensus::stages::track_peers::TrackPeersMsg>().boxed());
    guards.push(register_data_deserializer::<amaru_protocols::chainsync::ChainSyncInitiatorMsg>().boxed());
    guards.push(register_effect_deserializer::<amaru_consensus::effects::ValidateHeaderEffect>().boxed());
    guards
}

#[tokio::test]
async fn test_one_deliver_roundtrip_with_world_loop() {
    let _guards = trace_guards();
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let trace = TraceBuffer::new_shared(100, 1_000_000);
    let listener_addr: SocketAddr = "127.0.0.1:9000".parse().unwrap();
    let received = observed::<Vec<u8>>();
    let received_a = received.clone();

    let mut stage_graph_a = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    stage_graph_a.resources().put::<ConnectionsResource>(provider.clone());

    let stage_a = stage_graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let received_a = received_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let msg_len = NonZeroUsize::new("hello from B".len()).unwrap();
            let bytes = net.recv(conn, msg_len).await.unwrap();
            set_observed(&received_a, bytes.as_ref().to_vec());
        }
    });
    let stage_a = stage_graph_a.wire_up(stage_a, ());
    let mut sim_a = stage_graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut stage_graph_b = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    stage_graph_b.resources().put::<ConnectionsResource>(provider.clone());

    let stage_b = stage_graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        let msg = NonEmptyBytes::try_from(Bytes::from("hello from B")).unwrap();
        net.send(conn, msg).await.unwrap();
    });
    let stage_b = stage_graph_b.wire_up(stage_b, ());
    let mut sim_b = stage_graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();

    assert_eq!(received.lock().as_deref(), Some(b"hello from B".as_ref()));

    let (initiator, responder) = pair_ids();
    let initiator_sock = initiator_addr(initiator);
    let d_connected = wire_delay_nanos(SEED, 0);
    let d_accepted = wire_delay_nanos(SEED, 1);
    let d_deliver = wire_delay_nanos(SEED, 2);
    let t_connected = d_connected;
    let t_accepted = t_connected + d_accepted;
    let t_deliver = t_connected + d_deliver;
    let msg = NonEmptyBytes::try_from(Bytes::from("hello from B")).unwrap();
    let mut expected_log = vec![
        graph_wake(0, 0, 0, GraphWakeReason::Runnable),
        graph_wake(1, 0, 1, GraphWakeReason::Runnable),
        HeapLogEntry {
            sequence: 2,
            time_nanos: t_connected,
            kind: HeapLogKind::ConnectAttempt { target: listener_addr },
        },
        graph_wake(4, t_connected, 1, GraphWakeReason::Runnable),
        HeapLogEntry { sequence: 5, time_nanos: t_connected, kind: HeapLogKind::SendAck { conn: initiator } },
        graph_wake(7, t_connected, 1, GraphWakeReason::Runnable),
        HeapLogEntry {
            sequence: 3,
            time_nanos: t_accepted,
            kind: HeapLogKind::Accepted {
                listener: listener_addr,
                responder_conn: responder,
                initiator_addr: initiator_sock,
            },
        },
        graph_wake(8, t_accepted, 0, GraphWakeReason::Runnable),
        HeapLogEntry {
            sequence: 6,
            time_nanos: t_deliver,
            kind: HeapLogKind::Deliver { conn: responder, data_len: 12 },
        },
    ];
    if t_deliver > t_accepted {
        expected_log.push(graph_wake(9, t_deliver, 0, GraphWakeReason::Runnable));
    }
    assert_heap_log(world.take_heap_log(), expected_log);

    let mut expected = Vec::new();
    expected.extend([
        tm_state("node_a-1", &()),
        tm_state("node_b-1", &()),
        tm_input("node_a-1", &()),
        tm_input("node_b-1", &()),
        tm_resume_unit("node_a-1"),
        tm_effect("node_a-1", ListenEffect { addr: listener_addr }),
        tm_resume_external("node_a-1", Ok::<SocketAddr, ListenError>(listener_addr)),
        tm_effect("node_a-1", AcceptEffect { listener_addr }),
        tm_resume_unit("node_b-1"),
        tm_effect("node_b-1", ConnectEffect { addr: listener_addr.into(), timeout: Duration::from_secs(1) }),
        tm_clock(Duration::from_nanos(t_connected)),
        tm_resume_external("node_b-1", Ok::<ConnectionId, ConnectError>(initiator)),
        tm_effect("node_b-1", SendEffect { conn: initiator, data: msg.clone() }),
        tm_resume_external("node_b-1", Ok::<(), SendError>(())),
        tm_state("node_b-1", &()),
    ]);
    if t_accepted <= t_deliver {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(12).unwrap() }),
        ]);
        if t_deliver > t_accepted {
            expected.extend([tm_clock(Duration::from_nanos(t_deliver))]);
        }
        expected.extend([
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    } else {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(12).unwrap() }),
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    }
    assert_trace_match_filter(world.graph(0), &expected, &[]);
}

/// Horizon cuts keepalive.
///
/// Schedule two explicit heap events:
/// - keepalive at t_in=100 (≤ H=1000)
/// - another at t_out=1500 (> H=1000)
///
/// After run_until_horizon(H=1000):
/// - t_in=100 event is in heap_log
/// - peek_next_event_time() returns Some(1500) (still on heap)
#[tokio::test]
async fn test_horizon_cuts_keepalive() {
    let provider = provider();

    let conn_in = ConnectionId::initial();
    provider.schedule_event_at(100, NetworkEvent::Close { conn: conn_in });

    let conn_out = ConnectionId::initial();
    provider.schedule_event_at(1500, NetworkEvent::Close { conn: conn_out });

    let mut world = WorldLoop::new(provider, vec![]);
    world.run_until_horizon(1000);

    assert_heap_log(
        world.take_heap_log(),
        vec![HeapLogEntry { sequence: 0, time_nanos: 100, kind: HeapLogKind::Close { conn: conn_in } }],
    );
    assert_eq!(world.peek_next_event_time(), Some(1500), "Event at t=1500 should still be on heap (not popped)");
}

/// Connected completes the pending connect for that listener, not a process-wide FIFO.
#[tokio::test]
async fn test_pending_connect_matches_listener() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let addr1: SocketAddr = "127.0.0.1:9101".parse().unwrap();
    let addr2: SocketAddr = "127.0.0.1:9102".parse().unwrap();
    let got1 = observed::<Vec<u8>>();
    let got2 = observed::<Vec<u8>>();
    let g1 = got1.clone();
    let g2 = got2.clone();

    let listen = |name: &'static str, addr: SocketAddr, slot: Observed<Vec<u8>>| {
        let provider = provider.clone();
        let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo);
        graph.resources().put::<ConnectionsResource>(provider);
        let stage = graph.stage(name, move |_state: (), _unit: (), eff| {
            let slot = slot.clone();
            async move {
                let net = Network::new(&eff);
                net.listen(addr).await.unwrap();
                let (_peer, conn) = net.accept(addr).await.unwrap();
                let bytes = net.recv(conn, NonZeroUsize::new(3).unwrap()).await.unwrap();
                set_observed(&slot, bytes.as_ref().to_vec());
            }
        });
        let stage = graph.wire_up(stage, ());
        let mut sim = graph.run(&handle);
        sim.enqueue_msg(&stage, [()]);
        sim
    };
    let connect = |name: &'static str, addr: SocketAddr, payload: &'static [u8]| {
        let provider = provider.clone();
        let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo);
        graph.resources().put::<ConnectionsResource>(provider);
        let stage = graph.stage(name, move |_state: (), _unit: (), eff| async move {
            let net = Network::new(&eff);
            let conn = net.connect(addr.into(), Duration::from_secs(1)).await.unwrap();
            net.send(conn, NonEmptyBytes::try_from(Bytes::from(payload)).unwrap()).await.unwrap();
        });
        let stage = graph.wire_up(stage, ());
        let mut sim = graph.run(&handle);
        sim.enqueue_msg(&stage, [()]);
        sim
    };

    let mut world = WorldLoop::new(
        provider.clone(),
        vec![
            connect("c1", addr1, b"one"),
            connect("c2", addr2, b"two"),
            listen("l1", addr1, g1),
            listen("l2", addr2, g2),
        ],
    );
    world.run_to_completion();
    assert_eq!(got1.lock().as_deref(), Some(b"one".as_ref()));
    assert_eq!(got2.lock().as_deref(), Some(b"two".as_ref()));
}

/// Connect is a wire hop: listen after send but before SYN arrival still succeeds.
#[tokio::test]
async fn test_listen_before_connect_attempt_arrives() {
    let _guards = trace_guards();
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let trace = TraceBuffer::new_shared(100, 1_000_000);
    let listener_addr: SocketAddr = "127.0.0.1:9110".parse().unwrap();
    let received = observed::<Vec<u8>>();
    let received_a = received.clone();

    let mut graph_b = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        net.send(conn, NonEmptyBytes::try_from(Bytes::from("ok")).unwrap()).await.unwrap();
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut graph_a = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let received_a = received_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let bytes = net.recv(conn, NonZeroUsize::new(2).unwrap()).await.unwrap();
            set_observed(&received_a, bytes.as_ref().to_vec());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_b, sim_a]);
    world.run_to_completion();
    assert_eq!(received.lock().as_deref(), Some(b"ok".as_ref()));

    let (initiator, responder) = pair_ids();
    let initiator_sock = initiator_addr(initiator);
    let t_attempt = wire_delay_nanos(SEED, 0);
    let t_accepted = t_attempt + wire_delay_nanos(SEED, 1);
    let t_deliver = t_attempt + wire_delay_nanos(SEED, 2);
    assert!((WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(&t_attempt));
    let log = by_time_seq(world.take_heap_log());
    let attempt = log
        .iter()
        .find(|e| e.kind == HeapLogKind::ConnectAttempt { target: listener_addr })
        .expect("ConnectAttempt on the unified heap");
    assert_eq!(attempt.time_nanos, t_attempt);
    assert!(log.iter().any(|e| e.kind == HeapLogKind::SendAck { conn: initiator }));
    assert!(log.iter().any(|e| matches!(e.kind, HeapLogKind::GraphWake { .. })));

    let msg = NonEmptyBytes::try_from(Bytes::from("ok")).unwrap();
    let mut expected = Vec::new();
    expected.extend([
        tm_state("node_b-1", &()),
        tm_state("node_a-1", &()),
        tm_input("node_b-1", &()),
        tm_input("node_a-1", &()),
        tm_resume_unit("node_b-1"),
        tm_effect("node_b-1", ConnectEffect { addr: listener_addr.into(), timeout: Duration::from_secs(1) }),
        tm_resume_unit("node_a-1"),
        tm_effect("node_a-1", ListenEffect { addr: listener_addr }),
        tm_resume_external("node_a-1", Ok::<SocketAddr, ListenError>(listener_addr)),
        tm_effect("node_a-1", AcceptEffect { listener_addr }),
        tm_clock(Duration::from_nanos(t_attempt)),
        tm_resume_external("node_b-1", Ok::<ConnectionId, ConnectError>(initiator)),
        tm_effect("node_b-1", SendEffect { conn: initiator, data: msg.clone() }),
        tm_resume_external("node_b-1", Ok::<(), SendError>(())),
        tm_state("node_b-1", &()),
    ]);
    if t_accepted <= t_deliver {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(2).unwrap() }),
        ]);
        if t_deliver > t_accepted {
            expected.extend([tm_clock(Duration::from_nanos(t_deliver))]);
        }
        expected.extend([
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    } else {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(2).unwrap() }),
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    }
    assert_trace_match_filter(world.graph(0), &expected, &[]);
}

/// Connect completes and the initiator sends before accept; bytes must still arrive.
#[tokio::test]
async fn test_send_before_accept_delivers() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9200".parse().unwrap();
    let received = observed::<Vec<u8>>();
    let received_a = received.clone();

    let mut graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let received_a = received_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            eff.wait(Duration::from_nanos(10_000_000)).await;
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let bytes = net.recv(conn, NonZeroUsize::new(4).unwrap()).await.unwrap();
            set_observed(&received_a, bytes.as_ref().to_vec());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        net.send(conn, NonEmptyBytes::try_from(Bytes::from("ping")).unwrap()).await.unwrap();
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();
    assert_eq!(received.lock().as_deref(), Some(b"ping".as_ref()));

    let (initiator, responder) = pair_ids();
    let initiator_addr = initiator_addr(initiator);
    let d_connected = wire_delay_nanos(SEED, 0);
    let d_deliver = wire_delay_nanos(SEED, 1);
    let d_accepted = wire_delay_nanos(SEED, 2);
    assert_heap_log(
        world.take_heap_log(),
        vec![
            graph_wake(0, 0, 0, GraphWakeReason::Runnable),
            graph_wake(1, 0, 1, GraphWakeReason::Runnable),
            graph_wake(2, 10_000_000, 0, GraphWakeReason::Sleeping),
            HeapLogEntry {
                sequence: 3,
                time_nanos: d_connected,
                kind: HeapLogKind::ConnectAttempt { target: listener_addr },
            },
            graph_wake(4, d_connected, 1, GraphWakeReason::Runnable),
            HeapLogEntry { sequence: 5, time_nanos: d_connected, kind: HeapLogKind::SendAck { conn: initiator } },
            graph_wake(7, d_connected, 1, GraphWakeReason::Runnable),
            HeapLogEntry {
                sequence: 6,
                time_nanos: d_connected + d_deliver,
                kind: HeapLogKind::Deliver { conn: responder, data_len: 4 },
            },
            HeapLogEntry {
                sequence: 8,
                time_nanos: 10_000_000 + d_accepted,
                kind: HeapLogKind::Accepted { listener: listener_addr, responder_conn: responder, initiator_addr },
            },
            graph_wake(9, 10_000_000 + d_accepted, 0, GraphWakeReason::Runnable),
        ],
    );
}

/// Mux-style recv header then leftover body: second recv must complete from the buffer
/// via WorldLoop (recv is never Ready), not a stale pending_recvs entry.
#[tokio::test]
async fn test_mux_recv_header_then_leftover_body() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9300".parse().unwrap();
    let header = observed::<Vec<u8>>();
    let body = observed::<Vec<u8>>();
    let header_a = header.clone();
    let body_a = body.clone();

    let mut graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let header_a = header_a.clone();
        let body_a = body_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let head = net.recv(conn, NonZeroUsize::new(2).unwrap()).await.unwrap();
            set_observed(&header_a, head.as_ref().to_vec());
            let rest = net.recv(conn, NonZeroUsize::new(4).unwrap()).await.unwrap();
            set_observed(&body_a, rest.as_ref().to_vec());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        net.send(conn, NonEmptyBytes::try_from(Bytes::from("ABCDEF")).unwrap()).await.unwrap();
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();
    assert_eq!(header.lock().as_deref(), Some(b"AB".as_ref()));
    assert_eq!(body.lock().as_deref(), Some(b"CDEF".as_ref()));
}

/// Close must fail a parked recv on the peer, not leave it waiting.
#[tokio::test]
async fn test_close_fails_peer_recv() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9400".parse().unwrap();
    let recv_err = observed::<String>();
    let recv_err_a = recv_err.clone();

    let mut graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let recv_err_a = recv_err_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let err = net.recv(conn, NonZeroUsize::new(1).unwrap()).await.unwrap_err();
            set_observed(&recv_err_a, err.to_string());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        net.close(conn).await.unwrap();
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();
    assert!(recv_err.lock().as_ref().is_some_and(|s| s.contains("connection closed")));
}

/// A Wait must resume from next_wakeup even when the network heap is empty.
#[tokio::test]
async fn test_wait_resumes_without_heap_event() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let done = observed::<bool>();
    let done_a = done.clone();

    let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("waiter", move |_state: (), _unit: (), eff| {
        let done_a = done_a.clone();
        async move {
            eff.wait(Duration::from_nanos(1_000)).await;
            set_observed(&done_a, true);
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_to_completion();
    assert_eq!(*done.lock(), Some(true));
}

/// A Wait on a graph with a non-zero global epoch offset must still resume.
/// Instant comparison is `sim_elapsed + offset`. Waking with a zero-offset
/// max_time misses that Wait and reschedules the Sleeping wake forever, so a
/// later Deliver never pops.
#[tokio::test]
async fn test_sleeping_wake_uses_graph_epoch_offset() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let done = observed::<bool>();
    let done_a = done.clone();
    let epoch_offset = Duration::from_secs(70_419_600);
    let wait_at = 100_000_000;
    let deliver_at = 200_000_000;
    let hop_conn = ConnectionId::initial();
    provider.schedule_event_at(deliver_at, NetworkEvent::Deliver { conn: hop_conn, data: Bytes::from_static(b"x") });

    let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo).with_global_epoch_offset(epoch_offset);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("waiter", move |_state: (), _unit: (), eff| {
        let done_a = done_a.clone();
        async move {
            eff.wait(Duration::from_nanos(wait_at)).await;
            set_observed(&done_a, true);
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_until_horizon(wait_at.saturating_sub(1));
    assert_eq!(*done.lock(), None, "Wait must not complete before its wakeup");
    assert_eq!(world.peek_next_event_time(), Some(wait_at));

    world.run_until_horizon(deliver_at);
    assert_eq!(*done.lock(), Some(true), "Sleeping wait must resume using the graph epoch offset");
    assert!(
        world.heap_log().iter().any(|e| e.kind == HeapLogKind::Deliver { conn: hop_conn, data_len: 1 }),
        "later Deliver must pop after the offset Wait wakes"
    );
}

#[tokio::test]
async fn test_listen_same_port_errors() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9500".parse().unwrap();
    let second = observed::<bool>();
    let second_a = second.clone();

    let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("node", move |_state: (), _unit: (), eff| {
        let second_a = second_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            set_observed(&second_a, net.listen(listener_addr).await.is_err());
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_to_completion();
    assert_eq!(*second.lock(), Some(true));
}

#[tokio::test]
async fn test_connect_refused_at_attempt_arrival() {
    let _guards = trace_guards();
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let trace = TraceBuffer::new_shared(100, 1_000_000);
    let listener_addr: SocketAddr = "127.0.0.1:9600".parse().unwrap();
    let failed = observed::<bool>();
    let failed_b = failed.clone();

    let mut graph = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("node", move |_state: (), _unit: (), eff| {
        let failed_b = failed_b.clone();
        async move {
            let net = Network::new(&eff);
            set_observed(&failed_b, net.connect(listener_addr.into(), Duration::from_secs(1)).await.is_err());
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_to_completion();
    assert_eq!(*failed.lock(), Some(true));

    let t_attempt = wire_delay_nanos(SEED, 0);
    assert_ne!(t_attempt, 0);
    assert!((WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(&t_attempt));
    assert_heap_log(
        world.take_heap_log(),
        vec![
            graph_wake(0, 0, 0, GraphWakeReason::Runnable),
            HeapLogEntry {
                sequence: 1,
                time_nanos: t_attempt,
                kind: HeapLogKind::ConnectAttempt { target: listener_addr },
            },
            graph_wake(2, t_attempt, 0, GraphWakeReason::Runnable),
        ],
    );

    assert_trace_match_filter(
        world.graph(0),
        &[
            tm_state("node-1", &()),
            tm_input("node-1", &()),
            tm_resume_unit("node-1"),
            tm_effect("node-1", ConnectEffect { addr: listener_addr.into(), timeout: Duration::from_secs(1) }),
            tm_clock(Duration::from_nanos(t_attempt)),
            tm_resume_external(
                "node-1",
                Err::<ConnectionId, ConnectError>(ConnectError::new(listener_addr.into(), "connection refused")),
            ),
            tm_state("node-1", &()),
        ],
        &[],
    );
}

#[tokio::test]
async fn test_send_recv_on_closed_peer_reset() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9700".parse().unwrap();
    let send_err = observed::<bool>();
    let recv_err = observed::<bool>();
    let send_err_b = send_err.clone();
    let recv_err_a = recv_err.clone();

    let mut graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let recv_err_a = recv_err_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            set_observed(&recv_err_a, net.recv(conn, NonZeroUsize::new(1).unwrap()).await.is_err());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| {
        let send_err_b = send_err_b.clone();
        async move {
            let net = Network::new(&eff);
            let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
            net.close(conn).await.unwrap();
            eff.wait(Duration::from_nanos(1)).await;
            set_observed(
                &send_err_b,
                net.send(conn, NonEmptyBytes::try_from(Bytes::from("x")).unwrap()).await.is_err(),
            );
        }
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();
    assert_eq!(*recv_err.lock(), Some(true));
    assert_eq!(*send_err.lock(), Some(true));
}

#[tokio::test]
async fn test_latency_is_one_to_five_ms() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let listener_addr: SocketAddr = "127.0.0.1:9800".parse().unwrap();
    let received = observed::<Vec<u8>>();
    let received_a = received.clone();

    let mut graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_a.resources().put::<ConnectionsResource>(provider.clone());
    let stage_a = graph_a.stage("node_a", move |_state: (), _unit: (), eff| {
        let received_a = received_a.clone();
        async move {
            let net = Network::new(&eff);
            net.listen(listener_addr).await.unwrap();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            let bytes = net.recv(conn, NonZeroUsize::new(1).unwrap()).await.unwrap();
            set_observed(&received_a, bytes.as_ref().to_vec());
        }
    });
    let stage_a = graph_a.wire_up(stage_a, ());
    let mut sim_a = graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let mut graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph_b.resources().put::<ConnectionsResource>(provider.clone());
    let stage_b = graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        net.send(conn, NonEmptyBytes::try_from(Bytes::from("z")).unwrap()).await.unwrap();
    });
    let stage_b = graph_b.wire_up(stage_b, ());
    let mut sim_b = graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    world.run_to_completion();
    assert_eq!(received.lock().as_deref(), Some(b"z".as_ref()));

    let hop = world
        .take_heap_log()
        .into_iter()
        .find(|e| matches!(e.kind, HeapLogKind::ConnectAttempt { .. } | HeapLogKind::Deliver { .. }));
    let hop = hop.expect("ConnectAttempt or Deliver on the heap log");
    assert_ne!(hop.time_nanos, 0, "wire hop must be delayed");
    assert!(
        (WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(&hop.time_nanos),
        "wire hop time {} not in 1ms..=5ms",
        hop.time_nanos
    );
}

#[test]
fn test_honest_payload_cap_is_five_preprod_slots() {
    let slot = PREPROD_ERA_HISTORY.current_era_summary().params.slot_length;
    assert_eq!(slot, Duration::from_secs(1), "preprod slot length");
    assert_eq!(
        Duration::from_nanos(HONEST_PAYLOAD_DELAY_MAX_NANOS),
        slot * u32::try_from(HONEST_PAYLOAD_DELAY_SLOTS).expect("slot budget fits u32"),
    );
}

#[test]
fn test_default_payload_delay_matches_wire_hop() {
    for index in 0..32 {
        assert_eq!(
            payload_delay_nanos(SEED, index, WIRE_DELAY_MIN_NANOS, WIRE_DELAY_MAX_NANOS),
            wire_delay_nanos(SEED, index),
            "default payload range is the 1–5ms hop at sample {index}"
        );
    }
}

/// Seeded long-tail samples stay in the 1–5ms hop for the majority, with at least one
/// sample orders of magnitude later. A uniform draw over `[1ms, 5s]` fails this.
#[test]
fn test_long_tail_payload_delay_is_not_uniform_over_five_slots() {
    const N: u64 = 256;
    let samples: Vec<u64> = (0..N).map(|index| long_tail_payload_delay_nanos(SEED, index)).collect();
    let short = samples.iter().filter(|d| (WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(d)).count();
    let long =
        samples.iter().filter(|d| (LONG_TAIL_PAYLOAD_MIN_NANOS..=HONEST_PAYLOAD_DELAY_MAX_NANOS).contains(d)).count();
    assert!(
        short * 2 > samples.len(),
        "most samples must stay in the 1–5ms hop, not a uniform [1ms, 5s] draw; short={short}/{}",
        samples.len()
    );
    assert!(long >= 1, "at least one sample must land in the long-tail bucket (>= 1s), got none");
    assert!(
        samples.iter().all(|d| {
            (WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(d)
                || (LONG_TAIL_PAYLOAD_MIN_NANOS..=HONEST_PAYLOAD_DELAY_MAX_NANOS).contains(d)
        }),
        "every sample must be a short hop or a long-tail hop within the per-send cap: {samples:?}"
    );
    let again: Vec<u64> = (0..N).map(|index| long_tail_payload_delay_nanos(SEED, index)).collect();
    assert_eq!(samples, again, "long-tail samples must be deterministic for a seed");
}

/// Two honest payloads sent at the same instant — one short hop, one long-tail — sit on
/// the one physical heap at those times. Seed `7` draws that pair. Pop the short first;
/// the long one stays on the heap. A sorted `assert_heap_log` cannot hide a missing late payload.
#[test]
fn test_short_and_long_tail_payloads_sit_on_one_heap() {
    const PAYLOAD_SEED: u64 = 7;
    let d0 = long_tail_payload_delay_nanos(PAYLOAD_SEED, 0);
    let d1 = long_tail_payload_delay_nanos(PAYLOAD_SEED, 1);
    let short_band = WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS;
    let long_band = LONG_TAIL_PAYLOAD_MIN_NANOS..=HONEST_PAYLOAD_DELAY_MAX_NANOS;
    assert!(
        (short_band.contains(&d0) && long_band.contains(&d1)) || (long_band.contains(&d0) && short_band.contains(&d1)),
        "seed {PAYLOAD_SEED} must draw one short hop and one long-tail payload, got {d0} and {d1}"
    );

    let provider = Arc::new(WorldConnectionProvider::with_long_tail_payload_delay(PAYLOAD_SEED));
    let (conn0, conn1) = pair_ids();
    provider.schedule_payload(NetworkEvent::Deliver { conn: conn0, data: Bytes::from_static(b"p0") });
    provider.schedule_payload(NetworkEvent::Deliver { conn: conn1, data: Bytes::from_static(b"p1") });

    let first = HeapLogEntry { sequence: 0, time_nanos: d0, kind: HeapLogKind::Deliver { conn: conn0, data_len: 2 } };
    let second = HeapLogEntry { sequence: 1, time_nanos: d1, kind: HeapLogKind::Deliver { conn: conn1, data_len: 2 } };
    let (early, late) = if d0 < d1 { (first, second) } else { (second, first) };

    let mut world = WorldLoop::new(provider, vec![]);
    assert_eq!(
        world.heap_contents(),
        vec![early, late],
        "both payloads must already sit on the one heap at their sampled times"
    );
    assert!(short_band.contains(&early.time_nanos), "the earlier heap entry must be the short hop");
    assert!(long_band.contains(&late.time_nanos), "the later heap entry must be the long-tail payload");

    world.run_until_horizon(early.time_nanos);
    assert_eq!(world.take_heap_log(), vec![early], "short payload must pop first, not a sorted log of both");
    assert_eq!(world.heap_contents(), vec![late], "long-tail payload must still be on the heap");

    world.run_until_horizon(late.time_nanos);
    assert_eq!(world.take_heap_log(), vec![late]);
    assert!(world.heap_contents().is_empty(), "both payloads must have been popped");
}

/// A ready-now graph wake and a `NetworkEvent` at the same nanos are one heap.
///
/// `Deliver` is scheduled first (seq 0). The graph is then placed on that same heap
/// as `GraphWake` (seq 1). Both at t=0. The loop must pop `Deliver` then the graph —
/// not run the graph to park and only then the hop. `heap_contents` is checked
/// **before** the loop so both items are first-class heap entries, not a Vec scan.
#[tokio::test]
async fn test_equal_time_graph_wake_and_network_event_are_one_heap() {
    let _guards = trace_guards();
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let trace = TraceBuffer::new_shared(100, 1_000_000);
    let hop_conn = ConnectionId::initial();
    provider.schedule_event_at(0, NetworkEvent::Deliver { conn: hop_conn, data: Bytes::from_static(b"x") });

    let ran = observed::<bool>();
    let ran_a = ran.clone();
    let mut graph = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("ready", move |_state: (), _unit: (), _eff| {
        let ran_a = ran_a.clone();
        async move {
            set_observed(&ran_a, true);
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    assert_eq!(*ran.lock(), None, "graph must not run until its heap entry is popped");
    let deliver =
        HeapLogEntry { sequence: 0, time_nanos: 0, kind: HeapLogKind::Deliver { conn: hop_conn, data_len: 1 } };
    let wake = graph_wake(1, 0, 0, GraphWakeReason::Runnable);
    assert_eq!(
        world.heap_contents(),
        vec![deliver, wake],
        "graph wake and NetworkEvent must already share one heap at the same nanos"
    );
    assert_eq!(deliver.time_nanos, wake.time_nanos);
    assert!(deliver.sequence < wake.sequence);

    world.run_to_completion();
    assert_eq!(*ran.lock(), Some(true));

    let log = world.take_heap_log();
    assert_eq!(&log[..2], &[deliver, wake], "pop order must follow (time, sequence), not all-graphs-then-hop");

    assert_trace_match_filter(
        world.graph(0),
        &[tm_state("ready-1", &()), tm_input("ready-1", &()), tm_resume_unit("ready-1"), tm_state("ready-1", &())],
        &[],
    );
}

/// A sleeping graph wake and a `Deliver` at the same nanos sit on one heap before either pops.
/// Pop order follows `(time, sequence)` — the hop is not deferred until the graph parks.
#[tokio::test]
async fn test_equal_time_wait_and_deliver_share_one_heap() {
    let _guards = trace_guards();
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let trace = TraceBuffer::new_shared(100, 1_000_000);
    let hop_time = 2_000_000;
    let hop_conn = ConnectionId::initial();
    provider.schedule_event_at(hop_time, NetworkEvent::Deliver { conn: hop_conn, data: Bytes::from_static(b"x") });

    let woke = observed::<bool>();
    let woke_a = woke.clone();
    let mut graph = SimulationBuilder::default().with_trace_buffer(trace.clone()).with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("waiter", move |_state: (), _unit: (), eff| {
        let woke_a = woke_a.clone();
        async move {
            eff.wait(Duration::from_nanos(hop_time)).await;
            set_observed(&woke_a, true);
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_until_horizon(hop_time.saturating_sub(1));
    assert_eq!(*woke.lock(), None, "Wait must not complete before the shared timestamp");

    let deliver =
        HeapLogEntry { sequence: 0, time_nanos: hop_time, kind: HeapLogKind::Deliver { conn: hop_conn, data_len: 1 } };
    let at_hop: Vec<_> = world.heap_contents().into_iter().filter(|e| e.time_nanos == hop_time).collect();
    assert_eq!(at_hop.len(), 2, "Deliver and GraphWake must both be on the heap at {hop_time}: {at_hop:?}");
    assert_eq!(at_hop[0], deliver);
    assert!(
        matches!(at_hop[1].kind, HeapLogKind::GraphWake { reason: GraphWakeReason::Sleeping, graph: 0 }),
        "expected Sleeping graph wake: {at_hop:?}"
    );
    assert_eq!(at_hop[0].time_nanos, at_hop[1].time_nanos);
    assert!(at_hop[0].sequence < at_hop[1].sequence);

    world.run_to_completion();
    assert_eq!(*woke.lock(), Some(true));
    let popped: Vec<_> = world.take_heap_log().into_iter().filter(|e| e.time_nanos == hop_time).collect();
    assert_eq!(popped, at_hop, "pop order at the shared timestamp must match heap (time, sequence)");

    let wait = Duration::from_nanos(hop_time);
    assert_trace_match_filter(
        world.graph(0),
        &[
            tm_state("waiter-1", &()),
            tm_input("waiter-1", &()),
            tm_resume_unit("waiter-1"),
            TraceEntry::suspend(Effect::Wait { at_stage: Name::from("waiter-1"), duration: wait }).into(),
            tm_clock(wait),
            TraceEntry::resume("waiter-1", StageResponse::WaitResponse(Instant::at_offset(wait, Duration::ZERO)))
                .into(),
            tm_state("waiter-1", &()),
        ],
        &[],
    );
}

/// A sleeping graph is scheduled at `next_wakeup` and does not run before that time
/// while an earlier Deliver can complete.
#[tokio::test]
async fn test_sleeping_graph_does_not_run_before_earlier_deliver() {
    let handle = tokio::runtime::Handle::current();
    let provider = provider();
    let deliver_at = 1_000_000;
    let wake_at = 10_000_000;
    let hop_conn = ConnectionId::initial();
    provider.schedule_event_at(deliver_at, NetworkEvent::Deliver { conn: hop_conn, data: Bytes::from_static(b"x") });

    let done = observed::<bool>();
    let done_a = done.clone();
    let mut graph = SimulationBuilder::default().with_eval_strategy(Fifo);
    graph.resources().put::<ConnectionsResource>(provider.clone());
    let stage = graph.stage("late", move |_state: (), _unit: (), eff| {
        let done_a = done_a.clone();
        async move {
            eff.wait(Duration::from_nanos(wake_at)).await;
            set_observed(&done_a, true);
        }
    });
    let stage = graph.wire_up(stage, ());
    let mut sim = graph.run(&handle);
    sim.enqueue_msg(&stage, [()]);

    let mut world = WorldLoop::new(provider, vec![sim]);
    world.run_until_horizon(deliver_at);
    assert_eq!(*done.lock(), None, "graph must still be sleeping when the earlier Deliver pops");
    let log = world.heap_log();
    assert!(log.iter().any(|e| e.kind == HeapLogKind::Deliver { conn: hop_conn, data_len: 1 }));
    assert!(!log.iter().any(|e| {
        matches!(e.kind, HeapLogKind::GraphWake { reason: GraphWakeReason::Sleeping, .. }) && e.time_nanos == wake_at
    }));
    assert_eq!(world.peek_next_event_time(), Some(wake_at));

    world.run_to_completion();
    assert_eq!(*done.lock(), Some(true));
    let log = by_time_seq(world.take_heap_log());
    let deliver_seq =
        log.iter().find(|e| e.kind == HeapLogKind::Deliver { conn: hop_conn, data_len: 1 }).expect("Deliver").sequence;
    let wake_seq = log
        .iter()
        .find(|e| {
            matches!(e.kind, HeapLogKind::GraphWake { reason: GraphWakeReason::Sleeping, .. })
                && e.time_nanos == wake_at
        })
        .expect("Sleeping graph wake")
        .sequence;
    assert!(deliver_seq < wake_seq, "earlier Deliver must have a lower sequence than the later graph wake");
}

/// Two production-shaped nodes (`build_node` × SimulationBuilder × SimulationRunning)
/// over one WorldConnectionProvider, driven only by WorldLoop. A third node would need
/// the listen-side accept interval (100ms Wait) to be woken; that is left to a later PR
/// so keepalive Waits stay un-woken.
///
/// Proves they boot, connect, and put at least one header on the wire (typed
/// chainsync `RollForward` or `ValidateHeaderEffect`). Does not claim tip equality
/// and does not load a preprod fragment. `k` stays at the production value.
/// Long-tail payload delay is a world setting, not a theorem. Horizon only runs
/// far enough for sampled Deliveries to pop; it is not a Praos deadline.
///
/// Not `#[tokio::test]`: production graphs issue DurationDist::Zero effects whose `run()`
/// may be Pending on the first poll, and SimulationRunning then `Handle::block_on`s them.
/// That panics inside an existing Tokio context. WorldLoop is therefore synchronous.
#[test]
fn test_world_owns_production_nodes_boot_connect_exchange() {
    let _guards = fragment_trace_guards();
    let runtime = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
    let handle = runtime.handle().clone();
    let provider = Arc::new(WorldConnectionProvider::with_long_tail_payload_delay(SEED));

    let conway_start_slot = Slot::from(68_774_400);
    let root_point = NetworkPoint::Specific(conway_start_slot, Hash::new([0u8; 32]));
    let headers = run_strategy(any_headers_chain_with_root(2, root_point.with_height(BlockHeight::from(0))));

    let listen_a = "127.0.0.1:9311";
    let listen_b = "127.0.0.1:9310";
    let peer_a = Peer::new(listen_a);

    let node_a = NodeTestConfig::default()
        .with_no_upstream_peers()
        .with_listen_address(listen_a)
        .with_seed(11)
        .with_trace_buffer(TraceBuffer::new_shared(10_000, 8_000_000))
        .with_validated_blocks(headers);
    let node_b = NodeTestConfig::default()
        .with_upstream_peer(peer_a)
        .with_listen_address(listen_b)
        .with_seed(12)
        .with_trace_buffer(TraceBuffer::new_shared(10_000, 8_000_000));

    let connections: ConnectionsResource = provider.clone();
    let sim_a = build_world_node(&node_a, connections.clone(), &handle).expect("node A");
    let sim_b = build_world_node(&node_b, connections, &handle).expect("node B");

    let mut world = WorldLoop::new(provider, vec![sim_a, sim_b]);
    // World coverage so a sampled long-tail Deliver can pop. Not a Praos deadline.
    world.run_until_horizon(HONEST_PAYLOAD_DELAY_MAX_NANOS.saturating_add(WIRE_DELAY_MAX_NANOS));

    for graph in world.graphs() {
        let params = graph.resources().get::<ResourceParameters>().expect("production GlobalParameters");
        assert_eq!(
            params.consensus_security_param, PREPROD_GLOBAL_PARAMETERS.consensus_security_param,
            "world nodes must keep production k"
        );
        assert_eq!(params.consensus_security_param, 2160);
    }

    let log = world.heap_log();
    assert!(log.iter().any(|e| matches!(e.kind, HeapLogKind::ConnectAttempt { .. })), "nodes must connect: {log:?}");
    assert!(log.iter().any(|e| matches!(e.kind, HeapLogKind::Accepted { .. })), "nodes must accept: {log:?}");
    assert!(log.iter().any(|e| matches!(e.kind, HeapLogKind::SendAck { .. })), "nodes must send: {log:?}");
    assert!(log.iter().any(|e| matches!(e.kind, HeapLogKind::Deliver { .. })), "nodes must deliver: {log:?}");

    let header_on_wire = world.graphs().iter().any(|graph| {
        graph
            .trace_buffer()
            .lock()
            .hydrate_without_timestamps()
            .iter()
            .any(|entry| tm_chainsync_roll_forward() == *entry || tm_validate_header() == *entry)
    });
    assert!(header_on_wire, "expected a typed chainsync RollForward or ValidateHeaderEffect; heap={log:?}");
}

/// A real preprod fragment, produced by `run_until` after bootstrap, is disseminated over
/// `WorldConnectionProvider`. Node A is primed from that store (not `with_validated_blocks` on a
/// synthetic `any_headers_chain`). Node B starts from bootstrap only and must receive the
/// fragment HEAD on the mux.
///
/// B's `cmp_tip` equals the fragment HEAD after production `CanValidateHeaders`, once those
/// headers have arrived. Long-tail payload delay is a world setting, not a theorem. Horizon
/// only runs the world far enough for sampled Deliveries to pop; it is not a Praos deadline
/// and not a paper time bound. This is not P-diff, not Δ=5, not inbox-by-sl+6, not P-join,
/// and not 2Δ. `k` stays at the production value (2160).
///
/// `target_upstream_peers=1` is isolation (one intended hop). Dest-keyed pairing already completes
/// `Connected` only for the connect that targeted that listener.
///
/// Requires on-disk stores from `tests/fixtures/world-preprod-fragment/README.md`.
/// Not `#[tokio::test]`: production graphs may `Handle::block_on` DurationDist::Zero effects.
#[test]
#[ignore = "requires preprod fragment stores; see tests/fixtures/world-preprod-fragment/README.md"]
fn test_world_disseminates_preprod_fragment() {
    use std::cmp::Ordering;

    use amaru_consensus::stages::select_chain::cmp_tip;
    use amaru_kernel::{IsHeader, PREPROD_ERA_HISTORY, PREPROD_GLOBAL_PARAMETERS, Peer};
    use amaru_ouroboros::BaseReadChainStore;
    use amaru_protocols::store_effects::ResourceHeaderStore;

    use super::fragment::{
        copy_dir, fixture_root, header_hash_from_snapshot_point, linear_fragment_to_head, linear_fragment_with_bodies,
        load_committed_meta, open_chain_store, stores_ready,
    };

    let _guards = fragment_trace_guards();

    let root = fixture_root();
    assert!(stores_ready(&root), "preprod fragment stores missing under {}; follow README.md", root.display());
    let meta = load_committed_meta(&root).expect("meta.json");
    assert_eq!(meta.peer, "sleipnir.rkuhn.info:3001");

    let primed_tmp = tempfile::tempdir().expect("primed temp");
    let receiver_tmp = tempfile::tempdir().expect("receiver temp");
    copy_dir(&root.join("primed/chain"), &primed_tmp.path().join("chain")).expect("copy primed chain");
    copy_dir(&root.join("primed/ledger"), &primed_tmp.path().join("ledger")).expect("copy primed ledger");
    copy_dir(&root.join("bootstrap/chain"), &receiver_tmp.path().join("chain")).expect("copy bootstrap chain");
    copy_dir(&root.join("bootstrap/ledger"), &receiver_tmp.path().join("ledger")).expect("copy bootstrap ledger");

    let primed_chain_path = primed_tmp.path().join("chain");
    let snapshot_hash = header_hash_from_snapshot_point(&meta.latest_snapshot_point).expect("snapshot hash");
    let meta_head = {
        let store = open_chain_store(&primed_chain_path).expect("open primed chain");
        let fragment = linear_fragment_with_bodies(&store, snapshot_hash).expect("disseminable fragment");
        let head = fragment.last().cloned().expect("fragment has a HEAD");
        let walked = linear_fragment_to_head(&store, snapshot_hash, head.clone()).expect("parent walk to HEAD");
        assert_eq!(walked.last().map(|h| h.point()), Some(head.point()));
        assert_eq!(
            head.point(),
            fragment.last().expect("HEAD").point(),
            "linear fragment HEAD is the last header, not first()"
        );
        assert_eq!(format!("{}", head.point()), meta.fragment_head);
        assert_ne!(
            format!("{}", fragment[0].point()),
            meta.fragment_head,
            "HEAD must not be the first header after the snapshot"
        );
        head
    };

    let offset = PREPROD_ERA_HISTORY
        .slot_to_relative_time_unchecked_horizon(meta_head.slot())
        .expect("fragment slot in era history")
        + Duration::from_secs(30);

    let runtime = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
    let handle = runtime.handle().clone();
    let provider = Arc::new(WorldConnectionProvider::with_long_tail_payload_delay(SEED));

    let listen_primed = "127.0.0.1:9321";
    let listen_receiver = "127.0.0.1:9320";
    let peer_primed = Peer::new(listen_primed);

    // Isolation: one intended hop. Dest-keyed pairing still owns handshake matching.
    let node_primed = NodeTestConfig::default()
        .with_no_upstream_peers()
        .with_listen_address(listen_primed)
        .with_seed(21)
        .with_target_upstream_peers(1)
        .with_trace_buffer(TraceBuffer::new_shared(10_000, 8_000_000))
        .with_ledger_dir(primed_tmp.path().join("ledger"))
        .with_chain_dir(primed_tmp.path().join("chain"))
        .with_global_epoch_offset(offset);
    let node_receiver = NodeTestConfig::default()
        .with_upstream_peer(peer_primed)
        .with_listen_address(listen_receiver)
        .with_seed(22)
        .with_target_upstream_peers(1)
        .with_trace_buffer(TraceBuffer::new_shared(10_000, 8_000_000))
        .with_ledger_dir(receiver_tmp.path().join("ledger"))
        .with_chain_dir(receiver_tmp.path().join("chain"))
        .with_global_epoch_offset(offset);

    let connections: ConnectionsResource = provider.clone();
    let sim_primed = build_world_node(&node_primed, connections.clone(), &handle).expect("primed node");
    let sim_receiver = build_world_node(&node_receiver, connections, &handle).expect("receiver node");

    let primed_store = {
        let store = sim_primed.resources().get::<ResourceHeaderStore>().expect("primed chain store");
        Arc::clone(&*store)
    };
    let receiver_store = {
        let store = sim_receiver.resources().get::<ResourceHeaderStore>().expect("receiver chain store");
        Arc::clone(&*store)
    };

    // `build_node` realigns the best chain to the ledger tip. The HEAD WorldLoop serves is that
    // post-realign tip, not the last stored body recorded before open.
    let served_tip = primed_store.get_best_chain_tip();
    let served_head = primed_store
        .load_header(&served_tip.hash())
        .unwrap_or_else(|| panic!("primed store missing served tip header {served_tip}"));
    assert!(primed_store.has_block(&served_tip.hash()).expect("has_block"), "served tip must have a stored body");
    assert_ne!(served_tip.hash(), snapshot_hash, "served tip must be after the snapshot");
    let served_fragment = linear_fragment_to_head(primed_store.as_ref(), snapshot_hash, served_head.clone())
        .expect("parent walk from snapshot to served tip");
    assert_eq!(served_fragment.last().map(|h| h.point()), Some(served_tip));
    for earlier in &served_fragment[..served_fragment.len() - 1] {
        assert_eq!(
            cmp_tip(Some(&served_head), Some(earlier)),
            Ordering::Greater,
            "served HEAD must win cmp_tip against earlier headers"
        );
    }
    assert!(receiver_store.load_header(&served_tip.hash()).is_none(), "receiver must start without the served HEAD");
    assert_ne!(
        receiver_store.get_best_chain_tip(),
        served_tip,
        "receiver best tip starts at bootstrap, not the served HEAD"
    );

    let mut world = WorldLoop::new(provider, vec![sim_primed, sim_receiver]);
    // World coverage so sampled long-tail Deliveries can pop. Not a Praos deadline.
    world.run_until_horizon(HONEST_PAYLOAD_DELAY_MAX_NANOS.saturating_add(2_000_000_000));

    for graph in world.graphs() {
        let params = graph.resources().get::<ResourceParameters>().expect("production GlobalParameters");
        assert_eq!(params.consensus_security_param, PREPROD_GLOBAL_PARAMETERS.consensus_security_param);
        assert_eq!(params.consensus_security_param, 2160, "production k, not chain_length");
    }

    let receiver_after = world.graphs()[1].resources().get::<ResourceHeaderStore>().expect("receiver store");
    assert!(
        receiver_after.load_header(&served_tip.hash()).is_some(),
        "receiving node must have the served HEAD in store before tip equality is compared"
    );

    let head_hash = served_head.hash();
    let receiver_traces = world.graphs()[1].trace_buffer().lock().hydrate_without_timestamps();
    let receiver_got_roll_forward =
        receiver_traces.iter().any(|entry| entry_chainsync_roll_forward_hash(entry) == Some(head_hash));
    assert!(
        receiver_got_roll_forward,
        "B must see a typed chainsync RollForward of the served HEAD (not a Debug substring OR); head={head_hash}"
    );
    let receiver_validated = receiver_traces.iter().any(|entry| entry_is_validate_header_of(entry, &head_hash));
    assert!(receiver_validated, "B must run production ValidateHeaderEffect on the served HEAD; head={head_hash}");

    let primed_after = world.graphs()[0].resources().get::<ResourceHeaderStore>().expect("primed store");
    let primed_tip = primed_after.get_best_chain_tip();
    let receiver_tip = receiver_after.get_best_chain_tip();
    let primed_header = primed_after.load_header(&primed_tip.hash()).expect("primed tip header");
    let receiver_header = receiver_after.load_header(&receiver_tip.hash()).expect("receiver tip header");
    assert_eq!(
        cmp_tip(Some(&receiver_header), Some(&served_head)),
        Ordering::Equal,
        "receiver tip must be cmp_tip-equal to the served HEAD after production validation"
    );
    assert_eq!(
        cmp_tip(Some(&primed_header), Some(&served_head)),
        Ordering::Equal,
        "primed tip must be cmp_tip-equal to the served HEAD after production validation"
    );
    assert_eq!(receiver_tip, served_tip);
    assert_eq!(primed_tip, served_tip);
}

fn header_from_content(content: &amaru_protocols::chainsync::HeaderContent) -> Option<amaru_kernel::Header> {
    amaru_kernel::from_cbor(&content.cbor)
}

fn roll_forward_hash_from_result(
    msg: &amaru_protocols::chainsync::InitiatorResult,
) -> Option<amaru_kernel::HeaderHash> {
    match msg {
        amaru_protocols::chainsync::InitiatorResult::RollForward(content, _) => {
            header_from_content(content).map(|h| amaru_kernel::IsHeader::hash(&h))
        }
        amaru_protocols::chainsync::InitiatorResult::Initialize
        | amaru_protocols::chainsync::InitiatorResult::IntersectFound(_, _)
        | amaru_protocols::chainsync::InitiatorResult::IntersectNotFound(_)
        | amaru_protocols::chainsync::InitiatorResult::RollBackward(_, _)
        | amaru_protocols::chainsync::InitiatorResult::Terminated => None,
    }
}

fn send_data_chainsync_roll_forward_hash(data: &dyn amaru_pure_stage::SendData) -> Option<amaru_kernel::HeaderHash> {
    use amaru_consensus::stages::track_peers::TrackPeersMsg;
    use amaru_protocols::chainsync::ChainSyncInitiatorMsg;

    if let Ok(msg) = data.cast_ref::<ChainSyncInitiatorMsg>() {
        return roll_forward_hash_from_result(&msg.msg);
    }
    if let Ok(TrackPeersMsg::FromUpstream(msg)) = data.cast_ref::<TrackPeersMsg>() {
        return roll_forward_hash_from_result(&msg.msg);
    }
    None
}

/// Typed chainsync RollForward of a header hash on this graph. Not a Debug substring OR.
fn entry_chainsync_roll_forward_hash(entry: &TraceEntry) -> Option<amaru_kernel::HeaderHash> {
    match entry {
        TraceEntry::Suspend(Effect::Send { msg, .. }) => send_data_chainsync_roll_forward_hash(msg.as_ref()),
        TraceEntry::Input { input, .. } => send_data_chainsync_roll_forward_hash(input.as_ref()),
        TraceEntry::Suspend(_)
        | TraceEntry::Resume { .. }
        | TraceEntry::Clock(_)
        | TraceEntry::State { .. }
        | TraceEntry::Terminated { .. }
        | TraceEntry::InvalidBytes(..) => None,
    }
}

/// Typed chainsync `RollForward` on Send or Input. Specific matcher, next to the test.
fn tm_chainsync_roll_forward() -> TraceMatch<'static> {
    TraceMatch::Property(
        Box::new(|entry| entry_chainsync_roll_forward_hash(entry).is_some()),
        "chainsync RollForward".to_string(),
    )
}

/// Typed `ValidateHeaderEffect`. Specific wrapper; downcasts via the generic helper.
/// No `header()` accessor.
fn tm_validate_header() -> TraceMatch<'static> {
    tm_external_effect_any::<amaru_consensus::effects::ValidateHeaderEffect>()
}

/// Typed `ValidateHeaderEffect` on this graph whose Debug names `hash`.
///
/// `ValidateHeaderEffect` does not expose the header. Do not treat a substring OR on
/// `RollForward`/`ValidateHeader`/`HeaderContent` as this proof.
fn entry_is_validate_header_of(entry: &TraceEntry, hash: &amaru_kernel::HeaderHash) -> bool {
    let TraceEntry::Suspend(Effect::External { effect, .. }) = entry else {
        return false;
    };
    let Some(typed) = effect.cast_ref::<amaru_consensus::effects::ValidateHeaderEffect>() else {
        return false;
    };
    tm_validate_header() == *entry && format!("{typed:?}").contains(&hash.to_string())
}
