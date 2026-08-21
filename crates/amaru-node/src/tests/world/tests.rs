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

use amaru_kernel::{NonEmptyBytes, Peer};
use amaru_ouroboros::{ConnectionId, ConnectionsResource};
use amaru_protocols::network_effects::{
    AcceptEffect, AcceptError, ConnectEffect, ConnectError, ListenEffect, ListenError, Network, NetworkOps,
    ReceiveError, RecvEffect, SendEffect, SendError,
};
use amaru_pure_stage::{
    StageGraph, assert_trace_match_filter, register_data_deserializer, register_effect_deserializer,
    simulation::{Fifo, SimulationBuilder},
    tm_clock, tm_effect, tm_input, tm_resume_external, tm_resume_unit, tm_state,
    trace_buffer::TraceBuffer,
};
use parking_lot::Mutex;
use tokio_util::bytes::Bytes;

use super::{
    HeapLogEntry, HeapLogKind, NetworkEvent, WIRE_DELAY_MAX_NANOS, WIRE_DELAY_MIN_NANOS, WorldConnectionProvider,
    WorldLoop, wire_delay_nanos,
};

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
    world.run_to_completion().await;

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
    assert_eq!(
        world.take_heap_log(),
        vec![
            HeapLogEntry {
                sequence: 0,
                time_nanos: t_connected,
                kind: HeapLogKind::ConnectAttempt { target: listener_addr },
            },
            HeapLogEntry { sequence: 2, time_nanos: t_connected, kind: HeapLogKind::SendAck { conn: initiator } },
            HeapLogEntry {
                sequence: 1,
                time_nanos: t_accepted,
                kind: HeapLogKind::Accepted {
                    listener: listener_addr,
                    responder_conn: responder,
                    initiator_addr: initiator_sock,
                },
            },
            HeapLogEntry {
                sequence: 3,
                time_nanos: t_deliver,
                kind: HeapLogKind::Deliver { conn: responder, data_len: 12 }
            },
        ]
    );

    let mut expected = Vec::new();
    expected.extend([
        tm_state("node_a-1", &()),
        tm_state("node_b-1", &()),
        tm_input("node_a-1", &()),
        tm_resume_unit("node_a-1"),
        tm_effect("node_a-1", ListenEffect { addr: listener_addr }),
        tm_resume_external("node_a-1", Ok::<SocketAddr, ListenError>(listener_addr)),
        tm_effect("node_a-1", AcceptEffect { listener_addr }),
        tm_input("node_b-1", &()),
        tm_resume_unit("node_b-1"),
        tm_effect("node_b-1", ConnectEffect { addr: listener_addr.into(), timeout: Duration::from_secs(1) }),
        tm_clock(Duration::from_nanos(t_connected)),
        tm_clock(Duration::from_nanos(t_connected)),
        tm_resume_external("node_b-1", Ok::<ConnectionId, ConnectError>(initiator)),
        tm_effect("node_b-1", SendEffect { conn: initiator, data: msg.clone() }),
        tm_resume_external("node_b-1", Ok::<(), SendError>(())),
        tm_state("node_b-1", &()),
    ]);
    if t_accepted <= t_deliver {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(12).unwrap() }),
        ]);
        if t_deliver > t_accepted {
            expected.extend([tm_clock(Duration::from_nanos(t_deliver)), tm_clock(Duration::from_nanos(t_deliver))]);
        }
        expected.extend([
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    } else {
        expected.extend([
            tm_clock(Duration::from_nanos(t_deliver)),
            tm_clock(Duration::from_nanos(t_deliver)),
            tm_clock(Duration::from_nanos(t_accepted)),
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
    world.run_until_horizon(1000).await;

    assert_eq!(
        world.take_heap_log(),
        vec![HeapLogEntry { sequence: 0, time_nanos: 100, kind: HeapLogKind::Close { conn: conn_in } }]
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
    world.run_to_completion().await;
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
    world.run_to_completion().await;
    assert_eq!(received.lock().as_deref(), Some(b"ok".as_ref()));

    let (initiator, responder) = pair_ids();
    let initiator_sock = initiator_addr(initiator);
    let t_attempt = wire_delay_nanos(SEED, 0);
    let t_accepted = t_attempt + wire_delay_nanos(SEED, 1);
    let t_deliver = t_attempt + wire_delay_nanos(SEED, 2);
    assert!((WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(&t_attempt));
    let log = world.take_heap_log();
    assert_eq!(
        log[0],
        HeapLogEntry {
            sequence: 0,
            time_nanos: t_attempt,
            kind: HeapLogKind::ConnectAttempt { target: listener_addr },
        }
    );
    assert!(log.iter().any(|e| e.kind == HeapLogKind::SendAck { conn: initiator }));

    let msg = NonEmptyBytes::try_from(Bytes::from("ok")).unwrap();
    let mut expected = Vec::new();
    expected.extend([
        tm_state("node_b-1", &()),
        tm_state("node_a-1", &()),
        tm_input("node_b-1", &()),
        tm_resume_unit("node_b-1"),
        tm_effect("node_b-1", ConnectEffect { addr: listener_addr.into(), timeout: Duration::from_secs(1) }),
        tm_input("node_a-1", &()),
        tm_resume_unit("node_a-1"),
        tm_effect("node_a-1", ListenEffect { addr: listener_addr }),
        tm_resume_external("node_a-1", Ok::<SocketAddr, ListenError>(listener_addr)),
        tm_effect("node_a-1", AcceptEffect { listener_addr }),
        tm_clock(Duration::from_nanos(t_attempt)),
        tm_clock(Duration::from_nanos(t_attempt)),
        tm_resume_external("node_b-1", Ok::<ConnectionId, ConnectError>(initiator)),
        tm_effect("node_b-1", SendEffect { conn: initiator, data: msg.clone() }),
        tm_resume_external("node_b-1", Ok::<(), SendError>(())),
        tm_state("node_b-1", &()),
    ]);
    if t_accepted <= t_deliver {
        expected.extend([
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_clock(Duration::from_nanos(t_accepted)),
            tm_resume_external(
                "node_a-1",
                Ok::<(Peer, ConnectionId), AcceptError>((Peer::from_addr(&initiator_sock), responder)),
            ),
            tm_effect("node_a-1", RecvEffect { conn: responder, bytes: NonZeroUsize::new(2).unwrap() }),
        ]);
        if t_deliver > t_accepted {
            expected.extend([tm_clock(Duration::from_nanos(t_deliver)), tm_clock(Duration::from_nanos(t_deliver))]);
        }
        expected.extend([
            tm_resume_external("node_a-1", Ok::<NonEmptyBytes, ReceiveError>(msg)),
            tm_state("node_a-1", &()),
        ]);
    } else {
        expected.extend([
            tm_clock(Duration::from_nanos(t_deliver)),
            tm_clock(Duration::from_nanos(t_deliver)),
            tm_clock(Duration::from_nanos(t_accepted)),
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
    world.run_to_completion().await;
    assert_eq!(received.lock().as_deref(), Some(b"ping".as_ref()));

    let (initiator, responder) = pair_ids();
    let initiator_addr = initiator_addr(initiator);
    let d_connected = wire_delay_nanos(SEED, 0);
    let d_deliver = wire_delay_nanos(SEED, 1);
    let d_accepted = wire_delay_nanos(SEED, 2);
    assert_eq!(
        world.take_heap_log(),
        vec![
            HeapLogEntry {
                sequence: 0,
                time_nanos: d_connected,
                kind: HeapLogKind::ConnectAttempt { target: listener_addr },
            },
            HeapLogEntry { sequence: 1, time_nanos: d_connected, kind: HeapLogKind::SendAck { conn: initiator } },
            HeapLogEntry {
                sequence: 2,
                time_nanos: d_connected + d_deliver,
                kind: HeapLogKind::Deliver { conn: responder, data_len: 4 },
            },
            HeapLogEntry {
                sequence: 3,
                time_nanos: 10_000_000 + d_accepted,
                kind: HeapLogKind::Accepted { listener: listener_addr, responder_conn: responder, initiator_addr },
            },
        ]
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
    world.run_to_completion().await;
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
    world.run_to_completion().await;
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
    world.run_to_completion().await;
    assert_eq!(*done.lock(), Some(true));
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
    world.run_to_completion().await;
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
    world.run_to_completion().await;
    assert_eq!(*failed.lock(), Some(true));

    let t_attempt = wire_delay_nanos(SEED, 0);
    assert_ne!(t_attempt, 0);
    assert!((WIRE_DELAY_MIN_NANOS..=WIRE_DELAY_MAX_NANOS).contains(&t_attempt));
    assert_eq!(
        world.take_heap_log(),
        vec![HeapLogEntry {
            sequence: 0,
            time_nanos: t_attempt,
            kind: HeapLogKind::ConnectAttempt { target: listener_addr },
        }]
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
    world.run_to_completion().await;
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
    world.run_to_completion().await;
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
