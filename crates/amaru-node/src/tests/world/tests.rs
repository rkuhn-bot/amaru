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

use amaru_kernel::NonEmptyBytes;
use amaru_ouroboros::ConnectionsResource;
use amaru_protocols::network_effects::{Network, NetworkOps};
use amaru_pure_stage::{
    StageGraph,
    simulation::{Fifo, SimulationBuilder},
};
use tokio_util::bytes::Bytes;

use super::{NetworkEvent, WorldConnectionProvider, WorldLoop};

/// Prove one Deliver round-trip under the world loop.
/// Node A listens+accepts+recv, Node B connects+sends. Driven only by WorldLoop.
#[tokio::test]
async fn test_one_deliver_roundtrip_with_world_loop() {
    let handle = tokio::runtime::Handle::current();
    let provider = Arc::new(WorldConnectionProvider::new());
    let listener_addr: SocketAddr = "127.0.0.1:9000".parse().unwrap();

    let provider_a = provider.clone();
    let mut stage_graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_a.resources().put::<ConnectionsResource>(provider_a.clone());

    let stage_a = stage_graph_a.stage("node_a", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        net.listen(listener_addr).await.unwrap();
        let (_peer, conn) = net.accept(listener_addr).await.unwrap();
        let msg_len = NonZeroUsize::new("hello from B".len()).unwrap();
        let received = net.recv(conn, msg_len).await.unwrap();
        assert_eq!(received.as_ref(), b"hello from B");
    });
    let stage_a = stage_graph_a.wire_up(stage_a, ());
    let mut sim_a = stage_graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let provider_b = provider.clone();
    let mut stage_graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_b.resources().put::<ConnectionsResource>(provider_b.clone());

    let stage_b = stage_graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        let msg = NonEmptyBytes::try_from(Bytes::from("hello from B")).unwrap();
        net.send(conn, msg).await.unwrap();
    });
    let stage_b = stage_graph_b.wire_up(stage_b, ());
    let mut sim_b = stage_graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new((*provider).clone(), vec![sim_a, sim_b]);
    world.run_to_completion().await;

    let log = world.heap_log();
    assert!(log.iter().any(|e| e.kind == "Accepted"));
    assert!(log.iter().any(|e| e.kind == "Connected"));
    assert!(log.iter().any(|e| e.kind == "SendAck"));
    assert!(log.iter().any(|e| e.kind == "Deliver"));
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
    let provider = WorldConnectionProvider::new();

    let conn_in = amaru_ouroboros::ConnectionId::initial();
    provider.schedule_event_at(100, NetworkEvent::Close { conn: conn_in });

    let conn_out = amaru_ouroboros::ConnectionId::initial();
    provider.schedule_event_at(1500, NetworkEvent::Close { conn: conn_out });

    let mut world = WorldLoop::new(provider, vec![]);
    world.run_until_horizon(1000).await;

    let log = world.heap_log();
    assert!(log.iter().any(|e| e.time_nanos == 100 && e.kind == "Close"), "Event at t=100 should be in log");
    assert_eq!(world.peek_next_event_time(), Some(1500), "Event at t=1500 should still be on heap (not popped)");
}

/// Heap log structure: (seq, at, kind, conn).
#[tokio::test]
async fn test_heap_log_structure() {
    let handle = tokio::runtime::Handle::current();
    let provider = Arc::new(WorldConnectionProvider::new());
    let listener_addr: SocketAddr = "127.0.0.1:9020".parse().unwrap();

    let provider_a = provider.clone();
    let mut stage_graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_a.resources().put::<ConnectionsResource>(provider_a.clone());

    let stage_a = stage_graph_a.stage("node_a", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        net.listen(listener_addr).await.unwrap();
        let (_peer, conn) = net.accept(listener_addr).await.unwrap();
        let msg_len = NonZeroUsize::new(4).unwrap();
        let _received = net.recv(conn, msg_len).await.unwrap();
    });
    let stage_a = stage_graph_a.wire_up(stage_a, ());
    let mut sim_a = stage_graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let provider_b = provider.clone();
    let mut stage_graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_b.resources().put::<ConnectionsResource>(provider_b.clone());

    let stage_b = stage_graph_b.stage("node_b", move |_state: (), _unit: (), eff| async move {
        let net = Network::new(&eff);
        let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
        let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
        net.send(conn, msg).await.unwrap();
    });
    let stage_b = stage_graph_b.wire_up(stage_b, ());
    let mut sim_b = stage_graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new((*provider).clone(), vec![sim_a, sim_b]);
    world.run_to_completion().await;

    let log = world.heap_log();
    for entry in &log {
        assert!(!entry.kind.is_empty());
        assert!(entry.conn.is_some());
    }

    for i in 1..log.len() {
        assert!(log[i].sequence > log[i - 1].sequence);
    }
}
