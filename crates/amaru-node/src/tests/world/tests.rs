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
use amaru_ouroboros::{ConnectionId, ConnectionsResource};
use amaru_protocols::{Network, network_effects::NetworkOps};
use amaru_pure_stage::{
    StageGraph,
    simulation::{Fifo, SimulationBuilder},
};
use tokio_util::bytes::Bytes;

use super::{HeapEntry, NetworkEvent, WorldConnectionProvider, WorldLoop};

/// Prove one Deliver round-trip under world loop.
/// Node A listens+accepts, Node B connects+sends. No .await before world pops.
#[tokio::test]
async fn test_one_deliver_roundtrip_with_world_loop() {
    let handle = tokio::runtime::Handle::current();
    let provider = Arc::new(WorldConnectionProvider::new());
    let listener_addr: SocketAddr = "127.0.0.1:9000".parse().unwrap();

    // Node A: listen and accept, then recv
    let provider_a = provider.clone();
    let mut stage_graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_a.resources().set(provider_a.clone() as ConnectionsResource);

    let stage_a = stage_graph_a.stage("node_a", async move |mut state: Option<ConnectionId>, _unit: (), eff| {
        let net = Network::new(&eff);
        if state.is_none() {
            net.listen(listener_addr).await.ok();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            state = Some(conn);
            return state;
        }
        let msg_len = NonZeroUsize::new("hello from B".len()).unwrap();
        let received = net.recv(state.unwrap(), msg_len).await.unwrap();
        assert_eq!(received.as_ref(), b"hello from B");
        state
    });
    let stage_a = stage_graph_a.wire_up(stage_a, None);
    let mut sim_a = stage_graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    // Node B: connect and send
    let provider_b = provider.clone();
    let mut stage_graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_b.resources().set(provider_b.clone() as ConnectionsResource);

    let stage_b = stage_graph_b.stage("node_b", async move |mut state: Option<ConnectionId>, _unit: (), eff| {
        let net = Network::new(&eff);
        if state.is_none() {
            let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
            state = Some(conn);
            return state;
        }
        let msg = NonEmptyBytes::try_from(Bytes::from("hello from B")).unwrap();
        net.send(state.unwrap(), msg).await.unwrap();
        state
    });
    let stage_b = stage_graph_b.wire_up(stage_b, None);
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

/// Prove horizon cuts keepalive.
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

    // Manually schedule two events on the heap
    // Event 1: Close at t=100 (within horizon)
    let conn_in = amaru_ouroboros::ConnectionId::initial();
    provider.schedule_event_at(100, NetworkEvent::Close { conn: conn_in });

    // Event 2: Close at t=1500 (beyond horizon)
    let conn_out = amaru_ouroboros::ConnectionId::initial();
    provider.schedule_event_at(1500, NetworkEvent::Close { conn: conn_out });

    let mut world = WorldLoop::new(provider, vec![]);

    // Run to horizon=1000
    world.run_until_horizon(1000).await;

    // t_in=100 should be in heap_log
    let log = world.heap_log();
    assert!(log.iter().any(|e| e.time_nanos == 100 && e.kind == "Close"), "Event at t=100 should be in log");

    // t_out=1500 should still be on heap
    assert_eq!(world.peek_next_event_time(), Some(1500), "Event at t=1500 should still be on heap (not popped)");
}

/// Test heap log structure: (seq, at, kind, conn).
#[tokio::test]
async fn test_heap_log_structure() {
    let handle = tokio::runtime::Handle::current();
    let provider = Arc::new(WorldConnectionProvider::new());
    let listener_addr: SocketAddr = "127.0.0.1:9020".parse().unwrap();

    let provider_a = provider.clone();
    let mut stage_graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_a.resources().set(provider_a.clone() as ConnectionsResource);

    let stage_a = stage_graph_a.stage("node_a", async move |mut state: Option<ConnectionId>, _unit: (), eff| {
        let net = Network::new(&eff);
        if state.is_none() {
            net.listen(listener_addr).await.ok();
            let (_peer, conn) = net.accept(listener_addr).await.unwrap();
            state = Some(conn);
            return state;
        }
        let msg_len = NonZeroUsize::new(4).unwrap();
        let _received = net.recv(state.unwrap(), msg_len).await.unwrap();
        state
    });
    let stage_a = stage_graph_a.wire_up(stage_a, None);
    let mut sim_a = stage_graph_a.run(&handle);
    sim_a.enqueue_msg(&stage_a, [()]);

    let provider_b = provider.clone();
    let mut stage_graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    stage_graph_b.resources().set(provider_b.clone() as ConnectionsResource);

    let stage_b = stage_graph_b.stage("node_b", async move |mut state: Option<ConnectionId>, _unit: (), eff| {
        let net = Network::new(&eff);
        if state.is_none() {
            let conn = net.connect(listener_addr.into(), Duration::from_secs(1)).await.unwrap();
            state = Some(conn);
            return state;
        }
        let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
        net.send(state.unwrap(), msg).await.unwrap();
        state
    });
    let stage_b = stage_graph_b.wire_up(stage_b, None);
    let mut sim_b = stage_graph_b.run(&handle);
    sim_b.enqueue_msg(&stage_b, [()]);

    let mut world = WorldLoop::new((*provider).clone(), vec![sim_a, sim_b]);
    world.run_to_completion().await;

    let log = world.heap_log();
    for entry in &log {
        assert!(entry.sequence < u64::MAX);
        assert!(entry.time_nanos <= u64::MAX);
        assert!(!entry.kind.is_empty());
        assert!(entry.conn.is_some());
    }

    for i in 1..log.len() {
        assert!(log[i].sequence > log[i - 1].sequence);
    }
}
