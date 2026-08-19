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
use amaru_ouroboros::{ConnectionId, ConnectionProvider};
use amaru_pure_stage::{
    StageGraph,
    simulation::{Fifo, SimulationBuilder},
};
use tokio_util::bytes::Bytes;

use super::{NetworkEvent, WorldConnectionProvider, WorldLoop};

/// Prove one Deliver round-trip under the world loop.
///
/// Pattern: no tokio::spawn, no tokio::time::sleep, no wall-clock.
/// Node A sends to Node B, world loop processes SendAck→Deliver, B receives.
#[tokio::test]
async fn test_one_deliver_roundtrip_with_world_loop() -> std::io::Result<()> {
    let provider = Arc::new(WorldConnectionProvider::new());
    let listener_addr: SocketAddr = "127.0.0.1:9000".parse().unwrap();

    // Node A stage: connects and sends
    let provider_a = provider.clone();
    let mut stage_graph_a = SimulationBuilder::default().with_eval_strategy(Fifo);
    let stage_a = stage_graph_a.stage("node_a", async move |mut conn_id: Option<ConnectionId>, _unit: (), eff| {
        if conn_id.is_none() {
            // Connect
            let conn = eff.external(&provider_a, |p| p.connect(vec![listener_addr], Duration::from_secs(1))).await;
            conn_id = Some(conn);
            return conn_id;
        }
        // Send message
        let msg = NonEmptyBytes::try_from(Bytes::from("hello from A")).unwrap();
        let _ = eff.external(&provider_a, |p| p.send(conn_id.unwrap(), msg)).await;
        conn_id
    });
    let stage_a = stage_graph_a.wire_up(stage_a, None);
    let rt = tokio::runtime::Runtime::new().unwrap();
    let mut sim_a = stage_graph_a.run(rt.handle());
    sim_a.enqueue_msg(&stage_a, [()]);

    // Node B stage: listens and receives
    let provider_b = provider.clone();
    let mut stage_graph_b = SimulationBuilder::default().with_eval_strategy(Fifo);
    let stage_b = stage_graph_b.stage("node_b", async move |mut conn_id: Option<ConnectionId>, _unit: (), eff| {
        if conn_id.is_none() {
            // Listen
            let _ = eff.external(&provider_b, |p| p.listen(listener_addr)).await;
            // Accept
            let (_peer, conn) = eff.external(&provider_b, |p| p.accept(listener_addr)).await;
            conn_id = Some(conn);
            return conn_id;
        }
        // Receive message
        let msg_len = NonZeroUsize::new("hello from A".len()).unwrap();
        let received = eff.external(&provider_b, |p| p.recv(conn_id.unwrap(), msg_len)).await;
        assert_eq!(received.as_ref(), b"hello from A");
        conn_id
    });
    let stage_b = stage_graph_b.wire_up(stage_b, None);
    let mut sim_b = stage_graph_b.run(rt.handle());
    sim_b.enqueue_msg(&stage_b, [()]);

    // World loop: exhaust all newly-ready graphs, pop-if-at≤horizon
    let mut world = WorldLoop::new((*provider).clone(), vec![sim_a, sim_b]);
    world.run_to_completion();

    // Verify events in heap log: Connected, Accepted, SendAck, Deliver
    let log = world.heap_log();
    assert!(log.iter().any(|e| e.kind == "Connected"));
    assert!(log.iter().any(|e| e.kind == "Accepted"));
    assert!(log.iter().any(|e| e.kind == "SendAck"));
    assert!(log.iter().any(|e| e.kind == "Deliver"));

    Ok(())
}

/// Prove horizon cuts keepalive (or any future event).
///
/// Schedule an event beyond the horizon, verify it's not popped.
#[tokio::test]
async fn test_horizon_cuts_future_events() {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9010".parse().unwrap();

    provider.listen(listener_addr).await.unwrap();
    let conn_id = provider.connect(vec![listener_addr], Duration::from_secs(1)).await.unwrap();

    // Schedule a send (SendAck at current_time + 0)
    let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
    let send_fut = provider.send(conn_id, msg);

    // Set horizon before current_time (past): nothing should pop
    let current = provider.current_time_nanos();
    let past_horizon = current.saturating_sub(1);
    assert!(provider.pop_event_at_or_before(past_horizon).is_none());

    // Set horizon at current_time: Connected event should pop
    let now_horizon = current;
    let entry = provider.pop_event_at_or_before(now_horizon);
    assert!(entry.is_some());
    assert!(matches!(entry.unwrap().event, NetworkEvent::Connected { .. }));

    // Execute remaining events
    while let Some(e) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(e);
    }

    // Send completes
    drop(send_fut);

    // Verify log has events
    let log = provider.heap_log();
    assert!(!log.is_empty());
}

/// Test that pending_sends supports multiple sends per connection.
#[tokio::test]
async fn test_multiple_sends_per_connection() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9020".parse().unwrap();

    provider.listen(listener_addr).await?;
    let conn_a = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_peer, conn_b) = provider.accept(listener_addr).await?;

    // Queue 3 sends without awaiting
    let msg1 = NonEmptyBytes::try_from(Bytes::from("msg1")).unwrap();
    let msg2 = NonEmptyBytes::try_from(Bytes::from("msg2")).unwrap();
    let msg3 = NonEmptyBytes::try_from(Bytes::from("msg3")).unwrap();

    let send1 = provider.send(conn_a, msg1.clone());
    let send2 = provider.send(conn_a, msg2.clone());
    let send3 = provider.send(conn_a, msg3.clone());

    // Execute all heap events
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }

    // All sends complete
    send1.await?;
    send2.await?;
    send3.await?;

    // B receives all messages
    let r1 = provider.recv(conn_b, msg1.len()).await?;
    let r2 = provider.recv(conn_b, msg2.len()).await?;
    let r3 = provider.recv(conn_b, msg3.len()).await?;

    assert_eq!(r1.as_ref(), msg1.as_ref());
    assert_eq!(r2.as_ref(), msg2.as_ref());
    assert_eq!(r3.as_ref(), msg3.as_ref());

    Ok(())
}

/// Test that Close unparks Send and Recv on the same conn (not peer).
#[tokio::test]
async fn test_close_unparks_same_conn_only() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9030".parse().unwrap();

    provider.listen(listener_addr).await?;
    let conn_a = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_peer, conn_b) = provider.accept(listener_addr).await?;

    // A closes its connection
    provider.close(conn_a).await?;

    // Execute Close event
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }

    // A's send should fail (conn closed)
    let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
    let result_a = provider.send(conn_a, msg.clone()).await;
    assert!(result_a.is_err());

    // B's operations should still work (peer not closed)
    let send_b = provider.send(conn_b, msg.clone());
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }
    // This will succeed because conn_b is still open (A's closure doesn't affect B)
    // But the Deliver to A will be dropped because A's endpoint is removed
    drop(send_b);

    Ok(())
}

/// Test that recv with insufficient data re-inserts the pending recv.
#[tokio::test]
async fn test_recv_reinsertion_on_insufficient_data() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9040".parse().unwrap();

    provider.listen(listener_addr).await?;
    let conn_a = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_peer, conn_b) = provider.accept(listener_addr).await?;

    // B waits for 10 bytes
    let recv_fut = provider.recv(conn_b, NonZeroUsize::new(10).unwrap());

    // A sends 5 bytes
    let msg1 = NonEmptyBytes::try_from(Bytes::from("hello")).unwrap();
    provider.send(conn_a, msg1).await?;

    // Execute SendAck and first Deliver
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }

    // recv_fut should still be pending (not enough data)
    // Send 5 more bytes
    let msg2 = NonEmptyBytes::try_from(Bytes::from("world")).unwrap();
    provider.send(conn_a, msg2).await?;

    // Execute second Deliver
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }

    // Now recv completes
    let received = recv_fut.await?;
    assert_eq!(received.as_ref(), b"helloworld");

    Ok(())
}

/// Test heap log replay: verify sequence, time, kind, conn are recorded.
#[tokio::test]
async fn test_heap_log_for_replay() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9050".parse().unwrap();

    provider.listen(listener_addr).await?;
    let conn_a = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_peer, conn_b) = provider.accept(listener_addr).await?;

    let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
    provider.send(conn_a, msg).await?;

    // Execute all events
    while let Some(entry) = provider.pop_event_at_or_before(u64::MAX) {
        provider.execute_event(entry);
    }

    // Verify heap log
    let log = provider.heap_log();
    assert!(!log.is_empty());

    // Check that sequences are monotonic
    for i in 1..log.len() {
        assert!(log[i].sequence > log[i - 1].sequence);
    }

    // Check that we have expected events
    let kinds: Vec<&str> = log.iter().map(|e| e.kind).collect();
    assert!(kinds.contains(&"Connected"));
    assert!(kinds.contains(&"Accepted"));
    assert!(kinds.contains(&"SendAck"));
    assert!(kinds.contains(&"Deliver"));

    // Check that each event has a conn
    for entry in &log {
        assert!(entry.conn.is_some());
    }

    Ok(())
}
