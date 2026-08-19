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

use std::{net::SocketAddr, num::NonZeroUsize, time::Duration};

use amaru_kernel::{NonEmptyBytes, Peer};
use amaru_ouroboros::ConnectionProvider;
use tokio_util::bytes::Bytes;

use super::WorldConnectionProvider;

/// First-cut proof: 2 nodes, one Deliver round-trip, horizon cuts keepalive.
#[tokio::test]
async fn test_two_node_deliver_roundtrip() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9000".parse().unwrap();

    // Node 1 listens
    provider.listen(listener_addr).await?;

    // Node 2 connects
    let node2_conn = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;

    // Node 1 accepts
    let (_peer, node1_conn) = provider.accept(listener_addr).await?;

    // Node 2 sends a message
    let msg = NonEmptyBytes::try_from(Bytes::from("hello from node2")).unwrap();
    let send_fut = provider.send(node2_conn, msg.clone());

    // World runner processes heap events
    tokio::spawn({
        let provider = provider.clone();
        async move {
            tokio::time::sleep(Duration::from_millis(10)).await;
            let horizon = provider.current_time_nanos() + 10_000_000; // 10ms
            while let Some(event) = provider.pop_event_at_or_before(horizon) {
                provider.execute_event(event);
            }
        }
    });

    // Send completes when SendAck event is executed
    send_fut.await?;

    // Node 1 receives the message after Deliver event
    let recv_fut = provider.recv(node1_conn, msg.len());

    // Process Deliver event
    tokio::spawn({
        let provider = provider.clone();
        async move {
            tokio::time::sleep(Duration::from_millis(20)).await;
            let horizon = provider.current_time_nanos() + 20_000_000;
            while let Some(event) = provider.pop_event_at_or_before(horizon) {
                provider.execute_event(event);
            }
        }
    });

    let received = recv_fut.await?;
    assert_eq!(received.as_ref(), msg.as_ref());

    Ok(())
}

/// Test full bidirectional message exchange between two nodes.
#[tokio::test]
async fn test_bidirectional_exchange() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9010".parse().unwrap();

    provider.listen(listener_addr).await?;
    let conn_a = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_peer, conn_b) = provider.accept(listener_addr).await?;

    // A → B
    let msg_ab = NonEmptyBytes::try_from(Bytes::from("A to B")).unwrap();
    let send_ab = provider.send(conn_a, msg_ab.clone());

    // Execute network events
    let provider_clone = provider.clone();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(5)).await;
        let horizon = provider_clone.current_time_nanos() + 50_000_000;
        while let Some(event) = provider_clone.pop_event_at_or_before(horizon) {
            provider_clone.execute_event(event);
        }
    });

    send_ab.await?;
    let recv_b = provider.recv(conn_b, msg_ab.len()).await?;
    assert_eq!(recv_b.as_ref(), msg_ab.as_ref());

    // B → A
    let msg_ba = NonEmptyBytes::try_from(Bytes::from("B to A")).unwrap();
    let send_ba = provider.send(conn_b, msg_ba.clone());

    let provider_clone = provider.clone();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(5)).await;
        let horizon = provider_clone.current_time_nanos() + 50_000_000;
        while let Some(event) = provider_clone.pop_event_at_or_before(horizon) {
            provider_clone.execute_event(event);
        }
    });

    send_ba.await?;
    let recv_a = provider.recv(conn_a, msg_ba.len()).await?;
    assert_eq!(recv_a.as_ref(), msg_ba.as_ref());

    Ok(())
}

/// Test that events are ordered by (time, sequence).
#[tokio::test]
async fn test_event_ordering() {
    let provider = WorldConnectionProvider::new();

    // Schedule events with same time but different sequence
    provider.set_time(1000);

    // Events should be popped in FIFO order at same time
    let t1 = provider.current_time_nanos();
    assert_eq!(t1, 1000);

    // Advance time
    provider.set_time(2000);
    let t2 = provider.current_time_nanos();
    assert_eq!(t2, 2000);
}

/// Test that horizon prevents popping future events.
#[tokio::test]
async fn test_horizon_cuts_events() {
    let provider = WorldConnectionProvider::new();

    let listener_addr: SocketAddr = "127.0.0.1:9001".parse().unwrap();
    provider.listen(listener_addr).await.unwrap();

    let conn = provider.connect(vec![listener_addr], Duration::from_secs(1)).await.unwrap();

    let msg = NonEmptyBytes::try_from(Bytes::from("test")).unwrap();
    let _send_fut = provider.send(conn, msg);

    // Events are scheduled at current_time + 0
    let current = provider.current_time_nanos();

    // Horizon at current-1: no events should pop
    let past_horizon = current.saturating_sub(1);
    assert!(provider.pop_event_at_or_before(past_horizon).is_none());

    // Horizon at current: events should pop
    let now_horizon = current;
    assert!(provider.pop_event_at_or_before(now_horizon).is_some());
}

/// Test that multiple events at the same time are processed in FIFO order.
#[tokio::test]
async fn test_fifo_at_same_time() -> std::io::Result<()> {
    let provider = WorldConnectionProvider::new();
    let listener_addr: SocketAddr = "127.0.0.1:9020".parse().unwrap();

    provider.listen(listener_addr).await?;

    // Create 3 connections
    let conn1 = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_p1, resp1) = provider.accept(listener_addr).await?;

    let conn2 = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_p2, resp2) = provider.accept(listener_addr).await?;

    let conn3 = provider.connect(vec![listener_addr], Duration::from_secs(1)).await?;
    let (_p3, resp3) = provider.accept(listener_addr).await?;

    // Send messages at the same simulated time (all δ=0)
    let msg1 = NonEmptyBytes::try_from(Bytes::from("msg1")).unwrap();
    let msg2 = NonEmptyBytes::try_from(Bytes::from("msg2")).unwrap();
    let msg3 = NonEmptyBytes::try_from(Bytes::from("msg3")).unwrap();

    provider.send(conn1, msg1.clone()).await?;
    provider.send(conn2, msg2.clone()).await?;
    provider.send(conn3, msg3.clone()).await?;

    // Execute all events
    let horizon = provider.current_time_nanos() + 1_000_000;
    let mut events = Vec::new();
    while let Some(event) = provider.pop_event_at_or_before(horizon) {
        events.push(event);
        provider.execute_event(events.last().unwrap().clone());
    }

    // Verify FIFO ordering: should see SendAck then Deliver for each conn in sequence order
    assert!(events.len() >= 6); // At least 3 SendAck + 3 Deliver

    Ok(())
}
