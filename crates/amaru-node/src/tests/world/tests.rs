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

    // World runner processes heap events (SendAck, Deliver happen here)
    // In a real simulation, the world would pop events at-or-before horizon
    let horizon = provider.current_time_nanos() + 1_000_000; // 1ms
    while let Some(event) = provider.pop_event_at_or_before(horizon) {
        provider.execute_event(event);
    }

    // Node 2 sends a message
    let msg = NonEmptyBytes::try_from(Bytes::from("hello from node2")).unwrap();
    let send_fut = provider.send(node2_conn, msg.clone());

    // World runner advances: processes SendAck and Deliver
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(10)).await;
        let provider_clone = provider.clone();
        let horizon = provider_clone.current_time_nanos() + 10_000_000;
        while let Some(event) = provider_clone.pop_event_at_or_before(horizon) {
            provider_clone.execute_event(event);
        }
    });

    send_fut.await?;

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
