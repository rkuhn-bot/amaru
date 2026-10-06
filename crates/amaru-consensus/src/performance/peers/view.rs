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

//! Cheap copy of the population facts peer selection reconciles against.

use std::collections::BTreeMap;

use amaru_kernel::Peer;
use amaru_ouroboros::{ConnectionDirection, ConnectionId, LocalUse, ObservedAt};

use super::PeerPerformance;

/// One live bearer, with the local use the connection task has applied.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ViewConnection {
    pub peer: Peer,
    pub conn_id: ConnectionId,
    pub direction: ConnectionDirection,
    pub full_duplex_capable: bool,
    pub full_duplex: bool,
    pub advertisable: bool,
    pub local_use: LocalUse,
}

/// Population snapshot. `None` from a query means the generation has not moved.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct PeerView {
    pub generation: u64,
    pub connections: Vec<ViewConnection>,
    pub connect_failures: BTreeMap<Peer, ObservedAt>,
}

impl PeerPerformance {
    /// Copy live bearers and dial failures when `since_generation` is behind.
    ///
    /// Returns `None` when nothing this view carries has changed, so the caller can skip a round.
    pub fn query_peer_view(&self, since_generation: u64) -> Option<PeerView> {
        if since_generation >= self.generation {
            return None;
        }
        let mut connections = Vec::with_capacity(self.connections.len());
        for live in self.connections.values() {
            let record = &live.record;
            connections.push(ViewConnection {
                peer: record.peer,
                conn_id: record.conn_id,
                direction: record.direction,
                full_duplex_capable: record.full_duplex_capable,
                full_duplex: record.full_duplex,
                advertisable: record.advertisable,
                local_use: record.local_use,
            });
        }
        connections.sort_by(|left, right| left.conn_id.cmp(&right.conn_id).then(left.peer.cmp(&right.peer)));
        Some(PeerView { generation: self.generation, connections, connect_failures: self.last_connect_failure.clone() })
    }
}
