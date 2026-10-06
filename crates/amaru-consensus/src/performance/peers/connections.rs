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

//! Live bearers and the other population facts the peer-tracking methods record.
//!
//! Claim clearing on the last close uses the existing availability clear: scores and reputation
//! stay, tips go.

use std::{net::SocketAddr, time::Duration};

use amaru_kernel::Peer;
use amaru_ouroboros::{CloseReason, ConnectionId, ConnectionRecord, LocalUse, ObservedAt};
use amaru_pure_stage::Instant;

use super::PeerPerformance;

#[derive(Debug)]
pub(super) struct LiveConnection {
    pub(super) record: ConnectionRecord,
    pub(super) use_applied_at: Option<ObservedAt>,
}

#[derive(Debug)]
pub(super) struct CloseRecord {
    pub(super) conn_id: ConnectionId,
    pub(super) reason: CloseReason,
    pub(super) at: ObservedAt,
}

#[derive(Debug)]
pub(super) struct ShareRequests {
    pub(super) count: u32,
    pub(super) last_amount: u8,
    pub(super) last_at: ObservedAt,
}

/// Latest intersection-not-found mark for one peer.
#[derive(Debug)]
pub(super) struct UninterestingRecord {
    pub(super) conn_id: ConnectionId,
    pub(super) after_rollback: bool,
    pub(super) generation: u64,
}

pub(crate) fn instant_of(at: ObservedAt) -> Instant {
    Instant::at_offset(at.elapsed, at.global_epoch_offset)
}

impl PeerPerformance {
    pub fn record_connection_established(&mut self, conn: ConnectionRecord, at: ObservedAt) {
        let peer = conn.peer;
        let advertisable = conn.advertisable;
        self.connections.insert(conn.conn_id, LiveConnection { record: conn, use_applied_at: None });
        self.record_advertisability(peer, advertisable, instant_of(at));
        self.bump_generation();
    }

    /// Forget a bearer this map recorded for `peer`.
    ///
    /// A close for an unknown id, or for a different peer than the one stored under that id,
    /// changes nothing. The last remaining bearer clears claims.
    pub fn record_connection_closed(&mut self, peer: Peer, conn_id: ConnectionId, reason: CloseReason, at: ObservedAt) {
        let Some(live) = self.connections.get(&conn_id) else {
            return;
        };
        if live.record.peer != peer {
            return;
        }
        self.connections.remove(&conn_id);
        self.last_close.insert(peer, CloseRecord { conn_id, reason, at });
        let still_live = self.connections.values().any(|live| live.record.peer == peer);
        if !still_live {
            self.clear_availability(&peer);
        }
        self.drop_uninteresting_if_bearer_gone(peer);
        self.bump_generation();
    }

    pub fn record_connect_failed(&mut self, peer: Peer, at: ObservedAt) {
        self.last_connect_failure.insert(peer, at);
        self.record_connection_failure(peer, instant_of(at));
        self.bump_generation();
    }

    pub fn record_local_use_applied(&mut self, peer: Peer, conn_id: ConnectionId, local_use: LocalUse, at: ObservedAt) {
        let Some(live) = self.connections.get_mut(&conn_id) else {
            return;
        };
        if live.record.peer != peer {
            return;
        }
        live.record.local_use = local_use;
        live.use_applied_at = Some(at);
        self.bump_generation();
    }

    pub fn record_keepalive_sample(&mut self, peer: Peer, rtt: Duration, at: ObservedAt) {
        self.record_keepalive_rtt(peer, rtt, instant_of(at));
    }

    pub fn record_shared_peers(
        &mut self,
        from: &Peer,
        addrs: &[SocketAddr],
        at: ObservedAt,
    ) -> super::SharedIngestResult {
        self.last_shared_at.insert(*from, at);
        self.ingest_shared_peers(from, addrs)
    }

    /// Keep one mark per peer, at the generation this write just advanced.
    pub fn record_uninteresting(&mut self, peer: Peer, conn_id: ConnectionId, after_rollback: bool, _at: ObservedAt) {
        self.bump_generation();
        self.uninteresting.insert(peer, UninterestingRecord { conn_id, after_rollback, generation: self.generation });
    }

    fn drop_uninteresting_if_bearer_gone(&mut self, peer: Peer) {
        let Some(mark) = self.uninteresting.get(&peer) else {
            return;
        };
        let live =
            self.connections.values().any(|live| live.record.peer == peer && live.record.conn_id == mark.conn_id);
        if !live {
            self.uninteresting.remove(&peer);
        }
    }

    pub fn record_share_request_served(&mut self, requester: Peer, amount: u8, at: ObservedAt) {
        let entry = self.share_requests.entry(requester).or_insert(ShareRequests {
            count: 0,
            last_amount: amount,
            last_at: at,
        });
        entry.count = entry.count.saturating_add(1);
        entry.last_amount = amount;
        entry.last_at = at;
    }

    pub fn connection(&self, conn_id: ConnectionId) -> Option<&ConnectionRecord> {
        self.connections.get(&conn_id).map(|live| &live.record)
    }

    pub fn use_applied_at(&self, conn_id: ConnectionId) -> Option<ObservedAt> {
        self.connections.get(&conn_id).and_then(|live| live.use_applied_at)
    }

    pub fn last_close(&self, peer: &Peer) -> Option<(ConnectionId, CloseReason, ObservedAt)> {
        self.last_close.get(peer).map(|close| (close.conn_id, close.reason, close.at))
    }

    pub fn last_connect_failure(&self, peer: &Peer) -> Option<ObservedAt> {
        self.last_connect_failure.get(peer).copied()
    }

    pub fn last_shared_at(&self, peer: &Peer) -> Option<ObservedAt> {
        self.last_shared_at.get(peer).copied()
    }

    pub fn share_requests(&self, peer: &Peer) -> Option<(u32, u8, ObservedAt)> {
        self.share_requests.get(peer).map(|row| (row.count, row.last_amount, row.last_at))
    }

    pub fn query_share_peers(&self, requester: &Peer, amount: u8, now: ObservedAt) -> Vec<SocketAddr> {
        self.select_share_peers(requester, amount, instant_of(now))
    }
}
