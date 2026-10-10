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

//! Retention of per-peer rows and the caps on learned addresses and those rows.
//!
//! A write goes through [`PeerPerformance::touch`] or [`PeerPerformance::write_peer`]. That records
//! the latest observation instant (it only moves forward) and seats the peer: a live bearer, a
//! static, ledger, or snapshot candidate, or an active ban stub stays out of the dead sets. Losing
//! the last of those moves the peer into a dead set keyed by that instant. Becoming live again
//! takes it back out.
//!
//! The sweep only pops those dead sets. Expired entries come off the front. While over the record
//! cap, the oldest unverified dead entries come off the front too. Established peers stay until
//! retention. There is no cursor and no fixed batch.
//!
//! A shared address is as fresh as the later of when it was first learned and the peer's activity.
//! Repeating a share reply does not move the learned instant. The same live/dead split applies.

#[cfg(test)]
use std::net::SocketAddr;
use std::{collections::BTreeSet, time::Duration};

use amaru_kernel::{Peer, PeerCandidate};
use amaru_pure_stage::Instant;

use super::{PeerPerformance, record::PeerState};

/// How long an untouched, unprotected row is kept.
pub const PEER_RECORD_RETENTION: Duration = Duration::from_secs(24 * 60 * 60);

/// How long a banned peer's reputation stub is kept after the mark.
///
/// While peer selection still lists the peer as protected, each sweep extends this by the same
/// duration, so the stub outlasts the ban.
pub const BAN_STUB_GRACE: Duration = Duration::from_secs(24 * 60 * 60);

/// Learned share-reply addresses. Newcomers past this cap are dropped on ingest.
pub const SHARED_PEERS_CAP: usize = 4096;

/// Per-peer rows. A live bearer may briefly exceed it; the sweep frees unverified dead slots.
pub const PEER_RECORD_CAP: usize = 8192;

/// What one sweep removed. It does not bump [`PeerPerformance::generation`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sweep {
    pub removed_records: usize,
    pub removed_shared: usize,
}

impl PeerPerformance {
    pub fn peer_record_count(&self) -> usize {
        self.activity.len()
    }

    /// Drop expired dead rows, then the oldest unverified dead rows while over a cap.
    ///
    /// Protected peers and candidates passed in are marked live for this sweep and are not
    /// candidates. An adversarial peer among them has its ban stub extended by [`BAN_STUB_GRACE`].
    pub fn sweep(
        &mut self,
        now: Instant,
        protected_peers: &BTreeSet<Peer>,
        protected_candidates: &BTreeSet<PeerCandidate>,
    ) -> Sweep {
        self.release_external_holds(protected_peers, protected_candidates);
        for peer in protected_peers {
            self.shelter_peer(*peer, now);
        }
        for candidate in protected_candidates {
            self.shelter_candidate(candidate, now);
        }
        let mut removed_records = 0usize;
        let mut removed_shared = 0usize;
        self.expire_stubs(now, &mut removed_records);
        self.pop_expired_peers(now, &mut removed_records);
        self.pop_record_cap(&mut removed_records);
        self.pop_expired_shared(now, &mut removed_shared);
        self.pop_shared_cap(&mut removed_shared);
        Sweep { removed_records, removed_shared }
    }

    /// Record an observation and seat the peer. The instant only moves forward.
    pub(super) fn touch(&mut self, peer: Peer, at: Instant) {
        self.unseat_peer(peer);
        self.unseat_shared_peer(peer);
        self.advance_activity(peer, at);
        self.seat_peer(peer);
        self.seat_shared_peer(peer);
    }

    /// Update the peer row, then [`Self::touch`]. Unseats before `update` so a new ban stub is indexed.
    pub(super) fn write_peer(&mut self, peer: Peer, at: Instant, update: impl FnOnce(&mut PeerState)) {
        self.unseat_peer(peer);
        self.unseat_shared_peer(peer);
        update(self.peers.entry(peer).or_default());
        self.advance_activity(peer, at);
        self.seat_peer(peer);
        self.seat_shared_peer(peer);
    }

    /// Remember a learned address. A repeat does not move the learned instant.
    pub(super) fn remember_shared(&mut self, candidate: PeerCandidate, at: Instant) {
        if self.shared_learned.contains_key(&candidate) {
            return;
        }
        self.shared_peers.insert(candidate.clone());
        self.shared_learned.insert(candidate.clone(), at);
        self.seat_shared(&candidate);
    }

    /// Ledger membership changed. Peers that already have a row move between held and dead.
    pub(super) fn reclassify_source_members(&mut self, previous: &BTreeSet<PeerCandidate>) {
        let mut peers = BTreeSet::new();
        for candidate in previous.iter().chain(self.ledger_candidates.iter()) {
            if let Some(peer) = candidate.as_peer()
                && self.activity.contains_key(&peer)
            {
                peers.insert(peer);
            }
        }
        for peer in peers {
            self.reseat(peer);
        }
    }

    pub(super) fn clear_peer_claims(&mut self, peer: &Peer) {
        if let Some(state) = self.peers.get_mut(peer) {
            state.tips.clear();
        }
        let Some(hashes) = self.claim_index.remove(peer) else {
            return;
        };
        for hash in hashes {
            let remove_hash = match self.direct.get_mut(&hash) {
                Some(claimants) => {
                    claimants.remove(peer);
                    claimants.is_empty()
                }
                None => false,
            };
            if remove_hash {
                self.direct.remove(&hash);
            }
        }
    }

    fn reseat(&mut self, peer: Peer) {
        self.unseat_peer(peer);
        self.unseat_shared_peer(peer);
        self.seat_peer(peer);
        self.seat_shared_peer(peer);
    }

    fn advance_activity(&mut self, peer: Peer, at: Instant) {
        match self.activity.get(&peer).copied() {
            Some(prev) if at <= prev => {}
            _ => {
                self.activity.insert(peer, at);
            }
        }
    }

    fn release_external_holds(
        &mut self,
        protected_peers: &BTreeSet<Peer>,
        protected_candidates: &BTreeSet<PeerCandidate>,
    ) {
        let held = std::mem::take(&mut self.held_external);
        for peer in held {
            let socket = PeerCandidate::from(peer);
            if protected_peers.contains(&peer) || protected_candidates.contains(&socket) {
                self.held_external.insert(peer);
            } else {
                self.reseat(peer);
            }
        }
        let shared = std::mem::take(&mut self.shared_held);
        for candidate in shared {
            let peer_protected = candidate.as_peer().is_some_and(|peer| protected_peers.contains(&peer));
            if protected_candidates.contains(&candidate) || peer_protected || self.shared_internally_held(&candidate) {
                self.shared_held.insert(candidate);
            } else {
                self.seat_shared(&candidate);
            }
        }
    }

    fn shelter_peer(&mut self, peer: Peer, now: Instant) {
        if !self.activity.contains_key(&peer) {
            return;
        }
        self.unseat_peer(peer);
        if self.peers.get(&peer).is_some_and(|state| state.adversarial) {
            self.refresh_ban_stub(peer, now);
        }
        if self.stub_indexed(peer) {
            self.seat_shared_peer(peer);
            return;
        }
        if !self.internally_held(peer) {
            self.held_external.insert(peer);
        }
        self.seat_shared_peer(peer);
    }

    fn shelter_candidate(&mut self, candidate: &PeerCandidate, now: Instant) {
        if self.shared_learned.contains_key(candidate) {
            self.unseat_shared(candidate);
            self.shared_held.insert(candidate.clone());
        }
        if let Some(peer) = candidate.as_peer() {
            self.shelter_peer(peer, now);
        }
    }

    fn expire_stubs(&mut self, now: Instant, removed: &mut usize) {
        while let Some((until, peer)) = self.stubs.first().copied() {
            if until > now {
                break;
            }
            self.stubs.remove(&(until, peer));
            if self.internally_held(peer) || self.held_external.contains(&peer) {
                continue;
            }
            let Some(at) = self.activity.get(&peer).copied() else {
                continue;
            };
            self.insert_dead(peer, at);
            if self.activity_expired(at, now) {
                self.remove_dead_key(peer, at);
                self.forget_peer(peer);
                *removed += 1;
            }
        }
    }

    fn pop_expired_peers(&mut self, now: Instant, removed: &mut usize) {
        self.pop_expired_peer_set(now, true, removed);
        self.pop_expired_peer_set(now, false, removed);
    }

    fn pop_expired_peer_set(&mut self, now: Instant, established: bool, removed: &mut usize) {
        loop {
            let front = if established {
                self.dead_established.first().copied()
            } else {
                self.dead_unverified.first().copied()
            };
            let Some((at, peer)) = front else {
                break;
            };
            if !self.activity_expired(at, now) {
                break;
            }
            self.remove_dead_key(peer, at);
            if self.activity.get(&peer).copied() == Some(at) && self.droppable(peer) {
                self.forget_peer(peer);
                *removed += 1;
            }
        }
    }

    fn pop_record_cap(&mut self, removed: &mut usize) {
        while self.activity.len() > PEER_RECORD_CAP {
            let Some((at, peer)) = self.dead_unverified.first().copied() else {
                break;
            };
            self.dead_unverified.remove(&(at, peer));
            if self.activity.get(&peer).copied() == Some(at) && self.droppable(peer) {
                self.forget_peer(peer);
                *removed += 1;
            }
        }
    }

    fn pop_expired_shared(&mut self, now: Instant, removed: &mut usize) {
        self.pop_expired_shared_set(now, true, removed);
        self.pop_expired_shared_set(now, false, removed);
    }

    fn pop_expired_shared_set(&mut self, now: Instant, established: bool, removed: &mut usize) {
        loop {
            let front = if established {
                self.shared_dead_established.first().cloned()
            } else {
                self.shared_dead_unverified.first().cloned()
            };
            let Some((useful, candidate)) = front else {
                break;
            };
            if !self.activity_expired(useful, now) {
                break;
            }
            self.remove_shared_dead_key(&candidate, useful);
            if self.drop_shared_if_current(&candidate, useful) {
                *removed += 1;
            }
        }
    }

    fn pop_shared_cap(&mut self, removed: &mut usize) {
        while self.shared_peers.len() > SHARED_PEERS_CAP {
            let Some((useful, candidate)) = self.shared_dead_unverified.first().cloned() else {
                break;
            };
            self.shared_dead_unverified.remove(&(useful, candidate.clone()));
            if self.drop_shared_if_current(&candidate, useful) {
                *removed += 1;
            }
        }
    }

    fn droppable(&self, peer: Peer) -> bool {
        !self.internally_held(peer) && !self.held_external.contains(&peer) && !self.stub_indexed(peer)
    }

    fn activity_expired(&self, at: Instant, now: Instant) -> bool {
        now.saturating_since(at) >= PEER_RECORD_RETENTION
    }

    fn insert_dead(&mut self, peer: Peer, at: Instant) {
        if self.is_established_peer(peer) {
            self.dead_established.insert((at, peer));
        } else {
            self.dead_unverified.insert((at, peer));
        }
    }

    fn remove_dead_key(&mut self, peer: Peer, at: Instant) {
        self.dead_unverified.remove(&(at, peer));
        self.dead_established.remove(&(at, peer));
    }

    fn unseat_peer(&mut self, peer: Peer) {
        if let Some(at) = self.activity.get(&peer).copied() {
            self.remove_dead_key(peer, at);
        }
        if let Some(until) = self.peers.get(&peer).and_then(|state| state.stub_until) {
            self.stubs.remove(&(until, peer));
        }
        self.held_external.remove(&peer);
    }

    fn seat_peer(&mut self, peer: Peer) {
        if self.internally_held(peer) {
            return;
        }
        let Some(at) = self.activity.get(&peer).copied() else {
            return;
        };
        if let Some(until) = self.peers.get(&peer).and_then(|state| state.stub_until)
            && until > at
        {
            self.stubs.insert((until, peer));
            return;
        }
        self.insert_dead(peer, at);
    }

    fn internally_held(&self, peer: Peer) -> bool {
        self.has_live_bearer(peer) || self.is_source_protected(peer)
    }

    fn has_live_bearer(&self, peer: Peer) -> bool {
        self.connections.values().any(|live| live.record.peer == peer)
    }

    fn is_source_protected(&self, peer: Peer) -> bool {
        let socket = PeerCandidate::from(peer);
        self.static_peers.contains(&socket)
            || self.snapshot_candidates.contains(&socket)
            || self.ledger_candidates.contains(&socket)
    }

    fn stub_indexed(&self, peer: Peer) -> bool {
        self.peers
            .get(&peer)
            .and_then(|state| state.stub_until)
            .is_some_and(|until| self.stubs.contains(&(until, peer)))
    }

    fn refresh_ban_stub(&mut self, peer: Peer, now: Instant) {
        let Some(state) = self.peers.get_mut(&peer) else {
            return;
        };
        if !state.adversarial {
            return;
        }
        let until = now + BAN_STUB_GRACE;
        if state.stub_until.is_some_and(|existing| existing >= until) {
            if let Some(existing) = state.stub_until {
                self.stubs.insert((existing, peer));
            }
            return;
        }
        if let Some(old) = state.stub_until {
            self.stubs.remove(&(old, peer));
        }
        state.stub_until = Some(until);
        self.stubs.insert((until, peer));
    }

    fn shared_useful_at(&self, candidate: &PeerCandidate, learned: Instant) -> Instant {
        let Some(peer) = candidate.as_peer() else {
            return learned;
        };
        match self.activity.get(&peer).copied() {
            Some(at) if at > learned => at,
            _ => learned,
        }
    }

    fn shared_internally_held(&self, candidate: &PeerCandidate) -> bool {
        candidate.as_peer().is_some_and(|peer| self.internally_held(peer) || self.stub_indexed(peer))
    }

    fn unseat_shared_peer(&mut self, peer: Peer) {
        let candidate = PeerCandidate::from(peer);
        if self.shared_learned.contains_key(&candidate) {
            self.unseat_shared(&candidate);
        }
    }

    fn seat_shared_peer(&mut self, peer: Peer) {
        let candidate = PeerCandidate::from(peer);
        if self.shared_learned.contains_key(&candidate) {
            self.seat_shared(&candidate);
        }
    }

    fn unseat_shared(&mut self, candidate: &PeerCandidate) {
        if let Some(learned) = self.shared_learned.get(candidate).copied() {
            let useful = self.shared_useful_at(candidate, learned);
            self.remove_shared_dead_key(candidate, useful);
        }
        self.shared_held.remove(candidate);
    }

    fn seat_shared(&mut self, candidate: &PeerCandidate) {
        let Some(learned) = self.shared_learned.get(candidate).copied() else {
            return;
        };
        let useful = self.shared_useful_at(candidate, learned);
        if self.shared_internally_held(candidate)
            || candidate.as_peer().is_some_and(|peer| self.held_external.contains(&peer))
        {
            self.shared_held.insert(candidate.clone());
            return;
        }
        if self.candidate_is_established(candidate) {
            self.shared_dead_established.insert((useful, candidate.clone()));
        } else {
            self.shared_dead_unverified.insert((useful, candidate.clone()));
        }
    }

    fn remove_shared_dead_key(&mut self, candidate: &PeerCandidate, useful: Instant) {
        self.shared_dead_unverified.remove(&(useful, candidate.clone()));
        self.shared_dead_established.remove(&(useful, candidate.clone()));
    }

    fn drop_shared_if_current(&mut self, candidate: &PeerCandidate, useful: Instant) -> bool {
        let Some(learned) = self.shared_learned.get(candidate).copied() else {
            return false;
        };
        if self.shared_useful_at(candidate, learned) != useful {
            return false;
        }
        if self.shared_internally_held(candidate) || self.shared_held.contains(candidate) {
            self.shared_held.insert(candidate.clone());
            return false;
        }
        self.shared_peers.remove(candidate);
        self.shared_learned.remove(candidate);
        self.shared_held.remove(candidate);
        true
    }

    /// Handshake, a score change, a keep-alive sample, or a fetch success or timeout.
    fn is_established_peer(&self, peer: Peer) -> bool {
        self.peers.get(&peer).is_some_and(peer_is_established)
    }

    fn candidate_is_established(&self, candidate: &PeerCandidate) -> bool {
        candidate.as_peer().is_some_and(|peer| self.is_established_peer(peer))
    }

    fn forget_peer(&mut self, peer: Peer) {
        self.unseat_peer(peer);
        self.unseat_shared_peer(peer);
        self.clear_peer_claims(&peer);
        self.peers.remove(&peer);
        self.share_requests.remove(&peer);
        self.last_close.remove(&peer);
        self.last_connect_failure.remove(&peer);
        self.last_shared_at.remove(&peer);
        self.uninteresting.remove(&peer);
        self.peer_origin.remove(&peer);
        if let Some(candidates) = self.last_peer_by_peer.remove(&peer) {
            for candidate in candidates {
                if self.last_peer.get(&candidate).copied() == Some(peer) {
                    self.last_peer.remove(&candidate);
                }
            }
        }
        self.activity.remove(&peer);
        self.seat_shared_peer(peer);
    }

    /// Cap-sized dead sets whose entries are already past retention at `stale_at`.
    #[cfg(test)]
    pub fn testing_seed_eviction_cap(&mut self, stale_at: Instant, _fresh_at: Instant) {
        for n in 0..PEER_RECORD_CAP {
            self.testing_insert_idle_peer(Peer::for_test((n as u16).saturating_add(1)), stale_at);
        }
        for n in 0..SHARED_PEERS_CAP {
            self.testing_insert_shared(addr_from_port(20_000u16.saturating_add(n as u16)), stale_at);
        }
    }

    #[cfg(test)]
    pub fn testing_insert_idle_peer(&mut self, peer: Peer, at: Instant) {
        self.touch(peer, at);
    }

    #[cfg(test)]
    pub fn testing_set_activity(&mut self, peer: Peer, at: Instant) {
        self.unseat_peer(peer);
        self.unseat_shared_peer(peer);
        self.activity.insert(peer, at);
        self.seat_peer(peer);
        self.seat_shared_peer(peer);
    }

    #[cfg(test)]
    pub fn testing_insert_shared(&mut self, addr: SocketAddr, at: Instant) {
        let Ok(peer) = Peer::try_from(addr) else {
            return;
        };
        let candidate = PeerCandidate::from(peer);
        self.unseat_shared(&candidate);
        self.shared_peers.insert(candidate.clone());
        self.shared_learned.insert(candidate.clone(), at);
        self.seat_shared(&candidate);
    }

    #[cfg(test)]
    pub fn testing_stub_until(&self, peer: &Peer) -> Option<Instant> {
        self.peers.get(peer).and_then(|state| state.stub_until)
    }

    #[cfg(test)]
    pub fn testing_is_held(&self, peer: Peer) -> bool {
        self.activity.contains_key(&peer) && (self.internally_held(peer) || self.held_external.contains(&peer))
    }

    #[cfg(test)]
    pub fn testing_is_dead(&self, peer: Peer) -> bool {
        self.activity
            .get(&peer)
            .copied()
            .is_some_and(|at| self.dead_unverified.contains(&(at, peer)) || self.dead_established.contains(&(at, peer)))
    }

    #[cfg(test)]
    pub fn testing_is_dead_established(&self, peer: Peer) -> bool {
        self.activity.get(&peer).copied().is_some_and(|at| self.dead_established.contains(&(at, peer)))
    }
}

#[cfg(test)]
fn addr_from_port(port: u16) -> SocketAddr {
    SocketAddr::from(Peer::for_test(port))
}

fn peer_is_established(state: &PeerState) -> bool {
    state.ever_connected
        || state.scores.last_change.is_some()
        || state.scores.keepalive_rtt_latest.is_some()
        || state.scores.fetch_successes > 0
        || state.scores.fetch_timeouts > 0
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, net::SocketAddr, time::Duration};

    use amaru_kernel::{BlockHeight, HeaderHash, Peer, PeerCandidate, Point, Slot};
    use amaru_ouroboros::{
        CloseReason, ConnectionDirection, ConnectionId, ConnectionRecord, LocalUse, ObservedAt, RemoteInitiators,
    };
    use amaru_pure_stage::Instant;

    use super::{BAN_STUB_GRACE, PEER_RECORD_CAP, PEER_RECORD_RETENTION, SHARED_PEERS_CAP};
    use crate::performance::{PeerMix, PeerPerformance};

    fn t(secs: u64) -> Instant {
        Instant::at_offset(Duration::from_secs(secs), Duration::ZERO)
    }

    fn observed(secs: u64) -> ObservedAt {
        ObservedAt::new(Duration::from_secs(secs), Duration::ZERO)
    }

    fn hash(byte: u8) -> HeaderHash {
        HeaderHash::from([byte; 32])
    }

    fn tip(byte: u8, height: u64) -> Point {
        Point::Specific(Slot::from(height), hash(byte), BlockHeight::from(height))
    }

    fn addr(port: u16) -> SocketAddr {
        SocketAddr::from(Peer::for_test(port))
    }

    fn empty() -> (BTreeSet<Peer>, BTreeSet<PeerCandidate>) {
        (BTreeSet::new(), BTreeSet::new())
    }

    fn connect(peers: &mut PeerPerformance, peer: Peer, at: Instant) {
        let observed_at = ObservedAt::new(at.sim_elapsed(), Duration::ZERO);
        peers.record_connection_established(
            ConnectionRecord {
                peer,
                conn_id: ConnectionId::initial(),
                direction: ConnectionDirection::Outbound,
                full_duplex_capable: true,
                full_duplex: false,
                advertisable: true,
                local_use: LocalUse::None,
                remote_initiators: RemoteInitiators::default(),
                remote_use: LocalUse::None,
                established_at: observed_at,
            },
            observed_at,
        );
    }

    #[test]
    fn idle_peer_is_evicted_once_retention_elapses() {
        let mut peers = PeerPerformance::new();
        let who = Peer::for_test(1);
        let (protected_peers, protected_candidates) = empty();
        peers.record_header_announcement(who, tip(1, 1), None, t(1_000));
        peers.record_share_request_served(who, 4, observed(1_000));
        let generation = peers.generation();

        let before = t(1_000) + PEER_RECORD_RETENTION - Duration::from_secs(1);
        let kept = peers.sweep(before, &protected_peers, &protected_candidates);
        assert_eq!(kept.removed_records, 0);
        assert!(peers.share_flags(&who).is_some());
        assert_eq!(peers.direct_claimants(&hash(1)).len(), 1);

        let due = t(1_000) + PEER_RECORD_RETENTION;
        let gone = peers.sweep(due, &protected_peers, &protected_candidates);
        assert_eq!(gone.removed_records, 1);
        assert!(peers.share_flags(&who).is_none());
        assert!(peers.share_requests(&who).is_none());
        assert!(peers.direct_claimants(&hash(1)).is_empty());
        assert_eq!(peers.peer_record_count(), 0);
        assert_eq!(peers.generation(), generation);
    }

    #[test]
    fn protected_peers_are_kept() {
        let static_peer = Peer::for_test(1);
        let snapshot_peer = Peer::for_test(2);
        let ledger_peer = Peer::for_test(3);
        let live_peer = Peer::for_test(4);
        let banned = Peer::for_test(5);
        let dialing = Peer::for_test(6);
        let idle = Peer::for_test(7);
        let ancient = t(1_000);
        let now = ancient + PEER_RECORD_RETENTION + Duration::from_secs(1);
        let mut peers = PeerPerformance::with_sources(
            BTreeSet::from([PeerCandidate::from(static_peer)]),
            BTreeSet::from([PeerCandidate::from(snapshot_peer)]),
            BTreeSet::from([PeerCandidate::from(ledger_peer)]),
            PeerMix::default(),
        );
        for who in [static_peer, snapshot_peer, ledger_peer, live_peer, banned, dialing, idle] {
            peers.testing_insert_idle_peer(who, ancient);
        }
        connect(&mut peers, live_peer, ancient);
        peers.testing_set_activity(live_peer, ancient);
        peers.mark_adversarial(&banned, ancient);
        peers.testing_set_activity(banned, ancient - Duration::from_secs(48 * 60 * 60));
        let protected_peers = BTreeSet::from([banned]);
        let protected_candidates = BTreeSet::from([PeerCandidate::from(dialing)]);

        let sweep = peers.sweep(now, &protected_peers, &protected_candidates);
        assert_eq!(sweep.removed_records, 1);
        assert!(peers.share_flags(&static_peer).is_none());
        assert_eq!(peers.peer_record_count(), 6);
        for who in [static_peer, snapshot_peer, ledger_peer, live_peer, banned, dialing] {
            assert!(peers.activity_contains_for_test(who), "{who}");
        }
        assert!(!peers.activity_contains_for_test(idle));
        assert_eq!(peers.testing_stub_until(&banned), Some(now + BAN_STUB_GRACE));
        assert!(peers.connection(ConnectionId::initial()).is_some());
    }

    #[test]
    fn banned_stub_is_kept_through_the_ban_and_the_grace() {
        let mut peers = PeerPerformance::new();
        let who = Peer::for_test(8);
        let (protected_peers, protected_candidates) = empty();
        let marked = t(50_000);
        peers.mark_adversarial(&who, marked);
        peers.testing_set_activity(who, marked - Duration::from_secs(48 * 60 * 60));

        let during_ban = marked + Duration::from_secs(10 * 60);
        peers.sweep(during_ban, &protected_peers, &protected_candidates);
        assert!(peers.share_flags(&who).is_some_and(|flags| flags.adversarial));

        let almost = marked + BAN_STUB_GRACE - Duration::from_secs(1);
        peers.sweep(almost, &protected_peers, &protected_candidates);
        assert!(peers.share_flags(&who).is_some_and(|flags| flags.adversarial));
        assert_eq!(peers.testing_stub_until(&who), Some(marked + BAN_STUB_GRACE));

        let ended = marked + BAN_STUB_GRACE;
        peers.sweep(ended, &protected_peers, &protected_candidates);
        assert!(peers.share_flags(&who).is_none());
    }

    #[test]
    fn shared_cap_drops_newcomers_on_ingest_and_the_sweep_drops_the_oldest() {
        let mut peers = PeerPerformance::new();
        let donor = Peer::for_test(9);
        let learned = t(2_000);
        for port in 1..=SHARED_PEERS_CAP as u16 {
            peers.testing_insert_shared(addr(port), learned + Duration::from_secs(u64::from(port)));
        }
        let flood: Vec<SocketAddr> = (30_000..30_100).map(addr).collect();
        let ingested = peers.ingest_shared_peers(&donor, &flood, learned + Duration::from_secs(10_000));
        assert_eq!(ingested.added, 0);
        assert_eq!(ingested.dropped, flood.len());
        assert_eq!(peers.source_counts().shared_peers, SHARED_PEERS_CAP);
        assert!(!peers.shared_contains(&Peer::for_test(30_000)));

        for port in 1..101 {
            peers.testing_insert_shared(addr(40_000 + port), learned);
        }
        assert!(peers.source_counts().shared_peers > SHARED_PEERS_CAP);
        let (protected_peers, protected_candidates) = empty();
        let now = learned + Duration::from_secs(2);
        let sweep = peers.sweep(now, &protected_peers, &protected_candidates);
        assert!(sweep.removed_shared >= 100);
        assert_eq!(peers.source_counts().shared_peers, SHARED_PEERS_CAP);
        assert!(peers.shared_contains(&Peer::for_test(SHARED_PEERS_CAP as u16)));
        assert!(!peers.shared_contains(&Peer::for_test(40_001)));
    }

    #[test]
    fn peer_record_cap_drops_a_new_share_row_and_the_sweep_drops_idle_rows() {
        let mut peers = PeerPerformance::new();
        let stale = t(3_000);
        for port in 1..=PEER_RECORD_CAP as u16 {
            peers.testing_insert_idle_peer(Peer::for_test(port), stale);
        }
        let newcomer = Peer::for_test(60_000);
        peers.record_share_request_served(newcomer, 2, observed(3_000));
        assert!(peers.share_requests(&newcomer).is_none());
        assert_eq!(peers.peer_record_count(), PEER_RECORD_CAP);

        let known = Peer::for_test(1);
        peers.record_share_request_served(known, 2, observed(3_000));
        assert!(peers.share_requests(&known).is_some());
        assert_eq!(peers.peer_record_count(), PEER_RECORD_CAP);

        let scored = Peer::for_test(60_001);
        let fresh = stale + Duration::from_secs(10);
        peers.record_advertisability(scored, true, fresh);
        peers.record_connection_established(
            ConnectionRecord {
                peer: Peer::for_test(60_002),
                conn_id: ConnectionId::initial(),
                direction: ConnectionDirection::Outbound,
                full_duplex_capable: true,
                full_duplex: false,
                advertisable: false,
                local_use: LocalUse::None,
                remote_initiators: RemoteInitiators::default(),
                remote_use: LocalUse::None,
                established_at: observed(3_010),
            },
            observed(3_010),
        );
        assert!(peers.peer_record_count() > PEER_RECORD_CAP);

        let (protected_peers, protected_candidates) = empty();
        let sweep = peers.sweep(fresh, &protected_peers, &protected_candidates);
        assert!(sweep.removed_records >= 2);
        assert!(peers.share_flags(&scored).is_some_and(|flags| flags.ever_connected));
        assert!(peers.connection(ConnectionId::initial()).is_some());
        assert!(peers.peer_record_count() <= PEER_RECORD_CAP);
    }

    #[test]
    fn a_share_flood_does_not_evict_scored_peers() {
        let mut peers = PeerPerformance::new();
        let scored = Peer::for_test(7_000);
        let donor = Peer::for_test(7_001);
        let learned = t(4_000);
        let fresh = learned + Duration::from_secs(60);
        peers.record_keepalive_rtt(scored, Duration::from_millis(20), fresh);
        peers.testing_insert_shared(addr(7_000), learned);
        for port in 1..SHARED_PEERS_CAP as u16 {
            peers.testing_insert_shared(addr(port), learned + Duration::from_secs(1));
        }
        assert_eq!(peers.source_counts().shared_peers, SHARED_PEERS_CAP);

        let flood: Vec<SocketAddr> = (50_000..51_000).map(addr).collect();
        let first = peers.ingest_shared_peers(&donor, &flood, fresh);
        assert_eq!(first.added, 0);
        assert_eq!(first.dropped, flood.len());
        let repeated = peers.ingest_shared_peers(&donor, &[addr(1)], fresh + Duration::from_secs(48 * 60 * 60));
        assert_eq!(repeated.added, 0);
        assert_eq!(repeated.dropped, 0);

        for port in 1..50u16 {
            peers.testing_insert_shared(addr(52_000 + port), learned);
        }
        let (protected_peers, protected_candidates) = empty();
        let sweep = peers.sweep(fresh, &protected_peers, &protected_candidates);
        assert_eq!(sweep.removed_records, 0, "scored rows must stay");
        assert!(sweep.removed_shared > 0);
        assert_eq!(peers.source_counts().shared_peers, SHARED_PEERS_CAP);
        assert!(peers.shared_contains(&scored));
        assert!(peers.scores(&scored).keepalive_rtt_latest.is_some());
        assert!(!peers.shared_contains(&Peer::for_test(50_000)));
        assert!(!peers.shared_contains(&Peer::for_test(52_001)));

        let due = learned + Duration::from_secs(1) + PEER_RECORD_RETENTION;
        peers.sweep(due, &protected_peers, &protected_candidates);
        assert!(!peers.shared_contains(&Peer::for_test(1)), "a repeat ingest must not refresh the learned instant");
        assert!(peers.shared_contains(&scored));
        assert!(peers.scores(&scored).keepalive_rtt_latest.is_some());
    }

    #[test]
    fn one_sweep_drops_every_expired_dead_record() {
        let mut peers = PeerPerformance::new();
        let stale = t(5_000);
        let now = stale + PEER_RECORD_RETENTION;
        let (protected_peers, protected_candidates) = empty();
        for port in 1..=400u16 {
            peers.testing_insert_idle_peer(Peer::for_test(port), stale);
        }
        let sweep = peers.sweep(now, &protected_peers, &protected_candidates);
        assert_eq!(sweep.removed_records, 400);
        assert_eq!(peers.peer_record_count(), 0);
    }

    #[test]
    fn a_live_peer_moves_between_the_live_and_dead_sets() {
        let mut peers = PeerPerformance::new();
        let who = Peer::for_test(12);
        let (protected_peers, protected_candidates) = empty();
        connect(&mut peers, who, t(100));
        assert!(peers.testing_is_held(who));
        assert!(!peers.testing_is_dead(who));

        peers.record_connection_closed(who, ConnectionId::initial(), CloseReason::BearerEnded, observed(200));
        assert!(!peers.testing_is_held(who));
        assert!(peers.testing_is_dead_established(who));

        connect(&mut peers, who, t(300));
        assert!(peers.testing_is_held(who));
        assert!(!peers.testing_is_dead(who));

        let far = t(300) + PEER_RECORD_RETENTION + Duration::from_secs(10);
        let sweep = peers.sweep(far, &protected_peers, &protected_candidates);
        assert_eq!(sweep.removed_records, 0);
        assert!(peers.connection(ConnectionId::initial()).is_some());
        assert!(peers.testing_is_held(who));
    }

    impl PeerPerformance {
        fn activity_contains_for_test(&self, peer: Peer) -> bool {
            self.activity.contains_key(&peer)
        }
    }

    #[test]
    fn activity_does_not_move_backward() {
        let mut peers = PeerPerformance::new();
        let who = Peer::for_test(11);
        peers.touch(who, t(20));
        peers.touch(who, t(10));
        let (protected_peers, protected_candidates) = empty();
        peers.sweep(t(20) + PEER_RECORD_RETENTION - Duration::from_secs(1), &protected_peers, &protected_candidates);
        assert_eq!(peers.peer_record_count(), 1);
    }
}
