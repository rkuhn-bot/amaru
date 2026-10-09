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

//! Peer map owned by the performance worker: claims, quality, reputation, and source pools.

mod claims;
mod connections;
mod peer_mix;
mod quality;
mod record;
mod reputation;
mod select_outbound;
mod select_share;
mod sources;
mod view;

use std::collections::{BTreeMap, BTreeSet};

use amaru_kernel::{HeaderHash, Peer, PeerCandidate};
use amaru_ouroboros::ConnectionId;
pub use claims::{BlockClaim, ClaimKind, FetchPeerSet, PeerSnapshot, SelectPeersParams};
use claims::{ClaimMeta, ParentInfo};
pub(crate) use connections::instant_of;
pub use peer_mix::{DEFAULT_MALUS_HALF_LIFE, DEFAULT_PEER_MIX, MixEntry, PeerMix, PeerMixParseError, PeerSource};
pub use quality::{ChurnInput, ChurnRank, PeerScores, rank_churn};
use record::PeerState;
pub use reputation::{
    ADVERSARIAL_IMPULSE, CONNECT_FAIL_IMPULSE, DEFAULT_PEER_MALUS_HALF_LIFE, PeerShareFlags, SHARE_MALUS_THRESHOLD,
    malus_at,
};
pub use select_outbound::{
    NEVER_CONNECTED_BONUS, OutboundInputs, OutboundPick, SelectOutboundParams, SelectUsing, select_outbound_from,
};
pub use select_share::SHARE_POLICY_MAX;
pub(crate) use select_share::{ShareCandidate, sample_share_peers, share_reply_seed};
pub use sources::{SharedIngestResult, SourceCounts};
pub use view::{DialOutcome, PeerView, ViewConnection};

/// Peer performance map (availability + scores + source pools). Owned by the performance worker.
#[derive(Debug, Default)]
pub struct PeerPerformance {
    /// header tree link edges
    parents: BTreeMap<HeaderHash, ParentInfo>,
    /// announcements and deliveries by peer, per hash
    direct: BTreeMap<HeaderHash, BTreeMap<Peer, ClaimMeta>>,
    /// announcements by peer, with EWMA scores and tip claims
    peers: BTreeMap<Peer, PeerState>,
    /// Admin mix formula (floors, weights, per-source malus half-lives).
    peer_mix: PeerMix,
    static_peers: BTreeSet<PeerCandidate>,
    shared_peers: BTreeSet<PeerCandidate>,
    snapshot_candidates: BTreeSet<PeerCandidate>,
    ledger_candidates: BTreeSet<PeerCandidate>,
    /// Origin of a dialed [`Peer`], for malus half-life after Host/SRV resolution.
    peer_origin: BTreeMap<Peer, PeerSource>,
    /// Last address obtained for a candidate; used only to score Host/SRV on later picks.
    last_peer: BTreeMap<PeerCandidate, Peer>,
    /// Established bearers. Absent after close.
    connections: BTreeMap<ConnectionId, connections::LiveConnection>,
    /// Only the latest close for each peer is kept; an earlier close is replaced.
    last_close: BTreeMap<Peer, connections::CloseRecord>,
    /// Latest outbound dial that failed before handshake.
    last_connect_failure: BTreeMap<Peer, amaru_ouroboros::ObservedAt>,
    /// Latest share-reply ingest, including a repeat that added nothing.
    last_shared_at: BTreeMap<Peer, amaru_ouroboros::ObservedAt>,
    /// Share requests this node has answered.
    share_requests: BTreeMap<Peer, connections::ShareRequests>,
    /// Advances when a lifecycle write or a ledger-candidate replacement changes what selection reads.
    generation: u64,
}

impl PeerPerformance {
    #[expect(clippy::expect_used)]
    pub(super) fn bump_generation(&mut self) {
        self.generation = self.generation.checked_add(1).expect("peer performance generation overflow");
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Bootstrap candidate pools and the admin mix (typically once at node start).
    ///
    /// All four sources are [`PeerCandidate`] sets. Host/SRV names stay in the pool and are
    /// resolved again each time they are selected (DNS can change).
    pub fn with_sources(
        static_peers: BTreeSet<PeerCandidate>,
        snapshot_candidates: BTreeSet<PeerCandidate>,
        ledger_candidates: BTreeSet<PeerCandidate>,
        peer_mix: PeerMix,
    ) -> Self {
        Self { static_peers, snapshot_candidates, ledger_candidates, peer_mix, ..Self::default() }
    }
}
