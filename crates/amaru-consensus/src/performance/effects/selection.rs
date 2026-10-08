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

//! Outbound mix selection, churn ranking, and candidate-pool maintenance.

#![expect(clippy::unit_arg)]

use amaru_kernel::{Peer, PeerCandidate};
use amaru_pure_stage::{BoxFuture, ExternalEffectAPI, Instant, Resources, SendData};

use super::{enqueue, enqueue_query, require_perf};
use crate::performance::{
    PeerScores, Performance, SelectOutboundParams, SelectUsing,
    ops::{PeerOp, PerformanceOp},
};

impl Performance {
    pub fn rank_peers_for_churn(candidates: Vec<Peer>, now: Instant) -> RankPeersForChurnEffect {
        RankPeersForChurnEffect { candidates, now }
    }

    pub fn scores(peer: Peer) -> ScoresEffect {
        ScoresEffect { peer }
    }

    pub fn set_ledger_candidates(candidates: std::collections::BTreeSet<PeerCandidate>) -> SetLedgerCandidatesEffect {
        SetLedgerCandidatesEffect { candidates }
    }

    pub fn select_outbound(params: crate::performance::SelectOutboundParams) -> SelectOutboundEffect {
        SelectOutboundEffect { params }
    }

    pub fn is_static_peer(peer: Peer) -> IsStaticPeerEffect {
        IsStaticPeerEffect { peer }
    }

    pub fn note_dial(origin: crate::performance::PeerSource, candidate: PeerCandidate, peer: Peer) -> NoteDialEffect {
        NoteDialEffect { origin, candidate, peer }
    }

    pub fn shared_contains(peer: Peer) -> SharedContainsEffect {
        SharedContainsEffect { peer }
    }

    pub fn source_counts() -> SourceCountsEffect {
        SourceCountsEffect
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RankPeersForChurnEffect {
    pub(crate) candidates: Vec<Peer>,
    pub(crate) now: Instant,
}

impl ExternalEffectAPI for RankPeersForChurnEffect {
    type Response = Vec<(Peer, PeerScores)>;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::RankPeersForChurn { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ScoresEffect {
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for ScoresEffect {
    type Response = PeerScores;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::Scores { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SetLedgerCandidatesEffect {
    pub(crate) candidates: std::collections::BTreeSet<PeerCandidate>,
}

impl ExternalEffectAPI for SetLedgerCandidatesEffect {
    type Response = ();

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        self.wrap_sync({
            let perf = require_perf(&resources);
            enqueue(&perf, PerformanceOp::Peer(PeerOp::SetLedgerCandidates { effect: self.as_ref().clone() }));
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SelectOutboundEffect {
    pub(crate) params: SelectOutboundParams,
}

impl ExternalEffectAPI for SelectOutboundEffect {
    type Response = SelectUsing;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::SelectOutbound { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct IsStaticPeerEffect {
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for IsStaticPeerEffect {
    type Response = bool;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::IsStaticPeer { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct NoteDialEffect {
    pub(crate) origin: crate::performance::PeerSource,
    pub(crate) candidate: PeerCandidate,
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for NoteDialEffect {
    type Response = ();

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        self.wrap_sync({
            let perf = require_perf(&resources);
            enqueue(&perf, PerformanceOp::Peer(PeerOp::NoteDial { effect: self.as_ref().clone() }));
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SharedContainsEffect {
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for SharedContainsEffect {
    type Response = bool;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::SharedContains { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SourceCountsEffect;

impl ExternalEffectAPI for SourceCountsEffect {
    type Response = crate::performance::SourceCounts;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::SourceCounts { effect: this, reply })).await
        })
    }
}
