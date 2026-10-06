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

//! Peer-sharing ingest, reply selection, and the reputation queries those use.

use amaru_kernel::Peer;
use amaru_pure_stage::{BoxFuture, ExternalEffectAPI, Instant, Resources, SendData};

use super::{enqueue_query, require_perf};
use crate::performance::{
    PeerShareFlags, PeerSnapshot, Performance, SharedIngestResult,
    ops::{PeerOp, PerformanceOp},
    peers::{sample_share_peers, share_reply_seed},
};

impl Performance {
    pub fn share_flags(peer: Peer) -> ShareFlagsEffect {
        ShareFlagsEffect { peer }
    }

    pub fn snapshot(peer: Peer) -> SnapshotEffect {
        SnapshotEffect { peer }
    }

    pub fn ok_for_sharing(peer: Peer, now: Instant) -> OkForSharingEffect {
        OkForSharingEffect { peer, now }
    }

    pub fn ingest_shared_peers(from: Peer, peers: Vec<std::net::SocketAddr>) -> IngestSharedPeersEffect {
        IngestSharedPeersEffect { from, peers }
    }

    pub fn select_share_peers(requester: Peer, amount: u8, now: Instant) -> SelectSharePeersEffect {
        SelectSharePeersEffect { requester, amount, now }
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ShareFlagsEffect {
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for ShareFlagsEffect {
    type Response = Option<PeerShareFlags>;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::ShareFlags { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SnapshotEffect {
    pub(crate) peer: Peer,
}

impl ExternalEffectAPI for SnapshotEffect {
    type Response = Option<PeerSnapshot>;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::Snapshot { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct OkForSharingEffect {
    pub(crate) peer: Peer,
    pub(crate) now: Instant,
}

impl ExternalEffectAPI for OkForSharingEffect {
    type Response = bool;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::OkForSharing { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct IngestSharedPeersEffect {
    pub(crate) from: Peer,
    pub(crate) peers: Vec<std::net::SocketAddr>,
}

impl ExternalEffectAPI for IngestSharedPeersEffect {
    type Response = SharedIngestResult;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::IngestSharedPeers { effect: this, reply })).await
        })
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SelectSharePeersEffect {
    pub(crate) requester: Peer,
    pub(crate) amount: u8,
    pub(crate) now: Instant,
}

impl ExternalEffectAPI for SelectSharePeersEffect {
    type Response = Vec<std::net::SocketAddr>;

    fn run(self: Box<Self>, resources: Resources) -> BoxFuture<'static, Box<dyn SendData>> {
        let perf = require_perf(&resources);
        self.wrap(|this| async move {
            let now = this.now;
            let candidates =
                enqueue_query(&perf, |reply| PerformanceOp::Peer(PeerOp::ShareReplyCandidates { now, reply })).await;
            sample_share_peers(&this.requester, this.amount, &candidates, share_reply_seed(&this.requester))
        })
    }
}
