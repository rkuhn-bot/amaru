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

//! Addresses returned in one peer-sharing reply.

use std::net::SocketAddr;

use amaru_kernel::Peer;
use amaru_pure_stage::Instant;
use rand::{SeedableRng, rngs::StdRng};

use super::PeerPerformance;

/// Upper bound on peers returned in one share response.
pub const SHARE_POLICY_MAX: u8 = 10;

impl PeerPerformance {
    /// Addresses to advertise in a share reply (origin filter + sticky sample + reputation).
    pub fn select_share_peers(&self, requester: &Peer, amount: u8, now: Instant) -> Vec<SocketAddr> {
        let n = (amount.min(SHARE_POLICY_MAX)) as usize;
        if n == 0 {
            return Vec::new();
        }
        let mut eligible = Vec::new();
        for peer in self.share_candidate_pool() {
            if &peer == requester {
                continue;
            }
            let addr = SocketAddr::from(peer);
            // Pool members with no Performance row are treated as shareable (not observed bad).
            // Observed peers must pass advertisability / malus / non-adversarial checks.
            if self.peers.contains_key(&peer) && !self.ok_for_sharing(&peer, now) {
                continue;
            }
            eligible.push((peer, addr));
        }
        eligible.sort_by_key(|a| a.0);
        let seed = {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            requester.hash(&mut hasher);
            hasher.finish()
        };
        let mut rng = StdRng::seed_from_u64(seed);
        use rand::seq::SliceRandom;
        eligible.shuffle(&mut rng);
        eligible.into_iter().take(n).map(|(_, addr)| addr).collect()
    }
}
