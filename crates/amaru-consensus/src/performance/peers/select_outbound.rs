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

//! Mix allotment and quality-weighted outbound picks.

use std::collections::{BTreeMap, BTreeSet};

use amaru_kernel::PeerCandidate;
use amaru_pure_stage::Instant;
use rand::{Rng, SeedableRng, rngs::StdRng};

use super::{
    PeerPerformance,
    peer_mix::PeerSource,
    quality::{PeerScores, rank_score},
    reputation::malus_at,
};

/// Scale of malus in outbound score: `goodness - λ * malus`.
pub const OUTBOUND_MALUS_LAMBDA: f64 = 1.0;

/// Softmax temperature for weighted outbound sampling.
pub const OUTBOUND_PICK_TEMPERATURE: f64 = 1.0;

/// Bonus for peers with no Performance observation yet (never connected / unknown).
pub const NEVER_CONNECTED_BONUS: f64 = 0.5;

/// Parameters for mix + quality Using selection (outbound dials and inbound promotions).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SelectOutboundParams {
    /// How many new Using slots to fill (typically `target − occupancy`).
    pub open: usize,
    /// Candidates that must not be picked (already outbound, cooling down, or resolving).
    pub excluded: BTreeSet<PeerCandidate>,
    /// Duplex inbound connections that could be promoted to Using.
    pub eligible_inbound: usize,
    /// Deterministic RNG seed from peer selection’s random effect.
    pub seed: [u8; 32],
    pub now: Instant,
}

/// Mix result: inbound Using promotions plus outbound dials.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SelectUsing {
    /// How many duplex inbound connections to promote to Using.
    pub inbound: usize,
    pub outbound: Vec<OutboundPick>,
}

/// One mix pick: a [`PeerCandidate`] from a named source, not yet resolved to a dial address.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OutboundPick {
    pub candidate: PeerCandidate,
    pub origin: PeerSource,
}

struct OutboundWeight {
    candidate: PeerCandidate,
    score: f64,
    weight: f64,
}

/// Fill `n` slots from best score to worse. Ties are a weighted draw; a worse score is used
/// only after every better score in the bucket has been taken.
fn fill_by_worsening_score(rng: &mut StdRng, mut weights: Vec<OutboundWeight>, n: usize) -> Vec<PeerCandidate> {
    if n == 0 || weights.is_empty() {
        return Vec::new();
    }
    weights
        .sort_by(|left, right| right.score.total_cmp(&left.score).then_with(|| left.candidate.cmp(&right.candidate)));
    let mut out = Vec::with_capacity(n.min(weights.len()));
    let mut index = 0;
    while out.len() < n && index < weights.len() {
        let score = weights[index].score;
        let mut end = index + 1;
        while end < weights.len() && weights[end].score.total_cmp(&score).is_eq() {
            end += 1;
        }
        let group = weights[index..end].iter().map(|weight| (weight.candidate.clone(), weight.weight)).collect();
        let take = (n - out.len()).min(end - index);
        out.extend(weighted_sample_without_replacement(rng, group, take));
        index = end;
    }
    out
}

fn weighted_sample_without_replacement<T: Clone>(rng: &mut StdRng, mut items: Vec<(T, f64)>, n: usize) -> Vec<T> {
    let mut out = Vec::with_capacity(n.min(items.len()));
    for _ in 0..n {
        if items.is_empty() {
            break;
        }
        let total: f64 = items.iter().map(|(_, w)| *w).filter(|w| w.is_finite() && *w > 0.0).sum();
        let idx = if total <= 0.0 || !total.is_finite() {
            rng.random_range(0..items.len())
        } else {
            let mut r = rng.random::<f64>() * total;
            let mut chosen = items.len() - 1;
            for (i, (_, w)) in items.iter().enumerate() {
                if *w <= 0.0 || !w.is_finite() {
                    continue;
                }
                r -= w;
                if r <= 0.0 {
                    chosen = i;
                    break;
                }
            }
            chosen
        };
        out.push(items.swap_remove(idx).0);
    }
    out
}

fn outbound_goodness(scores: Option<&PeerScores>) -> f64 {
    // Reuse fetch-oriented heuristics with need_len=1 (no fragment context for dial).
    rank_score(scores, 1)
}

fn outbound_sampling_weight(score: f64) -> f64 {
    let t = OUTBOUND_PICK_TEMPERATURE.max(f64::EPSILON);
    let w = (score / t).exp();
    if w.is_finite() && w > 0.0 { w } else { f64::EPSILON }
}

impl PeerPerformance {
    /// Mix allotment: inbound Using promotions plus quality-weighted outbound dials.
    pub fn select_outbound(&self, params: SelectOutboundParams) -> SelectUsing {
        if params.open == 0 {
            return SelectUsing { inbound: 0, outbound: Vec::new() };
        }
        let mut eligible_counts = BTreeMap::new();
        let mut eligible_by_source: BTreeMap<PeerSource, Vec<PeerCandidate>> = BTreeMap::new();
        for entry in self.peer_mix.entries() {
            if entry.source.is_inbound() {
                eligible_counts.insert(PeerSource::Inbound, params.eligible_inbound);
                continue;
            }
            let list = self.eligible_for_source(entry.source, &params.excluded);
            eligible_counts.insert(entry.source, list.len());
            eligible_by_source.insert(entry.source, list);
        }
        let allotment = self.peer_mix.allot(params.open, &eligible_counts);
        let inbound = allotment.get(&PeerSource::Inbound).copied().unwrap_or(0);
        if allotment.values().all(|&n| n == 0) {
            return SelectUsing { inbound: 0, outbound: Vec::new() };
        }

        let mut rng = StdRng::from_seed(params.seed);
        let mut picked = Vec::new();
        let mut already: BTreeSet<PeerCandidate> = BTreeSet::new();

        for entry in self.peer_mix.entries() {
            if entry.source.is_inbound() {
                continue;
            }
            let n = allotment.get(&entry.source).copied().unwrap_or(0);
            if n == 0 {
                continue;
            }
            let candidates = eligible_by_source.remove(&entry.source).unwrap_or_default();
            let candidates: Vec<PeerCandidate> = candidates.into_iter().filter(|c| !already.contains(c)).collect();
            if candidates.is_empty() {
                continue;
            }
            let weights = self.outbound_weights_for(&candidates, params.now);
            // Best score first, then worse scores, until the bucket is full. Malus makes a
            // peer less preferred; it does not drop the peer while a slot is still open.
            for candidate in fill_by_worsening_score(&mut rng, weights, n) {
                already.insert(candidate.clone());
                picked.push(OutboundPick { candidate, origin: entry.source });
            }
        }
        SelectUsing { inbound, outbound: picked }
    }

    fn outbound_weights_for(&self, candidates: &[PeerCandidate], now: Instant) -> Vec<OutboundWeight> {
        candidates
            .iter()
            .map(|candidate| {
                let Some(peer) = candidate.as_peer().or_else(|| self.last_peer.get(candidate).copied()) else {
                    return OutboundWeight {
                        candidate: candidate.clone(),
                        score: NEVER_CONNECTED_BONUS,
                        weight: outbound_sampling_weight(NEVER_CONNECTED_BONUS),
                    };
                };
                let half_life = self.half_life_for(&peer);
                let (malus, goodness, never_connected) = match self.peers.get(&peer) {
                    None => (0.0, 0.0, true),
                    Some(state) => {
                        let malus = malus_at(state.malus, state.malus_as_of, now, half_life);
                        // Fresh / unknown to Performance: no successful handshake yet and no scores
                        // or tip activity. Failure-only stubs set `last_change` (and malus) so they
                        // do not receive the never-connected exploration bonus.
                        let never_connected =
                            !state.ever_connected && state.scores.last_change.is_none() && state.tips.is_empty();
                        let goodness = outbound_goodness(Some(&state.scores));
                        (malus, goodness, never_connected)
                    }
                };
                let mut score = goodness - OUTBOUND_MALUS_LAMBDA * malus;
                if never_connected {
                    score += NEVER_CONNECTED_BONUS;
                }
                OutboundWeight { candidate: candidate.clone(), score, weight: outbound_sampling_weight(score) }
            })
            .collect()
    }
}
