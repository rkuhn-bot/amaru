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

//! Trace and metric emission for [`super::HeaderTelemetry`].
//!
//! The performance worker produces the payloads. This module runs on the external-effect path,
//! where an export layer may drop or lag without stalling header or peer state.

use amaru_metrics::{Meter, MetricRecorder, consensus::ConsensusMetrics};
use amaru_observability::{debug, info};

use super::HeaderTelemetry;

impl HeaderTelemetry {
    /// Emit the corresponding tracing event and optional metric.
    ///
    /// Safe to call where OTel/export layers may drop or lag; must not run on the performance
    /// worker thread.
    pub fn emit(&self, meter: Option<&Meter>, live: bool) {
        match self {
            Self::Lifecycle {
                hash,
                peer,
                outcome,
                slot_start_to_header_micros,
                block_fetch_wait_micros,
                block_fetch_micros,
                forward_micros,
            } => {
                match (hash, peer) {
                    (Some(hash), Some(peer)) => {
                        debug!(
                            consensus::perf::header::LIFECYCLE,
                            peer,
                            header_hash = hash,
                            outcome = outcome.as_str(),
                            slot_start_to_header_micros = @slot_start_to_header_micros,
                            block_fetch_wait_micros = @block_fetch_wait_micros,
                            block_fetch_micros = @block_fetch_micros,
                            forward_micros = @forward_micros
                        );
                    }
                    (Some(hash), None) => {
                        debug!(
                            consensus::perf::header::LIFECYCLE,
                            header_hash = hash,
                            outcome = outcome.as_str(),
                            slot_start_to_header_micros = @slot_start_to_header_micros,
                            block_fetch_wait_micros = @block_fetch_wait_micros,
                            block_fetch_micros = @block_fetch_micros,
                            forward_micros = @forward_micros
                        );
                    }
                    _ => {
                        debug!(consensus::perf::header::LIFECYCLE, outcome = outcome.as_str());
                    }
                }
                record_metric(
                    meter,
                    ConsensusMetrics::HeaderLifecycle {
                        outcome: outcome.as_str().to_string(),
                        slot_start_to_header_micros: *slot_start_to_header_micros,
                        block_fetch_wait_micros: *block_fetch_wait_micros,
                        block_fetch_micros: *block_fetch_micros,
                        forward_micros: *forward_micros,
                    },
                );
            }
            Self::ForkSwitch { hash, outcome, duration_micros } => {
                debug!(
                    consensus::perf::fork::SWITCH,
                    header_hash = hash,
                    outcome = outcome.as_str(),
                    duration_micros = @duration_micros
                );
                record_metric(
                    meter,
                    ConsensusMetrics::ForkSwitch {
                        outcome: outcome.as_str().to_string(),
                        duration_micros: *duration_micros,
                    },
                );
            }
            Self::Announced { hash, peer, rank, slot_latency_ms } => {
                if live {
                    info!(
                        blockperf::header::ANNOUNCED,
                        peer,
                        header_hash = hash,
                        rank = *rank,
                        slot_latency_ms = @slot_latency_ms
                    );
                } else {
                    debug!(
                        blockperf::header::ANNOUNCED,
                        peer,
                        header_hash = hash,
                        rank = *rank,
                        slot_latency_ms = @slot_latency_ms
                    );
                }
            }
            Self::Requested { hash, peers, slot_latency_ms } => {
                if live {
                    info!(
                        blockperf::block::REQUESTED,
                        header_hash = hash,
                        peers = peers.as_str(),
                        slot_latency_ms = @slot_latency_ms
                    );
                } else {
                    debug!(
                        blockperf::block::REQUESTED,
                        header_hash = hash,
                        peers = peers.as_str(),
                        slot_latency_ms = @slot_latency_ms
                    );
                }
            }
            Self::Received { hash, peer, rank, slot_latency_ms, fetch_latency_ms } => {
                if live {
                    info!(
                        blockperf::block::RECEIVED,
                        peer,
                        header_hash = hash,
                        rank = *rank,
                        slot_latency_ms = @slot_latency_ms,
                        fetch_latency_ms = @fetch_latency_ms
                    );
                } else {
                    debug!(
                        blockperf::block::RECEIVED,
                        peer,
                        header_hash = hash,
                        rank = *rank,
                        slot_latency_ms = @slot_latency_ms,
                        fetch_latency_ms = @fetch_latency_ms
                    );
                }
            }
            Self::Adopted { hash, peer: Some(peer), slot_latency_ms } => {
                if live {
                    info!(blockperf::block::ADOPTED, header_hash = hash, peer, slot_latency_ms = @slot_latency_ms);
                } else {
                    debug!(blockperf::block::ADOPTED, header_hash = hash, peer, slot_latency_ms = @slot_latency_ms);
                }
            }
            Self::Adopted { hash, peer: None, slot_latency_ms } => {
                if live {
                    info!(blockperf::block::ADOPTED, header_hash = hash, slot_latency_ms = @slot_latency_ms);
                } else {
                    debug!(blockperf::block::ADOPTED, header_hash = hash, slot_latency_ms = @slot_latency_ms);
                }
            }
        }
    }

    /// Emit a batch of telemetry events.
    ///
    /// `live` prints block-propagation events at info; sync keeps them at debug.
    pub fn emit_all(events: &[Self], meter: Option<&Meter>, live: bool) {
        for event in events {
            event.emit(meter, live);
        }
    }
}

fn record_metric(meter: Option<&Meter>, metric: ConsensusMetrics) {
    if let Some(meter) = meter {
        metric.record_to_meter(meter);
    }
}
