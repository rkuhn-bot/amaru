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

use std::future::Future;

use amaru_pure_stage::simulation::{Blocked, SimulationRunning};

use super::{HeapEntry, WorldConnectionProvider};

/// World loop over N SimulationRunning graphs.
///
/// Uses only PUBLIC SimulationRunning API:
/// - receive_inputs, has_runnable, try_effect, handle_effect
/// - await_external_effect (to complete UntilResolved futures)
///
/// Pattern: exhaust all newly-ready graphs, pop-if-at≤horizon, execute event,
/// await external effects to complete stages, repeat.
pub struct WorldLoop {
    provider: WorldConnectionProvider,
    graphs: Vec<SimulationRunning>,
}

impl WorldLoop {
    pub fn new(provider: WorldConnectionProvider, graphs: Vec<SimulationRunning>) -> Self {
        Self { provider, graphs }
    }

    /// Run until no more events at-or-before horizon.
    ///
    /// After pop/execute, calls await_external_effect to complete UntilResolved
    /// futures and resume stages from Blocked::Busy.
    pub fn run_until_horizon(&mut self, horizon_nanos: u64) -> tokio::runtime::Handle {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            loop {
                // Exhaust all newly-ready graphs
                loop {
                    let mut any_ready = false;
                    for graph in &mut self.graphs {
                        graph.receive_inputs();
                        while graph.has_runnable() {
                            match graph.try_effect() {
                                Ok(effect) => {
                                    graph.handle_effect(effect);
                                    any_ready = true;
                                }
                                Err(Blocked::Busy { .. }) => break,
                                Err(_) => break,
                            }
                        }
                    }
                    if !any_ready {
                        break;
                    }
                }

                // Pop one event if at≤horizon
                if let Some(entry) = self.provider.pop_event_at_or_before(horizon_nanos) {
                    self.provider.execute_event(entry);

                    // Complete UntilResolved futures: await_external_effect polls pending_computations
                    // and delivers results via provide_external_result, making stages runnable again
                    for graph in &mut self.graphs {
                        graph.await_external_effect().await;
                    }
                } else {
                    break;
                }
            }
        });
        rt.handle().clone()
    }

    /// Run until no more events and all graphs idle/terminated.
    pub fn run_to_completion(&mut self) -> tokio::runtime::Handle {
        self.run_until_horizon(u64::MAX)
    }

    /// Get the event log.
    pub fn heap_log(&self) -> Vec<super::HeapLogEntry> {
        self.provider.heap_log()
    }

    /// Check if any events remain on heap before horizon.
    pub fn has_events_before(&self, horizon_nanos: u64) -> bool {
        self.provider.peek_next_event_time().map_or(false, |t| t <= horizon_nanos)
    }
}
