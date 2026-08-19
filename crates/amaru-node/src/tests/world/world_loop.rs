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

use amaru_pure_stage::simulation::{Blocked, SimulationRunning};

use super::WorldConnectionProvider;

/// World loop over N SimulationRunning graphs + WorldConnectionProvider heap.
///
/// ASYNC method (no block_on, no Runtime::new). Awaited by #[tokio::test].
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
    /// ASYNC method awaited by test. NO block_on, NO Runtime::new.
    /// Pattern: exhaust ready, pop-if-at≤horizon, execute, await_external_effect.
    pub async fn run_until_horizon(&mut self, horizon_nanos: u64) {
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
                self.provider.set_time(entry.time_nanos);
                self.provider.execute_event(entry); // Fixed: pass full HeapEntry

                // await_external_effect on all graphs (will complete if futures ready)
                for graph in &mut self.graphs {
                    graph.await_external_effect().await;
                }
            } else {
                break;
            }
        }
    }

    /// Run until no more events and all graphs idle/terminated.
    pub async fn run_to_completion(&mut self) {
        self.run_until_horizon(u64::MAX).await
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
