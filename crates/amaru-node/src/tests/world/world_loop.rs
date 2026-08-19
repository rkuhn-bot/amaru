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

use amaru_pure_stage::simulation::SimulationRunning;

use super::{HeapEntry, WorldConnectionProvider};

/// World loop over N SimulationRunning graphs.
///
/// Implements the required pattern:
/// - Exhaust every newly-ready graph
/// - while-ready-else-pop-if-at≤horizon
/// - No tokio::time::sleep, no tokio::spawn as the runner, no wall-clock
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
    /// Pattern: exhaust all newly-ready graphs, then pop one event if at≤horizon,
    /// execute it, repeat. Returns when no events are ready within horizon.
    pub fn run_until_horizon(&mut self, horizon_nanos: u64) {
        loop {
            // Exhaust all newly-ready graphs
            loop {
                let mut any_ready = false;
                for graph in &mut self.graphs {
                    graph.receive_inputs();
                    while graph.has_runnable() {
                        if let Some(_blocked) = graph.run_effect() {
                            break;
                        }
                        any_ready = true;
                    }
                }
                if !any_ready {
                    break;
                }
            }

            // Pop one event if at≤horizon
            if let Some(entry) = self.provider.pop_event_at_or_before(horizon_nanos) {
                self.provider.execute_event(entry);
            } else {
                break;
            }
        }
    }

    /// Run until no more events and all graphs are idle/terminated.
    pub fn run_to_completion(&mut self) {
        let horizon = u64::MAX;
        self.run_until_horizon(horizon);
    }

    /// Get the event log.
    pub fn heap_log(&self) -> Vec<super::HeapLogEntry> {
        self.provider.heap_log()
    }
}
