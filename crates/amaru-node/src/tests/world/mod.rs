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

//! World-based connection provider for deterministic simulation testing.
//!
//! This module implements EDR-011 discrete-event simulation for network effects.
//! [`WorldConnectionProvider`] owns the one physical `(time, sequence)` heap of
//! network events and graph wakes. [`WorldLoop`] is the only popper.

mod nodes;
mod world_connection_provider;
mod world_loop;

pub use nodes::build_world_node;
pub use world_connection_provider::{
    GraphWakeReason, HeapLogEntry, HeapLogKind, NetworkEvent, WIRE_DELAY_MAX_NANOS, WIRE_DELAY_MIN_NANOS,
    WorldConnectionProvider, WorldHeapEntry, WorldHeapItem, wire_delay_nanos,
};
pub use world_loop::WorldLoop;

#[cfg(test)]
mod tests;
