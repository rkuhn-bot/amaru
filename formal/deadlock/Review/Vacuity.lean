-- Copyright 2026 PRAGMA
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

/-
Negative record, not a proof.

`step_quiet` used to claim that from a quiet world the only applicable action
is `spawn`. `Action.ingress` makes that case split non-exhaustive:

  Review/Vacuity.lean:57:2: error: Alternative `ingress` has not been provided

The old conclusion `vacuous : ∀ I N ρ, ¬Deadlock ρ ∧ CellFresh ρ`, with no
`LocalOk`, `GraphOk`, `Assumptions`, or `Fair` hypothesis, therefore no longer
builds. `parkImpl` passes `park_graph_ok` and `park_local_ok`. On that
instance `parks_on_second_send` is the world after ingress and two sends, with
the producer parked, and `resumes_after_receive` is the world after the sink
receives, with the producer idle again.
-/
