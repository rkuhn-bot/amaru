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

import Deadlock.Rank

set_option autoImplicit false

namespace Deadlock

/-- Every accepted call is answered, and every message sitting in a bulk box is
later absent from that box. A later equal message is a new acceptance. -/
def Delivered {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  (∀ i id m, m ∈ ((ρ.cfg i).st id).box →
    ∃ j, i ≤ j ∧ m ∉ ((ρ.cfg j).st id).box) ∧
  (∀ i c d k, ((ρ.cfg i).st c).phase = .awaitReply d k →
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k)

/-- An admitted call does not stay in `awaitReply`. Leaving that phase is the
reply: `await_next` either keeps the wait or runs the caller's continuation. -/
theorem call_answered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (c d : InstId) (k : Cont)
    (hph : ((ρ.cfg i).st c).phase = .awaitReply d k) :
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k := by
  cases Classical.em (∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k) with
  | inl h => exact h
  | inr hno =>
    have hstay : ∀ j, i ≤ j → ((ρ.cfg j).st c).phase = .awaitReply d k := by
      intro j hj
      by_cases hphj : ((ρ.cfg j).st c).phase = .awaitReply d k
      · exact hphj
      · exact False.elim (hno ⟨j, hj, hphj⟩)
    have hS : Stuck ρ c i := by
      refine ⟨?_, ?_⟩
      · simp [SameWait, waitKind, hph]
      · intro j hj
        simp [SameWait, waitKind, hstay j hj, hph]
    exact False.elim (never_stuck I hL hG hA ρ hF c i hS)

end Deadlock
