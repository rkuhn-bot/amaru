import Deadlock.Local
import Deadlock.Proof

set_option autoImplicit false

namespace Deadlock

theorem transition_is_listed (I : Impl) (hA : Assumptions I) (tr : Transition) (hm : tr ∈ I.transitions) :
    ∃ tr' ∈ I.transitions,
      tr'.template = tr.template ∧ tr'.fromState = tr.fromState ∧ tr'.label = tr.label ∧
        tr'.program = tr.program ∧ tr'.toState = tr.toState ∧ tr'.acceptsCall = tr.acceptsCall :=
  hA.rust_refines tr hm

/-- Internal effects do not stick: `Assumptions.internal_complete` is the step
fairness applies, not a theorem about the binary. -/
theorem not_stuck_effect_assumed {I : Impl} {N : Nat} (ρ : Run I N) (hA : Assumptions I) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
    intro j hj
    obtain ⟨k, hk⟩ := wait_effect_phase ((ρ.cfg j).st s) (hall j hj)
    exact hA.internal_complete (ρ.cfg j) s k hk
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_effect (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer_assumed {I : Impl} {N : Nat} (ρ : Run I N) (hA : Assumptions I) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
    intro j hj
    obtain ⟨k, hk⟩ := wait_peer_phase ((ρ.cfg j).st s) (hall j hj)
    exact hA.peer_complete (ρ.cfg j) s k hk
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_peer (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

end Deadlock
