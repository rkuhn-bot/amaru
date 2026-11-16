import Deadlock.Local
import Deadlock.Proof

set_option autoImplicit false

namespace Deadlock

theorem transition_is_listed (I : Impl) (hA : Assumptions I) (tr : Transition) (hm : tr ∈ I.transitions) :
    ∃ tr' ∈ I.transitions,
      tr'.template = tr.template ∧ tr'.fromState = tr.fromState ∧ tr'.label = tr.label ∧
        tr'.program = tr.program ∧ tr'.toState = tr.toState ∧ tr'.acceptsCall = tr.acceptsCall :=
  hA.rust_refines tr hm

/-- Internal effects do not stick: `finish` is enabled while the wait lasts, and
fairness takes it. -/
theorem not_stuck_effect_assumed {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
    intro j hj
    exact enabled_finish_effect I (ρ.cfg j) s (hall j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_effect I (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer_assumed {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer)
    (hu : peerUntimed I.desc s = false) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
    intro j hj
    exact enabled_finish_peer I (ρ.cfg j) s (hall j hj) hu
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_peer I (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

/-- A deadlock is a send or a call that stays parked. An effect wait is taken
by fairness, and no phase is recorded as a cell wait. -/
theorem deadlock_kind {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (hD : Deadlock ρ) : ∃ s i dst, Stuck ρ s i ∧
      (waitKind ((ρ.cfg i).st s) = some (.blockingSend dst) ∨
        waitKind ((ρ.cfg i).st s) = some (.callReply dst)) := by
  obtain ⟨s, i, hS, hk⟩ := hD
  cases hkind : waitKind ((ρ.cfg i).st s) with
  | none => simp [hkind] at hk
  | some kind =>
    cases kind with
    | blockingSend dst =>
      exact ⟨s, i, dst, hS, Or.inl hkind⟩
    | callReply dst =>
      exact ⟨s, i, dst, hS, Or.inr hkind⟩
    | effect =>
      exact False.elim (not_stuck_effect_assumed ρ hF s i hS hkind)
    | peer =>
      exact False.elim (not_stuck_peer_assumed ρ hF s i hS hkind (by simp [hkind] at hk; exact hk))

end Deadlock
