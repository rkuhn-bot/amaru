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
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False :=
  not_stuck_effect ρ hF s i h hp hl

theorem not_stuck_peer_assumed {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer)
    (hf : peerFinishable I.desc s = true)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False :=
  not_stuck_peer ρ hF s i h hp hf hl

/-- A deadlock that is not an effect or a peer wait is a send or a call that
stays parked. `finish` clears an effect or a peer wait while the actor stays
alive, so those two are not the remaining cases. -/
theorem deadlock_kind {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (hD : Deadlock ρ)
    (halive : ∀ s i, Stuck ρ s i →
      (waitKind ((ρ.cfg i).st s) = some .effect ∨ waitKind ((ρ.cfg i).st s) = some .peer) →
      ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) :
    ∃ s i dst, Stuck ρ s i ∧
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
      exact False.elim (not_stuck_effect_assumed ρ hF s i hS hkind
        (halive s i hS (Or.inl hkind)))
    | peer =>
      exact False.elim (not_stuck_peer_assumed ρ hF s i hS hkind
        (peerFinishable_true I.desc s) (halive s i hS (Or.inr hkind)))

end Deadlock
