import Deadlock.Local
import Deadlock.Proof
import Deadlock.Step

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

theorem cfg_reachable {I : Impl} {N : Nat} (ρ : Run I N) (n : Nat) : Reachable I N (ρ.cfg n) := by
  induction n with
  | zero => simpa [ρ.start] using (Reachable.init : Reachable I N (initWorld I N))
  | succ n ih => exact Reachable.step (ρ.cfg n) (ρ.cfg (n + 1)) (ρ.act n) ih (ρ.valid n)

theorem waitKind_off (a : Actor) (h : a.phase = .idle ∨ a.phase = .crashed) : waitKind a = none := by
  rcases h with h | h <;> simp [waitKind, h]

/-- A stuck actor stays alive. A later world still has the same wait, and an
actor that is not alive is idle or crashed, which has no wait. -/
theorem stuck_alive {I : Impl} {N : Nat} (hL : LocalOk I) (ρ : Run I N) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (j : Nat) (hj : i ≤ j) : ((ρ.cfg j).st s).life = .alive := by
  have hS := sem_reachable I N (ρ.cfg j) hL (cfg_reachable ρ j)
  have hne : waitKind ((ρ.cfg j).st s) ≠ none := by
    rw [← (h.2 j hj).1]
    exact (h.2 j hj).2
  cases hlife : ((ρ.cfg j).st s).life with
  | alive => rfl
  | dead =>
    exact absurd (waitKind_off _ (hS.idleOff s (by rw [hlife]; intro h; cases h))) hne
  | absent =>
    exact absurd (waitKind_off _ (hS.idleOff s (by rw [hlife]; intro h; cases h))) hne

/-- A deadlock that is not an effect or a peer wait is a send or a call that
stays parked. `finish` clears an effect or a peer wait while the actor stays
alive, so those two are not the remaining cases. -/
theorem deadlock_kind {I : Impl} {N : Nat} (hL : LocalOk I) (ρ : Run I N) (hF : Fair ρ)
    (hD : Deadlock ρ) :
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
        (fun j hj => stuck_alive hL ρ s i hS j hj))
    | peer =>
      exact False.elim (not_stuck_peer_assumed ρ hF s i hS hkind
        (peerFinishable_true I.desc s) (fun j hj => stuck_alive hL ρ s i hS j hj))

end Deadlock
