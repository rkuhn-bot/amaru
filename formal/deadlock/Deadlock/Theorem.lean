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

/-- Caller progress, the statement of `call_answered` at `170f0ad85`.
A caller in `awaitReply` later leaves that phase. The callee's life is not
a hypothesis, and neither is the caller's: a wait that stays is a live actor
(`stuck_alive`), the deadline stays enabled, and fairness takes it
(`await_not_forever`). `call_answered` is the separate callee-side `recvBulk`
result recorded on 2026-11-20. `hG` and `hA` are the original hypotheses.
The 2026-11-20 proof sent them to `never_stuck`. This proof uses the deadline. -/
theorem caller_leaves_await (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (c d : InstId) (k : Cont)
    (hph : ((ρ.cfg i).st c).phase = .awaitReply d k) :
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k := by
  have _ := hG
  have _ := hA
  cases Classical.em (∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k) with
  | inl hleave => exact hleave
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
    have hlive : ∀ t, i ≤ t → ((ρ.cfg t).st c).life = .alive :=
      fun t ht => stuck_alive hL ρ c i hS t ht
    exact False.elim (await_not_forever I ρ hF c d i (fun t ht => ⟨k, hstay t ht⟩) hlive)

end Deadlock
