import Deadlock.Proof

set_option autoImplicit false

namespace Deadlock

/-- Trust boundary. The checker judges a finite description; these facts say the
running system is that description. They are hypotheses, not theorems about Rust. -/
structure Refines (I : Impl) : Prop where
  /-- Blocking send and call-reply waits are residual edges at the current typestates.
  Every co-reachable pair must appear in `compatibility`. -/
  projects :
    ∀ {N w s dst},
      Reachable I N w →
      (waitKind (w.st s) = some (.blockingSend dst) ∨
        waitKind (w.st s) = some (.callReply dst)) →
      edgeBool (residualEdges I.desc)
        { template := tname s, state := (w.st s).typestate }
        { template := tname dst, state := (w.st dst).typestate } = true
  /-- The dequeuing transition of a call contains the reply. -/
  call_replies : ∀ tr ∈ I.transitions, tr.acceptsCall = true → Eff.reply ∈ tr.program
  /-- Lemma 1 along real runs: a credited mailbox never parks a blocking sender. -/
  credit_clear :
    ∀ {N w id s},
      Reachable I N w →
      l1 I.desc (tname id) = true →
      waitKind (w.st s) ≠ some (.blockingSend id)
  /-- Self-schedule stays inside the priority bound. -/
  no_crash : ∀ {N w id}, Reachable I N w → (w.st id).phase ≠ .crashed

inductive WaitPath (w : World) : InstId → InstId → Prop where
  | step (s dst : InstId) :
      (waitKind (w.st s) = some (.blockingSend dst) ∨ waitKind (w.st s) = some (.callReply dst)) →
      WaitPath w s dst
  | cons (s t u : InstId) : WaitPath w s t → WaitPath w t u → WaitPath w s u

def actorNode (w : World) (s : InstId) : Node :=
  { template := tname s, state := (w.st s).typestate }

theorem Path.append {E : Node → Node → Bool} {a b c : Node}
    (p : Path E a b) (q : Path E b c) : Path E a c := by
  induction p with
  | single h => exact Path.cons h q
  | cons h _ ih => exact Path.cons h (ih q)

theorem run_reachable {I : Impl} {N : Nat} (ρ : Run I N) (k : Nat) : Reachable I N (ρ.cfg k) := by
  induction k with
  | zero => simpa [ρ.start] using (Reachable.init : Reachable I N (initWorld I N))
  | succ k ih => exact Reachable.step _ _ _ ih (ρ.valid k)

theorem project_path (I : Impl) (hR : Refines I) {N : Nat} {w : World} {a b : InstId}
    (hRch : Reachable I N w) (p : WaitPath w a b) :
    Path (edgeBool (residualEdges I.desc)) (actorNode w a) (actorNode w b) := by
  induction p with
  | step s dst hwait => exact Path.single (hR.projects hRch hwait)
  | cons _ _ _ _ _ ih1 ih2 => exact Path.append ih1 ih2

/-- For every `N`, a reachable wait cycle would be a residual cycle. -/
theorem no_wait_cycle (I : Impl) (hG : GraphOk I.desc) (hR : Refines I)
    {N : Nat} {w : World} (hRch : Reachable I N w) : ∀ s, ¬ WaitPath w s s := by
  intro s hp
  exact hG.acyclic _ (project_path I hR hRch hp)

theorem fair_recv {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (dst : InstId) (i : Nat)
    (h : ∀ j, i ≤ j → CanReceive (ρ.cfg j) dst) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk dst := by
  exact hF.weak (.recvBulk dst) i rfl (fun j hj => can_receive_enabled I (ρ.cfg j) dst (h j hj))

theorem stuck_same_wait {I : Impl} {N : Nat} (ρ : Run I N) {s : InstId} {i j : Nat}
    (h : Stuck ρ s i) (hj : i ≤ j) :
    waitKind ((ρ.cfg j).st s) = waitKind ((ρ.cfg i).st s) :=
  (h.2 j hj).1.symm

theorem resume_not_send (a : Actor) (dst : InstId) (isCall : Bool) (k : Cont)
    (hp : a.phase = .parked dst isCall k) :
    waitKind (resumeSender a isCall dst) ≠ some (.blockingSend dst) := by
  cases isCall <;> cases hk : k.rest <;> simp [resumeSender, hp, proceed, waitKind, hk]

/-- Effects, timed peers, cells, and blocking sends into Lemma 1 mailboxes do not
stick in a fair run. `no_wait_cycle` is the matching safety fact for every residual edge. -/
theorem local_and_credit_free (I : Impl) (hR : Refines I) {N : Nat} (ρ : Run I N) (hF : Fair ρ) :
    ∀ s i,
      (waitKind ((ρ.cfg i).st s) = some .effect → ¬ Stuck ρ s i) ∧
      (waitKind ((ρ.cfg i).st s) = some .peer → ¬ Stuck ρ s i) ∧
      waitKind ((ρ.cfg i).st s) ≠ some .cell ∧
      (∀ dst, l1 I.desc (tname dst) = true →
        waitKind ((ρ.cfg i).st s) ≠ some (.blockingSend dst)) := by
  intro s i
  refine ⟨?_, ?_, waitKind_ne_cell _, ?_⟩
  · intro hk hS; exact not_stuck_effect ρ hF s i hS hk
  · intro hk hS; exact not_stuck_peer ρ hF s i hS hk
  · intro dst hl1 hk; exact hR.credit_clear (run_reachable ρ i) hl1 hk

/-- For every instance count and every fair run: no wait-for cycle, no actor stuck
forever on an internal effect or a timed peer wait, no cell wait, and no blocking
send into a Lemma 1 mailbox. -/
theorem deadlock_freedom (I : Impl) (hG : GraphOk I.desc) (hR : Refines I) :
    ∀ N, ∀ ρ : Run I N, Fair ρ →
      (∀ i s, ¬ WaitPath (ρ.cfg i) s s) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) = some .effect → ¬ Stuck ρ s i) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) = some .peer → ¬ Stuck ρ s i) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) ≠ some .cell) ∧
      (∀ s i dst, l1 I.desc (tname dst) = true →
        waitKind ((ρ.cfg i).st s) ≠ some (.blockingSend dst)) := by
  intro N ρ hF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i s hp
    exact no_wait_cycle I hG hR (run_reachable ρ i) s hp
  · intro s i hk
    exact (local_and_credit_free I hR ρ hF s i).1 hk
  · intro s i hk
    exact (local_and_credit_free I hR ρ hF s i).2.1 hk
  · intro s i
    exact (local_and_credit_free I hR ρ hF s i).2.2.1
  · intro s i dst hl1 hk
    exact (local_and_credit_free I hR ρ hF s i).2.2.2 dst hl1 hk

end Deadlock
