import Deadlock

set_option autoImplicit false

namespace Deadlock.Review
open Deadlock

/-- Every actor idle with empty bulk box, priority lane, and parked list. -/
def Quiet (w : World) : Prop :=
  ∀ id, (w.st id).phase = .idle ∧ (w.st id).box = [] ∧ (w.st id).prio = [] ∧ (w.st id).parked = []

theorem readCells_st (D : Description) (w : World) (r : InstId) : (readCells D w r).st = w.st := by
  unfold readCells
  induction cellLabels D (tname r) generalizing w with
  | nil => rfl
  | cons l ls ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem readCells_val (D : Description) (w : World) (r : InstId) (d l : String) :
    ((readCells D w r).cell d l).value = (w.cell d l).value := by
  unfold readCells
  induction cellLabels D (tname r) generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]; rw [ih]
    simp only [setObserved, setCell]
    split <;> simp_all

theorem foldl_readCells_st (D : Description) (ids : List InstId) (w : World) :
    (ids.foldl (fun w id => readCells D w id) w).st = w.st := by
  induction ids generalizing w with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons]; rw [ih, readCells_st]

theorem foldl_readCells_val (D : Description) (ids : List InstId) (w : World) (d l : String) :
    ((ids.foldl (fun w id => readCells D w id) w).cell d l).value = (w.cell d l).value := by
  induction ids generalizing w with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons]; rw [ih, readCells_val]

theorem quiet_init (I : Impl) (N : Nat) : Quiet (initWorld I N) := by
  intro id
  simp only [initWorld]
  rw [foldl_readCells_st]
  dsimp only
  split
  · unfold initActor withTokens
    split <;> simp [absentActor]
  · simp [absentActor]

theorem val_init (I : Impl) (N : Nat) (d l : String) : ((initWorld I N).cell d l).value = 0 := by
  simp only [initWorld]; rw [foldl_readCells_val]; rfl

/-- From a quiet world, the only applicable action is `spawn`, and it yields a quiet
world with unchanged cell values. -/
theorem step_quiet (I : Impl) (w w' : World) (a : Action) (hq : Quiet w)
    (h : apply I a w = some w') : Quiet w' ∧ ∀ d l, (w'.cell d l).value = (w.cell d l).value := by
  cases a with
  | recvBulk s =>
    obtain ⟨_, hb, _, hp⟩ := hq s
    simp only [apply, receiveBulk, hb, hp] at h
    split at h <;> simp_all
  | recvPrio s =>
    obtain ⟨_, _, hpr, _⟩ := hq s
    simp [apply, receivePrio, hpr] at h
  | exec s =>
    obtain ⟨hph, _, _, _⟩ := hq s
    simp only [apply, execHead, hph] at h
    split at h <;> simp_all
  | finish s =>
    obtain ⟨hph, _, _, _⟩ := hq s
    simp [apply, finishWait, hph] at h
  | spawn t =>
    simp only [apply, spawn] at h
    split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨?_, ?_⟩
        · intro id
          rw [readCells_st]
          simp only [setActor]
          split
          · simp [withTokens]
          · exact hq id
        · intro d l
          rw [readCells_val]
          rfl
      · simp at h

theorem run_quiet (I : Impl) (N : Nat) (ρ : Run I N) :
    ∀ i, Quiet (ρ.cfg i) ∧ ∀ d l, ((ρ.cfg i).cell d l).value = 0 := by
  intro i
  induction i with
  | zero => rw [ρ.start]; exact ⟨quiet_init I N, val_init I N⟩
  | succ n ih =>
    obtain ⟨hq, hv⟩ := ih
    obtain ⟨hq', hv'⟩ := step_quiet I _ _ _ hq (ρ.valid n)
    exact ⟨hq', fun d l => (hv' d l).trans (hv d l)⟩

/-- Both headline conclusions hold for EVERY run of EVERY Impl, with no
LocalOk, GraphOk, Assumptions, or Fair hypothesis. -/
theorem vacuous (I : Impl) (N : Nat) (ρ : Run I N) : ¬ Deadlock ρ ∧ CellFresh ρ := by
  have hq := run_quiet I N ρ
  refine ⟨?_, ?_⟩
  · rintro ⟨s, i, hS, _⟩
    have := (hq i).1 s
    have hw : waitKind ((ρ.cfg i).st s) = none := by simp [waitKind, this.1]
    exact hS.1.2 hw
  · intro i dst label _ hlt
    rw [(hq i).2, (hq (i+1)).2] at hlt
    exact absurd hlt (Nat.lt_irrefl 0)

end Deadlock.Review

#print axioms Deadlock.Review.vacuous
