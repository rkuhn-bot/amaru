/-
A parent pointer cycle is not a crash, and it is not a reachable world.
`R` parents `C` and `C` parents `R`. Aborting `R` seals `C`, and sealing
`C` seals `R` as its descendant. The world is not crashed, so `commitCont`
installs the continuation: the parent is dead and `.run`. The pre-state is
a `SemInv` and a `MailInv`, and it is not `ParentAcyclic`, so it is outside
`Inv`.
-/
import Deadlock.Mail
import Deadlock.RunInv

set_option autoImplicit false

namespace Deadlock.ParentCycle
open Deadlock

def tR : Template where
  name := "R"
  multiplicity := .perPeer
  capacity := { a := 0, b := 1 }
  priorityCapacity := { a := 0, b := 4 }
  priorityBound := { a := 0, b := 4 }
  states := ["up", "done"]
  initial := "up"
  terminable := true
  untimedPeer := false
  mustFit := true

def tC : Template where
  name := "C"
  multiplicity := .perPeer
  capacity := { a := 0, b := 1 }
  priorityCapacity := { a := 0, b := 1 }
  priorityBound := { a := 0, b := 1 }
  states := ["idle"]
  initial := "idle"
  terminable := true
  untimedPeer := false
  mustFit := true
  supervisor := some "R"
  tombstone := "died"

def cycleDesc : Description where
  name := "parent-cycle"
  freshNames := true
  templates := [tR, tC]
  edges := []
  compatibility := .all
  steps := []

def trStop : Transition where
  template := "R"
  fromState := "up"
  label := "Stop"
  program := [.abort, .internal]
  toState := "done"
  acceptsCall := false
  release := 1

def cycleImpl : Impl where
  desc := cycleDesc
  transitions := [trStop]

def rId : InstId := .peer "R" 0 0
def cId : InstId := .peer "C" 0 0

def kAbort : Cont where
  rest := [.abort, .internal]
  toState := "done"
  replyTo := none

def aR : Actor :=
  { absentActor with life := .alive, phase := .run kAbort, typestate := "done", parent := some cId }

def aC : Actor := { absentActor with life := .alive, parent := some rId }

def w0 : World where
  N := 1
  roster := [rId, cId]
  nextIx := fun _ => 0
  st := fun i => if i = rId then aR else if i = cId then aC else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

def wAbort : World := execRun cycleImpl w0 rId (w0.st rId) kAbort

theorem not_crashed : wAbort.crashed = false := by
  rfl

theorem parent_dead : (wAbort.st rId).life = .dead := by
  rfl

theorem parent_still_running : (wAbort.st rId).phase = .run (afterHead kAbort) := by
  rfl

theorem parent_not_idle :
    (wAbort.st rId).phase ≠ .idle ∧ (wAbort.st rId).phase ≠ .crashed := by
  rw [parent_still_running]
  constructor
  · intro h
    cases h
  · intro h
    cases h

private theorem child_ne : cId ≠ rId := by
  decide

private theorem parked_empty (i : InstId) : (w0.st i).parked = [] := by
  by_cases hr : i = rId
  · simp [w0, hr, aR, absentActor]
  · by_cases hc : i = cId
    · simp [w0, hc, child_ne, aC, absentActor]
    · simp [w0, hr, hc, absentActor]

theorem pre_mail : MailInv w0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    simp [parked_empty] at hp
  · intro id dst isCall k hk
    by_cases hr : id = rId
    · simp [w0, hr, aR, kAbort] at hk
    · by_cases hc : id = cId
      · simp [w0, hc, child_ne, aC, absentActor] at hk
      · simp [w0, hr, hc, absentActor] at hk
  · intro mb1 mb2 p1 p2 h1 h2 _
    simp [parked_empty] at h1
  · intro mb
    simp [parked_empty]

theorem pre_sem : SemInv cycleImpl w0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp [cycleImpl, cycleDesc, compatGroups] at hg
  · intro g hg
    simp [cycleImpl, cycleDesc, compatGroups] at hg
  · intro id
    by_cases hr : id = rId
    · simp [w0, hr, aR, kAbort, contTy]
    · by_cases hc : id = cId
      · simp [w0, hc, child_ne, aC, absentActor, contTy]
      · simp [w0, hr, hc, absentActor, contTy]
  · intro id
    by_cases hr : id = rId
    · simp [w0, hr, aR, kAbort, programOk, effectsOk, effectOk]
    · by_cases hc : id = cId
      · simp [w0, hc, child_ne, aC, absentActor, programOk]
      · simp [w0, hr, hc, absentActor, programOk]
  · intro id
    by_cases hr : id = rId
    · simp [w0, hr, aR, waitEdge]
    · by_cases hc : id = cId
      · simp [w0, hc, child_ne, aC, absentActor, waitEdge]
      · simp [w0, hr, hc, absentActor, waitEdge]
  · intro id hne
    by_cases hr : id = rId
    · simp [w0, hr, aR] at hne
    · by_cases hc : id = cId
      · simp [w0, hc, child_ne, aC] at hne
      · simp [w0, hr, hc, absentActor]
  · intro id hlive
    by_cases hr : id = rId
    · simp [hr, w0]
    · by_cases hc : id = cId
      · simp [hc, w0]
      · simp [w0, hr, hc, absentActor] at hlive
  · intro id _
    simp [parked_empty]

/-- Every actor that is not absent is on the roster. That is `OpenSlots`. -/
theorem roster_open (id : InstId) (h : (w0.st id).life ≠ .absent) : id ∈ w0.roster := by
  by_cases hr : id = rId
  · simp [hr, w0]
  · by_cases hc : id = cId
    · simp [hc, w0]
    · simp [w0, hr, hc, absentActor] at h

/-- The running parent is on the landing of its only transition. That is `srcOk`,
which is `outcomeOk` for a `.run` phase. Every other actor is `.idle`, where
`outcomeOk` is `True`. -/
theorem parent_src :
    ∃ tr, tr ∈ cycleImpl.transitions ∧ tr.template = tname rId ∧
      landsAt tr (w0.st rId).typestate ∧
      kAbort.toNotAdmitted = tr.toNotAdmitted ∧ kAbort.toTimedOut = tr.toTimedOut ∧
      kAbort.toTimeout = tr.toTimeout ∧ kAbort.toFull = tr.toFull ∧
      kAbort.toGone = tr.toGone ∧ kAbort.toState = (w0.st rId).typestate := by
  refine ⟨trStop, List.Mem.head _, rfl, Or.inl rfl, ?_⟩
  simp [kAbort, trStop, w0, aR]

theorem child_idle : (w0.st cId).phase = .idle := by
  rfl

theorem edge_cr : ParentEdge w0 cId rId := by
  refine ⟨?_, child_ne⟩
  simp [w0, aC, child_ne]

theorem edge_rc : ParentEdge w0 rId cId := by
  refine ⟨?_, child_ne.symm⟩
  simp [w0, aR]

/-- The pre-state is its own ancestor, so it is not the parent forest `Inv` requires. -/
theorem pre_not_acyclic : ¬ ParentAcyclic w0 := by
  intro h
  exact ParentAcyclic.no_self h rId
    (StrictAncestor.tail edge_rc (StrictAncestor.edge edge_cr))

theorem post_not_sem (h : SemInv cycleImpl wAbort) : False := by
  have hdead : (wAbort.st rId).life ≠ .alive := by
    rw [parent_dead]
    intro hlife
    cases hlife
  have hdisj := h.idleOff rId hdead
  rw [parent_still_running] at hdisj
  cases hdisj with
  | inl hphase => cases hphase
  | inr hphase => cases hphase

end Deadlock.ParentCycle
