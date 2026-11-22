/-
Aborting a child whose tombstone label is empty crashes the roster. The
effect stops there: the parent stays `dead` and `.crashed`, and does not
enter the `.internal` continuation.
-/
import Deadlock.Mail
import Deadlock.RunInv

set_option autoImplicit false

namespace Deadlock.AbortCrash
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
  tombstone := ""

def crashDesc : Description where
  name := "abort-crash"
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

def crashImpl : Impl where
  desc := crashDesc
  transitions := [trStop]

def rId : InstId := .peer "R" 0 0
def cId : InstId := .peer "C" 0 0

def kAbort : Cont where
  rest := [.abort, .internal]
  toState := "done"
  replyTo := none

def aR : Actor := { absentActor with life := .alive, phase := .run kAbort, typestate := "done" }

def aC : Actor := { absentActor with life := .alive, parent := some rId }

def w0 : World where
  N := 1
  roster := [rId, cId]
  nextIx := fun _ => 0
  st := fun i => if i = rId then aR else if i = cId then aC else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

def wAbort : World := execRun crashImpl w0 rId (w0.st rId) kAbort

theorem parent_dead : (wAbort.st rId).life = .dead := by
  rfl

theorem parent_stays_crashed : (wAbort.st rId).phase = .crashed := by
  rfl

theorem parent_not_running : (wAbort.st rId).phase ≠ .run (afterHead kAbort) := by
  rw [parent_stays_crashed]
  intro h
  cases h

theorem roster_crashed : wAbort.crashed = true := by
  rfl

/-- The parent stands on the landing of its only transition, which is what
`srcOk` asks of a running actor. -/
theorem parent_src :
    ∃ tr, tr ∈ crashImpl.transitions ∧ tr.template = tname rId ∧
      landsAt tr (w0.st rId).typestate ∧
      kAbort.toNotAdmitted = tr.toNotAdmitted ∧ kAbort.toTimedOut = tr.toTimedOut ∧
      kAbort.toTimeout = tr.toTimeout ∧ kAbort.toFull = tr.toFull ∧
      kAbort.toGone = tr.toGone ∧ kAbort.toState = (w0.st rId).typestate := by
  refine ⟨trStop, List.Mem.head _, rfl, Or.inl rfl, ?_⟩
  simp [kAbort, trStop, w0, aR]

/-- A non-absent actor is on the roster. That is `OpenSlots`. -/
theorem roster_open (id : InstId) (h : (w0.st id).life ≠ .absent) : id ∈ w0.roster := by
  by_cases hr : id = rId
  · simp [hr, w0]
  · by_cases hc : id = cId
    · simp [hc, w0]
    · simp [w0, hr, hc, absentActor] at h

theorem parent_phase_ok :
    (wAbort.st rId).phase = .idle ∨ (wAbort.st rId).phase = .crashed := by
  exact Or.inr parent_stays_crashed

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

theorem pre_sem : SemInv crashImpl w0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp [crashImpl, crashDesc, compatGroups] at hg
  · intro g hg
    simp [crashImpl, crashDesc, compatGroups] at hg
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

end Deadlock.AbortCrash
