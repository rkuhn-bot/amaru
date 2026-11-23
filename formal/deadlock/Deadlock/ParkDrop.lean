import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock.ParkDrop

/-!
Sealing a subtree member drops a parked call while the caller stays parked.

`releaseWorld` clears the sealed actor's parked list and resumes only
non-call parked senders. A caller in `.parked dst true` is left there.
`execRun` takes that path for a per-peer template whose subtree is nonempty,
without consulting `hasParkedCall`. One `exec` step from a world that has
the entry reaches a world that does not.
-/

def boxT : Template :=
  { name := "box", multiplicity := .perPeer, capacity := Affine.ofNat 1,
    priorityCapacity := Affine.ofNat 1, priorityBound := Affine.ofNat 1,
    states := ["idle"], initial := "idle", terminable := true, subtree := "tree",
    untimedPeer := false, mustFit := true }

def callerT : Template :=
  { name := "caller", multiplicity := .one, capacity := Affine.ofNat 1,
    priorityCapacity := Affine.ofNat 1, priorityBound := Affine.ofNat 1,
    states := ["idle"], initial := "idle", terminable := false,
    untimedPeer := false, mustFit := true }

def dropDesc : Description :=
  { name := "parkdrop", freshNames := false, templates := [boxT, callerT], edges := [],
    compatibility := .all, steps := [], cellEffects := [] }

def dropImpl : Impl :=
  { desc := dropDesc, transitions := [] }

def callee : InstId := .peer "box" 0 0

def caller : InstId := .core "caller"

def waitK : Cont :=
  { toState := "idle", replyTo := none, rest := [] }

def termK : Cont :=
  { toState := "idle", replyTo := none, rest := [.terminate] }

def callMsg : Msg :=
  { label := "ask", sender := caller, callFrom := some caller }

def entry : Parked :=
  { sender := caller, msg := callMsg, isCall := true }

def calleeA : Actor :=
  { life := .alive, typestate := "idle", phase := .run termK,
    box := [], prio := [], parked := [entry], tokens := fun _ => 1, parent := none }

def callerA : Actor :=
  { life := .alive, typestate := "idle", phase := .parked callee true waitK,
    box := [], prio := [], parked := [], tokens := fun _ => 1, parent := none }

def dropWorld : World :=
  { N := 0, roster := [callee, caller], nextIx := fun _ => 0,
    st := fun i => if i = callee then calleeA else if i = caller then callerA else absentActor,
    cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

theorem before_phase : (dropWorld.st caller).phase = .parked callee true waitK := by
  simp [dropWorld, caller, callee, callerA]

theorem before_entry :
    ((dropWorld.st callee).parked.filter fun p => p.sender == caller && p.isCall) = [entry] := by
  simp [dropWorld, callee, caller, calleeA, entry, callMsg]

/-- `box` is a per-peer member of a nonempty subtree, so `terminate` seals it. -/
theorem box_template : templateOf dropDesc (tname callee) = some boxT := by
  simp [templateOf, dropDesc, tname, callee, boxT, callerT]

theorem box_not_core : (boxT.multiplicity == .one) = false := by
  decide

theorem box_subtree : ((boxT.multiplicity == .perPeer) = true ∧ ¬ boxT.subtree = "") := by
  decide

/-- No cell edge, so reading cells leaves the world alone. -/
theorem cells_id : readCells dropDesc dropWorld callee = dropWorld := by
  simp [readCells, cellLabels, dropDesc]

/-- The mailbox is empty, so the refund is the identity. -/
theorem msgs_id : refundMsgs dropWorld (tname callee) calleeA.box = dropWorld := by
  simp [refundMsgs, calleeA]

/-- The one parked call is credited to the caller. -/
theorem park_credit :
    refundParked dropWorld (tname callee) calleeA.parked =
      creditLive dropWorld (tname callee) caller := by
  simp [refundParked, calleeA, entry, callMsg]

def wCred : World := creditLive dropWorld (tname callee) caller

theorem cred_st_caller : (wCred.st caller).phase = .parked callee true waitK ∧
    (wCred.st caller).parked = [] ∧ (wCred.st caller).life = .alive := by
  simp [wCred, creditLive, budgetHolder, creditSender, bumpToken, setActor, dropWorld,
    caller, callee, callerA]

theorem cred_st_callee : (wCred.st callee) = calleeA := by
  simp [wCred, creditLive, budgetHolder, creditSender, setActor, dropWorld, caller, callee, calleeA]

theorem cred_parent : (wCred.st callee).parent = none := by
  simp [cred_st_callee, calleeA]

/-- The caller holds nothing sent by the callee, so the outbound pass is the identity. -/
theorem out_id : releaseOutbound wCred callee = wCred := by
  simp [releaseOutbound, wCred, creditLive, budgetHolder, creditSender, bumpToken, setActor,
    dropWorld, caller, callee, callerA, calleeA, entry, List.filter, List.isEmpty]

def deadA : Actor :=
  { calleeA with life := .dead, phase := .idle, box := [], prio := [], parked := [] }

def wDead : World := setActor wCred callee deadA

/-- Installing the dead actor clears its parked list and leaves the caller parked. -/
theorem dead_caller : (wDead.st caller).phase = .parked callee true waitK := by
  simp [wDead, setActor, caller, callee]
  exact cred_st_caller.1

theorem dead_parked : (wDead.st callee).parked = [] := by
  simp [wDead, deadA, setActor, callee]

theorem dead_life : (wDead.st callee).life = .dead := by
  simp [wDead, deadA, setActor, callee]

theorem dead_parent : (wDead.st callee).parent = none := by
  simp [wDead, deadA, setActor, callee, calleeA]

/-- The parked entry is a call, so the resume pass leaves both actors alone. -/
theorem resume_id : releaseParked wDead callee [entry] = wDead := by
  simp [releaseParked, entry]

theorem tomb_id : enqueueTombstone dropDesc wDead callee = wDead := by
  simp [enqueueTombstone, dead_parent]

/-- `releaseWorld` is the dead actor plus the caller's refunded token.
The lets inside `releaseWorld` are zeta-reduced with `dsimp` before
rewriting, and the outbound identity is stated on `creditLive` rather
than on the `wCred` abbreviation, which `rw` does not unfold. -/
theorem release_eq : releaseWorld dropDesc dropWorld callee calleeA = wDead := by
  unfold releaseWorld
  dsimp
  rw [cells_id, msgs_id, park_credit]
  have hout : releaseOutbound (creditLive dropWorld (tname callee) caller) callee =
      creditLive dropWorld (tname callee) caller := by
    simpa [wCred] using out_id
  rw [hout]
  have hcal : ((creditLive dropWorld (tname callee) caller).st callee) = calleeA := by
    simpa [wCred] using cred_st_callee
  rw [hcal]
  have hdead :
      { calleeA with life := .dead, phase := .idle, box := [], prio := [], parked := [] } = deadA := rfl
  rw [hdead]
  have hset : setActor (creditLive dropWorld (tname callee) caller) callee deadA = wDead := by
    simp [wDead, wCred]
  rw [hset]
  simp only [calleeA]
  rw [resume_id]

theorem descendants_id : dropDescendants dropDesc dropWorld callee = dropWorld := by
  simp [dropDescendants, dropWorld, isChild, caller, callee, calleeA, callerA]

theorem shutdown_eq : shutdownActor dropDesc dropWorld callee = wDead := by
  unfold shutdownActor
  have hlive : ((dropWorld.st callee).life == .alive) = true := by
    simp [dropWorld, callee, calleeA]
  rw [hlive]
  simp only [ite_true, sealActor]
  have hst : dropWorld.st callee = calleeA := by simp [dropWorld, callee, caller]
  rw [hst, release_eq, tomb_id]

/-- The seal of `callee` is one `exec` step. The caller is still parked on
the call, and the callee's parked list is empty. -/
theorem seal_drops_parked_call :
    ∃ w', apply dropImpl (.exec callee) dropWorld = some w' ∧
      (w'.st caller).phase = .parked callee true waitK ∧
      (w'.st callee).parked = [] ∧
      (w'.st callee).life = .dead := by
  refine ⟨wDead, ?_, dead_caller, dead_parked, dead_life⟩
  have hst : dropWorld.st callee = calleeA := by simp [dropWorld, callee, caller]
  have hrun : execRun dropImpl dropWorld callee calleeA termK =
      terminateStage dropDesc dropWorld callee calleeA := by
    simp [execRun, calleeA, termK, dropImpl, box_template, box_not_core, box_subtree]
  unfold apply
  have hc : dropWorld.crashed = false := rfl
  rw [hc]
  simp only [stepWorld, execHead, hst, calleeA]
  have hne : ¬ (Life.alive ≠ Life.alive) := by intro h; exact h rfl
  rw [if_neg hne]
  have hact :
      ({ life := .alive, typestate := "idle", phase := .run termK, box := [], prio := [],
          parked := [entry], tokens := fun (_ : String) => 1 } : Actor) = calleeA := rfl
  rw [hact, hrun]
  unfold terminateStage
  rw [descendants_id, shutdown_eq]

end Deadlock.ParkDrop
