/-
One listener. The accept stage is a static core and does not terminate.
The detached completion is an ingress message, `Accepted` or `AcceptError`.
Both edges are non-blocking, so the stage does not wait on its own result.
One bulk slot is the outstanding bound: a second completion is refused
while the first sits in the box. That one fits `prioSized` for a single
priority sender and Lemma 1 for the mailbox. The handlers are empty, so the
core stays idle; a second result cannot arrive while the first is running.
Forwarding `Accepted` to a manager is a different edge, not this completion.
There is no listen tombstone and no respawn. The wiring is `examples/accept.json`.
-/
import Deadlock.Local
import Deadlock.Semantics

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Deadlock.Accept

open Deadlock

def acceptId : InstId := .core "accept"

def result (label : String) (occ legal : Nat) : Edge where
  src := "accept"
  srcState := "idle"
  dst := "accept"
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := Affine.ofNat occ
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat legal)
  cell := .none

def acceptT : Template where
  name := "accept"
  multiplicity := .one
  capacity := Affine.ofNat 1
  priorityCapacity := Affine.ofNat 1
  priorityBound := Affine.ofNat 1
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

def step (label : String) : CompatStep where
  template := "accept"
  fromState := "idle"
  toState := "idle"
  label := label

def tr (label : String) : Transition where
  template := "accept"
  fromState := "idle"
  label := label
  program := []
  toState := "idle"
  acceptsCall := false
  release := 1

def acceptDesc : Description where
  name := "accept"
  freshNames := true
  templates := [acceptT]
  edges := [result "Accepted" 1 1, result "AcceptError" 0 0]
  compatibility := .all
  steps := [step "Accepted", step "AcceptError"]

def acceptImpl : Impl where
  desc := acceptDesc
  transitions := [tr "Accepted", tr "AcceptError"]

/-- Messages of a detached accept completion. -/
def acceptResult (label : String) : Bool :=
  label == "Accepted" || label == "AcceptError"

/-- How many accept completions are queued at the listener. -/
def acceptOutstanding (w : World) : Nat :=
  ((w.st acceptId).box.filter fun m => acceptResult m.label).length

/-- One queued completion, an idle core, and the token that completion spent. -/
def boundFields (w : World) : Bool :=
  !w.crashed &&
    (w.st acceptId).life == .alive &&
    (w.st acceptId).phase == .idle &&
    (w.st acceptId).typestate == "idle" &&
    (w.st acceptId).parked == [] &&
    (w.st acceptId).prio == [] &&
    (w.st acceptId).box.length ≤ 1 &&
    ((w.st acceptId).box.all fun m => acceptResult m.label) &&
    ((w.st acceptId).tokens "accept" + ((w.st acceptId).box.length : Int)) == 1

theorem accept_checked : checkBool acceptDesc = true ∧ localOkB acceptImpl = true := by
  decide

/-- The completion edges are not waits. -/
theorem accept_no_wait : residualEdges acceptDesc = [] := by
  decide

/-- The outstanding bound of one fits a priority lane sized for one sender. -/
theorem accept_fits_prio : prioSized acceptDesc "accept" 1 = true := by
  decide

/-- The same bound fits the mailbox Lemma 1 uses. -/
theorem accept_fits_occ : l1 acceptDesc "accept" = true := by
  decide

theorem accept_cap (N : Nat) : capBulk acceptDesc N acceptId = 1 := by
  simp [capBulk, acceptId, tname, templateOf, acceptDesc, acceptT, Affine.eval, Affine.ofNat]

/-- A full bulk slot refuses another ingress, whichever label the environment offers.
`simp` rather than `split`: `receiveIngress` binds the actor and the capacity
with `have`, and `split` does not reach the capacity `if` through those. -/
theorem ingress_when_full (I : Impl) (w : World) (dst : InstId) (label : String)
    (hcap : capBulk I.desc w.N dst ≤ (w.st dst).box.length) :
    receiveIngress I w dst label = none := by
  simp [receiveIngress, hcap]

theorem outstanding_le (w : World) (hb : boundFields w = true) : acceptOutstanding w ≤ 1 := by
  simp only [boundFields, Bool.and_eq_true] at hb
  -- The length conjunct is `decide (box.length ≤ 1) = true`, so the inequality
  -- is `of_decide_eq_true`, not a field of `≤`.
  have hshort : (w.st acceptId).box.length ≤ 1 := of_decide_eq_true hb.1.1.2
  have hsub : acceptOutstanding w ≤ (w.st acceptId).box.length :=
    List.Sublist.length_le
      (List.filter_sublist (l := (w.st acceptId).box) (p := fun m => acceptResult m.label))
  exact Nat.le_trans hsub hshort

theorem init_bounded : boundFields (initWorld acceptImpl 0) = true := by
  decide

def after (w : Option World) (a : Action) : Option World :=
  w.bind (apply acceptImpl a)

def trace : Option World :=
  after (after (after (after (some (initWorld acceptImpl 0))
    (.ingress acceptId "Accepted"))
    (.recvBulk acceptId))
    (.ingress acceptId "AcceptError"))
    (.recvBulk acceptId)

def stepLive : Option World → Bool
  | none => false
  | some w =>
    boundFields w && (w.st acceptId).box == [] && (w.st acceptId).phase == Phase.idle && !w.crashed

/-- Both results are delivered, and the listener is still idle and not crashed. -/
theorem both_results_consumed : stepLive trace = true := by
  decide

/-- A second completion is refused while the first is still queued. -/
theorem second_completion_refused :
    (match apply acceptImpl (.ingress acceptId "Accepted") (initWorld acceptImpl 0) with
      | none => false
      | some w =>
        acceptOutstanding w == 1 &&
          (apply acceptImpl (.ingress acceptId "AcceptError") w).isNone &&
          (apply acceptImpl (.ingress acceptId "Accepted") w).isNone) = true := by
  decide

theorem outstanding_fits_budgets (w : World) (hb : boundFields w = true) :
    acceptOutstanding w ≤ 1 ∧ prioSized acceptDesc "accept" 1 = true ∧
      l1 acceptDesc "accept" = true :=
  ⟨outstanding_le w hb, accept_fits_prio, accept_fits_occ⟩

end Deadlock.Accept
