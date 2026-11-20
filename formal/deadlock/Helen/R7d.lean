import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7d
open Deadlock

/-! Copied verbatim from Examples.lean:8-33 (Examples cannot be imported beside
Semantics: both declare `Deadlock.overflowDesc`). -/
def tpl (name : String) (cap : Nat) (states : List String) (initial : String) (mustFit : Bool) : Template where
  name := name
  multiplicity := .one
  capacity := .ofNat cap
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 1
  states := states
  initial := initial
  terminable := false
  untimedPeer := false
  mustFit := mustFit

def sendEdge (src ss dst label : String) (occ : Nat) : Edge where
  src := src
  srcState := ss
  dst := dst
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := label
  scope := .intra
  occupancy := .ofNat occ
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := false, release := 1 }

def runAt (I : Impl) (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply I a)) (some (initWorld I N))


/-! ## N12: a parked call's pending is `contSends`, plus its own message on `TimedOut`. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def pcDesc (capA capB k : Nat) : Description where
  name := "parked-call"
  freshNames := true
  templates := [tpl "A" capA ["idle", "w"] "idle" true, tpl "B" capB ["idle"] "idle" false]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" k,
            { (sendEdge "A" "w" "B" "Q" 1) with effect := .call, repliesInDequeue := true }]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Q" }]

def trc (t f l to : String) (p : List Eff) (c : Bool) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := c, release := 1 }

def pcImpl (capA capB k : Nat) : Impl where
  desc := pcDesc capA capB k
  transitions := [trc "A" "idle" "Go" "w" [.call "B" "Q" 0 [] (List.replicate k (.send "A" "M" 0))] false,
                  trc "A" "w" "Go" "w" [] false,
                  trc "A" "idle" "M" "idle" [] false,
                  trc "A" "w" "M" "w" [] false,
                  trc "B" "idle" "Q" "idle" [.reply] true]

def Ac : InstId := .core "A"
def Bc : InstId := .core "B"

def snap (w : World) : String × Nat × Nat × Nat × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | .awaitReply _ _ => 4 | _ => 3)
def pcActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .ingress Ac "Go",
   .recvBulk Bc, .callTimeout Ac, .exec Ac, .exec Ac, .exec Bc]
def PI : Impl := pcImpl 4 0 2

theorem pc_graph : checkBool (pcDesc 4 0 2) = true := by decide
theorem pc_local : LocalOk PI := by unfold LocalOk; decide

/-- While the call is parked, `pending` is `contSends` with the call's own
message added on `TimedOut`: two sends to A, and the call itself went to B. -/
theorem pc_pending :
    ((runAt PI 0 (pcActs.take 3)).map fun w =>
      (pending (w.st Ac) "A", (w.st Ac).tokens "A")) = some (2, 3) ∧
    ((runAt PI 0 (pcActs.take 4)).map fun w =>
      ((w.st Ac).box.length, (w.st Ac).tokens "A")) = some (1, 2) ∧
    runAt PI 0 (pcActs.take 5) = none := by decide

/-- A parked self-call counts its own message on `TimedOut`. `contSends` does
not, because that message was already issued. -/
def ownK : Cont := { rest := [], toState := "w", replyTo := none, onTimedOut := [.send "A" "M" 0] }
def ownActor : Actor :=
  { initActor (pcDesc 4 0 2) (.core "A") with phase := .parked (.core "A") true ownK, typestate := "w" }

theorem own_on_timed_out :
    contSends "A" ownK = 1 ∧ pending ownActor "A" = 2 := by decide

end Deadlock.Helen7d

#print axioms Deadlock.Helen7d.pc_graph
#print axioms Deadlock.Helen7d.pc_local
#print axioms Deadlock.Helen7d.pc_pending
#print axioms Deadlock.Helen7d.own_on_timed_out
