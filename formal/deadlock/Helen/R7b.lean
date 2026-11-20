import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7b
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


/-! ## N11: a branch lands in a typestate whose floor is higher than `toState`'s.
`sendsOk` and the ingress gate use `sends + floor(landing)` on every path. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def landDesc (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Description where
  name := "branch-landing"
  freshNames := true
  templates := [tpl "A" cap ["idle", "w", "miss"] "idle" true]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" occW, sendEdge "A" "miss" "A" "M" occM]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "miss", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "A", fromState := "miss", toState := "miss", label := "M" }]

def landImpl (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Impl where
  desc := landDesc cap occW occM
  transitions := [{ tr "A" "idle" "Go" "w" [.peer [.send "A" "M" 0]] with toTimeout := "miss" },
                  tr "A" "w" "Go" "w" [],
                  tr "A" "miss" "Go" "w" (List.replicate (occW + 1) (.send "A" "M" 0)),
                  tr "A" "idle" "M" "idle" [],
                  tr "A" "w" "M" "w" [],
                  tr "A" "miss" "M" "miss" []]

def Ac : InstId := .core "A"

def landActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .callTimeout Ac, .exec Ac,
   .recvBulk Ac, .exec Ac, .exec Ac, .exec Ac]

def snap (w : World) : String × Nat × Nat × Int × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | _ => 3)

def LI : Impl := landImpl 4 2 0

theorem land_graph : checkBool (landDesc 4 2 0) = true := by decide

/-- The timeout path lands in `miss`. Its reserve is the send plus that floor,
which `idle` does not hold, so `LocalOk` rejects the design. -/
theorem land_local : localOkB LI = false := by decide

def landAt : BranchAt := { here := "w", timeout := "miss" }

theorem land_reserve :
    floorState (landDesc 4 2 0) "A" "idle" "A" = 2 ∧
      floorState (landDesc 4 2 0) "A" "w" "A" = 0 ∧
      floorState (landDesc 4 2 0) "A" "miss" "A" = 3 ∧
      pathReserve (landDesc 4 2 0) "A" "A" landAt [.peer [.send "A" "M" 0]] = 4 := by decide

/-- After the peer wait starts, the gate reserves the `miss` floor. The next
ingress, which used to spend those tokens, is disabled. -/
theorem land_gate :
    (runAt LI 0 (landActs.take 3)).isSome = true ∧
    runAt LI 0 (landActs.take 4) = none ∧
    ((runAt LI 0 (landActs.take 3)).map fun w =>
      (tokenHold (landDesc 4 2 0) "A" "A" (w.st Ac), (w.st Ac).tokens "A")) = some (4, 3) := by decide

/-- Dropping the `miss → A M` edge is rejected, and the reporter names that failure. -/
def noEdge : Impl := { landImpl 4 2 0 with desc := { landDesc 4 2 0 with edges := (landDesc 4 2 0).edges.take 3 } }
theorem reporter_gap :
    localOkB noEdge = false ∧ (localIssues noEdge).isEmpty = false := by decide

end Deadlock.Helen7b

#print axioms Deadlock.Helen7b.land_graph
#print axioms Deadlock.Helen7b.land_local
#print axioms Deadlock.Helen7b.land_reserve
#print axioms Deadlock.Helen7b.land_gate
#print axioms Deadlock.Helen7b.reporter_gap
