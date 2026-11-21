import Deadlock.Semantics
import Deadlock.Local
import Deadlock.Graph
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen10g
open Deadlock

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
def ing (t st : String) : Edge :=
  { (sendEdge t st t "Go" 1) with effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := true, occupancy := { a := 1, b := 0 }, ingressLegal := some (Affine.ofNat 1) }
def step (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }

/-- Branch R8c mailDesc, unchanged. -/
def ingL (t st l : String) : Edge := { ing t st with label := l }
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
/-! ## E1: an orphaned grandchild blocks the restarted child's spawn. -/
def gR : Template := { tpl "R" 4 ["boot", "up"] "boot" true with
  multiplicity := .perPeer, subtree := "S", terminable := true, capacity := { a := 4, b := 4 } }
def gC : Template := { tpl "C" 4 ["idle", "has"] "idle" true with
  multiplicity := .perPeer, subtree := "S", supervisor := some "R", terminable := true,
  tombstone := "dead/C", capacity := { a := 8, b := 8 } }
def gG : Template := { tpl "G" 4 ["idle"] "idle" true with
  multiplicity := .perPeer, subtree := "S", supervisor := some "C", terminable := true,
  tombstone := "dead/G", capacity := { a := 4, b := 4 } }
def gDesc : Description where
  name := "orphan-grandchild"
  freshNames := true
  templates := [gR, gC, gG]
  edges := [ingL "R" "boot" "Go", ingL "R" "boot" "dead/C", ingL "R" "up" "Go", ingL "R" "up" "dead/C", ingL "C" "idle" "Go", ingL "C" "has" "Go",
            ingL "C" "idle" "Die", ingL "C" "has" "Die", ingL "C" "idle" "dead/G", ingL "C" "has" "dead/G",
            ingL "G" "idle" "Die"]
  compatibility := .all
  steps := [step "R" "boot" "Go" "up", step "R" "boot" "dead/C" "boot", step "R" "up" "Go" "up", step "R" "up" "dead/C" "up",
            step "C" "idle" "Go" "has", step "C" "has" "Go" "has",
            step "C" "idle" "Die" "idle", step "C" "has" "Die" "has",
            step "C" "idle" "dead/G" "idle", step "C" "has" "dead/G" "has",
            step "G" "idle" "Die" "idle"]
def gImpl : Impl where
  desc := gDesc
  transitions := [tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "boot" "dead/C" "boot" [],
                  tr "R" "up" "Go" "up" [], tr "R" "up" "dead/C" "up" [.spawn "C"],
                  tr "C" "idle" "Go" "has" [.spawn "G"], tr "C" "has" "Go" "has" [],
                  tr "C" "idle" "Die" "idle" [.terminate], tr "C" "has" "Die" "has" [.terminate],
                  tr "C" "idle" "dead/G" "idle" [], tr "C" "has" "dead/G" "has" [],
                  tr "G" "idle" "Die" "idle" [.terminate]]


/-! ## E3: a supervised child with no tombstone label terminates. -/
def gG3 : Template := { gG with tombstone := "" }
def gDesc3 : Description where
  name := "no-label"
  freshNames := true
  templates := [gR, gC, gG3]
  edges := gDesc.edges.filter (fun e => e.label != "dead/G")
  compatibility := .all
  steps := gDesc.steps.filter (fun s => s.label != "dead/G")
def gImpl3 : Impl where
  desc := gDesc3
  transitions := gImpl.transitions.filter (fun t => t.label != "dead/G")
#eval (render gDesc3, localIssues gImpl3)
#eval (runAt gImpl3 1 [.spawn "R", .ingress (.peer "R" 0 0) "Go", .recvBulk (.peer "R" 0 0), .exec (.peer "R" 0 0),
   .ingress (.peer "C" 0 0) "Go", .recvBulk (.peer "C" 0 0), .exec (.peer "C" 0 0),
   .ingress (.peer "G" 0 0) "Die", .recvBulk (.peer "G" 0 0), .exec (.peer "G" 0 0), .exec (.peer "G" 0 0)]).map (·.crashed)
#eval render gDesc
#eval localIssues gImpl
#eval (prioSized gDesc "R" (prioSenderBound gImpl "R"), prioSized gDesc "C" (prioSenderBound gImpl "C"))

def R0 : InstId := .peer "R" 0 0
def C0 : InstId := .peer "C" 0 0
def C1 : InstId := .peer "C" 0 1
def G0 : InstId := .peer "G" 0 0
def G1 : InstId := .peer "G" 0 1
def acts : List Action :=
  [.spawn "R", .ingress R0 "Go", .recvBulk R0, .exec R0,          -- R births C@0.0
   .ingress C0 "Go", .recvBulk C0, .exec C0,                       -- C@0.0 births G@0.0
   .ingress C0 "Die", .recvBulk C0, .exec C0,                      -- C marks itself and G
   .exec C0,                                                       -- C seals: dead/C#0 on R
   .recvPrio R0, .exec R0,                                         -- R consumes it, births C@0.1
   .ingress C1 "Go", .recvBulk C1, .exec C1]                       -- C@0.1 spawns G: no-op?
def snapG (w : World) :=
  (w.crashed, lifeTag (w.st C0).life, lifeTag (w.st C1).life, lifeTag (w.st G0).life,
   lifeTag (w.st G1).life, (w.st C1).typestate, decide (G1 ∈ w.roster),
   (w.st G0).parent.map fun p => toString (repr p).pretty)
#eval (runAt gImpl 1 acts).map snapG
-- G@0.0 seals later; its recorded parent C@0.0 is dead, so the tombstone is dropped.
#eval (runAt gImpl 1 (acts ++ [.exec G0])).map fun w =>
  (snapG w, (w.st C1).prio.length, route w gDesc C1 "G")
-- Same C@0.1 "Go" after G@0.0 sealed: still no-op? (C@0.1 is in `has`, its Go is []).
end Deadlock.Helen10g
