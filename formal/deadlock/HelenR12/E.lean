import Deadlock.Semantics
import Deadlock.Local
import Deadlock.Graph
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen10e
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

/-! ## E2: a non-terminable per-peer child's mail on a core outlives its key. -/
def eH : Template := { tpl "H" 1 ["idle"] "idle" true with capacity := { a := 1, b := 0 } }
def eR : Template := { tpl "R" 4 ["boot", "up"] "boot" true with
  multiplicity := .perPeer, subtree := "S", terminable := true, capacity := { a := 4, b := 4 } }
def eX : Template := { tpl "X" 4 ["idle", "sent"] "idle" true with
  multiplicity := .perPeer, subtree := "S", supervisor := some "R", tombstone := "dead/X", capacity := { a := 4, b := 4 } }
def eEdge : Edge := { (sendEdge "X" "sent" "H" "M" 0) with occupancy := { a := 1, b := 0 } }
def eDesc : Description where
  name := "dead-key-mail"
  freshNames := true
  templates := [eH, eR, eX]
  edges := [ingL "R" "boot" "Go", ingL "R" "up" "Kill", ingL "R" "up" "Go", ingL "R" "boot" "Kill",
            ingL "X" "idle" "Go", ingL "X" "sent" "Go", eEdge]
  compatibility := .all
  steps := [step "R" "boot" "dead/X" "boot", step "R" "up" "dead/X" "up", step "R" "boot" "Go" "up", step "R" "up" "Kill" "up", step "R" "up" "Go" "up",
            step "R" "boot" "Kill" "boot", step "X" "idle" "Go" "sent", step "X" "sent" "Go" "sent", step "H" "idle" "M" "idle"]
def eImpl : Impl where
  desc := eDesc
  transitions := [tr "R" "boot" "dead/X" "boot" [], tr "R" "up" "dead/X" "up" [], tr "R" "boot" "Go" "up" [.spawn "X"], tr "R" "up" "Kill" "up" [.terminate],
                  tr "R" "up" "Go" "up" [], tr "R" "boot" "Kill" "boot" [],
                  tr "X" "idle" "Go" "sent" [.send "H" "M" 0], tr "X" "sent" "Go" "sent" [], tr "H" "idle" "M" "idle" []]

#eval render eDesc
#eval localIssues eImpl
#eval (l1 eDesc "H", (totalOcc eDesc "H").eval 1, budget eDesc "X" "H")

def R0 : InstId := .peer "R" 0 0
def R1 : InstId := .peer "R" 1 0
def X0 : InstId := .peer "X" 0 0
def X1 : InstId := .peer "X" 1 0
def Hc : InstId := .core "H"
def life1 : List Action :=
  [.spawn "R", .ingress R0 "Go", .recvBulk R0, .exec R0,
   .ingress X0 "Go", .recvBulk X0, .exec X0,
   .ingress R0 "Kill", .recvBulk R0, .exec R0, .exec R0]
def life2 : List Action :=
  [.spawn "R", .ingress R1 "Go", .recvBulk R1, .exec R1, .ingress X1 "Go", .recvBulk X1, .exec X1]
def snap (w : World) :=
  (lifeTag (w.st X0).life, lifeTag (w.st X1).life, (w.st Hc).box.length, (w.st Hc).parked.length,
   (w.st X1).tokens "H", pending (w.st X1) "H", capBulk eDesc w.N Hc, toString (repr (w.st X1).phase).pretty.length)
#eval (runAt eImpl 1 life1).map fun w => (lifeTag (w.st X0).life, (w.st Hc).box.length)
#eval (runAt eImpl 1 (life1 ++ (life2.take 6))).map snap
#eval (runAt eImpl 1 (life1 ++ life2)).map snap
end Deadlock.Helen10e
