/-
A grandchild is sealed with its parent.

`terminate` of `C` seals `G` in that step. `G` is dead, so it does not occupy
the slot. `R` consumes `dead/C` and births the next `C`, and that `C` births
a new `G` at the same key. The new grandchild's parent is the new `C`.
-/
import Deadlock.Semantics
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Deadlock.Orphan
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

def ing (t st : String) : Edge :=
  { (sendEdge t st t "Go" 1) with effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := true, occupancy := { a := 1, b := 0 }, ingressLegal := some (Affine.ofNat 1) }

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := false, release := 1 }

def step (t f l to : String) : CompatStep :=
  { template := t, fromState := f, toState := to, label := l }

def tR : Template := { tpl "R" 4 ["idle", "up"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 4, b := 1 }, terminable := true, subtree := "S" }
def tC : Template := { tpl "C" 4 ["idle", "up", "done"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 4, b := 1 }, terminable := true, subtree := "S",
  supervisor := some "R", tombstone := "dead/C" }
def tG : Template := { tpl "G" 4 ["idle"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 4, b := 1 }, terminable := true, subtree := "S",
  supervisor := some "C", tombstone := "dead/G" }

def orphanDesc : Description where
  name := "orphan"
  freshNames := true
  templates := [tR, tC, tG]
  edges := [ing "R" "idle", ing "R" "up", ing "C" "idle", ing "C" "up", ing "C" "done", ing "G" "idle"]
  compatibility := .all
  steps := [step "R" "idle" "Go" "up", step "R" "idle" "dead/C" "idle",
            step "R" "up" "dead/C" "up", step "R" "up" "Go" "up",
            step "C" "idle" "Go" "up", step "C" "idle" "dead/G" "idle",
            step "C" "up" "Go" "done", step "C" "up" "dead/G" "up",
            step "C" "done" "Go" "done", step "C" "done" "dead/G" "done",
            step "G" "idle" "Go" "idle"]

def orphanImpl : Impl where
  desc := orphanDesc
  transitions := [tr "R" "idle" "Go" "up" [.spawn "C"],
                  tr "R" "up" "dead/C" "up" [.spawn "C"],
                  tr "C" "idle" "Go" "up" [.spawn "G"],
                  tr "C" "up" "Go" "done" [.terminate],
                  tr "R" "up" "Go" "up" [],
                  tr "R" "idle" "dead/C" "idle" [],
                  tr "C" "done" "Go" "done" [],
                  tr "C" "idle" "dead/G" "idle" [],
                  tr "C" "up" "dead/G" "up" [],
                  tr "C" "done" "dead/G" "done" [],
                  tr "G" "idle" "Go" "idle" []]

def runAt (I : Impl) (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply I a)) (some (initWorld I N))

def lifeTag (l : Life) : Nat :=
  match l with
  | .absent => 0
  | .alive => 1
  | .dead => 2

def R0 : InstId := .peer "R" 0 0
def C0 : InstId := .peer "C" 0 0
def C1 : InstId := .peer "C" 0 1
def G0 : InstId := .peer "G" 0 0
def G1 : InstId := .peer "G" 0 1

def birth : List Action :=
  [.spawn "R", .ingress R0 "Go", .recvBulk R0, .exec R0,
   .ingress C0 "Go", .recvBulk C0, .exec C0]

def killed : List Action :=
  birth ++ [.ingress C0 "Go", .recvBulk C0, .exec C0]

/-- `C`'s terminate seals `C` and `G` in that `exec`. The restart is the parent's
receive of `C`'s tombstone. -/
def restarted : List Action :=
  killed ++ [.recvPrio R0, .exec R0, .ingress C1 "Go", .recvBulk C1, .exec C1]

/-- The design passes the checker, and both parents are inside `prioSized`. -/
theorem orphan_checked :
    checkBool orphanDesc = true ∧ render orphanDesc = "pass" ∧ localOkB orphanImpl = true ∧
      prioSized orphanDesc "R" (prioLabels orphanImpl "R").length = true ∧
      prioSized orphanDesc "C" (prioLabels orphanImpl "C").length = true := by
  have hcheck : checkBool orphanDesc = true := by decide
  refine ⟨hcheck, ?_, by decide, by decide, by decide⟩
  simp [render, hcheck]

/-- `C`'s terminate seals `C` and `G` in that step. `G`'s slot is free.
Nothing has crashed. -/
theorem orphan_grandchild_sealed :
    (runAt orphanImpl 2 killed).map (fun w =>
      (lifeTag (w.st C0).life, lifeTag (w.st G0).life, slotOccupied w "G" 0, w.crashed)) =
      some (2, 2, false, false) := by
  decide

/-- The restarted `C` births a new `G`. The old `G` stays dead, parented by the
old `C`, and the new `G` is parented by the new `C`. -/
theorem orphan_respawn :
    (match runAt orphanImpl 2 restarted with
      | none => false
      | some w =>
        decide (lifeTag (w.st C0).life = 2) &&
          decide (lifeTag (w.st G0).life = 2) &&
          decide (lifeTag (w.st C1).life = 1) &&
          decide (lifeTag (w.st G1).life = 1) &&
          w.roster.contains G1 &&
          decide (route w orphanDesc C1 "G" = some G1) &&
          decide ((w.st G1).parent = some C1) &&
          decide ((w.st G0).parent = some C0) &&
          decide (w.crashed = false)) = true := by
  decide

end Deadlock.Orphan
