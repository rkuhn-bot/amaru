/-
`Eff.abort` seals the children and continues the parent.

The parent is a checked per-peer root. `Stop` runs `.abort` and then
`.internal`. The abort step leaves the parent in `.run` on that `.internal`,
with the child's tombstone already on the lane. `finish` returns the parent
to idle, and `recvPrio` takes the tombstone.
-/
import Deadlock.Semantics
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Deadlock.AbortCont
open Deadlock

def tpl (name : String) : Template where
  name := name
  multiplicity := .perPeer
  capacity := { a := 8, b := 2 }
  priorityCapacity := { a := 0, b := 4 }
  priorityBound := { a := 0, b := 4 }
  states := ["idle"]
  initial := "idle"
  terminable := true
  untimedPeer := false
  mustFit := true
  subtree := "S"

def tR : Template := { tpl "R" with states := ["idle", "up", "done"] }

def tC : Template := { tpl "C" with supervisor := some "R", tombstone := "died" }

def ing (t st label : String) : Edge where
  src := t
  srcState := st
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := { a := 1, b := 0 }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some { a := 0, b := 1 }
  cell := .none

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to,
    acceptsCall := false, release := 1 }

def step (t f l to : String) : CompatStep :=
  { template := t, fromState := f, toState := to, label := l }

def abortDesc : Description where
  name := "abort-cont"
  freshNames := true
  templates := [tR, tC]
  edges := [ing "R" "idle" "Go", ing "R" "up" "Stop", ing "R" "done" "Later"]
  compatibility := .all
  steps :=
    [step "R" "idle" "Go" "up", step "R" "up" "Go" "up", step "R" "done" "Go" "done",
     step "R" "idle" "Stop" "idle", step "R" "up" "Stop" "done", step "R" "done" "Stop" "done",
     step "R" "idle" "Later" "idle", step "R" "up" "Later" "up", step "R" "done" "Later" "done",
     step "R" "idle" "died" "idle", step "R" "up" "died" "up", step "R" "done" "died" "done"]

def abortImpl : Impl where
  desc := abortDesc
  transitions :=
    [tr "R" "idle" "Go" "up" [.spawn "C"],
     tr "R" "up" "Go" "up" [],
     tr "R" "done" "Go" "done" [],
     tr "R" "idle" "Stop" "idle" [],
     tr "R" "up" "Stop" "done" [.abort, .internal],
     tr "R" "done" "Stop" "done" [],
     tr "R" "idle" "Later" "idle" [],
     tr "R" "up" "Later" "up" [],
     tr "R" "done" "Later" "done" [],
     tr "R" "idle" "died" "idle" [],
     tr "R" "up" "died" "up" [],
     tr "R" "done" "died" "done" []]

def runAt (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply abortImpl a)) (some (initWorld abortImpl 1))

def rId : InstId := .peer "R" 0 0
def cId : InstId := .peer "C" 0 0

def born : List Action :=
  [.spawn "R", .ingress rId "Go", .recvBulk rId, .exec rId]

def aborted : List Action :=
  born ++ [.ingress rId "Stop", .recvBulk rId, .exec rId]

def continued (a : Actor) : Bool :=
  match a.phase with
  | .run k => k.rest == [.internal] && k.toState == "done"
  | _ => false

theorem abort_checked : checkBool abortDesc = true ∧ localOkB abortImpl = true := by
  decide

/-- The abort step seals the child, queues its tombstone, and leaves the parent
running the effect that follows `.abort`. -/
theorem abort_continues :
    (match runAt aborted with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          decide ((w.st rId).life = .alive) &&
          continued (w.st rId) &&
          decide ((w.st cId).life = .dead) &&
          decide ((w.st rId).prio.any (fun m => m.tombstone && m.sender == cId))) = true := by
  decide

def received : List Action :=
  aborted ++ [.exec rId, .finish rId, .recvPrio rId]

/-- The parent finishes the continuation and receives the tombstone. -/
theorem abort_receives :
    (match runAt received with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          decide ((w.st rId).life = .alive) &&
          decide ((w.st rId).phase = .idle) &&
          decide ((w.st rId).typestate = "done") &&
          decide ((w.st rId).prio == []) &&
          decide ((w.st cId).life = .dead)) = true := by
  decide

end Deadlock.AbortCont
