/-
An abort seals the aborting actor's live children. It does not clear a
sibling's continuation.

`R` runs `.abort` then `.internal`. `N` is a core, not a child of `R`, and is
already running `[.internal, .internal]` when that abort happens. The step
leaves `N` on that same rest.
-/
import Deadlock.Semantics
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Deadlock.AbortRest
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

def tN : Template where
  name := "N"
  multiplicity := .one
  capacity := { a := 0, b := 4 }
  priorityCapacity := { a := 0, b := 4 }
  priorityBound := { a := 0, b := 4 }
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

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

def ingN : Edge :=
  { ing "N" "idle" "Go" with occupancy := { a := 0, b := 1 }, ingressLegal := some { a := 0, b := 1 } }

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to,
    acceptsCall := false, release := 1 }

def step (t f l to : String) : CompatStep :=
  { template := t, fromState := f, toState := to, label := l }

def restDesc : Description where
  name := "abort-rest"
  freshNames := true
  templates := [tR, tC, tN]
  edges := [ing "R" "idle" "Go", ing "R" "up" "Stop", ing "R" "done" "Later", ingN]
  compatibility := .all
  steps :=
    [step "R" "idle" "Go" "up", step "R" "up" "Go" "up", step "R" "done" "Go" "done",
     step "R" "idle" "Stop" "idle", step "R" "up" "Stop" "done", step "R" "done" "Stop" "done",
     step "R" "idle" "Later" "idle", step "R" "up" "Later" "up", step "R" "done" "Later" "done",
     step "R" "idle" "died" "idle", step "R" "up" "died" "up", step "R" "done" "died" "done",
     step "N" "idle" "Go" "idle"]

def restImpl : Impl where
  desc := restDesc
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
     tr "R" "done" "died" "done" [],
     tr "N" "idle" "Go" "idle" [.internal, .internal]]

def runAt (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply restImpl a)) (some (initWorld restImpl 1))

def rId : InstId := .peer "R" 0 0
def cId : InstId := .peer "C" 0 0
def nId : InstId := .core "N"

def aborted : List Action :=
  [.spawn "R", .ingress rId "Go", .recvBulk rId, .exec rId,
   .ingress nId "Go", .recvBulk nId,
   .ingress rId "Stop", .recvBulk rId, .exec rId]

def parentContinued (a : Actor) : Bool :=
  match a.phase with
  | .run k => k.rest == [.internal] && k.toState == "done"
  | _ => false

/-- `N` is still on the program `Go` installed, both effects unconsumed. -/
def siblingRest (a : Actor) : Bool :=
  match a.phase with
  | .run k => k.rest == [.internal, .internal]
  | _ => false

theorem rest_checked : checkBool restDesc = true ∧ localOkB restImpl = true := by
  decide

/-- Reachable from `initWorld`. The abort step seals `C` and continues `R`.
`N` is not a child of `R`, and its rest is still `[.internal, .internal]`. -/
theorem abort_leaves_sibling_rest :
    (match runAt aborted with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          parentContinued (w.st rId) &&
          decide ((w.st cId).life = .dead) &&
          decide ((w.st nId).life = .alive) &&
          siblingRest (w.st nId)) = true := by
  decide

end Deadlock.AbortRest
