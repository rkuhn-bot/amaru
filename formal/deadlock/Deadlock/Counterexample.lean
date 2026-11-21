/-
The reused-key schedule crashed, and the fresh-key schedule does not.

Before a birth took a fresh key, this design was run at population 8.
An empty-named root at key 5 spawned `R` generation 0. Six later births of
`R` filled keys 0–4 and then took key 5 again, because the fallback in
`spawn` used `nextKey` with no liveness check. Generation 1 was born while
generation 0 was alive. Each generation spawned `C`. Both seals offered
`dead/C` to generation 0, whose lane held one message, and `offerPrio`
crashed. That action list is not a witness for the semantics below: the
empty-named root's `spawn "R"` is out of scope (`none` matches no template)
and the roster crashes there. The schedule that matches pure-stage is the
one in `faithful`: two scheduler births, two keys, one tombstone on each
live lane.

`foreign_tombstone` and `late_seal_drops` are the two probes from the
review of that crash. A new root is a fresh key. A parent that terminates
seals its child in that step and discards the child's tombstone.
-/

import Deadlock.Graph
import Deadlock.Local
import Deadlock.Semantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Deadlock

def tpl (name : String) (cap : Nat) (states : List String) (initial : String) : Template where
  name := name
  multiplicity := .perPeer
  capacity := .ofNat cap
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 1
  states := states
  initial := initial
  terminable := false
  untimedPeer := false
  mustFit := true

def ing (t st lab : String) : Edge :=
  { src := t, srcState := st, dst := t, kind := .nonBlocking, reliability := .reliable,
    effect := .trySend, label := lab, scope := .intra, occupancy := { a := 1, b := 0 },
    repliesInDequeue := false, ingress := true, ingressLegal := some (Affine.ofNat 1), cell := .none }

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := false, release := 1 }

def step (t f l to : String) : CompatStep :=
  { template := t, fromState := f, toState := to, label := l }

def big : Affine := { a := 4, b := 4 }

def rT : Template :=
  { tpl "R" 8 ["boot", "up"] "boot" with
      subtree := "S", capacity := big, priorityCapacity := Affine.ofNat 1 }

def cT : Template :=
  { tpl "C" 8 ["idle"] "idle" with
      terminable := true, subtree := "S", supervisor := some "R", tombstone := "dead/C",
      capacity := big }

def cxDesc : Description where
  name := "fresh-root"
  freshNames := true
  templates := [rT, cT]
  edges := [ing "R" "boot" "Go", ing "R" "up" "Go", ing "R" "boot" "dead/C",
            ing "R" "up" "dead/C", ing "C" "idle" "Die"]
  compatibility := .all
  steps := [step "R" "boot" "Go" "up", step "R" "up" "Go" "up",
            step "R" "boot" "dead/C" "boot", step "R" "up" "dead/C" "up",
            step "C" "idle" "Die" "idle"]

def cxImpl : Impl where
  desc := cxDesc
  transitions :=
    [tr "R" "boot" "Go" "up" [.spawn "C"],
     tr "R" "up" "Go" "up" [],
     tr "R" "boot" "dead/C" "boot" [],
     tr "R" "up" "dead/C" "up" [],
     tr "C" "idle" "Die" "idle" [.terminate]]

def runAt (I : Impl) (n : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply I a)) (some (initWorld I n))

def r0 : InstId := .peer "R" 0 0
def r1 : InstId := .peer "R" 1 0
def c0 : InstId := .peer "C" 0 0
def c1 : InstId := .peer "C" 1 0

def spawnC (parent : InstId) : List Action :=
  [.ingress parent "Go", .recvBulk parent, .exec parent]

/-- The `exec` of `Die` seals the child and queues its tombstone. There is no later seal. -/
def killC (id : InstId) : List Action :=
  [.ingress id "Die", .recvBulk id, .exec id]

/-- Two scheduler births. Each root births one child and seals it. -/
def faithful : List Action :=
  [.spawn "R"] ++ spawnC r0 ++ killC c0 ++ [.spawn "R"] ++ spawnC r1 ++ killC c1

theorem cx_graph : GraphOk cxDesc :=
  checkBool_sound cxDesc (by decide)

theorem cx_local : LocalOk cxImpl := by decide

theorem cx_sized : prioSized cxDesc "R" (prioSenderBound cxImpl "R") = true := by decide

/-- Each root is a fresh key. Each lane holds the one tombstone its own child
sealed, and the roster has not crashed. -/
theorem faithful_lanes :
    (match runAt cxImpl 2 faithful with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          decide ((w.st r0).life = .alive) && decide ((w.st r1).life = .alive) &&
          decide ((w.st r0).prio.map (·.label) = ["dead/C#0"]) &&
          decide ((w.st r1).prio.map (·.label) = ["dead/C#0"])) = true := by decide

/-! A child seals, then its parent terminates and is sealed in that same step.
The child's tombstone was queued on the parent and is cleared with the parent's lane. -/

def rT2 : Template :=
  { tpl "R" 8 ["boot", "up"] "boot" with
      subtree := "S", capacity := { a := 8, b := 4 }, priorityCapacity := Affine.ofNat 1,
      terminable := true }

def kDesc : Description where
  name := "late-seal"
  freshNames := true
  templates := [rT2, cT]
  edges := [ing "R" "boot" "Go", ing "R" "up" "Go", ing "R" "up" "Kill", ing "R" "boot" "Kill",
            ing "R" "boot" "dead/C", ing "R" "up" "dead/C", ing "C" "idle" "Die"]
  compatibility := .all
  steps := [step "R" "boot" "Go" "up", step "R" "up" "Go" "up", step "R" "up" "Kill" "up",
            step "R" "boot" "Kill" "boot", step "R" "boot" "dead/C" "boot",
            step "R" "up" "dead/C" "up", step "C" "idle" "Die" "idle"]

def kImpl : Impl where
  desc := kDesc
  transitions :=
    [tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "up" "Go" "up" [],
     tr "R" "up" "Kill" "up" [.terminate], tr "R" "boot" "Kill" "boot" [],
     tr "R" "boot" "dead/C" "boot" [], tr "R" "up" "dead/C" "up" [],
     tr "C" "idle" "Die" "idle" [.terminate]]

/-- `C` seals itself, then `R` terminates and is sealed in that step. -/
def lateBase : List Action :=
  [.spawn "R", .ingress r0 "Go", .recvBulk r0, .exec r0,
   .ingress c0 "Die", .recvBulk c0, .exec c0,
   .ingress r0 "Kill", .recvBulk r0, .exec r0]

theorem k_checks : checkBool kDesc = true ∧ localOkB kImpl = true ∧
    prioSized kDesc "R" (prioSenderBound kImpl "R") = true := by decide

/-- `R`'s terminate seals `R` in that step. `C` is already dead. `R`'s lane,
including `C`'s tombstone, is cleared by that seal, and the roster does not crash. -/
theorem late_seal_drops :
    (match runAt kImpl 2 lateBase with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          decide ((w.st r0).life = .dead) &&
          decide ((w.st c0).life = .dead) &&
          decide ((w.st r0).prio = [])) = true := by decide

/-- The dead root holds no mail and has no supervisor, so another root is born
at the next key. `C`'s tombstone was cleared with `R` and is not delivered there. -/
theorem foreign_tombstone :
    (match runAt kImpl 2 (lateBase ++ [.spawn "R"]) with
      | none => false
      | some w =>
        decide (w.crashed = false) &&
          decide ((w.st r0).life = .dead) &&
          decide ((w.st r1).life = .alive) &&
          decide ((w.st r1).prio = []) &&
          decide ((w.st c0).life = .dead)) = true := by decide

end Deadlock
