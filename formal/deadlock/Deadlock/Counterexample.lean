/-
`no_tombstone_overflow` is false.

`prioSized` counts one tombstone per child slot of one parent instance.
`restartOk` rejects a re-spawn that can run while that slot's tombstone is
still queued. Neither check sees two live generations of the same
supervisor.

The trace below builds both. Six scheduler births of the empty-named root
leave key 5 alive. That root spawns `R` generation 0 at key 5. Six more
births of `R` fill keys 0–4 and then key 5 again: `openSubtreeKey` only
looks below `nextKey`, so the sixth birth is generation 1, and both
generations stay alive. `findLive` returns generation 0.

Generation 0 spawns `C`, and `C`'s seal queues `dead/C#0` on generation 0.
The lane's capacity is 1 and its length is then 1. Generation 1 is still
in `boot`, which `restartOk` treats as a first spawn, and its own lane is
empty, so it spawns `C` again. The second seal offers another tombstone to
generation 0. `offerPrio` crashes.

The same trace does not crash when `R`'s priority capacity is 2, so the
crash is the full lane and not a dead parent, an empty label, or an
unclassified `terminate`.
-/

import Deadlock.Graph
import Deadlock.Local
import Deadlock.Semantics

set_option autoImplicit false
set_option maxRecDepth 100000

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

def zT : Template := { tpl "" 8 ["idle"] "idle" with capacity := big }

def rT : Template :=
  { tpl "R" 8 ["boot", "up"] "boot" with
      subtree := "S", capacity := big, priorityCapacity := Affine.ofNat 1 }

def cT : Template :=
  { tpl "C" 8 ["idle"] "idle" with
      terminable := true, subtree := "S", supervisor := "R", tombstone := "dead/C", capacity := big }

def cxDesc : Description where
  name := "two-live"
  freshNames := true
  templates := [zT, rT, cT]
  edges := [ing "" "idle" "Go", ing "R" "boot" "Go", ing "R" "up" "Go", ing "R" "boot" "dead/C",
            ing "R" "up" "dead/C", ing "C" "idle" "Die"]
  compatibility := .all
  steps := [step "" "idle" "Go" "idle", step "R" "boot" "Go" "up", step "R" "up" "Go" "up",
            step "R" "boot" "dead/C" "boot", step "R" "up" "dead/C" "up", step "C" "idle" "Die" "idle"]

def cxImpl : Impl where
  desc := cxDesc
  transitions :=
    [tr "" "idle" "Go" "idle" [.spawn "R"],
     tr "R" "boot" "Go" "up" [.spawn "C"],
     tr "R" "up" "Go" "up" [],
     tr "R" "boot" "dead/C" "boot" [],
     tr "R" "up" "dead/C" "up" [],
     tr "C" "idle" "Die" "idle" [.terminate]]

/-- Population 8. Six empty-named roots, then the births described above, all fit. -/
def runAt (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply cxImpl a)) (some (initWorld cxImpl 8))

def r5 : InstId := .peer "R" 5 0
def r5' : InstId := .peer "R" 5 1
def c0 : InstId := .peer "C" 5 0
def c1 : InstId := .peer "C" 5 1

def prelude : List Action :=
  (List.range 6).map (fun _ => .spawn "") ++
  [.ingress (.peer "" 5 0) "Go", .recvBulk (.peer "" 5 0), .exec (.peer "" 5 0)] ++
  (List.range 6).map (fun _ => .spawn "R")

def killC (id : InstId) : List Action :=
  [.ingress id "Die", .recvBulk id, .exec id, .exec id]

def spawnC (parent _child : InstId) : List Action :=
  [.ingress parent "Go", .recvBulk parent, .exec parent]

/-- Through the mark of the second child. The seal is the next `exec`. -/
def beforeSeal : List Action :=
  prelude ++ spawnC r5 c0 ++ killC c0 ++ spawnC r5' c1 ++ (killC c1).take 3

def twoLive : List Action :=
  beforeSeal ++ [.exec c1]

theorem cx_graph : GraphOk cxDesc :=
  checkBool_sound cxDesc (by decide)

theorem cx_local : LocalOk cxImpl := by decide

theorem cx_sized : prioSized cxDesc "R" (prioSenderBound cxImpl "R") = true := by decide

theorem cx_cap : capPrio cxDesc 8 r5 = 1 := by decide

/-- Both generations are alive. The older lane already holds this slot's tombstone. -/
theorem cx_ready :
    (match runAt beforeSeal with
      | none => false
      | some w =>
        decide ((w.st c1).life = .shuttingDown) && (w.st c1).pendingTombstone &&
          decide ((w.st r5).life = .alive) && decide ((w.st r5').life = .alive) &&
          decide (w.crashed = false) &&
          decide ((w.st r5).prio.map (·.label) = ["dead/C#0"]) &&
          decide ((w.st r5').prio.map (·.label) = [])) = true := by decide

/-- The seal of the second child crashes `offerPrio` on the older generation. -/
theorem cx_crashes :
    (match runAt twoLive with
      | none => false
      | some w => w.crashed)     = true := by decide

end Deadlock
