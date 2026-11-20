import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen6c
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

def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3

def crashedB (w : Option World) : Bool :=
  match w with
  | some w => w.roster.any fun id => (w.st id).life == .dead && (w.st id).phase == .crashed
  | none => false

def ing (t st : String) : Edge :=
  { (sendEdge t st t "Go" 1) with effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := true, occupancy := { a := 1, b := 0 }, ingressLegal := some (Affine.ofNat 1) }

def step (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }

/-! ## 1. Root connections under a core supervisor; `prioSized` holds, yet respawn
overflows the lane (F4 sizing). Also: unmatched tombstone in a later state, key split. -/

def tA : Template := { tpl "A" 2 ["idle", "done"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "s",
  timeoutKills := true, supervisor := "P", tombstone := "dead/A" }
def tB : Template := { tpl "B" 2 ["idle"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "s" }
def tP : Template := tpl "P" 2 ["idle", "seen"] "idle" true

def subDesc : Description where
  name := "subtree"
  freshNames := true
  templates := [tP, tA, tB]
  edges := [ing "A" "idle", ing "A" "done"]
  compatibility := .all
  steps := [step "A" "idle" "Go" "done", step "A" "done" "Go" "done", step "P" "idle" "dead/A" "seen"]

/-- `P` handles `dead/A` only in `idle`. `tombstoneHandled` asks for one such transition. -/
def subImpl : Impl where
  desc := subDesc
  transitions := [tr "A" "idle" "Go" "done" [.terminate], tr "A" "done" "Go" "done" [],
                  tr "P" "idle" "dead/A" "seen" []]

def Pc : InstId := .core "P"
def B0 : InstId := .peer "B" 0

def cycle (k : Nat) : List Action :=
  [.spawn "A", .ingress (.peer "A" k) "Go", .recvBulk (.peer "A" k), .exec (.peer "A" k), .exec (.peer "A" k)]

theorem sub_graph : checkBool subDesc = true := by decide
theorem sub_local : LocalOk subImpl := by
  show localOkB subImpl = true
  simp (config := { decide := true }) [localOkB, localTail, transitionOk, effectsOk, callOutcomesOk,
    bulkScopeOf, subImpl, subDesc, tr, ing, sendEdge, tpl, templateOf, tA, tB, tP, step]

/-- The static bound passes for `P` at `N = 1`: one simultaneous tombstone, capacity 4. -/
theorem sub_prioSized : prioSized subDesc "P" 1 (prioLabels subImpl "P").length = true ∧
    prioSizeFails subImpl 1 = [] := by decide

/-- F4 positive: four tombstones fit; the fifth on a lane of capacity 4 crashes the
world — in a reachable run of a `GraphOk ∧ LocalOk ∧ prioSized` design. -/
theorem respawn_overflow :
    ((runAt subImpl 1 ((List.range 4).flatMap cycle)).map fun w => ((w.st Pc).prio.length, capPrio subDesc 1 Pc)) =
      some (4, 4) ∧
    crashedB (runAt subImpl 1 ((List.range 4).flatMap cycle)) = false ∧
    crashedB (runAt subImpl 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4)) = true := by decide

/-- F4: the label is now per template, so `A#1`'s tombstone carries the same label.
But `P` handles it only in `idle`; in `seen` it is consumed with no transition. -/
def tombActs : List Action := cycle 0 ++ [.recvPrio Pc] ++ cycle 1 ++ [.recvPrio Pc]
theorem tombstone_later_state :
    ((runAt subImpl 1 (cycle 0 ++ [.recvPrio Pc] ++ cycle 1)).map fun w =>
      ((w.st Pc).typestate, (w.st Pc).prio.map (·.label))) = some ("seen", ["dead/A"]) ∧
    ((runAt subImpl 1 tombActs).map fun w => ((w.st Pc).typestate, (w.st Pc).prio.length)) =
      some ("seen", 0) ∧
    findTr subImpl "P" "seen" "dead/A" = none := by decide

/-- F5 still bites for roots: after A#0 dies, A respawns at a fresh key and
the live B#0 of the same subtree is out of reach. -/
def splitActs : List Action := [.spawn "A", .spawn "B"] ++ (cycle 0).tail ++ [.spawn "A"]
theorem respawn_key_split :
    ((runAt subImpl 1 splitActs).map fun w =>
      (lifeTag (w.st (.peer "A" 0)).life, lifeTag (w.st (.peer "A" 1)).life, lifeTag (w.st B0).life,
       route w subDesc (.peer "A" 1) "B", route w subDesc B0 "A")) =
    some (3, 1, 1, none, none) := by decide

/-- New: a crashed world is not absorbing. After the overflow crash, a root spawn
and an ingress still succeed. -/
theorem crash_not_absorbing :
    ((runAt subImpl 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4 ++ [.spawn "A", .ingress (.peer "A" 5) "Go"])).map
      fun w => (lifeTag (w.st (.peer "A" 5)).life, (w.st (.peer "A" 5)).box.length, lifeTag (w.st Pc).life)) =
    some (1, 1, 3) := by decide

/-! ## 2. F3 / F5 / F8: a per-peer connection supervises a handler, which
supervises a worker. -/

def tConn : Template := { tpl "Conn" 4 ["idle", "up", "done"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 4, b := 1 }, terminable := true, subtree := "net",
  timeoutKills := true, supervisor := "Mgr", tombstone := "dead/Conn" }
def tHand : Template := { tpl "Hand" 2 ["idle"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "net",
  supervisor := "Conn", tombstone := "dead/Hand" }
def tWork : Template := { tpl "Work" 2 ["idle"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "net",
  supervisor := "Hand", tombstone := "dead/Work" }
def tMgr : Template := tpl "Mgr" 2 ["idle"] "idle" true

def treeDesc : Description where
  name := "tree"
  freshNames := true
  templates := [tMgr, tConn, tHand, tWork]
  edges := [ing "Conn" "idle", ing "Conn" "up", ing "Conn" "done", ing "Hand" "idle"]
  compatibility := .all
  steps := []

def treeImpl : Impl where
  desc := treeDesc
  transitions := [tr "Conn" "idle" "Go" "up" [.spawn "Hand"],
                  tr "Conn" "up" "Go" "done" [.terminate],
                  tr "Conn" "done" "Go" "done" [.spawn "Hand"],
                  tr "Hand" "idle" "Go" "idle" [.spawn "Work"],
                  tr "Mgr" "idle" "dead/Conn" "idle" [],
                  tr "Conn" "idle" "dead/Hand" "idle" [], tr "Hand" "idle" "dead/Work" "idle" []]

def C0 : InstId := .peer "Conn" 0
def H0 : InstId := .peer "Hand" 0
def K0 : InstId := .peer "Work" 0

def treeActs : List Action :=
  [.spawn "Conn", .ingress C0 "Go", .recvBulk C0, .exec C0,      -- Conn spawns Hand#0
   .ingress H0 "Go", .recvBulk H0, .exec H0,                     -- Hand spawns Work#0
   .ingress C0 "Go", .recvBulk C0, .exec C0]                     -- Conn terminates

def treeSnap (w : Option World) : Option (List Nat × List String) :=
  w.map fun w => ([lifeTag (w.st C0).life, lifeTag (w.st H0).life, lifeTag (w.st K0).life],
    (w.st (.core "Mgr")).prio.map (·.label))

/-- F3/F5 positive: children are born at the parent's key, a per-peer parent
supervises them, and `terminate` marks the grandchild too. One tombstone, to `Mgr`. -/
theorem terminate_marks_grandchild :
    treeSnap (runAt treeImpl 1 (treeActs.take 7)) = some ([1, 1, 1], []) ∧
    treeSnap (runAt treeImpl 1 treeActs) = some ([2, 2, 2], ["dead/Conn"]) ∧
    isChild treeDesc C0 H0 = true ∧ isChild treeDesc H0 K0 = true := by decide

/-- After the seals, all three are dead. -/
theorem tree_sealed :
    treeSnap (runAt treeImpl 1 (treeActs ++ [.exec C0, .exec H0, .exec K0])) =
      some ([3, 3, 3], ["dead/Conn"]) := by decide

/-- New (high): `GraphOk` rejects every per-peer supervisor, so the tree above
is outside the theorems' hypotheses. Graph.lean `subtreeFails` is unchanged. -/
theorem tree_graph_rejected :
    (subtreeFails treeDesc).contains "fail: subtree net supervisor Conn is not a permanent core" = true ∧
    checkBool treeDesc = false := by decide

/-- New: a second `spawn` of a child whose id is alive or dead crashes the world. -/
theorem respawn_child_crashes :
    crashedB (runAt treeImpl 1 [.spawn "Conn", .ingress C0 "Go", .recvBulk C0, .exec C0,
      .ingress H0 "Go", .recvBulk H0, .exec H0, .ingress H0 "Go", .recvBulk H0, .exec H0]) = true := by decide

/-! ## 3. F2 positive and the supervisor-not-alive crash. -/

def tQ : Template := { tpl "Q" 2 ["idle", "gone"] "idle" true with terminable := true }
def tX : Template := { tpl "X" 2 ["idle", "sent"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "s",
  timeoutKills := true, supervisor := "Q", tombstone := "dead/X" }
def tY : Template := { tpl "Y" 2 ["idle", "done"] "idle" true with
  multiplicity := .perPeer, capacity := { a := 2, b := 1 }, terminable := true, subtree := "s",
  supervisor := "Q", tombstone := "dead/Y" }
def tH : Template := { tpl "H" 0 ["idle", "got"] "idle" false with
  multiplicity := .perPeer, terminable := true, subtree := "s" }

def deadDesc : Description where
  name := "dead-sender"
  freshNames := true
  templates := [tQ, tX, tY, tH]
  edges := [ing "X" "idle", ing "X" "sent", ing "Y" "idle", ing "Y" "done",
            { (sendEdge "X" "sent" "H" "M" 1) with occupancy := { a := 1, b := 0 } }]
  compatibility := .all
  steps := [step "X" "idle" "Go" "sent", step "Y" "idle" "Go" "done", step "Q" "idle" "dead/Y" "gone",
            step "Q" "idle" "dead/X" "gone", step "H" "idle" "M" "got", step "X" "sent" "Go" "sent",
            step "Y" "done" "Go" "done", step "H" "got" "M" "got"]

def deadImpl : Impl where
  desc := deadDesc
  transitions := [tr "X" "idle" "Go" "sent" [.send "H" "M" 0],
                  tr "Y" "idle" "Go" "done" [.terminate],
                  tr "Q" "idle" "dead/Y" "gone" [.terminate],
                  tr "Q" "idle" "dead/X" "gone" [],
                  tr "H" "idle" "M" "got" [],
                  tr "X" "sent" "Go" "sent" [], tr "Y" "done" "Go" "done" [],
                  tr "H" "got" "M" "got" []]

def X0 : InstId := .peer "X" 0
def Y0 : InstId := .peer "Y" 0
def Hh : InstId := .peer "H" 0
def Qc : InstId := .core "Q"

def deadActs : List Action :=
  [.spawn "X", .spawn "Y", .spawn "H",
   .ingress X0 "Go", .recvBulk X0, .exec X0,
   .ingress Y0 "Go", .recvBulk Y0, .exec Y0, .exec Y0,
   .recvPrio Qc, .exec Qc, .exec X0]

def deadSnap (w : Option World) : Option (Nat × Nat × String × Nat × Nat) :=
  w.map fun w => (lifeTag (w.st X0).life, lifeTag (w.st Hh).life, (w.st Hh).typestate,
    (w.st Hh).parked.length, (w.st X0).tokens "H")

theorem dead_graph : checkBool deadDesc = true := by decide
theorem dead_local : LocalOk deadImpl := by
  show localOkB deadImpl = true
  simp (config := { decide := true }) [localOkB, localTail, transitionOk, effectsOk, callOutcomesOk,
    bulkScopeOf, deadImpl, deadDesc, tr, ing, sendEdge, tpl, templateOf, tQ, tX, tY, tH, step,
    memberProgramOk, memberEffectOk, noBulkSend]

/-- F2 positive: when X seals, its parked entry on H is dropped and the slot
returns to X. H has nothing of X's left, so `recvBulk H` is disabled. -/
theorem dead_sender_refunded :
    deadSnap (runAt deadImpl 1 (deadActs.take 12)) = some (2, 1, "idle", 1, 0) ∧
    deadSnap (runAt deadImpl 1 deadActs) = some (3, 1, "idle", 0, 1) ∧
    (runAt deadImpl 1 (deadActs ++ [.recvBulk Hh])) = none := by decide

/-- New: once the lone-terminable supervisor `Q` is dead, a freshly spawned root
child of `Q` that terminates crashes the world (enqueueTombstone, parent not alive). -/
theorem dead_supervisor_crash :
    crashedB (runAt deadImpl 1 (deadActs ++ [.exec Qc, .spawn "Y", .ingress (.peer "Y" 1) "Go",
      .recvBulk (.peer "Y" 1), .exec (.peer "Y" 1)])) = true := by decide

end Deadlock.Helen6c

#print axioms Deadlock.Helen6c.sub_graph
#print axioms Deadlock.Helen6c.sub_local
#print axioms Deadlock.Helen6c.sub_prioSized
#print axioms Deadlock.Helen6c.respawn_overflow
#print axioms Deadlock.Helen6c.tombstone_later_state
#print axioms Deadlock.Helen6c.respawn_key_split
#print axioms Deadlock.Helen6c.crash_not_absorbing
#print axioms Deadlock.Helen6c.terminate_marks_grandchild
#print axioms Deadlock.Helen6c.tree_sealed
#print axioms Deadlock.Helen6c.tree_graph_rejected
#print axioms Deadlock.Helen6c.respawn_child_crashes
#print axioms Deadlock.Helen6c.dead_graph
#print axioms Deadlock.Helen6c.dead_local
#print axioms Deadlock.Helen6c.dead_sender_refunded
#print axioms Deadlock.Helen6c.dead_supervisor_crash
