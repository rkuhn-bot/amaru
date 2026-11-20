import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7c
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
def B0 : InstId := .peer "B" 0 0
def A0 : InstId := .peer "A" 0 0
def A1 : InstId := .peer "A" 0 1

/-- Respawn stays at key 0. `g` is the generation. -/
def cycle (g : Nat) : List Action :=
  [.spawn "A", .ingress (.peer "A" 0 g) "Go", .recvBulk (.peer "A" 0 g),
    .exec (.peer "A" 0 g), .exec (.peer "A" 0 g)]

theorem sub_graph : checkBool subDesc = true := by decide

/-- `P` does not handle `dead/A` in `seen`, so `LocalOk` rejects the design. -/
theorem sub_local : localOkB subImpl = false := by decide

/-- The static bound, with no tombstone left queued, passes for `P` at `N = 1`. -/
theorem sub_prioSized : prioSized subDesc "P" 1 (prioLabels subImpl "P").length = true ∧
    prioSizeFails subImpl 1 = [] := by decide

/-- Four tombstones fit. A fifth root spawn is admitted. The new child's
`terminate` then crashes on the full lane. -/
theorem respawn_overflow :
    ((runAt subImpl 1 ((List.range 4).flatMap cycle)).map fun w =>
      ((w.st Pc).prio.length, capPrio subDesc 1 Pc)) = some (4, 4) ∧
    crashedB (runAt subImpl 1 ((List.range 4).flatMap cycle)) = false ∧
    (runAt subImpl 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])).isSome = true ∧
    crashedB (runAt subImpl 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])) = false ∧
    ((runAt subImpl 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4)).map (·.crashed)) = some true ∧
    prioSized subDesc "P" 1 (prioLabels subImpl "P").length 4 = false := by decide

/-- A tombstone that arrives in `seen` stays queued. `LocalOk` requires the label
in every declared state of the parent. -/
def tombActs : List Action := cycle 0 ++ [.recvPrio Pc] ++ cycle 1 ++ [.recvPrio Pc]
theorem tombstone_later_state :
    ((runAt subImpl 1 (cycle 0 ++ [.recvPrio Pc] ++ cycle 1)).map fun w =>
      ((w.st Pc).typestate, (w.st Pc).prio.map (·.label))) = some ("seen", ["dead/A#1"]) ∧
    runAt subImpl 1 tombActs = none ∧
    findTr subImpl "P" "seen" "dead/A" = none := by decide

/-- After A generation 0 dies, the replacement is generation 1 at the same key,
and it still routes to the live B. -/
def splitActs : List Action := [.spawn "A", .spawn "B"] ++ (cycle 0).tail ++ [.spawn "A"]
theorem respawn_key_split :
    ((runAt subImpl 1 splitActs).map fun w =>
      (lifeTag (w.st A0).life, lifeTag (w.st A1).life, lifeTag (w.st B0).life,
       route w subDesc A1 "B", route w subDesc B0 "A")) =
    some (3, 1, 1, some B0, some A1) := by decide

/-- A permanent core's `terminate` crashes the roster, and nothing runs after that. -/
def ingP : Edge := { ing "P" "idle" with occupancy := { a := 0, b := 1 } }

def crashDesc : Description :=
  { subDesc with edges := subDesc.edges ++ [ingP], steps := subDesc.steps ++ [step "P" "idle" "Go" "idle"] }

def crashImpl : Impl where
  desc := crashDesc
  transitions := [tr "P" "idle" "Go" "idle" [.terminate]]

def crashActs : List Action := [.ingress Pc "Go", .recvBulk Pc, .exec Pc]

theorem crash_absorbing :
    crashedB (runAt crashImpl 1 crashActs) = true ∧
      ((runAt crashImpl 1 crashActs).map (·.crashed)) = some true ∧
      runAt crashImpl 1 (crashActs ++ [.spawn "A"]) = none ∧
      runAt crashImpl 1 (crashActs ++ [.stutter]) = none ∧
      runAt crashImpl 1 (crashActs ++ [.ingress Pc "Go"]) = none := by decide

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
  edges := [ing "Conn" "idle", ing "Conn" "up", ing "Conn" "done", ing "Hand" "idle", ing "Work" "idle"]
  compatibility := .all
  steps := []

def treeImpl : Impl where
  desc := treeDesc
  transitions := [tr "Conn" "idle" "Go" "up" [.spawn "Hand"],
                  tr "Conn" "up" "Go" "done" [.terminate],
                  tr "Conn" "done" "Go" "done" [.spawn "Hand"],
                  tr "Hand" "idle" "Go" "idle" [.spawn "Work"],
                  tr "Work" "idle" "Go" "idle" [.terminate],
                  tr "Mgr" "idle" "dead/Conn" "idle" [],
                  tr "Conn" "idle" "dead/Hand" "idle" [], tr "Hand" "idle" "dead/Work" "idle" []]

def C0 : InstId := .peer "Conn" 0 0
def H0 : InstId := .peer "Hand" 0 0
def K0 : InstId := .peer "Work" 0 0
def K1 : InstId := .peer "Work" 0 1

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
    treeSnap (runAt treeImpl 1 treeActs) = some ([2, 2, 2], ["dead/Conn#0"]) ∧
    isChild treeDesc C0 H0 = true ∧ isChild treeDesc H0 K0 = true := by decide

/-- After the seals, all three are dead. -/
theorem tree_sealed :
    treeSnap (runAt treeImpl 1 (treeActs ++ [.exec C0, .exec H0, .exec K0])) =
      some ([3, 3, 3], ["dead/Conn#0"]) := by decide

/-- A per-peer supervisor of its own subtree passes `GraphOk`. -/
theorem tree_graph_ok : subtreeFails treeDesc = [] ∧ checkBool treeDesc = true := by decide

/-- A second spawn while the child is alive does not crash, and does not birth a second copy. -/
theorem respawn_child_live :
    let acts : List Action := [.spawn "Conn", .ingress C0 "Go", .recvBulk C0, .exec C0,
      .ingress H0 "Go", .recvBulk H0, .exec H0, .ingress H0 "Go", .recvBulk H0, .exec H0]
    crashedB (runAt treeImpl 1 acts) = false ∧
      ((runAt treeImpl 1 acts).map fun w => lifeTag (w.st K0).life) = some 1 := by decide

/-- A dead child is restarted at a fresh generation of the same key. -/
theorem respawn_child_fresh :
    let acts : List Action := [.spawn "Conn", .ingress C0 "Go", .recvBulk C0, .exec C0,
      .ingress H0 "Go", .recvBulk H0, .exec H0,
      .ingress K0 "Go", .recvBulk K0, .exec K0, .exec K0,
      .ingress H0 "Go", .recvBulk H0, .exec H0]
    crashedB (runAt treeImpl 1 acts) = false ∧
      ((runAt treeImpl 1 acts).map fun w =>
        (lifeTag (w.st K0).life, lifeTag (w.st K1).life)) = some (3, 1) := by decide

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
            step "Q" "idle" "dead/X" "gone", step "Q" "gone" "dead/Y" "gone", step "Q" "gone" "dead/X" "gone",
            step "H" "idle" "M" "got", step "X" "sent" "Go" "sent",
            step "Y" "done" "Go" "done", step "H" "got" "M" "got"]

def deadImpl : Impl where
  desc := deadDesc
  transitions := [tr "X" "idle" "Go" "sent" [.send "H" "M" 0],
                  tr "Y" "idle" "Go" "done" [.terminate],
                  tr "Q" "idle" "dead/Y" "gone" [.terminate],
                  tr "Q" "idle" "dead/X" "gone" [],
                  tr "Q" "gone" "dead/Y" "gone" [],
                  tr "Q" "gone" "dead/X" "gone" [],
                  tr "H" "idle" "M" "got" [],
                  tr "X" "sent" "Go" "sent" [], tr "Y" "done" "Go" "done" [],
                  tr "H" "got" "M" "got" []]

def X0 : InstId := .peer "X" 0 0
def Y0 : InstId := .peer "Y" 0 0
def Hh : InstId := .peer "H" 0 0
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
  unfold LocalOk
  decide

/-- The parked entry leaves when X is marked, not only when X seals. H has
nothing of X's left, so `recvBulk H` is disabled. -/
theorem dead_sender_refunded :
    deadSnap (runAt deadImpl 1 (deadActs.take 12)) = some (2, 1, "idle", 0, 1) ∧
    deadSnap (runAt deadImpl 1 deadActs) = some (3, 1, "idle", 0, 1) ∧
    (runAt deadImpl 1 (deadActs ++ [.recvBulk Hh])) = none := by decide

/-- A dead supervisor admits no new child. The prefix is a live world, and the
spawn itself is disabled. -/
theorem dead_supervisor_refused :
    (runAt deadImpl 1 (deadActs ++ [.exec Qc])).isSome = true ∧
    crashedB (runAt deadImpl 1 (deadActs ++ [.exec Qc])) = false ∧
    runAt deadImpl 1 (deadActs ++ [.exec Qc, .spawn "Y"]) = none := by decide


/-! ## R7: original R6c statements, API-adapted (`.peer n k` → `.peer n key gen`), refuted -/

/-- The fifth root spawn is admitted, and the `terminate` inside that cycle
crashes on the full lane. -/
theorem root_respawn_crashes :
    (runAt subImpl 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])).isSome = true ∧
    crashedB (runAt subImpl 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])) = false ∧
    ((runAt subImpl 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4)).map (·.crashed)) =
      some true := by decide

/-- Original statement: the second tombstone is consumed in `seen`. Now `recvPrio` is
disabled there (the prefix up to it runs). -/
theorem orig_tombstone_later_refuted :
    ((runAt subImpl 1 tombActs).map fun w => ((w.st Pc).typestate, (w.st Pc).prio.length)) ≠
      some ("seen", 0) ∧
    (runAt subImpl 1 (cycle 0 ++ [.recvPrio Pc] ++ cycle 1)).isSome = true := by decide

theorem orig_key_split_refuted :
    ((runAt subImpl 1 splitActs).map fun w =>
      (lifeTag (w.st A0).life, lifeTag (w.st A1).life, lifeTag (w.st B0).life,
       route w subDesc A1 "B", route w subDesc B0 "A")) ≠ some (3, 1, 1, none, none) := by decide

theorem orig_crash_not_absorbing_refuted :
    (runAt subImpl 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4 ++
      [.spawn "A", .ingress (.peer "A" 0 5) "Go"])).isSome = false := by decide

theorem orig_tree_graph_rejected_refuted : checkBool treeDesc ≠ false := by decide

theorem orig_respawn_child_crashes_refuted :
    crashedB (runAt treeImpl 1 [.spawn "Conn", .ingress C0 "Go", .recvBulk C0, .exec C0,
      .ingress H0 "Go", .recvBulk H0, .exec H0, .ingress H0 "Go", .recvBulk H0, .exec H0]) ≠ true := by decide

/-- Original: the spawn under a dead `Q` and Y#1's terminate crash. Now the spawn itself
is disabled (the prefix before it is a real world). -/
theorem orig_dead_supervisor_crash_refuted :
    crashedB (runAt deadImpl 1 (deadActs ++ [.exec Qc, .spawn "Y", .ingress (.peer "Y" 0 1) "Go",
      .recvBulk (.peer "Y" 0 1), .exec (.peer "Y" 0 1)])) ≠ true ∧
    (runAt deadImpl 1 (deadActs ++ [.exec Qc])).isSome = true := by decide

/-! ## R7: `respawn_overflow` on a design that passes `LocalOk` (P handles `dead/A` in `seen`). -/

def subImpl2 : Impl := { subImpl with
  desc := { subDesc with steps := subDesc.steps ++ [step "P" "seen" "dead/A" "seen"] },
  transitions := subImpl.transitions ++ [tr "P" "seen" "dead/A" "seen" []] }

theorem sub2_ok : checkBool subImpl2.desc = true ∧ LocalOk subImpl2 ∧ prioSizeFails subImpl2 1 = [] := by
  refine ⟨by decide, by unfold LocalOk; decide, by decide⟩

/-- Four tombstones queued, the fifth root spawn is admitted, and its `terminate`
crashes. `LocalOk` does not refuse the spawn. -/
theorem sub2_root_crashes :
    ((runAt subImpl2 1 ((List.range 4).flatMap cycle)).map fun w => ((w.st Pc).prio.length, w.crashed)) =
      some (4, false) ∧
    (runAt subImpl2 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])).isSome = true ∧
    crashedB (runAt subImpl2 1 ((List.range 4).flatMap cycle ++ [.spawn "A"])) = false ∧
    ((runAt subImpl2 1 ((List.range 4).flatMap cycle ++ (cycle 4).take 4)).map (·.crashed)) = some true := by decide

/-! ## R7 NEW: a per-peer parent restarting its child overflows its lane and crashes,
in a `GraphOk ∧ LocalOk ∧ prioSized` design. `tombstoneRoom` guards only root spawns. -/

def rTrs : List Transition := [tr "Conn" "idle" "Go" "idle" [.spawn "Hand"],
                  tr "Conn" "up" "Go" "up" [], tr "Conn" "done" "Go" "done" [],
                  tr "Hand" "idle" "Go" "idle" [.terminate],
                  tr "Work" "idle" "Go" "idle" [],
                  tr "Mgr" "idle" "dead/Conn" "idle" [],
                  tr "Conn" "idle" "dead/Hand" "idle" [], tr "Conn" "up" "dead/Hand" "up" [],
                  tr "Conn" "done" "dead/Hand" "done" [],
                  tr "Hand" "idle" "dead/Work" "idle" []]

def rTree : Impl where
  desc := { treeDesc with steps := rTrs.map fun t => step t.template t.fromState t.label t.toState }
  transitions := rTrs

/-- Conn spawns Hand generation `g`; Hand terminates and seals; the tombstone stays queued. -/
def hcycle (g : Nat) : List Action :=
  [.ingress C0 "Go", .recvBulk C0, .exec C0,
   .ingress (.peer "Hand" 0 g) "Go", .recvBulk (.peer "Hand" 0 g), .exec (.peer "Hand" 0 g),
   .exec (.peer "Hand" 0 g)]

theorem rtree_ok : checkBool rTree.desc = true ∧ LocalOk rTree ∧ prioSizeFails rTree 1 = [] := by
  refine ⟨by decide, by unfold LocalOk; decide, by decide⟩

theorem child_restart_overflow :
    ((runAt rTree 1 (.spawn "Conn" :: (List.range 4).flatMap hcycle)).map fun w =>
      ((w.st C0).prio.length, capPrio rTree.desc 1 C0, w.crashed)) = some (4, 4, false) ∧
    ((runAt rTree 1 (.spawn "Conn" :: (List.range 4).flatMap hcycle ++ (hcycle 4).take 6)).map
      (·.crashed)) = some true := by decide

/-- Generation 0's tombstone stays queued while generation 1 is alive. The label
carries that generation, so the two are not the same message. -/
theorem stale_tombstone :
    ((runAt rTree 1 (.spawn "Conn" :: hcycle 0 ++ (hcycle 1).take 3)).map fun w =>
      ((w.st C0).prio.map (·.label), (w.st C0).prio.map (·.sender),
        lifeTag (w.st (.peer "Hand" 0 1)).life)) =
      some (["dead/Hand#0"], [.peer "Hand" 0 0], 1) := by decide

/-! ## R7: N1 counts, nested branches and stored continuations -/

theorem nested_counted :
    sendsTo "A" [.peer [.trySend "X" "l" 0 [] [.call "Y" "q" 0 [.send "A" "M" 0, .send "A" "M" 0] []]]] = 2 ∧
    sendsTo "A" [.call "Y" "q" 0 [.send "A" "M" 0] [.trySend "A" "M" 0 [.send "A" "M" 0] []], .send "A" "M" 0] = 1 ∧
    selfLabels [.peer [.call "Y" "q" 0 [] [.trySend "X" "l" 0 [.selfSchedule "z"] []]]] = ["z"] ∧
    hasTerminate [.trySend "X" "l" 0 [] [.peer [.terminate]]] = true ∧
    noSelfSchedule [.call "Y" "q" 0 [.peer [.selfSchedule "z"]] []] = false := by decide


/-! ## A core's pool: `slots` children, indexed by slot and generation. -/

def tM : Template := tpl "M" 4 ["idle"] "idle" false
def tW : Template := { tpl "W" 4 ["idle"] "idle" false with
  multiplicity := .perPeer, slots := 2, supervisor := "M", subtree := "pw",
  terminable := true, tombstone := "dead/W" }

def ingM : Edge := { ing "M" "idle" with occupancy := { a := 0, b := 1 } }

def poolDesc : Description where
  name := "pool"
  freshNames := true
  templates := [tM, tW]
  edges := [ingM, ing "W" "idle"]
  compatibility := .all
  steps := [step "M" "idle" "Go" "idle", step "W" "idle" "Go" "idle",
            step "M" "idle" "dead/W" "idle"]

def poolImpl : Impl where
  desc := poolDesc
  transitions := [tr "M" "idle" "Go" "idle" [.spawn "W"],
                  tr "W" "idle" "Go" "idle" [.terminate],
                  tr "M" "idle" "dead/W" "idle" []]

def Mc : InstId := .core "M"

def birth : List Action := [.ingress Mc "Go", .recvBulk Mc, .exec Mc]

def killSlot (k g : Nat) : List Action :=
  [.ingress (.peer "W" k g) "Go", .recvBulk (.peer "W" k g),
   .exec (.peer "W" k g), .exec (.peer "W" k g)]

def poolLives (w : World) : List Nat :=
  [lifeTag (w.st (.peer "W" 0 0)).life, lifeTag (w.st (.peer "W" 1 0)).life,
   lifeTag (w.st (.peer "W" 0 1)).life]

theorem pool_sized :
    subtreeFails poolDesc = [] ∧
    population poolDesc "W" 1 poolDesc.templates.length = 2 ∧
    simultaneousTombstones poolDesc "M" 1 = 2 ∧
    LocalOk poolImpl := by
  refine ⟨by decide, by decide, by decide, by unfold LocalOk; decide⟩

/-- Two spawns fill the two slots. A third is a no-op. Killing slot 0 and
spawning again births generation 1 in that slot. -/
theorem pool_slots :
    ((runAt poolImpl 1 (birth ++ birth)).map poolLives) = some [1, 1, 0] ∧
    ((runAt poolImpl 1 (birth ++ birth ++ birth)).map poolLives) = some [1, 1, 0] ∧
    ((runAt poolImpl 1 (birth ++ birth ++ killSlot 0 0 ++ birth)).map poolLives) =
      some [3, 1, 1] := by decide

/-! ## Mail queued by an old generation is charged to the key. -/

def tBox : Template := tpl "H" 4 ["idle"] "idle" false
def tS : Template := { tpl "S" 4 ["idle"] "idle" false with
  multiplicity := .perPeer, subtree := "mail", terminable := true }

def mailEdge : Edge :=
  { (sendEdge "S" "idle" "H" "M" 0) with occupancy := { a := 1, b := 0 } }

def mailDesc : Description where
  name := "old-mail"
  freshNames := true
  templates := [tBox, tS]
  edges := [ing "S" "idle", mailEdge]
  compatibility := .all
  steps := [step "S" "idle" "Go" "idle"]

def mailImpl : Impl where
  desc := mailDesc
  transitions := [tr "S" "idle" "Go" "idle" [.send "H" "M" 0, .terminate]]

def S0 : InstId := .peer "S" 0 0
def S1 : InstId := .peer "S" 0 1
def Hc : InstId := .core "H"

def mailActs : List Action :=
  [.spawn "S", .ingress S0 "Go", .recvBulk S0, .exec S0, .exec S0, .exec S0, .spawn "S"]

theorem old_mail_charged :
    ((runAt mailImpl 1 [.spawn "S"]).map fun w => (w.st S0).tokens "H") = some 1 ∧
    ((runAt mailImpl 1 mailActs).map fun w =>
      (lifeTag (w.st S0).life, lifeTag (w.st S1).life,
       (w.st Hc).box.length, (w.st S1).tokens "H")) = some (3, 1, 1, 0) := by decide

end Deadlock.Helen7c

#print axioms Deadlock.Helen7c.root_respawn_crashes
#print axioms Deadlock.Helen7c.orig_tombstone_later_refuted
#print axioms Deadlock.Helen7c.orig_key_split_refuted
#print axioms Deadlock.Helen7c.orig_crash_not_absorbing_refuted
#print axioms Deadlock.Helen7c.orig_tree_graph_rejected_refuted
#print axioms Deadlock.Helen7c.orig_respawn_child_crashes_refuted
#print axioms Deadlock.Helen7c.orig_dead_supervisor_crash_refuted
#print axioms Deadlock.Helen7c.sub2_ok
#print axioms Deadlock.Helen7c.sub2_root_crashes
#print axioms Deadlock.Helen7c.rtree_ok
#print axioms Deadlock.Helen7c.child_restart_overflow
#print axioms Deadlock.Helen7c.stale_tombstone
#print axioms Deadlock.Helen7c.nested_counted
#print axioms Deadlock.Helen7c.pool_sized
#print axioms Deadlock.Helen7c.pool_slots
#print axioms Deadlock.Helen7c.old_mail_charged
