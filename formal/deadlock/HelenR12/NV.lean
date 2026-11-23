import Deadlock.Orphan
import Deadlock.Tomb
import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen11nv
open Deadlock Deadlock.Orphan

def tM : Template := { tpl "M" 4 ["boot", "up", "done"] "boot" true with capacity := { a := 0, b := 4 } }
def nvDesc : Description where
  name := "nv"
  freshNames := true
  templates := orphanDesc.templates ++ [tM]
  edges := orphanDesc.edges ++ [{ ing "M" "boot" with occupancy := { a := 0, b := 1 } },
    { ing "M" "up" with occupancy := { a := 0, b := 1 } }, { ing "M" "done" with occupancy := { a := 0, b := 1 } }]
  compatibility := .all
  steps := orphanDesc.steps ++ [step "M" "boot" "Go" "up", step "M" "up" "Go" "done", step "M" "done" "Go" "done"]
def nvImpl : Impl where
  desc := nvDesc
  transitions := orphanImpl.transitions ++
      [tr "M" "boot" "Go" "up" [], tr "M" "up" "Go" "done" [], tr "M" "done" "Go" "done" []]
#eval (render nvDesc, localIssues nvImpl)
#eval (runAt nvImpl 2 [.ingress (.core "M") "Go", .recvBulk (.core "M"), .exec (.core "M"), .exec (.core "M")]).map fun w => (w.roster.map fun i => toString (repr i).pretty, (w.st (.core "M")).typestate)
#eval (List.range 8).map fun n => (n, (runAt nvImpl 2 ([.ingress (.core "M") "Go", .recvBulk (.core "M"), .exec (.core "M"), .exec (.core "M"), .ingress (.peer "W" 0 0) "Go", .recvBulk (.peer "W" 0 0), .exec (.peer "W" 0 0)].take n)).isSome)
#eval (["R", "C", "G", "M"].map fun p => (p, prioSized nvDesc p (prioLabels nvImpl p).length))

theorem foldl_reach (I : Impl) (N : Nat) :
    ∀ (acts : List Action) (w0 : Option World),
      (∀ w, w0 = some w → Reachable I N w) →
      ∀ w, acts.foldl (fun w a => w.bind (apply I a)) w0 = some w → Reachable I N w := by
  intro acts
  induction acts with
  | nil => intro w0 h w hw; exact h w hw
  | cons a as ih =>
    intro w0 h w hw
    simp only [List.foldl_cons] at hw
    refine ih _ ?_ w hw
    intro w1 hw1
    cases w0 with
    | none => simp at hw1
    | some w' =>
      simp only [Option.bind_some] at hw1
      exact Reachable.step w' w1 a (h w' rfl) hw1

theorem runAt_reach (I : Impl) (N : Nat) (acts : List Action) (w : World)
    (h : runAt I N acts = some w) : Reachable I N w :=
  foldl_reach I N acts (some (initWorld I N)) (fun w hw => by cases hw; exact Reachable.init) w h

theorem some_getD (o : Option World) (d : World) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o with
  | none => simp at h
  | some w => rfl

theorem nv_graph : GraphOk nvDesc := checkBool_sound nvDesc (by decide)
theorem nv_local : LocalOk nvImpl := by unfold LocalOk; decide

/-- Preconditions of `no_tombstone_overflow` on a concrete reachable seal: per-peer child C@0.0 under R@0.0. -/
def pre (w : World) (child : InstId) : Bool :=
  let s := releaseWorld nvDesc w child (w.st child)
  decide ((w.st child).life = .shuttingDown) && (w.st child).pendingTombstone &&
  (match liveSupervisor nvDesc s child with
   | some p => decide ((s.st p).life = .alive) && (tombstoneMsg nvDesc (s.st p) child).label != ""
   | none => false)

#eval (runAt nvImpl 2 killed).map fun w => (pre w C0, liveSupervisor nvDesc (releaseWorld nvDesc w C0 (w.st C0)) C0,
  (apply nvImpl (.exec C0) w).map fun w' => (w'.crashed, (w'.st R0).prio.map (·.label), prioLoad (w'.st R0).prio, capPrio nvDesc 2 R0))
/-- Non-vacuity: GraphOk, LocalOk and a reachable seal meeting every precondition, for a subtree child. -/
theorem nv_subtree_seal : ∃ w, Reachable nvImpl 2 w ∧ pre w C0 = true ∧
    prioLoad ((releaseWorld nvDesc w C0 (w.st C0)).st R0).prio <
      capPrio nvDesc (releaseWorld nvDesc w C0 (w.st C0)).N R0 := by
  have h := some_getD (runAt nvImpl 2 killed) (initWorld nvImpl 2) (by decide)
  refine ⟨_, runAt_reach _ _ _ _ h, by decide, ?_⟩
  have hR := runAt_reach _ _ _ _ h
  have hpre : liveSupervisor nvDesc (releaseWorld nvDesc ((runAt nvImpl 2 killed).getD (initWorld nvImpl 2)) C0
      (((runAt nvImpl 2 killed).getD (initWorld nvImpl 2)).st C0)) C0 = some R0 := by decide
  exact no_tombstone_overflow nvImpl 2 _ C0 nv_graph nv_local hR (by decide) (by decide) R0 hpre (by decide)

#print axioms nv_subtree_seal
#print axioms no_tombstone_overflow
#print axioms hold_reach
#print axioms Side
#print axioms side_step
#print axioms side_init
#print axioms reach_pack
#print axioms hold_step
end Deadlock.Helen11nv
#print axioms Deadlock.self_schedule_fits
#print axioms Deadlock.cell_wake_fits
#print axioms Deadlock.tombstone_label_ne
#print axioms Deadlock.wire_reach
#print axioms Deadlock.Outlive.outlive_refused
#print axioms Deadlock.Outlive.outlive_checked
#print axioms Deadlock.Orphan.orphan_respawn
