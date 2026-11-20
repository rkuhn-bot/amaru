import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7b
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


/-! ## N1 variant: a branch lands in a typestate whose floor is higher than `toState`'s.
`sendsOk` checks the program against `toState` only. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def landDesc (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Description where
  name := "branch-landing"
  freshNames := true
  templates := [tpl "A" cap ["idle", "w", "miss"] "idle" true]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" occW, sendEdge "A" "miss" "A" "M" occM]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "miss", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "A", fromState := "miss", toState := "miss", label := "M" }]

def landImpl (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Impl where
  desc := landDesc cap occW occM
  transitions := [{ tr "A" "idle" "Go" "w" [.peer [.send "A" "M" 0]] with toTimeout := "miss" },
                  tr "A" "w" "Go" "w" [],
                  tr "A" "miss" "Go" "w" (List.replicate (occW + 1) (.send "A" "M" 0)),
                  tr "A" "idle" "M" "idle" [],
                  tr "A" "w" "M" "w" [],
                  tr "A" "miss" "M" "miss" []]

def Ac : InstId := .core "A"

def landActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .callTimeout Ac, .exec Ac,
   .recvBulk Ac, .exec Ac, .exec Ac, .exec Ac]

def snap (w : World) : String × Nat × Nat × Nat × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | _ => 3)

def LI : Impl := landImpl 4 2 0

theorem land_graph : checkBool (landDesc 4 2 0) = true := by decide
theorem land_local : LocalOk LI := by unfold LocalOk; decide
theorem land_assumptions : Assumptions LI :=
  ⟨fun tr h => ⟨tr, h, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The timeout branch sends one `M` and lands in `miss`, whose floor (3) is
above `w`'s (0). `sendsOk` only checks `1 + floor w ≤ floor idle`. -/
theorem land_unchecked :
    sendsTo "A" [.peer [.send "A" "M" 0]] = 1 ∧
      floorState (landDesc 4 2 0) "A" "idle" "A" = 2 ∧
      floorState (landDesc 4 2 0) "A" "w" "A" = 0 ∧
      floorState (landDesc 4 2 0) "A" "miss" "A" = 3 := by decide

theorem land_overrun :
    ((runAt LI 0 landActs).map fun w =>
      ((w.st Ac).box.length, (w.st Ac).parked.length, capBulk (landDesc 4 2 0) 0 Ac,
        budget (landDesc 4 2 0) "A" "A")) = some (4, 1, 4, 3) := by decide

def L : Nat := 11
def cfgR (j : Nat) : World := (runAt LI 0 (landActs.take j)).getD (initWorld LI 0)
def actR (j : Nat) : Action := landActs.getD j .stutter
def WT : World := cfgR L

theorem cfgR_tail (j : Nat) (h : L ≤ j) : cfgR j = WT := by
  unfold cfgR WT
  rw [List.take_of_length_le (by simp [landActs]; unfold L at h; omega)]
  rfl

theorem actR_tail (j : Nat) (h : L ≤ j) : actR j = .stutter := by
  unfold actR
  simp [List.getD, landActs]
  rw [List.getElem?_eq_none (by simp; unfold L at h; omega)]
  rfl

theorem WT_quiet : runtimeBusy LI WT = false := by decide
theorem WT_open : WT.crashed = false := by decide
theorem WT_roster : WT.roster = [Ac] := by decide

theorem step_eq (j : Nat) (hj : j < L) :
    runAt LI 0 (landActs.take (j + 1)) =
      (runAt LI 0 (landActs.take j)).bind (apply LI (actR j)) := by
  have hget : landActs[j]? = some (actR j) := by
    unfold actR
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [landActs]; unfold L at hj; omega)]
    rfl
  rw [List.take_add_one, hget]
  simp [runAt, List.foldl_append]

theorem validR (j : Nat) : apply LI (actR j) (cfgR j) = some (cfgR (j + 1)) := by
  by_cases h : L ≤ j
  · rw [actR_tail j h, cfgR_tail j h, cfgR_tail (j + 1) (by omega)]
    simp [apply, stepWorld, WT_quiet, WT_open]
  · have hj : j < L := by omega
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by
      unfold L at hj; omega
    have h1 : (runAt LI 0 (landActs.take j)).isSome = true := by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : ((runAt LI 0 (landActs.take j)).bind (apply LI (actR j))).isSome = true := by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h1
    rw [hw] at h2
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp h2
    simp only [Option.bind_some] at hw'
    unfold cfgR
    rw [step_eq j hj, hw]
    simp [hw']

def ρL : Run LI 0 where
  cfg := cfgR
  act := actR
  startN := by decide
  start := rfl
  valid := validR

/-- `off_idle_reachable` (Progress.lean, red) specialised to `WT`, as in R6b. -/
def OffIdle : Prop := ∀ id, id ∉ WT.roster → (WT.st id).phase = .idle ∧ (WT.st id).life = .absent

theorem WT_disabled (hoff : OffIdle) (a : Action) (hf : forced a = true) : ¬ Enabled LI WT a := by
  intro hen
  apply hen
  have key : ∀ s, (a = .recvBulk s ∨ a = .recvPrio s ∨ a = .exec s ∨ a = .finish s ∨ a = .callTimeout s) →
      apply LI a WT = none := by
    intro s hsub
    by_cases hs : s ∈ WT.roster
    · rw [WT_roster] at hs; simp at hs; subst hs
      rcases hsub with rfl | rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨hidle, hdead⟩ := hoff s hs
      rcases hsub with rfl | rfl | rfl | rfl | rfl
      · simp [apply, stepWorld, WT_open, receiveBulk, hdead]
      · cases hp : (WT.st s).prio with
        | nil => simp [apply, stepWorld, WT_open, receivePrio, hp]
        | cons _ _ => simp [apply, stepWorld, WT_open, receivePrio, hp, hdead]
      · simp [apply, stepWorld, WT_open, execHead, hdead]
      · simp [apply, stepWorld, WT_open, finishWait, hdead]
      · simp [apply, stepWorld, WT_open, callTimeout, hdead]
  cases a with
  | recvBulk s => exact key s (Or.inl rfl)
  | recvPrio s => exact key s (Or.inr (Or.inl rfl))
  | exec s => exact key s (Or.inr (Or.inr (Or.inl rfl)))
  | finish s => exact key s (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | callTimeout s => exact key s (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | spawn _ => simp [forced] at hf
  | ingress _ _ => simp [forced] at hf
  | stutter => simp [forced] at hf

theorem fairL (hoff : OffIdle) : Fair ρL where
  weak := by
    intro a i hf hen
    exact absurd (hen (max i L) (by omega)) (by
      show ¬ Enabled LI (cfgR (max i L)) a
      rw [cfgR_tail _ (by omega)]; exact WT_disabled hoff a hf)
  bulk := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf L
    exact absurd hen (by
      show ¬ Enabled LI (cfgR j) (.recvBulk s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)
  prio := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf L
    exact absurd hen (by
      show ¬ Enabled LI (cfgR j) (.recvPrio s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)

theorem stuck_A : Stuck ρL Ac L := by
  have hw : waitKind (WT.st Ac) = some (.blockingSend Ac) := by decide
  refine ⟨⟨rfl, by show waitKind ((cfgR L).st Ac) ≠ none; rw [cfgR_tail L (Nat.le_refl _), hw]; simp⟩, ?_⟩
  intro j hj
  show SameWait ((cfgR L).st Ac) ((cfgR j).st Ac)
  rw [cfgR_tail L (Nat.le_refl _), cfgR_tail j hj]
  exact ⟨rfl, by rw [hw]; simp⟩

theorem land_deadlock (hoff : OffIdle) : Deadlock ρL := by
  refine ⟨Ac, L, stuck_A, ?_⟩
  show (match waitKind ((cfgR L).st Ac) with
    | some (.blockingSend _) => True | some (.callReply _) => True
    | some .effect => True | some .peer => True | _ => False)
  rw [cfgR_tail L (Nat.le_refl _)]
  have hw : waitKind (WT.st Ac) = some (.blockingSend Ac) := by decide
  rw [hw]; trivial

/-- The headline (Rank.lean:18783, exact hypothesis shape) fails: the final world is not crashed. -/
theorem deadlock_freedom_false (hoff : OffIdle) :
    ¬ (∀ (I : Impl), LocalOk I → GraphOk I.desc → Assumptions I →
        ∀ {N : Nat} (ρ : Run I N), Fair ρ → ¬ Deadlock ρ) := by
  intro h
  exact h LI land_local (checkBool_sound _ land_graph) land_assumptions ρL (fairL hoff) (land_deadlock hoff)

/-- The reporter disagrees with the checker: drop the `miss → A M` edge and
`localOkB` rejects (the branch send is checked at `miss`), but `localIssues` is empty. -/
def noEdge : Impl := { landImpl 4 2 0 with desc := { landDesc 4 2 0 with edges := (landDesc 4 2 0).edges.take 3 } }
theorem reporter_gap : localOkB noEdge = false := by decide
-- `#eval localIssues noEdge` prints `[]` (string-built, not kernel-reducible).
#eval localIssues noEdge

end Deadlock.Helen7b

#print axioms Deadlock.Helen7b.land_graph
#print axioms Deadlock.Helen7b.land_local
#print axioms Deadlock.Helen7b.land_unchecked
#print axioms Deadlock.Helen7b.land_overrun
#print axioms Deadlock.Helen7b.fairL
#print axioms Deadlock.Helen7b.land_deadlock
#print axioms Deadlock.Helen7b.deadlock_freedom_false
#print axioms Deadlock.Helen7b.reporter_gap
