import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7d
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


/-! ## N1 variant: a parked call's `onTimedOut` is not in `pending`. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def pcDesc (capA capB k : Nat) : Description where
  name := "parked-call"
  freshNames := true
  templates := [tpl "A" capA ["idle", "w"] "idle" true, tpl "B" capB ["idle"] "idle" false]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" k,
            { (sendEdge "A" "w" "B" "Q" 1) with effect := .call, repliesInDequeue := true }]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Q" }]

def trc (t f l to : String) (p : List Eff) (c : Bool) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := c, release := 1 }

def pcImpl (capA capB k : Nat) : Impl where
  desc := pcDesc capA capB k
  transitions := [trc "A" "idle" "Go" "w" [.call "B" "Q" 0 [] (List.replicate k (.send "A" "M" 0))] false,
                  trc "A" "w" "Go" "w" [] false,
                  trc "A" "idle" "M" "idle" [] false,
                  trc "A" "w" "M" "w" [] false,
                  trc "B" "idle" "Q" "idle" [.reply] true]

def Ac : InstId := .core "A"
def Bc : InstId := .core "B"

def snap (w : World) : String × Nat × Nat × Nat × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | .awaitReply _ _ => 4 | _ => 3)
def pcActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .ingress Ac "Go",
   .recvBulk Bc, .callTimeout Ac, .exec Ac, .exec Ac, .exec Bc]
def PI : Impl := pcImpl 4 0 2

theorem pc_graph : checkBool (pcDesc 4 0 2) = true := by decide
theorem pc_local : LocalOk PI := by unfold LocalOk; decide
theorem pc_assumptions : Assumptions PI :=
  ⟨fun tr h => ⟨tr, h, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- While the call is parked, `pending` ignores `onTimedOut` (2 sends to A). -/
theorem pc_pending_gap :
    ((runAt PI 0 (pcActs.take 3)).map fun w => (pending (w.st Ac) "A", (w.st Ac).tokens "A")) = some (0, 3) ∧
    ((runAt PI 0 (pcActs.take 6)).map fun w => (pending (w.st Ac) "A", (w.st Ac).tokens "A")) = some (0, 0) ∧
    ((runAt PI 0 (pcActs.take 7)).map fun w => (pending (w.st Ac) "A", (w.st Ac).tokens "A")) = some (2, 0) := by decide

theorem pc_overrun :
    ((runAt PI 0 pcActs).map fun w =>
      ((w.st Ac).box.length, (w.st Ac).parked.length, capBulk (pcDesc 4 0 2) 0 Ac)) = some (4, 1, 4) := by decide

def L : Nat := 11
def cfgR (j : Nat) : World := (runAt PI 0 (pcActs.take j)).getD (initWorld PI 0)
def actR (j : Nat) : Action := pcActs.getD j .stutter
def WT : World := cfgR L

theorem cfgR_tail (j : Nat) (h : L ≤ j) : cfgR j = WT := by
  unfold cfgR WT
  rw [List.take_of_length_le (by simp [pcActs]; unfold L at h; omega)]
  rfl

theorem actR_tail (j : Nat) (h : L ≤ j) : actR j = .stutter := by
  unfold actR
  simp [List.getD, pcActs]
  rw [List.getElem?_eq_none (by simp; unfold L at h; omega)]
  rfl

theorem WT_quiet : runtimeBusy PI WT = false := by decide
theorem WT_open : WT.crashed = false := by decide
theorem WT_roster : WT.roster = [Ac, Bc] := by decide

theorem step_eq (j : Nat) (hj : j < L) :
    runAt PI 0 (pcActs.take (j + 1)) =
      (runAt PI 0 (pcActs.take j)).bind (apply PI (actR j)) := by
  have hget : pcActs[j]? = some (actR j) := by
    unfold actR
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [pcActs]; unfold L at hj; omega)]
    rfl
  rw [List.take_add_one, hget]
  simp [runAt, List.foldl_append]

theorem validR (j : Nat) : apply PI (actR j) (cfgR j) = some (cfgR (j + 1)) := by
  by_cases h : L ≤ j
  · rw [actR_tail j h, cfgR_tail j h, cfgR_tail (j + 1) (by omega)]
    simp [apply, stepWorld, WT_quiet, WT_open]
  · have hj : j < L := by omega
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by
      unfold L at hj; omega
    have h1 : (runAt PI 0 (pcActs.take j)).isSome = true := by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : ((runAt PI 0 (pcActs.take j)).bind (apply PI (actR j))).isSome = true := by
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h1
    rw [hw] at h2
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp h2
    simp only [Option.bind_some] at hw'
    unfold cfgR
    rw [step_eq j hj, hw]
    simp [hw']

def ρP : Run PI 0 where
  cfg := cfgR
  act := actR
  startN := by decide
  start := rfl
  valid := validR

/-- `off_idle_reachable` (Progress.lean, red) specialised to `WT`, as in R6b. -/
def OffIdle : Prop := ∀ id, id ∉ WT.roster → (WT.st id).phase = .idle ∧ (WT.st id).life = .absent

theorem WT_disabled (hoff : OffIdle) (a : Action) (hf : forced a = true) : ¬ Enabled PI WT a := by
  intro hen
  apply hen
  have key : ∀ s, (a = .recvBulk s ∨ a = .recvPrio s ∨ a = .exec s ∨ a = .finish s ∨ a = .callTimeout s) →
      apply PI a WT = none := by
    intro s hsub
    by_cases hs : s ∈ WT.roster
    · rw [WT_roster] at hs; simp at hs
      rcases hs with rfl | rfl <;> rcases hsub with rfl | rfl | rfl | rfl | rfl <;> decide
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

theorem fairP (hoff : OffIdle) : Fair ρP where
  weak := by
    intro a i hf hen
    exact absurd (hen (max i L) (by omega)) (by
      show ¬ Enabled PI (cfgR (max i L)) a
      rw [cfgR_tail _ (by omega)]; exact WT_disabled hoff a hf)
  bulk := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf L
    exact absurd hen (by
      show ¬ Enabled PI (cfgR j) (.recvBulk s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)
  prio := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf L
    exact absurd hen (by
      show ¬ Enabled PI (cfgR j) (.recvPrio s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)

theorem stuck_A : Stuck ρP Ac L := by
  have hw : waitKind (WT.st Ac) = some (.blockingSend Ac) := by decide
  refine ⟨⟨rfl, by show waitKind ((cfgR L).st Ac) ≠ none; rw [cfgR_tail L (Nat.le_refl _), hw]; simp⟩, ?_⟩
  intro j hj
  show SameWait ((cfgR L).st Ac) ((cfgR j).st Ac)
  rw [cfgR_tail L (Nat.le_refl _), cfgR_tail j hj]
  exact ⟨rfl, by rw [hw]; simp⟩

theorem pc_deadlock (hoff : OffIdle) : Deadlock ρP := by
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
  exact h PI pc_local (checkBool_sound _ pc_graph) pc_assumptions ρP (fairP hoff) (pc_deadlock hoff)

end Deadlock.Helen7d

#print axioms Deadlock.Helen7d.pc_graph
#print axioms Deadlock.Helen7d.pc_local
#print axioms Deadlock.Helen7d.pc_pending_gap
#print axioms Deadlock.Helen7d.pc_overrun
#print axioms Deadlock.Helen7d.fairP
#print axioms Deadlock.Helen7d.pc_deadlock
#print axioms Deadlock.Helen7d.deadlock_freedom_false
