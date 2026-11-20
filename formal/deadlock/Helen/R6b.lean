import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen6b
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

/-! ## Budget bypass: sends inside an outcome branch are not counted by `sendsOk`. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def bypassDesc : Description where
  name := "branch-bypass"
  freshNames := true
  templates := [tpl "A" 3 ["idle", "w"] "idle" true]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" 1]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" }]

/-- The peer timeout sends `M` three times to itself; the edge budget is one. -/
def bypassImpl : Impl where
  desc := bypassDesc
  transitions := [tr "A" "idle" "Go" "w" [.peer [.send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0]],
                  tr "A" "w" "Go" "w" [],
                  tr "A" "idle" "M" "idle" [],
                  tr "A" "w" "M" "w" []]

def Ac : InstId := .core "A"

def bypassActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .callTimeout Ac, .exec Ac, .exec Ac, .exec Ac, .exec Ac]

theorem bypass_graph : checkBool bypassDesc = true := by decide

/-- The peer branch sends four times. `sendsOk` counts them, and `LocalOk` rejects
the design. The step relation still runs the program; the check is what stops it
entering the deadlock-freedom hypotheses. -/
theorem bypass_rejected :
    localOkB bypassImpl = false ∧
      sendsTo "A" [.peer [.send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0]] = 4 := by
  decide

theorem bypass_assumptions : Assumptions bypassImpl :=
  ⟨fun tr h => ⟨tr, h, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The unchecked program still overruns: A's own mail on A is 3 queued + 1 parked
against a budget of 2, and `sendsTo` now reports the four branch sends. -/
theorem bypass_overrun :
    ((runAt bypassImpl 0 bypassActs).map fun w =>
      ((w.st Ac).box.length + (w.st Ac).parked.length, budget bypassDesc "A" "A",
        sendsTo "A" [.peer [.send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0, .send "A" "M" 0]])) =
    some (4, 2, 4) := by decide

/-! A fair run that ends with A parked on itself forever: `deadlock_freedom` fails. -/

def cfgR (j : Nat) : World := (runAt bypassImpl 0 (bypassActs.take j)).getD (initWorld bypassImpl 0)
def actR (j : Nat) : Action := bypassActs.getD j .stutter
def WT : World := cfgR 8

theorem cfgR_tail (j : Nat) (h : 8 ≤ j) : cfgR j = WT := by
  unfold cfgR WT
  rw [List.take_of_length_le (by simp [bypassActs]; omega)]
  rfl

theorem actR_tail (j : Nat) (h : 8 ≤ j) : actR j = .stutter := by
  unfold actR
  simp [List.getD, bypassActs]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

theorem WT_quiet : runtimeBusy bypassImpl WT = false := by decide
theorem WT_open : WT.crashed = false := by decide
theorem WT_roster : WT.roster = [Ac] := by decide

theorem step_eq (j : Nat) (hj : j < 8) :
    runAt bypassImpl 0 (bypassActs.take (j + 1)) =
      (runAt bypassImpl 0 (bypassActs.take j)).bind (apply bypassImpl (actR j)) := by
  have hget : bypassActs[j]? = some (actR j) := by
    unfold actR
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [bypassActs]; omega)]
    rfl
  rw [List.take_add_one, hget]
  simp [runAt, List.foldl_append]

theorem validR (j : Nat) : apply bypassImpl (actR j) (cfgR j) = some (cfgR (j + 1)) := by
  by_cases h : 8 ≤ j
  · rw [actR_tail j h, cfgR_tail j h, cfgR_tail (j + 1) (by omega)]
    simp [apply, stepWorld, WT_quiet, WT_open]
  · have hj : j < 8 := by omega
    have h1 : (runAt bypassImpl 0 (bypassActs.take j)).isSome = true := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : ((runAt bypassImpl 0 (bypassActs.take j)).bind (apply bypassImpl (actR j))).isSome = true := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h1
    rw [hw] at h2
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp h2
    simp only [Option.bind_some] at hw'
    unfold cfgR
    rw [step_eq j hj, hw]
    simp [hw']

def ρB : Run bypassImpl 0 where
  cfg := cfgR
  act := actR
  startN := by decide
  start := rfl
  valid := validR

/-- Same hypothesis as in R6a: `off_idle_reachable` specialised to `WT`. -/
def OffIdle : Prop := ∀ id, id ∉ WT.roster → (WT.st id).phase = .idle ∧ (WT.st id).life = .absent

theorem WT_disabled (hoff : OffIdle) (a : Action) (hf : forced a = true) : ¬ Enabled bypassImpl WT a := by
  intro hen
  apply hen
  have key : ∀ s, (a = .recvBulk s ∨ a = .recvPrio s ∨ a = .exec s ∨ a = .finish s ∨ a = .callTimeout s) →
      apply bypassImpl a WT = none := by
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

theorem fairB (hoff : OffIdle) : Fair ρB where
  weak := by
    intro a i hf hen
    exact absurd (hen (max i 8) (by omega)) (by
      show ¬ Enabled bypassImpl (cfgR (max i 8)) a
      rw [cfgR_tail _ (by omega)]; exact WT_disabled hoff a hf)
  bulk := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf 8
    exact absurd hen (by
      show ¬ Enabled bypassImpl (cfgR j) (.recvBulk s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)
  prio := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf 8
    exact absurd hen (by
      show ¬ Enabled bypassImpl (cfgR j) (.recvPrio s)
      rw [cfgR_tail _ hj]; exact WT_disabled hoff _ rfl)

theorem stuck_A : Stuck ρB Ac 8 := by
  have hw : waitKind (WT.st Ac) = some (.blockingSend Ac) := by decide
  refine ⟨⟨rfl, by show waitKind ((cfgR 8).st Ac) ≠ none; rw [cfgR_tail 8 (Nat.le_refl _), hw]; simp⟩, ?_⟩
  intro j hj
  show SameWait ((cfgR 8).st Ac) ((cfgR j).st Ac)
  rw [cfgR_tail 8 (Nat.le_refl _), cfgR_tail j hj]
  exact ⟨rfl, by rw [hw]; simp⟩

theorem bypass_deadlock (hoff : OffIdle) : Deadlock ρB := by
  refine ⟨Ac, 8, stuck_A, ?_⟩
  show (match waitKind ((cfgR 8).st Ac) with
    | some (.blockingSend _) => True | some (.callReply _) => True
    | some .effect => True | some .peer => True | _ => False)
  rw [cfgR_tail 8 (Nat.le_refl _)]
  have hw : waitKind (WT.st Ac) = some (.blockingSend Ac) := by decide
  rw [hw]; trivial

end Deadlock.Helen6b

#print axioms Deadlock.Helen6b.bypass_graph
#print axioms Deadlock.Helen6b.bypass_rejected
#print axioms Deadlock.Helen6b.bypass_overrun
#print axioms Deadlock.Helen6b.fairB
