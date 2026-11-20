import Deadlock.Semantics
import Deadlock.Local
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen7a
open Deadlock

/-! Copied verbatim from Examples.lean:8-33. `Deadlock.Examples` cannot be imported
next to `Deadlock.Semantics`: both declare `Deadlock.overflowDesc`. -/
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

/-! ## 1. Every non-send wait has a forced exit that is enabled whenever the waiter is alive. -/

theorem timeout_enabled_reply (w : World) (s d : InstId) (k : Cont)
    (hl : (w.st s).life = .alive) (hp : (w.st s).phase = .awaitReply d k) :
    (callTimeout w s).isSome = true := by
  simp [callTimeout, hl, hp]

theorem timeout_enabled_parked (w : World) (s d : InstId) (k : Cont)
    (hl : (w.st s).life = .alive) (hp : (w.st s).phase = .parked d true k) :
    (callTimeout w s).isSome = true := by
  simp [callTimeout, hl, hp]

/-- `finish` now needs a live actor (Semantics.lean:1569). -/
theorem peer_finish_live (I : Impl) (w : World) (s : InstId) (k : Cont)
    (hl : (w.st s).life = .alive) (hp : (w.st s).phase = .awaitPeer k) :
    finishWait I w s = some (setActor w s (proceed (w.st s) k)) := by
  simp [finishWait, hl, hp]

/-! ## 2. Call instance: C calls core B. -/

def ingC (st : String) : Edge :=
  { (sendEdge "C" st "C" "Go" 1) with effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def callDesc : Description where
  name := "timed-call"
  freshNames := true
  templates := [tpl "C" 2 ["idle", "wait", "miss"] "idle" true, tpl "B" 2 ["idle"] "idle" true]
  edges := [ingC "idle", ingC "wait",
            { (sendEdge "C" "wait" "B" "Q" 1) with effect := .call, repliesInDequeue := true }]
  compatibility := .all
  steps := [{ template := "C", fromState := "idle", toState := "wait", label := "Go" },
            { template := "C", fromState := "wait", toState := "wait", label := "Go" },
            { template := "C", fromState := "miss", toState := "miss", label := "Go" },
            { template := "B", fromState := "idle", toState := "idle", label := "Q" }]

def tr (t f l to : String) (p : List Eff) (c : Bool) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := c, release := 1 }

def callImpl : Impl where
  desc := callDesc
  transitions := [{ tr "C" "idle" "Go" "wait" [.call "B" "Q" 0 [] []] false with toTimedOut := "miss" },
                  tr "C" "wait" "Go" "wait" [] false,
                  tr "C" "miss" "Go" "miss" [] false,
                  tr "B" "idle" "Q" "idle" [.reply] true]

def Cc : InstId := .core "C"
def Bc : InstId := .core "B"

def runAt (I : Impl) (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply I a)) (some (initWorld I N))

def raceActs : List Action :=
  [.ingress Cc "Go", .recvBulk Cc, .exec Cc, .callTimeout Cc, .recvBulk Bc, .exec Bc]
def replyActs : List Action :=
  [.ingress Cc "Go", .recvBulk Cc, .exec Cc, .recvBulk Bc, .exec Bc]

def lastTag (w : Option World) : Nat :=
  match w with
  | some w => match (w.st Cc).lastCall with
    | some (n, .reply) => 10 * n + 1
    | some (n, .notAdmitted) => 10 * n + 2
    | some (n, .timedOut) => 10 * n + 3
    | none => 0
  | none => 99

def phaseTag (w : Option World) (x : InstId) : Nat :=
  match w with
  | some w => match (w.st x).phase with
    | .idle => 1 | .run _ => 2 | .parked _ _ _ => 3 | .awaitReply _ _ => 4
    | .awaitEffect _ => 5 | .awaitPeer _ => 6 | .crashed => 7
  | none => 99

theorem call_graph : checkBool callDesc = true := by decide
theorem call_local : LocalOk callImpl := by
  unfold LocalOk
  decide

/-- Right after admission, both the callee's receive and the caller's timeout are enabled. -/
theorem race_point :
    phaseTag (runAt callImpl 0 (raceActs.take 3)) Cc = 4 ∧
    ((runAt callImpl 0 (raceActs.take 3)).bind (callTimeout · Cc)).isSome = true ∧
    ((runAt callImpl 0 (raceActs.take 3)).bind (receiveBulk callImpl · Bc)).isSome = true := by
  decide

/-- The timeout wins: call 0 ends `TimedOut`, B still handles the (detached) request,
and the world is quiet afterwards. B was alive throughout. -/
theorem race_timedout :
    lastTag (runAt callImpl 0 raceActs) = 3 ∧
    ((runAt callImpl 0 raceActs).map fun w => runtimeBusy callImpl w) = some false ∧
    (List.range (raceActs.length + 1)).all (fun n =>
      ((runAt callImpl 0 (raceActs.take n)).map fun w => (w.st Bc).life == .alive) == some true) = true := by
  decide

/-- The same call answered: `Reply`. -/
theorem race_reply : lastTag (runAt callImpl 0 replyActs) = 1 := by decide

/-- Each outcome lands in its own typestate. `TimedOut` is `miss`. `Reply` stays `wait`. -/
theorem outcome_own_state :
    ((runAt callImpl 0 raceActs).map fun w => (w.st Cc).typestate) = some "miss" ∧
    ((runAt callImpl 0 replyActs).map fun w => (w.st Cc).typestate) = some "wait" := by
  decide


/-- `TimedOut` runs its own program into its own typestate. The replied run does neither. -/
def callImpl2 : Impl where
  desc := callDesc
  transitions := [{ tr "C" "idle" "Go" "wait" [.call "B" "Q" 0 [] [.selfSchedule "late"]] false
                    with toTimedOut := "late" },
                  tr "C" "wait" "Go" "wait" [] false,
                  tr "B" "idle" "Q" "idle" [.reply] true]

theorem outcome_branches :
    ((runAt callImpl2 0 (raceActs.take 4 ++ [.exec Cc])).map fun w => ((w.st Cc).typestate, (w.st Cc).prio.map (·.label))) =
      some ("late", ["late"]) ∧
    ((runAt callImpl2 0 replyActs).map fun w => ((w.st Cc).typestate, (w.st Cc).prio.map (·.label))) =
      some ("wait", []) := by decide

/-- Outcome branches are visible to the counts `LocalOk` uses. -/
theorem branch_labels_counted :
    prioLabels callImpl2 "C" = ["late"] ∧
    selfLabels [.call "B" "Q" 0 [] [.selfSchedule "late"]] = ["late"] ∧
    replyCount [.peer [.reply]] = 1 ∧ hasTerminate [.peer [.terminate]] = true ∧
    sendsTo "B" [.peer [.send "B" "M" 0]] = 1 := by decide

/-! ## 3. A fair run in which the callee stays alive and the call never gets `Reply`. -/

def cfgR (j : Nat) : World := (runAt callImpl 0 (raceActs.take j)).getD (initWorld callImpl 0)
def actR (j : Nat) : Action := raceActs.getD j .stutter

def W6 : World := cfgR 6

theorem cfgR_tail (j : Nat) (h : 6 ≤ j) : cfgR j = W6 := by
  unfold cfgR W6
  rw [List.take_of_length_le (by simp [raceActs]; omega)]
  rfl

theorem actR_tail (j : Nat) (h : 6 ≤ j) : actR j = .stutter := by
  unfold actR
  simp [List.getD, raceActs]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

theorem W6_quiet : runtimeBusy callImpl W6 = false := by decide
theorem W6_open : W6.crashed = false := by decide
theorem W6_roster : W6.roster = [Cc, Bc] := by decide

theorem step_eq (j : Nat) (hj : j < 6) :
    runAt callImpl 0 (raceActs.take (j + 1)) =
      (runAt callImpl 0 (raceActs.take j)).bind (apply callImpl (actR j)) := by
  have hget : raceActs[j]? = some (actR j) := by
    unfold actR
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [raceActs]; omega)]
    rfl
  rw [List.take_add_one, hget]
  simp [runAt, List.foldl_append]

theorem validR (j : Nat) : apply callImpl (actR j) (cfgR j) = some (cfgR (j + 1)) := by
  by_cases h : 6 ≤ j
  · rw [actR_tail j h, cfgR_tail j h, cfgR_tail (j + 1) (by omega)]
    simp [apply, stepWorld, W6_quiet, W6_open]
  · have hj : j < 6 := by omega
    have h1 : (runAt callImpl 0 (raceActs.take j)).isSome = true := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : ((runAt callImpl 0 (raceActs.take j)).bind (apply callImpl (actR j))).isSome = true := by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h1
    rw [hw] at h2
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp h2
    simp only [Option.bind_some] at hw'
    unfold cfgR
    rw [step_eq j hj, hw]
    simp [hw']

def ρR : Run callImpl 0 where
  cfg := cfgR
  act := actR
  startN := by decide
  start := rfl
  valid := validR

/-- `off_idle_reachable` (Progress.lean:877) specialised to this world. That file
does not build in this snapshot, so it is a hypothesis here. The peer half is
proved below without it. -/
def OffIdle : Prop := ∀ id, id ∉ W6.roster → (W6.st id).phase = .idle ∧ (W6.st id).life = .absent

theorem off_peer (n : String) (k g : Nat) :
    (W6.st (.peer n k g)).phase = .idle ∧ (W6.st (.peer n k g)).life = .absent := by
  have h : ((W6.st (.peer n k g)).life == .absent, phaseTag (some W6) (.peer n k g)) = (true, 1) := rfl
  constructor
  · revert h; cases hp : (W6.st (.peer n k g)).phase <;> simp [phaseTag, hp]
  · revert h; cases hl : (W6.st (.peer n k g)).life <;> simp

theorem W6_none_on_roster (a : Action) (hf : forced a = true) (s : InstId) (hs : s ∈ [Cc, Bc])
    (hsub : a = .recvBulk s ∨ a = .recvPrio s ∨ a = .exec s ∨ a = .finish s ∨ a = .callTimeout s) :
    apply callImpl a W6 = none := by
  simp at hs
  rcases hs with rfl | rfl <;> rcases hsub with rfl | rfl | rfl | rfl | rfl <;> decide

theorem W6_disabled (hoff : OffIdle) (a : Action) (hf : forced a = true) : ¬ Enabled callImpl W6 a := by
  intro hen
  apply hen
  have key : ∀ s, (a = .recvBulk s ∨ a = .recvPrio s ∨ a = .exec s ∨ a = .finish s ∨ a = .callTimeout s) →
      apply callImpl a W6 = none := by
    intro s hsub
    by_cases hs : s ∈ W6.roster
    · rw [W6_roster] at hs; exact W6_none_on_roster a hf s hs hsub
    · obtain ⟨hidle, hdead⟩ := hoff s hs
      rcases hsub with rfl | rfl | rfl | rfl | rfl
      · simp [apply, stepWorld, W6_open, receiveBulk, hdead]
      · cases hp : (W6.st s).prio with
        | nil => simp [apply, stepWorld, W6_open, receivePrio, hp]
        | cons _ _ => simp [apply, stepWorld, W6_open, receivePrio, hp, hdead]
      · simp [apply, stepWorld, W6_open, execHead, hdead]
      · simp [apply, stepWorld, W6_open, finishWait, hidle]
      · simp [apply, stepWorld, W6_open, callTimeout, hdead]
  cases a with
  | recvBulk s => exact key s (Or.inl rfl)
  | recvPrio s => exact key s (Or.inr (Or.inl rfl))
  | exec s => exact key s (Or.inr (Or.inr (Or.inl rfl)))
  | finish s => exact key s (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | callTimeout s => exact key s (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | spawn _ => simp [forced] at hf
  | ingress _ _ => simp [forced] at hf
  | stutter => simp [forced] at hf

theorem fairR (hoff : OffIdle) : Fair ρR where
  weak := by
    intro a i hf hen
    exact absurd (hen (max i 6) (by omega)) (by
      show ¬ Enabled callImpl (cfgR (max i 6)) a
      rw [cfgR_tail _ (by omega)]; exact W6_disabled hoff a hf)
  bulk := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf 6
    exact absurd hen (by
      show ¬ Enabled callImpl (cfgR j) (.recvBulk s)
      rw [cfgR_tail _ hj]; exact W6_disabled hoff _ rfl)
  prio := by
    intro s hinf
    obtain ⟨j, hj, hen⟩ := hinf 6
    exact absurd hen (by
      show ¬ Enabled callImpl (cfgR j) (.recvPrio s)
      rw [cfgR_tail _ hj]; exact W6_disabled hoff _ rfl)

theorem callImpl_assumptions : Assumptions callImpl := ⟨fun tr h => ⟨tr, h, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Copied verbatim from Deliver.lean:33 (that file does not build). -/
def callWaiting (a : Actor) (d : InstId) (k : Cont) : Prop :=
  a.phase = .awaitReply d k ∨ a.phase = .parked d true k

/-- The state of the caller right after admission (index 3). -/
theorem waiting3 : ∃ k, callWaiting ((ρR.cfg 3).st Cc) Bc k := by
  cases hp : ((cfgR 3).st Cc).phase with
  | awaitReply d k =>
    have hd : d = Bc := by
      have : (match ((cfgR 3).st Cc).phase with | .awaitReply d _ => d == Bc | _ => false) = true := by decide
      rw [hp] at this; simpa using this
    subst hd; exact ⟨k, Or.inl hp⟩
  | _ => have : phaseTag (some (cfgR 3)) Cc = 4 := by decide
         simp [phaseTag, hp] at this

theorem B_alive_forever (t : Nat) : ((ρR.cfg t).st Bc).life = .alive := by
  show ((cfgR t).st Bc).life = .alive
  by_cases h : 6 ≤ t
  · rw [cfgR_tail t h]; decide
  · have : t < 6 := by omega
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem never_reply (j : Nat) (hj : 3 ≤ j) :
    ((ρR.cfg j).st Cc).lastCall ≠ some (((ρR.cfg 3).st Cc).waitId, .reply) := by
  show ((cfgR j).st Cc).lastCall ≠ some (((cfgR 3).st Cc).waitId, .reply)
  by_cases h : 6 ≤ j
  · rw [cfgR_tail j h]; decide
  · have : j < 6 := by omega
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `call_answered`'s Reply conjunct is false, given only `off_idle_reachable`. -/
theorem call_answered_reply_false (hoff : OffIdle) :
    ¬ (∀ (I : Impl) (_ : LocalOk I) (_ : GraphOk I.desc) (_ : Assumptions I)
        {N : Nat} (ρ : Run I N) (_ : Fair ρ) (i : Nat) (c d : InstId) (k : Cont)
        (_ : callWaiting ((ρ.cfg i).st c) d k),
        (∀ t, i ≤ t → ((ρ.cfg t).st d).life = .alive) →
          ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).lastCall = some (((ρ.cfg i).st c).waitId, .reply)) := by
  intro H
  obtain ⟨k, hw⟩ := waiting3
  obtain ⟨j, hj, hr⟩ := H callImpl call_local (checkBool_sound _ call_graph) callImpl_assumptions
    ρR (fairR hoff) 3 Cc Bc k hw (fun t _ => B_alive_forever t)
  exact never_reply j hj hr

/-! ## 4. `Deadlock` is discharged by `Fair.weak` alone for three of its four wait kinds.
No `GraphOk`, `LocalOk` or `Assumptions`: any `Impl`. -/

theorem proceed_wk (a : Actor) (k : Cont) : waitKind (proceed a k) = none := by
  unfold waitKind; rw [proceed_resumed]; unfold resumed; cases k.rest <;> rfl

theorem finishCall_wk (a : Actor) (k : Cont) (r : CallResult) : waitKind (finishCall a k r) = none := by
  unfold waitKind; rw [(finishCall_cont a k r).2.1, proceed_resumed]; unfold resumed
  cases (selectCall k r).rest <;> rfl

theorem timeout_wk (w w' : World) (s : InstId) (h : callTimeout w s = some w') :
    waitKind (w'.st s) = none := by
  unfold callTimeout at h
  by_cases hl : ((w.st s).life != .alive) = true
  · simp [hl] at h
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
    cases hp : (w.st s).phase with
    | awaitReply d k => rw [hp] at h; cases h; simp [setActor_self, finishCall_wk]
    | parked d c k =>
      cases c with
      | true => rw [hp] at h; cases h; simp [setActor_self, finishCall_wk]
      | false => rw [hp] at h; cases h
    | awaitPeer k => rw [hp] at h; cases h; simp [setActor_self, proceed_wk]
    | _ => rw [hp] at h; cases h

theorem finish_wk (I : Impl) (w w' : World) (s : InstId) (h : finishWait I w s = some w') :
    waitKind (w'.st s) = none := by
  unfold finishWait at h
  by_cases hl : (w.st s).life = .alive
  · simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte] at h
    cases hp : (w.st s).phase with
    | awaitEffect k => rw [hp] at h; cases h; simp [setActor_self, proceed_wk]
    | awaitPeer k => rw [hp] at h; cases h; simp [setActor_self, proceed_wk]
    | _ => rw [hp] at h; cases h
  · simp [hl] at h

theorem wk_finish_enabled (I : Impl) (w : World) (s : InstId) (hc : w.crashed = false)
    (hl : (w.st s).life = .alive)
    (h : waitKind (w.st s) = some .effect ∨ waitKind (w.st s) = some .peer) :
    Enabled I w (.finish s) := by
  unfold Enabled
  simp only [apply, hc, stepWorld]
  unfold finishWait
  simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte]
  unfold waitKind at h
  cases hp : (w.st s).phase with
  | awaitEffect k => simp
  | awaitPeer k => simp
  | parked d c k => rw [hp] at h; cases c <;> simp at h
  | _ => rw [hp] at h; simp at h

theorem wk_timeout_enabled (I : Impl) (w : World) (s d : InstId) (hc : w.crashed = false)
    (hl : (w.st s).life = .alive)
    (h : waitKind (w.st s) = some (.callReply d)) : Enabled I w (.callTimeout s) := by
  unfold Enabled
  simp only [apply, hc, stepWorld]
  unfold callTimeout
  simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  unfold waitKind at h
  cases hp : (w.st s).phase with
  | awaitReply d k => simp
  | parked d c k => rw [hp] at h; cases c <;> simp at h ⊢
  | _ => rw [hp] at h; simp at h

theorem stuck_later {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i j : Nat)
    (hS : Stuck ρ s i) (hj : i ≤ j) : waitKind ((ρ.cfg j).st s) = waitKind ((ρ.cfg i).st s) ∧
      waitKind ((ρ.cfg j).st s) ≠ none := by
  obtain ⟨e, ne⟩ := hS.2 j hj
  exact ⟨e.symm, e ▸ ne⟩

/-- Any fair run, any `Impl`: an actor never stays in an effect or peer wait. -/
theorem no_stuck_effect_peer {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (hS : Stuck ρ s i)
    (hk : waitKind ((ρ.cfg i).st s) = some .effect ∨ waitKind ((ρ.cfg i).st s) = some .peer)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False := by
  obtain ⟨j, hj, ha⟩ := hF.weak (.finish s) i rfl (fun j hj => by
    apply wk_finish_enabled I _ s ((apply_step I (ρ.act j) _ _ (ρ.valid j)).1) (hl j hj)
    rw [(stuck_later ρ s i j hS hj).1]; exact hk)
  have hv := ρ.valid j
  rw [ha] at hv
  have := finish_wk I _ _ s (by simpa [stepWorld] using (apply_step I (.finish s) _ _ hv).2)
  exact (stuck_later ρ s i (j + 1) hS (by omega)).2 this

/-- Any fair run, any `Impl`: a live caller never stays in a call wait. -/
theorem no_stuck_call {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s d : InstId) (i : Nat)
    (hS : Stuck ρ s i) (hk : waitKind ((ρ.cfg i).st s) = some (.callReply d))
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False := by
  obtain ⟨j, hj, ha⟩ := hF.weak (.callTimeout s) i rfl (fun j hj => by
    apply wk_timeout_enabled I _ s d ((apply_step I (ρ.act j) _ _ (ρ.valid j)).1) (hl j hj)
    rw [(stuck_later ρ s i j hS hj).1]; exact hk)
  have hv := ρ.valid j
  rw [ha] at hv
  have := timeout_wk _ _ s (by simpa [stepWorld] using (apply_step I (.callTimeout s) _ _ hv).2)
  exact (stuck_later ρ s i (j + 1) hS (by omega)).2 this

/-! ## 5. Smaller definitional facts. -/

/-- F9 positive: the peer timeout now runs `onTimeout`, the data result runs `rest`. -/
theorem peer_timeout_branch (w : World) (s : InstId) (k : Cont)
    (hl : (w.st s).life = .alive) (hp : (w.st s).phase = .awaitPeer k) :
    callTimeout w s = some (setActor w s (proceed (w.st s)
      { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout })) := by
  simp [callTimeout, hl, hp]


/-! ## R7: original R6a statements -/

/-- The original design (no per-outcome typestate): `outcome_blind` still holds. It is a
design choice now, not a limitation: `outcome_own_state` shows the other choice. -/
def callImpl0 : Impl := { callImpl with
  transitions := [tr "C" "idle" "Go" "wait" [.call "B" "Q" 0 [] []] false,
                  tr "C" "wait" "Go" "wait" [] false, tr "C" "miss" "Go" "miss" [] false,
                  tr "B" "idle" "Q" "idle" [.reply] true] }
theorem orig_outcome_blind_holds_by_choice :
    ((runAt callImpl0 0 raceActs).map fun w => ((w.st Cc).typestate, phaseTag (some w) Cc)) =
    ((runAt callImpl0 0 replyActs).map fun w => ((w.st Cc).typestate, phaseTag (some w) Cc)) := by decide

theorem orig_branch_label_uncounted_refuted :
    ¬ (prioLabels callImpl2 "C" = [] ∧ selfLabels [.call "B" "Q" 0 [] [.selfSchedule "late"]] = [] ∧
    replyCount [.peer [.reply]] = 0 ∧ hasTerminate [.peer [.terminate]] = false ∧
    sendsTo "B" [.peer [.send "B" "M" 0]] = 0) := by decide

end Deadlock.Helen7a
#print axioms Deadlock.Helen7a.orig_outcome_blind_holds_by_choice
#print axioms Deadlock.Helen7a.orig_branch_label_uncounted_refuted
