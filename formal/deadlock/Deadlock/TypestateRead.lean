import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

/-!
`proceed` writes `k.toState` when an arm is entered. The previous definition
left the field untouched on a nonempty arm. A step reads that field only for
an alive actor whose phase is idle or crashed: `tokenHold` in those two arms,
and `deliver` through `findDeliver`, which `receiveBulk` and `receivePrio`
call only for an idle actor. `maskActor` erases every other typestate.
`apply` commutes with that erasure, and the two `proceed`s agree after it.
-/

/-- `proceed` before a nonempty arm wrote its landing typestate. -/
def proceedLegacy (a : Actor) (k : Cont) : Actor :=
  match k.rest with
  | [] => { a with phase := .idle, typestate := k.toState }
  | _ => { a with phase := .run k }

/-- Phases whose typestate `tokenHold` reads. -/
def phaseAnchored : Phase → Bool
  | .idle | .crashed => true
  | _ => false

/-- The actor field is an input of a step only while the actor is alive and
idle or crashed. -/
def tyRead (a : Actor) : Bool :=
  a.life == .alive && phaseAnchored a.phase

/-- Erase a typestate no step reads. An alive idle or crashed actor keeps its field. -/
def maskActor (a : Actor) : Actor :=
  if tyRead a then a else { a with typestate := "" }

/-- Erase every unread typestate in `w`. -/
def maskWorld (w : World) : World :=
  { w with st := fun i => maskActor (w.st i) }

@[simp] theorem maskWorld_N (w : World) : (maskWorld w).N = w.N := rfl
@[simp] theorem maskWorld_roster (w : World) : (maskWorld w).roster = w.roster := rfl
@[simp] theorem maskWorld_nextIx (w : World) : (maskWorld w).nextIx = w.nextIx := rfl
@[simp] theorem maskWorld_nextKey (w : World) : (maskWorld w).nextKey = w.nextKey := rfl
@[simp] theorem maskWorld_cell (w : World) : (maskWorld w).cell = w.cell := rfl
@[simp] theorem maskWorld_observed (w : World) : (maskWorld w).observed = w.observed := rfl
@[simp] theorem maskWorld_failures (w : World) : (maskWorld w).failures = w.failures := rfl
@[simp] theorem maskWorld_crashed (w : World) : (maskWorld w).crashed = w.crashed := rfl
@[simp] theorem maskWorld_st (w : World) (i : InstId) : (maskWorld w).st i = maskActor (w.st i) := rfl

@[simp] theorem tyRead_spec (a : Actor) : tyRead a = (a.life == .alive && phaseAnchored a.phase) := rfl

theorem tyRead_typestate (a : Actor) (s : String) : tyRead { a with typestate := s } = tyRead a := by
  simp [tyRead]

@[simp] theorem maskActor_life (a : Actor) : (maskActor a).life = a.life := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_phase (a : Actor) : (maskActor a).phase = a.phase := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_box (a : Actor) : (maskActor a).box = a.box := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_prio (a : Actor) : (maskActor a).prio = a.prio := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_parked (a : Actor) : (maskActor a).parked = a.parked := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_tokens (a : Actor) : (maskActor a).tokens = a.tokens := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_nextMid (a : Actor) : (maskActor a).nextMid = a.nextMid := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_waitId (a : Actor) : (maskActor a).waitId = a.waitId := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_nextCall (a : Actor) : (maskActor a).nextCall = a.nextCall := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_oweId (a : Actor) : (maskActor a).oweId = a.oweId := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_lastCall (a : Actor) : (maskActor a).lastCall = a.lastCall := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_pending (a : Actor) : (maskActor a).pendingTombstone = a.pendingTombstone := by
  unfold maskActor; split <;> rfl

@[simp] theorem maskActor_parent (a : Actor) : (maskActor a).parent = a.parent := by
  unfold maskActor; split <;> rfl

theorem maskActor_keep (a : Actor) (h : tyRead a = true) : maskActor a = a := by
  unfold maskActor
  rw [h]
  simp

theorem maskActor_clear (a : Actor) (h : tyRead a = false) :
    maskActor a = { a with typestate := "" } := by
  unfold maskActor
  rw [h]
  simp

private theorem actor_eq {a b : Actor}
    (hl : a.life = b.life) (ht : a.typestate = b.typestate) (hp : a.phase = b.phase)
    (hbox : a.box = b.box) (hprio : a.prio = b.prio) (hpark : a.parked = b.parked)
    (htok : a.tokens = b.tokens) (hmid : a.nextMid = b.nextMid) (hwait : a.waitId = b.waitId)
    (hnext : a.nextCall = b.nextCall) (howe : a.oweId = b.oweId) (hlast : a.lastCall = b.lastCall)
    (hpend : a.pendingTombstone = b.pendingTombstone) (hpar : a.parent = b.parent) : a = b := by
  cases a
  cases b
  cases hl
  cases ht
  cases hp
  cases hbox
  cases hprio
  cases hpark
  cases htok
  cases hmid
  cases hwait
  cases hnext
  cases howe
  cases hlast
  cases hpend
  cases hpar
  rfl

/-- `b`'s payload on `a`'s life and phase. -/
def carried (a b : Actor) : Actor where
  life := a.life
  typestate := b.typestate
  phase := a.phase
  box := b.box
  prio := b.prio
  parked := b.parked
  tokens := b.tokens
  nextMid := b.nextMid
  waitId := b.waitId
  nextCall := b.nextCall
  oweId := b.oweId
  lastCall := b.lastCall
  pendingTombstone := b.pendingTombstone
  parent := b.parent

/-- An actor that agrees on life and phase has the same mask as the masked
source overwritten with its other fields. Typestate survives only when `tyRead`. -/
theorem mask_transport (a b : Actor) (hl : b.life = a.life) (hp : b.phase = a.phase) :
    maskActor b = maskActor (carried (maskActor a) b) := by
  have hs : tyRead b = tyRead a := by simp [tyRead, hl, hp]
  have hc : tyRead (carried (maskActor a) b) = tyRead a := by
    simp [tyRead, carried, maskActor_life, maskActor_phase]
  cases ht : tyRead a with
  | true =>
    rw [maskActor_keep b (hs.trans ht), maskActor_keep _ (hc.trans ht), maskActor_keep a ht]
    exact actor_eq hl rfl hp rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | false =>
    rw [maskActor_clear b (hs.trans ht), maskActor_clear _ (hc.trans ht), maskActor_clear a ht]
    exact actor_eq hl rfl hp rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem maskActor_idem (a : Actor) : maskActor (maskActor a) = maskActor a := by
  cases h : tyRead a with
  | true =>
    rw [maskActor_keep a h, maskActor_keep a h]
  | false =>
    rw [maskActor_clear a h]
    have h' : tyRead { a with typestate := "" } = false := by simpa [tyRead] using h
    rw [maskActor_clear _ h']

theorem maskWorld_idem (w : World) : maskWorld (maskWorld w) = maskWorld w := by
  unfold maskWorld
  simp only [maskWorld_st, maskActor_idem]

theorem mask_setActor (w : World) (id : InstId) (a : Actor) :
    maskWorld (setActor w id a) = setActor (maskWorld w) id (maskActor a) := by
  unfold maskWorld setActor
  congr 1
  funext i
  by_cases h : i = id <;> simp [h]

/-- Overwriting phase and typestate forgets a mask. -/
theorem mask_overwrite (a : Actor) (p : Phase) (t : String) :
    { maskActor a with phase := p, typestate := t } = { a with phase := p, typestate := t } := by
  unfold maskActor
  split <;> rfl

theorem proceed_erase (a : Actor) (k : Cont) : proceed (maskActor a) k = proceed a k := by
  cases hk : k.rest <;> simp [proceed, hk, mask_overwrite]

theorem proceed_legacy_masked (a : Actor) (k : Cont) :
    maskActor (proceed a k) = maskActor (proceedLegacy a k) := by
  cases hk : k.rest with
  | nil => simp [proceed, proceedLegacy, hk]
  | cons _ _ =>
    simp only [proceed, proceedLegacy, hk]
    have h1 : tyRead { a with phase := .run k, typestate := k.toState } = false := by
      simp [tyRead, phaseAnchored]
    have h2 : tyRead { a with phase := .run k } = false := by
      simp [tyRead, phaseAnchored]
    rw [maskActor_clear _ h1, maskActor_clear _ h2]

/-- `tokenHold` reads `typestate` only for an idle or crashed phase. -/
theorem tokenHold_running (D : Description) (template dst : String) (a : Actor) (s : String)
    (h : phaseAnchored a.phase = false) :
    tokenHold D template dst { a with typestate := s } = tokenHold D template dst a := by
  cases hph : a.phase with
  | idle => simp [hph, phaseAnchored] at h
  | crashed => simp [hph, phaseAnchored] at h
  | run k => simp [tokenHold, hph]
  | awaitEffect k => simp [tokenHold, hph]
  | awaitPeer k => simp [tokenHold, hph]
  | awaitReply dstK k => simp [tokenHold, hph]
  | parked dstK c k => cases c <;> simp [tokenHold, hph]

/-- A bulk receive that fires was an alive idle actor, so `deliver`'s
`findDeliver` read an idle typestate. -/
theorem receiveBulk_idle (I : Impl) (w w' : World) (id : InstId)
    (h : receiveBulk I w id = some w') :
    (w.st id).life = .alive ∧ (w.st id).phase = .idle := by
  unfold receiveBulk at h
  dsimp at h
  split at h
  · cases h
  · rename_i hready
    have hboth : decide ((w.st id).life ≠ .alive) = false ∧
        decide ((w.st id).phase ≠ .idle) = false := by
      simpa [Bool.or_eq_false_iff] using hready
    refine ⟨?_, ?_⟩
    · have hnot := decide_eq_false_iff_not.mp hboth.1
      simpa [ne_eq] using hnot
    · have hnot := decide_eq_false_iff_not.mp hboth.2
      simpa [ne_eq] using hnot

theorem bump_mask (a : Actor) (dst : String) (delta : Int) :
    maskActor (bumpToken a dst delta) = bumpToken (maskActor a) dst delta := by
  have hty : tyRead (bumpToken a dst delta) = tyRead a := by
    simp [tyRead, bumpToken]
  unfold maskActor
  rw [hty]
  cases ht : tyRead a with
  | true => simp [ht, bumpToken]
  | false => simp [ht, bumpToken]

theorem charge_mask (a : Actor) (dst : String) :
    maskActor (chargeSender a dst) = chargeSender (maskActor a) dst := by
  simp [chargeSender, bump_mask]

theorem issue_mask (a : Actor) :
    maskActor (issueCall a) = issueCall (maskActor a) := by
  have hty : tyRead (issueCall a) = tyRead a := by simp [tyRead, issueCall]
  unfold maskActor
  rw [hty]
  cases ht : tyRead a with
  | true => simp [ht, issueCall]
  | false => simp [ht, issueCall]

theorem addTokens_mask (a : Actor) (name : String) (n : Nat) :
    maskActor (addTokens a name n) = addTokens (maskActor a) name n := by
  have hty : tyRead (addTokens a name n) = tyRead a := by simp [tyRead, addTokens]
  unfold maskActor
  rw [hty]
  cases ht : tyRead a with
  | true => simp [ht, addTokens]
  | false => simp [ht, addTokens]

theorem finish_erase (a : Actor) (k : Cont) (r : CallResult) :
    finishCall (maskActor a) k r = finishCall a k r := by
  simp [finishCall, proceed_erase, maskActor_waitId, maskActor_nextCall]

theorem credit_mask (w : World) (name : String) (sender : InstId) :
    maskWorld (creditSender w name sender) = creditSender (maskWorld w) name sender := by
  simp [creditSender, mask_setActor, bump_mask]

theorem note_mask (w : World) (sender : InstId) (dst : String) :
    maskWorld (noteStale w sender dst) = noteStale (maskWorld w) sender dst := by
  simp [noteStale, maskWorld]

theorem setCell_mask (w : World) (dst label : String) (c : Cell) :
    maskWorld (setCell w dst label c) = setCell (maskWorld w) dst label c := by
  simp [setCell, maskWorld]

theorem setObserved_mask (w : World) (id : InstId) (label : String) (v : Nat) :
    maskWorld (setObserved w id label v) = setObserved (maskWorld w) id label v := by
  simp [setObserved, maskWorld]

theorem readCells_mask (D : Description) (w : World) (id : InstId) :
    maskWorld (readCells D w id) = readCells D (maskWorld w) id := by
  unfold readCells
  generalize cellLabels D (tname id) = labs
  induction labs generalizing w with
  | nil => simp
  | cons label labs ih =>
    simp only [List.foldl_cons]
    have hstep : maskWorld (setObserved (setCell w (tname id) label
        { (w.cell (tname id) label) with dirty := false }) id label
        (w.cell (tname id) label).value) =
      setObserved (setCell (maskWorld w) (tname id) label
        { ((maskWorld w).cell (tname id) label) with dirty := false }) id label
        ((maskWorld w).cell (tname id) label).value := by
      simp [setCell_mask, setObserved_mask, maskWorld_cell]
    rw [← hstep]
    exact ih _

theorem findLive_mask (w : World) (name : String) (key : Nat) :
    findLive (maskWorld w) name key = findLive w name key := by
  simp only [findLive, maskWorld_roster]
  congr 1
  funext id
  cases id with
  | core _ => rfl
  | peer n k g => simp [maskActor_life]

theorem maxGen_mask (w : World) (name : String) (key : Nat) :
    maxGen (maskWorld w) name key = maxGen w name key := by
  simp [maxGen, maskWorld_roster]

theorem isChild_mask (w : World) (parent child : InstId) :
    isChild (maskWorld w) parent child = isChild w parent child := by
  simp [isChild, maskActor_parent]

theorem crashActor_mask (a : Actor) :
    maskActor (crashActor a) = maskActor (crashActor (maskActor a)) := by
  cases hlive : (a.life == .alive || a.life == .shuttingDown) with
  | true =>
    have hlive' : ((maskActor a).life == .alive || (maskActor a).life == .shuttingDown) = true := by
      simpa [maskActor_life] using hlive
    unfold crashActor
    rw [hlive, hlive']
    rw [if_pos rfl, if_pos rfl]
    have hd : tyRead { a with life := .dead, phase := .crashed } = false := by
      simp [tyRead, phaseAnchored]
    have hd' : tyRead { maskActor a with life := .dead, phase := .crashed } = false := by
      simp [tyRead, phaseAnchored]
    rw [maskActor_clear _ hd, maskActor_clear _ hd']
    cases ht : tyRead a with
    | true => rw [maskActor_keep a ht]
    | false => rw [maskActor_clear a ht]
  | false =>
    have hlive' : ((maskActor a).life == .alive || (maskActor a).life == .shuttingDown) = false := by
      simpa [maskActor_life] using hlive
    unfold crashActor
    rw [hlive, hlive']
    rw [if_neg (by simp), if_neg (by simp)]
    exact (maskActor_idem a).symm

private theorem world_eq {w v : World}
    (hN : w.N = v.N) (hr : w.roster = v.roster) (hix : w.nextIx = v.nextIx)
    (hk : w.nextKey = v.nextKey) (hs : ∀ i, w.st i = v.st i) (hc : w.cell = v.cell)
    (ho : w.observed = v.observed) (hf : w.failures = v.failures) (hcr : w.crashed = v.crashed) :
    w = v := by
  have hst : w.st = v.st := funext hs
  cases w
  cases v
  cases hN
  cases hr
  cases hix
  cases hk
  cases hst
  cases hc
  cases ho
  cases hf
  cases hcr
  rfl

theorem crashWorld_st (w : World) (i : InstId) :
    (crashWorld w).st i = if decide (i ∈ w.roster) then crashActor (w.st i) else w.st i := by
  simp [crashWorld]

theorem crashWorld_mask (w : World) :
    maskWorld (crashWorld w) = maskWorld (crashWorld (maskWorld w)) := by
  refine world_eq rfl rfl rfl rfl ?_ rfl rfl rfl rfl
  intro i
  rw [maskWorld_st, maskWorld_st, crashWorld_st, crashWorld_st, maskWorld_roster]
  simp only [maskWorld_st]
  by_cases hmem : decide (i ∈ w.roster) = true
  · rw [hmem, if_pos rfl, if_pos rfl]
    exact crashActor_mask _
  · have hnot : decide (i ∈ w.roster) = false := by
      cases h : decide (i ∈ w.roster) with
      | true => exact absurd h hmem
      | false => rfl
    rw [hnot, if_neg (by simp), if_neg (by simp)]
    exact (maskActor_idem _).symm

theorem foldl_mask {α : Type} (xs : List α) (f : World → α → World) (w : World)
    (h : ∀ v x, maskWorld (f v x) = maskWorld (f (maskWorld v) x)) :
    maskWorld (xs.foldl f w) = maskWorld (xs.foldl f (maskWorld w)) := by
  induction xs generalizing w with
  | nil => simp [maskWorld_idem]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (f w x), ih (f (maskWorld w) x), h w x]

theorem budgetHolder_mask (w : World) (sender : InstId) :
    budgetHolder (maskWorld w) sender = budgetHolder w sender := by
  cases sender with
  | core _ => rfl
  | peer name key _ => simp [budgetHolder, findLive_mask]

theorem creditLive_mask (w : World) (name : String) (sender : InstId) :
    maskWorld (creditLive w name sender) = creditLive (maskWorld w) name sender := by
  simp [creditLive, budgetHolder_mask, credit_mask]

theorem refundMsgs_mask (w : World) (name : String) (ms : List Msg) :
    maskWorld (refundMsgs w name ms) = maskWorld (refundMsgs (maskWorld w) name ms) := by
  unfold refundMsgs
  exact foldl_mask ms (fun v m => creditLive v name m.sender) w fun v m => by
    rw [creditLive_mask, creditLive_mask, maskWorld_idem]

theorem refundParked_mask (w : World) (name : String) (ps : List Parked) :
    maskWorld (refundParked w name ps) = maskWorld (refundParked (maskWorld w) name ps) := by
  unfold refundParked
  exact foldl_mask ps (fun v p => creditLive v name p.msg.sender) w fun v p => by
    rw [creditLive_mask, creditLive_mask, maskWorld_idem]

/-- A phase that is not idle or crashed does not keep its typestate under the mask. -/
theorem mask_retarget (a : Actor) (p : Phase) (hp : phaseAnchored p = false) :
    maskActor { a with phase := p } = maskActor { maskActor a with phase := p } := by
  have h1 : tyRead { a with phase := p } = false := by simp [tyRead, hp]
  have h2 : tyRead { maskActor a with phase := p } = false := by simp [tyRead, hp]
  rw [maskActor_clear _ h1, maskActor_clear _ h2]
  cases ht : tyRead a with
  | true => rw [maskActor_keep a ht]
  | false => rw [maskActor_clear a ht]

theorem mask_set_proceed (w : World) (id : InstId) (a : Actor) (k : Cont) :
    maskWorld (setActor w id (proceed a k)) =
      maskWorld (setActor (maskWorld w) id (proceed (maskActor a) k)) := by
  rw [proceed_erase a k, mask_setActor, mask_setActor, maskWorld_idem]

theorem mask_set_phase (w : World) (id : InstId) (a : Actor) (p : Phase)
    (hp : phaseAnchored p = false) :
    maskWorld (setActor w id { a with phase := p }) =
      maskWorld (setActor (maskWorld w) id { maskActor a with phase := p }) := by
  rw [mask_setActor, mask_setActor, maskWorld_idem, mask_retarget a p hp]

theorem resume_mask (a : Actor) (c : Bool) (dst : InstId) :
    maskActor (resumeSender a c dst) = maskActor (resumeSender (maskActor a) c dst) := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases c with
    | false => simp [resumeSender, hph, proceed_erase, maskActor_phase]
    | true =>
      simp only [resumeSender, hph, maskActor_phase]
      exact mask_retarget a (.awaitReply dst k) rfl
  | idle => simp [resumeSender, hph, maskActor_idem, maskActor_phase]
  | run k => simp [resumeSender, hph, maskActor_idem, maskActor_phase]
  | awaitReply _ k => simp [resumeSender, hph, maskActor_idem, maskActor_phase]
  | awaitEffect k => simp [resumeSender, hph, maskActor_idem, maskActor_phase]
  | awaitPeer k => simp [resumeSender, hph, maskActor_idem, maskActor_phase]
  | crashed => simp [resumeSender, hph, maskActor_idem, maskActor_phase]

theorem mask_queue (a : Actor) (ms : List Msg) (ps : List Parked) :
    maskActor { a with box := ms, parked := ps } = { maskActor a with box := ms, parked := ps } := by
  have hs : tyRead { a with box := ms, parked := ps } = tyRead a := by simp [tyRead]
  cases ht : tyRead a with
  | true => rw [maskActor_keep _ (hs.trans ht), maskActor_keep a ht]
  | false => rw [maskActor_clear _ (hs.trans ht), maskActor_clear a ht]

theorem mask_repark (a : Actor) (ps : List Parked) :
    maskActor { a with parked := ps } = { maskActor a with parked := ps } := by
  have hs : tyRead { a with parked := ps } = tyRead a := by simp [tyRead]
  cases ht : tyRead a with
  | true => rw [maskActor_keep _ (hs.trans ht), maskActor_keep a ht]
  | false => rw [maskActor_clear _ (hs.trans ht), maskActor_clear a ht]

theorem releaseStep_mask (w : World) (id : InstId) (p : Parked) :
    maskWorld (if p.isCall || p.sender = id then w
        else setActor w p.sender (resumeSender (w.st p.sender) false id)) =
      maskWorld (if p.isCall || p.sender = id then (maskWorld w)
        else setActor (maskWorld w) p.sender
          (resumeSender ((maskWorld w).st p.sender) false id)) := by
  cases hskip : (p.isCall || decide (p.sender = id)) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    exact (maskWorld_idem _).symm
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    rw [mask_setActor, mask_setActor, maskWorld_idem, maskWorld_st]
    exact congrArg (setActor (maskWorld w) p.sender) (resume_mask _ false id)

theorem releaseParked_mask (w : World) (id : InstId) (ps : List Parked) :
    maskWorld (releaseParked w id ps) = maskWorld (releaseParked (maskWorld w) id ps) := by
  unfold releaseParked
  exact foldl_mask ps (fun v p =>
      if p.isCall || p.sender = id then v
      else setActor v p.sender (resumeSender (v.st p.sender) false id)) w
    fun v p => releaseStep_mask v id p

/-- One host of `releaseOutbound`. Typestate is not consulted: the branch is the
parked list, and both writes keep every field the mask reads. -/
def outboundHost (w : World) (dead host : InstId) : World :=
  if host == dead then w
  else
    let dropped := (w.st host).parked.filter fun p => p.sender == dead
    if dropped.isEmpty then w
    else
      let w := setActor w host
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      setActor w dead (addTokens (w.st dead) (tname host) dropped.length)

theorem outboundHost_eq (w : World) (dead : InstId) :
    releaseOutbound w dead = w.roster.foldl (fun v host => outboundHost v dead host) w := by
  simp [releaseOutbound, outboundHost]

theorem outboundHost_mask (w : World) (dead host : InstId) :
    maskWorld (outboundHost w dead host) = maskWorld (outboundHost (maskWorld w) dead host) := by
  unfold outboundHost
  cases hhost : (host == dead) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    exact (maskWorld_idem _).symm
  | false =>
    rw [if_neg (by simp)]
    conv => rhs; rw [if_neg (by simp)]
    have hpark : ((maskWorld w).st host).parked = (w.st host).parked := by
      simp [maskActor_parked]
    simp only [hpark]
    cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty with
    | true =>
      rw [if_pos rfl]
      conv => rhs; rw [if_pos rfl]
      exact (maskWorld_idem _).symm
    | false =>
      rw [if_neg (by simp)]
      conv => rhs; rw [if_neg (by simp)]
      have hne : host ≠ dead := by simpa [beq_iff_eq] using hhost
      -- Left-hand side, down to one masked write.
      rw [mask_setActor, mask_setActor, addTokens_mask]
      rw [mask_repark (w.st host) ((w.st host).parked.filter fun p => p.sender != dead)]
      rw [setActor_other _ host dead _ hne.symm]
      -- Right-hand side keeps the actor that was already masked.
      conv =>
        rhs
        rw [mask_setActor, addTokens_mask]
        rw [setActor_other _ host dead _ hne.symm]
      simp only [maskWorld_st, maskActor_idem]
      have hfix :
          maskActor { maskActor (w.st host) with
              parked := (w.st host).parked.filter fun p => p.sender != dead } =
            { maskActor (w.st host) with
              parked := (w.st host).parked.filter fun p => p.sender != dead } := by
        rw [← mask_repark (w.st host) ((w.st host).parked.filter fun p => p.sender != dead)]
        exact maskActor_idem _
      rw [mask_setActor, maskWorld_idem, hfix]

theorem releaseOutbound_mask (w : World) (dead : InstId) :
    maskWorld (releaseOutbound w dead) = maskWorld (releaseOutbound (maskWorld w) dead) := by
  rw [outboundHost_eq, outboundHost_eq]
  exact foldl_mask w.roster (fun v host => outboundHost v dead host) w
    fun v host => outboundHost_mask v dead host

theorem mask_prio_mid (a : Actor) (msg : Msg) :
    maskActor { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 } =
      maskActor { maskActor a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 } := by
  have hs : tyRead { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 } = tyRead a := by
    simp [tyRead]
  have hs2 : tyRead { maskActor a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 } =
      tyRead a := by simp [tyRead, maskActor_life, maskActor_phase]
  cases ht : tyRead a with
  | true =>
    rw [maskActor_keep _ (hs.trans ht), maskActor_keep _ (hs2.trans ht), maskActor_keep a ht]
  | false =>
    rw [maskActor_clear _ (hs.trans ht), maskActor_clear _ (hs2.trans ht), maskActor_clear a ht]

theorem offerPrio_mask (D : Description) (w : World) (host : InstId) (msg : Msg) :
    maskWorld (offerPrio D w host msg) = maskWorld (offerPrio D (maskWorld w) host msg) := by
  unfold offerPrio
  simp only [maskWorld_st, maskWorld_N, maskActor_prio, maskActor_nextMid]
  cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    exact crashWorld_mask w
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    rw [mask_setActor, mask_setActor, maskWorld_idem]
    exact congrArg (setActor (maskWorld w) host) (mask_prio_mid (w.st host) msg)

theorem tryWake_mask (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) :
    maskWorld (tryWake D w dstId label writer) =
      maskWorld (tryWake D (maskWorld w) dstId label writer) := by
  unfold tryWake
  simp only [maskWorld_st, maskActor_life, maskActor_prio, maskActor_nextMid]
  cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any fun p => p.label == label) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    exact (maskWorld_idem _).symm
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    exact offerPrio_mask D w dstId _

theorem wakeReaders_mask (D : Description) (w : World) (dst label : String) (writer : InstId) :
    maskWorld (wakeReaders D w dst label writer) =
      maskWorld (wakeReaders D (maskWorld w) dst label writer) := by
  unfold wakeReaders readersOf
  simp only [maskWorld_roster]
  have hreaders :
      (w.roster.filter fun id => tname id == dst && ((maskWorld w).st id).life == .alive) =
        (w.roster.filter fun id => tname id == dst && (w.st id).life == .alive) := by
    congr 1
    funext id
    simp [maskActor_life]
  conv => rhs; rw [hreaders]
  refine foldl_mask (w.roster.filter fun id => tname id == dst && (w.st id).life == .alive)
    (fun v id => tryWake D v id label writer) w ?_
  intro v id
  exact tryWake_mask D v id label writer

/-- Marking shutdown lands in a phase the mask does not read, so the previous
typestate is erased on both sides. -/
theorem mask_shutdown (a : Actor) :
    maskActor { a with life := .shuttingDown, phase := .idle } =
      maskActor { maskActor a with life := .shuttingDown, phase := .idle } := by
  have hs : tyRead { a with life := .shuttingDown, phase := .idle } = false := by simp [tyRead]
  have hs2 : tyRead { maskActor a with life := .shuttingDown, phase := .idle } = false := by
    simp [tyRead]
  rw [maskActor_clear _ hs, maskActor_clear _ hs2]
  cases ht : tyRead a with
  | true => rw [maskActor_keep a ht]
  | false => rw [maskActor_clear a ht]

theorem markShutdown_mask (w : World) (id : InstId) :
    maskWorld (markShutdown w id) = maskWorld (markShutdown (maskWorld w) id) := by
  unfold markShutdown
  simp only [maskWorld_st, maskActor_life]
  cases hlive : ((w.st id).life == .alive) with
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    exact (maskWorld_idem _).symm
  | true =>
    rw [if_pos rfl, if_pos rfl]
    rw [releaseOutbound_mask, mask_setActor]
    conv =>
      rhs
      rw [releaseOutbound_mask, mask_setActor, maskWorld_idem]
    exact congrArg (fun a => maskWorld (releaseOutbound (setActor (maskWorld w) id a) id))
      (mask_shutdown (w.st id))

theorem mask_arm (a : Actor) :
    maskActor { a with pendingTombstone := true } =
      maskActor { maskActor a with pendingTombstone := true } := by
  have hs : tyRead { a with pendingTombstone := true } = tyRead a := by simp [tyRead]
  have hs2 : tyRead { maskActor a with pendingTombstone := true } = tyRead a := by
    simp [tyRead, maskActor_life, maskActor_phase]
  cases ht : tyRead a with
  | true =>
    rw [maskActor_keep _ (hs.trans ht), maskActor_keep _ (hs2.trans ht), maskActor_keep a ht]
  | false =>
    rw [maskActor_clear _ (hs.trans ht), maskActor_clear _ (hs2.trans ht), maskActor_clear a ht]

theorem armTombstone_mask (w : World) (id : InstId) :
    maskWorld (armTombstone w id) = maskWorld (armTombstone (maskWorld w) id) := by
  unfold armTombstone
  rw [mask_setActor, mask_setActor, maskWorld_idem, maskWorld_st]
  exact congrArg (setActor (maskWorld w) id) (mask_arm (w.st id))

def killed (a : Actor) : Actor :=
  { a with life := .dead, phase := .idle, box := [], prio := [], parked := [] }

theorem mask_killed (a : Actor) :
    maskActor (killed a) = maskActor (killed (maskActor a)) := by
  have h1 : tyRead (killed a) = false := by simp [tyRead, killed]
  have h2 : tyRead (killed (maskActor a)) = false := by simp [tyRead, killed]
  rw [maskActor_clear _ h1, maskActor_clear _ h2]
  cases ht : tyRead a with
  | true => rw [maskActor_keep a ht]
  | false =>
    rw [maskActor_clear a ht]
    simp [killed]

def sealPipe (D : Description) (w : World) (id : InstId) (box : List Msg) (ps : List Parked) : World :=
  releaseOutbound (refundParked (refundMsgs (readCells D w id) (tname id) box) (tname id) ps) id

theorem sealPipe_mask (D : Description) (w : World) (id : InstId) (box : List Msg) (ps : List Parked) :
    maskWorld (sealPipe D w id box ps) = maskWorld (sealPipe D (maskWorld w) id box ps) := by
  unfold sealPipe
  rw [releaseOutbound_mask, refundParked_mask, refundMsgs_mask, readCells_mask]
  rw [← refundParked_mask, ← releaseOutbound_mask]

theorem releaseWorld_mask (D : Description) (w : World) (id : InstId) (a : Actor) :
    maskWorld (releaseWorld D w id a) =
      maskWorld (releaseWorld D (maskWorld w) id (maskActor a)) := by
  have hpipe : releaseWorld D w id a =
      releaseParked (setActor (sealPipe D w id a.box a.parked) id
        (killed ((sealPipe D w id a.box a.parked).st id))) id a.parked := by
    simp [releaseWorld, sealPipe, killed]
  have hpipe' : releaseWorld D (maskWorld w) id (maskActor a) =
      releaseParked (setActor (sealPipe D (maskWorld w) id a.box a.parked) id
        (killed ((sealPipe D (maskWorld w) id a.box a.parked).st id))) id a.parked := by
    simp [releaseWorld, sealPipe, killed, maskActor_box, maskActor_parked]
  rw [hpipe, hpipe']
  have hseal := sealPipe_mask D w id a.box a.parked
  conv =>
    lhs
    rw [releaseParked_mask, mask_setActor, hseal]
  conv =>
    rhs
    rw [releaseParked_mask, mask_setActor]
  -- `seal w` and `seal (mask w)` agree after the mask, so the dead actor does too.
  have hk :
      maskActor (killed ((sealPipe D w id a.box a.parked).st id)) =
        maskActor (killed ((sealPipe D (maskWorld w) id a.box a.parked).st id)) := by
    calc
      maskActor (killed ((sealPipe D w id a.box a.parked).st id))
        = maskActor (killed (maskActor ((sealPipe D w id a.box a.parked).st id))) := mask_killed _
      _ = maskActor (killed ((maskWorld (sealPipe D w id a.box a.parked)).st id)) := by
          rw [maskWorld_st]
      _ = maskActor (killed ((maskWorld (sealPipe D (maskWorld w) id a.box a.parked)).st id)) := by
          rw [hseal]
      _ = maskActor (killed (maskActor ((sealPipe D (maskWorld w) id a.box a.parked).st id))) := by
          rw [maskWorld_st]
      _ = maskActor (killed ((sealPipe D (maskWorld w) id a.box a.parked).st id)) := (mask_killed _).symm
  rw [hk]

theorem enqueueTombstone_mask (D : Description) (w : World) (child : InstId) :
    maskWorld (enqueueTombstone D w child) = maskWorld (enqueueTombstone D (maskWorld w) child) := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none =>
    have hpar' : ((maskWorld w).st child).parent = none := by
      rw [maskWorld_st, maskActor_parent, hpar]
    simp only [hpar, hpar']
    exact (maskWorld_idem _).symm
  | some parent =>
    have hpar' : ((maskWorld w).st child).parent = some parent := by
      rw [maskWorld_st, maskActor_parent, hpar]
    have hlife : ((maskWorld w).st parent).life = (w.st parent).life := by
      rw [maskWorld_st, maskActor_life]
    simp only [hpar, hpar', hlife]
    cases hlive : ((w.st parent).life != .alive) with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      exact (maskWorld_idem _).symm
    | false =>
      rw [if_neg (by simp)]
      conv => rhs; rw [if_neg (by simp)]
      have hmsg : tombstoneMsg D ((maskWorld w).st parent) child =
          tombstoneMsg D (w.st parent) child := by
        rw [maskWorld_st]
        simp [tombstoneMsg, maskActor_nextMid]
      simp only [hmsg]
      cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") with
      | true =>
        rw [if_pos rfl]
        conv => rhs; rw [if_pos rfl]
        exact crashWorld_mask _
      | false =>
        rw [if_neg (by simp)]
        conv => rhs; rw [if_neg (by simp)]
        exact offerPrio_mask D w parent (tombstoneMsg D (w.st parent) child)

theorem sealActor_mask (D : Description) (w : World) (id : InstId) (a : Actor) :
    maskWorld (sealActor D w id a) = maskWorld (sealActor D (maskWorld w) id (maskActor a)) := by
  unfold sealActor
  simp only [maskActor_pending]
  cases hpend : a.pendingTombstone with
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    exact releaseWorld_mask D w id a
  | true =>
    rw [if_pos rfl, if_pos rfl]
    rw [enqueueTombstone_mask, releaseWorld_mask, ← enqueueTombstone_mask]

theorem shutdownActor_mask (D : Description) (w : World) (id : InstId) :
    maskWorld (shutdownActor D w id) = maskWorld (shutdownActor D (maskWorld w) id) := by
  unfold shutdownActor
  simp only [maskWorld_st, maskActor_life]
  cases hlive : ((w.st id).life == .alive) with
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    exact markShutdown_mask w id
  | true =>
    rw [if_pos rfl, if_pos rfl]
    rw [armTombstone_mask, markShutdown_mask, ← armTombstone_mask]

theorem sealBranch_mask (fuel : Nat) (D : Description) (w : World) (id : InstId) :
    maskWorld (sealBranch fuel D w id) = maskWorld (sealBranch fuel D (maskWorld w) id) := by
  induction fuel generalizing w id with
  | zero => simp [sealBranch, maskWorld_idem]
  | succ n ih =>
    unfold sealBranch
    dsimp only
    have hstep : ∀ v child,
        maskWorld (if isChild v id child then sealBranch n D v child else v) =
          maskWorld (if isChild (maskWorld v) id child then sealBranch n D (maskWorld v) child
            else maskWorld v) := by
      intro v child
      have hc : isChild (maskWorld v) id child = isChild v id child := isChild_mask v id child
      cases hch : isChild v id child with
      | true =>
        simp only [hch, hc]
        rw [if_pos trivial, if_pos trivial]
        exact ih v child
      | false =>
        simp only [hch, hc]
        rw [if_neg (by simp), if_neg (by simp)]
        exact (maskWorld_idem _).symm
    have hfold := foldl_mask w.roster
      (fun acc child => if isChild acc id child then sealBranch n D acc child else acc) w hstep
    conv => rhs; rw [maskWorld_roster]
    generalize hse : (w.roster.foldl (fun acc child =>
      if isChild acc id child then sealBranch n D acc child else acc) w) = sealed
    generalize hsm : (w.roster.foldl (fun acc child =>
      if isChild acc id child then sealBranch n D acc child else acc) (maskWorld w)) = sealedM
    have hseal : maskWorld sealed = maskWorld sealedM := by rw [← hse, ← hsm]; exact hfold
    have hlife : (sealedM.st id).life = (sealed.st id).life := by
      have hL : ∀ u : World, (u.st id).life = ((maskWorld u).st id).life := by intro u; simp
      rw [hL sealedM, hL sealed, hseal]
    rw [hlife]
    split
    · rename_i hgo
      have hact : maskActor (sealed.st id) = maskActor (sealedM.st id) := by
        have hs := congrArg (fun u : World => u.st id) hseal
        simpa [maskWorld_st] using hs
      calc
        maskWorld (releaseWorld D sealed id (sealed.st id))
          = maskWorld (releaseWorld D (maskWorld sealed) id (maskActor (sealed.st id))) :=
            releaseWorld_mask D sealed id (sealed.st id)
        _ = maskWorld (releaseWorld D (maskWorld sealedM) id (maskActor (sealedM.st id))) := by
            rw [hseal, hact]
        _ = maskWorld (releaseWorld D sealedM id (sealedM.st id)) :=
            (releaseWorld_mask D sealedM id (sealedM.st id)).symm
    · exact hseal

theorem dropDescendants_mask (D : Description) (w : World) (id : InstId) :
    maskWorld (dropDescendants D w id) = maskWorld (dropDescendants D (maskWorld w) id) := by
  unfold dropDescendants
  have hlen : (maskWorld w).roster.length = w.roster.length := by simp
  simp only [hlen]
  conv => rhs; rw [maskWorld_roster]
  refine foldl_mask w.roster (fun acc child =>
      if isChild acc id child then sealBranch w.roster.length D acc child else acc) w ?_
  intro v child
  have hc : isChild (maskWorld v) id child = isChild v id child := isChild_mask v id child
  cases hch : isChild v id child with
  | true =>
    simp only [hch, hc]
    rw [if_pos trivial, if_pos trivial]
    exact sealBranch_mask _ D v child
  | false =>
    simp only [hch, hc]
    rw [if_neg (by simp), if_neg (by simp)]
    exact (maskWorld_idem _).symm

theorem terminateStage_mask (D : Description) (w : World) (id : InstId) (a : Actor) :
    maskWorld (terminateStage D w id a) =
      maskWorld (terminateStage D (maskWorld w) id (maskActor a)) := by
  unfold terminateStage
  dsimp only
  rw [shutdownActor_mask, dropDescendants_mask, ← shutdownActor_mask]

theorem abortChildren_mask (D : Description) (w : World) (parent : InstId) :
    maskWorld (abortChildren D w parent) = maskWorld (abortChildren D (maskWorld w) parent) := by
  unfold abortChildren
  conv => rhs; rw [maskWorld_roster]
  refine foldl_mask w.roster (fun acc child =>
      if isChild acc parent child && (acc.st child).life == .alive then
        shutdownActor D (dropDescendants D acc child) child
      else acc) w ?_
  intro v child
  have hc : isChild (maskWorld v) parent child = isChild v parent child := isChild_mask v parent child
  have hl : ((maskWorld v).st child).life = (v.st child).life := by simp
  simp only [hc, hl]
  split
  · rw [shutdownActor_mask, dropDescendants_mask, ← shutdownActor_mask]
  · exact (maskWorld_idem _).symm

theorem newer_mask (w : World) (m : Msg) :
    newerGeneration (maskWorld w) m = newerGeneration w m := by
  simp [newerGeneration, maskWorld_roster, maskWorld_st, maskActor_parent]

theorem readCells_roster_here (D : Description) (w : World) (id : InstId) :
    (readCells D w id).roster = w.roster := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem newer_cells (D : Description) (u : World) (id : InstId) (m : Msg) :
    newerGeneration (readCells D u id) m = newerGeneration u m := by
  simp [newerGeneration, readCells_roster_here, cellsSt]

/-- `deliver` reads typestate only to choose the transition. `receiveBulk` and
`receivePrio` call it for an idle actor, whose typestate the mask keeps. -/
theorem deliver_idle_mask (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (hl : a.life = .alive) (hp : a.phase = .idle) :
    (deliver I w id a m).map (fun p => (maskWorld p.1, maskActor p.2)) =
      (deliver I (maskWorld w) id a m).map (fun p => (maskWorld p.1, maskActor p.2)) := by
  have hcells : maskWorld (readCells I.desc w id) = readCells I.desc (maskWorld w) id :=
    readCells_mask I.desc w id
  have hfix : maskWorld (readCells I.desc (maskWorld w) id) = readCells I.desc (maskWorld w) id := by
    rw [readCells_mask, maskWorld_idem]
  unfold deliver
  simp only [newer_cells, newer_mask, hl, ne_eq]
  rw [if_neg (by simp)]
  conv => rhs; rw [if_neg (by simp)]
  cases hnewb : (m.tombstone && newerGeneration w m) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    simp only [Option.map]
    rw [hcells, hfix]
  | false =>
    rw [if_neg (by simp)]
    conv => rhs; rw [if_neg (by simp)]
    cases htr : findDeliver I (tname id) a.typestate m with
    | none =>
      simp only [htr]
      cases hkeep : (m.callFrom.isSome || m.tombstone) with
      | true =>
        rw [if_pos rfl, if_pos rfl]
      | false =>
        rw [if_neg (by simp)]
        conv => rhs; rw [if_neg (by simp)]
        simp only [Option.map]
        rw [hcells, hfix]
    | some tr =>
      simp only [htr]
      cases hacc : (m.callFrom.isSome && !tr.acceptsCall) with
      | true =>
        rw [if_pos rfl, if_pos rfl]
      | false =>
        rw [if_neg (by simp)]
        conv => rhs; rw [if_neg (by simp)]
        cases hempty : tr.program.isEmpty with
        | true =>
          rw [if_pos rfl]
          simp only [Option.map]
          rw [hcells, hfix]
        | false =>
          rw [if_neg (by simp)]
          simp only [Option.map]
          rw [hcells, hfix]

theorem receiveBulk_mask (I : Impl) (w : World) (id : InstId) :
    (receiveBulk I w id).map maskWorld = (receiveBulk I (maskWorld w) id).map maskWorld := by
  unfold receiveBulk
  dsimp only
  have hl : ((maskWorld w).st id).life = (w.st id).life := by simp
  have hp : ((maskWorld w).st id).phase = (w.st id).phase := by simp
  have hbox : ((maskWorld w).st id).box = (w.st id).box := by simp
  have hpark : ((maskWorld w).st id).parked = (w.st id).parked := by simp
  simp only [hl, hp, hbox, hpark]
  cases hgo : ((w.st id).life ≠ .alive || (w.st id).phase ≠ .idle) with
  | true =>
    rw [if_pos rfl, if_pos rfl]
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    have hlive : (w.st id).life = .alive := by
      simp only [Bool.or_eq_false_iff, bne, Bool.not_eq_true'] at hgo
      simpa using hgo.1
    have hidle : (w.st id).phase = .idle := by
      simp only [Bool.or_eq_false_iff, bne, Bool.not_eq_true'] at hgo
      simpa using hgo.2
    have hty : tyRead (w.st id) = true := by
      simp [tyRead, phaseAnchored, hlive, hidle]
    simp only [maskWorld_st, maskActor_keep _ hty]
    split
    · next m ms hbox hpark =>
      let aRecv : Actor :=
        { life := (w.st id).life, typestate := (w.st id).typestate, phase := (w.st id).phase, box := ms,
          prio := (w.st id).prio, parked := (w.st id).parked, tokens := (w.st id).tokens,
          nextMid := (w.st id).nextMid, waitId := (w.st id).waitId, nextCall := (w.st id).nextCall,
          oweId := (w.st id).oweId, lastCall := (w.st id).lastCall,
          pendingTombstone := (w.st id).pendingTombstone, parent := (w.st id).parent }
      have hlA : aRecv.life = .alive := by simp [aRecv, hlive]
      have hpA : aRecv.phase = .idle := by simp [aRecv, hidle]
      have hd := deliver_idle_mask I w id aRecv m hlA hpA
      cases h1 : deliver I w id aRecv m with
      | none =>
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => rfl
        | some _ => simp [h1, h2] at hd
      | some pair =>
        obtain ⟨w1, a1⟩ := pair
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => simp [h1, h2] at hd
        | some pair2 =>
          obtain ⟨w2, a2⟩ := pair2
          simp [h1, h2, creditLive_mask, mask_setActor] at hd ⊢
          simp [hd]
    · next m ms p ps hbox hpark =>
      let aRecv : Actor :=
        { life := (w.st id).life, typestate := (w.st id).typestate, phase := (w.st id).phase, box := ms,
          prio := (w.st id).prio, parked := (w.st id).parked, tokens := (w.st id).tokens,
          nextMid := (w.st id).nextMid, waitId := (w.st id).waitId, nextCall := (w.st id).nextCall,
          oweId := (w.st id).oweId, lastCall := (w.st id).lastCall,
          pendingTombstone := (w.st id).pendingTombstone, parent := (w.st id).parent }
      have hlA : aRecv.life = .alive := by simp [aRecv, hlive]
      have hpA : aRecv.phase = .idle := by simp [aRecv, hidle]
      have hd := deliver_idle_mask I w id aRecv m hlA hpA
      cases h1 : deliver I w id aRecv m with
      | none =>
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => rfl
        | some _ => simp [h1, h2] at hd
      | some pair =>
        obtain ⟨w1, a1⟩ := pair
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => simp [h1, h2] at hd
        | some pair2 =>
          obtain ⟨w2, a2⟩ := pair2
          simp [h1, h2] at hd
          simp only [Option.map, h1, h2]
          rw [mask_setActor, creditLive_mask, mask_setActor, mask_queue]
          conv =>
            rhs
            rw [mask_setActor, creditLive_mask, mask_setActor, mask_queue]
          rw [hd.1, hd.2]
          have hboxA : a1.box = a2.box := by
            simpa [maskActor_box] using congrArg (fun a : Actor => a.box) hd.2
          have hparkA : a1.parked = a2.parked := by
            simpa [maskActor_parked] using congrArg (fun a : Actor => a.parked) hd.2
          have hst : maskActor ((creditLive (setActor w1 id
                { a1 with box := a1.box ++ [p.msg], parked := ps }) (tname id) m.sender).st p.sender) =
              maskActor ((creditLive (setActor w2 id
                { a2 with box := a2.box ++ [p.msg], parked := ps }) (tname id) m.sender).st p.sender) := by
            have hworld : maskWorld (creditLive (setActor w1 id
                  { a1 with box := a1.box ++ [p.msg], parked := ps }) (tname id) m.sender) =
                maskWorld (creditLive (setActor w2 id
                  { a2 with box := a2.box ++ [p.msg], parked := ps }) (tname id) m.sender) := by
              rw [creditLive_mask, creditLive_mask, mask_setActor, mask_setActor, mask_queue, mask_queue,
                hd.1, hd.2, hboxA, hparkA]
              simp [mask_queue]
            have hs := congrArg (fun u : World => u.st p.sender) hworld
            simpa [maskWorld_st] using hs
          rw [resume_mask]
          conv => rhs; rw [resume_mask]
          rw [hst, hboxA]
    · next p ps hbox hpark =>
      let aRecv : Actor :=
        { life := (w.st id).life, typestate := (w.st id).typestate, phase := (w.st id).phase,
          box := (w.st id).box, prio := (w.st id).prio, parked := ps, tokens := (w.st id).tokens,
          nextMid := (w.st id).nextMid, waitId := (w.st id).waitId, nextCall := (w.st id).nextCall,
          oweId := (w.st id).oweId, lastCall := (w.st id).lastCall,
          pendingTombstone := (w.st id).pendingTombstone, parent := (w.st id).parent }
      have hlA : aRecv.life = .alive := by simp [aRecv, hlive]
      have hpA : aRecv.phase = .idle := by simp [aRecv, hidle]
      have hd := deliver_idle_mask I w id aRecv p.msg hlA hpA
      cases h1 : deliver I w id aRecv p.msg with
      | none =>
        cases h2 : deliver I (maskWorld w) id aRecv p.msg with
        | none => rfl
        | some _ => simp [h1, h2] at hd
      | some pair =>
        obtain ⟨w1, a1⟩ := pair
        cases h2 : deliver I (maskWorld w) id aRecv p.msg with
        | none => simp [h1, h2] at hd
        | some pair2 =>
          obtain ⟨w2, a2⟩ := pair2
          simp [h1, h2] at hd
          simp only [Option.map, h1, h2]
          rw [mask_setActor, creditLive_mask, mask_setActor]
          conv =>
            rhs
            rw [mask_setActor, creditLive_mask, mask_setActor]
          rw [hd.1, hd.2]
          have hst : maskActor ((creditLive (setActor w1 id a1) (tname id) p.msg.sender).st p.sender) =
              maskActor ((creditLive (setActor w2 id a2) (tname id) p.msg.sender).st p.sender) := by
            have hworld : maskWorld (creditLive (setActor w1 id a1) (tname id) p.msg.sender) =
                maskWorld (creditLive (setActor w2 id a2) (tname id) p.msg.sender) := by
              rw [creditLive_mask, creditLive_mask, mask_setActor, mask_setActor, hd.1, hd.2]
            have hs := congrArg (fun u : World => u.st p.sender) hworld
            simpa [maskWorld_st] using hs
          rw [resume_mask]
          conv => rhs; rw [resume_mask]
          rw [hst]
    · rfl

theorem descends_mask (fuel : Nat) (w : World) (anc desc : InstId) :
    descends fuel (maskWorld w) anc desc = descends fuel w anc desc := by
  induction fuel generalizing desc with
  | zero => simp [descends]
  | succ n ih =>
    unfold descends
    simp only [maskWorld_st, maskActor_parent]
    split
    · rfl
    · split
      · rfl
      · next p _ =>
        split
        · rfl
        · split
          · rfl
          · exact ih p

theorem mail_mask (w : World) (origin : InstId) :
    mailInFlight (maskWorld w) origin = mailInFlight w origin := by
  unfold mailInFlight sealedTogether
  simp only [maskWorld_roster, maskWorld_st, maskActor_life, maskActor_box, maskActor_prio,
    descends_mask]

theorem waits_mask (w : World) (m : Msg) :
    tombstoneWaits (maskWorld w) m = tombstoneWaits w m := by
  simp [tombstoneWaits, mail_mask]

theorem receivePrioFrom_mask (I : Impl) (w : World) (id : InstId) (skipped ms : List Msg)
    (hl : (w.st id).life = .alive) (hp : (w.st id).phase = .idle) :
    (receivePrioFrom I w id skipped ms).map maskWorld =
      (receivePrioFrom I (maskWorld w) id skipped ms).map maskWorld := by
  induction ms generalizing skipped with
  | nil => simp [receivePrioFrom]
  | cons m ms ih =>
    unfold receivePrioFrom
    simp only [waits_mask]
    split
    · exact ih (skipped ++ [m])
    · have hty : tyRead (w.st id) = true := by simp [tyRead, phaseAnchored, hl, hp]
      simp only [maskWorld_st, maskActor_keep _ hty]
      let aRecv : Actor := { (w.st id) with prio := skipped ++ ms }
      have hlA : aRecv.life = .alive := by simp [aRecv, hl]
      have hpA : aRecv.phase = .idle := by simp [aRecv, hp]
      have hd := deliver_idle_mask I w id aRecv m hlA hpA
      cases h1 : deliver I w id aRecv m with
      | none =>
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => rfl
        | some _ => simp [h1, h2] at hd
      | some pair =>
        obtain ⟨w1, a1⟩ := pair
        cases h2 : deliver I (maskWorld w) id aRecv m with
        | none => simp [h1, h2] at hd
        | some pair2 =>
          obtain ⟨w2, a2⟩ := pair2
          simp [h1, h2] at hd
          simp only [Option.map, h1, h2]
          rw [mask_setActor, mask_setActor, hd.1, hd.2]

theorem receivePrio_mask (I : Impl) (w : World) (id : InstId) :
    (receivePrio I w id).map maskWorld = (receivePrio I (maskWorld w) id).map maskWorld := by
  unfold receivePrio
  have hl : ((maskWorld w).st id).life = (w.st id).life := by simp
  have hp : ((maskWorld w).st id).phase = (w.st id).phase := by simp
  have hprio : ((maskWorld w).st id).prio = (w.st id).prio := by simp
  simp only [hl, hp, hprio]
  cases hgo : ((w.st id).life ≠ .alive || (w.st id).phase ≠ .idle) with
  | true => rw [if_pos rfl, if_pos rfl]
  | false =>
    rw [if_neg (by simp), if_neg (by simp)]
    have hlive : (w.st id).life = .alive := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_true'] at hgo
      simpa using hgo.1
    have hidle : (w.st id).phase = .idle := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_true'] at hgo
      simpa using hgo.2
    exact receivePrioFrom_mask I w id [] (w.st id).prio hlive hidle

theorem mask_edit (a : Actor) (ms : List Msg) (ps : List Parked) (mid : Nat) :
    maskActor { a with box := ms, parked := ps, nextMid := mid } =
      { maskActor a with box := ms, parked := ps, nextMid := mid } := by
  have hs : tyRead { a with box := ms, parked := ps, nextMid := mid } = tyRead a := by simp [tyRead]
  cases ht : tyRead a with
  | true => rw [maskActor_keep _ (hs.trans ht), maskActor_keep a ht]
  | false => rw [maskActor_clear _ (hs.trans ht), maskActor_clear a ht]

theorem mask_phase (a : Actor) (p : Phase) (hp : phaseAnchored p = false) :
    maskActor { a with phase := p } = maskActor { maskActor a with phase := p } := by
  have h1 : tyRead { a with phase := p } = false := by simp [tyRead, hp]
  cases ht : tyRead a with
  | true =>
    rw [maskActor_keep a ht]
  | false =>
    rw [maskActor_clear a ht]
    have h2 : tyRead { { a with typestate := "" } with phase := p } = false := by simp [tyRead, hp]
    rw [maskActor_clear _ h1, maskActor_clear _ h2]

theorem proceed_payload (a b : Actor) (k : Cont)
    (hl : a.life = b.life) (hbox : a.box = b.box) (hprio : a.prio = b.prio)
    (hpark : a.parked = b.parked) (htok : a.tokens = b.tokens) (hmid : a.nextMid = b.nextMid)
    (hwait : a.waitId = b.waitId) (hnext : a.nextCall = b.nextCall) (howe : a.oweId = b.oweId)
    (hlast : a.lastCall = b.lastCall) (hpend : a.pendingTombstone = b.pendingTombstone)
    (hpar : a.parent = b.parent) :
    proceed a k = proceed b k := by
  cases k.rest with
  | nil => simp [proceed, hl, hbox, hprio, hpark, htok, hmid, hwait, hnext, howe, hlast, hpend, hpar]
  | cons _ _ => simp [proceed, hl, hbox, hprio, hpark, htok, hmid, hwait, hnext, howe, hlast, hpend, hpar]

theorem proceed_charge (a : Actor) (dst : String) (k : Cont) :
    proceed (chargeSender (maskActor a) dst) k = proceed (chargeSender a dst) k := by
  rw [← charge_mask, proceed_erase]

theorem proceed_issued (a : Actor) (dst : String) (k : Cont) :
    proceed (issueCall (chargeSender (maskActor a) dst)) k =
      proceed (issueCall (chargeSender a dst)) k := by
  have h : issueCall (chargeSender (maskActor a) dst) =
      maskActor (issueCall (chargeSender a dst)) := by
    rw [← charge_mask, ← issue_mask]
  rw [h, proceed_erase]

theorem finish_issued (a : Actor) (k : Cont) (r : CallResult) :
    finishCall (issueCall (maskActor a)) k r = finishCall (issueCall a) k r := by
  rw [← issue_mask, finish_erase]

theorem mask_diff_ty (a b : Actor)
    (hl : a.life = b.life) (hp : a.phase = b.phase) (hbox : a.box = b.box) (hprio : a.prio = b.prio)
    (hpark : a.parked = b.parked) (htok : a.tokens = b.tokens) (hmid : a.nextMid = b.nextMid)
    (hwait : a.waitId = b.waitId) (hnext : a.nextCall = b.nextCall) (howe : a.oweId = b.oweId)
    (hlast : a.lastCall = b.lastCall) (hpend : a.pendingTombstone = b.pendingTombstone)
    (hpar : a.parent = b.parent) (hph : phaseAnchored a.phase = false) :
    maskActor a = maskActor b := by
  have ha : tyRead a = false := by simp [tyRead, hph]
  have hb : tyRead b = false := by
    unfold tyRead
    rw [← hp]
    simp [hph]
  rw [maskActor_clear a ha, maskActor_clear b hb]
  exact actor_eq (by simp [hl]) rfl (by simp [hp]) (by simp [hbox]) (by simp [hprio])
    (by simp [hpark]) (by simp [htok]) (by simp [hmid]) (by simp [hwait]) (by simp [hnext])
    (by simp [howe]) (by simp [hlast]) (by simp [hpend]) (by simp [hpar])

/-- Masking ignores a typestate that was already replaced by the masked typestate
of an actor with the same life, phase, and typestate. -/
theorem mask_join (c a b : Actor)
    (hcl : c.life = a.life) (hcp : c.phase = a.phase) (hct : c.typestate = a.typestate)
    (hl : a.life = b.life) (hp : a.phase = b.phase) (hbox : a.box = b.box) (hprio : a.prio = b.prio)
    (hpark : a.parked = b.parked) (htok : a.tokens = b.tokens) (hmid : a.nextMid = b.nextMid)
    (hwait : a.waitId = b.waitId) (hnext : a.nextCall = b.nextCall) (howe : a.oweId = b.oweId)
    (hlast : a.lastCall = b.lastCall) (hpend : a.pendingTombstone = b.pendingTombstone)
    (hpar : a.parent = b.parent) (ht : b.typestate = (maskActor c).typestate) :
    maskActor a = maskActor b := by
  have hty : tyRead a = tyRead c := by simp [tyRead, hcl, hcp, hct]
  cases htread : tyRead c with
  | true =>
    rw [maskActor_keep c htread] at ht
    rw [hct] at ht
    have he : a = b := actor_eq hl ht.symm hp hbox hprio hpark htok hmid hwait hnext howe hlast
      hpend hpar
    rw [he]
  | false =>
    have ha : tyRead a = false := by rw [hty, htread]
    have hb : tyRead b = false := by
      have : tyRead b = tyRead a := by simp [tyRead, hl, hp]
      rw [this, ha]
    rw [maskActor_clear a ha, maskActor_clear b hb]
    exact actor_eq (by simp [hl]) rfl (by simp [hp]) (by simp [hbox]) (by simp [hprio])
      (by simp [hpark]) (by simp [htok]) (by simp [hmid]) (by simp [hwait]) (by simp [hnext])
      (by simp [howe]) (by simp [hlast]) (by simp [hpend]) (by simp [hpar])

theorem mask_fields (a : Actor) (p : Phase) (ms : List Msg) (ps : List Parked) (mid : Nat)
    (hp : phaseAnchored p = false) :
    maskActor { a with phase := p, box := ms, parked := ps, nextMid := mid } =
      maskActor { maskActor a with phase := p, box := ms, parked := ps, nextMid := mid } := by
  have h1 : tyRead { a with phase := p, box := ms, parked := ps, nextMid := mid } = false := by
    simp [tyRead, hp]
  cases ht : tyRead a with
  | true => rw [maskActor_keep a ht]
  | false =>
    rw [maskActor_clear a ht]
    have h2 : tyRead { { a with typestate := "" } with phase := p, box := ms, parked := ps, nextMid := mid } =
        false := by simp [tyRead, hp]
    rw [maskActor_clear _ h1, maskActor_clear _ h2]

theorem mask_set_phased (w : World) (id : InstId) (a : Actor) (p : Phase) (ms : List Msg)
    (ps : List Parked) (mid : Nat) (hp : phaseAnchored p = false) :
    maskWorld (setActor w id { a with phase := p, box := ms, parked := ps, nextMid := mid }) =
      maskWorld (setActor (maskWorld w) id
        { maskActor a with phase := p, box := ms, parked := ps, nextMid := mid }) := by
  rw [mask_setActor, mask_fields a p ms ps mid hp]
  conv => rhs; rw [mask_setActor]
  rw [maskWorld_idem]

theorem mask_set_edit (w : World) (id : InstId) (a : Actor) (ms : List Msg) (ps : List Parked)
    (mid : Nat) :
    maskWorld (setActor w id { a with box := ms, parked := ps, nextMid := mid }) =
      setActor (maskWorld w) id { maskActor a with box := ms, parked := ps, nextMid := mid } := by
  rw [mask_setActor, mask_edit]

theorem enqueueOrPark_mask (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) :
    maskWorld (enqueueOrPark w D sender dst msg isCall k) =
      maskWorld (enqueueOrPark (maskWorld w) D sender dst msg isCall k) := by
  unfold enqueueOrPark
  simp only [maskWorld_N, maskWorld_st, maskActor_life, maskActor_parked, maskActor_box]
  split
  · split
    · rw [mask_setActor, mask_setActor, maskWorld_idem, finish_issued]
    · exact mask_set_proceed _ _ _ _
  · split
    · split
      · split
        · simp only [issueCall, chargeSender, bumpToken, maskActor_nextMid, maskActor_waitId,
            maskActor_box, maskActor_parked, maskActor_life, maskActor_phase, maskActor_prio,
            maskActor_tokens, maskActor_nextCall, maskActor_oweId, maskActor_lastCall,
            maskActor_pending, maskActor_parent]
          rw [mask_setActor, mask_setActor, maskWorld_idem]
          refine congrArg (setActor (maskWorld w) sender) ?_
          first
            | rfl
            | apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
        · simp only [issueCall, chargeSender, bumpToken, maskActor_nextMid, maskActor_waitId,
            maskActor_box, maskActor_parked, maskActor_life, maskActor_phase, maskActor_prio,
            maskActor_tokens, maskActor_nextCall, maskActor_oweId, maskActor_lastCall,
            maskActor_pending, maskActor_parent]
          rw [mask_setActor, mask_setActor, maskWorld_idem]
          refine congrArg (setActor (maskWorld w) sender) ?_
          first
            | rfl
            | apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
      · split
        · simp only [issueCall, chargeSender, bumpToken, maskWorld_st, maskActor_nextMid,
            maskActor_waitId, maskActor_box, maskActor_parked, maskActor_life, maskActor_phase,
            maskActor_prio, maskActor_tokens, maskActor_nextCall, maskActor_oweId,
            maskActor_lastCall, maskActor_pending, maskActor_parent]
          rw [mask_setActor, mask_setActor, mask_setActor, mask_setActor, maskWorld_idem]
          congr 1
          · congr 1
            apply mask_join (w.st dst) <;> rfl
          · apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
        · simp only [issueCall, chargeSender, bumpToken, maskWorld_st, maskActor_nextMid,
            maskActor_waitId, maskActor_box, maskActor_parked, maskActor_life, maskActor_phase,
            maskActor_prio, maskActor_tokens, maskActor_nextCall, maskActor_oweId,
            maskActor_lastCall, maskActor_pending, maskActor_parent]
          rw [mask_setActor, mask_setActor, mask_setActor, mask_setActor, maskWorld_idem]
          congr 1
          · congr 1
            apply mask_join (w.st dst) <;> rfl
    · split
      · cases isCall <;>
          simp only [issueCall, chargeSender, bumpToken, maskWorld_st, maskActor_nextMid,
            maskActor_waitId, maskActor_box, maskActor_parked, maskActor_life, maskActor_phase,
            maskActor_prio, maskActor_tokens, maskActor_nextCall, maskActor_oweId,
            maskActor_lastCall, maskActor_pending, maskActor_parent]
        <;> rw [mask_setActor, mask_setActor, maskWorld_idem]
        <;> refine congrArg (setActor (maskWorld w) sender) ?_
        <;> first
          | rfl
          | apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
      · cases isCall <;>
          simp only [issueCall, chargeSender, bumpToken, maskWorld_st, maskActor_nextMid,
            maskActor_waitId, maskActor_box, maskActor_parked, maskActor_life, maskActor_phase,
            maskActor_prio, maskActor_tokens, maskActor_nextCall, maskActor_oweId,
            maskActor_lastCall, maskActor_pending, maskActor_parent]
        <;> rw [mask_setActor, mask_setActor, mask_setActor, mask_setActor, maskWorld_idem]
        <;> (congr 1
             · congr 1
               apply mask_join (w.st dst) <;> rfl
             · apply mask_diff_ty <;> first | rfl | simp [phaseAnchored])

theorem performReply_mask (w : World) (sender : InstId) (k : Cont) :
    maskWorld (performReply w sender k) = maskWorld (performReply (maskWorld w) sender k) := by
  unfold performReply
  simp only [maskWorld_st, maskActor_phase, maskActor_oweId, maskActor_waitId]
  split
  · exact mask_set_proceed w sender (w.st sender) (afterHead k)
  · next caller hreply =>
    split
    · next dst ck _hphase =>
      split
      · rw [finish_erase]
        by_cases hself : sender = caller
        · simp only [hself, setActor_self]
          rw [mask_setActor, mask_setActor, mask_setActor, mask_setActor, maskWorld_idem]
        · rw [setActor_other w caller sender _ hself, setActor_other (maskWorld w) caller sender _ hself,
            maskWorld_st, proceed_erase]
          rw [mask_setActor, mask_setActor, mask_setActor, mask_setActor, maskWorld_idem]
      · exact mask_set_proceed w sender (w.st sender) (afterHead k)
    · exact mask_set_proceed w sender (w.st sender) (afterHead k)

theorem route_mask (w : World) (D : Description) (sender : InstId) (dst : String) (slot : Nat) :
    route (maskWorld w) D sender dst slot = route w D sender dst slot := by
  simp [route, maskWorld_st, maskActor_life, findLive_mask]

theorem resolve_mask (D : Description) (w : World) (sender : InstId) (dst : String) (slot : Nat) :
    resolveId D (maskWorld w) sender dst slot = resolveId D w sender dst slot := by
  simp [resolveId, findLive_mask]

theorem queued_mask (w : World) (name : String) (key : Nat) (dst : String) :
    queuedFromKey (maskWorld w) name key dst = queuedFromKey w name key dst := by
  unfold queuedFromKey
  simp only [maskWorld_roster, maskWorld_st, maskActor_box, maskActor_parked]

theorem occupied_mask (w : World) (name : String) (k : Nat) :
    slotOccupied (maskWorld w) name k = slotOccupied w name k := by
  simp [slotOccupied, maskWorld_roster, maskWorld_st, maskActor_life]

theorem tombQueued_mask (w : World) (parent : InstId) (child : String) (k : Nat) :
    slotTombstoneQueued (maskWorld w) parent child k = slotTombstoneQueued w parent child k := by
  simp [slotTombstoneQueued, maskWorld_st, maskActor_prio]

theorem blocked_mask (D : Description) (w : World) (parent : InstId) (name : String) (key : Nat) :
    slotRespawnBlocked D (maskWorld w) parent name key = slotRespawnBlocked D w parent name key := by
  simp [slotRespawnBlocked, occupied_mask, tombQueued_mask]

theorem freeGo_mask (D : Description) (w : World) (parent : InstId) (name : String) (n fuel : Nat) :
    freeGo D (maskWorld w) parent name n fuel = freeGo D w parent name n fuel := by
  induction fuel with
  | zero => simp [freeGo]
  | succ fuel ih =>
    simp only [freeGo, blocked_mask, ih]

theorem freeSlot_mask (D : Description) (w : World) (parent : InstId) (name : String) (n : Nat) :
    freeSlot D (maskWorld w) parent name n = freeSlot D w parent name n := by
  simp [freeSlot, freeGo_mask]

theorem born_mask (D : Description) (w : World) (template : String) (key : Nat) (initial : String) :
    bornActor D (maskWorld w) template key initial = bornActor D w template key initial := by
  simp [bornActor, withKeyTokens, queued_mask]

theorem child_mask (D : Description) (w : World) (id : InstId) :
    hasChild D (maskWorld w) id = hasChild D w id := by
  simp [hasChild, maskWorld_roster, isChild_mask, maskWorld_st, maskActor_life]

theorem mask_extend (w : World) (extra : List InstId) :
    maskWorld { w with roster := w.roster ++ extra } =
      { maskWorld w with roster := w.roster ++ extra } := by
  unfold maskWorld
  rfl

theorem admit_mask (I : Impl) (w : World) (id : InstId) (a : Actor) (ha : maskActor a = a) :
    maskWorld (admitBorn I w id a) = admitBorn I (maskWorld w) id a := by
  unfold admitBorn
  rw [readCells_mask, mask_setActor, ha, mask_extend, maskWorld_roster]

theorem born_kept (D : Description) (w : World) (template : String) (key : Nat) (initial : String)
    (parent : InstId) :
    maskActor { bornActor D w template key initial with parent := some parent } =
      { bornActor D w template key initial with parent := some parent } := by
  apply maskActor_keep
  simp [bornActor, withKeyTokens, tyRead, phaseAnchored]

theorem spawnChild_mask (I : Impl) (w : World) (parent : InstId) (child : String) :
    (spawnChild I w parent child).map maskWorld =
      (spawnChild I (maskWorld w) parent child).map maskWorld := by
  cases parent with
  | core pname =>
    unfold spawnChild
    simp only [maskWorld_st, maskActor_life, freeSlot_mask, maxGen_mask, born_mask, blocked_mask]
    split
    · rfl
    · next ht t =>
      split
      · split
        · split
          · next k _hk =>
            simp only [Option.map]
            have hkeep := born_kept I.desc w child k ht.initial (InstId.core pname)
            rw [admit_mask I w _ _ hkeep]
            rw [admit_mask I (maskWorld w) _ _ hkeep, maskWorld_idem]
          · simp [maskWorld_idem]
        · rfl
      · split
        · simp [maskWorld_idem]
        · rfl
  | peer pname pkey pgen =>
    unfold spawnChild
    simp only [maskWorld_st, maskActor_life, freeSlot_mask, maxGen_mask, born_mask, blocked_mask]
    split
    · rfl
    · next ht t =>
      split
      · split
        · split
          · simp [maskWorld_idem]
          · simp only [Option.map]
            have hkeep :=
              born_kept I.desc w child pkey ht.initial (InstId.peer pname pkey pgen)
            rw [admit_mask I w _ _ hkeep]
            rw [admit_mask I (maskWorld w) _ _ hkeep, maskWorld_idem]
        · rfl
      · split
        · simp [maskWorld_idem]
        · rfl

theorem execRun_mask (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) :
    maskWorld (execRun I w id a k) =
      maskWorld (execRun I (maskWorld w) id (maskActor a) k) := by
  unfold execRun
  simp only [maskActor_life, maskActor_phase, maskWorld_N, maskWorld_st, maskActor_box, maskActor_prio,
    maskActor_parked, maskActor_nextMid, maskActor_tokens, maskActor_waitId, maskActor_nextCall,
    maskActor_oweId, maskActor_lastCall, maskActor_pending, maskActor_parent, route_mask,
    resolve_mask, child_mask]
  split
  · split
    · have hland : { a with phase := .idle, typestate := k.toState } =
          { maskActor a with phase := .idle, typestate := k.toState } := by
        apply actor_eq <;> first | rfl | simp [maskActor_life, maskActor_box, maskActor_prio,
          maskActor_parked, maskActor_tokens, maskActor_nextMid, maskActor_waitId,
          maskActor_nextCall, maskActor_oweId, maskActor_lastCall, maskActor_pending,
          maskActor_parent]
      rw [hland, mask_setActor, mask_setActor, maskWorld_idem]
    · split
      · split
        · rw [← note_mask]
          exact mask_set_proceed (noteStale w id _) id a (afterHead k)
        · exact enqueueOrPark_mask w I.desc id _ _ false (afterHead k)
      · split
        · rw [← note_mask]
          exact mask_set_proceed (noteStale w id _) id a _
        · split
          · exact enqueueOrPark_mask w I.desc id _ _ false _
          · split
            · exact mask_set_proceed w id a _
            · exact mask_set_proceed w id a _
      · split
        · rw [← note_mask, ← finish_issued, mask_setActor, mask_setActor, maskWorld_idem]
        · exact enqueueOrPark_mask w I.desc id _ _ true _
      · exact performReply_mask w id k
      · split
        · exact mask_set_proceed w id a (afterHead k)
        · split
          · rw [mask_setActor, mask_setActor, maskWorld_idem]
            simp [proceed]
          · exact crashWorld_mask w
      · conv =>
          rhs
          rw [maskWorld_cell]
        have hcell : ∀ u d l c, (setCell u d l c).st = u.st := by
          intro u d l c
          simp [setCell]
        split
        · rw [hcell, hcell, maskWorld_st, proceed_erase, ← setCell_mask, mask_setActor, mask_setActor,
            maskWorld_idem]
        · rw [hcell, hcell, maskWorld_st, proceed_erase, ← setCell_mask, wakeReaders_mask]
          conv => rhs; rw [wakeReaders_mask]
          congr 1
          congr 1
          rw [mask_setActor, mask_setActor, maskWorld_idem]
      · rw [mask_setActor, mask_setActor, maskWorld_idem]
        refine congrArg (setActor (maskWorld w) id) ?_
        apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
      · rw [mask_setActor, mask_setActor, maskWorld_idem]
        refine congrArg (setActor (maskWorld w) id) ?_
        apply mask_diff_ty <;> first | rfl | simp [phaseAnchored]
      · exact abortChildren_mask I.desc w id
      · rename_i _x _tail _eff child _heq
        split
        · next w' hw =>
          have hs := spawnChild_mask I w id child
          rw [hw] at hs
          cases hM : spawnChild I (maskWorld w) id child with
          | none => simp [hM] at hs
          | some wM =>
            simp [hM] at hs
            have hst : maskActor (w'.st id) = maskActor (wM.st id) := by
              have hws := congrArg (fun u : World => u.st id) hs
              simpa [maskWorld_st] using hws
            have hp : proceed (w'.st id) (afterHead k) = proceed (wM.st id) (afterHead k) := by
              rw [← proceed_erase (w'.st id), ← proceed_erase (wM.st id), hst]
            simp [hp, mask_setActor, hs, maskWorld_idem]
        · next hnone =>
          have hs := spawnChild_mask I w id child
          rw [hnone] at hs
          cases hM : spawnChild I (maskWorld w) id child with
          | some _ => simp [hM] at hs
          | none =>
            simp [hM]
            exact crashWorld_mask w
      · split
        · split
          · exact crashWorld_mask w
          · split
            · exact terminateStage_mask I.desc w id a
            · split
              · exact shutdownActor_mask I.desc w id
              · split
                · exact terminateStage_mask I.desc w id a
                · exact crashWorld_mask w
        · exact crashWorld_mask w
  · exact (maskWorld_idem w).symm

theorem execHead_mask (I : Impl) (w : World) (id : InstId) :
    (execHead I w id).map maskWorld = (execHead I (maskWorld w) id).map maskWorld := by
  unfold execHead
  simp only [maskWorld_st, maskActor_life, maskActor_phase]
  split
  · exact congrArg some (sealActor_mask I.desc w id (w.st id))
  · split
    · rfl
    · split
      · next k _hk =>
        exact congrArg some (execRun_mask I w id (w.st id) k)
      · rfl

theorem mask_box (a : Actor) (ms : List Msg) :
    maskActor { a with box := ms } = maskActor { maskActor a with box := ms } := by
  have hs : tyRead { a with box := ms } = tyRead a := by simp [tyRead]
  cases ht : tyRead a with
  | true => rw [maskActor_keep a ht]
  | false =>
    rw [maskActor_clear a ht]
    have h1 : tyRead { a with box := ms } = false := hs.trans ht
    have h2 : tyRead { { a with typestate := "" } with box := ms } = false := by
      simp only [tyRead] at ht ⊢
      exact ht
    rw [maskActor_clear _ h1, maskActor_clear _ h2]

theorem detachBox_mask (a : Actor) (caller : InstId) :
    maskActor (detachBox a caller) = maskActor (detachBox (maskActor a) caller) := by
  simp only [detachBox, maskActor_box]
  exact mask_box a (a.box.map (detachMsg caller))

theorem clearReply_anchored (caller : InstId) (ph : Phase) :
    phaseAnchored (clearReplyPhase caller ph) = phaseAnchored ph := by
  cases ph <;> simp [clearReplyPhase, phaseAnchored]

theorem detachReply_mask (a : Actor) (caller : InstId) (cid : Nat) :
    maskActor (detachReply a caller cid) = maskActor (detachReply (maskActor a) caller cid) := by
  unfold detachReply
  simp only [maskActor_oweId, maskActor_phase]
  by_cases h : (a.oweId == some cid) = true
  · rw [if_pos h, if_pos h]
    cases hanch : phaseAnchored a.phase with
    | true =>
      cases hph : a.phase with
      | idle =>
        simp only [clearReplyPhase, hph]
        cases ht : tyRead a with
        | true => rw [maskActor_keep a ht]
        | false =>
          rw [maskActor_clear a ht]
          have h1 : tyRead { a with phase := .idle } = false := by
            simp only [tyRead, hph] at ht ⊢
            exact ht
          have h2 : tyRead { { a with typestate := "" } with phase := .idle } = false := by
            simp only [tyRead, hph] at ht ⊢
            exact ht
          rw [maskActor_clear _ h1, maskActor_clear _ h2]
      | crashed =>
        simp only [clearReplyPhase, hph]
        cases ht : tyRead a with
        | true => rw [maskActor_keep a ht]
        | false =>
          rw [maskActor_clear a ht]
          have h1 : tyRead { a with phase := .crashed } = false := by
            simp only [tyRead, hph] at ht ⊢
            exact ht
          have h2 : tyRead { { a with typestate := "" } with phase := .crashed } = false := by
            simp only [tyRead, hph] at ht ⊢
            exact ht
          rw [maskActor_clear _ h1, maskActor_clear _ h2]
      | run k => simp [phaseAnchored, hph] at hanch
      | parked d c k => simp [phaseAnchored, hph] at hanch
      | awaitReply d k => simp [phaseAnchored, hph] at hanch
      | awaitEffect k => simp [phaseAnchored, hph] at hanch
      | awaitPeer k => simp [phaseAnchored, hph] at hanch
    | false =>
      simpa [maskActor_life, maskActor_box, maskActor_prio, maskActor_parked, maskActor_tokens,
        maskActor_nextMid, maskActor_waitId, maskActor_nextCall, maskActor_oweId, maskActor_lastCall,
        maskActor_pending, maskActor_parent] using
        mask_phase a (clearReplyPhase caller a.phase) (by rw [clearReply_anchored]; exact hanch)
  · rw [if_neg h, if_neg h, maskActor_idem]

theorem detach_mask (a : Actor) (caller : InstId) (cid : Nat) :
    maskActor (detachReply (detachBox a caller) caller cid) =
      maskActor (detachReply (detachBox (maskActor a) caller) caller cid) := by
  have hbox := detachBox_mask a caller
  have h1 := detachReply_mask (detachBox a caller) caller cid
  have h2 := detachReply_mask (detachBox (maskActor a) caller) caller cid
  rw [h1, hbox]
  exact h2.symm

theorem refundParkedCall_mask (w : World) (caller dst : InstId) :
    maskWorld (refundParkedCall w caller dst) =
      maskWorld (refundParkedCall (maskWorld w) caller dst) := by
  unfold refundParkedCall
  simp only [maskWorld_st, maskActor_parked]
  by_cases hempty : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty = true
  · simp [hempty, maskWorld_idem]
  · have hfalse : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty = false := by
      cases h : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty with
      | false => rfl
      | true => exact absurd h hempty
    simp only [hfalse]
    rw [if_neg (by decide : ¬ (false = true))]
    conv => rhs; rw [if_neg (by decide : ¬ (false = true))]
    have hstep : ∀ v (_x : Parked), maskWorld (creditSender v (tname dst) caller) =
        maskWorld (creditSender (maskWorld v) (tname dst) caller) := by
      intro v _x
      rw [credit_mask, credit_mask, maskWorld_idem]
    have hstart := mask_setActor w dst
      { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
    rw [foldl_mask _ _ _ hstep, hstart, mask_repark]

theorem receiveIngress_mask (I : Impl) (w : World) (dst : InstId) (label : String) :
    (receiveIngress I w dst label).map maskWorld =
      (receiveIngress I (maskWorld w) dst label).map maskWorld := by
  unfold receiveIngress
  simp only [maskWorld_st, maskWorld_N, maskActor_life, maskActor_phase, maskActor_box,
    maskActor_tokens, maskActor_nextMid]
  split
  · rfl
  · next hopen =>
    have hdec : (decide ((w.st dst).life ≠ .alive) ||
        decide (ingressOpen (w.st dst).phase = false)) = false := by
      simpa using hopen
    have hlive : (w.st dst).life = .alive := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hdec
      cases hlife : (w.st dst).life with
      | alive => rfl
      | shuttingDown =>
        exact absurd (by rw [hlife]; intro h; cases h) hdec.1
      | dead =>
        exact absurd (by rw [hlife]; intro h; cases h) hdec.1
      | absent =>
        exact absurd (by rw [hlife]; intro h; cases h) hdec.1
    have hhold : tokenHold I.desc (tname dst) (tname dst) (maskActor (w.st dst)) =
        tokenHold I.desc (tname dst) (tname dst) (w.st dst) := by
      cases ht : tyRead (w.st dst) with
      | true => rw [maskActor_keep _ ht]
      | false =>
        rw [maskActor_clear _ ht]
        have hph : phaseAnchored (w.st dst).phase = false := by
          simp [tyRead, hlive] at ht
          exact ht
        exact tokenHold_running I.desc (tname dst) (tname dst) (w.st dst) "" hph
    simp only [hhold]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · simp only [Option.map]
            rw [mask_setActor, mask_setActor, maskWorld_idem]
            congr 1
            apply congrArg (setActor (maskWorld w) dst)
            cases ht : tyRead (w.st dst) with
            | true => rw [maskActor_keep _ ht]
            | false =>
              rw [maskActor_clear _ ht]
              have hph : phaseAnchored (w.st dst).phase = false := by
                simp [tyRead, hlive] at ht
                exact ht
              have h1 : tyRead { chargeSender (w.st dst) (tname dst) with
                  box := (w.st dst).box ++
                    [{ label := label, sender := dst, callFrom := none, mid := (w.st dst).nextMid }],
                  nextMid := (w.st dst).nextMid + 1 } = false := by
                simp [tyRead, chargeSender, bumpToken, hph]
              have h2 : tyRead { chargeSender { (w.st dst) with typestate := "" } (tname dst) with
                  box := (w.st dst).box ++
                    [{ label := label, sender := dst, callFrom := none, mid := (w.st dst).nextMid }],
                  nextMid := (w.st dst).nextMid + 1 } = false := by
                simp [tyRead, chargeSender, bumpToken, hph]
              rw [maskActor_clear _ h1, maskActor_clear _ h2]
              simp [chargeSender, bumpToken]

theorem finishWait_mask (I : Impl) (w : World) (id : InstId) :
    (finishWait I w id).map maskWorld = (finishWait I (maskWorld w) id).map maskWorld := by
  unfold finishWait
  simp only [maskWorld_st, maskActor_life, maskActor_phase]
  split
  · rfl
  · split
    · next k _hk =>
      simp only [Option.map]
      exact congrArg some (mask_set_proceed w id (w.st id) k)
    · next k _hk =>
      simp only [Option.map]
      exact congrArg some (mask_set_proceed w id (w.st id) k)
    · rfl

theorem callTimeout_mask (w : World) (id : InstId) :
    (callTimeout w id).map maskWorld = (callTimeout (maskWorld w) id).map maskWorld := by
  unfold callTimeout
  simp only [maskWorld_st, maskActor_life, maskActor_phase, maskActor_waitId]
  split
  · rfl
  · split
    · next dst k _hph =>
      simp only [Option.map]
      by_cases hself : id = dst
      · subst hself
        rw [mask_setActor, mask_setActor]
        conv =>
          rhs
          rw [mask_setActor, mask_setActor]
        rw [setActor_self, setActor_self, detach_mask, maskWorld_idem]
        have hfin : finishCall (detachReply (detachBox (w.st id) id) id (w.st id).waitId) k .timedOut =
            finishCall (detachReply (detachBox (maskActor (w.st id)) id) id (w.st id).waitId) k .timedOut := by
          rw [← finish_erase, detach_mask, finish_erase]
        simp [hfin]
      · rw [mask_setActor, mask_setActor]
        conv =>
          rhs
          rw [mask_setActor, mask_setActor]
        rw [setActor_other w dst id _ hself, setActor_other (maskWorld w) dst id _ hself, maskWorld_st,
          detach_mask, finish_erase, maskWorld_idem]
    · next dst k _hph =>
      simp only [Option.map]
      rw [mask_setActor]
      conv =>
        rhs
        rw [mask_setActor]
      rw [refundParkedCall_mask]
      have hst := congrArg (fun u : World => u.st id) (refundParkedCall_mask w id dst)
      simp only [maskWorld_st] at hst
      have hfin : finishCall ((refundParkedCall w id dst).st id) k .notAdmitted =
          finishCall ((refundParkedCall (maskWorld w) id dst).st id) k .notAdmitted := by
        rw [← finish_erase, hst, finish_erase]
      simp [hfin]
    · next k _hph =>
      simp only [Option.map]
      exact congrArg some (mask_set_proceed w id (w.st id)
        { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout })
    · rfl

theorem survives_mask (w : World) (sender host : InstId) :
    survivesSender (maskWorld w) sender host = survivesSender w sender host := by
  simp [survivesSender, maskWorld_st, maskActor_life, sealedTogether, descends_mask, maskWorld_roster]

theorem slotMail_mask (D : Description) (w : World) (name : String) (key : Nat) :
    slotMailHeld D (maskWorld w) name key = slotMailHeld D w name key := by
  unfold slotMailHeld slotCoreMail subtreeCoreMail actorHoldsSlotMail actorHoldsSubtreeMail
  simp only [maskWorld_roster, maskWorld_st, maskActor_box, maskActor_prio, maskActor_parked,
    survives_mask]

theorem rootOut_mask (D : Description) (w : World) (supervisor name : String) :
    rootOutstanding D (maskWorld w) supervisor name = rootOutstanding D w supervisor name := by
  unfold rootOutstanding
  simp only [maskWorld_roster, maskWorld_st, maskActor_life, tombQueued_mask]

theorem loneOut_mask (D : Description) (w : World) (name : String) :
    loneOutstanding D (maskWorld w) name = loneOutstanding D w name := by
  unfold loneOutstanding
  simp only [maskWorld_roster, maskWorld_st, maskActor_life, slotMail_mask]

theorem maySpawn_mask (D : Description) (w : World) (template : String) (t : Template) :
    maySpawnRoot D (maskWorld w) template t = maySpawnRoot D w template t := by
  unfold maySpawnRoot supervisorLive
  simp only [maskWorld_st, maskActor_life, maskWorld_N, rootOut_mask, loneOut_mask]

theorem freshKey_mask (D : Description) (w : World) (sub : String) :
    freshKey D (maskWorld w) sub = freshKey D w sub := by
  unfold freshKey
  simp [maskWorld_roster, maskWorld_nextKey]

theorem born_parent (D : Description) (w : World) (template : String) (key : Nat) (initial : String)
    (parent : Option InstId) :
    maskActor { bornActor D w template key initial with parent := parent } =
      { bornActor D w template key initial with parent := parent } := by
  apply maskActor_keep
  simp [bornActor, withKeyTokens, tyRead, phaseAnchored]

theorem read_born (I : Impl) (w : World) (id : InstId) (a : Actor) (ha : maskActor a = a) :
    maskWorld (readCells I.desc (setActor w id a) id) =
      readCells I.desc (setActor (maskWorld w) id a) id := by
  rw [readCells_mask, mask_setActor, ha]

theorem mask_nextKey (w : World) (k : String → Nat) :
    maskWorld { w with nextKey := k } = { maskWorld w with nextKey := k } := by
  unfold maskWorld
  rfl

theorem mask_nextIx (w : World) (k : String → Nat) :
    maskWorld { w with nextIx := k } = { maskWorld w with nextIx := k } := by
  unfold maskWorld
  rfl

theorem placePeer_mask (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnext : ∀ u, maskWorld (next u) = next (maskWorld u)) :
    maskWorld (placePeer I w template k initial parent next) =
      maskWorld (placePeer I (maskWorld w) template k initial parent next) := by
  unfold placePeer
  simp only [maxGen_mask, born_mask]
  have hkeep := born_parent I.desc w template k initial parent
  let id := InstId.peer template k (maxGen w template k)
  have hbase : maskWorld (next { w with roster := w.roster ++ [id] }) =
      maskWorld (next { maskWorld w with roster := (maskWorld w).roster ++ [id] }) := by
    rw [hnext, hnext, mask_extend, mask_extend, maskWorld_idem, maskWorld_roster]
  rw [read_born I (next { w with roster := w.roster ++ [id] }) id _ hkeep,
    read_born I (next { maskWorld w with roster := (maskWorld w).roster ++ [id] }) id _ hkeep, hbase]

theorem spawn_mask (I : Impl) (w : World) (template : String) :
    (spawn I w template).map maskWorld = (spawn I (maskWorld w) template).map maskWorld := by
  unfold spawn
  simp only [maySpawn_mask, freshKey_mask, maskWorld_nextIx]
  split
  · rfl
  · next t _ht =>
    split
    · split
      · simp only [Option.map]
        apply congrArg some
        apply placePeer_mask
        intro u
        rw [mask_nextKey]
        rfl
      · split
        · simp only [Option.map]
          apply congrArg some
          apply placePeer_mask
          intro u
          rw [mask_nextIx]
          rfl
        · simp only [Option.map]
          apply congrArg some
          apply placePeer_mask
          intro u
          rw [mask_nextKey]
          rfl
    · rfl

theorem option_isSome_map {α β : Type} (f : α → β) (o1 o2 : Option α)
    (h : o1.map f = o2.map f) : o1.isSome = o2.isSome := by
  cases o1 <;> cases o2 <;> simp [Option.map] at h <;> rfl

theorem runtimeBusy_mask (I : Impl) (w : World) :
    runtimeBusy I (maskWorld w) = runtimeBusy I w := by
  unfold runtimeBusy
  simp only [maskWorld_roster]
  have h : ∀ id, ((receiveBulk I w id).isSome || (receivePrio I w id).isSome ||
      (execHead I w id).isSome || (finishWait I w id).isSome || (callTimeout w id).isSome) =
      ((receiveBulk I (maskWorld w) id).isSome || (receivePrio I (maskWorld w) id).isSome ||
        (execHead I (maskWorld w) id).isSome || (finishWait I (maskWorld w) id).isSome ||
        (callTimeout (maskWorld w) id).isSome) := by
    intro id
    have hb := option_isSome_map maskWorld _ _ (receiveBulk_mask I w id)
    have hp := option_isSome_map maskWorld _ _ (receivePrio_mask I w id)
    have he := option_isSome_map maskWorld _ _ (execHead_mask I w id)
    have hf := option_isSome_map maskWorld _ _ (finishWait_mask I w id)
    have hc := option_isSome_map maskWorld _ _ (callTimeout_mask w id)
    simp [hb, hp, he, hf, hc]
  induction w.roster with
  | nil => rfl
  | cons id ids ih => simp [List.any_cons, h id, ih]

theorem stepWorld_mask (I : Impl) (a : Action) (w : World) :
    (stepWorld I a w).map maskWorld = (stepWorld I a (maskWorld w)).map maskWorld := by
  unfold stepWorld
  cases a with
  | recvBulk s => exact receiveBulk_mask I w s
  | recvPrio s => exact receivePrio_mask I w s
  | exec s => exact execHead_mask I w s
  | finish s => exact finishWait_mask I w s
  | spawn template => exact spawn_mask I w template
  | ingress dst label => exact receiveIngress_mask I w dst label
  | callTimeout s => exact callTimeout_mask w s
  | stutter =>
    simp only [runtimeBusy_mask]
    split
    · rfl
    · exact congrArg some (maskWorld_idem w).symm

theorem apply_mask (I : Impl) (a : Action) (w : World) :
    (apply I a w).map maskWorld = (apply I a (maskWorld w)).map maskWorld := by
  unfold apply
  simp only [maskWorld_crashed]
  cases hc : w.crashed with
  | true => rfl
  | false => exact stepWorld_mask I a w

/-- A step reads `typestate` only on an alive idle or crashed actor. Clearing it
everywhere else leaves the step unchanged. -/
theorem typestate_read_only_idle (I : Impl) (a : Action) (w : World) :
    (apply I a w).map maskWorld = (apply I a (maskWorld w)).map maskWorld :=
  apply_mask I a w

end Deadlock
