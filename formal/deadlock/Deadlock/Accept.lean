/-
One listener. The accept stage is a static core and does not terminate.
The detached completion is an ingress message, `Accepted` or `AcceptError`.
Both edges are non-blocking, so the stage does not wait on its own result.
One bulk slot is the outstanding bound: a second completion is refused
while the first sits in the box. That one fits `prioSized` for a single
priority sender and Lemma 1 for the mailbox. The handlers are empty, so the
core stays idle; a second result cannot arrive while the first is running.
Forwarding `Accepted` to a manager is a different edge, not this completion.
There is no listen tombstone and no respawn. The wiring is `examples/accept.json`.
-/
import Deadlock.Local
import Deadlock.Semantics

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Deadlock.Accept

open Deadlock

def acceptId : InstId := .core "accept"

def result (label : String) (occ legal : Nat) : Edge where
  src := "accept"
  srcState := "idle"
  dst := "accept"
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := Affine.ofNat occ
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat legal)
  cell := .none

def acceptT : Template where
  name := "accept"
  multiplicity := .one
  capacity := Affine.ofNat 1
  priorityCapacity := Affine.ofNat 1
  priorityBound := Affine.ofNat 1
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

def step (label : String) : CompatStep where
  template := "accept"
  fromState := "idle"
  toState := "idle"
  label := label

def tr (label : String) : Transition where
  template := "accept"
  fromState := "idle"
  label := label
  program := []
  toState := "idle"
  acceptsCall := false
  release := 1

def acceptDesc : Description where
  name := "accept"
  freshNames := true
  templates := [acceptT]
  edges := [result "Accepted" 1 1, result "AcceptError" 0 0]
  compatibility := .all
  steps := [step "Accepted", step "AcceptError"]

def acceptImpl : Impl where
  desc := acceptDesc
  transitions := [tr "Accepted", tr "AcceptError"]

/-- Messages of a detached accept completion. -/
def acceptResult (label : String) : Bool :=
  label == "Accepted" || label == "AcceptError"

/-- How many accept completions are queued at the listener. -/
def acceptOutstanding (w : World) : Nat :=
  ((w.st acceptId).box.filter fun m => acceptResult m.label).length

/-- One queued completion, an idle core, and the token that completion spent. -/
def boundFields (w : World) : Bool :=
  !w.crashed &&
    (w.st acceptId).life == .alive &&
    (w.st acceptId).phase == .idle &&
    (w.st acceptId).typestate == "idle" &&
    (w.st acceptId).parked == [] &&
    (w.st acceptId).prio == [] &&
    (w.st acceptId).box.length ≤ 1 &&
    ((w.st acceptId).box.all fun m => acceptResult m.label) &&
    ((w.st acceptId).tokens "accept" + ((w.st acceptId).box.length : Int)) == 1

theorem accept_checked : checkBool acceptDesc = true ∧ localOkB acceptImpl = true := by
  decide

/-- The completion edges are not waits. -/
theorem accept_no_wait : residualEdges acceptDesc = [] := by
  decide

/-- The outstanding bound of one fits a priority lane sized for one sender. -/
theorem accept_fits_prio : prioSized acceptDesc "accept" 1 = true := by
  decide

/-- The same bound fits the mailbox Lemma 1 uses. -/
theorem accept_fits_occ : l1 acceptDesc "accept" = true := by
  decide

theorem accept_cap (N : Nat) : capBulk acceptDesc N acceptId = 1 := by
  simp [capBulk, acceptId, tname, templateOf, acceptDesc, acceptT, Affine.eval, Affine.ofNat]

/-- A full bulk slot refuses another ingress, whichever label the environment offers.
`simp` rather than `split`: `receiveIngress` binds the actor and the capacity
with `have`, and `split` does not reach the capacity `if` through those. -/
theorem ingress_when_full (I : Impl) (w : World) (dst : InstId) (label : String)
    (hcap : capBulk I.desc w.N dst ≤ (w.st dst).box.length) :
    receiveIngress I w dst label = none := by
  simp [receiveIngress, hcap]

theorem outstanding_le (w : World) (hb : boundFields w = true) : acceptOutstanding w ≤ 1 := by
  simp only [boundFields, Bool.and_eq_true] at hb
  -- The length conjunct is `decide (box.length ≤ 1) = true`, so the inequality
  -- is `of_decide_eq_true`, not a field of `≤`.
  have hshort : (w.st acceptId).box.length ≤ 1 := of_decide_eq_true hb.1.1.2
  have hsub : acceptOutstanding w ≤ (w.st acceptId).box.length :=
    List.Sublist.length_le
      (List.filter_sublist (l := (w.st acceptId).box) (p := fun m => acceptResult m.label))
  exact Nat.le_trans hsub hshort

theorem init_bounded : boundFields (initWorld acceptImpl 0) = true := by
  decide

def after (w : Option World) (a : Action) : Option World :=
  w.bind (apply acceptImpl a)

def trace : Option World :=
  after (after (after (after (some (initWorld acceptImpl 0))
    (.ingress acceptId "Accepted"))
    (.recvBulk acceptId))
    (.ingress acceptId "AcceptError"))
    (.recvBulk acceptId)

def stepLive : Option World → Bool
  | none => false
  | some w =>
    boundFields w && (w.st acceptId).box == [] && (w.st acceptId).phase == Phase.idle && !w.crashed

/-- Both results are delivered, and the listener is still idle and not crashed. -/
theorem both_results_consumed : stepLive trace = true := by
  decide

/-- Capacity 1 refuses a second completion while the first is still queued.
This is the refusal at a full mailbox, not a claim about every reachable world.
`bound_reachable` is that claim. -/
theorem second_completion_refused :
    (match apply acceptImpl (.ingress acceptId "Accepted") (initWorld acceptImpl 0) with
      | none => false
      | some w =>
        acceptOutstanding w == 1 &&
          (apply acceptImpl (.ingress acceptId "AcceptError") w).isNone &&
          (apply acceptImpl (.ingress acceptId "Accepted") w).isNone) = true := by
  decide

theorem outstanding_fits_budgets (w : World) (hb : boundFields w = true) :
    acceptOutstanding w ≤ 1 ∧ prioSized acceptDesc "accept" 1 = true ∧
      l1 acceptDesc "accept" = true :=
  ⟨outstanding_le w hb, accept_fits_prio, accept_fits_occ⟩

/-- `AcceptError` at a neighbouring occupancy. Both arguments are `Affine.ofNat`,
so each is a pure `b` count. -/
def errDesc (occ legal : Nat) : Description :=
  { acceptDesc with edges := [result "Accepted" 1 1, result "AcceptError" occ legal] }

theorem accept_err_one_one : checkBool (errDesc 1 1) = false := by decide

theorem accept_err_one_zero : checkBool (errDesc 1 0) = false := by decide

theorem accept_err_zero_one : checkBool (errDesc 0 1) = false := by decide

/-- What `boundFields` says, as propositions. The mailbox is either empty with
its token, or holds one completion and has spent that token. -/
structure AcceptHold (w : World) : Prop where
  crash : w.crashed = false
  roster : w.roster = [acceptId]
  other : ∀ i, i ≠ acceptId → w.st i = absentActor
  life : (w.st acceptId).life = .alive
  phase : (w.st acceptId).phase = .idle
  ty : (w.st acceptId).typestate = "idle"
  park : (w.st acceptId).parked = []
  prio : (w.st acceptId).prio = []
  mail :
    ((w.st acceptId).box = [] ∧ (w.st acceptId).tokens "accept" = 1) ∨
      (∃ m, (w.st acceptId).box = [m] ∧ acceptResult m.label = true ∧
        m.callFrom = none ∧ m.tombstone = false ∧ m.sender = acceptId ∧
        (w.st acceptId).tokens "accept" = 0)

theorem bound_of_hold (w : World) (h : AcceptHold w) : boundFields w = true := by
  have hc : (!w.crashed) = true := by simp [h.crash]
  have hl : ((w.st acceptId).life == .alive) = true := by simp [h.life]
  have hp : ((w.st acceptId).phase == .idle) = true := by simp [h.phase]
  have ht : ((w.st acceptId).typestate == "idle") = true := by simp [h.ty]
  have hk : ((w.st acceptId).parked == ([] : List Parked)) = true := by simp [h.park]
  have hq : ((w.st acceptId).prio == ([] : List Msg)) = true := by simp [h.prio]
  rcases h.mail with ⟨hbox, htok⟩ | ⟨m, hbox, hres, _, _, _, htok⟩
  · have hlen : decide ((w.st acceptId).box.length ≤ 1) = true := decide_eq_true (by simp [hbox])
    have hall : ((w.st acceptId).box.all fun m => acceptResult m.label) = true := by simp [hbox]
    have hsum : decide ((w.st acceptId).tokens "accept" +
        ((w.st acceptId).box.length : Int) = 1) = true :=
      decide_eq_true (by simp [hbox, htok])
    simp [boundFields, hc, hl, hp, ht, hk, hq, hlen, hall]
    exact of_decide_eq_true hsum
  · have hlen : decide ((w.st acceptId).box.length ≤ 1) = true := decide_eq_true (by simp [hbox])
    have hall : ((w.st acceptId).box.all fun m => acceptResult m.label) = true := by
      simp [hbox, hres]
    have hsum : decide ((w.st acceptId).tokens "accept" +
        ((w.st acceptId).box.length : Int) = 1) = true :=
      decide_eq_true (by simp [hbox, htok])
    simp [boundFields, hc, hl, hp, ht, hk, hq, hlen, hall]
    exact of_decide_eq_true hsum

theorem budget_accept : budget acceptDesc "accept" "accept" = 1 := by decide

theorem debt_accept : debt acceptDesc "accept" "idle" "accept" = 1 := by decide

theorem read_accept (w : World) : readCells acceptDesc w acceptId = w := by
  have hlab : cellLabels acceptDesc "accept" = [] := by decide
  simp [readCells, hlab, tname, acceptId]

theorem roster_accept : coreRoster acceptDesc = [acceptId] := by decide

theorem gate_idle (a : Actor) (h : a.phase = .idle) (hty : a.typestate = "idle") :
    gateHold acceptDesc "accept" "accept" a = 0 := by
  simp [gateHold, tokenHold, h, hty, landFloor, budget_accept, debt_accept]

theorem lone_accept : loneTerminableB acceptDesc "accept" = false := by decide

theorem has_result (label : String) (h : acceptResult label = true) :
    hasIngress acceptDesc "accept" label = true := by
  simp only [acceptResult, Bool.or_eq_true] at h
  rcases h with hA | hE
  · have hl : label = "Accepted" := by simpa [beq_iff_eq] using hA
    subst hl
    decide
  · have hl : label = "AcceptError" := by simpa [beq_iff_eq] using hE
    subst hl
    decide

theorem allow_one (N : Nat) (label : String) (h : acceptResult label = true) :
    Nat.max (ingressAllowance acceptDesc N "accept" label) 1 = 1 := by
  simp only [acceptResult, Bool.or_eq_true] at h
  rcases h with hA | hE
  · have hl : label = "Accepted" := by simpa [beq_iff_eq] using hA
    subst hl
    have hfind : (acceptDesc.edges.find? fun e =>
        e.ingress && e.dst == "accept" && e.label == "Accepted") =
        some (result "Accepted" 1 1) := by decide
    simp [ingressAllowance, hfind, result, Affine.eval, Affine.ofNat, Nat.zero_mul, Nat.zero_add,
      Nat.max_self]
  · have hl : label = "AcceptError" := by simpa [beq_iff_eq] using hE
    subst hl
    have hfind : (acceptDesc.edges.find? fun e =>
        e.ingress && e.dst == "accept" && e.label == "AcceptError") =
        some (result "AcceptError" 0 0) := by decide
    simp [ingressAllowance, hfind, result, Affine.eval, Affine.ofNat, Nat.zero_mul, Nat.add_zero]

theorem accept_no_spawn (w : World) (template : String) : spawn acceptImpl w template = none := by
  cases hname : template == "accept" with
  | false =>
    have hne : ¬"accept" = template := by
      intro h
      simp [beq_iff_eq, h.symm] at hname
    have hto : templateOf acceptDesc template = none := by
      simp [templateOf, acceptDesc, List.findSome?, hne, acceptT]
    simp [spawn, acceptImpl, hto]
  | true =>
    have heq : "accept" = template := by
      have h : template = "accept" := by simpa [beq_iff_eq] using hname
      exact h.symm
    have hto : templateOf acceptDesc template = some acceptT := by
      simp [templateOf, acceptDesc, List.findSome?, heq, acceptT]
    have hmul : (acceptT.multiplicity == .perPeer) = false := by decide
    have hmay : maySpawnRoot acceptDesc w template acceptT = false := by
      simp [maySpawnRoot, hmul]
    simp [spawn, acceptImpl, hto, hmay]

theorem ingress_bad (w : World) (label : String) (hl : (w.st acceptId).life = .alive)
    (hp : (w.st acceptId).phase = .idle) (h : acceptResult label = false) :
    receiveIngress acceptImpl w acceptId label = none := by
  have hno : hasIngress acceptDesc "accept" label = false := by
    cases hA : label == "Accepted" <;> cases hE : label == "AcceptError"
    · have hneA : label ≠ "Accepted" := by simpa [beq_iff_eq] using hA
      have hneE : label ≠ "AcceptError" := by simpa [beq_iff_eq] using hE
      have hL : ("Accepted" == label) = false := by
        cases hcmp : ("Accepted" == label)
        · rfl
        · have heq : "Accepted" = label := by simpa [beq_iff_eq] using hcmp
          exact absurd heq.symm hneA
      have hR : ("AcceptError" == label) = false := by
        cases hcmp : ("AcceptError" == label)
        · rfl
        · have heq : "AcceptError" = label := by simpa [beq_iff_eq] using hcmp
          exact absurd heq.symm hneE
      simp [hasIngress, acceptDesc, result, List.any_cons, List.any_nil, hL, hR]
    · simp [acceptResult, hA, hE] at h
    · simp [acceptResult, hA, hE] at h
    · simp [acceptResult, hA, hE] at h
  simp [receiveIngress, acceptImpl, hl, hp, ingressOpen, hno]

theorem ingress_absent (w : World) (dst : InstId) (label : String)
    (hst : w.st dst = absentActor) : receiveIngress acceptImpl w dst label = none := by
  simp [receiveIngress, hst, absentActor]

/-- An empty mailbox takes one result and spends its token. -/
theorem ingress_empty (w : World) (label : String) (hH : AcceptHold w)
    (hbox : (w.st acceptId).box = []) (htok : (w.st acceptId).tokens "accept" = 1)
    (hr : acceptResult label = true) :
    receiveIngress acceptImpl w acceptId label =
      some (setActor w acceptId { chargeSender (w.st acceptId) "accept" with
        box := (w.st acceptId).box ++
          [{ label := label, sender := acceptId, callFrom := none, reliable := true,
             mid := (w.st acceptId).nextMid }],
        nextMid := (w.st acceptId).nextMid + 1 }) := by
  simp [receiveIngress, acceptImpl, hH.life, hH.phase, ingressOpen, has_result label hr, hbox,
    accept_cap, lone_accept, tname, acceptId,
    gate_idle (w.st acceptId) hH.phase hH.ty, allow_one w.N label hr, htok]

theorem hold_after_ingress (w : World) (label : String) (hH : AcceptHold w)
    (hbox : (w.st acceptId).box = []) (htok : (w.st acceptId).tokens "accept" = 1)
    (hr : acceptResult label = true)
    (hw : receiveIngress acceptImpl w acceptId label = some
      (setActor w acceptId { chargeSender (w.st acceptId) "accept" with
        box := (w.st acceptId).box ++
          [{ label := label, sender := acceptId, callFrom := none, reliable := true,
             mid := (w.st acceptId).nextMid }],
        nextMid := (w.st acceptId).nextMid + 1 }))
    (w' : World) (heq : receiveIngress acceptImpl w acceptId label = some w') : AcceptHold w' := by
  have hw' : w' = setActor w acceptId { chargeSender (w.st acceptId) "accept" with
      box := (w.st acceptId).box ++
        [{ label := label, sender := acceptId, callFrom := none, reliable := true,
           mid := (w.st acceptId).nextMid }],
      nextMid := (w.st acceptId).nextMid + 1 } := by
    rw [hw] at heq
    exact Option.some.inj heq
  let msg : Msg :=
    { label := label, sender := acceptId, callFrom := none, reliable := true, mid := (w.st acceptId).nextMid }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hw', setActor, hH.crash]
  · simp [hw', setActor, hH.roster]
  · intro i hi
    simp [hw', setActor, hi, hH.other i hi]
  · simp [hw', setActor, chargeSender, bumpToken, hH.life]
  · simp [hw', setActor, chargeSender, bumpToken, hH.phase]
  · simp [hw', setActor, chargeSender, bumpToken, hH.ty]
  · simp [hw', setActor, chargeSender, bumpToken, hH.park]
  · simp [hw', setActor, chargeSender, bumpToken, hH.prio]
  · refine Or.inr ⟨msg, ?_, hr, rfl, rfl, rfl, ?_⟩
    · simp [hw', setActor, hbox, msg]
    · simp [hw', setActor, chargeSender, bumpToken, htok, msg]

theorem deliver_result (w : World) (a : Actor) (m : Msg)
    (hl : a.life = .alive) (hty : a.typestate = "idle")
    (hc : m.callFrom = none) (ht : m.tombstone = false) (hs : acceptResult m.label = true) :
    deliver acceptImpl w acceptId a m =
      some (readCells acceptDesc w acceptId,
        { a with oweId := none, phase := .idle, typestate := "idle" }) := by
  cases hA : m.label == "Accepted" <;> cases hE : m.label == "AcceptError" <;>
    simp [acceptResult, hA, hE] at hs <;>
    simp [deliver, hl, hty, hc, ht, findDeliver, findTr, acceptImpl, tr, hA, hE, read_accept]

theorem bulk_one (w : World) (m : Msg) (hH : AcceptHold w)
    (hbox : (w.st acceptId).box = [m]) (hres : acceptResult m.label = true)
    (hc : m.callFrom = none) (ht : m.tombstone = false) (hsend : m.sender = acceptId)
    (htok : (w.st acceptId).tokens "accept" = 0) :
    receiveBulk acceptImpl w acceptId =
      some (creditLive (setActor (readCells acceptDesc w acceptId) acceptId
        { { (w.st acceptId) with box := [] } with oweId := none, phase := .idle, typestate := "idle" })
        "accept" acceptId) := by
  have hdel := deliver_result (readCells acceptDesc w acceptId)
    { (w.st acceptId) with box := [] } m
    (by simp [hH.life]) (by simp [hH.ty]) hc ht hres
  simp [receiveBulk, hH.life, hH.phase, hbox, hH.park, hdel, read_accept, hsend,
    creditLive, budgetHolder]

theorem hold_after_bulk (w : World) (m : Msg) (hH : AcceptHold w)
    (hbox : (w.st acceptId).box = [m]) (hres : acceptResult m.label = true)
    (hc : m.callFrom = none) (ht : m.tombstone = false) (hsend : m.sender = acceptId)
    (htok : (w.st acceptId).tokens "accept" = 0)
    (w' : World) (heq : receiveBulk acceptImpl w acceptId = some w') : AcceptHold w' := by
  have hw := bulk_one w m hH hbox hres hc ht hsend htok
  rw [hw] at heq
  cases heq
  let a' : Actor :=
    { { (w.st acceptId) with box := [] } with oweId := none, phase := .idle, typestate := "idle" }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [creditLive, creditSender, budgetHolder, setActor, hH.crash]
  · simp [creditLive, creditSender, budgetHolder, setActor, hH.roster]
  · intro i hi
    simp [creditLive, creditSender, budgetHolder, setActor, hi, hH.other i hi]
  · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a', hH.life]
  · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a']
  · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a']
  · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a', hH.park]
  · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a', hH.prio]
  · refine Or.inl ⟨?_, ?_⟩
    · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a']
    · simp [creditLive, creditSender, budgetHolder, setActor, bumpToken, a', htok]

theorem runtime_empty (w : World) (hH : AcceptHold w) (hbox : (w.st acceptId).box = []) :
    runtimeBusy acceptImpl w = false := by
  simp [runtimeBusy, hH.roster, receiveBulk, receivePrio, execHead, finishWait, callTimeout,
    hH.life, hH.phase, hbox, hH.park, hH.prio, receivePrioFrom]

theorem hold_init (N : Nat) : AcceptHold (initWorld acceptImpl N) := by
  have hw : initWorld acceptImpl N =
      { N := N, roster := [acceptId], nextIx := fun _ => 0,
        st := fun id => if [acceptId].contains id then initActor acceptDesc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } := by
    simp [initWorld, acceptImpl, roster_accept, read_accept, List.foldl]
  have hmem : ([acceptId].contains acceptId) = true := by simp
  have hact : initActor acceptDesc acceptId =
      withTokens acceptDesc "accept"
        { life := .alive, typestate := "idle", phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 } := by
    simp [initActor, templateOf, acceptDesc, acceptT, tname, acceptId]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hw]
  · simp [hw]
  · intro i hi
    have hc : ([acceptId].contains i) = false := by
      cases i <;> simp [List.contains, hi]
    simp [hw, hc]
  · simp [hw, hmem, hact, withTokens]
  · simp [hw, hmem, hact, withTokens]
  · simp [hw, hmem, hact, withTokens]
  · simp [hw, hmem, hact, withTokens]
  · simp [hw, hmem, hact, withTokens]
  · refine Or.inl ⟨?_, ?_⟩
    · simp [hw, hmem, hact, withTokens]
    · simp [hw, hmem, hact, withTokens, budget_accept]

theorem hold_step (w w' : World) (a : Action) (hH : AcceptHold w)
    (h : apply acceptImpl a w = some w') : AcceptHold w' := by
  have ⟨_, hstep⟩ := apply_step acceptImpl a w w' h
  cases a with
  | ingress dst label =>
    by_cases hd : dst = acceptId
    · subst hd
      rcases hH.mail with ⟨hbox, htok⟩ | ⟨m, hbox, _, _, _, _, _⟩
      · cases hr : acceptResult label with
        | false =>
          simp [stepWorld, ingress_bad w label hH.life hH.phase hr] at hstep
        | true =>
          have hrecv := ingress_empty w label hH hbox htok hr
          exact hold_after_ingress w label hH hbox htok hr hrecv w'
            (by simp [stepWorld] at hstep; exact hstep)
      · have hfull := ingress_when_full acceptImpl w acceptId label (by simp [accept_cap, hbox])
        simp [stepWorld, hfull] at hstep
    · have hst := hH.other dst hd
      simp [stepWorld, ingress_absent w dst label hst] at hstep
  | recvBulk s =>
    by_cases hs : s = acceptId
    · subst hs
      rcases hH.mail with ⟨hbox, _⟩ | ⟨m, hbox, hres, hc, ht, hsend, htok⟩
      · simp [stepWorld, receiveBulk, hH.life, hH.phase, hbox, hH.park] at hstep
      · exact hold_after_bulk w m hH hbox hres hc ht hsend htok w'
          (by simp [stepWorld] at hstep; exact hstep)
    · have hst := hH.other s hs
      simp [stepWorld, receiveBulk, hst, absentActor] at hstep
  | recvPrio s =>
    by_cases hs : s = acceptId
    · subst hs
      simp [stepWorld, receivePrio, hH.life, hH.phase, hH.prio, receivePrioFrom] at hstep
    · have hst := hH.other s hs
      simp [stepWorld, receivePrio, hst, absentActor] at hstep
  | exec s =>
    by_cases hs : s = acceptId
    · subst hs
      simp [stepWorld, execHead, hH.life, hH.phase] at hstep
    · have hst := hH.other s hs
      simp [stepWorld, execHead, hst, absentActor] at hstep
  | finish s =>
    by_cases hs : s = acceptId
    · subst hs
      simp [stepWorld, finishWait, hH.life, hH.phase] at hstep
    · have hst := hH.other s hs
      simp [stepWorld, finishWait, hst, absentActor] at hstep
  | spawn template =>
    simp [stepWorld, accept_no_spawn w template] at hstep
  | callTimeout s =>
    by_cases hs : s = acceptId
    · subst hs
      simp [stepWorld, callTimeout, hH.life, hH.phase] at hstep
    · have hst := hH.other s hs
      simp [stepWorld, callTimeout, hst, absentActor] at hstep
  | stutter =>
    rcases hH.mail with ⟨hbox, _⟩ | ⟨m, hbox, hres, hc, ht, hsend, htok⟩
    · simp [stepWorld, runtime_empty w hH hbox] at hstep
      cases hstep
      exact hH
    · have hbulk := bulk_one w m hH hbox hres hc ht hsend htok
      simp [stepWorld, runtimeBusy, hH.roster, hbulk] at hstep

theorem hold_reachable (N : Nat) (w : World) (h : Reachable acceptImpl N w) : AcceptHold w := by
  induction h with
  | init => exact hold_init N
  | step _ _ _ _ hstep ih => exact hold_step _ _ _ ih hstep

/-- Every world reachable from the initial listener satisfies the outstanding bound. -/
theorem bound_reachable (N : Nat) (w : World) (h : Reachable acceptImpl N w) :
    boundFields w = true :=
  bound_of_hold w (hold_reachable N w h)

end Deadlock.Accept
