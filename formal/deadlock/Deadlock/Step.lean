import Deadlock.Pres
import Deadlock.Mail
import Deadlock.Proof

set_option autoImplicit false

namespace Deadlock

theorem head_rest (D : Description) (template : String) (at_ : BranchAt) (e : Eff) (es : List Eff)
    (h : effectsOk D template at_ (e :: es) = true) : effectsOk D template at_ es = true :=
  effectsOk_tail D template at_ e es h

theorem head_send (D : Description) (t d l : String) (at_ : BranchAt) (n : Nat) (es : List Eff)
    (h : effectsOk D t at_ (.send d l n :: es) = true) :
    hasEdge D t at_.here d .send .blocking l = true ∧ effectsOk D t at_ es = true := by
  simp only [effectsOk, effectOk, Bool.and_eq_true] at h
  exact h

theorem head_call (D : Description) (t d l : String) (at_ : BranchAt) (n : Nat) (na to es : List Eff)
    (h : effectsOk D t at_ (.call d l n na to :: es) = true) :
    hasEdge D t at_.here d .call .blocking l = true ∧
      effectsOk D t (focus at_ at_.notAdmitted) na = true ∧
      effectsOk D t (focus at_ at_.timedOut) to = true ∧ effectsOk D t at_ es = true := by
  simp only [effectsOk, effectOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem head_try (D : Description) (t d l : String) (at_ : BranchAt) (n : Nat) (f g es : List Eff)
    (h : effectsOk D t at_ (.trySend d l n f g :: es) = true) :
    effectsOk D t (focus at_ at_.full) f = true ∧ effectsOk D t (focus at_ at_.gone) g = true ∧
      effectsOk D t at_ es = true := by
  simp only [effectsOk, effectOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem head_peer (D : Description) (t : String) (at_ : BranchAt) (o es : List Eff)
    (h : effectsOk D t at_ (.peer o :: es) = true) :
    effectsOk D t (focus at_ at_.timeout) o = true ∧ effectsOk D t at_ es = true := by
  simp only [effectsOk, effectOk, Bool.and_eq_true] at h
  exact h

theorem findLive_spec (w : World) (name : String) (key : Nat) (id : InstId)
    (h : findLive w name key = some id) : tname id = name ∧ (w.st id).life = .alive := by
  unfold findLive at h
  have hp := List.find?_some h
  cases id with
  | core r => simp at hp
  | peer n k g =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨by simp [tname, hp.1.1], hp.2⟩

theorem route_tname (w : World) (D : Description) (sender : InstId) (dst : String)
    (id : InstId) (h : route w D sender dst = some id) : tname id = dst := by
  unfold route at h
  split at h
  · cases h
  · next t _ =>
    cases hm : t.multiplicity with
    | one =>
      simp only [hm] at h
      split at h
      · cases h
        rfl
      · cases h
    | perPeer =>
      simp only [hm] at h
      cases hk : memberKey sender with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        exact (findLive_spec w dst k id h).1

theorem resolve_tname (D : Description) (w : World) (sender : InstId) (dst : String)
    (id : InstId) (h : resolveId D w sender dst = some id) : tname id = dst := by
  unfold resolveId at h
  split at h
  · cases h
  · next t _ =>
    cases hm : t.multiplicity with
    | one =>
      simp only [hm] at h
      cases h
      rfl
    | perPeer =>
      simp only [hm] at h
      cases hk : memberKey sender with
      | none => simp [hk] at h
      | some k =>
        simp only [hk] at h
        split at h
        · next hfind =>
          cases h
          exact (findLive_spec w dst k _ hfind).1
        · cases h
          rfl

/-- Outcome typestate fields of `k` are the ones `tr` declares. `toState` and
`rest` are not part of the match: `pickState` and `selectCall` rewrite those
and leave the fields. -/
def fieldMatch (tr : Transition) (k : Cont) : Prop :=
  k.toNotAdmitted = tr.toNotAdmitted ∧ k.toTimedOut = tr.toTimedOut ∧
    k.toTimeout = tr.toTimeout ∧ k.toFull = tr.toFull ∧ k.toGone = tr.toGone

/-- `a` stands in a landing state of a transition of its template, and `k`
carries that transition's outcome fields with `toState` equal to the typestate. -/
def srcOk (I : Impl) (id : InstId) (a : Actor) (k : Cont) : Prop :=
  ∃ tr, tr ∈ I.transitions ∧ tr.template = tname id ∧ landsAt tr a.typestate ∧
    fieldMatch tr k ∧ k.toState = a.typestate

/-- The outcome programs a wait still carries are checked at their own branch.
A running actor, and one waiting on an effect, only needs the source witness.
A parked call becomes an `awaitReply` on admission and a `NotAdmitted` on its
deadline, so both of its outcomes are checked. -/
def outcomeOk (I : Impl) (id : InstId) (a : Actor) : Prop :=
  match a.phase with
  | .run k => srcOk I id a k
  | .parked _ isCall k => srcOk I id a k ∧ (isCall = true →
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true)
  | .awaitReply _ k => srcOk I id a k ∧
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true
  | .awaitEffect k => srcOk I id a k
  | .awaitPeer k => srcOk I id a k ∧
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).timeout) k.onTimeout = true
  | _ => True

def OutcomeInv (I : Impl) (w : World) : Prop := ∀ id, outcomeOk I id (w.st id)

/-- An id off the roster has never been spawned: its life is still `absent`. -/
def OpenSlots (w : World) : Prop := ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster

/-- Every outcome typestate a transition names is empty or its `toState`. -/
def OutcomesLand (I : Impl) : Prop :=
  ∀ tr ∈ I.transitions,
    pickState tr.toState tr.toNotAdmitted = tr.toState ∧ pickState tr.toState tr.toTimedOut = tr.toState ∧
      pickState tr.toState tr.toTimeout = tr.toState ∧ pickState tr.toState tr.toFull = tr.toState ∧
      pickState tr.toState tr.toGone = tr.toState

theorem pick_named (fallback specific : String) (h : specific ≠ "") :
    pickState fallback specific = specific := by
  unfold pickState
  split
  · next heq => exact absurd (beq_iff_eq.mp heq) h
  · rfl

/-- An outcome field is a landing state when it is nonempty, and `pickState`
of the empty string stays on the fallback. -/
theorem lands_pick_field (tr : Transition) (fallback specific : String)
    (hl : landsAt tr fallback)
    (hs : specific = tr.toNotAdmitted ∨ specific = tr.toTimedOut ∨ specific = tr.toTimeout ∨
      specific = tr.toFull ∨ specific = tr.toGone) :
    landsAt tr (pickState fallback specific) := by
  unfold pickState
  split
  · exact hl
  · next heq =>
    have hne : specific ≠ "" := by
      intro he
      exact heq (beq_iff_eq.mpr he)
    exact Or.inr ⟨hne, hs⟩

theorem src_ty (I : Impl) (id : InstId) {a b : Actor} (k : Cont)
    (ht : b.typestate = a.typestate) (h : srcOk I id a k) : srcOk I id b k := by
  obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
  exact ⟨tr, hm, htm, by rw [ht]; exact hl, hf, hk.trans ht.symm⟩

theorem src_after (I : Impl) (id : InstId) (a : Actor) (k : Cont) (h : srcOk I id a k) :
    srcOk I id a (afterHead k) := by
  obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
  refine ⟨tr, hm, htm, hl, ?_, ?_⟩
  · unfold fieldMatch at hf ⊢
    simpa [afterHead] using hf
  · simpa [afterHead] using hk

theorem src_lists (I : Impl) (id : InstId) (a : Actor) (k : Cont) (na to o : List Eff)
    (h : srcOk I id a k) :
    srcOk I id a { k with onNotAdmitted := na, onTimedOut := to, onTimeout := o } := by
  obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
  refine ⟨tr, hm, htm, hl, ?_, ?_⟩
  · unfold fieldMatch at hf ⊢
    simpa using hf
  · simpa using hk

theorem src_reply (I : Impl) (id : InstId) (a : Actor) (k : Cont) (r : Option InstId)
    (h : srcOk I id a k) : srcOk I id a { k with replyTo := r } := by
  obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
  refine ⟨tr, hm, htm, hl, ?_, hk⟩
  unfold fieldMatch at hf ⊢
  exact hf

/-- `pickState` of an outcome field stays inside the transition's landing set,
and the updated continuation still carries that transition's fields. -/
theorem src_pick (I : Impl) (id : InstId) (a : Actor) (k : Cont) (rest : List Eff) (specific : String)
    (h : srcOk I id a k)
    (hs : specific = k.toNotAdmitted ∨ specific = k.toTimedOut ∨ specific = k.toTimeout ∨
      specific = k.toFull ∨ specific = k.toGone) :
    let k' := { k with rest := rest, toState := pickState k.toState specific }
    srcOk I id { a with typestate := k'.toState } k' := by
  obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
  refine ⟨tr, hm, htm, ?_, ?_, rfl⟩
  · have hlk : landsAt tr k.toState := by rw [hk]; exact hl
    have hs' : specific = tr.toNotAdmitted ∨ specific = tr.toTimedOut ∨ specific = tr.toTimeout ∨
        specific = tr.toFull ∨ specific = tr.toGone := by
      rcases hs with hs | hs | hs | hs | hs
      · exact Or.inl (hs.trans hf.1)
      · exact Or.inr (Or.inl (hs.trans hf.2.1))
      · exact Or.inr (Or.inr (Or.inl (hs.trans hf.2.2.1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hs.trans hf.2.2.2.1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hs.trans hf.2.2.2.2))))
    simpa using lands_pick_field tr k.toState specific hlk hs'
  · unfold fieldMatch at hf ⊢
    simpa using hf

theorem src_select (I : Impl) (id : InstId) (a : Actor) (k : Cont) (r : CallResult)
    (h : srcOk I id a k) :
    srcOk I id { a with typestate := (selectCall k r).toState } (selectCall k r) := by
  cases r with
  | reply =>
    obtain ⟨tr, hm, htm, hl, hf, hk⟩ := h
    refine ⟨tr, hm, htm, ?_, ?_, ?_⟩
    · simpa [selectCall, hk] using hl
    · unfold fieldMatch at hf ⊢
      simpa [selectCall] using hf
    · simp [selectCall]
  | notAdmitted =>
    simpa [selectCall] using
      src_pick I id a k k.onNotAdmitted k.toNotAdmitted h (Or.inl rfl)
  | timedOut =>
    simpa [selectCall] using
      src_pick I id a k k.onTimedOut k.toTimedOut h (Or.inr (Or.inl rfl))

/-- `proceed` writes `k.toState` on both arms. The pre-state need not equal it.
An empty arm is idle and a nonempty arm runs `k`, so `waitEdge` holds. -/
theorem proceed_any (D : Description) (id : InstId) (a : Actor) (k : Cont)
    (hprog : effectsOk D (tname id) (contAt k) k.rest = true) :
    (proceed a k).typestate = k.toState ∧ (proceed a k).life = a.life ∧
      contTy (proceed a k) ∧ programOk D id (proceed a k) ∧
      waitEdge D id (proceed a k) ∧ notParked (proceed a k).phase ∧
      (proceed a k).parked = a.parked := by
  cases hk : k.rest with
  | nil => simp [proceed, hk, contTy, programOk, waitEdge, notParked]
  | cons _ _ =>
    simp [proceed, hk, contTy, programOk, waitEdge, notParked]
    rw [← hk]
    exact hprog

theorem finish_preds (D : Description) (id : InstId) (a : Actor) (k : Cont) (r : CallResult)
    (hprog : effectsOk D (tname id) (contAt (selectCall k r)) (selectCall k r).rest = true) :
    (finishCall a k r).typestate = (selectCall k r).toState ∧
      (finishCall a k r).life = a.life ∧
      (finishCall a k r).parked = a.parked ∧
      contTy (finishCall a k r) ∧ programOk D id (finishCall a k r) ∧
      waitEdge D id (finishCall a k r) ∧ notParked (finishCall a k r).phase := by
  rcases proceed_any D id a (selectCall k r) hprog with ⟨htyP, hlifeP, hcont, hprogP, hwait, hfree, hpkP⟩
  have hph : (finishCall a k r).phase = (proceed a (selectCall k r)).phase := by simp [finishCall]
  have hty : (finishCall a k r).typestate = (proceed a (selectCall k r)).typestate := by simp [finishCall]
  have hlife : (finishCall a k r).life = (proceed a (selectCall k r)).life := by simp [finishCall]
  have hpk : (finishCall a k r).parked = (proceed a (selectCall k r)).parked := by simp [finishCall]
  refine ⟨hty.trans htyP, hlife.trans hlifeP, hpk.trans hpkP, ?_, ?_, ?_, by rw [hph]; exact hfree⟩
  · unfold contTy at hcont ⊢
    rw [hph, hty]
    exact hcont
  · unfold programOk at hprogP ⊢
    rw [hph]
    exact hprogP
  · unfold waitEdge at hwait ⊢
    rw [hph, hty]
    exact hwait

theorem lands_toState (I : Impl) (hO : OutcomesLand I) (tr : Transition) (htr : tr ∈ I.transitions)
    (s : String) (hs : landsAt tr s) : s = tr.toState := by
  rcases hs with rfl | ⟨hne, hfield⟩
  · rfl
  · rcases hfield with h | h | h | h | h
    · have hne' : tr.toNotAdmitted ≠ "" := by rw [← h]; exact hne
      have hp := (hO tr htr).1
      rw [pick_named tr.toState tr.toNotAdmitted hne'] at hp
      rw [h]; exact hp
    · have hne' : tr.toTimedOut ≠ "" := by rw [← h]; exact hne
      have hp := (hO tr htr).2.1
      rw [pick_named tr.toState tr.toTimedOut hne'] at hp
      rw [h]; exact hp
    · have hne' : tr.toTimeout ≠ "" := by rw [← h]; exact hne
      have hp := (hO tr htr).2.2.1
      rw [pick_named tr.toState tr.toTimeout hne'] at hp
      rw [h]; exact hp
    · have hne' : tr.toFull ≠ "" := by rw [← h]; exact hne
      have hp := (hO tr htr).2.2.2.1
      rw [pick_named tr.toState tr.toFull hne'] at hp
      rw [h]; exact hp
    · have hne' : tr.toGone ≠ "" := by rw [← h]; exact hne
      have hp := (hO tr htr).2.2.2.2
      rw [pick_named tr.toState tr.toGone hne'] at hp
      rw [h]; exact hp

theorem ne_bne (s : String) (h : s ≠ "") : (s != "") = true := by
  cases hb : (s == "") with
  | false => simp [bne, hb]
  | true => exact absurd (beq_iff_eq.mp hb) h

theorem mem_filter {α : Type} (p : α → Bool) (x : α) (xs : List α)
    (hx : x ∈ xs) (hp : p x = true) : x ∈ xs.filter p := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    cases hx with
    | head =>
      rw [List.filter_cons, hp, if_pos rfl]
      exact List.Mem.head _
    | tail _ ht =>
      rw [List.filter_cons]
      cases hy : p y with
      | true =>
        rw [if_pos rfl]
        exact List.Mem.tail _ (ih ht)
      | false =>
        rw [if_neg (by decide : ¬ (false = true))]
        exact ih ht

theorem outcome_mem (tr : Transition) (s : String) (hne : s ≠ "")
    (hs : s = tr.toNotAdmitted ∨ s = tr.toTimedOut ∨ s = tr.toTimeout ∨
      s = tr.toFull ∨ s = tr.toGone) :
    s ∈ outcomeFields tr := by
  unfold outcomeFields
  have hp := ne_bne s hne
  rcases hs with h | h | h | h | h
  · subst h; exact mem_filter (· != "") tr.toNotAdmitted _ (List.Mem.head _) hp
  · subst h; exact mem_filter (· != "") tr.toTimedOut _
      (List.Mem.tail _ (List.Mem.head _)) hp
  · subst h; exact mem_filter (· != "") tr.toTimeout _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hp
  · subst h; exact mem_filter (· != "") tr.toFull _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) hp
  · subst h; exact mem_filter (· != "") tr.toGone _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) hp

theorem lands_mem (tr : Transition) (s : String) (hs : landsAt tr s) : s ∈ landingStates tr := by
  rcases hs with rfl | ⟨hne, hfield⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (outcome_mem tr s hne hfield)

/-- `LocalOk` runs `pairBreaks` on every landing pair, so a move inside that set
is a checked step. -/
theorem landing_pair_nil (I : Impl) (hL : LocalOk I) (g : CompatGroup)
    (hg : g ∈ compatGroups I.desc.compatibility) (tr : Transition) (htr : tr ∈ I.transitions)
    (hrole : g.roles.elem tr.template = true) (s0 s1 : String)
    (hm0 : s0 ∈ landingStates tr) (hm1 : s1 ∈ landingStates tr) (hne : s0 ≠ s1) :
    stepBreaks g { template := tr.template, fromState := s0, toState := s1, label := tr.label } false = [] := by
  have hnil := landing_nil I hL
  cases hmode : I.desc.compatibility with
  | all => simp [compatGroups, hmode] at hg
  | explicit _ => simp [compatGroups, hmode] at hg
  | groups gs =>
    simp only [landingFails, hmode] at hnil
    simp only [compatGroups, hmode] at hg
    have hgrp := flatMap_nil_mem (fun g => I.transitions.flatMap (landingBreaks g)) gs g hnil hg
    have htrb := flatMap_nil_mem (landingBreaks g) I.transitions tr hgrp htr
    unfold landingBreaks pairBreaks at htrb
    rw [hrole] at htrb
    rw [if_pos rfl] at htrb
    have h0 := flatMap_nil_mem _ (landingStates tr) s0 htrb hm0
    have h1 := flatMap_nil_mem _ (landingStates tr) s1 h0 hm1
    have hbb : (s0 == s1) = false := by
      cases hb : (s0 == s1) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb) hne
    rw [hbb] at h1
    rw [if_neg (by decide : ¬ (false = true))] at h1
    exact h1

/-- A `RowOk` derivation is a stored tuple. Declared steps are closed by
`compatFails`. A landing move is closed by `landingFails`, including a move
between two distinct outcome states. -/
theorem row_mem (I : Impl) (hL : LocalOk I) (g : CompatGroup)
    (hg : g ∈ compatGroups I.desc.compatibility) {tup : List RoleState} (hR : RowOk I g tup) :
    tupleMem g.allowed tup = true := by
  induction hR with
  | raw hmem => exact hmem
  | step hpre hstep hrole hf ih =>
    rename_i tup st
    exact step_on_observed g st tup
      (step_in_closure I.desc g st (compat_empty_of_local I hL) hg hstep) ih hrole hf
  | land hpre htr hrole hlook hs0 hs1 ih =>
    rename_i tup tr s0 s1
    by_cases heq : s0 = s1
    · have hfix : substRole tup tr.template s1 = tup := by
        rw [← heq]
        apply substRole_fixed
        intro rs hrs hr
        obtain ⟨a, _, hag⟩ := tupleMem_pick g.allowed tup ih
        exact tuple_role_state a tup tr.template s0 hag hlook rs hrs hr
      simpa [hfix] using ih
    · exact step_on_observed g
        { template := tr.template, fromState := s0, toState := s1, label := tr.label } tup
        (landing_pair_nil I hL g hg tr htr hrole s0 s1 (lands_mem tr s0 hs0) (lands_mem tr s1 hs1) heq)
        ih hrole hlook

def Inv (I : Impl) (w : World) : Prop :=
  SemInv I w ∧ MailInv w ∧ OpenSlots w ∧ OutcomeInv I w ∧ ParentForest w ∧ SealInv w

theorem Inv.forest {I : Impl} {w : World} (h : Inv I w) : ParentForest w := h.2.2.2.2.1

theorem Inv.seal {I : Impl} {w : World} (h : Inv I w) : SealInv w := h.2.2.2.2.2

/-- `Inv` with the tombstone chain waived on `gap`. The other five conjuncts
are unchanged, so a later tombstone enqueue can rebuild `Inv`. -/
structure SealExcept (w : World) (gap : InstId → Prop) : Prop where
  liveParked : ParkedFromLive w
  quiet : DeadQuiet w
  childless : DeadChildless w
  chain : TombGap w gap
  parkedFrom : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender
  hostedMail : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ∈ w.roster

def ExceptInv (I : Impl) (w : World) (gap : InstId → Prop) : Prop :=
  SemInv I w ∧ MailInv w ∧ OpenSlots w ∧ OutcomeInv I w ∧ ParentForest w ∧ SealExcept w gap

theorem ExceptInv.forest {I : Impl} {w : World} {gap : InstId → Prop}
    (h : ExceptInv I w gap) : ParentForest w := h.2.2.2.2.1

theorem ExceptInv.seal {I : Impl} {w : World} {gap : InstId → Prop}
    (h : ExceptInv I w gap) : SealExcept w gap := h.2.2.2.2.2

theorem not_inv_of_parked {I : Impl} {w : World} (h : ¬ ParkedFromLive w) : ¬ Inv I w :=
  fun hI => h hI.seal.liveParked

/-- Life and the parked lanes agree, so a dead sender stays off every live lane. -/
theorem parkedLive_same {w w' : World} (h : ParkedFromLive w)
    (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hk : ∀ i, (w'.st i).parked = (w.st i).parked) : ParkedFromLive w' := by
  intro host p ha hp
  rw [hk host] at hp
  rw [hl p.sender]
  exact h host p (by rw [← hl host]; exact ha) hp

/-- Replacing one actor without changing its life or its parked lane. -/
theorem parkedLive_set (w : World) (id : InstId) (a : Actor) (h : ParkedFromLive w)
    (hlife : a.life = (w.st id).life) (hlist : a.parked = (w.st id).parked) :
    ParkedFromLive (setActor w id a) := by
  intro host p ha hp
  by_cases hh : host = id
  · rw [hh] at ha hp
    rw [setActor_self] at ha hp
    rw [hlist] at hp
    rw [hlife] at ha
    by_cases hs : p.sender = id
    · have h0 := h id p ha hp
      rw [hs] at h0
      rw [hs, setActor_self, hlife]
      exact h0
    · rw [setActor_other w id p.sender a hs]
      exact h id p ha hp
  · rw [setActor_other w id host a hh] at ha hp
    by_cases hs : p.sender = id
    · have h0 := h host p ha hp
      rw [hs] at h0
      rw [hs, setActor_self, hlife]
      exact h0
    · rw [setActor_other w id p.sender a hs]
      exact h host p ha hp

/-- Every parked entry of the new world was already parked, and life is unchanged. -/
theorem parkedLive_sub {w w' : World} (h : ParkedFromLive w)
    (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hk : ∀ host p, p ∈ (w'.st host).parked → p ∈ (w.st host).parked) : ParkedFromLive w' := by
  intro host p ha hp
  rw [hl p.sender]
  exact h host p (by rw [← hl host]; exact ha) (hk host p hp)

/-- One actor's parked lane may gain entries whose sender is not dead. -/
theorem parkedLive_extend (w : World) (id : InstId) (a : Actor) (h : ParkedFromLive w)
    (hlife : a.life = (w.st id).life)
    (hmem : ∀ p, p ∈ a.parked → p ∈ (w.st id).parked ∨ (w.st p.sender).life ≠ .dead) :
    ParkedFromLive (setActor w id a) := by
  intro host q ha hq
  by_cases hh : host = id
  · rw [hh] at ha hq
    rw [setActor_self] at ha hq
    rw [hlife] at ha
    rcases hmem q hq with hold | hliveS
    · by_cases hs : q.sender = id
      · have h0 := h id q ha hold
        rw [hs] at h0
        rw [hs, setActor_self, hlife]
        exact h0
      · rw [setActor_other w id q.sender a hs]
        exact h id q ha hold
    · by_cases hs : q.sender = id
      · rw [hs] at hliveS
        rw [hs, setActor_self, hlife]
        exact hliveS
      · rw [setActor_other w id q.sender a hs]
        exact hliveS
  · rw [setActor_other w id host a hh] at ha hq
    by_cases hs : q.sender = id
    · have h0 := h host q ha hq
      rw [hs] at h0
      rw [hs, setActor_self, hlife]
      exact h0
    · rw [setActor_other w id q.sender a hs]
      exact h host q ha hq

/-- After `crashWorld` no host is alive, so the parked lane of a live host is vacuous. -/
theorem parkedLive_crash (I : Impl) (w : World) (hS : SemInv I w) : ParkedFromLive (crashWorld w) := by
  intro host _ ha _
  exfalso
  by_cases hm : host ∈ w.roster
  · rw [crash_at w host hm] at ha
    by_cases hgo : (w.st host).life = .alive
    · rw [crash_go hgo] at ha
      cases ha
    · rw [crash_stay hgo] at ha
      exact hgo ha
  · rw [crash_off w host hm] at ha
    exact hm (hS.rostered host ha)

theorem parkedLive_init (I : Impl) (N : Nat) : ParkedFromLive (initWorld I N) := by
  intro host p _ hp
  have hempty : ((initWorld I N).st host).parked = [] := init_parked I N host
  rw [hempty] at hp
  cases hp

theorem parkedFrom_same {w w' : World}
    (h : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender)
    (hk : ∀ i, (w'.st i).parked = (w.st i).parked) :
    ∀ host p, p ∈ (w'.st host).parked → p.sender = p.msg.sender := by
  intro host p hp
  exact h host p (by rw [hk host] at hp; exact hp)

theorem parkedFrom_sub {w w' : World}
    (h : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender)
    (hk : ∀ host p, p ∈ (w'.st host).parked → p ∈ (w.st host).parked) :
    ∀ host p, p ∈ (w'.st host).parked → p.sender = p.msg.sender :=
  fun host p hp => h host p (hk host p hp)

theorem parkedFrom_set (w : World) (id : InstId) (a : Actor)
    (h : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender)
    (hpk : a.parked = (w.st id).parked) :
    ∀ host p, p ∈ ((setActor w id a).st host).parked → p.sender = p.msg.sender := by
  intro host p hp
  by_cases hh : host = id
  · rw [hh, setActor_self, hpk] at hp
    exact h id p hp
  · rw [setActor_other w id host a hh] at hp
    exact h host p hp

theorem hostedMail_same {w w' : World}
    (h : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ∈ w.roster)
    (hro : w'.roster = w.roster)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box) (hprio : ∀ i, (w'.st i).prio = (w.st i).prio) :
    ∀ host m, (m ∈ (w'.st host).box ∨ m ∈ (w'.st host).prio) → m.sender ∈ w'.roster := by
  intro host m hm
  rw [hro]
  rcases hm with hm | hm
  · exact h host m (Or.inl (by rw [hbox] at hm; exact hm))
  · exact h host m (Or.inr (by rw [hprio] at hm; exact hm))

theorem hostedMail_set (w : World) (id : InstId) (a : Actor)
    (h : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ∈ w.roster)
    (hbox : ∀ m, m ∈ a.box → m ∈ (w.st id).box ∨ m.sender ∈ w.roster)
    (hprio : ∀ m, m ∈ a.prio → m ∈ (w.st id).prio ∨ m.sender ∈ w.roster) :
    ∀ host m, (m ∈ ((setActor w id a).st host).box ∨ m ∈ ((setActor w id a).st host).prio) →
      m.sender ∈ (setActor w id a).roster := by
  intro host m hm
  show m.sender ∈ w.roster
  by_cases hh : host = id
  · rw [hh] at hm
    rw [setActor_self] at hm
    rcases hm with hm | hm
    · rcases hbox m hm with hold | hnew
      · exact h id m (Or.inl hold)
      · exact hnew
    · rcases hprio m hm with hold | hnew
      · exact h id m (Or.inr hold)
      · exact hnew
  · rw [setActor_other w id host a hh] at hm
    exact h host m hm

theorem quiet_of_crash {w : World} (h : w.crashed = true) : DeadQuiet w := Or.inl h

theorem childless_of_crash {w : World} (h : w.crashed = true) : DeadChildless w := Or.inl h

theorem chain_of_crash {w : World} (h : w.crashed = true) : TombChain w := by
  intro _ hcr _ _
  rw [h] at hcr
  cases hcr

theorem quiet_stable {w w' : World} (h : DeadQuiet w)
    (hcr : w'.crashed = w.crashed) (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box)
    (hpk : ∀ i, (w'.st i).parked = (w.st i).parked) : DeadQuiet w' := by
  rcases h with hcrW | h
  · exact Or.inl (hcr.trans hcrW)
  · refine Or.inr fun id hna => ?_
    have hna0 : (w.st id).life ≠ .alive := by
      intro ha
      exact hna (by rw [hl id]; exact ha)
    rcases h id hna0 with ⟨hb, hp⟩
    exact ⟨by rw [hbox, hb], by rw [hpk, hp]⟩

theorem childless_stable {w w' : World} (h : DeadChildless w)
    (hcr : w'.crashed = w.crashed) (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) : DeadChildless w' := by
  rcases h with hcrW | h
  · exact Or.inl (hcr.trans hcrW)
  · refine Or.inr fun id c hna hp => ?_
    have hna0 : (w.st id).life ≠ .alive := by
      intro ha
      exact hna (by rw [hl id]; exact ha)
    have hp0 : (w.st c).parent = some id := by rw [← hpar c]; exact hp
    rw [hl c]
    exact h id c hna0 hp0

theorem init_not_dead (I : Impl) (N : Nat) (id : InstId) :
    ((initWorld I N).st id).life ≠ .dead := by
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem quiet_init (I : Impl) (N : Nat) : DeadQuiet (initWorld I N) := by
  refine Or.inr fun id _ => ?_
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem childless_init (I : Impl) (N : Nat) : DeadChildless (initWorld I N) := by
  refine Or.inr fun _ c _ hp => ?_
  have hp0 : ((initWorld I N).st c).parent = none := by
    rw [init_base_st]
    split
    · simp [initActor, absentActor, withTokens]
      split <;> simp [withTokens, absentActor]
    · simp [absentActor]
  rw [hp0] at hp
  cases hp

theorem chain_init (I : Impl) (N : Nat) : TombChain (initWorld I N) := by
  intro id _ hd _
  exact absurd hd (init_not_dead I N id)

theorem seal_crash_open (I : Impl) (w : World)
    (hfrom : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender)
    (hhost : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ∈ w.roster)
    (hS : SemInv I w) : SealInv (crashWorld w) where
  liveParked := parkedLive_crash I w hS
  quiet := quiet_of_crash (by simp [crashWorld])
  childless := childless_of_crash (by simp [crashWorld])
  chain := chain_of_crash (by simp [crashWorld])
  parkedFrom := by
    intro host p hp
    have hpk : ((crashWorld w).st host).parked = (w.st host).parked := by
      by_cases hm : host ∈ w.roster
      · rw [crash_at w host hm]
        unfold crashActor
        split <;> rfl
      · rw [crash_off w host hm]
    exact hfrom host p (by rw [← hpk]; exact hp)
  hostedMail := by
    intro host m hm
    have hbox : ((crashWorld w).st host).box = (w.st host).box := by
      by_cases hi : host ∈ w.roster
      · rw [crash_at w host hi]
        unfold crashActor
        split <;> rfl
      · rw [crash_off w host hi]
    have hprio : ((crashWorld w).st host).prio = (w.st host).prio := by
      by_cases hi : host ∈ w.roster
      · rw [crash_at w host hi]
        unfold crashActor
        split <;> rfl
      · rw [crash_off w host hi]
    have hro : (crashWorld w).roster = w.roster := by simp [crashWorld]
    rw [hro]
    rcases hm with hm | hm
    · exact hhost host m (Or.inl (by rw [hbox] at hm; exact hm))
    · exact hhost host m (Or.inr (by rw [hprio] at hm; exact hm))

theorem seal_crash (I : Impl) (w : World) (h : SealInv w) (hS : SemInv I w) :
    SealInv (crashWorld w) :=
  seal_crash_open I w h.parkedFrom h.hostedMail hS

theorem seal_init (I : Impl) (N : Nat) : SealInv (initWorld I N) where
  liveParked := parkedLive_init I N
  quiet := quiet_init I N
  childless := childless_init I N
  chain := chain_init I N
  parkedFrom := by
    intro host p hp
    rw [init_parked I N host] at hp
    cases hp
  hostedMail := by
    intro host m hm
    have hempty : ((initWorld I N).st host).box = [] ∧ ((initWorld I N).st host).prio = [] := by
      rw [init_base_st]
      split
      · simp [initActor, absentActor, withTokens]
        split <;> simp [withTokens, absentActor]
      · simp [absentActor]
    rcases hm with hm | hm
    · rw [hempty.1] at hm
      cases hm
    · rw [hempty.2] at hm
      cases hm

theorem descends_parent (fuel : Nat) {w w' : World}
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) (anc desc : InstId) :
    descends fuel w' anc desc = descends fuel w anc desc := by
  induction fuel generalizing desc with
  | zero => rfl
  | succ fuel ih =>
    simp only [descends]
    by_cases htop : (desc == anc) = true
    · rw [ite_eq_left htop, ite_eq_left htop]
    · rw [ite_eq_right htop, ite_eq_right htop]
      rw [hpar desc]
      cases hp : (w.st desc).parent with
      | none =>
        rfl
      | some p =>
        dsimp
        by_cases hanc : (p == anc) = true
        · rw [ite_eq_left hanc, ite_eq_left hanc]
        · rw [ite_eq_right hanc, ite_eq_right hanc]
          by_cases hloop : (p == desc) = true
          · rw [ite_eq_left hloop, ite_eq_left hloop]
          · rw [ite_eq_right hloop, ite_eq_right hloop]
            exact ih p

theorem no_live_descendant (w : World) (hC : DeadChildless w) (hcr : w.crashed = false)
    (fuel : Nat) (anc desc : InstId) (hdead : (w.st anc).life ≠ .alive)
    (hd : descends fuel w anc desc = true) : (w.st desc).life ≠ .alive := by
  induction fuel generalizing desc with
  | zero => simp [descends] at hd
  | succ fuel ih =>
    simp only [descends] at hd
    by_cases heq : (desc == anc) = true
    · rw [ite_eq_left heq] at hd
      cases hd
    · rw [ite_eq_right heq] at hd
      cases hp : (w.st desc).parent with
      | none =>
        rw [hp] at hd
        cases hd
      | some p =>
        rw [hp] at hd
        dsimp at hd
        by_cases hpa : (p == anc) = true
        · rw [ite_eq_left hpa] at hd
          have hps : p = anc := by simpa [beq_iff_eq] using hpa
          rcases hC with hbad | hC
          · rw [hbad] at hcr
            cases hcr
          · exact hC anc desc hdead (by rw [hp, hps])
        · rw [ite_eq_right hpa] at hd
          by_cases hself : (p == desc) = true
          · rw [ite_eq_left hself] at hd
            cases hd
          · rw [ite_eq_right hself] at hd
            have hna : (w.st p).life ≠ .alive := ih p hd
            rcases hC with hbad | hC
            · rw [hbad] at hcr
              cases hcr
            · exact hC p desc hna hp

theorem sealed_live_false (w : World) (hC : DeadChildless w) (hcr : w.crashed = false)
    (origin sender : InstId) (hdead : (w.st origin).life ≠ .alive)
    (halive : (w.st sender).life = .alive) : sealedTogether w origin sender = false := by
  simp only [sealedTogether, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [Bool.eq_false_iff]
    intro heq
    have hsame : origin = sender := by simpa [beq_iff_eq] using heq
    rw [hsame] at hdead
    exact hdead halive
  · rw [Bool.eq_false_iff]
    intro hd
    exact no_live_descendant w hC hcr _ origin sender hdead hd halive

theorem any_pred {α : Type} (xs : List α) (p q : α → Bool) (h : ∀ a, p a = q a) :
    xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [List.any_cons, h a, ih]

theorem flight_parent {w w' : World}
    (hro : w'.roster = w.roster) (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box) (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) (origin : InstId) :
    mailInFlight w' origin = mailInFlight w origin := by
  simp only [mailInFlight, hro]
  refine any_pred w.roster _ _ fun host => ?_
  have hseal : ∀ m : Msg, sealedTogether w' origin m.sender = sealedTogether w origin m.sender := by
    intro m
    simp only [sealedTogether, hro, descends_parent _ hpar]
  have hL : ((w'.st host).life == .alive) = ((w.st host).life == .alive) := by rw [hl host]
  have hB : ((w'.st host).box.any fun m => !m.tombstone && sealedTogether w' origin m.sender) =
      ((w.st host).box.any fun m => !m.tombstone && sealedTogether w origin m.sender) := by
    rw [hbox host]
    exact any_pred _ _ _ fun m => by rw [hseal m]
  have hP : ((w'.st host).prio.any fun m => !m.tombstone && sealedTogether w' origin m.sender) =
      ((w.st host).prio.any fun m => !m.tombstone && sealedTogether w origin m.sender) := by
    rw [hprio host]
    exact any_pred _ _ _ fun m => by rw [hseal m]
  rw [hL, hB, hP]

theorem holds_parent {w w' : World} (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (parent id : InstId) : HoldsTomb w' parent id ↔ HoldsTomb w parent id := by
  simp only [HoldsTomb, hprio]

theorem chain_stable {w w' : World} (h : TombChain w)
    (hcr : w'.crashed = w.crashed) (hro : w'.roster = w.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) : TombChain w' := by
  intro id hc hd hf
  have hc0 : w.crashed = false := by rw [← hcr]; exact hc
  have hd0 : (w.st id).life = .dead := by rw [← hl id]; exact hd
  have hf0 : mailInFlight w id = true := by
    rw [← flight_parent hro hl hbox hprio hpar]; exact hf
  have hstep := h id hc0 hd0 hf0
  cases hp : (w'.st id).parent with
  | none =>
    have hnone : (w.st id).parent = none := by rw [← hpar id, hp]
    simp [hnone] at hstep
    simp [hp]
  | some p =>
    have hsome : (w.st id).parent = some p := by rw [← hpar id, hp]
    simp [hsome] at hstep
    simp [hp]
    rcases hstep with ⟨ha, ht⟩ | ⟨hna, hfP⟩
    · exact Or.inl ⟨by rw [hl p]; exact ha, (holds_parent hprio p id).2 ht⟩
    · exact Or.inr ⟨by
        intro ha
        exact hna (by rw [← hl p]; exact ha), by
        rw [flight_parent hro hl hbox hprio hpar]; exact hfP⟩

theorem seal_set_keep {w : World} {id : InstId} {a : Actor} (h : SealInv w)
    (hl : a.life = (w.st id).life) (hbox : a.box = (w.st id).box)
    (hprio : a.prio = (w.st id).prio) (hpk : a.parked = (w.st id).parked)
    (hpar : a.parent = (w.st id).parent) : SealInv (setActor w id a) := by
  have hlift : ∀ i, ((setActor w id a).st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hl]
    · rw [setActor_other w id i a hi]
  have hboxA : ∀ i, ((setActor w id a).st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hbox]
    · rw [setActor_other w id i a hi]
  have hprioA : ∀ i, ((setActor w id a).st i).prio = (w.st i).prio := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hprio]
    · rw [setActor_other w id i a hi]
  have hpkA : ∀ i, ((setActor w id a).st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hpk]
    · rw [setActor_other w id i a hi]
  have hparA : ∀ i, ((setActor w id a).st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hpar]
    · rw [setActor_other w id i a hi]
  exact {
    liveParked := parkedLive_set w id a h.liveParked hl hpk
    quiet := quiet_stable h.quiet rfl hlift hboxA hpkA
    childless := childless_stable h.childless rfl hlift hparA
    chain := chain_stable h.chain rfl rfl hlift hboxA hprioA hparA
    parkedFrom := parkedFrom_set w id a h.parkedFrom hpk
    hostedMail := hostedMail_set w id a h.hostedMail
      (fun m hm => Or.inl (by rw [hbox] at hm; exact hm))
      (fun m hm => Or.inl (by rw [hprio] at hm; exact hm))
  }


/-- A non-alive actor keeps an empty mailbox when only live actors change queues. -/
theorem quiet_live {w w' : World} (h : DeadQuiet w) (hcr : w'.crashed = w.crashed)
    (hl : ∀ i, (w'.st i).life ≠ .alive → (w.st i).life ≠ .alive)
    (hbox : ∀ i, (w.st i).life ≠ .alive → (w'.st i).box = (w.st i).box)
    (hpk : ∀ i, (w.st i).life ≠ .alive → (w'.st i).parked = (w.st i).parked) :
    DeadQuiet w' := by
  rcases h with hcrW | h
  · exact Or.inl (hcr.trans hcrW)
  · refine Or.inr fun id hna => ?_
    have hna0 : (w.st id).life ≠ .alive := hl id hna
    rcases h id hna0 with ⟨hb, hp⟩
    exact ⟨(hbox id hna0).trans hb, (hpk id hna0).trans hp⟩

/-- `ex` is the one actor that becomes not alive, and its mailbox is emptied. -/
theorem quiet_kill {w w' : World} {ex : InstId} (h : DeadQuiet w)
    (hcr : w'.crashed = w.crashed)
    (hl : ∀ i, i ≠ ex → (w'.st i).life = (w.st i).life)
    (hbox : ∀ i, i ≠ ex → (w'.st i).box = (w.st i).box)
    (hpk : ∀ i, i ≠ ex → (w'.st i).parked = (w.st i).parked)
    (hemptyB : (w'.st ex).box = []) (hemptyK : (w'.st ex).parked = []) : DeadQuiet w' := by
  rcases h with hcrW | hq
  · exact Or.inl (hcr.trans hcrW)
  · refine Or.inr fun id hna => ?_
    by_cases hi : id = ex
    · rw [hi]
      exact ⟨hemptyB, hemptyK⟩
    · have hna0 : (w.st id).life ≠ .alive := by
        intro ha
        exact hna (by rw [hl id hi]; exact ha)
      rcases hq id hna0 with ⟨hb, hp⟩
      exact ⟨(hbox id hi).trans hb, (hpk id hi).trans hp⟩

/-- A newly dead actor keeps `DeadChildless` when its children were already not alive. -/
theorem childless_kill {w w' : World} {ex : InstId} (h : DeadChildless w)
    (hcr : w'.crashed = w.crashed)
    (hl : ∀ i, i ≠ ex → (w'.st i).life = (w.st i).life)
    (hex : (w'.st ex).life ≠ .alive)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hkids : ∀ c, c ≠ ex → (w.st c).parent = some ex → (w.st c).life ≠ .alive) : DeadChildless w' := by
  rcases h with hcrW | hq
  · exact Or.inl (hcr.trans hcrW)
  · refine Or.inr fun id c hna hp => ?_
    by_cases hid : id = ex
    · rw [hid] at hp
      have hp0 : (w.st c).parent = some ex := by rw [← hpar c]; exact hp
      by_cases hc : c = ex
      · rw [hc]
        exact hex
      · rw [hl c hc]
        exact hkids c hc hp0
    · have hna0 : (w.st id).life ≠ .alive := by
        intro ha
        exact hna (by rw [hl id hid]; exact ha)
      have hp0 : (w.st c).parent = some id := by rw [← hpar c]; exact hp
      by_cases hc : c = ex
      · rw [hc]
        exact hex
      · rw [hl c hc]
        exact hq id c hna0 hp0

theorem nodup_length_le {α : Type} [DecidableEq α] (xs ys : List α) (hnd : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => exact Nat.le_refl 0
    | cons x _ =>
      exact absurd (hsub x (List.mem_cons_self (a := x))) (List.not_mem_nil (a := x))
  | cons y ys ih =>
    by_cases hy : y ∈ xs
    · have hsub' : ∀ x, x ∈ xs.erase y → x ∈ ys := by
        intro x hx
        have hx0 : x ∈ xs := List.mem_of_mem_erase hx
        have hne : x ≠ y := by
          intro hxy
          rw [hxy] at hx
          exact List.Nodup.not_mem_erase hnd hx
        cases List.mem_cons.mp (hsub x hx0) with
        | inl hxy => exact absurd hxy hne
        | inr h => exact h
      have hlen := ih (xs.erase y) (List.Nodup.erase y hnd) hsub'
      have h1 := List.length_erase_of_mem hy
      have hpos : 0 < xs.length := List.length_pos_of_mem hy
      rw [List.length_cons]
      have hxs : xs.length = (xs.erase y).length + 1 := by omega
      omega
    · have hsub' : ∀ x, x ∈ xs → x ∈ ys := by
        intro x hx
        cases List.mem_cons.mp (hsub x hx) with
        | inl hxy =>
          rw [hxy] at hx
          exact absurd hx hy
        | inr h => exact h
      rw [List.length_cons]
      exact Nat.le_succ_of_le (ih xs hnd hsub')

theorem roster_of_parent {w : World} (hF : ParentForest w) {id p : InstId}
    (hp : (w.st id).parent = some p) : id ∈ w.roster := by
  exact Classical.byContradiction fun h => by
    rw [hF.off id h] at hp
    cases hp

theorem strict_of_descends (w : World) (fuel : Nat) (anc desc : InstId)
    (hd : descends fuel w anc desc = true) : StrictAncestor w desc anc := by
  induction fuel generalizing desc with
  | zero => simp [descends] at hd
  | succ fuel ih =>
    simp only [descends] at hd
    by_cases heq : (desc == anc) = true
    · rw [ite_eq_left heq] at hd
      cases hd
    · rw [ite_eq_right heq] at hd
      cases hp : (w.st desc).parent with
      | none =>
        rw [hp] at hd
        cases hd
      | some p =>
        rw [hp] at hd
        dsimp at hd
        by_cases hpa : (p == anc) = true
        · rw [ite_eq_left hpa] at hd
          have hpe : p = anc := beq_iff_eq.mp hpa
          have hne : desc ≠ anc := by
            intro h
            exact heq (beq_iff_eq.mpr h)
          exact StrictAncestor.edge ⟨by rw [hp, hpe], hne⟩
        · rw [ite_eq_right hpa] at hd
          by_cases hself : (p == desc) = true
          · rw [ite_eq_left hself] at hd
            cases hd
          · rw [ite_eq_right hself] at hd
            have hne : p ≠ desc := by
              intro h
              exact hself (beq_iff_eq.mpr h)
            exact StrictAncestor.tail ⟨hp, hne.symm⟩ (ih p hd)

/-- The ancestor walk is a duplicate-free roster chain, and `descends` accepts it
once the fuel covers that chain. -/
theorem anc_chain (w : World) (hF : ParentForest w) {desc anc : InstId}
    (h : StrictAncestor w desc anc) :
    ∃ xs : List InstId, xs.Nodup ∧ desc ∈ xs ∧ anc ∈ xs ∧
      (∀ x, x ∈ xs → x ∈ w.roster) ∧
      (∀ x, x ∈ xs → x = desc ∨ StrictAncestor w desc x) ∧
      (∀ fuel, xs.length - 1 ≤ fuel → descends fuel w anc desc = true) := by
  induction h
  case edge d a he =>
    refine ⟨[d, a], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil (a := a), List.nodup_nil⟩⟩
      intro hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · exact he.2 hx
      · cases hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact roster_of_parent hF he.1
      · rcases hx with hx | hx
        · rw [hx]
          exact hF.hosted d a he.1
        · cases hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · rcases hx with hx | hx
        · exact Or.inr (by rw [hx]; exact StrictAncestor.edge he)
        · cases hx
    · intro fuel hf
      cases fuel with
      | zero => simp at hf
      | succ _ =>
        simp only [descends]
        have hne : ¬ ((d == a) = true) := by
          intro hb
          exact he.2 (beq_iff_eq.mp hb)
        rw [ite_eq_right hne, he.1]
        dsimp
        rw [ite_eq_left (by simp : (a == a) = true)]
  case tail d mid a he rest ih =>
    obtain ⟨xs, hnd, hmid, hancM, hsub, hrel, hfuel⟩ := ih
    have hnew : d ∉ xs := by
      intro hx
      rcases hrel d hx with hxm | hancD
      · exact he.2 hxm
      · exact ParentAcyclic.no_self hF.wf mid
          (StrictAncestor.trans hancD (StrictAncestor.edge he))
    refine ⟨d :: xs, List.nodup_cons.mpr ⟨hnew, hnd⟩, List.mem_cons_self,
        List.mem_cons_of_mem _ hancM, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact roster_of_parent hF he.1
      · exact hsub x hx
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · rcases hrel x hx with hxm | hancX
        · exact Or.inr (by rw [hxm]; exact StrictAncestor.edge he)
        · exact Or.inr (StrictAncestor.tail he hancX)
    · intro fuel hf
      cases fuel with
      | zero =>
        simp only [List.length_cons] at hf
        have hempty : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hf)
        rw [hempty] at hmid
        cases hmid
      | succ fuel =>
        simp only [descends]
        have hne : ¬ ((d == a) = true) := by
          intro hb
          exact ParentAcyclic.no_self hF.wf a
            (by
              have hpath : StrictAncestor w d a := StrictAncestor.tail he rest
              rw [beq_iff_eq.mp hb] at hpath
              exact hpath)
        rw [ite_eq_right hne, he.1]
        dsimp
        have hpm : ¬ ((mid == a) = true) := by
          intro hb
          exact ParentAcyclic.no_self hF.wf a (by rw [beq_iff_eq.mp hb] at rest; exact rest)
        rw [ite_eq_right hpm]
        have hps : ¬ ((mid == d) = true) := by
          intro hb
          exact he.2 (beq_iff_eq.mp hb).symm
        rw [ite_eq_right hps]
        apply hfuel
        simp only [List.length_cons] at hf
        omega

theorem descends_of_strict (w : World) (hF : ParentForest w) {desc anc : InstId}
    (h : StrictAncestor w desc anc) : descends w.roster.length w anc desc = true := by
  obtain ⟨xs, hnd, _, _, hsub, _, hfuel⟩ := anc_chain w hF h
  apply hfuel
  have hlen : xs.length ≤ w.roster.length := nodup_length_le xs w.roster hnd hsub
  omega

/-- A child of `p`, and anyone sealed with that child, is sealed with `p`. -/
theorem sealed_parent (w : World) (hF : ParentForest w) (id p s : InstId)
    (hpar : (w.st id).parent = some p) (hs : sealedTogether w id s = true) :
    sealedTogether w p s = true := by
  simp only [sealedTogether, Bool.or_eq_true] at hs ⊢
  rcases hs with heq | hd
  · have hids : id = s := beq_iff_eq.mp heq
    by_cases hid : id = p
    · exact Or.inl (beq_iff_eq.mpr (hid.symm.trans hids))
    · have hdsc := descends_of_strict w hF (StrictAncestor.edge ⟨hpar, hid⟩)
      rw [hids] at hdsc
      exact Or.inr hdsc
  · have hstrict := strict_of_descends w _ _ _ hd
    by_cases hid : id = p
    · rw [hid] at hstrict
      exact Or.inr (descends_of_strict w hF hstrict)
    · exact Or.inr (descends_of_strict w hF
        (StrictAncestor.trans hstrict (StrictAncestor.edge ⟨hpar, hid⟩)))

theorem sealed_eq {w w' : World} (hro : w'.roster = w.roster)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) (a b : InstId) :
    sealedTogether w' a b = sealedTogether w a b := by
  simp only [sealedTogether]
  rw [hro]
  exact congrArg (fun d => (a == b) || d) (descends_parent w.roster.length hpar a b)

theorem flight_of_msg (w : World) (origin host : InstId) (m : Msg)
    (hhost : host ∈ w.roster) (hlive : (w.st host).life = .alive)
    (ht : m.tombstone = false) (hs : sealedTogether w origin m.sender = true)
    (hm : m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) : mailInFlight w origin = true := by
  simp only [mailInFlight]
  apply _root_.List.any_eq_true.mpr
  refine ⟨host, hhost, ?_⟩
  have hlB : ((w.st host).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  have hhit : (!m.tombstone && sealedTogether w origin m.sender) = true := by simp [ht, hs]
  have hqs : ((w.st host).box.any fun m => !m.tombstone && sealedTogether w origin m.sender) = true ∨
      ((w.st host).prio.any fun m => !m.tombstone && sealedTogether w origin m.sender) = true := by
    rcases hm with hm | hm
    · exact Or.inl (_root_.List.any_eq_true.mpr ⟨m, hm, hhit⟩)
    · exact Or.inr (_root_.List.any_eq_true.mpr ⟨m, hm, hhit⟩)
  rw [hlB, Bool.true_and]
  rcases hqs with hqs | hqs
  · simp [hqs]
  · simp [hqs]

theorem flight_witness (w : World) (origin : InstId) (hf : mailInFlight w origin = true) :
    ∃ host m, host ∈ w.roster ∧ (w.st host).life = .alive ∧ m.tombstone = false ∧
      sealedTogether w origin m.sender = true ∧
      (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) := by
  simp only [mailInFlight, _root_.List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true] at hf
  obtain ⟨host, hhost, hlB, hqs⟩ := hf
  have hlive : (w.st host).life = .alive := beq_iff_eq.mp hlB
  rcases hqs with hb | hp
  · obtain ⟨m, hm, hnot, hs⟩ := hb
    have ht : m.tombstone = false := by simpa [Bool.not_eq_true'] using hnot
    exact ⟨host, m, hhost, hlive, ht, hs, Or.inl hm⟩
  · obtain ⟨m, hm, hnot, hs⟩ := hp
    have ht : m.tombstone = false := by simpa [Bool.not_eq_true'] using hnot
    exact ⟨host, m, hhost, hlive, ht, hs, Or.inr hm⟩

/-- Mail of a child is mail of its parent: the sender is sealed with both. -/
theorem flight_ancestor (w : World) (hF : ParentForest w) (id p : InstId)
    (hpar : (w.st id).parent = some p) (hf : mailInFlight w id = true) :
    mailInFlight w p = true := by
  obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w id hf
  exact flight_of_msg w p host m hhost hlive ht (sealed_parent w hF id p m.sender hpar hs) hm

theorem fresh_miss (w : World) (hC : DeadChildless w) (hcr : w.crashed = false)
    (origin : InstId) (m : Msg) (hdead : (w.st origin).life ≠ .alive)
    (hfresh : m.tombstone = true ∨ (w.st m.sender).life = .alive) :
    (!m.tombstone && sealedTogether w origin m.sender) = false := by
  rcases hfresh with ht | ha
  · simp [ht]
  · rw [sealed_live_false w hC hcr origin m.sender hdead ha]
    simp

/-- A queue edit that only adds a tombstone or mail from a live sender, and that
drops a tombstone only once that sender's mail is already gone. Lives and
parents stay. The parent's flight is the child's flight, via `sealed_parent`. -/
theorem chain_edit {w w' : World} (h : TombChain w) (hC : DeadChildless w) (hF : ParentForest w)
    (hcr : w'.crashed = w.crashed) (hro : w'.roster = w.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hnewB : ∀ i m, m ∈ (w'.st i).box →
      (∃ m', m' ∈ (w.st i).box ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hnewP : ∀ i m, m ∈ (w'.st i).prio →
      (∃ m', m' ∈ (w.st i).prio ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hkeep : ∀ parent id, HoldsTomb w parent id →
      HoldsTomb w' parent id ∨ mailInFlight w id = false) : TombChain w' := by
  intro id hc hd hf
  have hc0 : w.crashed = false := by rw [← hcr]; exact hc
  have hd0 : (w.st id).life = .dead := by rw [← hl id]; exact hd
  have hna : (w.st id).life ≠ .alive := by
    intro ha
    rw [hd0] at ha
    cases ha
  have hF' : ParentForest w' := ParentForest.parents hF hpar hro
  have hback : mailInFlight w id = true := by
    obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w' id hf
    have hhost0 : host ∈ w.roster := by rw [← hro]; exact hhost
    have hlive0 : (w.st host).life = .alive := by rw [← hl host]; exact hlive
    have hseal : sealedTogether w id m.sender = true := by
      rw [← sealed_eq hro hpar id m.sender]; exact hs
    rcases hm with hm | hm
    · rcases hnewB host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inl hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
    · rcases hnewP host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inr hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
  have hstep := h id hc0 hd0 hback
  cases hp : (w'.st id).parent with
  | none =>
    have hnone : (w.st id).parent = none := by rw [← hpar id, hp]
    simp [hnone] at hstep
    simp [hp]
  | some p =>
    have hsome : (w.st id).parent = some p := by rw [← hpar id, hp]
    simp [hsome] at hstep
    simp [hp]
    rcases hstep with ⟨ha, htomb⟩ | ⟨hdeadP, _⟩
    · rcases hkeep p id htomb with hhold | hgone
      · exact Or.inl ⟨by rw [hl p]; exact ha, hhold⟩
      · simp [hback] at hgone
    · exact Or.inr ⟨by
        intro ha
        exact hdeadP (by rw [← hl p]; exact ha),
        flight_ancestor w' hF' id p (by rw [hp]) hf⟩

/-- The same queue edit, read on a chain that already exempts `gap`. The exemption
does not grow: lives and parents stay, so an id outside `gap` stays outside it. -/
theorem chain_gap_keep {w w' : World} {gap : InstId → Prop}
    (h : TombGap w gap) (hC : DeadChildless w) (hF : ParentForest w)
    (hcr : w'.crashed = w.crashed) (hro : w'.roster = w.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hnewB : ∀ i m, m ∈ (w'.st i).box →
      (∃ m', m' ∈ (w.st i).box ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hnewP : ∀ i m, m ∈ (w'.st i).prio →
      (∃ m', m' ∈ (w.st i).prio ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hkeep : ∀ parent id, HoldsTomb w parent id →
      HoldsTomb w' parent id ∨ mailInFlight w id = false) : TombGap w' gap := by
  intro id hc hd hf hng
  have hc0 : w.crashed = false := by rw [← hcr]; exact hc
  have hd0 : (w.st id).life = .dead := by rw [← hl id]; exact hd
  have hna : (w.st id).life ≠ .alive := by
    intro ha
    rw [hd0] at ha
    cases ha
  have hF' : ParentForest w' := ParentForest.parents hF hpar hro
  have hback : mailInFlight w id = true := by
    obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w' id hf
    have hhost0 : host ∈ w.roster := by rw [← hro]; exact hhost
    have hlive0 : (w.st host).life = .alive := by rw [← hl host]; exact hlive
    have hseal : sealedTogether w id m.sender = true := by
      rw [← sealed_eq hro hpar id m.sender]; exact hs
    rcases hm with hm | hm
    · rcases hnewB host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inl hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
    · rcases hnewP host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inr hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
  have hstep := h id hc0 hd0 hback hng
  cases hp : (w'.st id).parent with
  | none =>
    have hnone : (w.st id).parent = none := by rw [← hpar id, hp]
    simp [hnone] at hstep
    simp [hp]
  | some p =>
    have hsome : (w.st id).parent = some p := by rw [← hpar id, hp]
    simp [hsome] at hstep
    simp [hp]
    rcases hstep with ⟨ha, htomb⟩ | ⟨hdeadP, _⟩
    · rcases hkeep p id htomb with hhold | hgone
      · exact Or.inl ⟨by rw [hl p]; exact ha, hhold⟩
      · simp [hback] at hgone
    · exact Or.inr ⟨by
        intro ha
        exact hdeadP (by rw [← hl p]; exact ha),
        flight_ancestor w' hF' id p (by rw [hp]) hf⟩

/-- One exempt id meets the chain, so the exemption is gone. -/
theorem chain_close {w : World} {ex : InstId} (h : TombGap w (fun i => i = ex))
    (hfix : mailInFlight w ex = true →
      match (w.st ex).parent with
      | none => True
      | some p =>
          ((w.st p).life = .alive ∧ HoldsTomb w p ex) ∨
          ((w.st p).life ≠ .alive ∧ mailInFlight w p = true)) : TombChain w := by
  intro id hc hd hf
  by_cases hi : id = ex
  · subst hi
    exact hfix hf
  · exact h id hc hd hf hi

/-- Killing `ex` drops its tombstone and every tombstone it held. A child of
`ex` is repaired, because `ex` is now the dead parent whose own mail stays in
flight. `ex` itself is the new gap: its tombstone has not been queued. -/
theorem chain_gap_kill {w w' : World} {gap : InstId → Prop} {ex : InstId}
    (h : TombGap w gap) (hC : DeadChildless w) (hF : ParentForest w)
    (hcr : w'.crashed = w.crashed) (hro : w'.roster = w.roster)
    (hex : (w'.st ex).life = .dead)
    (hl : ∀ i, i ≠ ex → (w'.st i).life = (w.st i).life)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hnewB : ∀ i m, m ∈ (w'.st i).box →
      (∃ m', m' ∈ (w.st i).box ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hnewP : ∀ i m, m ∈ (w'.st i).prio →
      (∃ m', m' ∈ (w.st i).prio ∧ m'.sender = m.sender ∧ m'.tombstone = m.tombstone) ∨
        m.tombstone = true ∨ (w.st m.sender).life = .alive)
    (hkeep : ∀ parent id, parent ≠ ex → HoldsTomb w parent id →
      HoldsTomb w' parent id ∨ mailInFlight w id = false) :
    TombGap w' (fun i => i = ex ∨ gap i ∧ (w.st i).parent ≠ some ex) := by
  intro id hc hd hf hgap
  have hne : id ≠ ex := by
    intro heq
    exact hgap (Or.inl heq)
  have hc0 : w.crashed = false := by rw [← hcr]; exact hc
  have hd0 : (w.st id).life = .dead := by rw [← hl id hne]; exact hd
  have hna : (w.st id).life ≠ .alive := by
    intro ha
    rw [hd0] at ha
    cases ha
  have hF' : ParentForest w' := ParentForest.parents hF hpar hro
  have hback : mailInFlight w id = true := by
    obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w' id hf
    have hneH : host ≠ ex := by
      intro heq
      rw [heq, hex] at hlive
      cases hlive
    have hhost0 : host ∈ w.roster := by rw [← hro]; exact hhost
    have hlive0 : (w.st host).life = .alive := by rw [← hl host hneH]; exact hlive
    have hseal : sealedTogether w id m.sender = true := by
      rw [← sealed_eq hro hpar id m.sender]; exact hs
    rcases hm with hm | hm
    · rcases hnewB host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inl hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
    · rcases hnewP host m hm with ⟨m', hm', hsnd, htom⟩ | hfresh
      · have ht' : m'.tombstone = false := by rw [htom]; exact ht
        have hs' : sealedTogether w id m'.sender = true := by rw [hsnd]; exact hseal
        exact flight_of_msg w id host m' hhost0 hlive0 ht' hs' (Or.inr hm')
      · have hbad := fresh_miss w hC hc0 id m hna hfresh
        have hhit : (!m.tombstone && sealedTogether w' id m.sender) = true := by simp [ht, hs]
        rw [sealed_eq hro hpar id m.sender] at hhit
        rw [hbad] at hhit
        cases hhit
  cases hp : (w'.st id).parent with
  | none =>
    have hng : ¬ gap id := by
      intro hg
      apply hgap
      refine Or.inr ⟨hg, ?_⟩
      rw [← hpar id, hp]
      intro hbad
      cases hbad
    have hnone : (w.st id).parent = none := by rw [← hpar id, hp]
    have hstep := h id hc0 hd0 hback hng
    simp [hnone] at hstep
    simp [hp]
  | some p =>
    by_cases hpx : p = ex
    · rw [hpx]
      refine Or.inr ⟨?_, flight_ancestor w' hF' id ex (by rw [hp, hpx]) hf⟩
      intro ha
      rw [hex] at ha
      cases ha
    · have hng : ¬ gap id := by
        intro hg
        apply hgap
        refine Or.inr ⟨hg, ?_⟩
        rw [← hpar id, hp]
        intro heq
        cases heq
        exact hpx rfl
      have hsome : (w.st id).parent = some p := by rw [← hpar id, hp]
      have hstep := h id hc0 hd0 hback hng
      simp [hsome] at hstep
      simp [hp]
      rcases hstep with ⟨ha, htomb⟩ | ⟨hdeadP, _⟩
      · rcases hkeep p id hpx htomb with hhold | hgone
        · exact Or.inl ⟨by rw [hl p hpx]; exact ha, hhold⟩
        · simp [hback] at hgone
      · exact Or.inr ⟨by
          intro ha
          exact hdeadP (by rw [← hl p hpx]; exact ha),
          flight_ancestor w' hF' id p (by rw [hp]) hf⟩

def Step (I : Impl) (w w' : World) : Prop :=
  ∃ a, apply I a w = some w'

theorem contTy_congr {a b : Actor} (hp : a.phase = b.phase) (ht : a.typestate = b.typestate)
    (h : contTy b) : contTy a := by
  unfold contTy at h ⊢
  rw [hp, ht]
  exact h

theorem programOk_congr (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (h : programOk D id b) : programOk D id a := by
  unfold programOk at h ⊢
  rw [hp]
  exact h

theorem waitEdge_congr (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) (h : waitEdge D id b) :
    waitEdge D id a := by
  unfold waitEdge at h ⊢
  rw [hp, ht]
  exact h

theorem outcome_congr (I : Impl) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) (h : outcomeOk I id b) :
    outcomeOk I id a := by
  unfold outcomeOk at h ⊢
  rw [hp]
  revert h
  cases b.phase with
  | run k =>
    intro h
    exact src_ty I id k ht h
  | parked d c k =>
    intro h
    exact ⟨src_ty I id k ht h.1, h.2⟩
  | awaitReply d k =>
    intro h
    exact ⟨src_ty I id k ht h.1, h.2⟩
  | awaitEffect k =>
    intro h
    exact src_ty I id k ht h
  | awaitPeer k =>
    intro h
    exact ⟨src_ty I id k ht h.1, h.2⟩
  | idle => intro h; exact h
  | crashed => intro h; exact h

/-- Same `toState`: `srcOk` of the actor that is entered is `srcOk` of the result,
because `proceed` writes that `toState`. -/
theorem outcome_proceed (I : Impl) (id : InstId) (a : Actor) (k : Cont) (h : srcOk I id a k) :
    outcomeOk I id (proceed a k) := by
  cases hk : k.rest with
  | nil => simp [proceed, hk, outcomeOk]
  | cons _ _ =>
    simp only [proceed, hk, outcomeOk]
    obtain ⟨tr, hm, htm, hl, hf, hto⟩ := h
    exact ⟨tr, hm, htm, by rw [hto]; exact hl, hf, rfl⟩

theorem contAt_pick (k : Cont) (r : List Eff) (s : String) :
    contAt { k with rest := r, toState := pickState k.toState s } = focus (contAt k) s := by
  simp [contAt, focus, pickState]

/-- Two worlds that agree on every field the invariant reads. -/
structure Same (w w' : World) : Prop where
  roster : w'.roster = w.roster
  life : ∀ i, (w'.st i).life = (w.st i).life
  ty : ∀ i, (w'.st i).typestate = (w.st i).typestate
  phase : ∀ i, (w'.st i).phase = (w.st i).phase
  parked : ∀ i, (w'.st i).parked = (w.st i).parked
  parent : ∀ i, (w'.st i).parent = (w.st i).parent

theorem same_refl (w : World) : Same w w :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_trans {w1 w2 w3 : World} (h1 : Same w1 w2) (h2 : Same w2 w3) : Same w1 w3 :=
  ⟨h2.roster.trans h1.roster, fun i => (h2.life i).trans (h1.life i),
    fun i => (h2.ty i).trans (h1.ty i), fun i => (h2.phase i).trans (h1.phase i),
    fun i => (h2.parked i).trans (h1.parked i), fun i => (h2.parent i).trans (h1.parent i)⟩

theorem sem_shape (I : Impl) (w w' : World) (hS : SemInv I w) (hr : w'.roster = w.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life) (ht : ∀ i, (w'.st i).typestate = (w.st i).typestate)
    (hp : ∀ i, (w'.st i).phase = (w.st i).phase)
    (hoff : ∀ i, i ∉ w.roster → (w'.st i).parked = (w.st i).parked) : SemInv I w' := by
  apply sem_stable I w w' hS
  · intro _ _ r _
    exact ht _
  · intro _ _ r _
    exact hl _
  · intro i
    exact contTy_congr (hp i) (ht i) (hS.cont i)
  · intro i
    exact programOk_congr I.desc i (hp i) (hS.prog i)
  · intro i
    exact waitEdge_congr I.desc i (hp i) (ht i) (hS.waited i)
  · intro i h
    rw [hp i]
    exact hS.idleOff i (by rw [← hl i]; exact h)
  · intro i h
    rw [hr]
    exact hS.rostered i (by rw [← hl i]; exact h)
  · intro i h
    rw [hr] at h
    rw [hoff i h]
    exact hS.offEmpty i h

theorem mail_shape (w w' : World) (hM : MailInv w)
    (hl : ∀ i, (w'.st i).life = (w.st i).life) (hp : ∀ i, (w'.st i).phase = (w.st i).phase)
    (hk : ∀ i, (w'.st i).parked = (w.st i).parked) : MailInv w' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hm
    rw [hk mb] at hm
    rcases hM.fwd mb p hm with ⟨k, hph⟩ | hh
    · exact Or.inl ⟨k, by rw [hp]; exact hph⟩
    · exact Or.inr (by rw [hl]; exact hh)
  · intro id dst c k hph
    rw [hp id] at hph
    rcases hM.bwd id dst c k hph with ⟨p, hm, hs, hc⟩ | ⟨hc, hd⟩
    · exact Or.inl ⟨p, by rw [hk]; exact hm, hs, hc⟩
    · exact Or.inr ⟨hc, by rw [hl]; exact hd⟩
  · intro mb1 mb2 p1 p2 h1 h2 hs
    rw [hk] at h1 h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs
  · intro mb
    rw [hk]
    exact hM.once mb

theorem open_shape (w w' : World) (hO : OpenSlots w) (hr : ∀ i, i ∈ w.roster → i ∈ w'.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life) : OpenSlots w' := by
  intro i h
  exact hr i (hO i (by rw [← hl i]; exact h))

theorem outcome_shape (I : Impl) (w w' : World) (hO : OutcomeInv I w)
    (hp : ∀ i, (w'.st i).phase = (w.st i).phase)
    (ht : ∀ i, (w'.st i).typestate = (w.st i).typestate) : OutcomeInv I w' :=
  fun i => outcome_congr I i (hp i) (ht i) (hO i)

theorem inv_frame (I : Impl) (w w' : World) (h : Inv I w) (hs : Same w w') (hseal : SealInv w') :
    Inv I w' :=
  ⟨sem_shape I w w' h.1 hs.roster hs.life hs.ty hs.phase (fun i _ => hs.parked i),
    mail_shape w w' h.2.1 hs.life hs.phase hs.parked,
    open_shape w w' h.2.2.1 (fun i hi => by rw [hs.roster]; exact hi) hs.life,
    outcome_shape I w w' h.2.2.2.1 hs.phase hs.ty,
    ParentForest.parents h.forest hs.parent hs.roster, hseal⟩

theorem except_frame (I : Impl) (w w' : World) {gap : InstId → Prop}
    (h : ExceptInv I w gap) (hs : Same w w') (hseal : SealInv w') : Inv I w' :=
  ⟨sem_shape I w w' h.1 hs.roster hs.life hs.ty hs.phase (fun i _ => hs.parked i),
    mail_shape w w' h.2.1 hs.life hs.phase hs.parked,
    open_shape w w' h.2.2.1 (fun i hi => by rw [hs.roster]; exact hi) hs.life,
    outcome_shape I w w' h.2.2.2.1 hs.phase hs.ty,
    ParentForest.parents h.forest hs.parent hs.roster, hseal⟩

theorem inv_same (I : Impl) (w w' : World) (h : Inv I w) (hs : Same w w')
    (hbox : ∀ i, (w'.st i).box = (w.st i).box)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hcr : w'.crashed = w.crashed) : Inv I w' :=
  inv_frame I w w' h hs
    { liveParked := parkedLive_same h.seal.liveParked hs.life hs.parked
      quiet := quiet_stable h.seal.quiet hcr hs.life hbox hs.parked
      childless := childless_stable h.seal.childless hcr hs.life hs.parent
      chain := chain_stable h.seal.chain hcr hs.roster hs.life hbox hprio hs.parent
      parkedFrom := parkedFrom_same h.seal.parkedFrom hs.parked
      hostedMail := hostedMail_same h.seal.hostedMail hs.roster hbox hprio }

theorem same_actor (w : World) (id : InstId) (a : Actor) (hl : a.life = (w.st id).life)
    (ht : a.typestate = (w.st id).typestate) (hp : a.phase = (w.st id).phase)
    (hk : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent) :
    Same w (setActor w id a) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> by_cases hi : i = id <;>
    simp [hi, setActor_self, setActor_other w id i a, hl, ht, hp, hk, hpar]

theorem same_cells (D : Description) (w : World) (id : InstId) : Same w (readCells D w id) :=
  ⟨cellsRoster D w id, fun i => by rw [cellsSt], fun i => by rw [cellsSt], fun i => by rw [cellsSt],
    fun i => by rw [cellsSt], fun i => readCells_parent D w id i⟩

theorem same_note (w : World) (sender : InstId) (dst : String) : Same w (noteStale w sender dst) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_setCell (w : World) (dst label : String) (c : Cell) : Same w (setCell w dst label c) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_credit (w : World) (tmpl : String) (sender : InstId) : Same w (creditSender w tmpl sender) :=
  ⟨rfl, fun i => (credit_rest w tmpl sender i).2.1, fun i => (credit_rest w tmpl sender i).2.2.2.2.2,
    fun i => (credit_rest w tmpl sender i).1, fun i => (credit_rest w tmpl sender i).2.2.2.2.1,
    fun i => creditSender_parent w tmpl sender i⟩

theorem same_refundMsgs (w : World) (name : String) (ms : List Msg) : Same w (refundMsgs w name ms) := by
  induction ms generalizing w with
  | nil => exact same_refl w
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact same_trans (same_credit w name _) (ih _)

theorem same_refundParked (w : World) (name : String) (ps : List Parked) :
    Same w (refundParked w name ps) := by
  induction ps generalizing w with
  | nil => exact same_refl w
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact same_trans (same_credit w name _) (ih _)

theorem open_set (w : World) (id : InstId) (a : Actor) (hO : OpenSlots w) (hmem : id ∈ w.roster) :
    OpenSlots (setActor w id a) := by
  intro i h
  by_cases hi : i = id
  · rw [hi]
    exact hmem
  · rw [setActor_other w id i a hi] at h
    exact hO i h

theorem outcome_set (I : Impl) (w : World) (id : InstId) (a : Actor) (hO : OutcomeInv I w)
    (ha : outcomeOk I id a) : OutcomeInv I (setActor w id a) := by
  intro i
  by_cases hi : i = id
  · rw [hi, setActor_self]
    exact ha
  · rw [setActor_other w id i a hi]
    exact hO i

/-- A live actor that is not parked moves to a phase that is not parked. -/
theorem inv_set_free (I : Impl) (w : World) (id : InstId) (a : Actor) (h : Inv I w)
    (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (hty : a.typestate = (w.st id).typestate)
    (hnew : notParked a.phase) (hlist : a.parked = (w.st id).parked)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hcont : contTy a) (hprog : programOk I.desc id a) (hwait : waitEdge I.desc id a)
    (hout : outcomeOk I id a) (hpar : a.parent = (w.st id).parent) : Inv I (setActor w id a) :=
  ⟨sem_set I w id a h.1 hty (hlife.trans halive.symm) hcont hprog hwait (idleOff_life hlife)
      (Or.inl hlist),
    mail_set_free w id a h.2.1 hfree hnew hlist (hlife.trans halive.symm),
    open_set w id a h.2.2.1 (h.1.rostered id halive),
    outcome_set I w id a h.2.2.2.1 hout,
    ParentForest.setActor h.forest hpar,
    seal_set_keep h.seal (hlife.trans halive.symm) hbox hprio hlist hpar⟩

/-- A live actor that is not parked resumes a checked continuation whose
`toState` is the typestate it already holds. -/
theorem inv_proceed (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (h : Inv I w)
    (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (hty : a.typestate = (w.st id).typestate)
    (hlist : a.parked = (w.st id).parked)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hk : (w.st id).typestate = k.toState)
    (hprog : effectsOk I.desc (tname id) (contAt k) k.rest = true) (hs : srcOk I id a k)
    (hpar : a.parent = (w.st id).parent) :
    Inv I (setActor w id (proceed a k)) := by
  have hp := proceed_ok I.desc id a k (hty.trans hk) hprog
  exact inv_set_free I w id (proceed a k) h halive hfree ((proceed_keeps_life a k).trans hlife)
    (hp.1.trans hty) (proceed_not_parked a k) ((proceed_keeps_parked a k).trans hlist)
    ((proceed_keeps_box a k).trans hbox) ((proceed_keeps_prio a k).trans hprio)
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 (outcome_proceed I id a k hs) ((proceed_parent a k).trans hpar)

/-- A role that is not a core may move to any typestate: no compatibility group names it. -/
theorem sem_noncore (I : Impl) (w : World) (id : InstId) (a : Actor) (hS : SemInv I w)
    (hcore : ∀ r, id ≠ .core r) (hcont : contTy a) (hprog : programOk I.desc id a)
    (hwait : waitEdge I.desc id a) (hoff : a.life ≠ .alive → a.phase = .idle ∨ a.phase = .crashed)
    (hroster : id ∈ w.roster) : SemInv I (setActor w id a) := by
  apply sem_stable I w (setActor w id a) hS
  · intro _ _ r _
    rw [setActor_other w id (.core r) a (Ne.symm (hcore r))]
  · intro _ _ r _
    rw [setActor_other w id (.core r) a (Ne.symm (hcore r))]
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]; exact hcont
    · rw [setActor_other w id i a hi]; exact hS.cont i
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]; exact hprog
    · rw [setActor_other w id i a hi]; exact hS.prog i
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]; exact hwait
    · rw [setActor_other w id i a hi]; exact hS.waited i
  · intro i hdead
    by_cases hi : i = id
    · rw [hi, setActor_self] at hdead ⊢
      exact hoff hdead
    · rw [setActor_other w id i a hi] at hdead ⊢
      exact hS.idleOff i hdead
  · intro i hlive
    by_cases hi : i = id
    · rw [hi]
      exact hroster
    · rw [setActor_other w id i a hi] at hlive
      exact hS.rostered i hlive
  · intro i hmiss
    have hne : i ≠ id := fun he => hmiss (by rw [he]; exact hroster)
    rw [setActor_other w id i a hne]
    exact hS.offEmpty i hmiss

/-- A move inside one transition's landing set. A core uses `sem_land`. A peer
is not a group role, so any typestate keeps `SemInv`. -/
theorem sem_enter (I : Impl) (w : World) (id : InstId) (a : Actor) (tr : Transition)
    (s0 s1 : String) (hS : SemInv I w)
    (hfrom : (w.st id).typestate = s0) (hto : a.typestate = s1)
    (hlife : a.life = (w.st id).life) (htm : tr.template = tname id)
    (hmem : tr ∈ I.transitions) (hs0 : landsAt tr s0) (hs1 : landsAt tr s1)
    (hcont : contTy a) (hprog : programOk I.desc id a) (hwait : waitEdge I.desc id a)
    (hoff : a.life ≠ .alive → a.phase = .idle ∨ a.phase = .crashed)
    (hlist : a.parked = (w.st id).parked) (hroster : id ∈ w.roster) :
    SemInv I (setActor w id a) := by
  cases id with
  | core r =>
    exact sem_land I w r a tr s0 s1 hS hfrom hto hlife (by simpa [tname] using htm) hmem hs0 hs1
      hcont hprog hwait hoff (Or.inl hlist)
  | peer n key g =>
    exact sem_noncore I w _ a hS (fun r => peer_ne_core n key g r) hcont hprog hwait hoff hroster

/-- Enter `k`, whose `toState` may differ from the typestate already held.
Both states land on the same transition, and `k` carries that transition's fields. -/
theorem inv_enter (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (tr : Transition)
    (h : Inv I w) (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (_hty : a.typestate = (w.st id).typestate)
    (hlist : a.parked = (w.st id).parked)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hmem : tr ∈ I.transitions) (htm : tr.template = tname id)
    (hs0 : landsAt tr (w.st id).typestate) (hs1 : landsAt tr k.toState) (hf : fieldMatch tr k)
    (hprog : effectsOk I.desc (tname id) (contAt k) k.rest = true)
    (hpar : a.parent = (w.st id).parent) :
    Inv I (setActor w id (proceed a k)) := by
  rcases proceed_any I.desc id a k hprog with ⟨htyP, hlifeP, hcont, hprogP, hwait, hfreeP, hpkP⟩
  have hS := sem_enter I w id (proceed a k) tr (w.st id).typestate k.toState h.1 rfl htyP
    (hlifeP.trans (hlife.trans halive.symm)) htm hmem hs0 hs1 hcont hprogP hwait
    (idleOff_life (hlifeP.trans hlife)) (hpkP.trans hlist) (h.1.rostered id halive)
  refine ⟨hS,
    mail_set_free w id (proceed a k) h.2.1 hfree hfreeP (hpkP.trans hlist) (hlifeP.trans (hlife.trans halive.symm)),
    open_set w id (proceed a k) h.2.2.1 (h.1.rostered id halive), ?_,
    ParentForest.setActor h.forest ((proceed_parent a k).trans hpar),
    seal_set_keep h.seal ((hlifeP.trans hlife).trans halive.symm)
      ((proceed_keeps_box a k).trans hbox) ((proceed_keeps_prio a k).trans hprio)
      (hpkP.trans hlist) ((proceed_parent a k).trans hpar)⟩
  apply outcome_set I w id (proceed a k) h.2.2.2.1
  cases hk : k.rest with
  | nil => simp [proceed, hk, outcomeOk]
  | cons _ _ =>
    simp only [proceed, hk, outcomeOk]
    exact ⟨tr, hmem, htm, by simpa using hs1, hf, rfl⟩

/-- Enter the continuation `pickState` builds from one outcome field of `k`. -/
theorem inv_pick (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (rest : List Eff) (specific : String) (h : Inv I w)
    (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (hty : a.typestate = (w.st id).typestate)
    (hlist : a.parked = (w.st id).parked)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hs : srcOk I id (w.st id) k)
    (hspec : specific = k.toNotAdmitted ∨ specific = k.toTimedOut ∨ specific = k.toTimeout ∨
      specific = k.toFull ∨ specific = k.toGone)
    (hprog : effectsOk I.desc (tname id)
        (contAt { k with rest := rest, toState := pickState k.toState specific }) rest = true)
    (hpar : a.parent = (w.st id).parent) :
    Inv I (setActor w id (proceed a { k with rest := rest, toState := pickState k.toState specific })) := by
  obtain ⟨tr, hmem, htm, hl, hf, hk⟩ := hs
  have hs' : specific = tr.toNotAdmitted ∨ specific = tr.toTimedOut ∨ specific = tr.toTimeout ∨
      specific = tr.toFull ∨ specific = tr.toGone := by
    rcases hspec with hspec | hspec | hspec | hspec | hspec
    · exact Or.inl (hspec.trans hf.1)
    · exact Or.inr (Or.inl (hspec.trans hf.2.1))
    · exact Or.inr (Or.inr (Or.inl (hspec.trans hf.2.2.1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hspec.trans hf.2.2.2.1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hspec.trans hf.2.2.2.2))))
  have hlk : landsAt tr k.toState := by rw [hk]; exact hl
  have hfield : fieldMatch tr { k with rest := rest, toState := pickState k.toState specific } := by
    unfold fieldMatch at hf ⊢
    simpa using hf
  have hprog' : effectsOk I.desc (tname id)
      (contAt { k with rest := rest, toState := pickState k.toState specific })
      ({ k with rest := rest, toState := pickState k.toState specific }).rest = true := by
    simpa using hprog
  exact inv_enter I w id a _ tr h halive hfree hlife hty hlist hbox hprio hmem htm hl
    (lands_pick_field tr k.toState specific hlk hs') hfield hprog' hpar

theorem contAt_select_na (k : Cont) :
    contAt (selectCall k .notAdmitted) = focus (contAt k) (contAt k).notAdmitted :=
  contAt_pick k _ _

theorem contAt_select_to (k : Cont) :
    contAt (selectCall k .timedOut) = focus (contAt k) (contAt k).timedOut :=
  contAt_pick k _ _

theorem outcome_finish (I : Impl) (id : InstId) (a : Actor) (k : Cont) (r : CallResult)
    (h : srcOk I id a k) : outcomeOk I id (finishCall a k r) := by
  have hs := src_select I id a k r h
  cases hr : (selectCall k r).rest with
  | nil => simp [finishCall, proceed, hr, outcomeOk]
  | cons _ _ =>
    simp only [finishCall, proceed, hr, outcomeOk]
    obtain ⟨tr, hm, htm, hl, hf, hto⟩ := hs
    exact ⟨tr, hm, htm, hl, hf, hto⟩

theorem outcome_await (I : Impl) (id : InstId) (a : Actor) (dst : InstId) (k : Cont)
    (hph : a.phase = .awaitReply dst k) (hs : srcOk I id a k)
    (ht : effectsOk I.desc (tname id) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true) :
    outcomeOk I id a := by
  unfold outcomeOk
  rw [hph]
  exact ⟨hs, ht⟩

theorem outcome_parked (I : Impl) (id : InstId) (a : Actor) (dst : InstId) (c : Bool) (k : Cont)
    (hph : a.phase = .parked dst c k) (hs : srcOk I id a k)
    (hc : c = true →
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
      effectsOk I.desc (tname id) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true) :
    outcomeOk I id a := by
  unfold outcomeOk
  rw [hph]
  exact ⟨hs, hc⟩

/-- A live actor that is not parked leaves a call wait. `.reply` keeps `toState`.
`NotAdmitted` and `TimedOut` may land on the outcome's own typestate. -/
theorem inv_finish (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (r : CallResult)
    (h : Inv I w) (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (hty : a.typestate = (w.st id).typestate)
    (hlist : a.parked = (w.st id).parked)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hs : srcOk I id a k)
    (hprog : effectsOk I.desc (tname id) (contAt (selectCall k r)) (selectCall k r).rest = true)
    (hpar : a.parent = (w.st id).parent) :
    Inv I (setActor w id (finishCall a k r)) := by
  obtain ⟨tr, hmem, htm, hl, hf, hk⟩ := hs
  rcases finish_preds I.desc id a k r hprog with ⟨htyF, hlifeF, hpkF, hcont, hprogF, hwait, hfreeF⟩
  have hl0 : landsAt tr (w.st id).typestate := by
    rw [← hty]
    exact hl
  have hl1 : landsAt tr (selectCall k r).toState := by
    cases r with
    | reply =>
      rw [show (selectCall k .reply).toState = k.toState from rfl, hk]
      exact hl
    | notAdmitted =>
      rw [show (selectCall k .notAdmitted).toState = pickState k.toState k.toNotAdmitted from rfl]
      exact lands_pick_field tr k.toState k.toNotAdmitted (by rw [hk]; exact hl) (Or.inl hf.1)
    | timedOut =>
      rw [show (selectCall k .timedOut).toState = pickState k.toState k.toTimedOut from rfl]
      exact lands_pick_field tr k.toState k.toTimedOut (by rw [hk]; exact hl) (Or.inr (Or.inl hf.2.1))
  have hS := sem_enter I w id (finishCall a k r) tr (w.st id).typestate (selectCall k r).toState h.1
    rfl htyF (hlifeF.trans (hlife.trans halive.symm)) htm hmem hl0 hl1
    hcont hprogF hwait (idleOff_life (hlifeF.trans hlife)) (hpkF.trans hlist) (h.1.rostered id halive)
  refine ⟨hS,
    mail_set_free w id (finishCall a k r) h.2.1 hfree hfreeF (hpkF.trans hlist)
      (hlifeF.trans (hlife.trans halive.symm)),
    open_set w id _ h.2.2.1 (h.1.rostered id halive),
    outcome_set I w id _ h.2.2.2.1 (outcome_finish I id a k r ⟨tr, hmem, htm, hl, hf, hk⟩),
    ParentForest.setActor h.forest ((finishCall_parent a k r).trans hpar),
    seal_set_keep h.seal ((hlifeF.trans hlife).trans halive.symm)
      ((by
          unfold finishCall proceed
          cases (selectCall k r).rest <;> rfl : (finishCall a k r).box = a.box).trans hbox)
      ((by
          unfold finishCall proceed
          cases (selectCall k r).rest <;> rfl : (finishCall a k r).prio = a.prio).trans hprio)
      (hpkF.trans hlist) ((finishCall_parent a k r).trans hpar)⟩

theorem enqueue_roster (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).roster = w.roster := by
  unfold enqueueOrPark
  dsimp only
  cases isCall <;> split <;> (try split) <;> (try split) <;> rfl

theorem enqueue_parent (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).parent = (w.st i).parent := by
  unfold enqueueOrPark
  dsimp only
  cases isCall <;> split <;> (try split) <;> (try split) <;>
    (by_cases hi : i = sender
     · subst hi
       simp [setActor, finishCall_parent, issueCall_parent, chargeSender_parent, proceed_parent]
     · by_cases hd : i = dst
       · subst hd
         simp [setActor, hi, issueCall_parent, chargeSender_parent]
       · simp [setActor, hi, hd])

theorem enqueue_life (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).life = (w.st i).life := by
  unfold enqueueOrPark
  dsimp only
  cases isCall <;> split <;> (try split) <;> (try split) <;>
    (by_cases hi : i = sender
     · subst hi
       simp [setActor, finishCall_life, issueCall, chargeSender, bumpToken, proceed_keeps_life]
     · by_cases hd : i = dst
       · subst hd
         simp [setActor, hi, issueCall, chargeSender, bumpToken]
       · simp [setActor, hi, hd])

theorem enqueue_outcome (I : Impl) (D' : Description) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hO : OutcomeInv I w) (hs : srcOk I sender (w.st sender) k)
    (hcall : isCall = true →
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true) :
    OutcomeInv I (enqueueOrPark w D' sender dst msg isCall k) := by
  have hsrc : ∀ a : Actor, a.typestate = (w.st sender).typestate → srcOk I sender a k :=
    fun a ht => src_ty I sender k ht hs
  have hhost : ∀ stored : Actor, stored.phase = (w.st dst).phase →
      stored.typestate = (w.st dst).typestate →
      OutcomeInv I (setActor w dst stored) :=
    fun stored hp ht => outcome_set I w dst stored hO (outcome_congr I dst hp ht (hO dst))
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · rw [ite_eq_right (fun h => h halive)]
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D' w.N dst)) = true
    · rw [ite_eq_left hroom]
      by_cases hsame : sender = dst
      · subst hsame
        cases isCall
        · simp only [decide_true, ↓reduceIte, Bool.false_eq_true]
          exact outcome_set I w sender _ hO
            (outcome_proceed I sender _ k (hsrc _ (by simp [chargeSender, bumpToken])))
        · simp only [decide_true, ↓reduceIte]
          exact outcome_set I w sender _ hO
            (outcome_await I sender _ sender k rfl
              (hsrc _ (by simp [issueCall, chargeSender, bumpToken])) (hcall rfl).2)
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        cases isCall
        · simp only [hdec, ↓reduceIte, Bool.false_eq_true]
          exact outcome_set I _ sender _ (hhost _ rfl rfl)
            (outcome_proceed I sender _ k (hsrc _ (by simp [chargeSender, bumpToken])))
        · simp only [hdec, ↓reduceIte]
          exact outcome_set I _ sender _ (hhost _ rfl rfl)
            (outcome_await I sender _ dst k rfl
              (hsrc _ (by simp [issueCall, chargeSender, bumpToken])) (hcall rfl).2)
    · rw [ite_eq_right hroom]
      by_cases hsame : sender = dst
      · subst hsame
        simp only [decide_true, ↓reduceIte]
        exact outcome_set I w sender _ hO
          (outcome_parked I sender _ sender isCall k rfl
            (hsrc _ (by cases isCall <;> simp [issueCall, chargeSender, bumpToken])) hcall)
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        simp only [hdec, ↓reduceIte, Bool.false_eq_true]
        exact outcome_set I _ sender _ (hhost _ rfl rfl)
          (outcome_parked I sender _ dst isCall k rfl
            (hsrc _ (by cases isCall <;> simp [issueCall, chargeSender, bumpToken])) hcall)
  · rw [ite_eq_left halive]
    cases isCall
    · rw [ite_eq_right Bool.false_ne_true]
      exact outcome_set I w sender _ hO (outcome_proceed I sender _ k (hsrc _ rfl))
    · rw [ite_eq_left rfl]
      exact outcome_set I w sender _ hO
        (outcome_finish I sender _ k .notAdmitted (hsrc _ (by simp [issueCall])))

/-- `SemInv` for a mailbox write. A dead call target runs `NotAdmitted`, which may
land on a different typestate of the same transition. -/
theorem enqueue_sem_src (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (hS : SemInv I w) (hs : srcOk I sender (w.st sender) k)
    (htail : effectsOk I.desc (tname sender) (contAt k) k.rest = true)
    (hedge : ∃ label, hasEdge I.desc (tname sender) (w.st sender).typestate (tname dst)
      (if isCall then .call else .send) .blocking label = true)
    (hsender : (w.st sender).life = .alive)
    (hna : isCall = true → (w.st dst).life ≠ .alive →
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true) :
    SemInv I (enqueueOrPark w I.desc sender dst msg isCall k) := by
  obtain ⟨tr, hmem, htm, hl, hf, hk⟩ := hs
  by_cases hlive : (w.st dst).life = .alive
  · exact enqueue_sem I w sender dst msg isCall k hS hk.symm htail hedge hsender
      (fun _ hne => absurd hlive hne) hna
  · cases isCall with
    | false =>
      exact enqueue_sem I w sender dst msg false k hS hk.symm htail hedge hsender
        (fun hc => absurd hc Bool.false_ne_true) (fun hc => absurd hc Bool.false_ne_true)
    | true =>
      unfold enqueueOrPark
      rw [ite_eq_left hlive, ite_eq_left rfl]
      have hprog : effectsOk I.desc (tname sender) (contAt (selectCall k .notAdmitted))
          (selectCall k .notAdmitted).rest = true := by
        rw [contAt_select_na]
        simpa [selectCall] using hna rfl hlive
      rcases finish_preds I.desc sender (issueCall (w.st sender)) k .notAdmitted hprog with
        ⟨htyF, hlifeF, hpkF, hcont, hprogF, hwait, _⟩
      have hl1 : landsAt tr (selectCall k .notAdmitted).toState := by
        rw [show (selectCall k .notAdmitted).toState = pickState k.toState k.toNotAdmitted from rfl]
        exact lands_pick_field tr k.toState k.toNotAdmitted (by rw [hk]; exact hl) (Or.inl hf.1)
      have hissue := issueCall_keeps (w.st sender)
      exact sem_enter I w sender (finishCall (issueCall (w.st sender)) k .notAdmitted) tr
        (w.st sender).typestate (selectCall k .notAdmitted).toState hS rfl htyF
        (hlifeF.trans hissue.2.1) htm hmem hl hl1
        hcont hprogF hwait (idleOff_life (hlifeF.trans (hissue.2.1.trans hsender)))
        (hpkF.trans (by simp [issueCall])) (hS.rostered sender hsender)

/-- A send or call parks only for the live sender, or leaves every parked lane as it was. -/
theorem parkedLive_enqueue (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (h : ParkedFromLive w) (hlive : (w.st sender).life = .alive) :
    ParkedFromLive (enqueueOrPark w D sender dst msg isCall k) := by
  have hsend : (w.st sender).life ≠ .dead := by
    rw [hlive]
    intro hd
    cases hd
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · rw [ite_eq_right (fun hne => hne halive)]
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · rw [ite_eq_left hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        cases isCall
        · simp only [decide_true, ↓reduceIte, Bool.false_eq_true]
          apply parkedLive_set
          · exact h
          · rw [proceed_keeps_life, (charge_ok _ _).2.1]
          · rw [proceed_keeps_parked, charge_parked]
        · simp only [decide_true, ↓reduceIte]
          apply parkedLive_set
          · exact h
          · rw [(issueCall_keeps _).2.1, (charge_ok _ _).2.1]
          · rw [show (issueCall (chargeSender (w.st dst) (tname dst))).parked =
              (chargeSender (w.st dst) (tname dst)).parked by simp [issueCall], charge_parked]
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        cases isCall
        · simp only [hdec, ↓reduceIte, Bool.false_eq_true]
          apply parkedLive_set
          · apply parkedLive_set
            · exact h
            · rfl
            · rfl
          · rw [setActor_other w dst sender _ hsame, proceed_keeps_life, (charge_ok _ _).2.1, hlive]
          · rw [setActor_other w dst sender _ hsame, proceed_keeps_parked, charge_parked]
        · simp only [hdec, ↓reduceIte]
          apply parkedLive_set
          · apply parkedLive_set
            · exact h
            · rfl
            · rfl
          · rw [setActor_other w dst sender _ hsame, (issueCall_keeps _).2.1, (charge_ok _ _).2.1, hlive]
          · rw [setActor_other w dst sender _ hsame]
            rw [show (issueCall (chargeSender (w.st sender) (tname dst))).parked =
              (chargeSender (w.st sender) (tname dst)).parked by simp [issueCall]]
            rw [charge_parked]
    · rw [ite_eq_right hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        simp only [decide_true, ↓reduceIte]
        apply parkedLive_extend
        · exact h
        · cases isCall with
          | false => rw [ite_eq_right Bool.false_ne_true, (charge_ok _ _).2.1]
          | true => rw [ite_eq_left rfl, (issueCall_keeps _).2.1, (charge_ok _ _).2.1]
        · intro p hp
          cases isCall with
          | false =>
            rw [ite_eq_right Bool.false_ne_true] at hp
            simp only [chargeSender, bumpToken, List.mem_append, List.mem_singleton] at hp
            rcases hp with hold | rfl
            · exact Or.inl hold
            · exact Or.inr (hsame ▸ hsend)
          | true =>
            rw [ite_eq_left rfl] at hp
            simp only [issueCall, chargeSender, bumpToken, List.mem_append, List.mem_singleton] at hp
            rcases hp with hold | rfl
            · exact Or.inl hold
            · exact Or.inr (hsame ▸ hsend)
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        simp only [hdec, ↓reduceIte, Bool.false_eq_true]
        apply parkedLive_set
        · apply parkedLive_extend w dst
          · exact h
          · rfl
          · intro p hp
            simp only [List.mem_append, List.mem_singleton] at hp
            rcases hp with hold | rfl
            · exact Or.inl hold
            · exact Or.inr hsend
        · rw [setActor_other _ dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
        · rw [setActor_other _ dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
  · rw [ite_eq_left halive]
    cases isCall
    · rw [ite_eq_right Bool.false_ne_true]
      apply parkedLive_set w sender _ h
      · rw [proceed_keeps_life, hlive]
      · rw [proceed_keeps_parked]
    · rw [ite_eq_left rfl]
      apply parkedLive_set w sender _ h
      · simp only [finishCall]
        rw [proceed_keeps_life, (issueCall_keeps _).2.1, hlive]
      · simp only [finishCall]
        rw [proceed_keeps_parked]
        simp [issueCall]

theorem seal_grow_box (w : World) (h : SealInv w) (hF : ParentForest w) (host : InstId)
    (a : Actor) (msg : Msg) (halive : (w.st host).life = .alive)
    (hl : a.life = (w.st host).life) (hparA : a.parent = (w.st host).parent)
    (hpk : a.parked = (w.st host).parked) (hprio : a.prio = (w.st host).prio)
    (hboxA : a.box = (w.st host).box ++ [msg])
    (hfrom : msg.tombstone = true ∨ (w.st msg.sender).life = .alive)
    (hmem : msg.sender ∈ w.roster) : SealInv (setActor w host a) := by
  let w' := setActor w host a
  have hlift : ∀ i, (w'.st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hl]
    · rw [setActor_other w host i a hi]
  have hpar : ∀ i, (w'.st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hparA]
    · rw [setActor_other w host i a hi]
  have hprioA : ∀ i, (w'.st i).prio = (w.st i).prio := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hprio]
    · rw [setActor_other w host i a hi]
  have hpkA : ∀ i, (w'.st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hpk]
    · rw [setActor_other w host i a hi]
  have hdead : ∀ i, (w.st i).life ≠ .alive → (w'.st i).box = (w.st i).box := by
    intro i hna
    by_cases hi : i = host
    · exact absurd (by rw [hi]; exact halive) hna
    · rw [setActor_other w host i a hi]
  refine ⟨parkedLive_same h.liveParked hlift hpkA,
    quiet_live h.quiet rfl (fun i hna ha => hna (by rw [hlift i]; exact ha)) hdead
      (fun i _ => hpkA i),
    childless_stable h.childless rfl hlift hpar,
    chain_edit h.chain h.childless hF rfl rfl hlift hpar ?_ ?_ ?_,
    parkedFrom_same h.parkedFrom hpkA, ?_⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self, hboxA] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
      · have hm' : m = msg := by simpa [List.mem_singleton] using hm
        rw [hm']
        exact Or.inr hfrom
    · rw [setActor_other w host i a hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self, hprio] at hm
      exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
    · rw [setActor_other w host i a hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro parent id ht
    refine Or.inl ?_
    obtain ⟨m, hm, htomb, hsnd⟩ := ht
    refine ⟨m, ?_, htomb, hsnd⟩
    by_cases hp : parent = host
    · rw [hp, setActor_self, hprio]
      exact (by rw [← hp]; exact hm)
    · rw [setActor_other w host parent a hp]
      exact hm
  · intro host' m hm
    rcases hm with hm | hm
    · by_cases hi : host' = host
      · rw [hi, setActor_self, hboxA] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h.hostedMail host' m (Or.inl (by rw [hi]; exact hm))
        · have hm' : m = msg := by simpa [List.mem_singleton] using hm
          rw [hm']
          exact hmem
      · rw [setActor_other w host host' a hi] at hm
        exact h.hostedMail host' m (Or.inl hm)
    · by_cases hi : host' = host
      · rw [hi, setActor_self, hprio] at hm
        exact h.hostedMail host' m (Or.inr (by rw [hi]; exact hm))
      · rw [setActor_other w host host' a hi] at hm
        exact h.hostedMail host' m (Or.inr hm)

theorem seal_park_snoc (w : World) (h : SealInv w) (hF : ParentForest w) (host : InstId)
    (a : Actor) (entry : Parked) (halive : (w.st host).life = .alive)
    (hl : a.life = (w.st host).life) (hparA : a.parent = (w.st host).parent)
    (hboxA : a.box = (w.st host).box) (hprio : a.prio = (w.st host).prio)
    (hpk : a.parked = (w.st host).parked ++ [entry])
    (hfrom : entry.sender = entry.msg.sender)
    (hsend : (w.st entry.sender).life ≠ .dead) : SealInv (setActor w host a) := by
  let w' := setActor w host a
  have hlift : ∀ i, (w'.st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hl]
    · rw [setActor_other w host i a hi]
  have hpar : ∀ i, (w'.st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hparA]
    · rw [setActor_other w host i a hi]
  have hbox : ∀ i, (w'.st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hboxA]
    · rw [setActor_other w host i a hi]
  have hprioA : ∀ i, (w'.st i).prio = (w.st i).prio := by
    intro i
    by_cases hi : i = host
    · rw [hi, setActor_self, hprio]
    · rw [setActor_other w host i a hi]
  have hdeadP : ∀ i, (w.st i).life ≠ .alive → (w'.st i).parked = (w.st i).parked := by
    intro i hna
    by_cases hi : i = host
    · exact absurd (by rw [hi]; exact halive) hna
    · rw [setActor_other w host i a hi]
  refine ⟨?_, quiet_live h.quiet rfl (fun i hna ha => hna (by rw [hlift i]; exact ha))
      (fun i _ => hbox i) hdeadP,
    childless_stable h.childless rfl hlift hpar,
    chain_edit h.chain h.childless hF rfl rfl hlift hpar
      (fun i m hm => Or.inl ⟨m, by rw [hbox i] at hm; exact hm, rfl, rfl⟩)
      (fun i m hm => Or.inl ⟨m, by rw [hprioA i] at hm; exact hm, rfl, rfl⟩)
      (fun parent id ht => Or.inl (by
        obtain ⟨m, hm, htomb, hsnd⟩ := ht
        exact ⟨m, by rw [hprioA parent]; exact hm, htomb, hsnd⟩)),
    ?_, hostedMail_same h.hostedMail rfl hbox hprioA⟩
  · intro host' p ha hp
    by_cases hh : host' = host
    · rw [hh, setActor_self, hpk] at hp
      rcases List.mem_append.mp hp with hp | hp
      · have hold := h.liveParked host p halive hp
        by_cases hs : p.sender = host
        · rw [hs, setActor_self, hl]
          rw [hs] at hold
          exact hold
        · rw [setActor_other w host p.sender a hs]
          exact hold
      · have hp' : p = entry := by simpa [List.mem_singleton] using hp
        rw [hp']
        by_cases hs : entry.sender = host
        · rw [hs, setActor_self, hl]
          rw [hs] at hsend
          exact hsend
        · rw [setActor_other w host entry.sender a hs]
          exact hsend
    · rw [setActor_other w host host' a hh] at hp
      rw [setActor_other w host host' a hh] at ha
      have hold := h.liveParked host' p ha hp
      by_cases hs : p.sender = host
      · rw [hs, setActor_self, hl]
        rw [hs] at hold
        exact hold
      · rw [setActor_other w host p.sender a hs]
        exact hold
  · intro host' p hp
    by_cases hh : host' = host
    · rw [hh, setActor_self, hpk] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact h.parkedFrom host p hp
      · have hp' : p = entry := by simpa [List.mem_singleton] using hp
        rw [hp']
        exact hfrom
    · rw [setActor_other w host host' a hh] at hp
      exact h.parkedFrom host' p hp


theorem enqueue_seal (D : Description) (w : World) (h : SealInv w) (hF : ParentForest w)
    (hO : OpenSlots w) (sender dst : InstId) (msg : Msg) (isCall : Bool) (k : Cont)
    (hlive : (w.st sender).life = .alive) (hfrom : msg.sender = sender) :
    SealInv (enqueueOrPark w D sender dst msg isCall k) := by
  have hmem : sender ∈ w.roster := hO sender (by rw [hlive]; intro hna; cases hna)
  have hsend : (w.st sender).life ≠ .dead := by
    rw [hlive]
    intro hd
    cases hd
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · rw [ite_eq_right (fun hne => hne halive)]
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · rw [ite_eq_left hroom]
      by_cases hsame : sender = dst
      · subst hsame
        cases isCall
        · simp only [decide_true, ↓reduceIte, Bool.false_eq_true]
          let issued := Msg.mk msg.label msg.sender msg.callFrom (w.st sender).nextMid
            msg.reliable msg.callId msg.tombstone msg.baseLabel
          apply seal_grow_box (msg := issued)
          · exact h
          · exact hF
          · exact halive
          · simp [proceed_keeps_life, chargeSender, bumpToken]
          · simp [proceed_parent, chargeSender, bumpToken]
          · simp [proceed_keeps_parked, chargeSender, bumpToken]
          · simp [proceed_keeps_prio, chargeSender, bumpToken]
          · simp [proceed_keeps_box, chargeSender, bumpToken]
            rfl
          · exact Or.inr (by simpa [issued, hfrom] using halive)
          · rw [hfrom]
            exact hmem
        · simp only [decide_true, ↓reduceIte]
          let issued := Msg.mk msg.label msg.sender msg.callFrom (w.st sender).nextMid
            msg.reliable (some (w.st sender).nextCall) msg.tombstone msg.baseLabel
          apply seal_grow_box (msg := issued)
          · exact h
          · exact hF
          · exact halive
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · rfl
          · exact Or.inr (by simpa [issued, hfrom] using halive)
          · rw [hfrom]
            exact hmem
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        cases isCall
        · simp only [hdec, ↓reduceIte, Bool.false_eq_true]
          apply seal_set_keep
          · apply seal_grow_box w h hF dst
            · exact halive
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · exact Or.inr (by simpa [hfrom] using hlive)
            · rw [hfrom]
              exact hmem
          · rw [setActor_other w dst sender _ hsame]
            simp [proceed_keeps_life, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [proceed_keeps_box, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [proceed_keeps_prio, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [proceed_keeps_parked, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [proceed_parent, chargeSender, bumpToken]
        · simp only [hdec, ↓reduceIte]
          apply seal_set_keep
          · apply seal_grow_box w h hF dst
            · exact halive
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · exact Or.inr (by simpa [hfrom] using hlive)
            · rw [hfrom]
              exact hmem
          · rw [setActor_other w dst sender _ hsame]
            simp [issueCall, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [issueCall, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [issueCall, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [issueCall, chargeSender, bumpToken]
          · rw [setActor_other w dst sender _ hsame]
            simp [issueCall, chargeSender, bumpToken]
    · rw [ite_eq_right hroom]
      by_cases hsame : sender = dst
      · subst hsame
        cases isCall
        · simp only [decide_true, ↓reduceIte, Bool.false_eq_true]
          let issued := Msg.mk msg.label msg.sender msg.callFrom (w.st sender).nextMid
            msg.reliable msg.callId msg.tombstone msg.baseLabel
          apply seal_park_snoc (entry := Parked.mk sender issued false)
          · exact h
          · exact hF
          · exact halive
          · simp [chargeSender, bumpToken]
          · simp [chargeSender, bumpToken]
          · simp [chargeSender, bumpToken]
          · simp [chargeSender, bumpToken]
          · rfl
          · simp [issued, hfrom]
          · simpa [issued, hfrom] using hsend
        · simp only [decide_true, ↓reduceIte]
          let issued := Msg.mk msg.label msg.sender msg.callFrom (w.st sender).nextMid
            msg.reliable (some (w.st sender).nextCall) msg.tombstone msg.baseLabel
          apply seal_park_snoc (entry := Parked.mk sender issued true)
          · exact h
          · exact hF
          · exact halive
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · simp [issueCall, chargeSender, bumpToken]
          · rfl
          · simp [issued, issueCall, hfrom]
          · simpa [issued, issueCall, hfrom] using hsend
      · have hdec : decide (sender = dst) = false := by simp [hsame]
        simp only [hdec, ↓reduceIte, Bool.false_eq_true]
        apply seal_set_keep
        · apply seal_park_snoc w h hF dst
          · exact halive
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · simp [hfrom]
          · simpa [hfrom] using hsend
        · rw [setActor_other w dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
        · rw [setActor_other w dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
        · rw [setActor_other w dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
        · rw [setActor_other w dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
        · rw [setActor_other w dst sender _ hsame]
          cases isCall <;> simp [issueCall, chargeSender, bumpToken]
  · rw [ite_eq_left halive]
    cases isCall
    · rw [ite_eq_right Bool.false_ne_true]
      exact seal_set_keep h (proceed_keeps_life _ _) (proceed_keeps_box _ _)
        (proceed_keeps_prio _ _) (proceed_keeps_parked _ _) (proceed_parent _ _)
    · rw [ite_eq_left rfl]
      exact seal_set_keep h
        (by simp [finishCall, issueCall, proceed_keeps_life])
        (by simp [finishCall, issueCall, proceed_keeps_box])
        (by simp [finishCall, issueCall, proceed_keeps_prio])
        (by simp [finishCall, issueCall, proceed_keeps_parked])
        (by simp [finishCall, issueCall, proceed_parent])

/-- The mailbox write of a send or call, given the running sender's `SemInv` result. -/
theorem enqueue_inv (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (h : Inv I w) (hS : SemInv I (enqueueOrPark w I.desc sender dst msg isCall k))
    (hfree : notParked (w.st sender).phase) (hlive : (w.st sender).life = .alive)
    (hs : srcOk I sender (w.st sender) k)
    (hcall : isCall = true →
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true)
    (hfrom : msg.sender = sender) :
    Inv I (enqueueOrPark w I.desc sender dst msg isCall k) :=
  ⟨hS, enqueue_mail w I.desc sender dst msg isCall k h.2.1 hfree hlive,
    open_shape w _ h.2.2.1 (fun i hi => by rw [enqueue_roster]; exact hi)
      (enqueue_life w I.desc sender dst msg isCall k),
    enqueue_outcome I I.desc w sender dst msg isCall k h.2.2.2.1 hs hcall,
    ParentForest.parents h.forest
      (enqueue_parent w I.desc sender dst msg isCall k)
      (enqueue_roster w I.desc sender dst msg isCall k),
    enqueue_seal I.desc w h.seal h.forest h.2.2.1 sender dst msg isCall k hlive hfrom⟩

theorem crash_parked (w : World) (i : InstId) : ((crashWorld w).st i).parked = (w.st i).parked := by
  by_cases hm : i ∈ w.roster
  · rw [crash_at w i hm]
    unfold crashActor
    split <;> rfl
  · rw [crash_off w i hm]

theorem crash_halted (w : World) (s : InstId)
    (h : Halted (w.st s).life ∨ ((w.st s).life = .alive ∧ s ∈ w.roster)) :
    Halted ((crashWorld w).st s).life := by
  by_cases hm : s ∈ w.roster
  · rw [crash_at w s hm]
    rcases h with hh | ⟨ha, _⟩
    · rw [crash_stay (by rw [hh]; intro he; cases he)]
      exact hh
    · rw [crash_go ha]
      exact rfl
  · rw [crash_off w s hm]
    rcases h with hh | ⟨_, hin⟩
    · exact hh
    · exact absurd hin hm

theorem crash_inv (I : Impl) (w : World) (h : Inv I w) : Inv I (crashWorld w) := by
  have hS := h.1
  have hM := h.2.1
  have hbusy : ∀ s mb c k, (w.st s).phase = .parked mb c k → (w.st s).life = .alive := by
    intro s mb c k hph
    exact busy_alive I w hS s (by rw [hph]; intro he; cases he) (by rw [hph]; intro he; cases he)
  refine ⟨crash_sem I w hS, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro mb p hp
    rw [crash_parked] at hp
    right
    rcases hM.fwd mb p hp with ⟨k, hk⟩ | hh
    · have ha := hbusy p.sender mb p.isCall k hk
      exact crash_halted w p.sender (Or.inr ⟨ha, hS.rostered _ ha⟩)
    · exact crash_halted w p.sender (Or.inl hh)
  · intro s dst c k hph
    exfalso
    by_cases hm : s ∈ w.roster
    · rw [crash_at w s hm] at hph
      by_cases hgo : (w.st s).life = .alive
      · rw [crash_go hgo] at hph
        cases hph
      · rw [crash_stay hgo] at hph
        exact hgo (hbusy s dst c k hph)
    · rw [crash_off w s hm] at hph
      exact hm (hS.rostered s (hbusy s dst c k hph))
  · intro mb1 mb2 p1 p2 h1 h2 hs
    rw [crash_parked] at h1 h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs
  · intro mb
    rw [crash_parked]
    exact hM.once mb
  · intro i hl
    by_cases hm : i ∈ w.roster
    · exact hm
    · rw [crash_off w i hm] at hl
      exact h.2.2.1 i hl
  · intro i
    by_cases hm : i ∈ w.roster
    · rw [crash_at w i hm]
      by_cases hgo : (w.st i).life = .alive
      · rw [crash_go hgo]
        simp [outcomeOk]
      · rw [crash_stay hgo]
        exact h.2.2.2.1 i
    · rw [crash_off w i hm]
      exact h.2.2.2.1 i
  · exact ParentForest.parents h.forest (fun i => crashWorld_parent w i) rfl
  · exact seal_crash I w h.seal hS

theorem crash_except (I : Impl) (w : World) {gap : InstId → Prop}
    (h : ExceptInv I w gap) : Inv I (crashWorld w) := by
  have hS := h.1
  have hM := h.2.1
  have hbusy : ∀ s mb c k, (w.st s).phase = .parked mb c k → (w.st s).life = .alive := by
    intro s mb c k hph
    exact busy_alive I w hS s (by rw [hph]; intro he; cases he) (by rw [hph]; intro he; cases he)
  refine ⟨crash_sem I w hS, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro mb p hp
    rw [crash_parked] at hp
    right
    rcases hM.fwd mb p hp with ⟨k, hk⟩ | hh
    · have ha := hbusy p.sender mb p.isCall k hk
      exact crash_halted w p.sender (Or.inr ⟨ha, hS.rostered _ ha⟩)
    · exact crash_halted w p.sender (Or.inl hh)
  · intro s dst c k hph
    exfalso
    by_cases hm : s ∈ w.roster
    · rw [crash_at w s hm] at hph
      by_cases hgo : (w.st s).life = .alive
      · rw [crash_go hgo] at hph
        cases hph
      · rw [crash_stay hgo] at hph
        exact hgo (hbusy s dst c k hph)
    · rw [crash_off w s hm] at hph
      exact hm (hS.rostered s (hbusy s dst c k hph))
  · intro mb1 mb2 p1 p2 h1 h2 hs
    rw [crash_parked] at h1 h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs
  · intro mb
    rw [crash_parked]
    exact hM.once mb
  · intro i hl
    by_cases hm : i ∈ w.roster
    · exact hm
    · rw [crash_off w i hm] at hl
      exact h.2.2.1 i hl
  · intro i
    by_cases hm : i ∈ w.roster
    · rw [crash_at w i hm]
      by_cases hgo : (w.st i).life = .alive
      · rw [crash_go hgo]
        simp [outcomeOk]
      · rw [crash_stay hgo]
        exact h.2.2.2.1 i
    · rw [crash_off w i hm]
      exact h.2.2.2.1 i
  · exact ParentForest.parents h.forest (fun i => crashWorld_parent w i) rfl
  · exact seal_crash_open I w h.seal.parkedFrom h.seal.hostedMail hS

def withPrio (a : Actor) (msg : Msg) : Actor :=
  { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 }

theorem seal_grow_prio (w : World) (h : SealInv w) (hF : ParentForest w) (host : InstId) (msg : Msg)
    (hfrom : msg.tombstone = true ∨ (w.st msg.sender).life = .alive)
    (hmem : msg.sender ∈ w.roster) :
    SealInv (setActor w host
      { (w.st host) with prio := (w.st host).prio ++ [msg], nextMid := (w.st host).nextMid + 1 }) := by
  let w' := setActor w host (withPrio (w.st host) msg)
  have hl : ∀ i, (w'.st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = host
    · rw [hi]
      simp [w', setActor, withPrio]
    · simp [w', setActor, withPrio, hi]
  have hpar : ∀ i, (w'.st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = host
    · rw [hi]
      simp [w', setActor, withPrio]
    · simp [w', setActor, withPrio, hi]
  have hbox : ∀ i, (w'.st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = host
    · rw [hi]
      simp [w', setActor, withPrio]
    · simp [w', setActor, withPrio, hi]
  have hpk : ∀ i, (w'.st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = host
    · rw [hi]
      simp [w', setActor, withPrio]
    · simp [w', setActor, withPrio, hi]
  refine ⟨parkedLive_same h.liveParked hl hpk,
    quiet_stable h.quiet rfl hl hbox hpk,
    childless_stable h.childless rfl hl hpar,
    chain_edit h.chain h.childless hF rfl rfl hl hpar ?_ ?_ ?_,
    parkedFrom_same h.parkedFrom hpk,
    ?_⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self] at hm
      simp [withPrio] at hm
      exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
    · rw [setActor_other w host i _ hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
      · have hm' : m = msg := by simpa [List.mem_singleton] using hm
        rw [hm']
        exact Or.inr hfrom
    · rw [setActor_other w host i _ hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro parent id ht
    refine Or.inl ?_
    obtain ⟨m, hm, htomb, hsnd⟩ := ht
    refine ⟨m, ?_, htomb, hsnd⟩
    by_cases hp : parent = host
    · rw [hp, setActor_self]
      exact List.mem_append_left _ (by rw [← hp]; exact hm)
    · rw [setActor_other w host parent _ hp]
      exact hm
  · intro host' m hm
    rcases hm with hm | hm
    · by_cases hi : host' = host
      · rw [hi, setActor_self] at hm
        simp [withPrio] at hm
        exact h.hostedMail host' m (Or.inl (by rw [hi]; exact hm))
      · rw [setActor_other w host host' _ hi] at hm
        exact h.hostedMail host' m (Or.inl hm)
    · by_cases hi : host' = host
      · rw [hi, setActor_self] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h.hostedMail host' m (Or.inr (by rw [hi]; exact hm))
        · have hm' : m = msg := by simpa [List.mem_singleton] using hm
          rw [hm']
          exact hmem
      · rw [setActor_other w host host' _ hi] at hm
        exact h.hostedMail host' m (Or.inr hm)

/-- Appending `ex`'s tombstone at its live parent removes the one exemption. -/
theorem seal_grow_close (w : World) (host : InstId) (msg : Msg)
    (h : SealExcept w (fun i => i = msg.sender)) (hF : ParentForest w)
    (hparS : (w.st msg.sender).parent = some host)
    (halive : (w.st host).life = .alive) (htomb : msg.tombstone = true)
    (hmem : msg.sender ∈ w.roster) :
    SealInv (setActor w host (withPrio (w.st host) msg)) := by
  let w' := setActor w host (withPrio (w.st host) msg)
  have hl : ∀ i, (w'.st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = host <;> simp [w', setActor, withPrio, hi, setActor_self, setActor_other]
  have hparL : ∀ i, (w'.st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = host <;> simp [w', setActor, withPrio, hi, setActor_self, setActor_other]
  have hbox : ∀ i, (w'.st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = host <;> simp [w', setActor, withPrio, hi, setActor_self, setActor_other]
  have hpk : ∀ i, (w'.st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = host <;> simp [w', setActor, withPrio, hi, setActor_self, setActor_other]
  refine ⟨parkedLive_same h.liveParked hl hpk,
    quiet_stable h.quiet rfl hl hbox hpk,
    childless_stable h.childless rfl hl hparL,
    chain_close (chain_gap_keep h.chain h.childless hF rfl rfl hl hparL ?_ ?_ ?_) ?_,
    parkedFrom_same h.parkedFrom hpk, ?_⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self] at hm
      simp [withPrio] at hm
      exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
    · rw [setActor_other w host i _ hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro i m hm
    by_cases hi : i = host
    · rw [hi, setActor_self] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl ⟨m, by rw [hi]; exact hm, rfl, rfl⟩
      · have hm' : m = msg := by simpa [List.mem_singleton] using hm
        rw [hm']
        exact Or.inr (Or.inl htomb)
    · rw [setActor_other w host i _ hi] at hm
      exact Or.inl ⟨m, hm, rfl, rfl⟩
  · intro parent id ht
    refine Or.inl ?_
    obtain ⟨m, hm, ht, hsnd⟩ := ht
    refine ⟨m, ?_, ht, hsnd⟩
    by_cases hp : parent = host
    · rw [hp, setActor_self]
      exact List.mem_append_left _ (by rw [← hp]; exact hm)
    · rw [setActor_other w host parent _ hp]
      exact hm
  · intro hf
    rw [hparL msg.sender, hparS]
    refine Or.inl ⟨by rw [hl host]; exact halive, ?_⟩
    refine ⟨msg, ?_, htomb, rfl⟩
    rw [setActor_self]
    simp [withPrio]
  · intro host' m hm
    rcases hm with hm | hm
    · by_cases hi : host' = host
      · rw [hi, setActor_self] at hm
        simp [withPrio] at hm
        exact h.hostedMail host' m (Or.inl (by rw [hi]; exact hm))
      · rw [setActor_other w host host' _ hi] at hm
        exact h.hostedMail host' m (Or.inl hm)
    · by_cases hi : host' = host
      · rw [hi, setActor_self] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h.hostedMail host' m (Or.inr (by rw [hi]; exact hm))
        · have hm' : m = msg := by simpa [List.mem_singleton] using hm
          rw [hm']
          exact hmem
      · rw [setActor_other w host host' _ hi] at hm
        exact h.hostedMail host' m (Or.inr hm)

theorem offerPrio_inv (I : Impl) (D : Description) (w : World) (host : InstId) (msg : Msg)
    (h : Inv I w) (hfrom : msg.tombstone = true ∨ (w.st msg.sender).life = .alive)
    (hmem : msg.sender ∈ w.roster) : Inv I (offerPrio D w host msg) := by
  unfold offerPrio
  dsimp only
  split
  · exact crash_inv I w h
  · exact inv_frame I w _ h (same_actor w host _ rfl rfl rfl rfl rfl)
      (seal_grow_prio w h.seal h.forest host msg hfrom hmem)

theorem crash_not_alive (w : World) (i : InstId) (hi : i ∈ w.roster) :
    ((crashWorld w).st i).life ≠ .alive := by
  rw [crash_at w i hi]
  unfold crashActor
  by_cases hb : ((w.st i).life == .alive) = true
  · rw [ite_eq_left hb]
    intro h
    cases h
  · rw [ite_eq_right hb]
    intro hlive
    exact hb (beq_iff_eq.mpr hlive)

theorem tryWake_skip (D : Description) (w : World) (dstId writer : InstId) (label : String)
    (hd : (w.st dstId).life ≠ .alive) : tryWake D w dstId label writer = w := by
  unfold tryWake
  dsimp only
  have hbit : ((w.st dstId).life == .alive) = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hd (beq_iff_eq.mp hb)
  have hcond : ((w.st dstId).life != .alive) = true := by
    show (!((w.st dstId).life == .alive)) = true
    rw [hbit]
    rfl
  rw [hcond]
  rfl

theorem tryWake_cases (D : Description) (w : World) (dstId writer : InstId) (label : String) :
    tryWake D w dstId label writer = w ∨
    tryWake D w dstId label writer = crashWorld w ∨
    (∃ msg, msg.sender = writer ∧ msg.tombstone = false ∧
      tryWake D w dstId label writer = setActor w dstId (withPrio (w.st dstId) msg)) := by
  unfold tryWake
  dsimp only
  split
  · exact Or.inl rfl
  · unfold offerPrio
    dsimp only
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨_, rfl, rfl, rfl⟩)

theorem fold_skip (D : Description) (ids : List InstId) (label : String) (writer : InstId) (w : World)
    (hd : ∀ i ∈ ids, (w.st i).life ≠ .alive) :
    ids.foldl (fun w id => tryWake D w id label writer) w = w := by
  induction ids with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [tryWake_skip D w i writer label (hd i (List.mem_cons_self (a := i)))]
    exact ih (fun j hj => hd j (List.mem_cons_of_mem i hj))

theorem tryWake_inv (I : Impl) (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (h : Inv I w) (hw : (w.st writer).life = .alive) :
    Inv I (tryWake D w dstId label writer) := by
  unfold tryWake
  dsimp only
  split
  · exact h
  · exact offerPrio_inv I D w dstId _ h (Or.inr hw)
      (h.2.2.1 writer (by rw [hw]; intro hna; cases hna))

theorem wakes_inv (I : Impl) (D : Description) (w : World) (ids : List InstId) (label : String)
    (writer : InstId) (h : Inv I w) (hw : (w.st writer).life = .alive)
    (hsub : ∀ i ∈ ids, i ∈ w.roster) :
    Inv I (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    rcases tryWake_cases D w i writer label with hskip | hrest
    · rw [hskip]
      exact ih _ h hw (fun j hj => hsub j (List.mem_cons_of_mem i hj))
    · rcases hrest with hcrash | ⟨msg, hsnd, htomb, heq⟩
      · rw [hcrash, fold_skip D is label writer (crashWorld w)
          (fun j hj => crash_not_alive w j (hsub j (List.mem_cons_of_mem i hj)))]
        exact crash_inv I w h
      · rw [heq]
        have hmem : writer ∈ w.roster := h.2.2.1 writer (by rw [hw]; intro hna; cases hna)
        have hfrom : msg.tombstone = true ∨ (w.st msg.sender).life = .alive := by
          rw [htomb, hsnd]
          exact Or.inr hw
        have h1 := inv_frame I w (setActor w i (withPrio (w.st i) msg)) h
          (same_actor w i (withPrio (w.st i) msg) rfl rfl rfl rfl rfl)
          (seal_grow_prio w h.seal h.forest i msg hfrom (by rw [hsnd]; exact hmem))
        refine ih _ h1 ?_ ?_
        · by_cases he : writer = i
          · rw [he, setActor_self]
            simp [withPrio]
            rw [he] at hw
            exact hw
          · rw [setActor_other w i writer _ he]
            exact hw
        · intro j hj
          simp [setActor]
          exact hsub j (List.mem_cons_of_mem i hj)

theorem wakeReaders_inv (I : Impl) (D : Description) (w : World) (dst label : String) (writer : InstId)
    (h : Inv I w) (hw : (w.st writer).life = .alive) :
    Inv I (wakeReaders D w dst label writer) :=
  wakes_inv I D w _ label writer h hw
    (fun i hi => (List.mem_filter.mp hi).1)

theorem enqueueTombstone_inv (I : Impl) (D : Description) (w : World) (child : InstId) (h : Inv I w) :
    Inv I (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  match hpar : (w.st child).parent with
  | none => exact h
  | some parent =>
    simp only [hpar]
    split
    · exact h
    · split
      · exact crash_inv I w h
      · exact offerPrio_inv I D w parent (tombstoneMsg D (w.st parent) child) h
          (Or.inl rfl) (roster_of_parent h.forest hpar)

theorem resume_false_ok (D : Description) (sid : InstId) (a : Actor) (dst : InstId)
    (hc : contTy a) (hg : programOk D sid a) (hw : waitEdge D sid a) :
    let b := resumeSender a false dst
    b.typestate = a.typestate ∧ b.life = a.life ∧ contTy b ∧ programOk D sid b ∧ waitEdge D sid b ∧
      notParked b.phase ∧ b.parked = a.parked := by
  cases hph : a.phase with
  | parked _ _ k =>
    simp only [resumeSender, hph, Bool.false_eq_true, ite_false]
    have hty : a.typestate = k.toState := by simpa [contTy, hph] using hc
    have hprog : effectsOk D (tname sid) (contAt k) k.rest = true := by simpa [programOk, hph] using hg
    have hp := proceed_ok D sid a k hty hprog
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, proceed_not_parked a k, proceed_parked a k⟩
  | idle => simp [resumeSender, hph, notParked, hc, hg, hw]
  | run _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitReply _ _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitEffect _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitPeer _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | crashed => simp [resumeSender, hph, notParked, hc, hg, hw]

/-- A resumed sender keeps its checked outcomes. A call resumes only from a parked call. -/
theorem outcome_resume (I : Impl) (s : InstId) (a : Actor) (b : Bool) (dst : InstId)
    (h : outcomeOk I s a) (hc : ∀ d c k, a.phase = .parked d c k → b = true → c = true) :
    outcomeOk I s (resumeSender a b dst) := by
  cases hph : a.phase with
  | parked d c k =>
    have hk : srcOk I s a k ∧ (c = true →
        effectsOk I.desc (tname s) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
        effectsOk I.desc (tname s) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true) := by
      unfold outcomeOk at h
      rw [hph] at h
      exact h
    cases b with
    | false =>
      simp only [resumeSender, hph, Bool.false_eq_true, ite_false]
      exact outcome_proceed I s a k hk.1
    | true =>
      simp only [resumeSender, hph, ite_true]
      exact outcome_await I s _ dst k rfl (src_ty I s k rfl hk.1) (hk.2 (hc d c k hph rfl)).2
  | idle => simp only [resumeSender, hph]; exact h
  | run _ => simp only [resumeSender, hph]; exact h
  | awaitReply _ _ => simp only [resumeSender, hph]; exact h
  | awaitEffect _ => simp only [resumeSender, hph]; exact h
  | awaitPeer _ => simp only [resumeSender, hph]; exact h
  | crashed => simp only [resumeSender, hph]; exact h

theorem fold_release (I : Impl) (id : InstId) (ps : List Parked) (w : World) (hS : SemInv I w) :
    SemInv I (ps.foldl (fun w p =>
      if (p.isCall || decide (p.sender = id)) = true then w
      else setActor w p.sender (resumeSender (w.st p.sender) false id)) w) := by
  induction ps generalizing w with
  | nil => simpa using hS
  | cons p ps ih =>
    simp only [List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [ite_eq_left hskip]
      exact ih _ hS
    · rw [ite_eq_right hskip]
      have hr := resume_false_ok I.desc p.sender (w.st p.sender) id (hS.cont _) (hS.prog _) (hS.waited _)
      exact ih _ (sem_set I w p.sender (resumeSender (w.st p.sender) false id) hS hr.1 hr.2.1
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 (idleOff_resume I w hS p.sender false id)
        (Or.inl hr.2.2.2.2.2.2))

def releaseFold (id : InstId) (ps : List Parked) (w : World) : World :=
  ps.foldl (fun w p =>
    if (p.isCall || decide (p.sender = id)) = true then w
    else setActor w p.sender (resumeSender (w.st p.sender) false id)) w

theorem release_fold_eq (w : World) (id : InstId) (ps : List Parked) :
    releaseParked w id ps = releaseFold id ps w := by
  simp [releaseParked, releaseFold]

theorem release_sem (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hS : SemInv I w) :
    SemInv I (releaseFold id ps w) :=
  fold_release I id ps w hS

theorem release_step_skip (id : InstId) (p : Parked) (ps : List Parked) (w : World)
    (hskip : (p.isCall || decide (p.sender = id)) = true) :
    releaseFold id (p :: ps) w = releaseFold id ps w := by
  simp only [releaseFold, List.foldl_cons]
  rw [ite_eq_left hskip]

theorem release_step_go (id : InstId) (p : Parked) (ps : List Parked) (w : World)
    (hgo : ¬ (p.isCall || decide (p.sender = id)) = true) :
    releaseFold id (p :: ps) w =
      releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
  simp only [releaseFold, List.foldl_cons]
  rw [ite_eq_right hgo]

theorem release_go_ne (id : InstId) (p : Parked) (hgo : ¬ (p.isCall || decide (p.sender = id)) = true) :
    p.sender ≠ id := by
  intro h
  apply hgo
  simp [h]

theorem release_roster (id : InstId) (ps : List Parked) (w : World) :
    (releaseFold id ps w).roster = w.roster := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip]
      exact ih _

theorem release_outcome (I : Impl) (id : InstId) (ps : List Parked) (w : World)
    (hO : OutcomeInv I w) : OutcomeInv I (releaseFold id ps w) := by
  induction ps generalizing w with
  | nil => exact hO
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w hO
    · rw [release_step_go id p ps w hskip]
      exact ih _ (outcome_set I w p.sender _ hO (outcome_resume I p.sender _ false id (hO _)
        (fun _ _ _ _ hb => by cases hb)))

theorem release_spares_id (id : InstId) (ps : List Parked) (w : World) :
    (releaseFold id ps w).st id = w.st id := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      exact setActor_other w p.sender id _ (release_go_ne id p hskip).symm

theorem release_skips_sender (id : InstId) (ps : List Parked) (w : World) (sid : InstId)
    (hs : ∀ p ∈ ps, p.sender = sid → p.isCall = true) :
    (releaseFold id ps w).st sid = w.st sid := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.sender = sid → q.isCall = true :=
      fun q hq => hs q (List.mem_cons_of_mem _ hq)
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w htail
    · rw [release_step_go id p ps w hskip, ih _ htail]
      have hwho : p.sender ≠ sid := by
        intro hsid
        apply hskip
        simp [hs p List.mem_cons_self hsid]
      exact setActor_other w p.sender sid _ hwho.symm

theorem release_st_other (id : InstId) (ps : List Parked) (i : InstId) (w : World)
    (hs : ∀ p ∈ ps, p.sender ≠ i) : (releaseFold id ps w).st i = w.st i :=
  release_skips_sender id ps w i (fun p hp he => absurd he (hs p hp))

theorem release_life (id : InstId) (ps : List Parked) (w : World) (i : InstId) :
    ((releaseFold id ps w).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      by_cases hi : i = p.sender
      · rw [hi, setActor_self]
        exact resume_keeps_life _ _ _
      · rw [setActor_other w p.sender i _ hi]

theorem resume_parked (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).parked = a.parked := by
  cases h : a.phase with
  | parked _ _ _ =>
    cases isCall with
    | true => simp [resumeSender, h]
    | false =>
      simp [resumeSender, h, proceed]
      split <;> rfl
  | idle => simp [resumeSender, h]
  | run _ => simp [resumeSender, h]
  | awaitReply _ _ => simp [resumeSender, h]
  | awaitEffect _ => simp [resumeSender, h]
  | awaitPeer _ => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem resume_false_free (a : Actor) (dst : InstId) :
    notParked (resumeSender a false dst).phase := by
  cases h : a.phase with
  | parked _ _ _ =>
    simp [resumeSender, h]
    exact proceed_not_parked a _
  | idle => simp [resumeSender, h, notParked]
  | run _ => simp [resumeSender, h, notParked]
  | awaitReply _ _ => simp [resumeSender, h, notParked]
  | awaitEffect _ => simp [resumeSender, h, notParked]
  | awaitPeer _ => simp [resumeSender, h, notParked]
  | crashed => simp [resumeSender, h, notParked]

theorem release_keeps_free (id : InstId) (ps : List Parked) (w : World) (sid : InstId)
    (hf : notParked (w.st sid).phase) : notParked ((releaseFold id ps w).st sid).phase := by
  induction ps generalizing w with
  | nil => exact hf
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w hf
    · rw [release_step_go id p ps w hskip]
      by_cases hwho : p.sender = sid
      · subst hwho
        exact ih _ (by rw [setActor_self]; exact resume_false_free _ _)
      · exact ih _ (by rw [setActor_other w p.sender sid _ (Ne.symm hwho)]; exact hf)

theorem release_resumed (id : InstId) (ps : List Parked) (w : World) (p : Parked)
    (hp : p ∈ ps) (hc : p.isCall = false) (hs : p.sender ≠ id) :
    notParked ((releaseFold id ps w).st p.sender).phase := by
  induction ps generalizing w with
  | nil => cases hp
  | cons q qs ih =>
    by_cases hskip : (q.isCall || decide (q.sender = id)) = true
    · rw [release_step_skip id q qs w hskip]
      have hmem : p ∈ qs := by
        rcases List.mem_cons.mp hp with rfl | hmem
        · exfalso
          apply hs
          simpa [hc] using hskip
        · exact hmem
      exact ih w hmem
    · rw [release_step_go id q qs w hskip]
      by_cases hwho : q.sender = p.sender
      · rw [hwho]
        exact release_keeps_free id qs _ p.sender (by
          rw [setActor_self, ← hwho]
          exact resume_false_free _ _)
      · have hmem : p ∈ qs := by
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact absurd rfl hwho
          · exact hmem
        exact ih _ hmem

theorem resume_box (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).box = a.box := by
  cases h : a.phase with
  | parked _ _ _ =>
    cases isCall with
    | false => simp [resumeSender, h, proceed_keeps_box]
    | true => simp [resumeSender, h]
  | idle => simp [resumeSender, h]
  | run _ => simp [resumeSender, h]
  | awaitReply _ _ => simp [resumeSender, h]
  | awaitEffect _ => simp [resumeSender, h]
  | awaitPeer _ => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem resume_prio (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).prio = a.prio := by
  cases h : a.phase with
  | parked _ _ _ =>
    cases isCall with
    | false => simp [resumeSender, h, proceed_keeps_prio]
    | true => simp [resumeSender, h]
  | idle => simp [resumeSender, h]
  | run _ => simp [resumeSender, h]
  | awaitReply _ _ => simp [resumeSender, h]
  | awaitEffect _ => simp [resumeSender, h]
  | awaitPeer _ => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem release_box (id : InstId) (ps : List Parked) (w : World) (i : InstId) :
    ((releaseFold id ps w).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      by_cases hwho : p.sender = i
      · subst hwho
        rw [setActor_self, resume_box]
      · rw [setActor_other w p.sender i _ (Ne.symm hwho)]

theorem release_prio (id : InstId) (ps : List Parked) (w : World) (i : InstId) :
    ((releaseFold id ps w).st i).prio = (w.st i).prio := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      by_cases hwho : p.sender = i
      · subst hwho
        rw [setActor_self, resume_prio]
      · rw [setActor_other w p.sender i _ (Ne.symm hwho)]

theorem release_crashed (id : InstId) (ps : List Parked) (w : World) :
    (releaseFold id ps w).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      simp [setActor]

theorem release_parked_all (id : InstId) (ps : List Parked) (w : World) (i : InstId) :
    ((releaseFold id ps w).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w
    · rw [release_step_go id p ps w hskip, ih]
      by_cases hwho : p.sender = i
      · subst hwho
        rw [setActor_self, resume_parked]
      · rw [setActor_other w p.sender i _ (Ne.symm hwho)]

/-- One host of `releaseOutbound`: drop `dead`'s entries and return their tokens to `dead`. -/
def outHost (w : World) (dead host : InstId) : World :=
  if host == dead then w
  else
    let dropped := (w.st host).parked.filter fun p => p.sender == dead
    if dropped.isEmpty then w
    else
      let w := setActor w host
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      setActor w dead (addTokens (w.st dead) (tname host) dropped.length)

theorem releaseOutbound_eq (w : World) (dead : InstId) :
    releaseOutbound w dead = w.roster.foldl (fun w host => outHost w dead host) w := rfl

/-- One host's parked sends from `dead` are removed and the same count is added
to `dead`'s tokens. Life is unchanged, so this credit lands while `dead` is
still the live holder. `releaseWorld` marks `dead` dead only after this. -/
theorem outHost_credit (w : World) (dead host : InstId) (hne : host ≠ dead)
    (hgo : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false) :
    ((outHost w dead host).st dead).life = (w.st dead).life ∧
      ((outHost w dead host).st dead).tokens (tname host) =
        (w.st dead).tokens (tname host) +
          ((w.st host).parked.filter fun p => p.sender == dead).length := by
  unfold outHost
  rw [ite_eq_right (by simp [hne])]
  dsimp only
  rw [ite_eq_right (by simp [hgo])]
  have hdh : dead ≠ host := Ne.symm hne
  simp [setActor_self, setActor_other w host dead _ hdh, addTokens]

/-- `releaseWorld` installs the dead actor after `releaseOutbound`, and the
parked-sender resume does not touch that actor. The credited tokens stay. -/
theorem releaseWorld_keeps_credit (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).life = .dead ∧
      ((releaseWorld D w id a).st id).tokens =
        ((releaseOutbound (refundParked (refundMsgs (readCells D w id) (tname id) a.box)
          (tname id) a.parked) id).st id).tokens := by
  simp only [releaseWorld]
  rw [release_fold_eq, release_spares_id, setActor_self]
  exact ⟨rfl, rfl⟩

theorem filter_keep_of_empty (ps : List Parked) (dead : InstId)
    (h : (ps.filter fun p => p.sender == dead).isEmpty = true) :
    ps.filter (fun p => p.sender != dead) = ps :=
  filter_drop_empty (fun p : Parked => p.sender == dead) ps h

theorem filter_ne_idem (ps : List Parked) (dead : InstId) :
    ((ps.filter fun p => p.sender != dead).filter fun p => p.sender != dead) =
      ps.filter fun p => p.sender != dead := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : (p.sender != dead) = true
    · simp [List.filter, hp, ih]
    · simp [List.filter, hp, ih]

theorem outHost_fields (w : World) (dead host i : InstId) :
    (outHost w dead host).roster = w.roster ∧
      ((outHost w dead host).st i).life = (w.st i).life ∧
      ((outHost w dead host).st i).typestate = (w.st i).typestate ∧
      ((outHost w dead host).st i).phase = (w.st i).phase ∧
      ((outHost w dead host).st i).parked =
        (if i = host ∧ i ≠ dead then (w.st i).parked.filter (fun p => p.sender != dead)
          else (w.st i).parked) := by
  unfold outHost
  by_cases hh : (host == dead) = true
  · rw [ite_eq_left hh]
    have hhd : host = dead := by simpa using hh
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    rw [ite_eq_right (fun hc : i = host ∧ i ≠ dead => hc.2 (hc.1.trans hhd))]
  · rw [ite_eq_right hh]
    dsimp only
    have hne : host ≠ dead := fun h => hh (by simp [h])
    have hdh : dead ≠ host := Ne.symm hne
    by_cases he : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · rw [ite_eq_left he]
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      by_cases hc : i = host ∧ i ≠ dead
      · rw [ite_eq_left hc, hc.1]
        exact (filter_keep_of_empty _ dead he).symm
      · rw [ite_eq_right hc]
    · rw [ite_eq_right he]
      by_cases hd : i = dead
      · subst hd
        refine ⟨rfl, ?_⟩
        simp [setActor_self, setActor_other w host i _ hdh, addTokens]
      · by_cases hi : i = host
        · subst hi
          refine ⟨rfl, ?_⟩
          simp [setActor_other _ dead i _ hd, setActor_self, hd]
        · refine ⟨rfl, ?_⟩
          simp [setActor_other _ dead i _ hd, setActor_other w host i _ hi, hi]

theorem outFold_fields (dead : InstId) (ids : List InstId) (w : World) (i : InstId) :
    (ids.foldl (fun w host => outHost w dead host) w).roster = w.roster ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).life = (w.st i).life ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).typestate = (w.st i).typestate ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).phase = (w.st i).phase ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).parked =
        (if i ∈ ids ∧ i ≠ dead then (w.st i).parked.filter (fun p => p.sender != dead)
          else (w.st i).parked) := by
  induction ids generalizing w with
  | nil => simp
  | cons h hs ih =>
    simp only [List.foldl_cons]
    obtain ⟨r1, l1, t1, p1, k1⟩ := ih (outHost w dead h)
    obtain ⟨r0, l0, t0, p0, k0⟩ := outHost_fields w dead h i
    refine ⟨r1.trans r0, l1.trans l0, t1.trans t0, p1.trans p0, ?_⟩
    rw [k1, k0]
    by_cases hd : i = dead
    · simp [hd]
    · by_cases hi : i = h
      · subst hi
        by_cases hm : i ∈ hs <;> simp [hd, hm]
      · simp [hd, hi]

theorem releaseOutbound_fields (w : World) (dead i : InstId) :
    (releaseOutbound w dead).roster = w.roster ∧
      ((releaseOutbound w dead).st i).life = (w.st i).life ∧
      ((releaseOutbound w dead).st i).typestate = (w.st i).typestate ∧
      ((releaseOutbound w dead).st i).phase = (w.st i).phase ∧
      ((releaseOutbound w dead).st i).parked =
        (if i ∈ w.roster ∧ i ≠ dead then (w.st i).parked.filter (fun p => p.sender != dead)
          else (w.st i).parked) :=
  outFold_fields dead w.roster w i

/-- Sealing or marking an actor: same typestate, a halted life, and the idle phase. -/
theorem sem_seal (I : Impl) (w : World) (id : InstId) (a : Actor) (hS : SemInv I w)
    (hty : a.typestate = (w.st id).typestate) (hhalt : Halted a.life) (hph : a.phase = .idle)
    (hmem : id ∈ w.roster) : SemInv I (setActor w id a) := by
  have hnot : a.life ≠ .alive := by
    rw [hhalt]
    intro h'
    cases h'
  have hty' : ∀ r, ((setActor w id a).st (.core r)).typestate = (w.st (.core r)).typestate := by
    intro r
    by_cases hq : InstId.core r = id
    · rw [hq, setActor_self]
      exact hty
    · rw [setActor_other w id _ a hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hlive
    have hold : groupLive w g := by
      intro r hr
      have hl := hlive r hr
      by_cases hq : InstId.core r = id
      · rw [hq, setActor_self] at hl
        exact absurd hl hnot
      · rw [setActor_other w id _ a hq] at hl
        exact hl
    rw [roleTuple_stable w (setActor w id a) g (fun r _ => hty' r)]
    exact hS.compat g hg hold
  · intro g hg
    refine ⟨?_, ?_⟩
    · rw [roleTuple_stable w (setActor w id a) g (fun r _ => hty' r)]
      exact (hS.live g hg).1
    · intro r hr
      by_cases hq : InstId.core r = id
      · rw [hq, setActor_self]
        exact Or.inr hhalt
      · rw [setActor_other w id _ a hq]
        exact (hS.live g hg).2 r hr
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]
      simp [contTy, hph]
    · rw [setActor_other w id i a hi]
      exact hS.cont i
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]
      simp [programOk, hph]
    · rw [setActor_other w id i a hi]
      exact hS.prog i
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self]
      simp [waitEdge, hph]
    · rw [setActor_other w id i a hi]
      exact hS.waited i
  · intro i hn
    by_cases hi : i = id
    · rw [hi, setActor_self]
      exact Or.inl hph
    · rw [setActor_other w id i a hi] at hn ⊢
      exact hS.idleOff i hn
  · intro i hl
    by_cases hi : i = id
    · rw [hi]
      exact hmem
    · rw [setActor_other w id i a hi] at hl
      exact hS.rostered i hl
  · intro i hmiss
    by_cases hi : i = id
    · exact absurd (hi ▸ hmem) hmiss
    · rw [setActor_other w id i a hi]
      exact hS.offEmpty i hmiss

/-- A live actor stops: its parked entries stay until the seal, and its sender
entries elsewhere are covered by the halted life. -/
theorem mail_halt (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hwas : (w.st id).life = .alive) (hhalt : Halted a.life) (hnew : notParked a.phase)
    (hlist : a.parked = (w.st id).parked) : MailInv (setActor w id a) := by
  have hpk : ∀ i, ((setActor w id a).st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hlist]
    · rw [setActor_other w id i a hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    rw [hpk] at hp
    by_cases hs : p.sender = id
    · right
      rw [hs, setActor_self]
      exact hhalt
    · rw [setActor_other w id p.sender a hs]
      exact hM.fwd mb p hp
  · intro s dst c k hph
    have hs : s ≠ id := by
      intro he
      rw [he, setActor_self] at hph
      rw [hph] at hnew
      exact hnew
    rw [setActor_other w id s a hs] at hph
    rcases hM.bwd s dst c k hph with ⟨p, hp, hps, hpc⟩ | ⟨hc, hd⟩
    · exact Or.inl ⟨p, by rw [hpk]; exact hp, hps, hpc⟩
    · right
      refine ⟨hc, ?_⟩
      by_cases hdi : dst = id
      · rw [hdi, hwas] at hd
        cases hd
      · rw [setActor_other w id dst a hdi]
        exact hd
  · intro mb1 mb2 p1 p2 h1 h2 hs
    rw [hpk] at h1 h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs
  · intro mb
    rw [hpk]
    exact hM.once mb

/-- Dropping every parked entry whose sender is `dead`, which is not itself parked. -/
theorem mail_unpark (w w' : World) (dead : InstId) (hM : MailInv w)
    (hfree : notParked (w.st dead).phase)
    (hl : ∀ i, (w'.st i).life = (w.st i).life) (hp : ∀ i, (w'.st i).phase = (w.st i).phase)
    (hk : ∀ i, (w'.st i).parked = (w.st i).parked ∨
      (w'.st i).parked = (w.st i).parked.filter fun p => p.sender != dead) : MailInv w' := by
  have hsub : ∀ i p, p ∈ (w'.st i).parked → p ∈ (w.st i).parked := by
    intro i p hm
    rcases hk i with h | h
    · rw [h] at hm
      exact hm
    · rw [h] at hm
      exact (List.mem_filter.mp hm).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hm
    rcases hM.fwd mb p (hsub mb p hm) with ⟨k, hph⟩ | hh
    · exact Or.inl ⟨k, by rw [hp]; exact hph⟩
    · exact Or.inr (by rw [hl]; exact hh)
  · intro s dst c k hph
    rw [hp s] at hph
    have hsd : s ≠ dead := by
      intro he
      rw [he] at hph
      rw [hph] at hfree
      exact hfree
    rcases hM.bwd s dst c k hph with ⟨p, hm, hps, hpc⟩ | ⟨hc, hd⟩
    · left
      refine ⟨p, ?_, hps, hpc⟩
      rcases hk dst with h | h
      · rw [h]
        exact hm
      · rw [h]
        exact List.mem_filter.mpr ⟨hm, by rw [hps]; simp [hsd]⟩
    · exact Or.inr ⟨hc, by rw [hl]; exact hd⟩
  · intro mb1 mb2 p1 p2 h1 h2 hs
    exact hM.uniq mb1 mb2 p1 p2 (hsub mb1 p1 h1) (hsub mb2 p2 h2) hs
  · intro mb
    rcases hk mb with h | h
    · rw [h]
      exact hM.once mb
    · rw [h]
      exact nodup_filter _ (hM.once mb)

theorem outHost_queues (w : World) (dead host i : InstId) :
    ((outHost w dead host).st i).box = (w.st i).box ∧
      ((outHost w dead host).st i).prio = (w.st i).prio ∧
      ((outHost w dead host).st i).parent = (w.st i).parent ∧
      (outHost w dead host).crashed = w.crashed := by
  unfold outHost
  by_cases hh : (host == dead) = true
  · rw [ite_eq_left hh]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [ite_eq_right hh]
    dsimp only
    by_cases he : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · rw [ite_eq_left he]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [ite_eq_right he]
      by_cases hi : i = host
      · subst hi
        have hne : i ≠ dead := fun hd => hh (beq_iff_eq.mpr hd)
        refine ⟨?_, ?_, ?_, rfl⟩
        all_goals simp [setActor_self, setActor_other, addTokens, hne]
      · by_cases hd : i = dead
        · subst hd
          refine ⟨?_, ?_, ?_, rfl⟩
          all_goals simp [setActor_self, setActor_other, addTokens, hi]
        · refine ⟨?_, ?_, ?_, rfl⟩
          all_goals simp [setActor_other, addTokens, hi, hd]

theorem outFold_queues (dead : InstId) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun w host => outHost w dead host) w).st i).box = (w.st i).box ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).prio = (w.st i).prio ∧
      ((ids.foldl (fun w host => outHost w dead host) w).st i).parent = (w.st i).parent ∧
      (ids.foldl (fun w host => outHost w dead host) w).crashed = w.crashed := by
  induction ids generalizing w with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons h hs ih =>
    simp only [List.foldl_cons]
    obtain ⟨b1, p1, a1, c1⟩ := ih (outHost w dead h)
    obtain ⟨b0, p0, a0, c0⟩ := outHost_queues w dead h i
    exact ⟨b1.trans b0, p1.trans p0, a1.trans a0, c1.trans c0⟩

theorem releaseOutbound_queues (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).box = (w.st i).box ∧
      ((releaseOutbound w dead).st i).prio = (w.st i).prio ∧
      ((releaseOutbound w dead).st i).parent = (w.st i).parent ∧
      (releaseOutbound w dead).crashed = w.crashed := by
  rw [releaseOutbound_eq]
  exact outFold_queues dead w.roster w i

theorem releaseOutbound_inv (I : Impl) (w : World) (dead : InstId) (h : Inv I w)
    (hfree : notParked (w.st dead).phase) : Inv I (releaseOutbound w dead) := by
  have hf := releaseOutbound_fields w dead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sem_shape I w _ h.1 (hf dead).1 (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
      (fun i => (hf i).2.2.2.1)
    intro i hi
    rw [(hf i).2.2.2.2, ite_eq_right (fun hc => hi hc.1)]
  · apply mail_unpark w _ dead h.2.1 hfree (fun i => (hf i).2.1) (fun i => (hf i).2.2.2.1)
    intro i
    rw [(hf i).2.2.2.2]
    by_cases hc : i ∈ w.roster ∧ i ≠ dead
    · rw [ite_eq_left hc]
      exact Or.inr rfl
    · rw [ite_eq_right hc]
      exact Or.inl rfl
  · exact open_shape w _ h.2.2.1 (fun i hi => by rw [(hf i).1]; exact hi) (fun i => (hf i).2.1)
  · exact outcome_shape I w _ h.2.2.2.1 (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.1)
  · exact ParentForest.parents h.forest (fun i => releaseOutbound_parent w dead i) (hf dead).1
  · have hq := fun i => releaseOutbound_queues w dead i
    exact {
      liveParked := parkedLive_sub h.seal.liveParked (fun i => (hf i).2.1) (fun host p hp => by
        rw [(hf host).2.2.2.2] at hp
        by_cases hc : host ∈ w.roster ∧ host ≠ dead
        · rw [ite_eq_left hc] at hp
          exact (List.mem_filter.mp hp).1
        · rw [ite_eq_right hc] at hp
          exact hp)
      quiet := by
        rcases h.seal.quiet with hcr | hq0
        · exact Or.inl ((hq dead).2.2.2.trans hcr)
        · refine Or.inr fun id hna => ?_
          have hna0 : (w.st id).life ≠ .alive := by
            intro ha
            exact hna ((hf id).2.1 ▸ ha)
          rcases hq0 id hna0 with ⟨hb, hp⟩
          refine ⟨by rw [(hq id).1, hb], ?_⟩
          rw [(hf id).2.2.2.2]
          split
          · simp [hp]
          · rw [hp]
      childless := childless_stable h.seal.childless (hq dead).2.2.2 (fun i => (hf i).2.1)
        (fun i => releaseOutbound_parent w dead i)
      chain := chain_edit h.seal.chain h.seal.childless h.forest (hq dead).2.2.2 (hf dead).1
        (fun i => (hf i).2.1) (fun i => releaseOutbound_parent w dead i)
        (fun i m hm => Or.inl ⟨m, (hq i).1 ▸ hm, rfl, rfl⟩)
        (fun i m hm => Or.inl ⟨m, (hq i).2.1 ▸ hm, rfl, rfl⟩)
        (fun parent id ht => Or.inl (by
          obtain ⟨m, hm, htomb, hsnd⟩ := ht
          exact ⟨m, (hq parent).2.1.symm ▸ hm, htomb, hsnd⟩))
      parkedFrom := parkedFrom_sub h.seal.parkedFrom (fun host p hp => by
        rw [(hf host).2.2.2.2] at hp
        by_cases hc : host ∈ w.roster ∧ host ≠ dead
        · rw [ite_eq_left hc] at hp
          exact (List.mem_filter.mp hp).1
        · rw [ite_eq_right hc] at hp
          exact hp)
      hostedMail := hostedMail_same h.seal.hostedMail (hf dead).1 (fun i => (hq i).1)
        (fun i => (hq i).2.1) }

/-- `Inv` is the tombstone chain with an empty gap. -/
theorem except_of_inv {I : Impl} {w : World} (h : Inv I w) : ExceptInv I w (fun _ => False) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.forest,
    { liveParked := h.seal.liveParked, quiet := h.seal.quiet, childless := h.seal.childless,
      chain := gap_of_chain h.seal.chain, parkedFrom := h.seal.parkedFrom,
      hostedMail := h.seal.hostedMail }⟩

/-- A larger gap exempts more ids, so the chain for the smaller gap still holds. -/
theorem gap_widen {w : World} {gap gap' : InstId → Prop} (h : TombGap w gap)
    (hsub : ∀ i, gap i → gap' i) : TombGap w gap' :=
  fun i hc hd hf hng => h i hc hd hf (fun hg => hng (hsub i hg))

/-- Replace the waived chain and keep the other seal facts. -/
theorem except_chain {I : Impl} {w : World} {gap gap' : InstId → Prop}
    (h : ExceptInv I w gap) (hc : TombGap w gap') : ExceptInv I w gap' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.forest,
    { liveParked := h.seal.liveParked, quiet := h.seal.quiet, childless := h.seal.childless,
      chain := hc, parkedFrom := h.seal.parkedFrom, hostedMail := h.seal.hostedMail }⟩

/-- The extra disjunct is empty, so the only exempt id is the actor just sealed. -/
theorem gap_only_id {w : World} {ex : InstId} {gap : InstId → Prop}
    (h : TombGap w (fun i => i = ex ∨ gap i ∧ (w.st i).parent ≠ some ex))
    (hno : ∀ i, ¬ gap i) : TombGap w (fun i => i = ex) := by
  intro i hc hd hf hng
  exact h i hc hd hf (by
    intro hbad
    rcases hbad with hbad | hbad
    · exact hng hbad
    · exact hno i hbad.1)

/-- Sealing `ex` while its parent is already dead does not waive `ex`: the
parent's mail stays in flight, which is the ancestor half of the chain. -/
theorem gap_drop_dead {w : World} {ex : InstId} {gap : InstId → Prop}
    (h : TombGap w (fun i => i = ex ∨ gap i ∧ (w.st i).parent ≠ some ex))
    (hF : ParentForest w)
    (hdead : match (w.st ex).parent with
      | none => True
      | some p => (w.st p).life ≠ .alive) : TombGap w gap := by
  intro i hc hd hf hng
  by_cases he : i = ex
  · cases hpar : (w.st ex).parent with
    | none =>
      rw [he, hpar]
      trivial
    | some p =>
      rw [he, hpar]
      have hna : (w.st p).life ≠ .alive := by
        rw [hpar] at hdead
        exact hdead
      exact Or.inr ⟨hna, flight_ancestor w hF ex p hpar (by rw [← he]; exact hf)⟩
  · exact h i hc hd hf (by
      intro hbad
      rcases hbad with hbad | hbad
      · exact he hbad
      · exact hng hbad.1)

/-- The seal of a live actor, after its outbound entries are gone. Ids already
in `gap` stay waived, except a child of `id`: that child is repaired because
`id` is now dead, and `id` itself is the new waiver. -/
theorem release_inv (I : Impl) (w w4 : World) (id : InstId) {gap : InstId → Prop}
    (h : ExceptInv I w gap)
    (hgo : (w.st id).life = .alive)
    (hr : w4.roster = w.roster) (hl : ∀ i, (w4.st i).life = (w.st i).life)
    (ht : ∀ i, (w4.st i).typestate = (w.st i).typestate) (hp : ∀ i, (w4.st i).phase = (w.st i).phase)
    (hpar : ∀ i, (w4.st i).parent = (w.st i).parent)
    (hk : ∀ i, i ≠ id → (w4.st i).parked = (w.st i).parked.filter fun p => p.sender != id)
    (hbox : ∀ i, (w4.st i).box = (w.st i).box)
    (hprio : ∀ i, (w4.st i).prio = (w.st i).prio)
    (hcr : w4.crashed = w.crashed)
    (hkids : ∀ c, c ≠ id → (w.st c).parent = some id → (w.st c).life ≠ .alive) :
    ExceptInv I (releaseParked (setActor w4 id
      { (w4.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] })
      id (w.st id).parked)
      (fun i => i = id ∨ gap i ∧ (w.st i).parent ≠ some id) := by
  have hS := h.1
  have hM := h.2.1
  have hmem : id ∈ w.roster :=
    h.2.2.1 id (by rw [hgo]; intro he; cases he)
  have hoff : ∀ i, i ∉ w.roster → (w4.st i).parked = (w.st i).parked := by
    intro i hi
    have hne : i ≠ id := fun he => hi (he ▸ hmem)
    rw [hk i hne, hS.offEmpty i hi]
    rfl
  generalize hdead :
    ({ (w4.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] } : Actor) = dead
  have hdl : dead.life = .dead := by rw [← hdead]
  have hdp : dead.phase = .idle := by rw [← hdead]
  have hdk : dead.parked = [] := by rw [← hdead]
  have hdb : dead.box = [] := by rw [← hdead]
  have hdpr : dead.prio = [] := by rw [← hdead]
  have hdt : dead.typestate = (w4.st id).typestate := by rw [← hdead]
  have hS4 : SemInv I w4 := sem_shape I w w4 hS hr hl ht hp hoff
  have hS5 : SemInv I (setActor w4 id dead) :=
    sem_seal I w4 id dead hS4 hdt hdl hdp (by rw [hr]; exact hmem)
  have hst5 : ∀ i, i ≠ id → (setActor w4 id dead).st i = w4.st i :=
    fun i hi => setActor_other w4 id i dead hi
  have hid5 : (setActor w4 id dead).st id = dead := setActor_self w4 id dead
  rw [release_fold_eq]
  have hidF : (releaseFold id (w.st id).parked (setActor w4 id dead)).st id = dead :=
    (release_spares_id id _ _).trans hid5
  refine ⟨release_sem I _ id _ hS5, ?_, ?_, ?_, ?_, ?_⟩
  · apply mail_of_abort w _ id (w.st id).parked hM (fun p => Iff.rfl)
    · rw [hidF]
      exact hdp
    · rw [hidF]
      exact hdk
    · intro i hi
      rw [release_parked_all id _ _ i, hst5 i hi, hk i hi]
    · intro p hpm hc
      by_cases hs : p.sender = id
      · rw [hs, hidF, hdp]
        trivial
      · exact release_resumed id _ _ p hpm hc hs
    · intro p hpm hs hc
      rw [release_skips_sender id _ _ p.sender (fun q hq hqs => by
          rw [(hM.uniq id id q p hq hpm hqs).2]
          exact hc), hst5 _ hs, hp p.sender]
    · rw [hidF]
      exact hdl
    · intro i hi hns
      left
      rw [release_st_other id _ i _ hns, hst5 i hi, hp i]
    · intro i hd
      rw [release_life]
      by_cases hi : i = id
      · rw [hi, hid5]
        exact hdl
      · rw [hst5 i hi, hl i]
        exact hd
    · intro i hh
      rw [release_life]
      by_cases hi : i = id
      · rw [hi, hid5]
        exact hdl
      · rw [hst5 i hi, hl i]
        exact hh
    · intro i mb c k hph
      have ha := busy_alive I w hS i (by rw [hph]; intro he; cases he) (by rw [hph]; intro he; cases he)
      rw [ha]
      intro hh
      cases hh
  · intro i hlife
    rw [release_life] at hlife
    rw [release_roster]
    show i ∈ w4.roster
    rw [hr]
    by_cases hi : i = id
    · rw [hi]
      exact hmem
    · rw [hst5 i hi, hl i] at hlife
      exact h.2.2.1 i hlife
  · apply release_outcome
    intro i
    by_cases hi : i = id
    · rw [hi, hid5]
      unfold outcomeOk
      rw [hdp]
      trivial
    · rw [hst5 i hi]
      exact outcome_congr I i (hp i) (ht i) (h.2.2.2.1 i)
  · rw [← release_fold_eq]
    exact ParentForest.parents
      (ParentForest.setActor (ParentForest.parents h.forest hpar hr) (by rw [← hdead]))
      (fun i => releaseParked_parent _ id _ i)
      (by rw [release_fold_eq]; exact release_roster id _ _)
  · let base := setActor w4 id dead
    let wF := releaseFold id (w.st id).parked base
    have hlifeF : ∀ i, (wF.st i).life = (base.st i).life := fun i => release_life id _ base i
    have hboxF : ∀ i, (wF.st i).box = (base.st i).box := fun i => release_box id _ base i
    have hprioF : ∀ i, (wF.st i).prio = (base.st i).prio := fun i => release_prio id _ base i
    have hpkF : ∀ i, (wF.st i).parked = (base.st i).parked := fun i => release_parked_all id _ base i
    have hparF : ∀ i, (wF.st i).parent = (base.st i).parent := by
      intro i
      simpa [wF, base, release_fold_eq] using releaseParked_parent base id (w.st id).parked i
    have hcrF : wF.crashed = w.crashed := by
      simpa [wF, base, setActor] using (release_crashed id (w.st id).parked base).trans hcr
    have hroF : wF.roster = w.roster := by
      simpa [wF, base, setActor, hr] using release_roster id (w.st id).parked base
    have hlifeId : (wF.st id).life = .dead := by rw [hlifeF, hid5, hdl]
    have hboxId : (wF.st id).box = [] := by rw [hboxF, hid5, hdb]
    have hprioId : (wF.st id).prio = [] := by rw [hprioF, hid5, hdpr]
    have hpkId : (wF.st id).parked = [] := by rw [hpkF, hid5, hdk]
    have hlift : ∀ i, i ≠ id → (wF.st i).life = (w.st i).life := by
      intro i hi
      rw [hlifeF, hst5 i hi, hl i]
    have hboxLift : ∀ i, i ≠ id → (wF.st i).box = (w.st i).box := by
      intro i hi
      rw [hboxF, hst5 i hi, hbox i]
    have hprioLift : ∀ i, i ≠ id → (wF.st i).prio = (w.st i).prio := by
      intro i hi
      rw [hprioF, hst5 i hi, hprio i]
    have hpkLift : ∀ i, i ≠ id → (wF.st i).parked = (w.st i).parked.filter fun p => p.sender != id := by
      intro i hi
      rw [hpkF, hst5 i hi, hk i hi]
    have hparLift : ∀ i, (wF.st i).parent = (w.st i).parent := by
      intro i
      by_cases hi : i = id
      · rw [hi, hparF, hid5, ← hdead, hpar id]
      · rw [hparF, hst5 i hi, hpar i]
    exact {
      liveParked := by
        intro host p ha hp
        have hneHost : host ≠ id := by
          intro heq
          rw [heq, hlifeId] at ha
          cases ha
        rw [hpkLift host hneHost] at hp
        have hmemP : p ∈ (w.st host).parked := (List.mem_filter.mp hp).1
        have hsender : p.sender ≠ id := by
          intro heq
          have hkeep : (p.sender != id) = true := (List.mem_filter.mp hp).2
          simp [heq] at hkeep
        have ha0 : (w.st host).life = .alive := by rw [← hlift host hneHost]; exact ha
        have hsend0 : (w.st p.sender).life ≠ .dead := h.seal.liveParked host p ha0 hmemP
        rw [hlift p.sender hsender]
        exact hsend0
      quiet := by
        rcases h.seal.quiet with hcr0 | hq
        · exact Or.inl (hcrF.trans hcr0)
        · refine Or.inr fun i hna => ?_
          by_cases hi : i = id
          · rw [hi]
            exact ⟨hboxId, hpkId⟩
          · have hna0 : (w.st i).life ≠ .alive := by
              intro ha
              exact hna (by rw [hlift i hi]; exact ha)
            rcases hq i hna0 with ⟨hb, hp0⟩
            refine ⟨(hboxLift i hi).trans hb, ?_⟩
            rw [hpkLift i hi, hp0]
            simp
      childless := childless_kill h.seal.childless hcrF hlift (by rw [hlifeId]; intro ha; cases ha)
        hparLift hkids
      chain := chain_gap_kill h.seal.chain h.seal.childless h.forest
        hcrF hroF hlifeId hlift hparLift
        (fun i m hm => by
          by_cases hi : i = id
          · rw [hi, hboxId] at hm
            cases hm
          · exact Or.inl ⟨m, by rw [← hboxLift i hi]; exact hm, rfl, rfl⟩)
        (fun i m hm => by
          by_cases hi : i = id
          · rw [hi, hprioId] at hm
            cases hm
          · exact Or.inl ⟨m, by rw [← hprioLift i hi]; exact hm, rfl, rfl⟩)
        (fun parent id0 hpx ht => by
          obtain ⟨m, hm, htomb, hsnd⟩ := ht
          exact Or.inl ⟨m, by rw [hprioLift parent hpx]; exact hm, htomb, hsnd⟩)
      parkedFrom := by
        intro host p hp
        by_cases hh : host = id
        · rw [hh, hpkId] at hp
          cases hp
        · rw [hpkLift host hh] at hp
          exact h.seal.parkedFrom host p (List.mem_filter.mp hp).1
      hostedMail := by
        intro host m hm
        by_cases hh : host = id
        · rw [hh] at hm
          rcases hm with hm | hm
          · rw [hboxId] at hm
            cases hm
          · rw [hprioId] at hm
            cases hm
        · rw [hroF]
          rcases hm with hm | hm
          · exact h.seal.hostedMail host m (Or.inl (by rw [← hboxLift host hh]; exact hm))
          · exact h.seal.hostedMail host m (Or.inr (by rw [← hprioLift host hh]; exact hm))
    }

theorem readCells_crashed (D : Description) (w : World) (id : InstId) :
    (readCells D w id).crashed = w.crashed := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (by simp [setCell, setObserved])

theorem releaseWorld_gap (I : Impl) (D : Description) (w : World) (id : InstId)
    {gap : InstId → Prop} (h : ExceptInv I w gap)
    (hgo : (w.st id).life = .alive)
    (hkids : ∀ c, c ≠ id → (w.st c).parent = some id → (w.st c).life ≠ .alive) :
    ExceptInv I (releaseWorld D w id (w.st id))
      (fun i => i = id ∨ gap i ∧ (w.st i).parent ≠ some id) := by
  have hs3 : Same w (refundParked (refundMsgs (readCells D w id) (tname id) (w.st id).box)
      (tname id) (w.st id).parked) :=
    same_trans (same_trans (same_cells D w id) (same_refundMsgs _ _ _)) (same_refundParked _ _ _)
  generalize hw3 : refundParked (refundMsgs (readCells D w id) (tname id) (w.st id).box)
      (tname id) (w.st id).parked = w3 at hs3
  have hrel : releaseWorld D w id (w.st id) =
      releaseParked (setActor (releaseOutbound w3 id) id
        { ((releaseOutbound w3 id).st id) with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }) id (w.st id).parked := by
    rw [← hw3]
    rfl
  rw [hrel]
  have hf := releaseOutbound_fields w3 id
  have hboxW : ∀ i, ((releaseOutbound w3 id).st i).box = (w.st i).box := by
    intro i
    rw [(releaseOutbound_queues w3 id i).1, ← hw3]
    rw [(refundParked_fields (refundMsgs (readCells D w id) (tname id) (w.st id).box)
        (tname id) (w.st id).parked i).2.2.1]
    rw [(refundMsgs_fields (readCells D w id) (tname id) (w.st id).box i).2.2.1]
    rw [cellsSt]
  have hprioW : ∀ i, ((releaseOutbound w3 id).st i).prio = (w.st i).prio := by
    intro i
    rw [(releaseOutbound_queues w3 id i).2.1, ← hw3]
    rw [(refundParked_fields (refundMsgs (readCells D w id) (tname id) (w.st id).box)
        (tname id) (w.st id).parked i).2.2.2.2]
    rw [(refundMsgs_fields (readCells D w id) (tname id) (w.st id).box i).2.2.2.2]
    rw [cellsSt]
  have hcrW : (releaseOutbound w3 id).crashed = w.crashed := by
    rw [(releaseOutbound_queues w3 id id).2.2.2, ← hw3]
    exact (refundParked_crashed _ _ _).trans
      ((refundMsgs_crashed _ _ _).trans (readCells_crashed _ _ _))
  apply release_inv I w (releaseOutbound w3 id) id h hgo ((hf id).1.trans hs3.roster)
    (fun i => (hf i).2.1.trans (hs3.life i)) (fun i => (hf i).2.2.1.trans (hs3.ty i))
    (fun i => (hf i).2.2.2.1.trans (hs3.phase i))
    (fun i => (releaseOutbound_parent w3 id i).trans (hs3.parent i))
    (fun i hi => by
      rw [(hf i).2.2.2.2, hs3.parked i]
      by_cases hm : i ∈ w3.roster
      · rw [ite_eq_left ⟨hm, hi⟩]
      · rw [ite_eq_right (fun hc => hm hc.1)]
        rw [hs3.roster] at hm
        rw [h.1.offEmpty i hm]
        rfl)
    hboxW hprioW hcrW hkids

/-- Releasing from a full chain waives only the actor that just died. -/
theorem releaseWorld_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w)
    (hgo : (w.st id).life = .alive)
    (hkids : ∀ c, c ≠ id → (w.st c).parent = some id → (w.st c).life ≠ .alive) :
    ExceptInv I (releaseWorld D w id (w.st id)) (fun i => i = id) := by
  have hwide := releaseWorld_gap I D w id (except_of_inv h) hgo hkids
  refine except_chain hwide ?_
  intro i hc hd hf hng
  exact hwide.seal.chain i hc hd hf (by
    intro hbad
    rcases hbad with hbad | hbad
    · exact hng hbad
    · exact hbad.1)

theorem closed_inv {I : Impl} {w : World} {ex : InstId}
    (h : ExceptInv I w (fun i => i = ex))
    (hfix : mailInFlight w ex = true →
      match (w.st ex).parent with
      | none => True
      | some p =>
          ((w.st p).life = .alive ∧ HoldsTomb w p ex) ∨
          ((w.st p).life ≠ .alive ∧ mailInFlight w p = true)) : Inv I w :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.forest,
    { liveParked := h.seal.liveParked, quiet := h.seal.quiet, childless := h.seal.childless,
      chain := chain_close h.seal.chain hfix, parkedFrom := h.seal.parkedFrom,
      hostedMail := h.seal.hostedMail }⟩

/-- Queuing the exempt actor's tombstone, or crashing, or finding no live parent,
restores `Inv`. -/
theorem enqueue_closes (I : Impl) (D : Description) (w : World) (child : InstId)
    (h : ExceptInv I w (fun i => i = child)) : Inv I (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  match hpar : (w.st child).parent with
  | none => exact closed_inv h (by intro _; rw [hpar]; trivial)
  | some parent =>
    simp only [hpar]
    split
    · next hdead =>
      exact closed_inv h (by
        intro hf
        rw [hpar]
        refine Or.inr ⟨?_, flight_ancestor w h.forest child parent hpar hf⟩
        intro ha
        have hb : ((w.st parent).life == .alive) = true := by simpa [beq_iff_eq] using ha
        have hbad : ((w.st parent).life != .alive) = false := by
          show (!((w.st parent).life == .alive)) = false
          rw [hb]
          rfl
        exact absurd (hbad.symm.trans hdead) Bool.false_ne_true)
    · next hlive =>
      split
      · exact crash_except I w h
      · unfold offerPrio
        dsimp only
        split
        · exact crash_except I w h
        · have halive : (w.st parent).life = .alive := by
            by_cases ha : (w.st parent).life = .alive
            · exact ha
            · have hb : ((w.st parent).life == .alive) = false := by
                simpa [beq_iff_eq] using ha
              have hne : ((w.st parent).life != .alive) = true := by
                show (!((w.st parent).life == .alive)) = true
                rw [hb]
                rfl
              exact absurd hne hlive
          let msg := tombstoneMsg D (w.st parent) child
          exact except_frame I w _ h
            (same_actor w parent (withPrio (w.st parent) msg) rfl rfl rfl rfl rfl)
            (seal_grow_close w parent msg h.seal h.forest hpar halive rfl
              (roster_of_parent h.forest hpar))

theorem sealActor_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w)
    (hgo : (w.st id).life = .alive)
    (hkids : ∀ c, c ≠ id → (w.st c).parent = some id → (w.st c).life ≠ .alive) :
    Inv I (sealActor D w id (w.st id)) := by
  unfold sealActor
  exact enqueue_closes I D _ id (releaseWorld_inv I D w id h hgo hkids)

theorem shutdownActor_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w)
    (hkids : ∀ c, c ≠ id → (w.st c).parent = some id → (w.st c).life ≠ .alive) :
    Inv I (shutdownActor D w id) := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · rw [ite_eq_left hlive]
    exact sealActor_inv I D w id h (by simpa [beq_iff_eq] using hlive) hkids
  · rw [ite_eq_right hlive]
    exact h

theorem releaseWorld_life_ne (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (hi : i ≠ id) : ((releaseWorld D w id a).st i).life = (w.st i).life := by
  have hs3 : Same w (refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked) :=
    same_trans (same_trans (same_cells D w id) (same_refundMsgs _ _ _)) (same_refundParked _ _ _)
  simp only [releaseWorld]
  rw [release_fold_eq, release_life, setActor_other _ id i _ hi, (releaseOutbound_fields _ id i).2.1]
  exact hs3.life i

theorem releaseWorld_roster (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).roster = w.roster := by
  have hs3 : Same w (refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked) :=
    same_trans (same_trans (same_cells D w id) (same_refundMsgs _ _ _)) (same_refundParked _ _ _)
  simp only [releaseWorld]
  rw [release_fold_eq, release_roster, setActor, (releaseOutbound_fields _ id id).1, hs3.roster]

/-- Every descending chain from `id` has at most `n` steps. `0` means no proper child. -/
def DescShort (w : World) (id : InstId) : Nat → Prop
  | 0 => ∀ c, (w.st c).parent = some id → c = id
  | n + 1 => ∀ c, c ≠ id → (w.st c).parent = some id → DescShort w c n

theorem desc_short_parent {w w' : World} (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    {id : InstId} {n : Nat} (h : DescShort w id n) : DescShort w' id n := by
  induction n generalizing id with
  | zero =>
    intro c hp
    exact h c (by rw [hpar c] at hp; exact hp)
  | succ n ih =>
    intro c hc hp
    exact ih (h c hc (by rw [← hpar c]; exact hp))

/-- `xs` is a chain of proper descendants of `id`, nearest child first. -/
inductive DPath (w : World) : InstId → List InstId → Prop where
  | nil {id : InstId} : DPath w id []
  | cons {id c : InstId} {rest : List InstId} :
      (w.st c).parent = some id → c ≠ id → DPath w c rest → DPath w id (c :: rest)

theorem path_of_not_short {w : World} {id : InstId} {n : Nat} (h : ¬ DescShort w id n) :
    ∃ xs, DPath w id xs ∧ xs.length = n + 1 := by
  induction n generalizing id with
  | zero =>
    obtain ⟨c, hc⟩ := Classical.not_forall.mp h
    have hc' := Classical.not_imp.mp hc
    exact ⟨[c], DPath.cons hc'.1 hc'.2 DPath.nil, rfl⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := Classical.not_forall.mp h
    have hc1 := Classical.not_imp.mp hc
    have hc2 := Classical.not_imp.mp hc1.2
    obtain ⟨xs, hpath, hlen⟩ := ih hc2.2
    exact ⟨c :: xs, DPath.cons hc2.1 hc1.1 hpath, by simp [hlen]⟩

theorem dpath_anc {w : World} {id : InstId} {xs : List InstId} (h : DPath w id xs) :
    ∀ x, x ∈ xs → StrictAncestor w x id := by
  induction h with
  | nil =>
    intro x hx
    cases hx
  | cons hp hne _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact StrictAncestor.edge ⟨hp, hne⟩
    · exact StrictAncestor.trans (ih x hx) (StrictAncestor.edge ⟨hp, hne⟩)

theorem dpath_mem {w : World} (hF : ParentForest w) {id : InstId} {xs : List InstId}
    (h : DPath w id xs) : ∀ x, x ∈ xs → x ∈ w.roster := by
  induction h with
  | nil =>
    intro x hx
    cases hx
  | cons hp _ _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact roster_of_parent hF hp
    · exact ih x hx

theorem dpath_nodup {w : World} (hF : ParentForest w) {id : InstId} {xs : List InstId}
    (h : DPath w id xs) : (id :: xs).Nodup := by
  induction h
  case nil =>
    refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
    intro hx
    cases hx
  case cons pid child rest hp hne hrest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · exact hne hx.symm
    · exact ParentAcyclic.no_self hF.wf pid
        (StrictAncestor.trans (dpath_anc hrest pid hx) (StrictAncestor.edge ⟨hp, hne⟩))

theorem dpath_host {w : World} (hF : ParentForest w) {id c : InstId} {rest : List InstId}
    (h : DPath w id (c :: rest)) : id ∈ w.roster := by
  cases h with
  | cons hp _ _ =>
    exact hF.hosted c id hp

/-- A descending chain is a duplicate-free roster list, so it fits in the roster. -/
theorem desc_short_roster (w : World) (hF : ParentForest w) (id : InstId) :
    DescShort w id (w.roster.length - 1) := by
  exact Classical.byContradiction fun h => by
    obtain ⟨xs, hpath, hlen⟩ := path_of_not_short h
    have hnd := dpath_nodup hF hpath
    have hsub : ∀ x, x ∈ id :: xs → x ∈ w.roster := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        cases xs with
        | nil =>
          simp only [List.length_nil] at hlen
          omega
        | cons c rest =>
          exact dpath_host hF hpath
      · exact dpath_mem hF hpath x hx
    have hle := nodup_length_le (id :: xs) w.roster hnd hsub
    simp only [List.length_cons, hlen] at hle
    omega

theorem strict_of_parent {w w' : World} (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    {desc anc : InstId} (h : StrictAncestor w desc anc) : StrictAncestor w' desc anc := by
  induction h
  case edge d a he =>
    exact StrictAncestor.edge ⟨by rw [hpar d]; exact he.1, he.2⟩
  case tail d mid a he rest ih =>
    exact StrictAncestor.tail ⟨by rw [hpar d]; exact he.1, he.2⟩ ih

theorem seal_parent (fuel : Nat) (D : Description) (w : World) (id i : InstId) :
    ((sealBranch fuel D w id).st i).parent = (w.st i).parent := by
  induction fuel generalizing w id with
  | zero => rfl
  | succ n ih =>
    unfold sealBranch
    dsimp only
    have hfold : ∀ (ids : List InstId) (acc : World),
        ((ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc).st i).parent =
          (acc.st i).parent := by
      intro ids
      induction ids with
      | nil => intro _; rfl
      | cons c cs ihc =>
        intro acc
        simp only [List.foldl_cons]
        split
        · rw [ihc, ih]
        · rw [ihc]
    split
    · rw [releaseWorld_parent, hfold]
    · exact hfold _ _

theorem seal_roster (fuel : Nat) (D : Description) (w : World) (id : InstId) :
    (sealBranch fuel D w id).roster = w.roster := by
  induction fuel generalizing w id with
  | zero => rfl
  | succ n ih =>
    unfold sealBranch
    dsimp only
    have hfold : ∀ (ids : List InstId) (acc : World),
        (ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc).roster =
          acc.roster := by
      intro ids
      induction ids with
      | nil => intro _; rfl
      | cons _ cs ihc =>
        intro acc
        simp only [List.foldl_cons]
        split
        · rw [ihc, ih]
        · rw [ihc]
    split
    · rw [releaseWorld_roster, hfold]
    · exact hfold _ _

theorem seal_not_born (fuel : Nat) (D : Description) (w : World) (id i : InstId)
    (h : (w.st i).life ≠ .alive) : ((sealBranch fuel D w id).st i).life ≠ .alive := by
  induction fuel generalizing w id with
  | zero => exact h
  | succ n ih =>
    unfold sealBranch
    dsimp only
    have hfold : ∀ (ids : List InstId) (acc : World), (acc.st i).life ≠ .alive →
        ((ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc).st i).life ≠
          .alive := by
      intro ids
      induction ids with
      | nil => intro _ ha; exact ha
      | cons _ cs ihc =>
        intro acc ha
        simp only [List.foldl_cons]
        split
        · exact ihc _ (ih _ _ ha)
        · exact ihc _ ha
    have hs := hfold w.roster w h
    split
    · by_cases hi : i = id
      · rw [hi, (releaseWorld_keeps_credit D _ id _).1]
        intro hd
        cases hd
      · rw [releaseWorld_life_ne D _ id _ i hi]
        exact hs
    · exact hs

/-- Sealing `id` does not rewrite `spared` when `spared` is not under `id`. -/
theorem seal_spares (fuel : Nat) (D : Description) (w : World) (id spared : InstId)
    (hF : ParentForest w) (hne : spared ≠ id) (hnot : ¬ StrictAncestor w spared id) :
    ((sealBranch fuel D w id).st spared).life = (w.st spared).life := by
  induction fuel generalizing w id with
  | zero => rfl
  | succ n ih =>
    unfold sealBranch
    dsimp only
    have hfold : ∀ (ids : List InstId) (acc : World),
        (∀ i, (acc.st i).parent = (w.st i).parent) → acc.roster = w.roster →
        ParentForest acc → ¬ StrictAncestor acc spared id →
        ((ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc).st spared).life =
          (acc.st spared).life := by
      intro ids
      induction ids with
      | nil => intro _ _ _ _ _; rfl
      | cons c cs ihc =>
        intro acc hpar hro hFa hnotA
        simp only [List.foldl_cons]
        split
        · next hchild =>
          have hp := isChild_parent acc id c hchild
          have hcne : c ≠ id := by
            simp only [isChild] at hchild
            split at hchild
            · next p hp =>
              exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hchild).2
            · simp at hchild
          have hnotC : ¬ StrictAncestor acc spared c := by
            intro hanc
            exact hnotA (StrictAncestor.trans hanc (StrictAncestor.edge ⟨hp, hcne⟩))
          have hspC : spared ≠ c := by
            intro heq
            exact hnotA (heq ▸ StrictAncestor.edge ⟨hp, hcne⟩)
          have hlife := ih acc c hFa hspC hnotC
          have hparS : ∀ i, ((sealBranch n D acc c).st i).parent = (w.st i).parent := by
            intro i
            rw [seal_parent, hpar]
          have hroS : (sealBranch n D acc c).roster = w.roster := by
            rw [seal_roster, hro]
          rw [ihc (sealBranch n D acc c) hparS hroS
            (ParentForest.parents hF hparS hroS)
            (by
              intro hanc
              exact hnotA (strict_of_parent (fun i => (seal_parent n D acc c i).symm) hanc))]
          exact hlife
        · exact ihc acc hpar hro hFa hnotA
    split
    · rw [releaseWorld_life_ne D _ id _ spared hne]
      exact hfold w.roster w (fun _ => rfl) rfl hF hnot
    · exact hfold w.roster w (fun _ => rfl) rfl hF hnot

/-- Ids waived only as live children of a now-dead `id` are repaired: their mail
keeps `id` in flight. -/
theorem gap_drop_children {w : World} {id : InstId} {gap g : InstId → Prop}
    (h : TombGap w g) (hF : ParentForest w)
    (hsub : ∀ i, g i → gap i ∨ ((w.st i).parent = some id ∧ i ≠ id))
    (hdead : (w.st id).life ≠ .alive) : TombGap w gap := by
  intro i hc hd hf hng
  by_cases hg : g i
  · rcases hsub i hg with hsub | hsub
    · exact absurd hsub hng
    · cases hpar : (w.st i).parent with
      | none =>
        have hbad := hsub.1
        rw [hpar] at hbad
        cases hbad
      | some p =>
        have hp : p = id := by
          have hsome := hsub.1
          rw [hpar] at hsome
          cases hsome
          rfl
        exact Or.inr ⟨by rw [hp]; exact hdead, flight_ancestor w hF i p hpar hf⟩
  · exact h i hc hd hf hg

theorem inv_of_nogap {I : Impl} {w : World} (h : ExceptInv I w (fun _ => False)) : Inv I w :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.forest,
    { liveParked := h.seal.liveParked, quiet := h.seal.quiet, childless := h.seal.childless,
      chain := chain_of_gap h.seal.chain, parkedFrom := h.seal.parkedFrom,
      hostedMail := h.seal.hostedMail }⟩

theorem desc_short_succ {w : World} {id : InstId} {k : Nat} (h : DescShort w id k) :
    DescShort w id (k + 1) := by
  induction k generalizing id with
  | zero =>
    intro c hc hp
    exact absurd (h c hp) hc
  | succ _ ih =>
    intro c hc hp
    exact ih (h c hc hp)

theorem isChild_ne (w : World) (parent child : InstId) (h : isChild w parent child = true) :
    child ≠ parent := by
  simp only [isChild] at h
  split at h
  · next _ _ =>
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp h).2
  · simp at h

/-- The world after sealing every listed child of `id`, with the waiver those
live children add and the facts the parent's own release needs. -/
structure KidsSeal (I : Impl) (id : InstId) (gap gapOf : InstId → Prop)
    (start result : World) : Prop where
  inv : ExceptInv I result gapOf
  sub : ∀ i, gapOf i → gap i ∨ ((start.st i).parent = some id ∧ i ≠ id)
  parent : ∀ i, (result.st i).parent = (start.st i).parent
  roster : result.roster = start.roster
  lifeId : (result.st id).life = (start.st id).life
  kids : ∀ c, c ≠ id → (start.st c).parent = some id → (result.st c).life ≠ .alive
  stays : ∀ j, (start.st j).life ≠ .alive → (result.st j).life ≠ .alive

theorem seal_kids_fold (I : Impl) (n : Nat) (D : Description) (id : InstId)
    (ids : List InstId) (acc : World) {gap : InstId → Prop} (h : ExceptInv I acc gap)
    (hD : DescShort acc id (n + 1))
    (hcover : ∀ c, c ≠ id → (acc.st c).parent = some id → c ∈ ids ∨ (acc.st c).life ≠ .alive)
    (hstep : ∀ (w1 : World) (child : InstId) {g : InstId → Prop},
      ExceptInv I w1 g → DescShort w1 child n →
      ((w1.st child).life = .alive →
          ExceptInv I (sealBranch (n + 1) D w1 child)
            (fun i => i = child ∨ g i ∧ (w1.st i).parent ≠ some child) ∧
          ((sealBranch (n + 1) D w1 child).st child).life = .dead) ∧
      ((w1.st child).life ≠ .alive → ExceptInv I (sealBranch (n + 1) D w1 child) g)) :
    ∃ gapOf, KidsSeal I id gap gapOf acc (ids.foldl (fun acc child =>
      if isChild acc id child then sealBranch (n + 1) D acc child else acc) acc) := by
  induction ids generalizing acc gap with
  | nil =>
    exact ⟨gap, {
      inv := h
      sub := fun i hg => Or.inl hg
      parent := fun _ => rfl
      roster := rfl
      lifeId := rfl
      kids := by
        intro c hne hp
        rcases hcover c hne hp with hmem | hdead
        · exact absurd hmem (List.not_mem_nil (a := c))
        · exact hdead
      stays := fun _ hj => hj
    }⟩
  | cons c cs ihc =>
    simp only [List.foldl_cons]
    split
    · next hchild =>
      have hp := isChild_parent acc id c hchild
      have hcne := isChild_ne acc id c hchild
      have hnot : ¬ StrictAncestor acc id c := by
        intro hanc
        exact ParentAcyclic.no_self h.forest.wf id
          (StrictAncestor.trans hanc (StrictAncestor.edge ⟨hp, hcne⟩))
      have hpar1 : ∀ i, ((sealBranch (n + 1) D acc c).st i).parent = (acc.st i).parent :=
        fun i => seal_parent (n + 1) D acc c i
      have hro1 : (sealBranch (n + 1) D acc c).roster = acc.roster := seal_roster (n + 1) D acc c
      have hstay1 : ∀ j, (acc.st j).life ≠ .alive →
          ((sealBranch (n + 1) D acc c).st j).life ≠ .alive :=
        fun j hj => seal_not_born (n + 1) D acc c j hj
      have hspare := seal_spares (n + 1) D acc c id h.forest (Ne.symm hcne) hnot
      have hDc : DescShort acc c n := hD c hcne hp
      have hpair := hstep acc c h hDc
      let mid := sealBranch (n + 1) D acc c
      by_cases hgo : (acc.st c).life = .alive
      · have hlive := hpair.1 hgo
        have hDmid := desc_short_parent hpar1 hD
        have hcover' : ∀ c', c' ≠ id → (mid.st c').parent = some id →
            c' ∈ cs ∨ (mid.st c').life ≠ .alive := by
          intro c' hne hp'
          have hp0 : (acc.st c').parent = some id := by rw [← hpar1 c']; exact hp'
          rcases hcover c' hne hp0 with hmem | hdead
          · simp only [List.mem_cons] at hmem
            rcases hmem with hmem | hmem
            · exact Or.inr (by rw [hmem, hlive.2]; intro h'; cases h')
            · exact Or.inl hmem
          · exact Or.inr (hstay1 c' hdead)
        obtain ⟨gTail, htail⟩ := ihc mid hlive.1 hDmid hcover'
        exact ⟨gTail, {
          inv := htail.inv
          sub := by
            intro i hi
            rcases htail.sub i hi with hsub | hsub
            · rcases hsub with hsub | hsub
              · refine Or.inr ?_
                rw [hsub]
                exact ⟨hp, hcne⟩
              · exact Or.inl hsub.1
            · exact Or.inr ⟨by rw [← hpar1 i]; exact hsub.1, hsub.2⟩
          parent := fun i => by rw [htail.parent, hpar1]
          roster := by rw [htail.roster, hro1]
          lifeId := by rw [htail.lifeId, hspare]
          kids := by
            intro c' hne hp'
            exact htail.kids c' hne (by rw [hpar1 c']; exact hp')
          stays := fun j hj => htail.stays j (hstay1 j hj)
        }⟩
      · have hna : (acc.st c).life ≠ .alive := hgo
        have hdead := hpair.2 hna
        have hDmid := desc_short_parent hpar1 hD
        have hcover' : ∀ c', c' ≠ id → (mid.st c').parent = some id →
            c' ∈ cs ∨ (mid.st c').life ≠ .alive := by
          intro c' hne hp'
          have hp0 : (acc.st c').parent = some id := by rw [← hpar1 c']; exact hp'
          rcases hcover c' hne hp0 with hmem | hdead0
          · simp only [List.mem_cons] at hmem
            rcases hmem with hmem | hmem
            · exact Or.inr (by rw [hmem]; exact hstay1 c hna)
            · exact Or.inl hmem
          · exact Or.inr (hstay1 c' hdead0)
        obtain ⟨gTail, htail⟩ := ihc mid hdead hDmid hcover'
        exact ⟨gTail, {
          inv := htail.inv
          sub := by
            intro i hi
            rcases htail.sub i hi with hsub | hsub
            · exact Or.inl hsub
            · exact Or.inr ⟨by rw [← hpar1 i]; exact hsub.1, hsub.2⟩
          parent := fun i => by rw [htail.parent, hpar1]
          roster := by rw [htail.roster, hro1]
          lifeId := by rw [htail.lifeId, hspare]
          kids := by
            intro c' hne hp'
            exact htail.kids c' hne (by rw [hpar1 c']; exact hp')
          stays := fun j hj => htail.stays j (hstay1 j hj)
        }⟩
    · next hnotChild =>
      have hcover' : ∀ c', c' ≠ id → (acc.st c').parent = some id →
          c' ∈ cs ∨ (acc.st c').life ≠ .alive := by
        intro c' hne hp
        rcases hcover c' hne hp with hmem | hdead
        · simp only [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · have hrec := isChild_recorded acc id c' hp hne
            rw [hmem] at hrec
            exact absurd hrec hnotChild
          · exact Or.inl hmem
        · exact Or.inr hdead
      exact ihc acc h hD hcover'

/-- Sealing `id` waives `id` when `id` is alive, and leaves the incoming gap when
it is not. A live child is waived only until this release: its parent is `id`,
so the kill repairs it. -/
theorem seal_gap (I : Impl) (n : Nat) (D : Description) (w : World) (id : InstId)
    {gap : InstId → Prop} (h : ExceptInv I w gap) (hD : DescShort w id n) :
    ((w.st id).life = .alive →
        ExceptInv I (sealBranch (n + 1) D w id)
          (fun i => i = id ∨ gap i ∧ (w.st i).parent ≠ some id) ∧
        ((sealBranch (n + 1) D w id).st id).life = .dead) ∧
    ((w.st id).life ≠ .alive → ExceptInv I (sealBranch (n + 1) D w id) gap) := by
  induction n generalizing w id gap with
  | zero =>
    have hfold : (w.roster.foldl (fun acc child =>
        if isChild acc id child then sealBranch 0 D acc child else acc) w) = w := by
      induction w.roster with
      | nil => rfl
      | cons _ _ ih =>
        simp only [List.foldl_cons]
        split
        · rw [show sealBranch 0 D _ _ = _ by rfl]
          exact ih
        · exact ih
    refine ⟨?_, ?_⟩
    · intro hgo
      unfold sealBranch
      dsimp only
      rw [hfold]
      rw [ite_eq_left (by simpa [beq_iff_eq] using hgo)]
      refine ⟨?_, (releaseWorld_keeps_credit D w id (w.st id)).1⟩
      exact releaseWorld_gap I D w id h hgo (by
        intro c hc hp
        exact absurd (hD c hp) hc)
    · intro hna
      unfold sealBranch
      dsimp only
      rw [hfold]
      rw [ite_eq_right (by
        intro hb
        exact hna (beq_iff_eq.mp hb))]
      exact h
  | succ n ih =>
    obtain ⟨_, hk⟩ := seal_kids_fold I n D id w.roster w h hD
      (fun _ _ hp => Or.inl (roster_of_parent h.forest hp))
      (fun w1 child _ hE hDc => ih w1 child hE hDc)
    unfold sealBranch
    dsimp only
    refine ⟨?_, ?_⟩
    · intro hgo
      have hbit : ((((w.roster.foldl (fun acc child =>
          if isChild acc id child then sealBranch (n + 1) D acc child else acc) w).st id).life ==
            .alive)) = true := by
        rw [hk.lifeId]
        simpa [beq_iff_eq] using hgo
      rw [ite_eq_left hbit]
      refine ⟨?_, (releaseWorld_keeps_credit D _ id _).1⟩
      have halive : ((w.roster.foldl (fun acc child =>
          if isChild acc id child then sealBranch (n + 1) D acc child else acc) w).st id).life =
          .alive := by rw [hk.lifeId]; exact hgo
      have hrel := releaseWorld_gap I D _ id hk.inv halive (by
        intro c hne hp
        exact hk.kids c hne (by rw [hk.parent c] at hp; exact hp))
      refine except_chain hrel ?_
      intro i hc hd hf hng
      exact hrel.seal.chain i hc hd hf (by
        intro hbad
        rcases hbad with hbad | hbad
        · exact hng (Or.inl hbad)
        · rcases hk.sub i hbad.1 with hsub | hsub
          · exact hng (Or.inr ⟨hsub, by rw [← hk.parent i]; exact hbad.2⟩)
          · exact hbad.2 (by rw [hk.parent i]; exact hsub.1))
    · intro hna
      rw [ite_eq_right (by
        intro hb
        rw [hk.lifeId] at hb
        exact hna (beq_iff_eq.mp hb))]
      refine except_chain hk.inv ?_
      exact gap_drop_children hk.inv.seal.chain hk.inv.forest (by
        intro i hg
        rcases hk.sub i hg with hsub | hsub
        · exact Or.inl hsub
        · exact Or.inr ⟨by rw [hk.parent i]; exact hsub.1, hsub.2⟩) (by
        rw [hk.lifeId]
        exact hna)

/-- Proper descendants of `id`, sealed, with each live child waived while `id` lives. -/
theorem drop_seal (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w) :
    ∃ gapOf, KidsSeal I id (fun _ => False) gapOf w (dropDescendants D w id) := by
  by_cases hlen : w.roster.length = 0
  · have hempty : w.roster = [] := List.length_eq_zero_iff.mp hlen
    unfold dropDescendants
    rw [hempty]
    exact ⟨fun _ => False, {
      inv := except_of_inv h
      sub := fun _ hg => absurd hg (fun hf => hf)
      parent := fun _ => rfl
      roster := rfl
      lifeId := rfl
      kids := by
        intro c _ hp
        have hmem := roster_of_parent h.forest hp
        rw [hempty] at hmem
        exact absurd hmem (List.not_mem_nil (a := c))
      stays := fun _ hj => hj }⟩
  · have hn : (w.roster.length - 1) + 1 = w.roster.length := by omega
    unfold dropDescendants
    rw [← hn]
    exact seal_kids_fold I (w.roster.length - 1) D id w.roster w (except_of_inv h)
      (desc_short_succ (desc_short_roster w h.forest id))
      (fun _ _ hp => Or.inl (roster_of_parent h.forest hp))
      (fun w1 child _ hE hDc => seal_gap I (w.roster.length - 1) D w1 child hE hDc)

theorem dropDescendants_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w) :
    ExceptInv I (dropDescendants D w id)
      (fun i => i ≠ id ∧ (w.st i).parent = some id) := by
  obtain ⟨_, hk⟩ := drop_seal I D w id h
  refine except_chain hk.inv ?_
  apply gap_widen hk.inv.seal.chain
  intro i hg
  rcases hk.sub i hg with hsub | hsub
  · exact absurd hsub (fun hf => hf)
  · exact ⟨hsub.2, hsub.1⟩

theorem terminateStage_inv (I : Impl) (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : Inv I w) : Inv I (terminateStage D w id a) := by
  obtain ⟨_, hk⟩ := drop_seal I D w id h
  unfold terminateStage
  dsimp only
  unfold shutdownActor
  by_cases hgo : (((dropDescendants D w id).st id).life == .alive) = true
  · rw [ite_eq_left hgo]
    unfold sealActor
    have halive : ((dropDescendants D w id).st id).life = .alive := by
      simpa [beq_iff_eq] using hgo
    have hrel := releaseWorld_gap I D (dropDescendants D w id) id hk.inv halive (by
      intro c hne hp
      exact hk.kids c hne (by rw [hk.parent c] at hp; exact hp))
    refine enqueue_closes I D _ id (except_chain hrel ?_)
    intro i hc hd hf hng
    exact hrel.seal.chain i hc hd hf (by
      intro hbad
      rcases hbad with hbad | hbad
      · exact hng hbad
      · rcases hk.sub i hbad.1 with hsub | hsub
        · exact absurd hsub (fun hf => hf)
        · exact hbad.2 (by rw [hk.parent i]; exact hsub.1))
  · rw [ite_eq_right hgo]
    have hna : ((dropDescendants D w id).st id).life ≠ .alive := by
      intro ha
      exact hgo (beq_iff_eq.mpr ha)
    exact inv_of_nogap (except_chain hk.inv (gap_drop_children hk.inv.seal.chain hk.inv.forest
      (by
        intro i hg
        rcases hk.sub i hg with hsub | hsub
        · exact absurd hsub (fun hf => hf)
        · exact Or.inr ⟨by rw [hk.parent i]; exact hsub.1, hsub.2⟩) hna))

theorem abortChildren_inv (I : Impl) (D : Description) (w : World) (parent : InstId) (h : Inv I w) :
    Inv I (abortChildren D w parent) := by
  unfold abortChildren
  have hfold : ∀ (ids : List InstId) (acc : World), Inv I acc →
      Inv I (ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) acc) := by
    intro ids
    induction ids with
    | nil => intro acc ha; exact ha
    | cons c cs ihc =>
      intro acc ha
      simp only [List.foldl_cons]
      apply ihc
      split
      · have hstep : shutdownActor D (dropDescendants D acc c) c =
            terminateStage D acc c (acc.st c) := by
          unfold terminateStage
          rfl
        rw [hstep]
        exact terminateStage_inv I D acc c _ ha
      · exact ha
  exact hfold w.roster w h

theorem run_facts (I : Impl) (w : World) (id : InstId) (k : Cont) (h : Inv I w)
    (hph : (w.st id).phase = .run k) :
    (w.st id).typestate = k.toState ∧ effectsOk I.desc (tname id) (contAt k) k.rest = true ∧
      srcOk I id (w.st id) k ∧ notParked (w.st id).phase := by
  have hc := h.1.cont id
  have hp := h.1.prog id
  have ho := h.2.2.2.1 id
  unfold contTy at hc
  unfold programOk at hp
  unfold outcomeOk at ho
  rw [hph] at hc hp ho
  exact ⟨hc, hp, ho, by rw [hph]; trivial⟩

theorem after_rest (k : Cont) (e : Eff) (es : List Eff) (hk : k.rest = e :: es) :
    (afterHead k).rest = es := by
  simp [afterHead, hk]

theorem inv_note (I : Impl) (w : World) (s : InstId) (d : String) (id : InstId) (a : Actor)
    (h : Inv I (setActor w id a)) : Inv I (setActor (noteStale w s d) id a) :=
  inv_same I _ _ h ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    (fun i => by
      by_cases hi : i = id
      · rw [hi, setActor_self, setActor_self]
      · rw [setActor_other (noteStale w s d) id i a hi, setActor_other w id i a hi, noteStale_st])
    (fun i => by
      by_cases hi : i = id
      · rw [hi, setActor_self, setActor_self]
      · rw [setActor_other (noteStale w s d) id i a hi, setActor_other w id i a hi, noteStale_st])
    (by simp [setActor, noteStale])

theorem reply_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff) (h : Inv I w)
    (hph : (w.st id).phase = .run k) (hk : k.rest = .reply :: es) (ha : (w.st id).life = .alive)
    (hty : (w.st id).typestate = k.toState) (hprog : effectsOk I.desc (tname id) (contAt k) es = true)
    (hs : srcOk I id (w.st id) k) : Inv I (performReply w id k) := by
  have hfree : notParked (w.st id).phase := by rw [hph]; trivial
  have hk' : (afterHead k).rest = es := after_rest k _ es hk
  have hsrc : srcOk I id (w.st id) (afterHead k) := src_after I id (w.st id) k hs
  have hproc : ∀ w0 : World, Inv I w0 → w0.st id = w.st id →
      Inv I (setActor w0 id (proceed (w0.st id) (afterHead k))) := by
    intro w0 h0 hst
    rw [hst]
    exact inv_proceed I w0 id (w.st id) (afterHead k) h0 (by rw [hst]; exact ha)
      (by rw [hst]; exact hfree) ha (by rw [hst]) (by rw [hst]) (by rw [hst]) (by rw [hst])
      (by rw [hst]; exact hty) (by rw [hk']; exact hprog) hsrc (by rw [hst])
  unfold performReply
  dsimp only
  split
  · exact hproc w h rfl
  · next caller _ =>
    split
    · next dst ck hcph =>
      split
      · have hcid : caller ≠ id := by
          intro he
          rw [he, hph] at hcph
          cases hcph
        have hcalive := busy_alive I w h.1 caller (by rw [hcph]; intro he; cases he)
          (by rw [hcph]; intro he; cases he)
        have hp := h.1.prog caller
        have ho := h.2.2.2.1 caller
        unfold programOk at hp
        unfold outcomeOk at ho
        rw [hcph] at hp ho
        have h1 := inv_finish I w caller (w.st caller) ck .reply h hcalive (by rw [hcph]; trivial)
          hcalive rfl rfl rfl rfl ho.1 (by simpa [selectCall] using hp) rfl
        exact hproc _ h1 (setActor_other w caller id _ (Ne.symm hcid))
      · exact hproc w h rfl
    · exact hproc w h rfl

theorem cell_step_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (dst label : String) (c : Cell)
    (b : Bool) (h : Inv I w) (ha : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hty : (w.st id).typestate = k.toState)
    (hprog : effectsOk I.desc (tname id) (contAt k) k.rest = true) (hs : srcOk I id (w.st id) k) :
    Inv I (if b = true then setActor (setCell w dst label c) id (proceed ((setCell w dst label c).st id) k)
      else wakeReaders I.desc (setActor (setCell w dst label c) id
        (proceed ((setCell w dst label c).st id) k)) dst label id) := by
  have h1 : Inv I (setActor (setCell w dst label c) id (proceed ((setCell w dst label c).st id) k)) :=
    inv_proceed I (setCell w dst label c) id _ k
      (inv_same I w _ h (same_setCell w dst label c) (fun _ => by simp [setCell])
        (fun _ => by simp [setCell]) (by simp [setCell])) ha
      hfree ha rfl rfl rfl rfl hty hprog (src_ty I id k (by simp [setCell]) hs) rfl
  split
  · exact h1
  · have hw : (((setActor (setCell w dst label c) id
        (proceed ((setCell w dst label c).st id) k)).st id).life) = .alive := by
      rw [setActor_self, proceed_keeps_life]
      simp [setCell]
      exact ha
    exact wakeReaders_inv I I.desc _ dst label id h1 hw

/-- An id off the roster: never spawned, so its life is still `absent`. -/
theorem off_absent (I : Impl) (w : World) (id : InstId) (h : Inv I w) (hoff : id ∉ w.roster) :
    (w.st id).life = .absent :=
  Classical.byContradiction fun hne => hoff (h.2.2.1 id hne)

theorem mail_born (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hold : notParked (w.st id).phase) (habs : (w.st id).life = .absent)
    (hk : (w.st id).parked = []) (hnew : notParked a.phase) (hlist : a.parked = []) :
    MailInv (setActor w id a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    have hmb : mb ≠ id := by
      intro he
      rw [he, setActor_self, hlist] at hp
      cases hp
    rw [setActor_other w id mb a hmb] at hp
    have hs : p.sender ≠ id := by
      intro he
      rcases hM.fwd mb p hp with ⟨k, hph⟩ | hh
      · rw [he] at hph
        rw [hph] at hold
        exact hold
      · rw [he, habs] at hh
        cases hh
    rw [setActor_other w id p.sender a hs]
    exact hM.fwd mb p hp
  · intro s dst c k hph
    have hs : s ≠ id := by
      intro he
      rw [he, setActor_self] at hph
      rw [hph] at hnew
      exact hnew
    rw [setActor_other w id s a hs] at hph
    have hd : dst ≠ id := by
      intro he
      rcases hM.bwd s dst c k hph with ⟨p, hp, _, _⟩ | ⟨_, hdead⟩
      · rw [he, hk] at hp
        cases hp
      · rw [he, habs] at hdead
        cases hdead
    rw [setActor_other w id dst a hd]
    exact hM.bwd s dst c k hph
  · intro mb1 mb2 p1 p2 h1 h2 hs
    have hm1 : mb1 ≠ id := by
      intro he
      rw [he, setActor_self, hlist] at h1
      cases h1
    have hm2 : mb2 ≠ id := by
      intro he
      rw [he, setActor_self, hlist] at h2
      cases h2
    rw [setActor_other w id mb1 a hm1] at h1
    rw [setActor_other w id mb2 a hm2] at h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs
  · intro mb
    by_cases hmb : mb = id
    · rw [hmb, setActor_self, hlist]
      exact List.nodup_nil
    · rw [setActor_other w id mb a hmb]
      exact hM.once mb

theorem fresh_off (w : World) (template : String) (k : Nat) :
    InstId.peer template k (maxGen w template k) ∉ w.roster :=
  fun hm => Nat.lt_irrefl _ (maxGen_fresh w template k _ hm)

/-- A descent that succeeds with less fuel still succeeds when the walk is allowed
to run longer. -/
theorem descends_mono (w : World) (anc desc : InstId) (fuel fuel' : Nat)
    (hle : fuel ≤ fuel') (h : descends fuel w anc desc = true) :
    descends fuel' w anc desc = true := by
  induction fuel generalizing desc fuel' with
  | zero =>
    simp [descends] at h
  | succ fuel ih =>
    cases fuel' with
    | zero =>
      exact absurd hle (Nat.not_succ_le_zero _)
    | succ fuel' =>
      simp only [descends] at h ⊢
      by_cases htop : (desc == anc) = true
      · rw [ite_eq_left htop] at h
        cases h
      · rw [ite_eq_right htop] at h
        rw [ite_eq_right htop]
        cases hp : (w.st desc).parent with
        | none =>
          rw [hp] at h
          cases h
        | some p =>
          rw [hp] at h
          dsimp at h ⊢
          by_cases hanc : (p == anc) = true
          · rw [ite_eq_left hanc] at h
            rw [ite_eq_left hanc]
          · rw [ite_eq_right hanc] at h
            rw [ite_eq_right hanc]
            by_cases hloop : (p == desc) = true
            · rw [ite_eq_left hloop] at h
              cases h
            · rw [ite_eq_right hloop] at h
              rw [ite_eq_right hloop]
              exact ih p fuel' (Nat.le_of_succ_le_succ hle) h

/-- The parent walk from `desc` never reads `fresh` when nothing on the old map
points at it, so a birth that only retargets `fresh` leaves that walk alone. -/
theorem descends_avoid (fuel : Nat) {w w' : World} (fresh : InstId)
    (hpar : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (anc desc : InstId) (hd : desc ≠ fresh) :
    descends fuel w' anc desc = descends fuel w anc desc := by
  induction fuel generalizing desc with
  | zero => rfl
  | succ fuel ih =>
    simp only [descends]
    by_cases htop : (desc == anc) = true
    · rw [ite_eq_left htop, ite_eq_left htop]
    · rw [ite_eq_right htop, ite_eq_right htop]
      rw [hpar desc hd]
      cases hp : (w.st desc).parent with
      | none => rfl
      | some p =>
        dsimp
        by_cases hanc : (p == anc) = true
        · rw [ite_eq_left hanc, ite_eq_left hanc]
        · rw [ite_eq_right hanc, ite_eq_right hanc]
          by_cases hloop : (p == desc) = true
          · rw [ite_eq_left hloop, ite_eq_left hloop]
          · rw [ite_eq_right hloop, ite_eq_right hloop]
            exact ih p (by intro he; exact hno desc (by rw [hp, he]))

/-- One extra roster slot does not reveal a new descent among the ids that
were already present: a real chain already fits in the old length. -/
theorem descends_roster (w : World) (hF : ParentForest w) (anc desc : InstId)
    (h : descends (w.roster.length + 1) w anc desc = true) :
    descends w.roster.length w anc desc = true :=
  descends_of_strict w hF (strict_of_descends w (w.roster.length + 1) anc desc h)

/-- Sealing of two ids that are not the newborn agrees before and after the
birth. The new parent link leaves `fresh`, and the extra fuel is idle. -/
theorem sealed_born {w w' : World} (hF : ParentForest w) (fresh : InstId)
    (hro : w'.roster = w.roster ++ [fresh])
    (hpar : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (origin sender : InstId)
    (hs : sender ≠ fresh) :
    sealedTogether w' origin sender = sealedTogether w origin sender := by
  have hlen : w'.roster.length = w.roster.length + 1 := by
    rw [hro, List.length_append]
    simp
  have hdesc : descends w'.roster.length w' origin sender =
      descends w.roster.length w origin sender := by
    rw [hlen, descends_avoid (w.roster.length + 1) fresh hpar hno origin sender hs]
    cases hlong : descends (w.roster.length + 1) w origin sender with
    | false =>
      cases hshort : descends w.roster.length w origin sender with
      | false => rfl
      | true =>
        have hmono := descends_mono w origin sender w.roster.length (w.roster.length + 1)
          (Nat.le_succ _) hshort
        rw [hlong] at hmono
        cases hmono
    | true =>
      exact (descends_roster w hF origin sender hlong).symm
  simp only [sealedTogether]
  rw [hdesc]

/-- Program mail of an id that is not the newborn is unchanged by the birth.
The newborn's mailbox is empty, and no queued message names it as sender. -/
theorem flight_born {w w' : World} (hF : ParentForest w) (fresh : InstId)
    (hoff : fresh ∉ w.roster) (hro : w'.roster = w.roster ++ [fresh])
    (hl : ∀ i, i ≠ fresh → (w'.st i).life = (w.st i).life)
    (hpar : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hbox : ∀ i, i ≠ fresh → (w'.st i).box = (w.st i).box)
    (hprio : ∀ i, i ≠ fresh → (w'.st i).prio = (w.st i).prio)
    (hbox0 : (w'.st fresh).box = []) (hprio0 : (w'.st fresh).prio = [])
    (hno : ∀ i, (w.st i).parent ≠ some fresh)
    (hsender : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ≠ fresh)
    (id : InstId) (_hid : id ≠ fresh) : mailInFlight w' id = mailInFlight w id := by
  cases hnew : mailInFlight w' id with
  | false =>
    cases hold : mailInFlight w id with
    | false => rfl
    | true =>
      obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w id hold
      have hhost' : host ≠ fresh := by
        intro he
        exact hoff (he ▸ hhost)
      have hsend : m.sender ≠ fresh := hsender host m hm
      have hseal := sealed_born hF fresh hro hpar hno id m.sender hsend
      rw [← hseal] at hs
      have hhostR : host ∈ w'.roster := by rw [hro]; exact List.mem_append_left _ hhost
      have hlive' : (w'.st host).life = .alive := by rw [hl host hhost']; exact hlive
      have hm' : m ∈ (w'.st host).box ∨ m ∈ (w'.st host).prio := by
        rcases hm with hm | hm
        · exact Or.inl (by rw [hbox host hhost']; exact hm)
        · exact Or.inr (by rw [hprio host hhost']; exact hm)
      have hhit := flight_of_msg w' id host m hhostR hlive' ht hs hm'
      rw [hnew] at hhit
      cases hhit
  | true =>
    obtain ⟨host, m, hhost, hlive, ht, hs, hm⟩ := flight_witness w' id hnew
    have hmem : host ∈ w.roster ∨ host = fresh := by
      rw [hro] at hhost
      simpa [List.mem_append, List.mem_singleton] using hhost
    rcases hmem with hmem | hmem
    · have hhost' : host ≠ fresh := by
        intro he
        exact hoff (he ▸ hmem)
      have hm0 : m ∈ (w.st host).box ∨ m ∈ (w.st host).prio := by
        rcases hm with hm | hm
        · exact Or.inl (by rw [← hbox host hhost']; exact hm)
        · exact Or.inr (by rw [← hprio host hhost']; exact hm)
      have hsend : m.sender ≠ fresh := hsender host m hm0
      have hseal := sealed_born hF fresh hro hpar hno id m.sender hsend
      rw [hseal] at hs
      have hlive0 : (w.st host).life = .alive := by rw [← hl host hhost']; exact hlive
      have hhit := flight_of_msg w id host m hmem hlive0 ht hs hm0
      exact hhit.symm
    · rcases hm with hm | hm
      · rw [hmem, hbox0] at hm
        cases hm
      · rw [hmem, hprio0] at hm
        cases hm

/-- Installing one fresh idle peer. -/
theorem place_inv (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnext : ∀ v : World, (next v).st = v.st ∧ (next v).roster = v.roster)
    (hcr : ∀ v : World, (next v).crashed = v.crashed)
    (hparLive : ∀ p, parent = some p → (w.st p).life = .alive)
    (hhost : ∀ p, parent = some p → p ∈ w.roster) (h : Inv I w) :
    Inv I (placePeer I w template k initial parent next) := by
  have hS := place_sem I w template k initial parent next hnext h.1
  have hoff := fresh_off w template k
  unfold placePeer at hS ⊢
  dsimp only at hS ⊢
  generalize InstId.peer template k (maxGen w template k) = nid at hS hoff ⊢
  generalize hborn : ({ bornActor I.desc w template k initial with parent := parent } : Actor) = born
    at hS ⊢
  have hph : born.phase = .idle := by rw [← hborn]; simp [bornActor, withKeyTokens]
  have hpk : born.parked = [] := by rw [← hborn]; simp [bornActor, withKeyTokens]
  generalize hW : next { w with roster := w.roster ++ [nid] } = W1 at hS ⊢
  have hst : W1.st = w.st := by rw [← hW]; exact (hnext _).1
  have hro : W1.roster = w.roster ++ [nid] := by rw [← hW]; exact (hnext _).2
  have habs := off_absent I w nid h hoff
  have hk0 : (w.st nid).parked = [] := h.1.offEmpty nid hoff
  have hfree : notParked (w.st nid).phase := by
    rcases h.1.idleOff nid (by rw [habs]; intro he; cases he) with hp | hp <;> rw [hp] <;> trivial
  have hM1 : MailInv W1 := mail_copy w W1 h.2.1 (fun i => by rw [hst])
  have hM2 : MailInv (setActor W1 nid born) :=
    mail_born W1 nid born hM1 (by rw [hst]; exact hfree) (by rw [hst]; exact habs)
      (by rw [hst]; exact hk0) (by rw [hph]; trivial) hpk
  refine ⟨hS, mail_copy _ _ hM2 (fun i => cellsSt _ _ _ i), ?_, ?_, ?_, ?_⟩
  · intro i hl
    rw [cellsSt] at hl
    rw [cellsRoster]
    show i ∈ W1.roster
    rw [hro]
    by_cases hi : i = nid
    · rw [hi]
      exact List.mem_append_right _ (List.Mem.head _)
    · rw [setActor_other W1 nid i born hi, hst] at hl
      exact List.mem_append_left _ (h.2.2.1 i hl)
  · intro i
    rw [cellsSt]
    by_cases hi : i = nid
    · rw [hi, setActor_self]
      unfold outcomeOk
      rw [hph]
      trivial
    · rw [setActor_other W1 nid i born hi, hst]
      exact h.2.2.2.1 i
  · have hbornPar : born.parent = parent := by rw [← hborn]
    have hold : (w.st nid).parent = none := h.forest.off nid hoff
    have hfreeId : ∀ i, (w.st i).parent ≠ some nid := by
      intro i hp
      exact hoff (h.forest.hosted i nid hp)
    have hne : ∀ p, born.parent = some p → p ≠ nid := by
      intro p hp
      have hm := hhost p (by rw [← hbornPar]; exact hp)
      intro heq
      exact hoff (heq ▸ hm)
    have hW1 : ParentForest W1 :=
      ParentForest.parents (ParentForest.grow h.forest nid) (fun i => by rw [hst]) hro
    have hlink : ParentAcyclic (setActor W1 nid born) :=
      parentAcyclic_link W1 nid born hW1.wf (by rw [hst]; exact hold)
        (fun i hp => hfreeId i (by rw [hst] at hp; exact hp)) hne
    have hset : ParentForest (setActor W1 nid born) := by
      refine ⟨hlink, ?_, ?_⟩
      · intro i hi
        simp only [setActor] at hi
        have holdi : i ∉ w.roster := fun hm => hi (by rw [hro]; exact List.mem_append_left _ hm)
        by_cases hii : i = nid
        · exact absurd (by rw [hii, hro]; exact List.mem_append_right _ (List.mem_cons_self : nid ∈ [nid])) hi
        · rw [setActor_other W1 nid i born hii, hst]
          exact h.forest.off i holdi
      · intro i p hp
        by_cases hii : i = nid
        · rw [hii, setActor_self, hbornPar] at hp
          simp only [setActor]
          rw [hro]
          exact List.mem_append_left _ (hhost p hp)
        · rw [setActor_other W1 nid i born hii, hst] at hp
          simp only [setActor]
          rw [hro]
          exact List.mem_append_left _ (h.forest.hosted i p hp)
    exact ParentForest.parents hset (fun i => readCells_parent _ _ _ i) (cellsRoster _ _ _)
  · generalize hR : readCells I.desc (setActor W1 nid born) nid = wR
    have hstR : ∀ i, (wR.st i) = (setActor W1 nid born).st i := by
      intro i
      rw [← hR]
      exact cellsSt _ _ _ i
    have hroR : wR.roster = w.roster ++ [nid] := by
      rw [← hR, cellsRoster]
      simp only [setActor]
      exact hro
    have hcrash : wR.crashed = w.crashed := by
      rw [← hR, readCells_crashed]
      simp only [setActor]
      rw [← hW, hcr _]
    have hlR : ∀ i, i ≠ nid → (wR.st i).life = (w.st i).life := by
      intro i hi
      rw [hstR, setActor_other W1 nid i born hi, hst]
    have hparR : ∀ i, i ≠ nid → (wR.st i).parent = (w.st i).parent := by
      intro i hi
      rw [hstR, setActor_other W1 nid i born hi, hst]
    have hboxR : ∀ i, i ≠ nid → (wR.st i).box = (w.st i).box := by
      intro i hi
      rw [hstR, setActor_other W1 nid i born hi, hst]
    have hprioR : ∀ i, i ≠ nid → (wR.st i).prio = (w.st i).prio := by
      intro i hi
      rw [hstR, setActor_other W1 nid i born hi, hst]
    have hpkR : ∀ i, i ≠ nid → (wR.st i).parked = (w.st i).parked := by
      intro i hi
      rw [hstR, setActor_other W1 nid i born hi, hst]
    have hbox0 : (wR.st nid).box = [] := by
      rw [hstR, setActor_self, ← hborn]
      simp [bornActor, withKeyTokens]
    have hprio0 : (wR.st nid).prio = [] := by
      rw [hstR, setActor_self, ← hborn]
      simp [bornActor, withKeyTokens]
    have hliveN : (wR.st nid).life = .alive := by
      rw [hstR, setActor_self, ← hborn]
      simp [bornActor, withKeyTokens]
    have hfreeId : ∀ i, (w.st i).parent ≠ some nid := by
      intro i hp
      exact hoff (h.forest.hosted i nid hp)
    have hsender : ∀ host m, (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ≠ nid := by
      intro host m hm he
      exact hoff (he ▸ h.seal.hostedMail host m hm)
    have hflight : ∀ i, i ≠ nid → mailInFlight wR i = mailInFlight w i := by
      intro i hi
      exact flight_born h.forest nid hoff hroR hlR hparR hboxR hprioR hbox0 hprio0 hfreeId hsender i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro host p ha hp
      by_cases hh : host = nid
      · rw [hh, hstR, setActor_self, hpk] at hp
        cases hp
      · rw [hstR, setActor_other W1 nid host born hh, hst] at ha hp
        by_cases hs : p.sender = nid
        · rw [hs, hstR, setActor_self, ← hborn]
          simp [bornActor, withKeyTokens]
        · rw [hstR, setActor_other W1 nid p.sender born hs, hst]
          exact h.seal.liveParked host p ha hp
    · rcases h.seal.quiet with hcr0 | hq
      · exact Or.inl (hcrash.trans hcr0)
      · refine Or.inr ?_
        intro i hna
        have hi : i ≠ nid := by
          intro he
          rw [he, hliveN] at hna
          exact hna rfl
        rw [hboxR i hi, hpkR i hi]
        exact hq i (by
          intro ha
          exact hna (by rw [hlR i hi]; exact ha))
    · rcases h.seal.childless with hcr0 | hk
      · exact Or.inl (hcrash.trans hcr0)
      · refine Or.inr ?_
        intro id c hdead hparC
        by_cases hc : c = nid
        · rw [hc, hstR, setActor_self, ← hborn] at hparC
          simp at hparC
          have hid : id ≠ nid := by
            intro he
            exact hoff (he ▸ hhost id hparC)
          exact absurd (hparLive id hparC) (by
            intro ha
            exact hdead (by rw [hlR id hid]; exact ha))
        · by_cases hid : id = nid
          · rw [hid, hparR c hc] at hparC
            exact absurd hparC (hfreeId c)
          · rw [hlR c hc]
            exact hk id c (by
              intro ha
              exact hdead (by rw [hlR id hid]; exact ha)) (by rw [← hparR c hc]; exact hparC)
    · intro id hc hd hf
      have hid : id ≠ nid := by
        intro he
        rw [he, hliveN] at hd
        cases hd
      rw [hcrash] at hc
      have hd0 : (w.st id).life = .dead := by rw [← hlR id hid]; exact hd
      have hf0 : mailInFlight w id = true := by rw [← hflight id hid]; exact hf
      have hstep := h.seal.chain id hc hd0 hf0
      cases hp : (wR.st id).parent with
      | none =>
        have hnone : (w.st id).parent = none := by rw [← hparR id hid, hp]
        simp [hnone] at hstep
        trivial
      | some p =>
        have hsome : (w.st id).parent = some p := by rw [← hparR id hid, hp]
        simp [hsome] at hstep
        have hpne : p ≠ nid := by
          intro he
          exact hfreeId id (by rw [hsome, he])
        rcases hstep with ⟨ha, htomb⟩ | ⟨hdeadP, hfp⟩
        · rcases htomb with ⟨m, hm, htom, hs⟩
          refine Or.inl ⟨by rw [hlR p hpne]; exact ha, ⟨m, by rw [hprioR p hpne]; exact hm, htom, hs⟩⟩
        · refine Or.inr ⟨?_, by rw [hflight p hpne]; exact hfp⟩
          intro ha
          exact hdeadP (by rw [← hlR p hpne]; exact ha)
    · intro host p hp
      by_cases hh : host = nid
      · rw [hh, hstR, setActor_self, hpk] at hp
        cases hp
      · rw [hstR, setActor_other W1 nid host born hh, hst] at hp
        exact h.seal.parkedFrom host p hp
    · intro host m hm
      by_cases hh : host = nid
      · rw [hh, hstR, setActor_self, ← hborn] at hm
        simp [bornActor, withKeyTokens] at hm
      · rw [hstR, setActor_other W1 nid host born hh, hst] at hm
        rw [hroR]
        exact List.mem_append_left _ (h.seal.hostedMail host m hm)

theorem spawn_inv (I : Impl) (w w' : World) (template : String) (h : Inv I w)
    (hs : spawn I w template = some w') : Inv I w' := by
  unfold spawn at hs
  split at hs
  · cases hs
  · next t _ =>
    split at hs
    · next hmay =>
      split at hs
      · next name hsup =>
        cases hs
        have hlive : (w.st (.core name)).life = .alive := by
          unfold maySpawnRoot at hmay
          simp only [Bool.and_eq_true] at hmay
          have hsupLive : supervisorLive I.desc w t = true := hmay.1.2
          unfold supervisorLive at hsupLive
          rw [hsup] at hsupLive
          split at hsupLive
          · next heq => cases heq
          · next _ heq =>
            cases heq
            split at hsupLive
            · simp at hsupLive
            · next sup _ =>
              cases hm : sup.multiplicity with
              | one => simpa [hm, beq_iff_eq] using hsupLive
              | perPeer => simp [hm] at hsupLive
        exact place_inv I w _ _ _ (some (.core name)) _ (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
          (fun p hp => by cases hp; exact hlive)
          (fun p hp => by cases hp; exact h.1.rostered _ hlive) h
      · split at hs
        · cases hs
          exact place_inv I w _ _ _ none _ (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
            (fun _ hp => by cases hp) (fun _ hp => by cases hp) h
        · cases hs
          exact place_inv I w _ _ _ none _ (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
            (fun _ hp => by cases hp) (fun _ hp => by cases hp) h
    · cases hs

theorem admit_inv (I : Impl) (w : World) (child : String) (k : Nat) (initial : String)
    (parent : Option InstId) (hhost : ∀ p, parent = some p → p ∈ w.roster)
    (hparLive : ∀ p, parent = some p → (w.st p).life = .alive) (h : Inv I w) :
    Inv I (admitBorn I w (InstId.peer child k (maxGen w child k))
      { bornActor I.desc w child k initial with parent := parent }) :=
  place_inv I w child k initial parent (fun v => v) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl)
    hparLive hhost h

theorem spawnChild_inv (I : Impl) (w w' : World) (parent : InstId) (child : String) (h : Inv I w)
    (hs : spawnChild I w parent child = some w') : Inv I w' := by
  unfold spawnChild at hs
  split at hs
  · cases hs
  · next t _ =>
    split at hs
    · next hgo =>
      have halive : (w.st parent).life = .alive := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hgo
        exact hgo.2
      have hhost : ∀ p, some parent = some p → p ∈ w.roster := by
        intro p hp
        cases hp
        exact h.1.rostered parent halive
      split at hs
      · cases hs
      · split at hs
        · cases hs
          exact h
        · cases hs
          exact admit_inv I w child _ t.initial _ hhost
            (fun p hp => by cases hp; exact halive) h
    · split at hs
      · cases hs
        exact h
      · cases hs

theorem exec_run_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (h : Inv I w)
    (hph : (w.st id).phase = .run k) : Inv I (execRun I w id (w.st id) k) := by
  by_cases ha : (w.st id).life = .alive
  case neg =>
    have hno : ((w.st id).life == .alive) = false := by simpa [beq_iff_eq] using ha
    simp only [execRun, hno, Bool.false_eq_true, ↓reduceIte]
    exact h
  have hgo : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using ha
  obtain ⟨hty, hprog, hsrc0, hfree⟩ := run_facts I w id k h hph
  have hsrc : srcOk I id (w.st id) (afterHead k) := src_after I id (w.st id) k hsrc0
  cases hk : k.rest with
  | nil =>
    simp only [execRun, hgo, hk, ite_true]
    exact inv_set_free I w id _ h ha hfree (by exact ha) (by exact hty.symm) (by trivial) (by rfl)
      (by rfl) (by rfl) (by trivial) (by trivial) (by trivial) (by trivial) rfl
  | cons e es =>
    have hk' : (afterHead k).rest = es := after_rest k e es hk
    have hpe : effectsOk I.desc (tname id) (contAt k) (e :: es) = true := by rw [← hk]; exact hprog
    have htail : effectsOk I.desc (tname id) (contAt (afterHead k)) (afterHead k).rest = true := by
      rw [hk']
      exact head_rest _ _ _ _ _ hpe
    cases e with
    | send d l n =>
      have hs := head_send I.desc (tname id) d l (contAt k) n es hpe
      cases hr : route w I.desc id d with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact inv_note I w id d id _
          (inv_proceed I w id (w.st id) (afterHead k) h ha hfree ha rfl rfl rfl rfl hty htail hsrc rfl)
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact enqueue_inv I w id dstId _ false (afterHead k) h
          (enqueue_sem I w id dstId _ false (afterHead k) h.1 hty htail
            ⟨l, by rw [route_tname w I.desc id d dstId hr, hty]; exact hs.1⟩ ha
            (fun hc => absurd hc Bool.false_ne_true) (fun hc => absurd hc Bool.false_ne_true))
          hfree ha hsrc (fun hc => absurd hc Bool.false_ne_true) rfl
    | trySend d l n f g =>
      have hs := head_try I.desc (tname id) d l (contAt k) n f g es hpe
      have hgone : Inv I (setActor w id (proceed (w.st id) { afterHead k with
          rest := g, toState := pickState (afterHead k).toState (afterHead k).toGone })) :=
        inv_pick I w id (w.st id) (afterHead k) g (afterHead k).toGone h ha hfree ha rfl rfl rfl rfl hsrc
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by rw [contAt_pick]; exact hs.2.1) rfl
      have hfull : Inv I (setActor w id (proceed (w.st id) { afterHead k with
          rest := f, toState := pickState (afterHead k).toState (afterHead k).toFull })) :=
        inv_pick I w id (w.st id) (afterHead k) f (afterHead k).toFull h ha hfree ha rfl rfl rfl rfl hsrc
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by rw [contAt_pick]; exact hs.1) rfl
      cases hr : route w I.desc id d with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact inv_note I w id d id _ hgone
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        split
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          exact enqueue_inv I w id dstId _ false (afterHead k) h
            (try_room_sem I w id dstId _ (afterHead k) h.1 hty htail hc.1.1 hc.1.2 hc.2 ha)
            hfree ha hsrc (fun hc => absurd hc Bool.false_ne_true) rfl
        · split
          · exact hfull
          · exact hgone
    | call d l n na to =>
      have hs := head_call I.desc (tname id) d l (contAt k) n na to es hpe
      have hwait := src_lists I id (w.st id) (afterHead k) na to (afterHead k).onTimeout hsrc
      cases hr : resolveId I.desc w id d with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact inv_note I w id d id _
          (inv_finish I w id (issueCall (w.st id)) { afterHead k with onNotAdmitted := na, onTimedOut := to }
            .notAdmitted h ha hfree ha rfl rfl (by simp [issueCall]) (by simp [issueCall])
            (src_ty I id _ (by simp [issueCall]) hwait)
            (by rw [contAt_select_na]; exact hs.2.1) (issueCall_parent _))
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact enqueue_inv I w id dstId _ true { afterHead k with onNotAdmitted := na, onTimedOut := to } h
          (enqueue_sem_src I w id dstId _ true { afterHead k with onNotAdmitted := na, onTimedOut := to }
            h.1 hwait htail ⟨l, by rw [resolve_tname I.desc w id d dstId hr, hty]; exact hs.1⟩ ha
            (fun _ _ => hs.2.1))
          hfree ha hwait (fun _ => ⟨hs.2.1, hs.2.2.1⟩) rfl
    | reply =>
      simp only [execRun, hgo, hk, ite_true]
      exact reply_inv I w id k es h hph hk ha hty (head_rest _ _ _ _ _ hpe) hsrc0
    | selfSchedule label =>
      simp only [execRun, hgo, hk, ite_true]
      split
      · exact inv_proceed I w id (w.st id) (afterHead k) h ha hfree ha rfl rfl rfl rfl hty htail hsrc rfl
      · next hnew =>
        split
        · let msg : Msg :=
            { label := label, sender := id, callFrom := none, reliable := true, mid := (w.st id).nextMid }
          have happ : upsertPrio (w.st id).prio msg = (w.st id).prio ++ [msg] := by
            unfold upsertPrio
            rw [ite_eq_right hnew]
          let grown := setActor w id (withPrio (w.st id) msg)
          have h1 : Inv I grown :=
            inv_frame I w grown h (same_actor w id (withPrio (w.st id) msg) rfl rfl rfl rfl rfl)
              (seal_grow_prio w h.seal h.forest id msg (Or.inr ha)
                (h.2.2.1 id (by rw [ha]; intro hna; cases hna)))
          rw [happ]
          have hover (b : Actor) :
              setActor (setActor w id (withPrio (w.st id) msg)) id b = setActor w id b := by
            simp only [setActor]
            congr
            funext j
            by_cases hj : j = id <;> simp [hj]
          change Inv I (setActor w id (proceed (withPrio (w.st id) msg) (afterHead k)))
          rw [← hover (proceed (withPrio (w.st id) msg) (afterHead k))]
          have hst : grown.st id = withPrio (w.st id) msg := by simp [grown, setActor]
          rw [← hst]
          have hback : setActor w id (grown.st id) = grown := by simp [grown, setActor, hst]
          rw [hback]
          exact inv_proceed I grown id (grown.st id) (afterHead k) h1
            (by simp [grown, setActor, withPrio, ha])
            (by simp [grown, setActor, withPrio]; exact hfree)
            (by simp [grown, setActor, withPrio, ha])
            (by simp [grown, setActor, withPrio])
            (by simp [grown, setActor, withPrio])
            rfl rfl (by simp [grown, setActor, withPrio, afterHead]; exact hty) htail
            (src_ty I id (afterHead k) (by simp [grown, setActor, withPrio]) hsrc)
            (by simp [grown, setActor, withPrio])
        · exact crash_inv I w h
    | cell dst label value =>
      simp only [execRun, hgo, hk, ite_true]
      exact cell_step_inv I w id (afterHead k) dst label _ _ h ha hfree hty htail hsrc
    | internal =>
      simp only [execRun, hgo, hk, ite_true]
      exact inv_set_free I w id _ h ha hfree (by exact ha) (by rfl) (by trivial) (by rfl)
        (by rfl) (by rfl) (by exact hty) (by exact htail) (by trivial)
        (by exact src_ty I id (afterHead k) rfl hsrc) rfl
    | peer o =>
      have hs := head_peer I.desc (tname id) (contAt k) o es hpe
      simp only [execRun, hgo, hk, ite_true]
      exact inv_set_free I w id _ h ha hfree (by exact ha) (by rfl) (by trivial) (by rfl)
        (by rfl) (by rfl) (by exact hty) (by exact htail) (by trivial)
        (by exact ⟨src_ty I id _ rfl
          (src_lists I id (w.st id) (afterHead k) (afterHead k).onNotAdmitted (afterHead k).onTimedOut o hsrc),
          hs.1⟩) rfl
    | abort =>
      simp only [execRun, hgo, hk, ite_true, commitCont]
      have hw' := abortChildren_inv I I.desc w id h
      by_cases hcr : (abortChildren I.desc w id).crashed = true
      · rw [ite_eq_left hcr]
        exact hw'
      · rw [ite_eq_right hcr]
        have hcf : (abortChildren I.desc w id).crashed = false := by
          cases hb : (abortChildren I.desc w id).crashed with
          | false => rfl
          | true => exact absurd hb hcr
        have hlive : ((abortChildren I.desc w id).st id).life = .alive :=
          abort_parent_alive I.desc w id h.forest.wf ha hcf
        have hph' := abortChildren_preserves_run I.desc w id id k hph hlive
        have hc := hw'.1.cont id
        unfold contTy at hc
        rw [hph'] at hc
        have hty' : ((abortChildren I.desc w id).st id).typestate = (w.st id).typestate :=
          hc.trans hty.symm
        have hsrc' : srcOk I id ((abortChildren I.desc w id).st id) (afterHead k) :=
          src_ty I id (afterHead k) hty' hsrc
        exact inv_proceed I (abortChildren I.desc w id) id
          ((abortChildren I.desc w id).st id) (afterHead k) hw' hlive
          (by rw [hph']; trivial) hlive rfl rfl rfl rfl (by simpa [afterHead] using hc) htail hsrc' rfl
    | terminate =>
      have hstep := exec_term_step I w id (w.st id) k ha ⟨es, hk⟩
      generalize execRun I w id (w.st id) k = wR at hstep ⊢
      cases hstep with
      | fall => exact crash_inv I w h
      | crash _ _ _ => exact crash_inv I w h
      | lone _ _ _ _ _ _ hch =>
        exact shutdownActor_inv I I.desc w id h (by
          intro c hne hp ha
          have hmem : c ∈ w.roster :=
            h.2.2.1 c (by rw [ha]; intro hna; cases hna)
          have hbit : ((w.st c).life == .alive) = true := by simpa [beq_iff_eq] using ha
          have hchild : hasChild I.desc w id = true := by
            unfold hasChild
            apply _root_.List.any_eq_true.mpr
            refine ⟨c, hmem, ?_⟩
            simp [isChild, hp, hne, hbit]
          simp [hch] at hchild)
      | tree _ _ _ _ => exact terminateStage_inv I I.desc w id _ h
      | cascade _ _ _ _ _ _ _ => exact terminateStage_inv I I.desc w id _ h
    | spawn child =>
      cases hsp : spawnChild I w id child with
      | none =>
        simp only [execRun, hgo, hk, hsp, ite_true]
        exact crash_inv I w h
      | some w' =>
        simp only [execRun, hgo, hk, hsp, ite_true, commitCont]
        have hw' := spawnChild_inv I w w' id child h hsp
        by_cases hcr : w'.crashed = true
        · rw [ite_eq_left hcr]
          exact hw'
        · rw [ite_eq_right hcr]
          have hst := spawnChild_other_st I w w' id child id hsp (h.1.rostered id ha)
          exact inv_proceed I w' id (w'.st id) (afterHead k) hw' (by rw [hst]; exact ha)
            (by rw [hst]; exact hfree) (by rw [hst]; exact ha) rfl rfl rfl rfl
            (by rw [hst]; exact hty) htail
            (src_ty I id (afterHead k) (by rw [hst]) hsrc) rfl

theorem exec_head_inv (I : Impl) (w w' : World) (id : InstId) (h : Inv I w)
    (hs : execHead I w id = some w') : Inv I w' := by
  unfold execHead at hs
  dsimp only at hs
  split at hs
  · cases hs
  · split at hs
    · next k hph =>
      cases hs
      exact exec_run_inv I w id k h hph
    · cases hs

theorem finish_inv (I : Impl) (w w' : World) (id : InstId) (h : Inv I w)
    (hs : finishWait I w id = some w') : Inv I w' := by
  unfold finishWait at hs
  split at hs
  · cases hs
  · next hal =>
    have ha : (w.st id).life = .alive := Classical.byContradiction hal
    have hc := h.1.cont id
    have hp := h.1.prog id
    have ho := h.2.2.2.1 id
    unfold contTy at hc
    unfold programOk at hp
    unfold outcomeOk at ho
    split at hs
    · next k hph =>
      cases hs
      rw [hph] at hc hp ho
      exact inv_proceed I w id (w.st id) k h ha (by rw [hph]; trivial) ha rfl rfl rfl rfl hc hp ho rfl
    · next k hph =>
      cases hs
      rw [hph] at hc hp ho
      exact inv_proceed I w id (w.st id) k h ha (by rw [hph]; trivial) ha rfl rfl rfl rfl hc hp ho.1 rfl
    · cases hs

theorem findDeliver_mem (I : Impl) (template state : String) (m : Msg) (tr : Transition)
    (h : findDeliver I template state m = some tr) :
    tr ∈ I.transitions ∧ tr.template = template ∧ tr.fromState = state := by
  unfold findDeliver at h
  cases htr : findTr I template state m.label with
  | some tr' =>
    simp only [htr, Option.some.injEq] at h
    subst h
    have hm := findTr_mem I template state m.label tr' htr
    exact ⟨hm.1, hm.2.1, hm.2.2.1⟩
  | none =>
    simp only [htr] at h
    split at h
    · have hm := findTr_mem I template state m.baseLabel tr h
      exact ⟨hm.1, hm.2.1, hm.2.2.1⟩
    · cases h

theorem effects_of_transition (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    effectsOk I.desc tr.template (branchAt tr) tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some _ =>
    simp only [transitionOk, ht, Bool.and_eq_true] at hok
    exact hok.1.1.1.1.1.2

theorem stateNamed_mem (t : Template) (s : String) (h : stateNamed t s = true) (hne : s ≠ "") :
    t.states.elem s = true := by
  unfold stateNamed at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hne
  · exact h

/-- A landing state of a checked transition is a declared state of its template. -/
theorem lands_named (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (s : String) (hs : landsAt tr s) : (statesOf I.desc tr.template).elem s = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some t =>
    simp only [transitionOk, ht, Bool.and_eq_true] at hok
    rw [statesOf, ht]
    rcases hs with rfl | ⟨hne, hfield⟩
    · exact hok.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · rcases hfield with h | h | h | h | h
      · exact stateNamed_mem t s (by rw [h]; exact hok.1.1.1.1.1.1.1.1.1.1.1.2) hne
      · exact stateNamed_mem t s (by rw [h]; exact hok.1.1.1.1.1.1.1.1.1.1.2) hne
      · exact stateNamed_mem t s (by rw [h]; exact hok.1.1.1.1.1.1.1.1.1.2) hne
      · exact stateNamed_mem t s (by rw [h]; exact hok.1.1.1.1.1.1.1.1.2) hne
      · exact stateNamed_mem t s (by rw [h]; exact hok.1.1.1.1.1.1.1.2) hne

/-- What a delivery leaves: the world only reads cells, and the receiver is installed
in a checked, unparked phase with the same life and parked list. -/
structure DeliverOk (I : Impl) (w : World) (id : InstId) (a a' : Actor) (w' : World) : Prop where
  sem : SemInv I (setActor w' id a')
  life : a'.life = a.life
  parked : a'.parked = a.parked
  free : notParked a'.phase
  st : ∀ i, w'.st i = w.st i
  roster : w'.roster = w.roster
  out : outcomeOk I id a'
  parent : a'.parent = a.parent
  box : a'.box = a.box
  prio : a'.prio = a.prio
  crashed : w'.crashed = w.crashed

theorem deliver_ok (I : Impl) (hL : LocalOk I) (w : World) (id : InstId)
    (a : Actor) (m : Msg) (w' : World) (a' : Actor) (hS : SemInv I w)
    (hlife : a.life = (w.st id).life) (hty : a.typestate = (w.st id).typestate)
    (h : deliver I w id a m = some (w', a')) : DeliverOk I w id a a' w' := by
  have hS1 := cells_sem I w id hS
  have hst : ∀ i, (readCells I.desc w id).st i = w.st i := fun i => readCells_st I.desc w id i
  have hro : (readCells I.desc w id).roster = w.roster := cellsRoster I.desc w id
  unfold deliver at h
  dsimp only at h
  split at h
  · cases h
  · next hal =>
    have halive : a.life = .alive := Classical.byContradiction hal
    have hmem : id ∈ w.roster := hS.rostered id (hlife.symm.trans halive)
    have hmem1 : id ∈ (readCells I.desc w id).roster := by rw [hro]; exact hmem
    have hidle : ∀ b : Actor, b.phase = .idle → b.life = a.life → b.typestate = a.typestate →
        b.parked = a.parked → b.parent = a.parent → b.box = a.box → b.prio = a.prio →
        DeliverOk I w id a b (readCells I.desc w id) := by
      intro b hp hl ht hk hpar hbox hprio
      refine ⟨?_, hl, hk, by rw [hp]; trivial, hst, hro, by unfold outcomeOk; rw [hp]; trivial, hpar,
        hbox, hprio, readCells_crashed I.desc w id⟩
      apply sem_set I _ id b hS1
      · rw [hst, ht, hty]
      · rw [hst, hl, hlife]
      · unfold contTy; rw [hp]; trivial
      · unfold programOk; rw [hp]; trivial
      · unfold waitEdge; rw [hp]; trivial
      · exact idleOff_now b hp
      · exact Or.inr hmem1
    split at h
    · cases h
      exact hidle _ rfl rfl rfl rfl rfl rfl rfl
    · split at h
      · split at h
        · cases h
        · cases h
          exact hidle _ rfl rfl rfl rfl rfl rfl rfl
      · next tr htr =>
        split at h
        · cases h
        · cases h
          have hfm := findDeliver_mem I (tname id) a.typestate m tr htr
          have heff := effects_of_transition I hL tr hfm.1
          rw [hfm.2.1] at heff
          have hfrom : ∀ i, i = id → ((readCells I.desc w id).st i).typestate = tr.fromState := by
            intro i hi
            rw [hst, hi, hfm.2.2, hty]
          split
          · refine ⟨?_, rfl, rfl, trivial, hst, hro, trivial, rfl, rfl, rfl, readCells_crashed I.desc w id⟩
            cases id with
            | core r =>
              exact sem_move I _ r _ tr hS1 hL (hfrom _ rfl) rfl (by rw [hst]; exact hlife) hfm.2.1
                hfm.1 trivial trivial trivial (idleOff_now _ rfl) (Or.inr hmem1)
            | peer n k g =>
              exact sem_noncore I _ _ _ hS1 (fun r => peer_ne_core n k g r) trivial trivial trivial
                (idleOff_now _ rfl) hmem1
          · refine ⟨?_, rfl, rfl, trivial, hst, hro, ?_, rfl, rfl, rfl, readCells_crashed I.desc w id⟩
            · cases id with
              | core r =>
                exact sem_move I _ r _ tr hS1 hL (hfrom _ rfl) rfl (by rw [hst]; exact hlife) hfm.2.1
                  hfm.1 rfl heff trivial (idleOff_life halive) (Or.inr hmem1)
              | peer n k g =>
                exact sem_noncore I _ _ _ hS1 (fun r => peer_ne_core n k g r) rfl heff trivial
                  (idleOff_life halive) hmem1
            · unfold outcomeOk
              refine ⟨tr, hfm.1, hfm.2.1, Or.inl rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The receiver installed after a delivery that took a message from its bulk or priority queue. -/
theorem inv_deliver (I : Impl) (w w1 : World) (id : InstId) (a a1 : Actor) (h : Inv I w)
    (hd : DeliverOk I w id a a1 w1) (hidle : (w.st id).phase = .idle)
    (halive : (w.st id).life = .alive) (hlife : a.life = (w.st id).life)
    (hpk : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent)
    (hbox : ∀ m, m ∈ a.box → m ∈ (w.st id).box)
    (hprio : ∀ m, m ∈ a.prio → m ∈ (w.st id).prio)
    (hkeep : ∀ parent dead, HoldsTomb w parent dead →
      HoldsTomb (setActor w1 id a1) parent dead ∨ mailInFlight w dead = false) :
    Inv I (setActor w1 id a1) := by
  have hM1 := mail_copy w w1 h.2.1 hd.st
  have hl : ∀ i, ((setActor w1 id a1).st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hd.life, hlife]
    · rw [setActor_other w1 id i a1 hi, hd.st]
  have hparAll : ∀ i, ((setActor w1 id a1).st i).parent = (w.st i).parent := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hd.parent, hpar]
    · rw [setActor_other w1 id i a1 hi, hd.st]
  have hpkAll : ∀ i, ((setActor w1 id a1).st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, hd.parked, hpk]
    · rw [setActor_other w1 id i a1 hi, hd.st]
  have hcrW : (setActor w1 id a1).crashed = w.crashed := by
    simp only [setActor]
    exact hd.crashed
  have hroW : (setActor w1 id a1).roster = w.roster := by
    simp only [setActor]
    exact hd.roster
  refine ⟨hd.sem, ?_, ?_, ?_, ?_, ?_⟩
  · exact mail_set_free w1 id a1 hM1 (by rw [hd.st, hidle]; trivial) hd.free
      (by rw [hd.parked, hd.st, hpk]) (by rw [hd.st]; exact hd.life.trans hlife)
  · exact open_set w1 id a1 (open_shape w w1 h.2.2.1 (fun i hi => by rw [hd.roster]; exact hi)
      (fun i => by rw [hd.st])) (by rw [hd.roster]; exact h.1.rostered id halive)
  · exact outcome_set I w1 id a1
      (outcome_shape I w w1 h.2.2.2.1 (fun i => by rw [hd.st]) (fun i => by rw [hd.st])) hd.out
  · exact ParentForest.setActor
      (ParentForest.parents h.forest (fun i => by rw [hd.st]) hd.roster)
      (by rw [hd.st, hd.parent]; exact hpar)
  · refine ⟨parkedLive_set w1 id a1
      (parkedLive_same h.seal.liveParked (fun i => congrArg Actor.life (hd.st i))
        (fun i => congrArg Actor.parked (hd.st i)))
      ((hd.life.trans hlife).trans (congrArg Actor.life (hd.st id)).symm)
      (by rw [hd.parked, hd.st, hpk]), ?_, ?_, ?_, ?_, ?_⟩
    · rcases h.seal.quiet with hcr0 | hq
      · exact Or.inl (hcrW.trans hcr0)
      · refine Or.inr fun i hna => ?_
        have hi : i ≠ id := by
          intro he
          exact hna (by rw [he]; exact (hl id).trans halive)
        rcases hq i (fun ha => hna ((hl i).trans ha)) with ⟨hb, hp⟩
        exact ⟨by rw [setActor_other w1 id i a1 hi, hd.st]; exact hb, by rw [hpkAll i]; exact hp⟩
    · exact childless_stable h.seal.childless hcrW hl hparAll
    · exact chain_edit h.seal.chain h.seal.childless h.forest hcrW hroW hl hparAll
        (by
          intro i msg hm
          by_cases hi : i = id
          · subst hi
            rw [setActor_self, hd.box] at hm
            exact Or.inl ⟨msg, hbox msg hm, rfl, rfl⟩
          · rw [setActor_other w1 id i a1 hi, hd.st] at hm
            exact Or.inl ⟨msg, hm, rfl, rfl⟩)
        (by
          intro i msg hm
          by_cases hi : i = id
          · subst hi
            rw [setActor_self, hd.prio] at hm
            exact Or.inl ⟨msg, hprio msg hm, rfl, rfl⟩
          · rw [setActor_other w1 id i a1 hi, hd.st] at hm
            exact Or.inl ⟨msg, hm, rfl, rfl⟩)
        hkeep
    · exact parkedFrom_set w1 id a1
        (parkedFrom_same h.seal.parkedFrom (fun i => congrArg Actor.parked (hd.st i)))
        (by rw [hd.parked, hd.st, hpk])
    · exact hostedMail_set w1 id a1
        (hostedMail_same h.seal.hostedMail hd.roster (fun i => congrArg Actor.box (hd.st i))
          (fun i => congrArg Actor.prio (hd.st i)))
        (fun msg hm => Or.inl (by
          rw [hd.st]
          rw [hd.box] at hm
          exact hbox msg hm))
        (fun msg hm => Or.inl (by
          rw [hd.st]
          rw [hd.prio] at hm
          exact hprio msg hm))

theorem resume_call_ok (D : Description) (sid : InstId) (a : Actor) (dst : InstId) (k : Cont)
    (hc : contTy a) (hg : programOk D sid a) (hw : waitEdge D sid a)
    (hph : a.phase = .parked dst true k) :
    let b := resumeSender a true dst
    b.typestate = a.typestate ∧ b.life = a.life ∧ contTy b ∧ programOk D sid b ∧ waitEdge D sid b ∧
      notParked b.phase ∧ b.parked = a.parked := by
  unfold contTy at hc
  unfold programOk at hg
  unfold waitEdge at hw
  rw [hph] at hc hg hw
  simp only [resumeSender, hph, ite_true]
  exact ⟨trivial, trivial, hc, hg, hw, trivial, trivial⟩

theorem resume_off (a : Actor) (b : Bool) (dst : InstId) (h : a.phase = .idle ∨ a.phase = .crashed) :
    resumeSender a b dst = a := by
  rcases h with h | h <;> simp [resumeSender, h]

/-- Resuming a parked sender does not touch its mailbox. -/
theorem resume_queues (a : Actor) (c : Bool) (dst : InstId) :
    (resumeSender a c dst).box = a.box ∧ (resumeSender a c dst).prio = a.prio := by
  unfold resumeSender
  split
  · split
    · simp
    · unfold proceed
      split <;> simp
  · simp

/-- A parked entry on a live host names a live sender. A halted sender was
already dropped, and a parked phase is not how an absent or dead actor stands. -/
theorem parked_sender_alive (I : Impl) (w : World) (host : InstId) (p : Parked)
    (hS : SemInv I w) (hM : MailInv w) (hP : ParkedFromLive w)
    (hlive : (w.st host).life = .alive) (hp : p ∈ (w.st host).parked) :
    (w.st p.sender).life = .alive := by
  have hnd := hP host p hlive hp
  rcases hM.fwd host p hp with ⟨_, hph⟩ | hhalt
  · exact Classical.byContradiction fun hna => by
      rcases hS.idleOff p.sender hna with hi | hi
      · rw [hph] at hi
        cases hi
      · rw [hph] at hi
        cases hi
  · exact absurd hhalt hnd

/-- One parked entry is admitted after the receiver is installed: the sender is credited,
and a sender still parked on this mailbox resumes. -/
theorem resume_one (I : Impl) (w w1 : World) (id : InstId) (cur : Actor) (p : Parked) (ps : List Parked)
    (who : InstId) (h : Inv I w) (hS : SemInv I (setActor w1 id cur)) (hst : ∀ i, w1.st i = w.st i)
    (hro : w1.roster = w.roster) (hidle : (w.st id).phase = .idle) (halive : (w.st id).life = .alive)
    (hqueue : (w.st id).parked = p :: ps)     (hcurPk : cur.parked = ps) (hcurPh : notParked cur.phase)
    (hcurLife : cur.life = (w.st id).life) (hcurOut : outcomeOk I id cur)
    (hcurPar : cur.parent = (w1.st id).parent) (hcr1 : w1.crashed = w.crashed)
    (hbox : ∀ m, m ∈ cur.box → m ∈ (w.st id).box ∨ m.sender = p.sender)
    (hprio : cur.prio = (w.st id).prio) :
    Inv I (setActor (creditSender (setActor w1 id cur) (tname id) who) p.sender
      (resumeSender ((creditSender (setActor w1 id cur) (tname id) who).st p.sender) p.isCall id)) := by
  have hM := h.2.1
  have hfree : notParked (w.st id).phase := by rw [hidle]; trivial
  have hmemp : p ∈ (w.st id).parked := by rw [hqueue]; exact List.mem_cons_self
  have hsnd : p.sender ≠ id := not_queued w id hM hfree halive id p hmemp
  generalize hbase : setActor w1 id cur = base at hS
  have hcr := same_credit base (tname id) who
  have hS1 : SemInv I (creditSender base (tname id) who) := credit_sem I base (tname id) who hS
  generalize hcred : creditSender base (tname id) who = cred at hcr hS1
  have hbid : base.st id = cur := by rw [← hbase, setActor_self]
  have hbo : ∀ i, i ≠ id → base.st i = w.st i := by
    intro i hi
    rw [← hbase, setActor_other w1 id i cur hi, hst]
  have hbr : base.roster = w.roster := by rw [← hbase]; exact hro
  have hsl : (cred.st p.sender).life = (w.st p.sender).life := by rw [hcr.life, hbo _ hsnd]
  have hsp : (cred.st p.sender).phase = (w.st p.sender).phase := by rw [hcr.phase, hbo _ hsnd]
  have hsty : (cred.st p.sender).typestate = (w.st p.sender).typestate := by rw [hcr.ty, hbo _ hsnd]
  have hsk : (cred.st p.sender).parked = (w.st p.sender).parked := by rw [hcr.parked, hbo _ hsnd]
  have hcont : contTy (cred.st p.sender) := contTy_congr hsp hsty (h.1.cont _)
  have hprog : programOk I.desc p.sender (cred.st p.sender) := programOk_congr _ _ hsp (h.1.prog _)
  have hwait : waitEdge I.desc p.sender (cred.st p.sender) := waitEdge_congr _ _ hsp hsty (h.1.waited _)
  have hout : outcomeOk I p.sender (cred.st p.sender) :=
    outcome_congr I p.sender hsp hsty (h.2.2.2.1 _)
  have hstat : (∃ k, (cred.st p.sender).phase = .parked id p.isCall k) ∨
      ((cred.st p.sender).phase = .idle ∨ (cred.st p.sender).phase = .crashed) := by
    rcases hM.fwd id p hmemp with ⟨k, hk⟩ | hh
    · exact Or.inl ⟨k, by rw [hsp]; exact hk⟩
    · right
      rw [hsp]
      exact h.1.idleOff _ (by rw [hh]; intro he; cases he)
  have hres : (resumeSender (cred.st p.sender) p.isCall id).typestate = (cred.st p.sender).typestate ∧
      (resumeSender (cred.st p.sender) p.isCall id).life = (cred.st p.sender).life ∧
      contTy (resumeSender (cred.st p.sender) p.isCall id) ∧
      programOk I.desc p.sender (resumeSender (cred.st p.sender) p.isCall id) ∧
      waitEdge I.desc p.sender (resumeSender (cred.st p.sender) p.isCall id) ∧
      notParked (resumeSender (cred.st p.sender) p.isCall id).phase ∧
      (resumeSender (cred.st p.sender) p.isCall id).parked = (cred.st p.sender).parked := by
    cases hc : p.isCall with
    | false => exact resume_false_ok I.desc p.sender (cred.st p.sender) id hcont hprog hwait
    | true =>
      rcases hstat with ⟨k, hk⟩ | hoff
      · rw [hc] at hk
        exact resume_call_ok I.desc p.sender (cred.st p.sender) id k hcont hprog hwait hk
      · rw [resume_off _ _ _ hoff]
        exact ⟨rfl, rfl, hcont, hprog, hwait,
          by rcases hoff with hp | hp <;> rw [hp] <;> trivial, rfl⟩
  have hrout : outcomeOk I p.sender (resumeSender (cred.st p.sender) p.isCall id) := by
    apply outcome_resume I p.sender _ p.isCall id hout
    intro d c k hph hb
    rcases hstat with ⟨k', hk'⟩ | hoff
    · rw [hk'] at hph
      cases hph
      exact hb
    · rcases hoff with hp | hp <;> rw [hp] at hph <;> cases hph
  generalize hr : resumeSender (cred.st p.sender) p.isCall id = r at hres hrout
  have hrsem : SemInv I (setActor cred p.sender r) :=
    sem_set I cred p.sender r hS1 hres.1 hres.2.1 hres.2.2.1 hres.2.2.2.1 hres.2.2.2.2.1
      (by rw [← hr]; exact idleOff_resume I cred hS1 p.sender p.isCall id) (Or.inl hres.2.2.2.2.2.2)
  have hlifeAll : ∀ i, ((setActor cred p.sender r).st i).life = (w.st i).life := by
    intro i
    by_cases hi : i = p.sender
    · rw [hi, setActor_self, hres.2.1, hsl]
    · rw [setActor_other cred p.sender i r hi, hcr.life]
      by_cases hii : i = id
      · rw [hii, hbid, hcurLife]
      · rw [hbo i hii]
  have hidst : (setActor cred p.sender r).st id = cred.st id := setActor_other cred p.sender id r (Ne.symm hsnd)
  have hphO : ∀ i, i ≠ id → i ≠ p.sender → ((setActor cred p.sender r).st i).phase = (w.st i).phase := by
    intro i hi hs
    rw [setActor_other cred p.sender i r hs, hcr.phase, hbo i hi]
  refine ⟨hrsem, ?_, ?_, ?_, ?_, ?_⟩
  · apply mail_drop w _ id p ps hM hfree hqueue
    · rw [hidst, hcr.phase, hbid]
      exact hcurPh
    · rw [hidst, hcr.parked, hbid]
      exact hcurPk
    · intro i hi
      by_cases hs : i = p.sender
      · rw [hs, setActor_self, hres.2.2.2.2.2.2, hsk]
      · rw [setActor_other cred p.sender i r hs, hcr.parked, hbo i hi]
    · rw [setActor_self]
      exact hres.2.2.2.2.2.1
    · exact hphO
    · intro i hd
      rw [hlifeAll]
      exact hd
    · exact halive
    · intro i hh
      rw [hlifeAll]
      exact hh
  · apply open_shape w _ h.2.2.1 _ hlifeAll
    intro i hi
    show i ∈ cred.roster
    rw [hcr.roster, hbr]
    exact hi
  · intro i
    by_cases hs : i = p.sender
    · rw [hs, setActor_self]
      exact hrout
    · rw [setActor_other cred p.sender i r hs]
      by_cases hii : i = id
      · rw [hii]
        exact outcome_congr I id (by rw [hcr.phase, hbid]) (by rw [hcr.ty, hbid]) hcurOut
      · exact outcome_congr I i (by rw [hcr.phase, hbo i hii]) (by rw [hcr.ty, hbo i hii]) (h.2.2.2.1 i)
  · have hfBase : ParentForest base := by
      rw [← hbase]
      exact ParentForest.setActor (ParentForest.parents h.forest (fun i => by rw [hst]) hro) hcurPar
    have hfCred : ParentForest cred := by
      rw [← hcred]
      exact ParentForest.parents hfBase (fun i => creditSender_parent _ _ _ i) rfl
    exact ParentForest.setActor hfCred (by rw [← hr]; exact resumeSender_parent _ _ _)
  · have hsender := parked_sender_alive I w id p h.1 h.2.1 h.seal.liveParked halive hmemp
    have hcrW : (setActor cred p.sender r).crashed = w.crashed := by
      simp only [setActor]
      rw [← hcred]
      simp only [creditSender, setActor]
      rw [← hbase]
      simp only [setActor]
      exact hcr1
    have hroW : (setActor cred p.sender r).roster = w.roster := by
      simp only [setActor]
      rw [← hcred]
      simp only [creditSender, setActor]
      rw [← hbase]
      simp only [setActor]
      exact hro
    have hparAll : ∀ i, ((setActor cred p.sender r).st i).parent = (w.st i).parent := by
      intro i
      by_cases hs : i = p.sender
      · subst hs
        rw [setActor_self, ← hr, resumeSender_parent, ← hcred, creditSender_parent, ← hbase,
          setActor_other w1 id p.sender cur hsnd, hst]
      · rw [setActor_other cred p.sender i r hs, ← hcred, creditSender_parent, ← hbase]
        by_cases hi : i = id
        · subst hi
          rw [setActor_self, hcurPar, hst]
        · rw [setActor_other w1 id i cur hi, hst]
    have hboxKeep : ∀ i, i ≠ id → ((setActor cred p.sender r).st i).box = (w.st i).box := by
      intro i hi
      by_cases hs : i = p.sender
      · subst hs
        rw [setActor_self, ← hr, (resume_queues _ _ _).1, ← hcred]
        rw [(credit_fields base (tname id) who p.sender).2.2.1, ← hbase,
          setActor_other w1 id p.sender cur hsnd, hst]
      · rw [setActor_other cred p.sender i r hs, ← hcred]
        rw [(credit_fields base (tname id) who i).2.2.1, ← hbase, setActor_other w1 id i cur hi, hst]
    have hprioKeep : ∀ i, i ≠ id → ((setActor cred p.sender r).st i).prio = (w.st i).prio := by
      intro i hi
      by_cases hs : i = p.sender
      · subst hs
        rw [setActor_self, ← hr, (resume_queues _ _ _).2, ← hcred]
        rw [(credit_fields base (tname id) who p.sender).2.2.2.2, ← hbase,
          setActor_other w1 id p.sender cur hsnd, hst]
      · rw [setActor_other cred p.sender i r hs, ← hcred]
        rw [(credit_fields base (tname id) who i).2.2.2.2, ← hbase, setActor_other w1 id i cur hi, hst]
    have hprioId : ((setActor cred p.sender r).st id).prio = (w.st id).prio := by
      rw [setActor_other cred p.sender id r (Ne.symm hsnd), ← hcred]
      rw [(credit_fields base (tname id) who id).2.2.2.2, ← hbase, setActor_self, hprio]
    have hboxId : ∀ m, m ∈ ((setActor cred p.sender r).st id).box → m ∈ cur.box := by
      intro m hm
      rw [setActor_other cred p.sender id r (Ne.symm hsnd), ← hcred] at hm
      rw [(credit_fields base (tname id) who id).2.2.1, ← hbase, setActor_self] at hm
      exact hm
    refine ⟨parkedLive_sub h.seal.liveParked hlifeAll ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro host q hq
      by_cases hh : host = p.sender
      · rw [hh] at hq ⊢
        rw [setActor_self, hres.2.2.2.2.2.2, hsk] at hq
        exact hq
      · rw [setActor_other cred p.sender host r hh] at hq
        by_cases hid : host = id
        · rw [hid] at hq ⊢
          rw [hcr.parked, hbid, hcurPk] at hq
          rw [hqueue]
          exact List.mem_cons_of_mem _ hq
        · rw [hcr.parked, hbo host hid] at hq
          exact hq
    · rcases h.seal.quiet with hcr0 | hq
      · exact Or.inl (hcrW.trans hcr0)
      · refine Or.inr fun i hna => ?_
        have hi : i ≠ id := by
          intro he
          rw [he] at hna
          exact hna ((hlifeAll id).trans halive)
        rcases hq i (fun ha => hna ((hlifeAll i).trans ha)) with ⟨hb, hp⟩
        refine ⟨by rw [hboxKeep i hi]; exact hb, ?_⟩
        by_cases hs : i = p.sender
        · rw [hs] at hp ⊢
          rw [setActor_self, hres.2.2.2.2.2.2, hsk]
          exact hp
        · rw [setActor_other cred p.sender i r hs, ← hcred,
            (credit_fields base (tname id) who i).2.2.2.1, ← hbase, setActor_other w1 id i cur hi, hst]
          exact hp
    · exact childless_stable h.seal.childless hcrW hlifeAll hparAll
    · exact chain_edit h.seal.chain h.seal.childless h.forest hcrW hroW hlifeAll hparAll
        (by
          intro host m hm
          by_cases hid : host = id
          · subst hid
            rcases hbox m (hboxId m hm) with hold | hsend
            · exact Or.inl ⟨m, hold, rfl, rfl⟩
            · exact Or.inr (Or.inr (by rw [hsend]; exact hsender))
          · rw [hboxKeep host hid] at hm
            exact Or.inl ⟨m, hm, rfl, rfl⟩)
        (by
          intro host m hm
          by_cases hid : host = id
          · subst hid
            rw [hprioId] at hm
            exact Or.inl ⟨m, hm, rfl, rfl⟩
          · rw [hprioKeep host hid] at hm
            exact Or.inl ⟨m, hm, rfl, rfl⟩)
        (by
          intro parent dead ht
          rcases ht with ⟨msg, hm, htom, hs⟩
          refine Or.inl ⟨msg, ?_, htom, hs⟩
          by_cases hid : parent = id
          · subst hid
            rw [hprioId]
            exact hm
          · rw [hprioKeep parent hid]
            exact hm)
    · exact parkedFrom_sub h.seal.parkedFrom (by
        intro host q hq
        by_cases hs : host = p.sender
        · rw [hs] at hq ⊢
          rw [setActor_self, hres.2.2.2.2.2.2, hsk] at hq
          exact hq
        · rw [setActor_other cred p.sender host r hs] at hq
          by_cases hid : host = id
          · rw [hid] at hq ⊢
            rw [← hcred, (credit_fields base (tname id) who id).2.2.2.1, ← hbase, setActor_self,
              hcurPk] at hq
            rw [hqueue]
            exact List.mem_cons_of_mem _ hq
          · rw [← hcred, (credit_fields base (tname id) who host).2.2.2.1, ← hbase,
              setActor_other w1 id host cur hid, hst] at hq
            exact hq)
    · intro host m hm
      rw [hroW]
      by_cases hid : host = id
      · rw [hid] at hm
        rcases hm with hm | hm
        · rcases hbox m (hboxId m hm) with hold | hsend
          · exact h.seal.hostedMail id m (Or.inl hold)
          · rw [hsend]
            exact h.1.rostered p.sender hsender
        · rw [hprioId] at hm
          exact h.seal.hostedMail id m (Or.inr hm)
      · rcases hm with hm | hm
        · rw [hboxKeep host hid] at hm
          exact h.seal.hostedMail host m (Or.inl hm)
        · rw [hprioKeep host hid] at hm
          exact h.seal.hostedMail host m (Or.inr hm)

theorem sem_requeue (I : Impl) (w : World) (id : InstId) (a b : Actor) (hS : SemInv I (setActor w id a))
    (hl : b.life = a.life) (ht : b.typestate = a.typestate) (hp : b.phase = a.phase)
    (hmem : id ∈ w.roster) : SemInv I (setActor w id b) := by
  apply sem_shape I (setActor w id a) (setActor w id b) hS rfl
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, setActor_self]; exact hl
    · rw [setActor_other w id i b hi, setActor_other w id i a hi]
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, setActor_self]; exact ht
    · rw [setActor_other w id i b hi, setActor_other w id i a hi]
  · intro i
    by_cases hi : i = id
    · rw [hi, setActor_self, setActor_self]; exact hp
    · rw [setActor_other w id i b hi, setActor_other w id i a hi]
  · intro i hi
    have hne : i ≠ id := fun he => hi (by rw [he]; exact hmem)
    rw [setActor_other w id i b hne, setActor_other w id i a hne]

theorem receive_bulk_inv (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (h : Inv I w) (hs : receiveBulk I w id = some w') : Inv I w' := by
  unfold receiveBulk at hs
  dsimp only at hs
  split at hs
  · cases hs
  · next hready =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, ne_eq, Decidable.not_not] at hready
    obtain ⟨halive, hidle⟩ := hready
    have hmem : id ∈ w.roster := h.1.rostered id halive
    cases hbox : (w.st id).box with
    | nil =>
      cases hpk : (w.st id).parked with
      | nil => simp [hbox, hpk] at hs
      | cons p ps =>
        simp only [hbox, hpk] at hs
        split at hs
        · cases hs
        · next w1 a1 hd =>
          cases hs
          have hd' := deliver_ok I hL w id _ p.msg w1 a1 h.1 (by rfl) (by rfl) hd
          exact resume_one I w w1 id a1 p ps _ h hd'.sem hd'.st hd'.roster hidle halive hpk hd'.parked
            hd'.free hd'.life hd'.out (by rw [hd'.parent, hd'.st]) hd'.crashed
            (by
              intro msg hm
              exact Or.inl (by
                rw [hd'.box] at hm
                rw [hbox]
                exact hm))
            (by rw [hd'.prio])
    | cons m ms =>
      cases hpk : (w.st id).parked with
      | nil =>
        simp only [hbox, hpk] at hs
        split at hs
        · cases hs
        · next w1 a1 hd =>
          cases hs
          have hd' := deliver_ok I hL w id ({ (w.st id) with box := ms, parked := [] }) m w1 a1 h.1
            (by rfl) (by rfl) hd
          have hsubB : ∀ msg, msg ∈ ({ (w.st id) with box := ms, parked := [] } : Actor).box →
              msg ∈ (w.st id).box := by
            intro msg hm
            simp at hm
            rw [hbox]
            exact List.mem_cons_of_mem _ hm
          have hsubP : ∀ msg, msg ∈ ({ (w.st id) with box := ms, parked := [] } : Actor).prio →
              msg ∈ (w.st id).prio := by
            intro msg hm
            simpa using hm
          have hkeep : ∀ parent dead, HoldsTomb w parent dead →
              HoldsTomb (setActor w1 id a1) parent dead ∨ mailInFlight w dead = false := by
            intro parent dead ht
            rcases ht with ⟨msg, hm, htom, hsnd⟩
            refine Or.inl ⟨msg, ?_, htom, hsnd⟩
            by_cases hp : parent = id
            · rw [hp] at hm ⊢
              rw [setActor_self, hd'.prio]
              simpa using hm
            · rw [setActor_other w1 id parent a1 hp, hd'.st]
              exact hm
          exact inv_same I _ _
            (inv_deliver I w w1 id ({ (w.st id) with box := ms, parked := [] }) a1 h hd' hidle halive
              rfl (hpk.symm) rfl hsubB hsubP hkeep)
            (same_credit _ _ _) (fun i => (credit_fields _ _ _ i).2.2.1)
            (fun i => (credit_fields _ _ _ i).2.2.2.2) (by simp [creditSender, setActor])
      | cons p ps =>
        simp only [hbox, hpk] at hs
        split at hs
        · cases hs
        · next w1 a1 hd =>
          cases hs
          have hd' := deliver_ok I hL w id _ m w1 a1 h.1 (by rfl) (by rfl) hd
          have hS2 : SemInv I (setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps }) :=
            sem_requeue I w1 id a1 _ hd'.sem rfl rfl rfl (by rw [hd'.roster]; exact hmem)
          exact resume_one I w w1 id { a1 with box := a1.box ++ [p.msg], parked := ps } p ps _ h hS2 hd'.st
            hd'.roster hidle halive hpk rfl hd'.free hd'.life (outcome_congr I id rfl rfl hd'.out)
            (by rw [hd'.parent, hd'.st]) hd'.crashed
            (by
              intro msg hm
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | hm
              · refine Or.inl ?_
                rw [hd'.box] at hm
                rw [hbox]
                exact List.mem_cons_of_mem _ hm
              · refine Or.inr ?_
                have hfrom := h.seal.parkedFrom id p (by rw [hpk]; exact List.mem_cons_self)
                rw [hm]
                exact hfrom.symm)
            (by rw [hd'.prio])

theorem receive_prio_inv (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (h : Inv I w) (hs : receivePrio I w id = some w') : Inv I w' := by
  obtain ⟨m, pre, suf, w1, a1, halive, hidle, hsplit, hwait, hd, hw'⟩ :=
    receivePrio_spec I w w' id hs
  subst hw'
  have hd' := deliver_ok I hL w id ({ (w.st id) with prio := pre ++ suf }) m w1 a1 h.1
    (by rfl) (by rfl) hd
  have hsubB : ∀ msg, msg ∈ ({ (w.st id) with prio := pre ++ suf } : Actor).box →
      msg ∈ (w.st id).box := by
    intro msg hm
    simpa using hm
  have hsubP : ∀ msg, msg ∈ ({ (w.st id) with prio := pre ++ suf } : Actor).prio →
      msg ∈ (w.st id).prio := by
    intro msg hm
    rw [hsplit]
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · exact List.mem_append_left _ hm
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
  have hkeep : ∀ parent dead, HoldsTomb w parent dead →
      HoldsTomb (setActor w1 id a1) parent dead ∨ mailInFlight w dead = false := by
    intro parent dead ht
    rcases ht with ⟨msg, hm, htom, hsnd⟩
    by_cases hp : parent = id
    · rw [hp, hsplit] at hm
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with hm | hm | hm
      · refine Or.inl ⟨msg, ?_, htom, hsnd⟩
        rw [hp, setActor_self, hd'.prio]
        simp only [List.mem_append]
        exact Or.inl hm
      · rw [hm] at htom hsnd
        exact Or.inr (by rw [← hsnd]; exact tombstone_clear_of_take w m hwait htom)
      · refine Or.inl ⟨msg, ?_, htom, hsnd⟩
        rw [hp, setActor_self, hd'.prio]
        simp only [List.mem_append]
        exact Or.inr hm
    · refine Or.inl ⟨msg, ?_, htom, hsnd⟩
      rw [setActor_other w1 id parent a1 hp, hd'.st]
      exact hm
  exact inv_deliver I w w1 id ({ (w.st id) with prio := pre ++ suf }) a1 h hd' hidle halive rfl rfl
    rfl hsubB hsubP hkeep

theorem clear_cont (caller : InstId) (k : Cont) : ∃ r, clearReplyCont caller k = { k with replyTo := r } := by
  unfold clearReplyCont
  split
  · exact ⟨none, rfl⟩
  · exact ⟨k.replyTo, rfl⟩

/-- Forgetting a reply obligation keeps every checked field of the continuation. -/
theorem clear_preds (I : Impl) (id caller : InstId) (a b : Actor)
    (hp : b.phase = clearReplyPhase caller a.phase) (ht : b.typestate = a.typestate)
    (hc : contTy a) (hg : programOk I.desc id a) (hw : waitEdge I.desc id a) (ho : outcomeOk I id a) :
    contTy b ∧ programOk I.desc id b ∧ waitEdge I.desc id b ∧ outcomeOk I id b := by
  cases hph : a.phase with
  | idle =>
    have hb : b.phase = .idle := by rw [hp, hph]; rfl
    exact ⟨by unfold contTy; rw [hb]; trivial, by unfold programOk; rw [hb]; trivial,
      by unfold waitEdge; rw [hb]; trivial, by unfold outcomeOk; rw [hb]; trivial⟩
  | crashed =>
    have hb : b.phase = .crashed := by rw [hp, hph]; rfl
    exact ⟨by unfold contTy; rw [hb]; trivial, by unfold programOk; rw [hb]; trivial,
      by unfold waitEdge; rw [hb]; trivial, by unfold outcomeOk; rw [hb]; trivial⟩
  | run k =>
    obtain ⟨r, hr⟩ := clear_cont caller k
    have hb : b.phase = .run { k with replyTo := r } := by
      rw [hp, hph, show clearReplyPhase caller (Phase.run k) = Phase.run (clearReplyCont caller k) from rfl, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold contTy at hc ⊢
      rw [hph] at hc
      rw [hb, ht]
      exact hc
    · unfold programOk at hg ⊢
      rw [hph] at hg
      rw [hb]
      exact hg
    · unfold waitEdge at hw ⊢
      rw [hph] at hw
      rw [hb, ht]
      exact hw
    · unfold outcomeOk at ho ⊢
      rw [hph] at ho
      rw [hb]
      exact src_reply I id b k r (src_ty I id k ht ho)
  | parked d c k =>
    obtain ⟨r, hr⟩ := clear_cont caller k
    have hb : b.phase = .parked d c { k with replyTo := r } := by
      rw [hp, hph,
        show clearReplyPhase caller (Phase.parked d c k) =
          Phase.parked d c (clearReplyCont caller k) from rfl, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold contTy at hc ⊢
      rw [hph] at hc
      rw [hb, ht]
      exact hc
    · unfold programOk at hg ⊢
      rw [hph] at hg
      rw [hb]
      exact hg
    · unfold waitEdge at hw ⊢
      rw [hph] at hw
      rw [hb, ht]
      exact hw
    · unfold outcomeOk at ho ⊢
      rw [hph] at ho
      rw [hb]
      exact ⟨src_reply I id b k r (src_ty I id k ht ho.1), ho.2⟩
  | awaitReply d k =>
    obtain ⟨r, hr⟩ := clear_cont caller k
    have hb : b.phase = .awaitReply d { k with replyTo := r } := by
      rw [hp, hph,
        show clearReplyPhase caller (Phase.awaitReply d k) =
          Phase.awaitReply d (clearReplyCont caller k) from rfl, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold contTy at hc ⊢
      rw [hph] at hc
      rw [hb, ht]
      exact hc
    · unfold programOk at hg ⊢
      rw [hph] at hg
      rw [hb]
      exact hg
    · unfold waitEdge at hw ⊢
      rw [hph] at hw
      rw [hb, ht]
      exact hw
    · unfold outcomeOk at ho ⊢
      rw [hph] at ho
      rw [hb]
      exact ⟨src_reply I id b k r (src_ty I id k ht ho.1), ho.2⟩
  | awaitEffect k =>
    obtain ⟨r, hr⟩ := clear_cont caller k
    have hb : b.phase = .awaitEffect { k with replyTo := r } := by
      rw [hp, hph,
        show clearReplyPhase caller (Phase.awaitEffect k) =
          Phase.awaitEffect (clearReplyCont caller k) from rfl, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold contTy at hc ⊢
      rw [hph] at hc
      rw [hb, ht]
      exact hc
    · unfold programOk at hg ⊢
      rw [hph] at hg
      rw [hb]
      exact hg
    · unfold waitEdge at hw ⊢
      rw [hph] at hw
      rw [hb, ht]
      exact hw
    · unfold outcomeOk at ho ⊢
      rw [hph] at ho
      rw [hb]
      exact src_reply I id b k r (src_ty I id k ht ho)
  | awaitPeer k =>
    obtain ⟨r, hr⟩ := clear_cont caller k
    have hb : b.phase = .awaitPeer { k with replyTo := r } := by
      rw [hp, hph,
        show clearReplyPhase caller (Phase.awaitPeer k) =
          Phase.awaitPeer (clearReplyCont caller k) from rfl, hr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold contTy at hc ⊢
      rw [hph] at hc
      rw [hb, ht]
      exact hc
    · unfold programOk at hg ⊢
      rw [hph] at hg
      rw [hb]
      exact hg
    · unfold waitEdge at hw ⊢
      rw [hph] at hw
      rw [hb, ht]
      exact hw
    · unfold outcomeOk at ho ⊢
      rw [hph] at ho
      rw [hb]
      exact ⟨src_reply I id b k r (src_ty I id k ht ho.1), ho.2⟩

theorem detach_phase (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).phase = clearReplyPhase caller a.phase ∨
      (detachReply (detachBox a caller) caller cid).phase = a.phase := by
  unfold detachReply
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem detach_preds (I : Impl) (id caller : InstId) (a : Actor) (cid : Nat)
    (hc : contTy a) (hg : programOk I.desc id a) (hw : waitEdge I.desc id a) (ho : outcomeOk I id a) :
    contTy (detachReply (detachBox a caller) caller cid) ∧
      programOk I.desc id (detachReply (detachBox a caller) caller cid) ∧
      waitEdge I.desc id (detachReply (detachBox a caller) caller cid) ∧
      outcomeOk I id (detachReply (detachBox a caller) caller cid) := by
  have ht := (detachHost_rest a caller cid).1
  rcases detach_phase a caller cid with hp | hp
  · exact clear_preds I id caller a _ hp ht hc hg hw ho
  · exact ⟨contTy_congr hp ht hc, programOk_congr I.desc id hp hg, waitEdge_congr I.desc id hp ht hw,
      outcome_congr I id hp ht ho⟩

theorem detach_off (a : Actor) (caller : InstId) (cid : Nat) (h : a.phase = .idle ∨ a.phase = .crashed) :
    (detachReply (detachBox a caller) caller cid).phase = .idle ∨
      (detachReply (detachBox a caller) caller cid).phase = .crashed := by
  rcases detach_phase a caller cid with hp | hp <;> rw [hp]
  · rcases h with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact h

theorem detach_free (a : Actor) (caller : InstId) (cid : Nat) (h : notParked a.phase) :
    notParked (detachReply (detachBox a caller) caller cid).phase := by
  rcases detach_phase a caller cid with hp | hp <;> rw [hp]
  · revert h
    cases a.phase <;> exact fun h => h
  · exact h

theorem detach_keeps (caller : InstId) (m : Msg) :
    (detachMsg caller m).sender = m.sender ∧ (detachMsg caller m).tombstone = m.tombstone := by
  unfold detachMsg
  split <;> simp

theorem detach_inv (I : Impl) (w : World) (dst caller : InstId) (cid : Nat) (h : Inv I w) :
    Inv I (setActor w dst (detachReply (detachBox (w.st dst) caller) caller cid)) := by
  have hrest := detachHost_rest (w.st dst) caller cid
  have hpre := detach_preds I dst caller (w.st dst) cid (h.1.cont dst) (h.1.prog dst) (h.1.waited dst)
    (h.2.2.2.1 dst)
  have hlife : ∀ i, ((setActor w dst (detachReply (detachBox (w.st dst) caller) caller cid)).st i).life =
      (w.st i).life := by
    intro i
    by_cases hi : i = dst
    · rw [hi, setActor_self]
      exact hrest.2.1
    · rw [setActor_other w dst i _ hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply sem_set I w dst _ h.1 hrest.1 hrest.2.1 hpre.1 hpre.2.1 hpre.2.2.1
    · intro hd
      exact detach_off _ _ _ (h.1.idleOff dst (by rw [← hrest.2.1]; exact hd))
    · exact Or.inl hrest.2.2
  · exact mail_scrub w dst _ h.2.1 hrest.2.2 hrest.2.1
      (fun d c k hk => (detachHost_park (w.st dst) caller cid d c).mpr ⟨k, hk⟩)
      (fun d c k hk => (detachHost_park (w.st dst) caller cid d c).mp ⟨k, hk⟩)
  · exact open_shape w _ h.2.2.1 (fun i hi => hi) hlife
  · exact outcome_set I w dst _ h.2.2.2.1 hpre.2.2.2
  · exact ParentForest.setActor h.forest (detachHost_parent _ _ _)
  · let a := detachReply (detachBox (w.st dst) caller) caller cid
    let w' := setActor w dst a
    have hprioA : a.prio = (w.st dst).prio := by
      simp only [a]
      unfold detachReply detachBox
      split <;> simp
    have hboxA : a.box = ((w.st dst).box.map (detachMsg caller)) := by
      simp only [a]
      unfold detachReply detachBox
      split <;> simp
    have hpar : ∀ i, (w'.st i).parent = (w.st i).parent := by
      intro i
      by_cases hi : i = dst
      · rw [hi, setActor_self]
        exact detachHost_parent _ _ _
      · rw [setActor_other w dst i _ hi]
    have hboxL : ∀ i, i ≠ dst → (w'.st i).box = (w.st i).box := by
      intro i hi
      rw [setActor_other w dst i _ hi]
    have hprioL : ∀ i, (w'.st i).prio = (w.st i).prio := by
      intro i
      by_cases hi : i = dst
      · rw [hi, setActor_self, hprioA]
      · rw [setActor_other w dst i _ hi]
    have hpkL : ∀ i, (w'.st i).parked = (w.st i).parked := by
      intro i
      by_cases hi : i = dst
      · rw [hi, setActor_self]
        exact hrest.2.2
      · rw [setActor_other w dst i _ hi]
    exact {
      liveParked := parkedLive_set w dst a h.seal.liveParked hrest.2.1 hrest.2.2
      quiet := by
        rcases h.seal.quiet with hcr | hq
        · exact Or.inl (by simpa [w', setActor] using hcr)
        · refine Or.inr fun i hna => ?_
          by_cases hi : i = dst
          · have hna0 : (w.st i).life ≠ .alive := by
              intro ha
              exact hna (by rw [hlife i]; exact ha)
            rcases hq i hna0 with ⟨hb, hp⟩
            rw [hi] at hb hp
            rw [hi, setActor_self, hboxA, hb]
            simp [hp, hrest.2.2]
          · have hna0 : (w.st i).life ≠ .alive := by
              intro ha
              exact hna (by rw [hlife i]; exact ha)
            rcases hq i hna0 with ⟨hb, hp⟩
            exact ⟨(hboxL i hi).trans hb, (hpkL i).trans hp⟩
      childless := childless_stable h.seal.childless (by simp [w', setActor]) hlife hpar
      chain := chain_edit h.seal.chain h.seal.childless h.forest (by simp [w', setActor]) rfl
        hlife hpar
        (fun i m hm => by
          by_cases hi : i = dst
          · rw [hi] at hm ⊢
            rw [setActor_self, hboxA] at hm
            obtain ⟨m', hm', heq⟩ := List.mem_map.mp hm
            have hk := detach_keeps caller m'
            exact Or.inl ⟨m', hm', by rw [← heq]; exact hk.1.symm, by rw [← heq]; exact hk.2.symm⟩
          · exact Or.inl ⟨m, by rw [hboxL i hi] at hm; exact hm, rfl, rfl⟩)
        (fun i m hm => Or.inl ⟨m, by rw [hprioL i] at hm; exact hm, rfl, rfl⟩)
        (fun parent id ht => Or.inl (by
          obtain ⟨m, hm, htomb, hsnd⟩ := ht
          exact ⟨m, by rw [hprioL parent]; exact hm, htomb, hsnd⟩))
      parkedFrom := parkedFrom_same h.seal.parkedFrom hpkL
      hostedMail := by
        intro host m hm
        by_cases hh : host = dst
        · rw [hh] at hm
          rcases hm with hm | hm
          · rw [setActor_self, hboxA] at hm
            obtain ⟨m', hm', heq⟩ := List.mem_map.mp hm
            have hk := detach_keeps caller m'
            rw [← heq, hk.1]
            exact h.seal.hostedMail dst m' (Or.inl hm')
          · rw [setActor_self, hprioA] at hm
            exact h.seal.hostedMail dst m (Or.inr hm)
        · rw [setActor_other w dst host _ hh] at hm
          exact h.seal.hostedMail host m hm
    }

theorem refund_call_roster (w : World) (caller dst : InstId) :
    (refundParkedCall w caller dst).roster = w.roster := by
  unfold refundParkedCall
  dsimp only
  split
  · rfl
  · have hfold : ∀ (ps : List Parked) (w0 : World), w0.roster = w.roster →
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).roster = w.roster := by
      intro ps
      induction ps with
      | nil => intro w0 h; exact h
      | cons _ ps ih =>
        intro w0 h
        simp only [List.foldl_cons]
        exact ih _ (by rw [creditSender, setActor]; exact h)
    exact hfold _ _ (by rw [setActor])

/-- A parked-call refund edits the target's parked lane and then credits the caller.
Bulk mail, priority mail, and the crash bit stay. -/
theorem refund_queues (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).box = (w.st i).box ∧
      ((refundParkedCall w caller dst).st i).prio = (w.st i).prio ∧
      (refundParkedCall w caller dst).crashed = w.crashed := by
  unfold refundParkedCall
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl⟩
  · have hfold : ∀ (ps : List Parked) (w0 : World),
        (w0.st i).box = (w.st i).box → (w0.st i).prio = (w.st i).prio →
        w0.crashed = w.crashed →
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).box = (w.st i).box) ∧
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).prio =
          (w.st i).prio) ∧
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).crashed = w.crashed := by
      intro ps
      induction ps with
      | nil =>
        intro w0 hb hp hc
        exact ⟨hb, hp, hc⟩
      | cons _ ps ih =>
        intro w0 hb hp hc
        simp only [List.foldl_cons]
        have hcF := credit_fields w0 (tname dst) caller i
        exact ih _ (hcF.2.2.1.trans hb) (hcF.2.2.2.2.trans hp) (by
          rw [creditSender, setActor]
          exact hc)
    refine hfold _ _ ?_ ?_ (by rw [setActor])
    · by_cases hi : i = dst
      · rw [hi, setActor_self]
      · rw [setActor_other w dst i _ hi]
    · by_cases hi : i = dst
      · rw [hi, setActor_self]
      · rw [setActor_other w dst i _ hi]

theorem setActor_at (w : World) (dst id : InstId) (a : Actor) (h : id = dst) : (setActor w dst a).st id = a := by
  rw [h, setActor_self]

theorem callTimeout_inv (I : Impl) (w w' : World) (id : InstId) (h : Inv I w)
    (hs : callTimeout w id = some w') : Inv I w' := by
  unfold callTimeout at hs
  dsimp only at hs
  split at hs
  · cases hs
  · next hal =>
    have halive : (w.st id).life = .alive := by simpa using hal
    have hS := h.1
    have hc := hS.cont id
    have ho := h.2.2.2.1 id
    unfold contTy at hc
    unfold outcomeOk at ho
    split at hs
    · next dst k hph =>
      cases hs
      rw [hph] at hc ho
      have hW := detach_inv I w dst id (w.st id).waitId h
      have hrest := detachHost_rest (w.st dst) id (w.st id).waitId
      have hl1 : ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id).life =
          .alive := by
        by_cases hid : id = dst
        · rw [setActor_at w dst id _ hid, hrest.2.1, ← hid]
          exact halive
        · rw [setActor_other w dst id _ hid]
          exact halive
      have hk : ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id).typestate =
          k.toState := by
        by_cases hid : id = dst
        · rw [setActor_at w dst id _ hid, hrest.1, ← hid]
          exact hc
        · rw [setActor_other w dst id _ hid]
          exact hc
      have hfree : notParked ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st
          id).phase := by
        by_cases hid : id = dst
        · rw [setActor_at w dst id _ hid]
          apply detach_free
          rw [← hid, hph]
          trivial
        · rw [setActor_other w dst id _ hid, hph]
          trivial
      exact inv_finish I _ id
        ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id) k .timedOut
        hW hl1 hfree hl1 rfl rfl rfl rfl (src_ty I id k (hk.trans hc.symm) ho.1)
        (by rw [contAt_select_to]; exact ho.2) rfl
    · next dst k hph =>
      cases hs
      rw [hph] at hc ho
      have hR := refund_call_roster w id dst
      have hf := fun i => refundCall_fields w id dst i
      have hSR : SemInv I (refundParkedCall w id dst) := by
        apply sem_shape I w _ hS hR (fun i => (hf i).2.1) (fun i => (hf i).2.2.1) (fun i => (hf i).1)
        intro i hi
        rw [(hf i).2.2.2]
        split
        · next hd =>
          subst hd
          rw [hS.offEmpty _ hi]
          rfl
        · rfl
      have hs1 : srcOk I id ((refundParkedCall w id dst).st id) k :=
        src_ty I id k (hf id).2.2.1 ho.1
      obtain ⟨tr, hmem, htm, hl, hfld, hk⟩ := hs1
      have hprog : effectsOk I.desc (tname id) (contAt (selectCall k .notAdmitted))
          (selectCall k .notAdmitted).rest = true := by
        rw [contAt_select_na]
        simpa [selectCall] using (ho.2 rfl).1
      rcases finish_preds I.desc id ((refundParkedCall w id dst).st id) k .notAdmitted hprog with
        ⟨htyF, hlifeF, hpkF, hcont, hprogF, hwait, hfreeF⟩
      have hl1 : landsAt tr (selectCall k .notAdmitted).toState := by
        simpa [selectCall] using
          lands_pick_field tr k.toState k.toNotAdmitted (by rw [hk]; exact hl) (Or.inl hfld.1)
      have hlife : ((refundParkedCall w id dst).st id).life = .alive := (hf id).2.1.trans halive
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact sem_enter I _ id (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted) tr
          ((refundParkedCall w id dst).st id).typestate (selectCall k .notAdmitted).toState hSR rfl htyF
          hlifeF htm hmem hl hl1 hcont hprogF hwait
          (idleOff_life (hlifeF.trans hlife)) hpkF (by rw [hR]; exact hS.rostered id halive)
      · exact mail_not_admitted w id dst _ h.2.1 ⟨k, hph⟩ hfreeF (hlifeF.trans (hf id).2.1) hpkF
      · exact open_set _ id _ (open_shape w _ h.2.2.1 (fun i hi => by rw [hR]; exact hi) (fun i => (hf i).2.1))
          (by rw [hR]; exact hS.rostered id halive)
      · exact outcome_set I _ id _
          (outcome_shape I w _ h.2.2.2.1 (fun i => (hf i).1) (fun i => (hf i).2.2.1))
          (outcome_finish I id _ k .notAdmitted ⟨tr, hmem, htm, hl, hfld, hk⟩)
      · exact ParentForest.setActor
          (ParentForest.parents h.forest (fun i => refundCall_parent w id dst i) hR)
          (finishCall_parent _ _ _)
      · have hq := fun i => refund_queues w id dst i
        have hsub : ∀ host p, p ∈ ((refundParkedCall w id dst).st host).parked →
            p ∈ (w.st host).parked := by
          intro host p hp
          by_cases hd : host = dst
          · rw [hd] at hp ⊢
            rw [(hf dst).2.2.2, ite_eq_left rfl] at hp
            exact (List.mem_filter.mp hp).1
          · rw [(hf host).2.2.2, ite_eq_right hd] at hp
            exact hp
        have hSeal : SealInv (refundParkedCall w id dst) := by
          refine ⟨parkedLive_sub h.seal.liveParked (fun i => (hf i).2.1) hsub, ?_, ?_, ?_, ?_, ?_⟩
          · rcases h.seal.quiet with hcr0 | hquiet
            · exact Or.inl ((hq id).2.2.trans hcr0)
            · refine Or.inr fun i hna => ?_
              rcases hquiet i (fun ha => hna (((hf i).2.1).trans ha)) with ⟨hb, hpk0⟩
              refine ⟨by rw [(hq i).1]; exact hb, ?_⟩
              by_cases hid : i = dst
              · rw [hid, (hf dst).2.2.2, ite_eq_left rfl]
                rw [hid] at hpk0
                rw [hpk0]
                rfl
              · rw [(hf i).2.2.2, ite_eq_right hid]
                exact hpk0
          · exact childless_stable h.seal.childless (hq id).2.2 (fun i => (hf i).2.1)
              (fun i => refundCall_parent w id dst i)
          · exact chain_stable h.seal.chain (hq id).2.2 hR (fun i => (hf i).2.1)
              (fun i => (hq i).1) (fun i => (hq i).2.1) (fun i => refundCall_parent w id dst i)
          · exact parkedFrom_sub h.seal.parkedFrom hsub
          · exact hostedMail_same h.seal.hostedMail hR (fun i => (hq i).1) (fun i => (hq i).2.1)
        have hfin : (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted).box =
            ((refundParkedCall w id dst).st id).box ∧
            (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted).prio =
              ((refundParkedCall w id dst).st id).prio ∧
            (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted).parent =
              ((refundParkedCall w id dst).st id).parent := by
          unfold finishCall proceed
          split <;> simp
        exact seal_set_keep hSeal hlifeF hfin.1 hfin.2.1 hpkF hfin.2.2
    · next k hph =>
      cases hs
      rw [hph] at hc ho
      exact inv_pick I w id (w.st id) k k.onTimeout k.toTimeout h halive (by rw [hph]; trivial) halive
        rfl rfl rfl rfl ho.1 (Or.inr (Or.inr (Or.inl rfl))) (by rw [contAt_pick]; exact ho.2) rfl
    · cases hs

theorem ingress_inv (I : Impl) (w w' : World) (dst : InstId) (label : String) (h : Inv I w)
    (hs : receiveIngress I w dst label = some w') : Inv I w' := by
  obtain ⟨hlive, _, _, _, heq⟩ := ingress_open I w w' dst label hs
  rw [heq]
  exact inv_frame I w _ h (same_actor w dst _ rfl rfl rfl rfl rfl)
    (seal_grow_box w h.seal h.forest dst
      { chargeSender (w.st dst) (tname dst) with
        box := (w.st dst).box ++
          [{ label := label, sender := dst, callFrom := none, reliable := true,
             mid := (w.st dst).nextMid }],
        nextMid := (w.st dst).nextMid + 1 }
      { label := label, sender := dst, callFrom := none, reliable := true,
        mid := (w.st dst).nextMid }
      hlive (by simp [chargeSender, bumpToken]) (by simp [chargeSender, bumpToken])
      (by simp [chargeSender, bumpToken]) (by simp [chargeSender, bumpToken])
      (by simp [chargeSender, bumpToken]) (Or.inr hlive)
      (h.2.2.1 dst (by rw [hlive]; intro hna; cases hna)))

theorem step_inv (I : Impl) (hL : LocalOk I) (w w' : World) (hstep : Step I w w')
    (h : Inv I w) : Inv I w' := by
  obtain ⟨a, ha⟩ := hstep
  have hs := (apply_step I a w w' ha).2
  cases a with
  | recvBulk id => exact receive_bulk_inv I hL w w' id h hs
  | recvPrio id => exact receive_prio_inv I hL w w' id h hs
  | exec id => exact exec_head_inv I w w' id h hs
  | finish id => exact finish_inv I w w' id h hs
  | spawn template => exact spawn_inv I w w' template h hs
  | ingress dst label => exact ingress_inv I w w' dst label h hs
  | callTimeout id => exact callTimeout_inv I w w' id h hs
  | stutter =>
    cases stutter_unchanged I w w' ha
    exact h

theorem init_roster (I : Impl) (N : Nat) : (initWorld I N).roster = coreRoster I.desc := by
  have hf : ∀ (ids : List InstId) (w : World),
      (ids.foldl (fun w id => readCells I.desc w id) w).roster = w.roster := by
    intro ids
    induction ids with
    | nil => intro w; rfl
    | cons i is ih =>
      intro w
      simp only [List.foldl_cons]
      rw [ih, cellsRoster]
  unfold initWorld
  exact hf _ _

theorem open_init (I : Impl) (N : Nat) : OpenSlots (initWorld I N) := by
  intro id hl
  rw [init_roster]
  rw [init_base_st] at hl
  by_cases hc : (coreRoster I.desc).contains id = true
  · simpa using hc
  · rw [ite_eq_right hc] at hl
    exact absurd rfl hl

theorem outcome_init (I : Impl) (N : Nat) : OutcomeInv I (initWorld I N) := by
  intro id
  unfold outcomeOk
  rw [init_phase]
  trivial

theorem init_parent (I : Impl) (N : Nat) (id : InstId) :
    ((initWorld I N).st id).parent = none := by
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem forest_init (I : Impl) (N : Nat) : ParentForest (initWorld I N) where
  wf := ⟨fun id => Acc.intro id fun _ h => by
    unfold ParentEdge at h
    rw [init_parent] at h
    cases h.1⟩
  off := fun id _ => init_parent I N id
  hosted := fun id p hp => by
    rw [init_parent] at hp
    cases hp

theorem inv_init (I : Impl) (N : Nat) (hL : LocalOk I) : Inv I (initWorld I N) :=
  ⟨semInv_init I N hL, mail_init I N, open_init I N, outcome_init I N, forest_init I N,
    seal_init I N⟩

theorem inv_reachable (I : Impl) (N : Nat) (w : World) (hL : LocalOk I)
    (hR : Reachable I N w) : Inv I w := by
  induction hR with
  | init => exact inv_init I N hL
  | step _ _ _ _ ha ih => exact step_inv I hL _ _ ⟨_, ha⟩ ih

/-- Reachable worlds satisfy the semantic invariant. A scheduler step is proved
for the whole invariant, and this is that result's first field. -/
theorem sem_reachable (I : Impl) (N : Nat) (w : World) (hL : LocalOk I)
    (hR : Reachable I N w) : SemInv I w :=
  (inv_reachable I N w hL hR).1

theorem effect_beq (a b : EffectKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem kind_beq (a b : EdgeKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem hasEdge_mem (D : Description) (src ss dst : String) (effect : EffectKind) (kind : EdgeKind)
    (label : String) (h : hasEdge D src ss dst effect kind label = true) :
    ∃ e, e ∈ D.edges ∧ e.src = src ∧ e.srcState = ss ∧ e.dst = dst ∧
      e.effect = effect ∧ e.kind = kind ∧ e.label = label := by
  simp [hasEdge, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, hf⟩ := h
  obtain ⟨hf, hlab⟩ := hf
  obtain ⟨hf, hkind⟩ := hf
  obtain ⟨hf, heff⟩ := hf
  obtain ⟨hf, hdst⟩ := hf
  obtain ⟨hsrc, hss⟩ := hf
  exact ⟨e, he, hsrc, hss, hdst, (effect_beq _ _).mp heff, (kind_beq _ _).mp hkind,
    by simpa [beq_iff_eq] using hlab⟩

/-- A parked actor is waiting on a blocking edge of the description. -/
theorem described_park (I : Impl) (w : World) (h : Inv I w) (id dst : InstId) (isCall : Bool)
    (k : Cont) (hph : (w.st id).phase = .parked dst isCall k) :
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧
      e.effect = (if isCall then EffectKind.call else EffectKind.send) ∧ e.label = label := by
  have hw := h.1.waited id
  simp [waitEdge, hph] at hw
  obtain ⟨label, hedge⟩ := hw
  obtain ⟨e, he, hsrc, hss, hdst, heff, hkind, hlab⟩ :=
    hasEdge_mem I.desc (tname id) (w.st id).typestate (tname dst)
      (if isCall then EffectKind.call else EffectKind.send) .blocking label hedge
  exact ⟨label, e, he, hsrc, hss, hdst, hkind, heff, hlab⟩

/-- An actor awaiting a reply is waiting on a blocking call edge. -/
theorem described_reply (I : Impl) (w : World) (h : Inv I w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .awaitReply dst k) :
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧ e.effect = EffectKind.call ∧ e.label = label := by
  have hw := h.1.waited id
  simp [waitEdge, hph] at hw
  obtain ⟨label, hedge⟩ := hw
  obtain ⟨e, he, hsrc, hss, hdst, heff, hkind, hlab⟩ :=
    hasEdge_mem I.desc (tname id) (w.st id).typestate (tname dst) .call .blocking label hedge
  exact ⟨label, e, he, hsrc, hss, hdst, hkind, heff, hlab⟩

end Deadlock
