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

theorem route_tname (w : World) (D : Description) (sender : InstId) (dst : String) (slot : Nat)
    (id : InstId) (h : route w D sender dst slot = some id) : tname id = dst := by
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
      split at h
      · split at h
        · exact (findLive_spec w dst slot id h).1
        · cases h
      · split at h
        · cases h
        · exact (findLive_spec w dst _ id h).1

theorem resolve_tname (D : Description) (w : World) (sender : InstId) (dst : String) (slot : Nat)
    (id : InstId) (h : resolveId D w sender dst slot = some id) : tname id = dst := by
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
      split at h
      · split at h
        · split at h
          · cases h
            exact (findLive_spec w dst slot _ (by assumption)).1
          · cases h
            rfl
        · cases h
      · split at h
        · cases h
        · split at h
          · cases h
            exact (findLive_spec w dst _ _ (by assumption)).1
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
  SemInv I w ∧ MailInv w ∧ OpenSlots w ∧ OutcomeInv I w

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

theorem same_refl (w : World) : Same w w :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_trans {w1 w2 w3 : World} (h1 : Same w1 w2) (h2 : Same w2 w3) : Same w1 w3 :=
  ⟨h2.roster.trans h1.roster, fun i => (h2.life i).trans (h1.life i),
    fun i => (h2.ty i).trans (h1.ty i), fun i => (h2.phase i).trans (h1.phase i),
    fun i => (h2.parked i).trans (h1.parked i)⟩

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

theorem inv_same (I : Impl) (w w' : World) (h : Inv I w) (hs : Same w w') : Inv I w' :=
  ⟨sem_shape I w w' h.1 hs.roster hs.life hs.ty hs.phase (fun i _ => hs.parked i),
    mail_shape w w' h.2.1 hs.life hs.phase hs.parked,
    open_shape w w' h.2.2.1 (fun i hi => by rw [hs.roster]; exact hi) hs.life,
    outcome_shape I w w' h.2.2.2 hs.phase hs.ty⟩

theorem same_actor (w : World) (id : InstId) (a : Actor) (hl : a.life = (w.st id).life)
    (ht : a.typestate = (w.st id).typestate) (hp : a.phase = (w.st id).phase)
    (hk : a.parked = (w.st id).parked) : Same w (setActor w id a) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> intro i <;> by_cases hi : i = id <;>
    simp [hi, setActor_self, setActor_other w id i a, hl, ht, hp, hk]

theorem same_cells (D : Description) (w : World) (id : InstId) : Same w (readCells D w id) :=
  ⟨cellsRoster D w id, fun i => by rw [cellsSt], fun i => by rw [cellsSt], fun i => by rw [cellsSt],
    fun i => by rw [cellsSt]⟩

theorem same_note (w : World) (sender : InstId) (dst : String) : Same w (noteStale w sender dst) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_setCell (w : World) (dst label : String) (c : Cell) : Same w (setCell w dst label c) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_credit (w : World) (tmpl : String) (sender : InstId) : Same w (creditSender w tmpl sender) :=
  ⟨rfl, fun i => (credit_rest w tmpl sender i).2.1, fun i => (credit_rest w tmpl sender i).2.2.2.2.2,
    fun i => (credit_rest w tmpl sender i).1, fun i => (credit_rest w tmpl sender i).2.2.2.2.1⟩

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

theorem same_arm (w : World) (id : InstId) : Same w (armTombstone w id) :=
  same_actor w id _ rfl rfl rfl rfl

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
    (hcont : contTy a) (hprog : programOk I.desc id a) (hwait : waitEdge I.desc id a)
    (hout : outcomeOk I id a) : Inv I (setActor w id a) :=
  ⟨sem_set I w id a h.1 hty (hlife.trans halive.symm) hcont hprog hwait (idleOff_life hlife)
      (Or.inl hlist),
    mail_set_free w id a h.2.1 hfree hnew hlist (hlife.trans halive.symm),
    open_set w id a h.2.2.1 (h.1.rostered id halive),
    outcome_set I w id a h.2.2.2 hout⟩

/-- A live actor that is not parked resumes a checked continuation whose
`toState` is the typestate it already holds. -/
theorem inv_proceed (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (h : Inv I w)
    (halive : (w.st id).life = .alive) (hfree : notParked (w.st id).phase)
    (hlife : a.life = .alive) (hty : a.typestate = (w.st id).typestate)
    (hlist : a.parked = (w.st id).parked) (hk : (w.st id).typestate = k.toState)
    (hprog : effectsOk I.desc (tname id) (contAt k) k.rest = true) (hs : srcOk I id a k) :
    Inv I (setActor w id (proceed a k)) := by
  have hp := proceed_ok I.desc id a k (hty.trans hk) hprog
  exact inv_set_free I w id (proceed a k) h halive hfree ((proceed_keeps_life a k).trans hlife)
    (hp.1.trans hty) (proceed_not_parked a k) ((proceed_keeps_parked a k).trans hlist) hp.2.2.1
    hp.2.2.2.1 hp.2.2.2.2 (outcome_proceed I id a k hs)

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
    (hlist : a.parked = (w.st id).parked) (hmem : tr ∈ I.transitions) (htm : tr.template = tname id)
    (hs0 : landsAt tr (w.st id).typestate) (hs1 : landsAt tr k.toState) (hf : fieldMatch tr k)
    (hprog : effectsOk I.desc (tname id) (contAt k) k.rest = true) :
    Inv I (setActor w id (proceed a k)) := by
  rcases proceed_any I.desc id a k hprog with ⟨htyP, hlifeP, hcont, hprogP, hwait, hfreeP, hpkP⟩
  have hS := sem_enter I w id (proceed a k) tr (w.st id).typestate k.toState h.1 rfl htyP
    (hlifeP.trans (hlife.trans halive.symm)) htm hmem hs0 hs1 hcont hprogP hwait
    (idleOff_life (hlifeP.trans hlife)) (hpkP.trans hlist) (h.1.rostered id halive)
  refine ⟨hS,
    mail_set_free w id (proceed a k) h.2.1 hfree hfreeP (hpkP.trans hlist) (hlifeP.trans (hlife.trans halive.symm)),
    open_set w id (proceed a k) h.2.2.1 (h.1.rostered id halive), ?_⟩
  apply outcome_set I w id (proceed a k) h.2.2.2
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
    (hlist : a.parked = (w.st id).parked) (hs : srcOk I id (w.st id) k)
    (hspec : specific = k.toNotAdmitted ∨ specific = k.toTimedOut ∨ specific = k.toTimeout ∨
      specific = k.toFull ∨ specific = k.toGone)
    (hprog : effectsOk I.desc (tname id)
        (contAt { k with rest := rest, toState := pickState k.toState specific }) rest = true) :
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
  exact inv_enter I w id a _ tr h halive hfree hlife hty hlist hmem htm hl
    (lands_pick_field tr k.toState specific hlk hs') hfield hprog'

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
    (hlist : a.parked = (w.st id).parked) (hs : srcOk I id a k)
    (hprog : effectsOk I.desc (tname id) (contAt (selectCall k r)) (selectCall k r).rest = true) :
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
    outcome_set I w id _ h.2.2.2 (outcome_finish I id a k r ⟨tr, hmem, htm, hl, hf, hk⟩)⟩

theorem enqueue_roster (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).roster = w.roster := by
  unfold enqueueOrPark
  dsimp only
  cases isCall <;> split <;> (try split) <;> (try split) <;> rfl

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

/-- The mailbox write of a send or call, given the running sender's `SemInv` result. -/
theorem enqueue_inv (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (h : Inv I w) (hS : SemInv I (enqueueOrPark w I.desc sender dst msg isCall k))
    (hfree : notParked (w.st sender).phase) (hlive : (w.st sender).life = .alive)
    (hs : srcOk I sender (w.st sender) k)
    (hcall : isCall = true →
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).notAdmitted) k.onNotAdmitted = true ∧
      effectsOk I.desc (tname sender) (focus (contAt k) (contAt k).timedOut) k.onTimedOut = true) :
    Inv I (enqueueOrPark w I.desc sender dst msg isCall k) :=
  ⟨hS, enqueue_mail w I.desc sender dst msg isCall k h.2.1 hfree hlive,
    open_shape w _ h.2.2.1 (fun i hi => by rw [enqueue_roster]; exact hi)
      (enqueue_life w I.desc sender dst msg isCall k),
    enqueue_outcome I I.desc w sender dst msg isCall k h.2.2.2 hs hcall⟩

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
    rcases h with (hh | hh) | ⟨ha, _⟩
    · rw [crash_go (Or.inr hh)]
      exact Or.inr rfl
    · rw [crash_stay (by rw [hh]; intro he; cases he) (by rw [hh]; intro he; cases he)]
      exact Or.inr hh
    · rw [crash_go (Or.inl ha)]
      exact Or.inr rfl
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
  refine ⟨crash_sem I w hS, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
      by_cases hgo : (w.st s).life = .alive ∨ (w.st s).life = .shuttingDown
      · rw [crash_go hgo] at hph
        cases hph
      · rw [crash_stay (fun he => hgo (Or.inl he)) (fun he => hgo (Or.inr he))] at hph
        exact hgo (Or.inl (hbusy s dst c k hph))
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
      by_cases hgo : (w.st i).life = .alive ∨ (w.st i).life = .shuttingDown
      · rw [crash_go hgo]
        simp [outcomeOk]
      · rw [crash_stay (fun he => hgo (Or.inl he)) (fun he => hgo (Or.inr he))]
        exact h.2.2.2 i
    · rw [crash_off w i hm]
      exact h.2.2.2 i

theorem offerPrio_inv (I : Impl) (D : Description) (w : World) (host : InstId) (msg : Msg)
    (h : Inv I w) : Inv I (offerPrio D w host msg) := by
  unfold offerPrio
  dsimp only
  split
  · exact crash_inv I w h
  · exact inv_same I w _ h (same_actor w host _ rfl rfl rfl rfl)

theorem tryWake_inv (I : Impl) (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (h : Inv I w) : Inv I (tryWake D w dstId label writer) := by
  unfold tryWake
  dsimp only
  split
  · exact h
  · exact offerPrio_inv I D w dstId _ h

theorem wakes_inv (I : Impl) (D : Description) (w : World) (ids : List InstId) (label : String)
    (writer : InstId) (h : Inv I w) :
    Inv I (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih _ (tryWake_inv I D w i label writer h)

theorem wakeReaders_inv (I : Impl) (D : Description) (w : World) (dst label : String) (writer : InstId)
    (h : Inv I w) : Inv I (wakeReaders D w dst label writer) :=
  wakes_inv I D w _ label writer h

theorem enqueueTombstone_inv (I : Impl) (D : Description) (w : World) (child : InstId) (h : Inv I w) :
    Inv I (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  split
  · exact h
  · dsimp only
    split
    · exact h
    · split
      · exact crash_inv I w h
      · exact offerPrio_inv I D w _ _ h

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
    rcases hhalt with h | h <;> rw [h] <;> intro h' <;> cases h'
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

theorem releaseOutbound_inv (I : Impl) (w : World) (dead : InstId) (h : Inv I w)
    (hfree : notParked (w.st dead).phase) : Inv I (releaseOutbound w dead) := by
  have hf := releaseOutbound_fields w dead
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · exact outcome_shape I w _ h.2.2.2 (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.1)

/-- The seal of a live or shutting-down actor, after its outbound entries are gone. -/
theorem release_inv (I : Impl) (w w4 : World) (id : InstId) (h : Inv I w)
    (hgo : (w.st id).life = .alive ∨ (w.st id).life = .shuttingDown)
    (hr : w4.roster = w.roster) (hl : ∀ i, (w4.st i).life = (w.st i).life)
    (ht : ∀ i, (w4.st i).typestate = (w.st i).typestate) (hp : ∀ i, (w4.st i).phase = (w.st i).phase)
    (hk : ∀ i, i ≠ id → (w4.st i).parked = (w.st i).parked.filter fun p => p.sender != id) :
    Inv I (releaseParked (setActor w4 id
      { (w4.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] })
      id (w.st id).parked) := by
  have hS := h.1
  have hM := h.2.1
  have hmem : id ∈ w.roster :=
    h.2.2.1 id (by rcases hgo with hg | hg <;> rw [hg] <;> intro he <;> cases he)
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
  have hdt : dead.typestate = (w4.st id).typestate := by rw [← hdead]
  have hS4 : SemInv I w4 := sem_shape I w w4 hS hr hl ht hp hoff
  have hS5 : SemInv I (setActor w4 id dead) :=
    sem_seal I w4 id dead hS4 hdt (Or.inr hdl) hdp (by rw [hr]; exact hmem)
  have hst5 : ∀ i, i ≠ id → (setActor w4 id dead).st i = w4.st i :=
    fun i hi => setActor_other w4 id i dead hi
  have hid5 : (setActor w4 id dead).st id = dead := setActor_self w4 id dead
  rw [release_fold_eq]
  have hidF : (releaseFold id (w.st id).parked (setActor w4 id dead)).st id = dead :=
    (release_spares_id id _ _).trans hid5
  refine ⟨release_sem I _ id _ hS5, ?_, ?_, ?_⟩
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
        exact Or.inr hdl
      · rw [hst5 i hi, hl i]
        exact hh
    · intro i mb c k hph
      have ha := busy_alive I w hS i (by rw [hph]; intro he; cases he) (by rw [hph]; intro he; cases he)
      rw [ha]
      intro hh
      rcases hh with hh | hh <;> cases hh
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
      exact outcome_congr I i (hp i) (ht i) (h.2.2.2 i)

theorem releaseWorld_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w)
    (hgo : (w.st id).life = .alive ∨ (w.st id).life = .shuttingDown) :
    Inv I (releaseWorld D w id (w.st id)) := by
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
  apply release_inv I w (releaseOutbound w3 id) id h hgo ((hf id).1.trans hs3.roster)
    (fun i => (hf i).2.1.trans (hs3.life i)) (fun i => (hf i).2.2.1.trans (hs3.ty i))
    (fun i => (hf i).2.2.2.1.trans (hs3.phase i))
  intro i hi
  rw [(hf i).2.2.2.2, hs3.parked i]
  by_cases hm : i ∈ w3.roster
  · rw [ite_eq_left ⟨hm, hi⟩]
  · rw [ite_eq_right (fun hc => hm hc.1)]
    rw [hs3.roster] at hm
    rw [h.1.offEmpty i hm]
    rfl

theorem markShutdown_inv (I : Impl) (w : World) (id : InstId) (h : Inv I w) :
    Inv I (markShutdown w id) := by
  unfold markShutdown
  split
  · next halive =>
    have ha : (w.st id).life = .alive := by simpa using halive
    have hmem := h.1.rostered id ha
    have h1 : Inv I (setActor w id { (w.st id) with life := .shuttingDown, phase := .idle }) :=
      ⟨sem_seal I w id _ h.1 rfl (Or.inl rfl) rfl hmem,
        mail_halt w id _ h.2.1 ha (Or.inl rfl) trivial rfl,
        open_set w id _ h.2.2.1 hmem,
        outcome_set I w id _ h.2.2.2 (by simp [outcomeOk])⟩
    exact releaseOutbound_inv I _ id h1 (by rw [setActor_self]; trivial)
  · exact h

theorem shutdownActor_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w) :
    Inv I (shutdownActor D w id) := by
  unfold shutdownActor
  dsimp only
  split
  · exact inv_same I _ _ (markShutdown_inv I w id h) (same_arm _ id)
  · exact markShutdown_inv I w id h

theorem sealActor_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w)
    (hgo : (w.st id).life = .alive ∨ (w.st id).life = .shuttingDown) :
    Inv I (sealActor D w id (w.st id)) := by
  unfold sealActor
  dsimp only
  split
  · exact enqueueTombstone_inv I D _ id (releaseWorld_inv I D w id h hgo)
  · exact releaseWorld_inv I D w id h hgo

theorem sealBranch_inv (I : Impl) (fuel : Nat) (D : Description) (w : World) (id : InstId)
    (h : Inv I w) : Inv I (sealBranch fuel D w id) := by
  induction fuel generalizing w id with
  | zero => exact h
  | succ n ih =>
    have hfold : ∀ (ids : List InstId) (acc : World), Inv I acc →
        Inv I (ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc) := by
      intro ids
      induction ids with
      | nil => intro acc ha; exact ha
      | cons c cs ihc =>
        intro acc ha
        simp only [List.foldl_cons]
        apply ihc
        split
        · exact ih _ _ ha
        · exact ha
    have hs := hfold w.roster w h
    unfold sealBranch
    dsimp only
    split
    · next hgo =>
      apply releaseWorld_inv I D _ id hs
      simpa [Bool.or_eq_true, beq_iff_eq] using hgo
    · exact hs

theorem dropDescendants_inv (I : Impl) (D : Description) (w : World) (id : InstId) (h : Inv I w) :
    Inv I (dropDescendants D w id) := by
  unfold dropDescendants
  have hfold : ∀ (ids : List InstId) (acc : World), Inv I acc →
      Inv I (ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch w.roster.length D acc child else acc) acc) := by
    intro ids
    induction ids with
    | nil => intro acc ha; exact ha
    | cons c cs ihc =>
      intro acc ha
      simp only [List.foldl_cons]
      apply ihc
      split
      · exact sealBranch_inv I _ D _ _ ha
      · exact ha
  exact hfold w.roster w h

theorem terminateStage_inv (I : Impl) (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : Inv I w) : Inv I (terminateStage D w id a) :=
  shutdownActor_inv I D _ id (dropDescendants_inv I D w id h)

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
      · exact shutdownActor_inv I D _ c (dropDescendants_inv I D _ c ha)
      · exact ha
  exact hfold w.roster w h

theorem run_facts (I : Impl) (w : World) (id : InstId) (k : Cont) (h : Inv I w)
    (hph : (w.st id).phase = .run k) :
    (w.st id).typestate = k.toState ∧ effectsOk I.desc (tname id) (contAt k) k.rest = true ∧
      srcOk I id (w.st id) k ∧ notParked (w.st id).phase := by
  have hc := h.1.cont id
  have hp := h.1.prog id
  have ho := h.2.2.2 id
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
  inv_same I _ _ h ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

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
      (by rw [hst]; exact hfree) ha (by rw [hst]) (by rw [hst]) (by rw [hst]; exact hty)
      (by rw [hk']; exact hprog) hsrc
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
        have ho := h.2.2.2 caller
        unfold programOk at hp
        unfold outcomeOk at ho
        rw [hcph] at hp ho
        have h1 := inv_finish I w caller (w.st caller) ck .reply h hcalive (by rw [hcph]; trivial)
          hcalive rfl rfl ho.1 (by simpa [selectCall] using hp)
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
    inv_proceed I (setCell w dst label c) id _ k (inv_same I w _ h (same_setCell w dst label c)) ha
      hfree ha rfl rfl hty hprog (src_ty I id k (by simp [setCell]) hs)
  split
  · exact h1
  · exact wakeReaders_inv I I.desc _ dst label id h1

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
        rcases hh with hh | hh <;> cases hh
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

/-- Installing one fresh idle peer. -/
theorem place_inv (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnext : ∀ v : World, (next v).st = v.st ∧ (next v).roster = v.roster) (h : Inv I w) :
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
  refine ⟨hS, mail_copy _ _ hM2 (fun i => cellsSt _ _ _ i), ?_, ?_⟩
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
      exact h.2.2.2 i

theorem spawn_inv (I : Impl) (w w' : World) (template : String) (h : Inv I w)
    (hs : spawn I w template = some w') : Inv I w' := by
  unfold spawn at hs
  split at hs
  · cases hs
  · split at hs
    · split at hs
      · cases hs
        exact place_inv I w _ _ _ _ _ (fun _ => ⟨rfl, rfl⟩) h
      · split at hs
        · cases hs
          exact place_inv I w _ _ _ _ _ (fun _ => ⟨rfl, rfl⟩) h
        · cases hs
          exact place_inv I w _ _ _ _ _ (fun _ => ⟨rfl, rfl⟩) h
    · cases hs

theorem admit_inv (I : Impl) (w : World) (child : String) (k : Nat) (initial : String)
    (parent : Option InstId) (h : Inv I w) :
    Inv I (admitBorn I w (InstId.peer child k (maxGen w child k))
      { bornActor I.desc w child k initial with parent := parent }) :=
  place_inv I w child k initial parent (fun v => v) (fun _ => ⟨rfl, rfl⟩) h

theorem spawnChild_inv (I : Impl) (w w' : World) (parent : InstId) (child : String) (h : Inv I w)
    (hs : spawnChild I w parent child = some w') : Inv I w' := by
  unfold spawnChild at hs
  split at hs
  · cases hs
  · next t _ =>
    split at hs
    · split at hs
      · split at hs
        · split at hs
          · cases hs
            exact admit_inv I w child _ t.initial _ h
          · cases hs
            exact h
        · cases hs
      · split at hs
        · split at hs
          · cases hs
            exact h
          · cases hs
            exact admit_inv I w child _ t.initial _ h
        · cases hs
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
      (by trivial) (by trivial) (by trivial) (by trivial)
  | cons e es =>
    have hk' : (afterHead k).rest = es := after_rest k e es hk
    have hpe : effectsOk I.desc (tname id) (contAt k) (e :: es) = true := by rw [← hk]; exact hprog
    have htail : effectsOk I.desc (tname id) (contAt (afterHead k)) (afterHead k).rest = true := by
      rw [hk']
      exact head_rest _ _ _ _ _ hpe
    cases e with
    | send d l n =>
      have hs := head_send I.desc (tname id) d l (contAt k) n es hpe
      cases hr : route w I.desc id d n with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact inv_note I w id d id _
          (inv_proceed I w id (w.st id) (afterHead k) h ha hfree ha rfl rfl hty htail hsrc)
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact enqueue_inv I w id dstId _ false (afterHead k) h
          (enqueue_sem I w id dstId _ false (afterHead k) h.1 hty htail
            ⟨l, by rw [route_tname w I.desc id d n dstId hr, hty]; exact hs.1⟩ ha
            (fun hc => absurd hc Bool.false_ne_true) (fun hc => absurd hc Bool.false_ne_true))
          hfree ha hsrc (fun hc => absurd hc Bool.false_ne_true)
    | trySend d l n f g =>
      have hs := head_try I.desc (tname id) d l (contAt k) n f g es hpe
      have hgone : Inv I (setActor w id (proceed (w.st id) { afterHead k with
          rest := g, toState := pickState (afterHead k).toState (afterHead k).toGone })) :=
        inv_pick I w id (w.st id) (afterHead k) g (afterHead k).toGone h ha hfree ha rfl rfl hsrc
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by rw [contAt_pick]; exact hs.2.1)
      have hfull : Inv I (setActor w id (proceed (w.st id) { afterHead k with
          rest := f, toState := pickState (afterHead k).toState (afterHead k).toFull })) :=
        inv_pick I w id (w.st id) (afterHead k) f (afterHead k).toFull h ha hfree ha rfl rfl hsrc
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by rw [contAt_pick]; exact hs.1)
      cases hr : route w I.desc id d n with
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
            hfree ha hsrc (fun hc => absurd hc Bool.false_ne_true)
        · split
          · exact hfull
          · exact hgone
    | call d l n na to =>
      have hs := head_call I.desc (tname id) d l (contAt k) n na to es hpe
      have hwait := src_lists I id (w.st id) (afterHead k) na to (afterHead k).onTimeout hsrc
      cases hr : resolveId I.desc w id d n with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact inv_note I w id d id _
          (inv_finish I w id (issueCall (w.st id)) { afterHead k with onNotAdmitted := na, onTimedOut := to }
            .notAdmitted h ha hfree ha rfl rfl (src_ty I id _ (by simp [issueCall]) hwait)
            (by rw [contAt_select_na]; exact hs.2.1))
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact enqueue_inv I w id dstId _ true { afterHead k with onNotAdmitted := na, onTimedOut := to } h
          (enqueue_sem_src I w id dstId _ true { afterHead k with onNotAdmitted := na, onTimedOut := to }
            h.1 hwait htail ⟨l, by rw [resolve_tname I.desc w id d n dstId hr, hty]; exact hs.1⟩ ha
            (fun _ _ => hs.2.1))
          hfree ha hwait (fun _ => ⟨hs.2.1, hs.2.2.1⟩)
    | reply =>
      simp only [execRun, hgo, hk, ite_true]
      exact reply_inv I w id k es h hph hk ha hty (head_rest _ _ _ _ _ hpe) hsrc0
    | selfSchedule label =>
      simp only [execRun, hgo, hk, ite_true]
      split
      · exact inv_proceed I w id (w.st id) (afterHead k) h ha hfree ha rfl rfl hty htail hsrc
      · split
        · exact inv_proceed I w id _ (afterHead k) h ha hfree (by exact ha) (by rfl) (by rfl) hty htail
            (src_ty I id (afterHead k) rfl hsrc)
        · exact crash_inv I w h
    | cell dst label value =>
      simp only [execRun, hgo, hk, ite_true]
      exact cell_step_inv I w id (afterHead k) dst label _ _ h ha hfree hty htail hsrc
    | internal =>
      simp only [execRun, hgo, hk, ite_true]
      exact inv_set_free I w id _ h ha hfree (by exact ha) (by rfl) (by trivial) (by rfl)
        (by exact hty) (by exact htail) (by trivial) (by exact src_ty I id (afterHead k) rfl hsrc)
    | peer o =>
      have hs := head_peer I.desc (tname id) (contAt k) o es hpe
      simp only [execRun, hgo, hk, ite_true]
      exact inv_set_free I w id _ h ha hfree (by exact ha) (by rfl) (by trivial) (by rfl)
        (by exact hty) (by exact htail) (by trivial)
        (by exact ⟨src_ty I id _ rfl
          (src_lists I id (w.st id) (afterHead k) (afterHead k).onNotAdmitted (afterHead k).onTimedOut o hsrc),
          hs.1⟩)
    | abort =>
      simp only [execRun, hgo, hk, ite_true]
      exact abortChildren_inv I I.desc w id h
    | terminate =>
      have hstep := exec_term_step I w id (w.st id) k ha ⟨es, hk⟩
      generalize execRun I w id (w.st id) k = wR at hstep ⊢
      cases hstep with
      | fall => exact crash_inv I w h
      | crash _ _ _ => exact crash_inv I w h
      | lone _ _ _ _ _ _ _ => exact shutdownActor_inv I I.desc w id h
      | tree _ _ _ _ => exact terminateStage_inv I I.desc w id _ h
      | cascade _ _ _ _ _ _ _ => exact terminateStage_inv I I.desc w id _ h
    | spawn child =>
      cases hsp : spawnChild I w id child with
      | none =>
        simp only [execRun, hgo, hk, hsp, ite_true]
        exact crash_inv I w h
      | some w' =>
        simp only [execRun, hgo, hk, hsp, ite_true]
        have hw' := spawnChild_inv I w w' id child h hsp
        have hst := spawnChild_other_st I w w' id child id hsp (h.1.rostered id ha)
        exact inv_proceed I w' id (w'.st id) (afterHead k) hw' (by rw [hst]; exact ha)
          (by rw [hst]; exact hfree) (by rw [hst]; exact ha) rfl rfl (by rw [hst]; exact hty) htail
          (src_ty I id (afterHead k) (by rw [hst]) hsrc)

theorem exec_head_inv (I : Impl) (w w' : World) (id : InstId) (h : Inv I w)
    (hs : execHead I w id = some w') : Inv I w' := by
  unfold execHead at hs
  dsimp only at hs
  split at hs
  · next hsd =>
    cases hs
    exact sealActor_inv I I.desc w id h (Or.inr (by simpa [beq_iff_eq] using hsd))
  · split at hs
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
    have ho := h.2.2.2 id
    unfold contTy at hc
    unfold programOk at hp
    unfold outcomeOk at ho
    split at hs
    · next k hph =>
      cases hs
      rw [hph] at hc hp ho
      exact inv_proceed I w id (w.st id) k h ha (by rw [hph]; trivial) ha rfl rfl hc hp ho
    · next k hph =>
      cases hs
      rw [hph] at hc hp ho
      exact inv_proceed I w id (w.st id) k h ha (by rw [hph]; trivial) ha rfl rfl hc hp ho.1
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
        b.parked = a.parked → DeliverOk I w id a b (readCells I.desc w id) := by
      intro b hp hl ht hk
      refine ⟨?_, hl, hk, by rw [hp]; trivial, hst, hro, by unfold outcomeOk; rw [hp]; trivial⟩
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
      exact hidle _ rfl rfl rfl rfl
    · split at h
      · split at h
        · cases h
        · cases h
          exact hidle _ rfl rfl rfl rfl
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
          · refine ⟨?_, rfl, rfl, trivial, hst, hro, trivial⟩
            cases id with
            | core r =>
              exact sem_move I _ r _ tr hS1 hL (hfrom _ rfl) rfl (by rw [hst]; exact hlife) hfm.2.1
                hfm.1 trivial trivial trivial (idleOff_now _ rfl) (Or.inr hmem1)
            | peer n k g =>
              exact sem_noncore I _ _ _ hS1 (fun r => peer_ne_core n k g r) trivial trivial trivial
                (idleOff_now _ rfl) hmem1
          · refine ⟨?_, rfl, rfl, trivial, hst, hro, ?_⟩
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
    (hpk : a.parked = (w.st id).parked) : Inv I (setActor w1 id a1) := by
  have hM1 := mail_copy w w1 h.2.1 hd.st
  refine ⟨hd.sem, ?_, ?_, ?_⟩
  · exact mail_set_free w1 id a1 hM1 (by rw [hd.st, hidle]; trivial) hd.free
      (by rw [hd.parked, hd.st, hpk]) (by rw [hd.st]; exact hd.life.trans hlife)
  · exact open_set w1 id a1 (open_shape w w1 h.2.2.1 (fun i hi => by rw [hd.roster]; exact hi)
      (fun i => by rw [hd.st])) (by rw [hd.roster]; exact h.1.rostered id halive)
  · exact outcome_set I w1 id a1 (outcome_shape I w w1 h.2.2.2 (fun i => by rw [hd.st]) (fun i => by rw [hd.st]))
      hd.out

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

/-- One parked entry is admitted after the receiver is installed: the sender is credited,
and a sender still parked on this mailbox resumes. -/
theorem resume_one (I : Impl) (w w1 : World) (id : InstId) (cur : Actor) (p : Parked) (ps : List Parked)
    (who : InstId) (h : Inv I w) (hS : SemInv I (setActor w1 id cur)) (hst : ∀ i, w1.st i = w.st i)
    (hro : w1.roster = w.roster) (hidle : (w.st id).phase = .idle) (halive : (w.st id).life = .alive)
    (hqueue : (w.st id).parked = p :: ps) (hcurPk : cur.parked = ps) (hcurPh : notParked cur.phase)
    (hcurLife : cur.life = (w.st id).life) (hcurOut : outcomeOk I id cur) :
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
    outcome_congr I p.sender hsp hsty (h.2.2.2 _)
  have hstat : (∃ k, (cred.st p.sender).phase = .parked id p.isCall k) ∨
      ((cred.st p.sender).phase = .idle ∨ (cred.st p.sender).phase = .crashed) := by
    rcases hM.fwd id p hmemp with ⟨k, hk⟩ | hh
    · exact Or.inl ⟨k, by rw [hsp]; exact hk⟩
    · right
      rw [hsp]
      exact h.1.idleOff _ (by rcases hh with hh | hh <;> rw [hh] <;> intro he <;> cases he)
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
  refine ⟨hrsem, ?_, ?_, ?_⟩
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
      · exact outcome_congr I i (by rw [hcr.phase, hbo i hii]) (by rw [hcr.ty, hbo i hii]) (h.2.2.2 i)

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
            hd'.free hd'.life hd'.out
    | cons m ms =>
      cases hpk : (w.st id).parked with
      | nil =>
        simp only [hbox, hpk] at hs
        split at hs
        · cases hs
        · next w1 a1 hd =>
          cases hs
          have hd' := deliver_ok I hL w id _ m w1 a1 h.1 (by rfl) (by rfl) hd
          exact inv_same I _ _ (inv_deliver I w w1 id _ a1 h hd' hidle halive rfl (by simp [hpk]))
            (same_credit _ _ _)
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

theorem receive_prio_inv (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (h : Inv I w) (hs : receivePrio I w id = some w') : Inv I w' := by
  obtain ⟨m, pre, suf, w1, a1, halive, hidle, _, _, hd, hw'⟩ := receivePrio_spec I w w' id hs
  subst hw'
  have hd' := deliver_ok I hL w id _ m w1 a1 h.1 (by rfl) (by rfl) hd
  exact inv_deliver I w w1 id _ a1 h hd' hidle halive rfl rfl

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

theorem detach_inv (I : Impl) (w : World) (dst caller : InstId) (cid : Nat) (h : Inv I w) :
    Inv I (setActor w dst (detachReply (detachBox (w.st dst) caller) caller cid)) := by
  have hrest := detachHost_rest (w.st dst) caller cid
  have hpre := detach_preds I dst caller (w.st dst) cid (h.1.cont dst) (h.1.prog dst) (h.1.waited dst)
    (h.2.2.2 dst)
  have hlife : ∀ i, ((setActor w dst (detachReply (detachBox (w.st dst) caller) caller cid)).st i).life =
      (w.st i).life := by
    intro i
    by_cases hi : i = dst
    · rw [hi, setActor_self]
      exact hrest.2.1
    · rw [setActor_other w dst i _ hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sem_set I w dst _ h.1 hrest.1 hrest.2.1 hpre.1 hpre.2.1 hpre.2.2.1
    · intro hd
      exact detach_off _ _ _ (h.1.idleOff dst (by rw [← hrest.2.1]; exact hd))
    · exact Or.inl hrest.2.2
  · exact mail_scrub w dst _ h.2.1 hrest.2.2 hrest.2.1
      (fun d c k hk => (detachHost_park (w.st dst) caller cid d c).mpr ⟨k, hk⟩)
      (fun d c k hk => (detachHost_park (w.st dst) caller cid d c).mp ⟨k, hk⟩)
  · exact open_shape w _ h.2.2.1 (fun i hi => hi) hlife
  · exact outcome_set I w dst _ h.2.2.2 hpre.2.2.2

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
    have ho := h.2.2.2 id
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
        hW hl1 hfree hl1 rfl rfl (src_ty I id k (hk.trans hc.symm) ho.1)
        (by rw [contAt_select_to]; exact ho.2)
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
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact sem_enter I _ id (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted) tr
          ((refundParkedCall w id dst).st id).typestate (selectCall k .notAdmitted).toState hSR rfl htyF
          hlifeF htm hmem hl hl1 hcont hprogF hwait
          (idleOff_life (hlifeF.trans hlife)) hpkF (by rw [hR]; exact hS.rostered id halive)
      · exact mail_not_admitted w id dst _ h.2.1 ⟨k, hph⟩ hfreeF (hlifeF.trans (hf id).2.1) hpkF
      · exact open_set _ id _ (open_shape w _ h.2.2.1 (fun i hi => by rw [hR]; exact hi) (fun i => (hf i).2.1))
          (by rw [hR]; exact hS.rostered id halive)
      · exact outcome_set I _ id _
          (outcome_shape I w _ h.2.2.2 (fun i => (hf i).1) (fun i => (hf i).2.2.1))
          (outcome_finish I id _ k .notAdmitted ⟨tr, hmem, htm, hl, hfld, hk⟩)
    · next k hph =>
      cases hs
      rw [hph] at hc ho
      exact inv_pick I w id (w.st id) k k.onTimeout k.toTimeout h halive (by rw [hph]; trivial) halive
        rfl rfl ho.1 (Or.inr (Or.inr (Or.inl rfl))) (by rw [contAt_pick]; exact ho.2)
    · cases hs

theorem ingress_inv (I : Impl) (w w' : World) (dst : InstId) (label : String) (h : Inv I w)
    (hs : receiveIngress I w dst label = some w') : Inv I w' := by
  unfold receiveIngress at hs
  dsimp only at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · split at hs
      · cases hs
      · split at hs
        · cases hs
        · split at hs
          · cases hs
          · cases hs
            exact inv_same I w _ h (same_actor w dst _ rfl rfl rfl rfl)

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

theorem inv_init (I : Impl) (N : Nat) (hL : LocalOk I) : Inv I (initWorld I N) :=
  ⟨semInv_init I N hL, mail_init I N, open_init I N, outcome_init I N⟩

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
