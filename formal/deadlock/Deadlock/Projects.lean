import Deadlock.Step

set_option autoImplicit false

namespace Deadlock

/-! A parked send or an `awaitReply` is a blocking edge of the description, and
either Lemma 1 deletes that edge or a live partner stands in a state
`targetStates` still draws. Group mode reads the partner off the live tuple.
`"all"` uses the declared state list. `"explicit"` does not pass `LocalOk`. -/

def TyOk (D : Description) (w : World) : Prop :=
  ∀ id, (w.st id).life = .alive → (statesOf D (tname id)).elem (w.st id).typestate = true

theorem tyOk_id (D : Description) (w : World) (id : InstId) (a : Actor) (hT : TyOk D w)
    (hty : a.typestate = (w.st id).typestate) (hl : a.life = (w.st id).life) :
    TyOk D (setActor w id a) := by
  intro i hi
  by_cases h : i = id
  · rw [h] at hi ⊢
    rw [setActor_self] at hi ⊢
    rw [hl] at hi
    rw [hty]
    exact hT id hi
  · rw [setActor_other w id i a h] at hi ⊢
    exact hT i hi

theorem tyOk_new (D : Description) (w : World) (id : InstId) (a : Actor) (hT : TyOk D w)
    (h : a.life = .alive → (statesOf D (tname id)).elem a.typestate = true) :
    TyOk D (setActor w id a) := by
  intro i hi
  by_cases heq : i = id
  · rw [heq] at hi ⊢
    rw [setActor_self] at hi ⊢
    exact h hi
  · rw [setActor_other w id i a heq] at hi ⊢
    exact hT i hi

theorem tyOk_st (D : Description) (w w' : World) (hT : TyOk D w) (h : ∀ i, w'.st i = w.st i) :
    TyOk D w' := by
  intro id hi
  rw [h] at hi ⊢
  exact hT id hi

theorem tyOk_cell (D : Description) (w : World) (dst label : String) (c : Cell) (hT : TyOk D w) :
    TyOk D (setCell w dst label c) := by
  intro id hi
  have hs : (setCell w dst label c).st id = w.st id := by simp [setCell]
  rw [hs] at hi ⊢
  exact hT id hi

theorem tyOk_read (D : Description) (w : World) (id : InstId) (hT : TyOk D w) :
    TyOk D (readCells D w id) := by
  intro i hi
  rw [readCells_st] at hi ⊢
  exact hT i hi

theorem tyOk_credit (D : Description) (w : World) (tmpl : String) (sender : InstId) (hT : TyOk D w) :
    TyOk D (creditSender w tmpl sender) :=
  tyOk_id D w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) hT (bump_keeps _ _ _).1 (bump_keeps _ _ _).2.1

theorem proceed_life (a : Actor) (k : Cont) : (proceed a k).life = a.life := by
  cases hr : k.rest <;> simp [proceed, hr]

theorem tyOk_proceed (D : Description) (w : World) (id : InstId) (k : Cont) (hT : TyOk D w)
    (hty : (w.st id).typestate = k.toState) :
    TyOk D (setActor w id (proceed (w.st id) k)) :=
  tyOk_id D w id (proceed (w.st id) k) hT (proceed_keeps_ty _ _ hty) (proceed_life _ _)

theorem finish_keeps_ty (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).typestate = (selectCall k r).toState ∧ (finishCall a k r).life = a.life := by
  refine ⟨?_, finishCall_life a k r⟩
  cases hr : (selectCall k r).rest <;> simp [finishCall, proceed, hr]

theorem contTy_match (a b : Actor) (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) :
    contTy a ↔ contTy b := by
  unfold contTy
  rw [hp, ht]

theorem resume_keeps (a : Actor) (isCall : Bool) (dst : InstId) (hc : contTy a) :
    (resumeSender a isCall dst).typestate = a.typestate ∧ (resumeSender a isCall dst).life = a.life := by
  cases hph : a.phase with
  | parked d c k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hph] using hc
    cases isCall with
    | true => simp [resumeSender, hph]
    | false => cases hk : k.rest <;> simp [resumeSender, hph, proceed, hk, hty]
  | idle => simp [resumeSender, hph]
  | run k => simp [resumeSender, hph]
  | awaitReply d k => simp [resumeSender, hph]
  | awaitEffect k => simp [resumeSender, hph]
  | awaitPeer k => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem resume_cont (a : Actor) (isCall : Bool) (dst : InstId) (hc : contTy a) :
    contTy (resumeSender a isCall dst) := by
  cases hph : a.phase with
  | parked d c k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hph] using hc
    cases isCall with
    | true => simp [resumeSender, hph, contTy, hty]
    | false => cases hk : k.rest <;> simp [resumeSender, hph, proceed, hk, contTy, hty]
  | idle => simpa [resumeSender, hph] using hc
  | run k => simpa [resumeSender, hph] using hc
  | awaitReply d k => simpa [resumeSender, hph] using hc
  | awaitEffect k => simpa [resumeSender, hph] using hc
  | awaitPeer k => simpa [resumeSender, hph] using hc
  | crashed => simpa [resumeSender, hph] using hc

theorem cont_after (w : World) (id : InstId) (a : Actor) (hC : ∀ i, contTy (w.st i)) (ha : contTy a) :
    ∀ i, contTy ((setActor w id a).st i) := by
  intro i
  by_cases h : i = id
  · rw [h, setActor_self]
    exact ha
  · rw [setActor_other w id i a h]
    exact hC i

theorem tyOk_resume (D : Description) (w : World) (sender : InstId) (isCall : Bool) (dst : InstId)
    (hT : TyOk D w) (hc : contTy (w.st sender)) :
    TyOk D (setActor w sender (resumeSender (w.st sender) isCall dst)) := by
  obtain ⟨hty, hl⟩ := resume_keeps (w.st sender) isCall dst hc
  exact tyOk_id D w sender _ hT hty hl

theorem cont_credit (w : World) (tmpl : String) (sender : InstId) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((creditSender w tmpl sender).st i) := by
  intro i
  by_cases h : i = sender
  · rw [h, creditSender, setActor_self]
    simpa [bumpToken, contTy] using hC sender
  · rw [creditSender, setActor_other w sender i _ h]
    exact hC i

theorem cont_read (D : Description) (w : World) (id : InstId) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((readCells D w id).st i) := by
  intro i
  rw [readCells_st]
  exact hC i

theorem refund_msgs_ty (D : Description) (w : World) (dst : String) (ms : List Msg) (hT : TyOk D w) :
    TyOk D (refundMsgs w dst ms) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using hT
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact ih (creditLive w dst m.sender) (tyOk_credit D w dst _ hT)

theorem refund_park_ty (D : Description) (w : World) (dst : String) (ps : List Parked) (hT : TyOk D w) :
    TyOk D (refundParked w dst ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hT
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih (creditLive w dst p.msg.sender) (tyOk_credit D w dst _ hT)

theorem refund_msgs_cont (w : World) (dst : String) (ms : List Msg) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((refundMsgs w dst ms).st i) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using hC
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact ih (creditLive w dst m.sender) (cont_credit w dst _ hC)

theorem refund_park_cont (w : World) (dst : String) (ps : List Parked) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((refundParked w dst ps).st i) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hC
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih (creditLive w dst p.msg.sender) (cont_credit w dst _ hC)
theorem release_ty (D : Description) (w : World) (id : InstId) (ps : List Parked) (hT : TyOk D w)
    (hC : ∀ i, contTy (w.st i)) : TyOk D (releaseParked w id ps) := by
  unfold releaseParked
  induction ps generalizing w with
  | nil => simpa using hT
  | cons p ps ih =>
    rw [List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w hT hC
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      have hneg : ¬ ((p.isCall || decide (p.sender = id)) = true) := by
        rw [hf]
        decide
      rw [if_neg hneg]
      exact ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
        (tyOk_resume D w p.sender false id hT (hC p.sender))
        (cont_after w p.sender _ hC (resume_cont _ false id (hC p.sender)))

theorem release_cont (w : World) (id : InstId) (ps : List Parked)
    (hC : ∀ i, contTy (w.st i)) : ∀ i, contTy ((releaseParked w id ps).st i) := by
  unfold releaseParked
  induction ps generalizing w with
  | nil => simpa using hC
  | cons p ps ih =>
    rw [List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · simp only [hskip, ite_true]
      exact ih w hC
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      simp only [hf]
      exact ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
        (cont_after w p.sender _ hC (resume_cont _ false id (hC p.sender)))

theorem perform_ty (D : Description) (w : World) (sender : InstId) (k : Cont) (hT : TyOk D w)
    (hC : ∀ i, contTy (w.st i)) (hty : (w.st sender).typestate = k.toState) :
    TyOk D (performReply w sender k) := by
  unfold performReply
  have hty' : (w.st sender).typestate = (afterHead k).toState := by simp [afterHead, hty]
  split
  · exact tyOk_proceed D w sender (afterHead k) hT hty'
  · rename_i caller hto
    split
    · next dst ck hph =>
      split
      · have htyC : (w.st caller).typestate = ck.toState := by simpa [contTy, hph] using hC caller
        have hT1 := tyOk_id D w caller (finishCall (w.st caller) ck .reply) hT
          (by simp [finishCall]; exact proceed_keeps_ty _ _ htyC)
          (by simp [finishCall]; exact proceed_life _ _)
        by_cases hsc : caller = sender
        · subst hsc
          apply tyOk_proceed
          · exact hT1
          · rw [setActor_self]
            simp [finishCall]
            exact (proceed_keeps_ty _ _ htyC).trans hty'
        · apply tyOk_proceed
          · exact hT1
          · rw [setActor_other _ caller sender _ (Ne.symm hsc)]
            exact hty'
      · exact tyOk_proceed D w sender (afterHead k) hT hty'
    · exact tyOk_proceed D w sender (afterHead k) hT hty'

theorem contTy_eq (a b : Actor) (hph : b.phase = a.phase) (hty : b.typestate = a.typestate)
    (hc : contTy a) : contTy b := by
  unfold contTy at hc ⊢
  rw [hph, hty]
  exact hc

/-- Failing a waiter keeps its typestate. An empty continuation goes idle at the
state the continuation already named. -/
theorem failWaiter_ty (w : World) (dead i s : InstId) (hc : contTy (w.st s)) :
    ((failWaiter w dead i).st s).typestate = (w.st s).typestate ∧
      contTy ((failWaiter w dead i).st s) := by
  by_cases hs : s = i
  · rw [hs] at hc ⊢
    unfold failWaiter
    split
    · exact ⟨rfl, hc⟩
    · cases hph : (w.st i).phase with
      | parked d b k =>
        cases b with
        | false =>
          by_cases hd : d = dead
          · simp [hph, hd]
            cases hk : k.rest with
            | nil =>
              have hty : (w.st i).typestate = k.toState := by simpa [contTy, hph] using hc
              refine ⟨?_, ?_⟩
              · simp [setActor_self, proceed, hk, hty]
              · simp [contTy, setActor_self, proceed, hk]
            | cons _ _ =>
              have hty : (w.st i).typestate = k.toState := by simpa [contTy, hph] using hc
              refine ⟨?_, ?_⟩
              · simp [setActor_self, proceed, hk, hty]
              · simp [contTy, setActor_self, proceed, hk]
          · simp [hph, hd]
            exact hc
        | true =>
          simp [hph]
          exact hc
      | awaitReply _ _ =>
        simp [hph]
        exact hc
      | idle =>
        simp [hph]
        exact hc
      | run _ =>
        simp [hph]
        exact hc
      | awaitEffect _ =>
        simp [hph]
        exact hc
      | awaitPeer _ =>
        simp [hph]
        exact hc
      | crashed =>
        simp [hph]
        exact hc
  · rw [failWaiter_other w dead i s hs]
    exact ⟨rfl, hc⟩

theorem failFold_ty (w : World) (dead s : InstId) (ids : List InstId) (hc : contTy (w.st s)) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).typestate = (w.st s).typestate ∧
      contTy ((ids.foldl (fun w i => failWaiter w dead i) w).st s) := by
  induction ids generalizing w with
  | nil => exact ⟨rfl, hc⟩
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have h1 := failWaiter_ty w dead i s hc
    have h2 := ih (failWaiter w dead i) h1.2
    exact ⟨h2.1.trans h1.1, h2.2⟩

theorem killOne_ty (w : World) (D : Description) (id s : InstId) (hne : s ≠ id)
    (hc : contTy (w.st s)) :
    ((killOne w D id).st s).typestate = (w.st s).typestate ∧
      contTy ((killOne w D id).st s) := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  have hc1 : contTy (w1.st s) := by simpa [hst1] using hc
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
  have hph2 : (w2.st s).phase = (w1.st s).phase := by simpa [w2] using h2.1
  have hty2 : (w2.st s).typestate = (w1.st s).typestate := by simpa [w2] using h2.2.2.2.2.2
  have hc2 : contTy (w2.st s) := contTy_eq (w1.st s) (w2.st s) hph2 hty2 hc1
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
  have hph3 : (w3.st s).phase = (w2.st s).phase := by simpa [w3] using h3.1
  have hty3 : (w3.st s).typestate = (w2.st s).typestate := by simpa [w3] using h3.2.2.2.2.2
  have hc3 : contTy (w3.st s) := contTy_eq (w2.st s) (w3.st s) hph3 hty3 hc2
  let w4 := failWaiters w3 id
  have h4 := failFold_ty w3 id s w3.roster hc3
  have hc4 : contTy (w4.st s) := by simpa [w4, failWaiters] using h4.2
  have hty4 : (w4.st s).typestate = (w.st s).typestate := by
    have h4t : (w4.st s).typestate = (w3.st s).typestate := by simpa [w4, failWaiters] using h4.1
    exact h4t.trans (hty3.trans (hty2.trans (congrArg (·.typestate) hst1)))
  let w5 := forgetSender w4 id
  have h5 := forget_stable w4 id s
  have hph5 : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
  have hty5r : (w5.st s).typestate = (w4.st s).typestate := by simpa [w5] using h5.2.2.1
  have hc5 : contTy (w5.st s) := contTy_eq (w4.st s) (w5.st s) hph5 hty5r hc4
  have hty5 : (w5.st s).typestate = (w.st s).typestate := hty5r.trans hty4
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact ⟨hty5, hc5⟩

theorem killFold_ty (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (hlive : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
      .alive)
    (hc : contTy (w.st s)) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).typestate =
      (w.st s).typestate := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons] at hlive ⊢
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true] at hlive ⊢
      by_cases hs : s = j
      · subst hs
        exact absurd hlive (killFold_stays_dead (killOne w D s) D sub key js s
          (by rw [(killOne_self w D s).1]; intro h; cases h))
      · have hstep := killOne_ty w D j s hs hc
        exact (ih (killOne w D j) hlive hstep.2).trans hstep.1
    · simp only [hcond] at hlive ⊢
      exact ih w hlive hc

theorem killSubtree_ty (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) (hc : contTy (w.st s)) :
    ((killSubtree w D sub key).st s).typestate = (w.st s).typestate := by
  have hlive' : ((w.roster.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
      .alive := by
    simpa [killSubtree, killMembers] using hlive
  simpa [killSubtree, killMembers] using killFold_ty w D sub key w.roster s hlive' hc

theorem failWaiters_ty (D : Description) (w : World) (dead : InstId)
    (hT : TyOk D w) (hC : ∀ i, contTy (w.st i)) : TyOk D (failWaiters w dead) := by
  intro s hl
  have hty : ((failWaiters w dead).st s).typestate = (w.st s).typestate := by
    simpa [failWaiters] using (failFold_ty w dead s w.roster (hC s)).1
  have hold : (w.st s).life = .alive := by
    rw [← failWaiters_life w dead s]
    simpa [failWaiters] using hl
  rw [hty]
  exact hT s hold

/-- `stateFails` is one conjunct of a passing structural check. -/
theorem state_lines (D : Description) (hG : GraphOk D) : stateFails D = [] := by
  have h := hG.struct
  unfold structLines at h
  exact append_nil_right
    (append_nil_left (append_nil_left (append_nil_left (append_nil_left
      (append_nil_left (append_nil_left (append_nil_left (append_nil_left h))))))))

theorem filterMap_mem_none {α β : Type} (f : α → Option β) (xs : List α) (a : α)
    (h : xs.filterMap f = []) (ha : a ∈ xs) : f a = none := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.filterMap_cons] at h
    cases ha with
    | head =>
      cases hf : f a with
      | none => rfl
      | some b =>
        rw [hf] at h
        simp at h
    | tail _ ht =>
      cases hf : f x with
      | none =>
        rw [hf] at h
        exact ih h ht
      | some b =>
        rw [hf] at h
        simp at h

theorem filter_some {α β : Type} (f : α → Option β) (xs : List α) (b : β) (a : α)
    (ha : a ∈ xs) (hf : f a = some b) : b ∈ xs.filterMap f := by
  simpa [List.mem_filterMap] using ⟨a, ha, hf⟩

theorem initial_declared (D : Description) (t : Template) (h : stateFails D = []) (ht : t ∈ D.templates) :
    t.states.elem t.initial = true := by
  unfold stateFails at h
  have hf := filterMap_mem_none _ D.templates t h ht
  cases he : t.states.isEmpty
  · simp [he] at hf
    cases hi : t.states.elem t.initial
    · have hnin : ¬ t.initial ∈ t.states := by
        intro hm
        have hbad := List.elem_iff.mpr hm
        rw [hi] at hbad
        cases hbad
      rw [if_neg hnin] at hf
      simp at hf
    · rfl
  · simp [he] at hf

theorem tyOk_record (D : Description) (w : World) (roster : List InstId) (next : String → Nat)
    (hT : TyOk D w) : TyOk D { w with roster := roster, nextIx := next } := by
  intro id hi
  have hs : ({ w with roster := roster, nextIx := next }).st id = w.st id := by simp
  rw [hs] at hi ⊢
  exact hT id hi


theorem ty_init (I : Impl) (hG : GraphOk I.desc) (N : Nat) : TyOk I.desc (initWorld I N) := by
  intro id hl
  rw [init_base_st] at hl ⊢
  by_cases hc : (coreRoster I.desc).contains id = true
  · rw [if_pos hc] at hl ⊢
    cases ht : templateOf I.desc (tname id) with
    | none => simp [initActor, withTokens, ht, absentActor] at hl
    | some t =>
      simp only [initActor, withTokens, ht] at hl ⊢
      rw [statesOf, ht]
      exact initial_declared I.desc t (state_lines I.desc hG) (template_mem I.desc (tname id) t ht)
  · have hf : (coreRoster I.desc).contains id = false := by
      cases hbb : (coreRoster I.desc).contains id <;> simp_all
    have hneg : ¬ ((coreRoster I.desc).contains id = true) := by
      rw [hf]
      decide
    rw [if_neg hneg] at hl
    simp [absentActor] at hl

theorem to_mem (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    (statesOf I.desc tr.template).elem tr.toState = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some t =>
    simp only [transitionOk, ht, Bool.and_eq_true] at hok
    have h2 : t.states.elem tr.toState = true := hok.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    simpa [statesOf, ht] using h2

def picked (k : Cont) (rest : List Eff) (specific : String) : Cont :=
  { k with rest := rest, toState := pickState k.toState specific }

theorem proceed_writes (a : Actor) (k : Cont) : (proceed a k).typestate = k.toState := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem src_state_named (I : Impl) (hL : LocalOk I) (id : InstId) (a : Actor) (k : Cont)
    (h : srcOk I id a k) : (statesOf I.desc (tname id)).elem k.toState = true := by
  obtain ⟨tr, hm, htm, hl, _, hk⟩ := h
  have hn := lands_named I hL tr hm a.typestate hl
  simpa [statesOf, htm, hk] using hn

theorem pick_state_named (I : Impl) (hL : LocalOk I) (id : InstId) (a : Actor) (k : Cont)
    (specific : String) (h : srcOk I id a k)
    (hs : specific = k.toNotAdmitted ∨ specific = k.toTimedOut ∨ specific = k.toTimeout ∨
      specific = k.toFull ∨ specific = k.toGone) :
    (statesOf I.desc (tname id)).elem (pickState k.toState specific) = true :=
  src_state_named I hL id { a with typestate := pickState k.toState specific }
    { k with rest := [], toState := pickState k.toState specific }
    (src_pick I id a k [] specific h hs)

theorem select_state_named (I : Impl) (hL : LocalOk I) (id : InstId) (a : Actor) (k : Cont)
    (r : CallResult) (h : srcOk I id a k) :
    (statesOf I.desc (tname id)).elem (selectCall k r).toState = true :=
  src_state_named I hL id { a with typestate := (selectCall k r).toState } (selectCall k r)
    (src_select I id a k r h)

/-! A frame is a world operation after which every live actor was already live,
in the same typestate. Only a delivery and a birth move a live typestate, so
every seal, kill, refund and crash is a frame. -/

def Frame (w w' : World) : Prop :=
  ∀ i, (w'.st i).life = .alive → (w.st i).life = .alive ∧ (w'.st i).typestate = (w.st i).typestate

theorem frame_refl (w : World) : Frame w w := fun _ h => ⟨h, rfl⟩

theorem frame_trans {w1 w2 w3 : World} (h1 : Frame w1 w2) (h2 : Frame w2 w3) : Frame w1 w3 := by
  intro i hl
  obtain ⟨ha, ht⟩ := h2 i hl
  obtain ⟨ha', ht'⟩ := h1 i ha
  exact ⟨ha', ht.trans ht'⟩

theorem frame_fields (w w' : World)
    (h : ∀ i, (w'.st i).life = (w.st i).life ∧ (w'.st i).typestate = (w.st i).typestate) :
    Frame w w' := by
  intro i hl
  obtain ⟨h1, h2⟩ := h i
  exact ⟨h1.symm.trans hl, h2⟩

theorem frame_st (w w' : World) (h : ∀ i, w'.st i = w.st i) : Frame w w' :=
  frame_fields w w' fun i => by rw [h i]; exact ⟨rfl, rfl⟩

theorem frame_same {w w' : World} (h : Same w w') : Frame w w' :=
  frame_fields w w' fun i => ⟨h.life i, h.ty i⟩

theorem frame_set (w : World) (id : InstId) (a : Actor)
    (h : a.life = .alive → (w.st id).life = .alive ∧ a.typestate = (w.st id).typestate) :
    Frame w (setActor w id a) := by
  intro i hl
  by_cases hi : i = id
  · subst hi
    rw [setActor_self] at hl ⊢
    exact h hl
  · rw [setActor_other w id i a hi] at hl ⊢
    exact ⟨hl, rfl⟩

theorem frame_keep (w : World) (id : InstId) (a : Actor) (hl : a.life = (w.st id).life)
    (ht : a.typestate = (w.st id).typestate) : Frame w (setActor w id a) :=
  frame_set w id a fun h => ⟨hl.symm.trans h, ht⟩

theorem frame_halt (w : World) (id : InstId) (a : Actor) (hl : a.life ≠ .alive) :
    Frame w (setActor w id a) :=
  frame_set w id a fun h => absurd h hl

theorem frame_note (w : World) (sender : InstId) (dst : String) : Frame w (noteStale w sender dst) :=
  frame_st w _ fun _ => rfl

theorem frame_credit (w : World) (tmpl : String) (sender : InstId) :
    Frame w (creditSender w tmpl sender) :=
  frame_same (same_credit w tmpl sender)

theorem frame_crash (w : World) : Frame w (crashWorld w) := by
  intro i hl
  refine ⟨?_, crashWorld_ty w i⟩
  by_cases hm : i ∈ w.roster
  · rw [crash_at w i hm] at hl
    by_cases hgo : (w.st i).life = .alive
    · rw [crash_go hgo] at hl
      cases hl
    · rw [crash_stay (fun he => hgo he)] at hl
      exact hl
  · rw [crash_off w i hm] at hl
    exact hl

theorem frame_offer (D : Description) (w : World) (host : InstId) (msg : Msg) :
    Frame w (offerPrio D w host msg) := by
  unfold offerPrio
  dsimp only
  split
  · exact frame_crash w
  · exact frame_keep w host _ rfl rfl

theorem frame_tryWake (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId) :
    Frame w (tryWake D w dstId label writer) := by
  unfold tryWake
  dsimp only
  split
  · exact frame_refl w
  · exact frame_offer D w dstId _

theorem frame_wakes (D : Description) (ids : List InstId) (w : World) (label : String) (writer : InstId) :
    Frame w (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => exact frame_refl w
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact frame_trans (frame_tryWake D w i label writer) (ih _)

theorem frame_wake (D : Description) (w : World) (dst label : String) (writer : InstId) :
    Frame w (wakeReaders D w dst label writer) :=
  frame_wakes D (readersOf w dst) w label writer

theorem frame_tomb (D : Description) (w : World) (child : InstId) :
    Frame w (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  split
  · exact frame_refl w
  · dsimp only
    split
    · exact frame_refl w
    · split
      · exact frame_crash w
      · exact frame_offer D w _ _

theorem frame_outbound (w : World) (dead : InstId) : Frame w (releaseOutbound w dead) :=
  frame_fields w _ fun i => ⟨(releaseOutbound_fields w dead i).2.1, (releaseOutbound_fields w dead i).2.2.1⟩

/-- Resuming the non-call senders parked on a sealed actor keeps their typestate:
an empty continuation goes idle at the state it already named. -/
theorem release_frame (id : InstId) (ps : List Parked) (w : World) (hC : ∀ i, contTy (w.st i)) :
    Frame w (releaseParked w id ps) ∧ ∀ i, contTy ((releaseParked w id ps).st i) := by
  rw [release_fold_eq]
  induction ps generalizing w with
  | nil => exact ⟨frame_refl w, hC⟩
  | cons p ps ih =>
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [release_step_skip id p ps w hskip]
      exact ih w hC
    · rw [release_step_go id p ps w hskip]
      obtain ⟨hty, hl⟩ := resume_keeps (w.st p.sender) false id (hC p.sender)
      obtain ⟨hF, hC'⟩ := ih _ (cont_after w p.sender _ hC (resume_cont _ false id (hC p.sender)))
      exact ⟨frame_trans (frame_keep w p.sender _ hl hty) hF, hC'⟩

theorem frame_releaseWorld (D : Description) (w : World) (id : InstId) (a : Actor)
    (hC : ∀ i, contTy (w.st i)) : Frame w (releaseWorld D w id a) := by
  have hs3 : Same w (refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked) :=
    same_trans (same_trans (same_cells D w id) (same_refundMsgs _ _ _)) (same_refundParked _ _ _)
  generalize hw3 : refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked = w3
    at hs3
  have hrel : releaseWorld D w id a =
      releaseParked (setActor (releaseOutbound w3 id) id
        { ((releaseOutbound w3 id).st id) with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }) id a.parked := by
    rw [← hw3]
    rfl
  rw [hrel]
  have hf := releaseOutbound_fields w3 id
  have hF4 : Frame w (releaseOutbound w3 id) := frame_trans (frame_same hs3) (frame_outbound w3 id)
  have hC4 : ∀ i, contTy ((releaseOutbound w3 id).st i) := fun i =>
    contTy_congr ((hf i).2.2.2.1.trans (hs3.phase i)) ((hf i).2.2.1.trans (hs3.ty i)) (hC i)
  have hdead : contTy { ((releaseOutbound w3 id).st id) with
      life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [contTy]
  have hC5 := cont_after (releaseOutbound w3 id) id _ hC4 hdead
  exact frame_trans (frame_trans hF4 (frame_halt _ id _ (by simp))) (release_frame id a.parked _ hC5).1

theorem releaseWorld_cont (D : Description) (w : World) (id : InstId) (a : Actor)
    (hC : ∀ i, contTy (w.st i)) : ∀ i, contTy ((releaseWorld D w id a).st i) := by
  have hs3 : Same w (refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked) :=
    same_trans (same_trans (same_cells D w id) (same_refundMsgs _ _ _)) (same_refundParked _ _ _)
  generalize hw3 : refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked = w3
    at hs3
  have hrel : releaseWorld D w id a =
      releaseParked (setActor (releaseOutbound w3 id) id
        { ((releaseOutbound w3 id).st id) with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }) id a.parked := by
    rw [← hw3]
    rfl
  rw [hrel]
  have hf := releaseOutbound_fields w3 id
  have hC4 : ∀ i, contTy ((releaseOutbound w3 id).st i) := fun i =>
    contTy_congr ((hf i).2.2.2.1.trans (hs3.phase i)) ((hf i).2.2.1.trans (hs3.ty i)) (hC i)
  have hdead : contTy { ((releaseOutbound w3 id).st id) with
      life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [contTy]
  exact (release_frame id a.parked _ (cont_after (releaseOutbound w3 id) id _ hC4 hdead)).2

theorem frame_seal (D : Description) (w : World) (id : InstId) (a : Actor) (hC : ∀ i, contTy (w.st i)) :
    Frame w (sealActor D w id a) := by
  unfold sealActor
  exact frame_trans (frame_releaseWorld D w id a hC) (frame_tomb D _ id)

theorem frame_shutdown (D : Description) (w : World) (id : InstId)
    (hC : ∀ i, contTy (w.st i)) : Frame w (shutdownActor D w id) := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · rw [ite_eq_left hlive]
    exact frame_seal D w id (w.st id) hC
  · rw [ite_eq_right hlive]
    exact frame_refl w

/-- Sealing a branch is a frame. `contTy` is enough: a seal does not install a live phase. -/
theorem seal_frame_cont (fuel : Nat) (D : Description) (w : World) (id : InstId)
    (hC : ∀ i, contTy (w.st i)) :
    Frame w (sealBranch fuel D w id) ∧ ∀ i, contTy ((sealBranch fuel D w id).st i) := by
  induction fuel generalizing w id with
  | zero => exact ⟨frame_refl w, hC⟩
  | succ n ih =>
    have hfold : ∀ (ids : List InstId) (acc : World),
        (∀ i, contTy (acc.st i)) → Frame w acc →
        Frame w (ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc) ∧
        ∀ i, contTy ((ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch n D acc child else acc) acc).st i) := by
      intro ids
      induction ids with
      | nil => intro acc hCa hf; exact ⟨hf, hCa⟩
      | cons c cs ihc =>
        intro acc hCa hf
        simp only [List.foldl_cons]
        split
        · obtain ⟨hF, hC'⟩ := ih acc c hCa
          exact ihc _ hC' (frame_trans hf hF)
        · exact ihc _ hCa hf
    obtain ⟨hF, hC'⟩ := hfold w.roster w hC (frame_refl w)
    unfold sealBranch
    dsimp only
    split
    · refine ⟨frame_trans hF (frame_releaseWorld D _ id _ hC'), ?_⟩
      intro i
      exact releaseWorld_cont D _ id _ hC' i
    · exact ⟨hF, hC'⟩

theorem frame_sealBranch (fuel : Nat) (D : Description) (w : World) (id : InstId)
    (hC : ∀ i, contTy (w.st i)) : Frame w (sealBranch fuel D w id) :=
  (seal_frame_cont fuel D w id hC).1

theorem frame_drop (D : Description) (w : World) (id : InstId) (hC : ∀ i, contTy (w.st i)) :
    Frame w (dropDescendants D w id) := by
  unfold dropDescendants
  have hfold : ∀ (ids : List InstId) (acc : World),
      (∀ i, contTy (acc.st i)) → Frame w acc →
      Frame w (ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch w.roster.length D acc child else acc) acc) := by
    intro ids
    induction ids with
    | nil => intro _ hf; exact hf
    | cons c cs ihc =>
      intro acc hCa hf
      simp only [List.foldl_cons]
      split
      · exact ihc _ (seal_frame_cont w.roster.length D acc c hCa).2
          (frame_trans hf (frame_sealBranch w.roster.length D acc c hCa))
      · exact ihc _ hCa hf
  exact hfold w.roster w hC (frame_refl w)

theorem frame_terminate (I : Impl) (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : Inv I w) : Frame w (terminateStage D w id a) :=
  frame_trans (frame_drop D w id h.1.cont)
    (frame_shutdown D (dropDescendants D w id) id (dropDescendants_inv I D w id h).1.cont)

theorem frame_abort (I : Impl) (D : Description) (w : World) (parent : InstId) (h : Inv I w) :
    Frame w (abortChildren D w parent) := by
  unfold abortChildren
  have hfold : ∀ (ids : List InstId) (acc : World), Inv I acc → Frame w acc →
      Inv I (ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) acc) ∧
      Frame w (ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) acc) := by
    intro ids
    induction ids with
    | nil => intro acc ha hf; exact ⟨ha, hf⟩
    | cons c cs ihc =>
      intro acc ha hf
      simp only [List.foldl_cons]
      apply ihc
      · split
        · have hstep : shutdownActor D (dropDescendants D acc c) c =
              terminateStage D acc c (acc.st c) := by
            unfold terminateStage
            rfl
          rw [hstep]
          exact terminateStage_inv I D acc c _ ha
        · exact ha
      · split
        · exact frame_trans hf (frame_trans (frame_drop D acc c ha.1.cont)
            (frame_shutdown D (dropDescendants D acc c) c
              (dropDescendants_inv I D acc c ha).1.cont))
        · exact hf
  exact (hfold w.roster w h (frame_refl w)).2

/-- A send keeps every typestate. The dead target proceeds in `k.toState`, which
the sender already holds. -/
theorem enqueue_ty_eq (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (k : Cont) (hty : (w.st sender).typestate = k.toState) (i : InstId) :
    ((enqueueOrPark w D sender dst msg false k).st i).typestate = (w.st i).typestate := by
  have hpro : ∀ a : Actor, a.typestate = (w.st sender).typestate → (proceed a k).typestate = a.typestate :=
    fun a ha => proceed_keeps_ty a k (ha.trans hty)
  unfold enqueueOrPark
  dsimp only
  by_cases hi : i = sender
  · subst hi
    split <;> (try split) <;> (try split) <;>
      simp_all [setActor, chargeSender, bumpToken, issueCall]
  · by_cases hd : i = dst
    · subst hd
      split <;> (try split) <;> (try split) <;> simp [setActor, hi]
    · split <;> (try split) <;> (try split) <;> simp [setActor, hi, hd]

theorem frame_enqueue (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (k : Cont) (hty : (w.st sender).typestate = k.toState) :
    Frame w (enqueueOrPark w D sender dst msg false k) :=
  frame_fields w _ fun i =>
    ⟨enqueue_life w D sender dst msg false k i, enqueue_ty_eq w D sender dst msg k hty i⟩

/-- A call whose target is alive parks or awaits. Neither writes a typestate. -/
theorem enqueue_admitted_ty (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (k : Cont) (hlive : (w.st dst).life = .alive) (i : InstId) :
    ((enqueueOrPark w D sender dst msg true k).st i).typestate = (w.st i).typestate := by
  unfold enqueueOrPark
  dsimp only
  rw [ite_eq_right (fun h => h hlive)]
  simp only [ite_true]
  by_cases hi : i = sender
  · subst hi
    split <;> split <;> simp [setActor, chargeSender, bumpToken, issueCall]
  · by_cases hd : i = dst
    · subst hd
      split <;> split <;> simp [setActor, hi, chargeSender, bumpToken, issueCall]
    · split <;> split <;> simp [setActor, hi, hd, chargeSender, bumpToken, issueCall]

theorem enqueue_admitted_frame (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (k : Cont) (hlive : (w.st dst).life = .alive) :
    Frame w (enqueueOrPark w D sender dst msg true k) :=
  frame_fields w _ fun i =>
    ⟨enqueue_life w D sender dst msg true k i, enqueue_admitted_ty w D sender dst msg k hlive i⟩

theorem frame_reply (I : Impl) (w : World) (sender : InstId) (k : Cont) (h : Inv I w)
    (hph : (w.st sender).phase = .run k) : Frame w (performReply w sender k) := by
  have hty : (w.st sender).typestate = (afterHead k).toState := by
    simpa [contTy, hph, afterHead] using h.1.cont sender
  have hproc : ∀ w0 : World, Frame w w0 → w0.st sender = w.st sender →
      Frame w (setActor w0 sender (proceed (w0.st sender) (afterHead k))) := by
    intro w0 hF hst
    refine frame_trans hF (frame_keep w0 sender _ (proceed_life _ _) ?_)
    rw [hst]
    exact proceed_keeps_ty _ _ hty
  unfold performReply
  dsimp only
  split
  · exact hproc w (frame_refl w) rfl
  · next caller _ =>
    split
    · next dst ck hcph =>
      split
      · have hcid : caller ≠ sender := by
          intro he
          rw [he, hph] at hcph
          cases hcph
        have hc : (w.st caller).typestate = ck.toState := by simpa [contTy, hcph] using h.1.cont caller
        have hfin := finish_keeps_ty (w.st caller) ck .reply
        have htyEq : (finishCall (w.st caller) ck .reply).typestate = (w.st caller).typestate := by
          rw [hfin.1]
          simpa [selectCall] using hc.symm
        exact hproc _ (frame_keep w caller _ hfin.2 htyEq) (setActor_other w caller sender _ (Ne.symm hcid))
      · exact hproc w (frame_refl w) rfl
    · exact hproc w (frame_refl w) rfl

/-! Every live peer belongs to a per-peer template. A spawn and a child birth
check `perPeer`, and nothing else makes an actor live. -/

def PeerOk (D : Description) (w : World) : Prop :=
  ∀ n k g, (w.st (.peer n k g)).life = .alive → ∃ t, templateOf D n = some t ∧ t.multiplicity = .perPeer

/-- The two facts about live actors that `Projects` reads. -/
def Good (D : Description) (w : World) : Prop := TyOk D w ∧ PeerOk D w

theorem good_frame {D : Description} {w w' : World} (hG : Good D w) (hF : Frame w w') : Good D w' := by
  refine ⟨?_, ?_⟩
  · intro i hl
    obtain ⟨ha, ht⟩ := hF i hl
    rw [ht]
    exact hG.1 i ha
  · intro n k g hl
    exact hG.2 n k g (hF _ hl).1

theorem good_set {D : Description} {w : World} (id : InstId) (a : Actor) (hG : Good D w)
    (hl : a.life = .alive → (w.st id).life = .alive)
    (ht : a.life = .alive → (statesOf D (tname id)).elem a.typestate = true) :
    Good D (setActor w id a) := by
  refine ⟨tyOk_new D w id a hG.1 ht, ?_⟩
  intro n k g hal
  by_cases hi : InstId.peer n k g = id
  · rw [hi, setActor_self] at hal
    have hw := hl hal
    rw [← hi] at hw
    exact hG.2 n k g hw
  · rw [setActor_other w id _ a hi] at hal
    exact hG.2 n k g hal

/-- A call whose target is not alive ends as `NotAdmitted` in a declared state. -/
theorem enqueue_refused_good (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId)
    (msg : Msg) (k : Cont) (hG : Good I.desc w) (hs : srcOk I sender (w.st sender) k)
    (hdead : (w.st dst).life ≠ .alive) :
    Good I.desc (enqueueOrPark w I.desc sender dst msg true k) := by
  unfold enqueueOrPark
  dsimp only
  rw [ite_eq_left hdead, ite_eq_left rfl]
  refine good_set sender (finishCall (issueCall (w.st sender)) k .notAdmitted) hG ?_ ?_
  · intro hl
    rw [(finish_keeps_ty _ _ _).2] at hl
    simpa [issueCall] using hl
  · intro _
    rw [(finish_keeps_ty (issueCall (w.st sender)) k .notAdmitted).1]
    exact select_state_named I hL sender (issueCall (w.st sender)) k .notAdmitted
      (src_ty I sender k (by simp [issueCall]) hs)

theorem good_born {D : Description} {w : World} (n : String) (key gen : Nat) (a : Actor) (t : Template)
    (hG : Good D w) (ht : templateOf D n = some t) (hm : t.multiplicity = .perPeer)
    (hs : (statesOf D n).elem a.typestate = true) : Good D (setActor w (.peer n key gen) a) := by
  refine ⟨tyOk_new D w _ a hG.1 (fun _ => hs), ?_⟩
  intro n' k' g' hal
  by_cases hi : InstId.peer n' k' g' = InstId.peer n key gen
  · cases hi
    exact ⟨t, ht, hm⟩
  · rw [setActor_other w _ _ a hi] at hal
    exact hG.2 n' k' g' hal

theorem perPeer_of_beq (t : Template) (h : (t.multiplicity == .perPeer) = true) :
    t.multiplicity = .perPeer := by
  cases hm : t.multiplicity with
  | one =>
    rw [hm] at h
    exact absurd h (by decide)
  | perPeer => rfl

theorem good_place (I : Impl) (hGr : GraphOk I.desc) (w : World) (template : String) (k : Nat)
    (t : Template) (parent : Option InstId) (next : World → World) (hnext : ∀ v : World, (next v).st = v.st)
    (ht : templateOf I.desc template = some t) (hm : t.multiplicity = .perPeer) (hG : Good I.desc w) :
    Good I.desc (placePeer I w template k t.initial parent next) := by
  have hdecl : (statesOf I.desc template).elem t.initial = true := by
    simpa [statesOf, ht] using
      initial_declared I.desc t (state_lines I.desc hGr) (template_mem I.desc template t ht)
  unfold placePeer
  dsimp only
  have hG1 : Good I.desc (next { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] }) :=
    good_frame hG (frame_st _ _ fun i => by rw [hnext])
  have hG2 := good_born template k (maxGen w template k)
    { bornActor I.desc w template k t.initial with parent := parent } t hG1 ht hm
    (by simpa [bornActor, withKeyTokens] using hdecl)
  exact good_frame hG2 (frame_st _ _ fun i => cellsSt _ _ _ i)

theorem spawn_good (I : Impl) (hGr : GraphOk I.desc) (w w' : World) (template : String)
    (hG : Good I.desc w) (hs : spawn I w template = some w') : Good I.desc w' := by
  unfold spawn at hs
  split at hs
  · cases hs
  · next t ht =>
    split at hs
    · next hmay =>
      have hm : t.multiplicity = .perPeer := by
        simp only [maySpawnRoot, Bool.and_eq_true] at hmay
        exact perPeer_of_beq t hmay.1.1.1.1
      split at hs
      · cases hs
        exact good_place I hGr w template _ t _ _ (fun _ => rfl) ht hm hG
      · split at hs
        · cases hs
          exact good_place I hGr w template _ t _ _ (fun _ => rfl) ht hm hG
        · cases hs
          exact good_place I hGr w template _ t _ _ (fun _ => rfl) ht hm hG
    · cases hs

theorem spawnChild_good (I : Impl) (hGr : GraphOk I.desc) (w w' : World) (parent : InstId) (child : String)
    (hG : Good I.desc w) (hs : spawnChild I w parent child = some w') : Good I.desc w' := by
  unfold spawnChild at hs
  split at hs
  · cases hs
  · next t ht =>
    split at hs
    · next hc =>
      have hm : t.multiplicity = .perPeer := by
        simp only [Bool.and_eq_true] at hc
        exact perPeer_of_beq t hc.1.1
      split at hs
      · split at hs
        · split at hs
          · cases hs
            exact good_place I hGr w child _ t _ (fun v => v) (fun _ => rfl) ht hm hG
          · cases hs
            exact hG
        · cases hs
      · split at hs
        · split at hs
          · cases hs
            exact hG
          · cases hs
            exact good_place I hGr w child _ t _ (fun v => v) (fun _ => rfl) ht hm hG
        · cases hs
    · split at hs
      · cases hs
        exact hG
      · cases hs

theorem exec_good (I : Impl) (hL : LocalOk I) (hGr : GraphOk I.desc) (w : World) (id : InstId)
    (k : Cont) (h : Inv I w) (hG : Good I.desc w) (hph : (w.st id).phase = .run k) :
    Good I.desc (execRun I w id (w.st id) k) := by
  by_cases ha : (w.st id).life = .alive
  case neg =>
    have hno : ((w.st id).life == .alive) = false := by simpa [beq_iff_eq] using ha
    simp only [execRun, hno, Bool.false_eq_true, ↓reduceIte]
    exact hG
  have hgo : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using ha
  obtain ⟨hty, _, hsrc, _⟩ := run_facts I w id k h hph
  have hty' : (w.st id).typestate = (afterHead k).toState := hty
  have hsrcA : srcOk I id (w.st id) (afterHead k) := src_after I id (w.st id) k hsrc
  have hproc : ∀ (w0 : World) (k' : Cont), w0.st id = w.st id → (w.st id).typestate = k'.toState →
      Frame w0 (setActor w0 id (proceed (w.st id) k')) := by
    intro w0 k' hst h'
    exact frame_keep w0 id _ (by rw [hst]; exact proceed_life _ _) (by rw [hst]; exact proceed_keeps_ty _ _ h')
  cases hk : k.rest with
  | nil =>
    simp only [execRun, hgo, hk, ite_true]
    exact good_frame hG (frame_keep w id _ rfl hty.symm)
  | cons e es =>
    cases e with
    | send d l n =>
      cases hr : route w I.desc id d n with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact good_frame hG (frame_trans (frame_note w id d) (hproc _ _ rfl hty'))
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        exact good_frame hG (frame_enqueue w I.desc id dstId _ (afterHead k) hty')
    | trySend d l n f g =>
      have hgoneN := pick_state_named I hL id (w.st id) (afterHead k) (afterHead k).toGone hsrcA
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      have hfullN := pick_state_named I hL id (w.st id) (afterHead k) (afterHead k).toFull hsrcA
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have hset (rest : List Eff) (specific : String)
          (hn : (statesOf I.desc (tname id)).elem (pickState (afterHead k).toState specific) = true) :
          Good I.desc (setActor w id (proceed (w.st id) (picked (afterHead k) rest specific))) := by
        let k' := picked (afterHead k) rest specific
        refine good_set id (proceed (w.st id) k') hG (fun hl => ?_) (fun _ => ?_)
        · exact (proceed_life (w.st id) k').symm.trans hl
        · rw [proceed_writes]
          simp only [k', picked]
          exact hn
      cases hr : route w I.desc id d n with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        let k' := picked (afterHead k) g (afterHead k).toGone
        exact good_set id (proceed ((noteStale w id d).st id) k') (good_frame hG (frame_note w id d))
          (fun hl => by
            rw [show (noteStale w id d).st id = w.st id from rfl]
            exact (proceed_life _ k').symm.trans hl)
          (fun _ => by
            rw [proceed_writes]
            simp only [k', picked]
            exact hgoneN)
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        split
        · exact good_frame hG (frame_enqueue w I.desc id dstId _ (afterHead k) hty')
        · split
          · exact hset f (afterHead k).toFull hfullN
          · exact hset g (afterHead k).toGone hgoneN
    | call d l n na to =>
      have hsrcC := src_lists I id (w.st id) (afterHead k) na to (afterHead k).onTimeout hsrcA
      cases hr : resolveId I.desc w id d n with
      | none =>
        simp only [execRun, hgo, hk, hr, ite_true]
        let kC := ({ afterHead k with onNotAdmitted := na, onTimedOut := to } : Cont)
        exact good_set id (finishCall (issueCall (w.st id)) kC .notAdmitted)
          (good_frame hG (frame_note w id d))
          (fun hl => by
            rw [(finish_keeps_ty (issueCall (w.st id)) kC .notAdmitted).2] at hl
            simpa [issueCall] using hl)
          (fun _ => by
            rw [(finish_keeps_ty (issueCall (w.st id)) kC .notAdmitted).1]
            exact select_state_named I hL id (issueCall (w.st id)) kC .notAdmitted
              (src_ty I id kC (by simp [issueCall]) hsrcC))
      | some dstId =>
        simp only [execRun, hgo, hk, hr, ite_true]
        by_cases hlive : (w.st dstId).life = .alive
        · exact good_frame hG (enqueue_admitted_frame w I.desc id dstId _
            { afterHead k with onNotAdmitted := na, onTimedOut := to } hlive)
        · exact enqueue_refused_good I hL w id dstId _
            { afterHead k with onNotAdmitted := na, onTimedOut := to } hG hsrcC hlive
    | reply =>
      simp only [execRun, hgo, hk, ite_true]
      exact good_frame hG (frame_reply I w id k h hph)
    | selfSchedule label =>
      simp only [execRun, hgo, hk, ite_true]
      split
      · exact good_frame hG (hproc w _ rfl hty')
      · split
        · exact good_frame hG (frame_keep w id _ (proceed_life _ _) (proceed_keeps_ty _ _ hty'))
        · exact good_frame hG (frame_crash w)
    | cell dst label value =>
      simp only [execRun, hgo, hk, ite_true]
      have hF : Frame w (setActor (setCell w dst label { value := max (w.cell dst label).value value, dirty := true })
          id (proceed ((setCell w dst label
            { value := max (w.cell dst label).value value, dirty := true }).st id) (afterHead k))) :=
        frame_trans (frame_same (same_setCell w dst label _)) (hproc _ _ rfl hty')
      split
      · exact good_frame hG hF
      · exact good_frame hG (frame_trans hF (frame_wake I.desc _ dst label id))
    | internal =>
      simp only [execRun, hgo, hk, ite_true]
      exact good_frame hG (frame_keep w id _ rfl rfl)
    | peer o =>
      simp only [execRun, hgo, hk, ite_true]
      exact good_frame hG (frame_keep w id _ rfl rfl)
    | abort =>
      simp only [execRun, hgo, hk, ite_true, commitCont]
      by_cases hcr : (abortChildren I.desc w id).crashed = true
      · rw [ite_eq_left hcr]
        exact good_frame hG (frame_abort I I.desc w id h)
      · rw [ite_eq_right hcr]
        exact good_frame hG (frame_trans (frame_abort I I.desc w id h)
          (frame_set (abortChildren I.desc w id) id
            (proceed ((abortChildren I.desc w id).st id) (afterHead k)) (fun hl => by
              have hlife : ((abortChildren I.desc w id).st id).life = .alive :=
                (proceed_life _ _).symm.trans hl
              have htyW := (frame_abort I I.desc w id h id hlife).2
              exact ⟨hlife, proceed_keeps_ty _ _ (htyW.trans hty')⟩)))
    | terminate =>
      have hstep := exec_term_step I w id (w.st id) k ha ⟨es, hk⟩
      generalize execRun I w id (w.st id) k = wR at hstep ⊢
      cases hstep with
      | fall => exact good_frame hG (frame_crash w)
      | crash _ _ _ => exact good_frame hG (frame_crash w)
      | lone _ _ _ _ _ _ _ => exact good_frame hG (frame_shutdown I.desc w id h.1.cont)
      | tree _ _ _ _ => exact good_frame hG (frame_terminate I I.desc w id _ h)
      | cascade _ _ _ _ _ _ _ => exact good_frame hG (frame_terminate I I.desc w id _ h)
    | spawn child =>
      cases hsp : spawnChild I w id child with
      | none =>
        simp only [execRun, hgo, hk, hsp, ite_true]
        exact good_frame hG (frame_crash w)
      | some w' =>
        simp only [execRun, hgo, hk, hsp, ite_true, commitCont]
        by_cases hcr : w'.crashed = true
        · rw [ite_eq_left hcr]
          exact spawnChild_good I hGr w w' id child hG hsp
        · rw [ite_eq_right hcr]
          have hst := spawnChild_other_st I w w' id child id hsp (h.1.rostered id ha)
          exact good_frame (spawnChild_good I hGr w w' id child hG hsp)
            (frame_keep w' id _ (proceed_life _ _) (by rw [hst]; exact proceed_keeps_ty _ _ hty'))

theorem head_good (I : Impl) (hL : LocalOk I) (hGr : GraphOk I.desc) (w w' : World) (id : InstId)
    (h : Inv I w) (hG : Good I.desc w) (hs : execHead I w id = some w') : Good I.desc w' := by
  unfold execHead at hs
  dsimp only at hs
  split at hs
  · cases hs
  · split at hs
    · next k hph =>
      cases hs
      exact exec_good I hL hGr w id k h hG hph
    · cases hs

theorem finish_good (I : Impl) (w w' : World) (id : InstId) (h : Inv I w) (hG : Good I.desc w)
    (hs : finishWait I w id = some w') : Good I.desc w' := by
  obtain ⟨k, hph, hw'⟩ := finish_proceed I w w' id hs
  subst hw'
  have hty : (w.st id).typestate = k.toState := by
    rcases hph with hph | hph <;> simpa [contTy, hph] using h.1.cont id
  exact good_frame hG (frame_keep w id _ (proceed_life _ _) (proceed_keeps_ty _ _ hty))

theorem ingress_good (I : Impl) (w w' : World) (dst : InstId) (label : String) (hG : Good I.desc w)
    (hs : receiveIngress I w dst label = some w') : Good I.desc w' :=
  good_frame hG (frame_fields w w' fun i =>
    ⟨(ingress_phase I w w' dst label i hs).2.1, ingress_ty_eq I w w' dst label i hs⟩)

theorem callTimeout_good (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (h : Inv I w)
    (hG : Good I.desc w) (hs : callTimeout w id = some w') : Good I.desc w' := by
  have hO := h.2.2.2.1 id
  have hC := h.1.cont id
  unfold callTimeout at hs
  dsimp only at hs
  split at hs
  · cases hs
  · split at hs
    · next dst k hph =>
      cases hs
      have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hC
      unfold outcomeOk at hO
      rw [hph] at hO
      have hr := detachHost_rest (w.st dst) id (w.st id).waitId
      have hF1 := frame_keep w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId) hr.2.1 hr.1
      have hW : ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id).typestate =
          k.toState := by
        by_cases hd : id = dst
        · subst hd
          rw [setActor_self]
          exact hr.1.trans hty
        · rw [setActor_other _ _ _ _ hd]
          exact hty
      have hfin := finish_keeps_ty ((setActor w dst
        (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id) k .timedOut
      have hs1 := src_ty I id k (hW.trans hty.symm) hO.1
      exact good_set id _ (good_frame hG hF1) (fun hl => hfin.2.symm.trans hl)
        (fun _ => by
          rw [hfin.1]
          exact select_state_named I hL id _ k .timedOut hs1)
    · next dst k hph =>
      cases hs
      have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hC
      unfold outcomeOk at hO
      rw [hph] at hO
      have hF1 : Frame w (refundParkedCall w id dst) := frame_fields w _ fun i =>
        ⟨(refundCall_fields w id dst i).2.1, (refundCall_fields w id dst i).2.2.1⟩
      have hfin := finish_keeps_ty ((refundParkedCall w id dst).st id) k .notAdmitted
      have hs1 := src_ty I id k (refundCall_fields w id dst id).2.2.1 hO.1
      exact good_set id _ (good_frame hG hF1) (fun hl => hfin.2.symm.trans hl)
        (fun _ => by
          rw [hfin.1]
          exact select_state_named I hL id _ k .notAdmitted hs1)
    · next k hph =>
      cases hs
      have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hC
      unfold outcomeOk at hO
      rw [hph] at hO
      let k' := picked k k.onTimeout k.toTimeout
      exact good_set id (proceed (w.st id) k') hG
        (fun hl => (proceed_life (w.st id) k').symm.trans hl)
        (fun _ => by
          rw [proceed_writes]
          simp only [k', picked]
          exact pick_state_named I hL id (w.st id) k k.toTimeout hO.1
            (Or.inr (Or.inr (Or.inl rfl))))
    · cases hs

theorem deliver_decl (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w' : World) (a' : Actor) (hs : (statesOf I.desc (tname id)).elem a.typestate = true)
    (h : deliver I w id a m = some (w', a')) : (statesOf I.desc (tname id)).elem a'.typestate = true := by
  unfold deliver at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
      exact hs
    · split at h
      · split at h
        · cases h
        · cases h
          exact hs
      · next tr htr =>
        split at h
        · cases h
        · cases h
          have hfm := findDeliver_mem I (tname id) a.typestate m tr htr
          have hele := to_mem I hL tr hfm.1
          rw [hfm.2.1] at hele
          split <;> exact hele

/-- The receiver after a delivery: still live, in a declared typestate, and every
continuation still matches its typestate. -/
theorem good_install (I : Impl) (hL : LocalOk I) (w : World) (id : InstId)
    (a0 : Actor) (m : Msg) (w1 : World) (a1 : Actor) (h : Inv I w) (hG : Good I.desc w)
    (halive : (w.st id).life = .alive) (hl : a0.life = (w.st id).life) (ht : a0.typestate = (w.st id).typestate)
    (hd : deliver I w id a0 m = some (w1, a1)) :
    Good I.desc w1 ∧ (∀ i, w1.st i = w.st i) ∧ a1.life = .alive ∧
      (statesOf I.desc (tname id)).elem a1.typestate = true ∧ ∀ i, contTy ((setActor w1 id a1).st i) := by
  have hok := deliver_ok I hL w id a0 m w1 a1 h.1 hl ht hd
  refine ⟨good_frame hG (frame_st w w1 hok.st), hok.st, hok.life.trans (hl.trans halive),
    deliver_decl I hL w id a0 m w1 a1 (by rw [ht]; exact hG.1 id halive) hd, hok.sem.cont⟩

theorem good_resume (D : Description) (w : World) (tmpl : String) (s p dst : InstId) (b : Bool)
    (hG : Good D w) (hC : ∀ i, contTy (w.st i)) :
    Good D (setActor (creditSender w tmpl s) p (resumeSender ((creditSender w tmpl s).st p) b dst)) := by
  have hc := cont_credit w tmpl s hC p
  obtain ⟨hty, hl⟩ := resume_keeps _ b dst hc
  exact good_frame hG (frame_trans (frame_credit w tmpl s) (frame_keep _ p _ hl hty))

theorem receive_bulk_good (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (h : Inv I w) (hG : Good I.desc w) (hs : receiveBulk I w id = some w') : Good I.desc w' := by
  unfold receiveBulk at hs
  dsimp only at hs
  split at hs
  · cases hs
  · next hready =>
    have halive : (w.st id).life = .alive := by
      by_cases hl : (w.st id).life = .alive
      · exact hl
      · simp [hl] at hready
    split at hs
    · split at hs
      · cases hs
      · next w1 a1 hd =>
        cases hs
        obtain ⟨hG1, hst, hl1, ht1, _⟩ := good_install I hL w id _ _ w1 a1 h hG halive (by rfl) (by rfl) hd
        exact good_frame (good_set id a1 hG1 (fun _ => by rw [hst]; exact halive) (fun _ => ht1))
          (frame_credit _ _ _)
    · split at hs
      · cases hs
      · next w1 a1 hd =>
        cases hs
        obtain ⟨hG1, hst, hl1, ht1, hC1⟩ := good_install I hL w id _ _ w1 a1 h hG halive (by rfl) (by rfl) hd
        refine good_resume I.desc _ _ _ _ _ _ ?_ ?_
        · exact good_set id _ hG1 (fun _ => by rw [hst]; exact halive) (fun _ => ht1)
        · intro i
          by_cases hi : i = id
          · subst hi
            rw [setActor_self]
            have hc := hC1 i
            rw [setActor_self] at hc
            exact contTy_congr rfl rfl hc
          · rw [setActor_other _ _ _ _ hi]
            have hc := hC1 i
            rw [setActor_other _ _ _ _ hi] at hc
            exact hc
    · split at hs
      · cases hs
      · next w1 a1 hd =>
        cases hs
        obtain ⟨hG1, hst, hl1, ht1, hC1⟩ := good_install I hL w id _ _ w1 a1 h hG halive (by rfl) (by rfl) hd
        exact good_resume I.desc _ _ _ _ _ _
          (good_set id a1 hG1 (fun _ => by rw [hst]; exact halive) (fun _ => ht1)) hC1
    · cases hs

theorem receive_prio_good (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (h : Inv I w) (hG : Good I.desc w) (hs : receivePrio I w id = some w') : Good I.desc w' := by
  obtain ⟨m, pre, suf, w1, a1, hlife, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id hs
  subst hw'
  obtain ⟨hG1, hst, _, ht1, _⟩ := good_install I hL w id _ m w1 a1 h hG hlife (by rfl) (by rfl) hdel
  exact good_set id a1 hG1 (fun _ => by rw [hst]; exact hlife) (fun _ => ht1)

theorem peer_init (I : Impl) (N : Nat) : PeerOk I.desc (initWorld I N) := by
  intro n k g hl
  rw [init_base_st] at hl
  have hc : (coreRoster I.desc).contains (InstId.peer n k g) = false := by
    simp [coreRoster]
  rw [hc] at hl
  simp [absentActor] at hl

theorem good_step (I : Impl) (hL : LocalOk I) (hGr : GraphOk I.desc) (w w' : World)
    (a : Action) (h : Inv I w) (hG : Good I.desc w) (ha : apply I a w = some w') : Good I.desc w' := by
  have hs := (apply_step I a w w' ha).2
  cases a with
  | recvBulk id => exact receive_bulk_good I hL w w' id h hG hs
  | recvPrio id => exact receive_prio_good I hL w w' id h hG hs
  | exec id => exact head_good I hL hGr w w' id h hG hs
  | finish id => exact finish_good I w w' id h hG hs
  | spawn template => exact spawn_good I hGr w w' template hG hs
  | ingress dst label => exact ingress_good I w w' dst label hG hs
  | callTimeout id => exact callTimeout_good I hL w w' id h hG hs
  | stutter =>
    cases stutter_unchanged I w w' ha
    exact hG

theorem good_reachable (I : Impl) (hL : LocalOk I) (hGr : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) : Good I.desc w := by
  induction hR with
  | init => exact ⟨ty_init I hGr N, peer_init I N⟩
  | step w0 _ _ hR0 ha ih => exact good_step I hL hGr w0 _ _ (inv_reachable I N w0 hL hR0) ih ha

theorem ty_step (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w w' : World) (a : Action) (hR : Reachable I N w) (h : apply I a w = some w') (hT : TyOk I.desc w) :
    TyOk I.desc w' :=
  (good_step I hL hG w w' a (inv_reachable I N w hL hR) ⟨hT, (good_reachable I hL hG N w hR).2⟩ h).1

theorem ty_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) : TyOk I.desc w :=
  (good_reachable I hL hG N w hR).1

theorem peer_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) : PeerOk I.desc w :=
  (good_reachable I hL hG N w hR).2

/-- A live actor of a multiplicity-one template is that template's core. -/
theorem alive_is_core (D : Description) (w : World) (hP : PeerOk D w) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hmul : t.multiplicity = .one)
    (id : InstId) (hn : tname id = name) (hl : (w.st id).life = .alive) : id = InstId.core name := by
  cases id with
  | core n =>
    simp [tname] at hn
    rw [hn]
  | peer n k g =>
    simp [tname] at hn
    subst hn
    obtain ⟨t', ht', hm'⟩ := hP n k g hl
    rw [ht] at ht'
    cases ht'
    rw [hmul] at hm'
    cases hm'
theorem refundCall_ix (w : World) (caller dst : InstId) (name : String) :
    (refundParkedCall w caller dst).nextIx name = w.nextIx name := by
  unfold refundParkedCall
  dsimp only
  split
  · rfl
  · let keep := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall)
    have hbase : (setActor w dst { (w.st dst) with parked := keep }).nextIx name = w.nextIx name := by
      simp [setActor]
    suffices ∀ (ps : List Parked) (w0 : World), w0.nextIx name = w.nextIx name →
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).nextIx name = w.nextIx name from
      this ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall)
        (setActor w dst { (w.st dst) with parked := keep }) hbase
    intro ps
    induction ps with
    | nil => intro w0 h; exact h
    | cons p ps ih =>
      intro w0 h
      simp only [List.foldl_cons]
      exact ih (creditSender w0 (tname dst) caller) (by simpa [creditSender, setActor] using h)

theorem fold_keep (acc xs : List String) (x : String) (h : x ∈ acc ∨ x ∈ xs) :
    x ∈ xs.foldl (fun acc y => if acc.elem y then acc else acc ++ [y]) acc := by
  induction xs generalizing acc with
  | nil =>
    simp at h
    simpa using h
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases he : (acc.elem y) = true
    · simp only [he, ite_true]
      apply ih
      cases h with
      | inl hx => exact Or.inl hx
      | inr hxs =>
        cases List.mem_cons.mp hxs with
        | inl heq =>
          subst heq
          exact Or.inl (List.elem_iff.mp he)
        | inr ht => exact Or.inr ht
    · have hf : acc.elem y = false := by
        cases hbb : acc.elem y <;> simp_all
      simp only [hf]
      apply ih
      cases h with
      | inl hx => exact Or.inl (List.mem_append_left _ hx)
      | inr hxs =>
        cases List.mem_cons.mp hxs with
        | inl heq =>
          subst heq
          exact Or.inl (List.mem_append_right _ (by simp))
        | inr ht => exact Or.inr ht

theorem mem_dedup (xs : List String) (x : String) (h : x ∈ xs) : x ∈ dedup xs := by
  simpa [dedup] using fold_keep [] xs x (Or.inr h)

theorem co_mem (g : CompatGroup) (src ss dst ds : String) (a : List RoleState) (ha : a ∈ g.allowed)
    (hs : lookupRole a src = some ss) (hd : lookupRole a dst = some ds) : ds ∈ coStates g src ss dst := by
  have hf : (if lookupRole a src == some ss then lookupRole a dst else none) = some ds := by
    simp [hs, hd]
  have hmap := filter_some (fun tup => if lookupRole tup src == some ss then lookupRole tup dst else none)
    g.allowed ds a ha hf
  simpa [coStates] using mem_dedup _ ds hmap

theorem fold_targets (src ss dst ds : String) (rest : List CompatGroup) (acc : List String)
    (hacc : ds ∈ acc) (hrest : ∀ g ∈ rest, ds ∈ coStates g src ss dst) :
    ds ∈ rest.foldl (fun acc g => listInter acc (coStates g src ss dst)) acc := by
  induction rest generalizing acc with
  | nil => simpa using hacc
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact (listInter_elem acc (coStates g src ss dst) ds).mpr
        ⟨hacc, List.elem_iff.mpr (hrest g (List.mem_cons_self))⟩
    · intro g' hg
      exact hrest g' (List.mem_cons_of_mem _ hg)

theorem in_targets (gs : List CompatGroup) (src ss dst ds : String)
    (hcover : ∃ g, g ∈ gs ∧ g.roles.elem src = true ∧ g.roles.elem dst = true)
    (hall : ∀ g ∈ gs, g.roles.elem src = true → g.roles.elem dst = true → ds ∈ coStates g src ss dst) :
    ds ∈ groupTargets gs src ss dst := by
  unfold groupTargets
  cases hf : gs.filter fun g => g.roles.elem src && g.roles.elem dst with
  | nil =>
    obtain ⟨g, hg, hs, hd⟩ := hcover
    have hbool : (g.roles.elem src && g.roles.elem dst) = true := by
      rw [hs, hd]
      rfl
    have hmem : g ∈ gs.filter fun g => g.roles.elem src && g.roles.elem dst :=
      List.mem_filter.mpr ⟨hg, hbool⟩
    rw [hf] at hmem
    cases hmem
  | cons g rest =>
    simp
    apply fold_targets
    · have hg : g ∈ gs.filter fun g => g.roles.elem src && g.roles.elem dst := by
        rw [hf]
        exact List.mem_cons_self
      have hm := List.mem_filter.mp hg
      have hpair : g.roles.elem src = true ∧ g.roles.elem dst = true := by
        simpa [Bool.and_eq_true] using hm.2
      exact hall g hm.1 hpair.1 hpair.2
    · intro h hh
      have hmem : h ∈ g :: rest := List.mem_cons_of_mem _ hh
      rw [← hf] at hmem
      have hm := List.mem_filter.mp hmem
      have hpair : h.roles.elem src = true ∧ h.roles.elem dst = true := by
        simpa [Bool.and_eq_true] using hm.2
      exact hall h hm.1 hpair.1 hpair.2

theorem uncovered_nil (D : Description) (gs : List CompatGroup) (h : compatFails D = [])
    (hc : D.compatibility = .groups gs) : uncoveredEdges D gs = [] := by
  unfold compatFails at h
  simp only [hc] at h
  exact append_nil_right h

theorem edge_covered (D : Description) (gs : List CompatGroup) (e : Edge) (h : uncoveredEdges D gs = [])
    (he : e ∈ D.edges) (hk : e.kind = .blocking) :
    ∃ g ∈ gs, g.roles.elem e.src = true ∧ g.roles.elem e.dst = true := by
  unfold uncoveredEdges at h
  have hf := filterMap_mem_none _ D.edges e h he
  rw [hk] at hf
  have hnot : (EdgeKind.blocking != EdgeKind.blocking) = false := by decide
  simp [hnot] at hf
  obtain ⟨g, hg, hs, hd⟩ := hf
  exact ⟨g, hg, List.elem_iff.mpr hs, List.elem_iff.mpr hd⟩

theorem partner_mem (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (e : Edge) (he : e ∈ I.desc.edges) (hk : e.kind = .blocking)
    (id dst : InstId) (hsrc : e.src = tname id) (hss : e.srcState = (w.st id).typestate)
    (hdstn : e.dst = tname dst) (hbusy : (w.st id).phase ≠ .idle) (hcr : (w.st id).phase ≠ .crashed) :
    discharged I.desc e = true ∨
      ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e) := by
  cases hmode : I.desc.compatibility with
  | explicit _ =>
    have hempty := compat_empty_of_local I hL
    simp [compatFails, hmode] at hempty
  | all =>
    refine Or.inr ?_
    intro hl
    have hT := ty_reachable I hL hG N w hR
    have hele := hT dst hl
    rw [← hdstn] at hele
    simpa [targetStates, hmode] using List.elem_iff.mp hele
  | groups gs =>
    refine Or.inr ?_
    intro hl
    have hI := inv_reachable I N w hL hR
    have hP := peer_reachable I hL hG N w hR
    have hun := uncovered_nil I.desc gs (compat_empty_of_local I hL) hmode
    obtain ⟨g0, hg0, hs0, hd0⟩ := edge_covered I.desc gs e hun he hk
    have hgGroup : g0 ∈ compatGroups I.desc.compatibility := by simp [compatGroups, hmode, hg0]
    have hwell := (compat_group_closed I.desc g0 (compat_empty_of_local I hL) hgGroup).1
    obtain ⟨tS, htS, hmS, _, _⟩ := role_static I.desc g0 e.src hwell (List.elem_iff.mp hs0)
    obtain ⟨tD, htD, hmD, _, _⟩ := role_static I.desc g0 e.dst hwell (List.elem_iff.mp hd0)
    have hcoreS : id = InstId.core e.src :=
      alive_is_core I.desc w hP e.src tS htS hmS id hsrc.symm (busy_alive I w hI.1 id hbusy hcr)
    have hcoreD : dst = InstId.core e.dst := alive_is_core I.desc w hP e.dst tD htD hmD dst hdstn.symm hl
    have hmem := in_targets gs e.src e.srcState e.dst (w.st dst).typestate ⟨g0, hg0, hs0, hd0⟩ ?_
    simpa [targetStates, hmode] using hmem
    · intro g hg hs hd
      have hgG : g ∈ compatGroups I.desc.compatibility := by simp [compatGroups, hmode, hg]
      have htup := (hI.1.live g hgG).1
      have hraw := row_mem I hL g hgG htup
      obtain ⟨a, ha, hag⟩ := tupleMem_pick g.allowed (roleTuple w g) hraw
      have hlookS := lookup_roleTuple w g e.src (List.elem_iff.mp hs)
      have hss' : lookupRole (roleTuple w g) e.src = some e.srcState := by
        rw [hlookS, ← hcoreS, ← hss]
      have hagreeS := tuple_agree a (roleTuple w g) hag e.src e.srcState hss'
      have hlookD := lookup_roleTuple w g e.dst (List.elem_iff.mp hd)
      have hds : lookupRole (roleTuple w g) e.dst = some (w.st dst).typestate := by
        rw [hlookD, ← hcoreD]
      have hagreeD := tuple_agree a (roleTuple w g) hag e.dst (w.st dst).typestate hds
      exact co_mem g e.src e.srcState e.dst (w.st dst).typestate a ha hagreeS hagreeD

/-- A parked actor waits on a blocking edge that is discharged, or whose live
partner typestate is one `targetStates` still draws. -/
theorem projects_park (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id dst : InstId) (isCall : Bool) (k : Cont)
    (hph : (w.st id).phase = .parked dst isCall k) :
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧
      e.effect = (if isCall then EffectKind.call else EffectKind.send) ∧ e.label = label ∧
      (discharged I.desc e = true ∨
        ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e)) := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab⟩ :=
    described_park I w hI id dst isCall k hph
  have hpart := partner_mem I hL hG N w hR e he hkind id dst hsrc hss hdstn
    (by rw [hph]; intro hbad; cases hbad) (by rw [hph]; intro hbad; cases hbad)
  exact ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab, hpart⟩

/-- An actor awaiting a reply waits on a blocking call edge with the same filter. -/
theorem projects_reply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hph : (w.st id).phase = .awaitReply dst k) :
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧ e.effect = EffectKind.call ∧ e.label = label ∧
      (discharged I.desc e = true ∨
        ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e)) := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab⟩ := described_reply I w hI id dst k hph
  have hpart := partner_mem I hL hG N w hR e he hkind id dst hsrc hss hdstn
    (by rw [hph]; intro hbad; cases hbad) (by rw [hph]; intro hbad; cases hbad)
  exact ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab, hpart⟩

/-- Both waits of `Deadlock` that name a partner. -/
def Projects (I : Impl) (w : World) : Prop :=
  (∀ id dst isCall k, (w.st id).phase = .parked dst isCall k →
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧
      e.effect = (if isCall then EffectKind.call else EffectKind.send) ∧ e.label = label ∧
      (discharged I.desc e = true ∨
        ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e))) ∧
  (∀ id dst k, (w.st id).phase = .awaitReply dst k →
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧ e.effect = EffectKind.call ∧ e.label = label ∧
      (discharged I.desc e = true ∨
        ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e)))

theorem projects (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) : Projects I w :=
  ⟨fun id dst isCall k hph => projects_park I hL hG N w hR id dst isCall k hph,
   fun id dst k hph => projects_reply I hL hG N w hR id dst k hph⟩

end Deadlock
