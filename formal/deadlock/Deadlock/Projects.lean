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
    exact ih (creditSender w dst m.sender) (tyOk_credit D w dst m.sender hT)

theorem refund_park_ty (D : Description) (w : World) (dst : String) (ps : List Parked) (hT : TyOk D w) :
    TyOk D (refundParked w dst ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hT
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih (creditSender w dst p.msg.sender) (tyOk_credit D w dst p.msg.sender hT)

theorem refund_msgs_cont (w : World) (dst : String) (ms : List Msg) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((refundMsgs w dst ms).st i) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using hC
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact ih (creditSender w dst m.sender) (cont_credit w dst m.sender hC)

theorem refund_park_cont (w : World) (dst : String) (ps : List Parked) (hC : ∀ i, contTy (w.st i)) :
    ∀ i, contTy ((refundParked w dst ps).st i) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hC
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih (creditSender w dst p.msg.sender) (cont_credit w dst p.msg.sender hC)

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

theorem try_ty (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (hT : TyOk D w) : TyOk D (tryWake D w dstId label writer) := by
  simp only [tryWake]
  split
  · exact tyOk_id D w dstId _ hT (by simp) (by simp)
  · exact hT

theorem wake_ty (D : Description) (w : World) (dst label : String) (writer : InstId) (hT : TyOk D w) :
    TyOk D (wakeReaders D w dst label writer) := by
  unfold wakeReaders
  induction readersOf w dst generalizing w with
  | nil => simpa using hT
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih (tryWake D w i label writer) (try_ty D w i label writer hT)

theorem enqueue_ty (D : Description) (w : World) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (hT : TyOk D w) (hty : (w.st sender).typestate = k.toState) :
    TyOk D (enqueueOrPark w D sender dst msg isCall k) := by
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · simp [halive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        if hcall : isCall = true then
          simp [hcall]
          apply tyOk_id
          · exact hT
          · simp [chargeSender, bumpToken]
          · simp [chargeSender, bumpToken]
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          apply tyOk_id
          · exact hT
          · cases hr : k.rest <;> simp [proceed, hr, chargeSender, bumpToken, hty]
          · cases hr : k.rest <;> simp [proceed, hr, chargeSender, bumpToken]
      · simp [hsame]
        if hcall : isCall = true then
          simp [hcall]
          apply tyOk_id
          · apply tyOk_id
            · exact hT
            · rfl
            · exact halive.symm
          · rw [setActor_other _ dst sender _ hsame]
            simp [chargeSender, bumpToken]
          · rw [setActor_other _ dst sender _ hsame]
            simp [chargeSender, bumpToken]
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          apply tyOk_id
          · apply tyOk_id
            · exact hT
            · rfl
            · exact halive.symm
          · rw [setActor_other _ dst sender _ hsame]
            cases hr : k.rest <;> simp [proceed, hr, chargeSender, bumpToken, hty]
          · rw [setActor_other _ dst sender _ hsame]
            cases hr : k.rest <;> simp [proceed, hr, chargeSender, bumpToken]
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        simp
        apply tyOk_id
        · exact hT
        · simp [chargeSender, bumpToken]
        · simp [chargeSender, bumpToken]
      · simp [hsame]
        apply tyOk_id
        · apply tyOk_id
          · exact hT
          · rfl
          · exact halive.symm
        · rw [setActor_other _ dst sender _ hsame]
          simp [chargeSender, bumpToken]
        · rw [setActor_other _ dst sender _ hsame]
          simp [chargeSender, bumpToken]
  · simp [halive]
    exact tyOk_proceed D w sender k hT hty

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
        have hT1 := tyOk_proceed D w caller ck hT htyC
        by_cases hsc : caller = sender
        · subst hsc
          apply tyOk_proceed
          · exact hT1
          · rw [setActor_self, proceed_keeps_ty _ _ htyC]
            simp [afterHead, hty]
        · apply tyOk_proceed
          · exact hT1
          · rw [setActor_other _ caller sender _ (Ne.symm hsc)]
            exact hty'
      · exact tyOk_proceed D w sender (afterHead k) hT hty'
    · exact tyOk_proceed D w sender (afterHead k) hT hty'

theorem exec_ty (I : Impl) (w : World) (id : InstId) (k : Cont) (hT : TyOk I.desc w)
    (hS : SemInv I w) (hph : (w.st id).phase = .run k) :
    TyOk I.desc (execRun I w id (w.st id) k) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
  have hC : ∀ i, contTy (w.st i) := hS.cont
  cases hk : k.rest with
  | nil =>
    simp [execRun, hk]
    exact tyOk_id I.desc w id _ hT (by simp [hty]) (by simp)
  | cons e es =>
    cases e with
    | internal =>
      simp [execRun, hk]
      exact tyOk_id I.desc w id _ hT (by simp) (by simp)
    | peer =>
      simp [execRun, hk]
      exact tyOk_id I.desc w id _ hT (by simp) (by simp)
    | send d l n =>
      cases hr : route w I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        exact tyOk_proceed I.desc w id (afterHead k) hT (by simp [afterHead, hty])
      | some dst =>
        simp [execRun, hk, hr]
        exact enqueue_ty I.desc w id dst _ false (afterHead k) hT (by simp [afterHead, hty])
    | call d l n =>
      cases hr : route w I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        exact tyOk_proceed I.desc w id (afterHead k) hT (by simp [afterHead, hty])
      | some dst =>
        simp [execRun, hk, hr]
        exact enqueue_ty I.desc w id dst _ true (afterHead k) hT (by simp [afterHead, hty])
    | trySend d l n =>
      cases hr : route w I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        exact tyOk_proceed I.desc w id (afterHead k) hT (by simp [afterHead, hty])
      | some dst =>
        simp [execRun, hk, hr]
        split
        · exact enqueue_ty I.desc w id dst _ false (afterHead k) hT (by simp [afterHead, hty])
        · exact tyOk_proceed I.desc w id (afterHead k) hT (by simp [afterHead, hty])
    | reply =>
      simp [execRun, hk]
      exact perform_ty I.desc w id k hT hC hty
    | selfSchedule _ =>
      simp [execRun, hk]
      split
      · exact tyOk_proceed I.desc w id (afterHead k) hT (by simp [afterHead, hty])
      · split
        · apply tyOk_id
          · exact hT
          · cases es with
            | nil => simp [proceed, hk, afterHead, hty]
            | cons _ _ => simp [proceed, hk, afterHead, hty]
          · cases es with
            | nil => simp [proceed, hk, afterHead]
            | cons _ _ => simp [proceed, hk, afterHead]
        · apply tyOk_id
          · exact hT
          · simp
          · simp
    | cell dst label value =>
      simp [execRun, hk, setCell]
      split
      · exact tyOk_proceed I.desc _ id (afterHead k)
          (tyOk_cell I.desc w dst label { value := max (w.cell dst label).value value, dirty := true } hT)
          (by
            simp only [setCell]
            simp [afterHead, hty])
      · exact wake_ty I.desc _ dst label id
          (tyOk_proceed I.desc _ id (afterHead k)
            (tyOk_cell I.desc w dst label { value := max (w.cell dst label).value value, dirty := true } hT)
            (by
              simp only [setCell]
              simp [afterHead, hty]))
    | terminate =>
      simp [execRun, hk]
      split
      · next t ht =>
        split
        · let wR := readCells I.desc w id
          let wM := refundMsgs wR (tname id) (w.st id).box
          let wP := refundParked wM (tname id) (w.st id).parked
          let dead : Actor :=
            { (wP.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
          have hT1 := tyOk_read I.desc w id hT
          have hT2 := refund_msgs_ty I.desc wR (tname id) (w.st id).box hT1
          have hT3 := refund_park_ty I.desc wM (tname id) (w.st id).parked hT2
          have hT4 := tyOk_new I.desc wP id dead hT3 (by intro hl; simp [dead] at hl)
          have hC1 := cont_read I.desc w id hC
          have hC2 := refund_msgs_cont wR (tname id) (w.st id).box hC1
          have hC3 := refund_park_cont wM (tname id) (w.st id).parked hC2
          have hC4 := cont_after wP id dead hC3 (by simp [dead, contTy])
          have hrel := release_ty I.desc (setActor wP id dead) id (w.st id).parked hT4 hC4
          simpa [wR, wM, wP, dead, ht] using hrel
        · exact hT
      · exact hT

theorem to_mem (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    (statesOf I.desc tr.template).elem tr.toState = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some t =>
    simp only [transitionOk, ht] at hok
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    simpa [statesOf, ht] using hok.2

theorem deliver_ty_mem (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w' : World) (a' : Actor) (hT : TyOk I.desc w) (hlife : a.life = (w.st id).life)
    (hty : a.typestate = (w.st id).typestate) (halive : a.life = .alive)
    (h : deliver I w id a m = some (w', a')) :
    (statesOf I.desc (tname id)).elem a'.typestate = true ∧ a'.life = .alive := by
  unfold deliver at h
  simp [halive] at h
  cases hf : findTr I (tname id) a.typestate m.label with
  | none =>
    by_cases hc : m.callFrom.isSome = true
    · simp [hf, hc] at h
    · have hc' : m.callFrom.isSome = false := by
        cases hsome : m.callFrom.isSome
        · rfl
        · exact False.elim (hc hsome)
      simp [hf, hc'] at h
      refine ⟨?_, ?_⟩
      · rw [← h.2, hty]
        exact hT id (by rw [← hlife]; exact halive)
      · rw [← h.2]
  | some tr =>
    simp only [hf] at h
    by_cases href : m.callFrom.isSome = true ∧ tr.acceptsCall = false
    · rw [if_pos href] at h
      cases h
    · rw [if_neg href] at h
      cases h
      have hmem := findTr_mem I (tname id) a.typestate m.label tr hf
      have hele := to_mem I hL tr hmem.1
      refine ⟨?_, ?_⟩
      · cases hp : tr.program <;> (simp [← hmem.2.1]; exact List.elem_iff.mp hele)
      · cases hp : tr.program <;> simp [halive]

theorem receive_prio_ty (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (w' : World)
    (hT : TyOk I.desc w) (h : receivePrio I w id = some w') : TyOk I.desc w' := by
  have hready := prio_ready I w id w' h
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp only [hp, hready.1, hready.2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := (w.st id).box, prio := ms,
          parked := (w.st id).parked, tokens := (w.st id).tokens, nextMid := (w.st id).nextMid }
        have hmem := deliver_ty_mem I hL w id a0 m w1 a1 hT hready.1.symm rfl rfl hd
        exact tyOk_new I.desc w1 id a1 (tyOk_st I.desc w w1 hT (fun i => deliver_st I w id a0 m w1 a1 i hd))
          (fun _ => hmem.1)

theorem install_ty (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a0 : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (hT : TyOk I.desc w) (hlife : a0.life = (w.st id).life)
    (hty : a0.typestate = (w.st id).typestate) (halive : a0.life = .alive)
    (hd : deliver I w id a0 m = some (w1, a1)) : TyOk I.desc (setActor w1 id a1) := by
  have hmem := deliver_ty_mem I hL w id a0 m w1 a1 hT hlife hty halive hd
  exact tyOk_new I.desc w1 id a1 (tyOk_st I.desc w w1 hT (fun i => deliver_st I w id a0 m w1 a1 i hd))
    (fun _ => hmem.1)

theorem receive_bulk_ty (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (wOut : World)
    (hT : TyOk I.desc w) (hS : SemInv I w) (hM : MailInv w) (h : receiveBulk I w id = some wOut) :
    TyOk I.desc wOut := by
  have hready := receive_ready I w id wOut h
  unfold receiveBulk at h
  simp only [hready.1, hready.2] at h
  cases hbox : (w.st id).box with
  | nil =>
    cases hpk : (w.st id).parked with
    | nil => simp [hbox, hpk] at h
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := [], prio := (w.st id).prio,
          parked := ps, tokens := (w.st id).tokens, nextMid := (w.st id).nextMid }
        have hT1 := install_ty I hL w id a0 p.msg w1 a1 hT hready.1.symm rfl rfl hd
        have hT2 := tyOk_credit I.desc _ (tname id) p.msg.sender hT1
        have hfree : notParked (w.st id).phase := by simp [hready.2, notParked]
        have hsnd : p.sender ≠ id :=
          not_queued w id hM hfree id p (by rw [hpk]; exact List.mem_cons_self)
        let credited := creditSender (setActor w1 id a1) (tname id) p.msg.sender
        have hphS : (credited.st p.sender).phase = (w.st p.sender).phase := by
          rw [(credit_phase (setActor w1 id a1) (tname id) p.msg.sender p.sender).1,
            setActor_other w1 id p.sender a1 hsnd, deliver_st I w id a0 p.msg w1 a1 p.sender hd]
        have htyS : (credited.st p.sender).typestate = (w.st p.sender).typestate := by
          rw [(credit_keeps_ty (setActor w1 id a1) (tname id) p.msg.sender p.sender).2,
            setActor_other w1 id p.sender a1 hsnd, deliver_st I w id a0 p.msg w1 a1 p.sender hd]
        have hc : contTy (credited.st p.sender) := (contTy_match _ _ hphS htyS).mpr (hS.cont p.sender)
        exact tyOk_resume I.desc _ p.sender p.isCall id hT2 hc
  | cons m ms =>
    cases hpk : (w.st id).parked with
    | nil =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := ms, prio := (w.st id).prio,
          parked := [], tokens := (w.st id).tokens, nextMid := (w.st id).nextMid }
        exact tyOk_credit I.desc _ (tname id) m.sender
          (install_ty I hL w id a0 m w1 a1 hT hready.1.symm rfl rfl hd)
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := ms, prio := (w.st id).prio,
          parked := p :: ps, tokens := (w.st id).tokens, nextMid := (w.st id).nextMid }
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hmem := deliver_ty_mem I hL w id a0 m w1 a1 hT hready.1.symm rfl rfl hd
        have hT2 := tyOk_new I.desc w1 id admitted
          (tyOk_st I.desc w w1 hT (fun i => deliver_st I w id a0 m w1 a1 i hd)) (fun _ => hmem.1)
        have hT3 := tyOk_credit I.desc _ (tname id) m.sender hT2
        have hfree : notParked (w.st id).phase := by simp [hready.2, notParked]
        have hsnd : p.sender ≠ id :=
          not_queued w id hM hfree id p (by rw [hpk]; exact List.mem_cons_self)
        let base := setActor w1 id admitted
        let credited := creditSender base (tname id) m.sender
        have hphS : (credited.st p.sender).phase = (w.st p.sender).phase := by
          rw [(credit_phase base (tname id) m.sender p.sender).1, setActor_other w1 id p.sender admitted hsnd,
            deliver_st I w id a0 m w1 a1 p.sender hd]
        have htyS : (credited.st p.sender).typestate = (w.st p.sender).typestate := by
          rw [(credit_keeps_ty base (tname id) m.sender p.sender).2, setActor_other w1 id p.sender admitted hsnd,
            deliver_st I w id a0 m w1 a1 p.sender hd]
        have hc : contTy (credited.st p.sender) := (contTy_match _ _ hphS htyS).mpr (hS.cont p.sender)
        exact tyOk_resume I.desc _ p.sender p.isCall id hT3 hc

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

theorem spawn_ty (I : Impl) (hG : GraphOk I.desc) (w : World) (template : String) (w' : World)
    (hT : TyOk I.desc w) (h : spawn I w template = some w') : TyOk I.desc w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      have hmem := template_mem I.desc template t ht
      have hele := initial_declared I.desc t (state_lines I.desc hG) hmem
      let pid := InstId.peer template (w.nextIx template)
      let born := withTokens I.desc template
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 }
      have hT1 := tyOk_record I.desc w (w.roster ++ [pid])
        (fun n => if n = template then w.nextIx n + 1 else w.nextIx n) hT
      have hT2 := tyOk_new I.desc _ pid born hT1 (by
        intro _
        simp [born, withTokens, pid, tname, statesOf, ht]
        exact List.elem_iff.mp hele)
      simpa [pid, born] using tyOk_read I.desc _ pid hT2
    · simp [hif] at h

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

theorem finish_ty (I : Impl) (w : World) (id : InstId) (w' : World) (hT : TyOk I.desc w)
    (hS : SemInv I w) (h : finishWait I w id = some w') : TyOk I.desc w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    exact tyOk_proceed I.desc w id k hT (by simpa [contTy, hph] using hS.cont id)
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    exact tyOk_proceed I.desc w id k hT (by simpa [contTy, hph] using hS.cont id)
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem ingress_ty (I : Impl) (w w' : World) (dst : InstId) (label : String) (hT : TyOk I.desc w)
    (h : receiveIngress I w dst label = some w') : TyOk I.desc w' := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · cases h
            exact tyOk_id I.desc w dst _ hT (by simp [chargeSender, bumpToken]) (by simp [chargeSender, bumpToken])

theorem head_ty (I : Impl) (w : World) (id : InstId) (w' : World) (hT : TyOk I.desc w)
    (hS : SemInv I w) (h : execHead I w id = some w') : TyOk I.desc w' := by
  simp only [execHead] at h
  split at h
  · cases h
  · next _ =>
    split at h
    · next k hph =>
      cases h
      exact exec_ty I w id k hT hS hph
    · cases h

theorem ty_step (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w w' : World) (a : Action)
    (hR : Reachable I N w) (h : apply I a w = some w') (hT : TyOk I.desc w) : TyOk I.desc w' := by
  have hS := (inv_reachable I N w hL hR).1
  cases a with
  | recvBulk id =>
    exact receive_bulk_ty I hL w id w' hT hS (inv_reachable I N w hL hR).2.1 h
  | recvPrio id => exact receive_prio_ty I hL w id w' hT h
  | exec id => exact head_ty I w id w' hT hS h
  | finish id => exact finish_ty I w id w' hT hS h
  | spawn template => exact spawn_ty I hG w template w' hT h
  | ingress dst label => exact ingress_ty I w w' dst label hT (by simpa [apply] using h)
  | kill sub key => sorry
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hT

theorem ty_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : TyOk I.desc w := by
  induction hR with
  | init => exact ty_init I hG N
  | step _ _ _ _ ha ih => exact ty_step I hL hG N _ _ _ ‹_› ha ih

/-! Indices of a multiplicity-one template stay at zero, so a busy actor of that
name is the core the group tuple reads. -/

theorem enqueue_ix (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (name : String) : (enqueueOrPark w D sender dst msg isCall k).nextIx name = w.nextIx name := by
  unfold enqueueOrPark
  dsimp only
  split
  · simp [setActor]
  · split
    · split
      · split <;> simp [setActor]
      · split <;> simp [setActor]
    · split
      · simp [setActor]
      · simp [setActor]

theorem perform_ix (w : World) (sender : InstId) (k : Cont) (name : String) :
    (performReply w sender k).nextIx name = w.nextIx name := by
  unfold performReply
  split
  · simp [setActor]
  · split
    · split <;> simp [setActor]
    · simp [setActor]

theorem try_ix (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (name : String) : (tryWake D w dstId label writer).nextIx name = w.nextIx name := by
  simp only [tryWake]
  split <;> simp [setActor]

theorem wake_ix (D : Description) (w : World) (dst label : String) (writer : InstId) (name : String) :
    (wakeReaders D w dst label writer).nextIx name = w.nextIx name := by
  unfold wakeReaders
  induction readersOf w dst generalizing w with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih (tryWake D w i label writer), try_ix]

theorem release_ix (w : World) (id : InstId) (ps : List Parked) (name : String) :
    (releaseParked w id ps).nextIx name = w.nextIx name := by
  unfold releaseParked
  induction ps generalizing w with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      have hneg : ¬ ((p.isCall || decide (p.sender = id)) = true) := by
        rw [hf]
        decide
      rw [if_neg hneg]
      rw [ih (setActor w p.sender (resumeSender (w.st p.sender) false id)), actor_ix]

theorem refund_msgs_ix (w : World) (dst : String) (ms : List Msg) (name : String) :
    (refundMsgs w dst ms).nextIx name = w.nextIx name := by
  unfold refundMsgs
  induction ms generalizing w with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons]
    rw [ih (creditSender w dst m.sender), credit_ix]

theorem refund_park_ix (w : World) (dst : String) (ps : List Parked) (name : String) :
    (refundParked w dst ps).nextIx name = w.nextIx name := by
  unfold refundParked
  induction ps generalizing w with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (creditSender w dst p.msg.sender), credit_ix]

theorem exec_ix (I : Impl) (w : World) (id : InstId) (k : Cont) (name : String) :
    (execRun I w id (w.st id) k).nextIx name = w.nextIx name := by
  cases hk : k.rest with
  | nil => simp [execRun, hk, setActor]
  | cons e es =>
    cases e with
    | internal => simp [execRun, hk, setActor]
    | peer => simp [execRun, hk, setActor]
    | send d l n =>
      cases hr : route w I.desc id d with
      | none => simp [execRun, hk, hr, setActor]
      | some dst => simp [execRun, hk, hr, enqueue_ix]
    | call d l n =>
      cases hr : route w I.desc id d with
      | none => simp [execRun, hk, hr, setActor]
      | some dst => simp [execRun, hk, hr, enqueue_ix]
    | trySend d l n =>
      cases hr : route w I.desc id d with
      | none => simp [execRun, hk, hr, setActor]
      | some dst =>
        simp [execRun, hk, hr]
        split
        · simp [enqueue_ix]
        · simp [setActor]
    | reply => simp [execRun, hk, perform_ix]
    | selfSchedule _ =>
      simp [execRun, hk]
      split
      · rw [actor_ix]
      · split <;> rw [actor_ix]
    | cell dst label value =>
      simp [execRun, hk, setCell]
      split
      · simp [setActor]
      · rw [wake_ix, actor_ix]
    | terminate =>
      simp [execRun, hk]
      split
      · next t ht =>
        split
        · rw [release_ix, actor_ix, refund_park_ix, refund_msgs_ix, read_ix]
        · rfl
      · rfl

theorem head_ix (I : Impl) (w : World) (id : InstId) (w' : World) (name : String)
    (h : execHead I w id = some w') : w'.nextIx name = w.nextIx name := by
  simp only [execHead] at h
  split at h
  · cases h
  · next _ =>
    split at h
    · next k hph =>
      cases h
      exact exec_ix I w id k name
    · cases h

theorem finish_ix (I : Impl) (w : World) (id : InstId) (w' : World) (name : String) (h : finishWait I w id = some w') :
    w'.nextIx name = w.nextIx name := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    simp [setActor]
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    simp [setActor]
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem receive_prio_ix (I : Impl) (w : World) (id : InstId) (w' : World) (name : String)
    (h : receivePrio I w id = some w') : w'.nextIx name = w.nextIx name := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp only [hp] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        rw [actor_ix, deliver_ix I w id _ m w1 a1 name hd]

theorem receive_bulk_ix (I : Impl) (w : World) (id : InstId) (w' : World) (name : String)
    (h : receiveBulk I w id = some w') : w'.nextIx name = w.nextIx name := by
  simp only [receiveBulk] at h
  split at h
  · cases h
  · cases hbox : (w.st id).box with
    | nil =>
      cases hpk : (w.st id).parked with
      | nil => simp [hbox, hpk] at h
      | cons p ps =>
        simp [hbox, hpk] at h
        split at h
        · cases h
        · next w1 a1 hd =>
          cases h
          rw [actor_ix, credit_ix, actor_ix, deliver_ix I w id _ _ w1 a1 name hd]
    | cons m ms =>
      cases hpk : (w.st id).parked with
      | nil =>
        simp [hbox, hpk] at h
        split at h
        · cases h
        · next w1 a1 hd =>
          cases h
          rw [credit_ix, actor_ix, deliver_ix I w id _ _ w1 a1 name hd]
      | cons p ps =>
        simp [hbox, hpk] at h
        split at h
        · cases h
        · next w1 a1 hd =>
          cases h
          rw [actor_ix, credit_ix, actor_ix, deliver_ix I w id _ _ w1 a1 name hd]

theorem spawn_ix (I : Impl) (w : World) (template : String) (w' : World) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hmul : t.multiplicity = .one)
    (h : spawn I w template = some w') : w'.nextIx name = w.nextIx name := by
  unfold spawn at h
  split at h
  · cases h
  · next u hu =>
    by_cases hif : (u.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      by_cases hname : name = template
      · have hu' : templateOf I.desc name = some u := by simpa [hname] using hu
        have heqt : u = t := by
          rw [ht] at hu'
          cases hu'
          rfl
        simp [Bool.and_eq_true] at hif
        have hper : (u.multiplicity == .perPeer) = true := hif.1
        rw [heqt, hmul] at hper
        have hone : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
        rw [hone] at hper
        cases hper
      · rw [read_ix, actor_ix]
        dsimp
        rw [if_neg hname]
    · simp [hif] at h

theorem ix_preserved (I : Impl) (w w' : World) (a : Action) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hmul : t.multiplicity = .one)
    (h : apply I a w = some w') : w'.nextIx name = w.nextIx name := by
  cases a with
  | recvBulk id => exact receive_bulk_ix I w id w' name h
  | recvPrio id => exact receive_prio_ix I w id w' name h
  | exec id => exact head_ix I w id w' name h
  | finish id => exact finish_ix I w id w' name h
  | spawn template => exact spawn_ix I w template w' name t ht hmul h
  | ingress dst label =>
    exact congrFun (ingress_phase I w w' dst label (InstId.core name) (by simpa [apply] using h)).2.2.2.2.2.2.1 name
  | kill sub key =>
    rw [kill_apply_world I w w' sub key h, killSubtree_nextIx]
  | stutter =>
    cases stutter_unchanged I w w' h
    rfl

theorem ix_zero (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hmul : t.multiplicity = .one) : w.nextIx name = 0 := by
  induction hR with
  | init => exact init_ix I N name
  | step _ _ _ _ ha ih => rw [ix_preserved I _ _ _ name t ht hmul ha, ih]

theorem busy_is_core (w : World) (hO : OpenSlots w) (name : String) (hix : w.nextIx name = 0)
    (id : InstId) (hn : tname id = name) (hph : (w.st id).phase ≠ .idle) : id = InstId.core name := by
  cases id with
  | core n =>
    simp [tname] at hn
    cases hn
    rfl
  | peer n i =>
    simp [tname] at hn
    cases hn
    exact False.elim (not_open_phase w hO (InstId.peer name i) name i (by rw [hix]; exact Nat.zero_le i) rfl hph)

theorem alive_is_core (w : World) (hO : OpenSlots w) (name : String) (hix : w.nextIx name = 0)
    (id : InstId) (hn : tname id = name) (hl : (w.st id).life = .alive) : id = InstId.core name := by
  cases id with
  | core n =>
    simp [tname] at hn
    cases hn
    rfl
  | peer n i =>
    simp [tname] at hn
    cases hn
    exact False.elim (not_open w hO (InstId.peer name i) name i (by rw [hix]; exact Nat.zero_le i) rfl hl)

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

theorem partner_mem (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (e : Edge) (he : e ∈ I.desc.edges) (hk : e.kind = .blocking)
    (id dst : InstId) (hsrc : e.src = tname id) (hss : e.srcState = (w.st id).typestate)
    (hdstn : e.dst = tname dst) (hbusy : (w.st id).phase ≠ .idle) :
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
    have hun := uncovered_nil I.desc gs (compat_empty_of_local I hL) hmode
    obtain ⟨g0, hg0, hs0, hd0⟩ := edge_covered I.desc gs e hun he hk
    have hgGroup : g0 ∈ compatGroups I.desc.compatibility := by simp [compatGroups, hmode, hg0]
    have hwell := (compat_group_closed I.desc g0 (compat_empty_of_local I hL) hgGroup).1
    obtain ⟨tS, htS, hmS, _, _⟩ := role_static I.desc g0 e.src hwell (List.elem_iff.mp hs0)
    obtain ⟨tD, htD, hmD, _, _⟩ := role_static I.desc g0 e.dst hwell (List.elem_iff.mp hd0)
    have hixS := ix_zero I N w hR e.src tS htS hmS
    have hixD := ix_zero I N w hR e.dst tD htD hmD
    have hcoreS : id = InstId.core e.src := busy_is_core w hI.2.2 e.src hixS id hsrc.symm hbusy
    have hcoreD : dst = InstId.core e.dst := alive_is_core w hI.2.2 e.dst hixD dst hdstn.symm hl
    have hmem := in_targets gs e.src e.srcState e.dst (w.st dst).typestate ⟨g0, hg0, hs0, hd0⟩ ?_
    simpa [targetStates, hmode] using hmem
    · intro g hg hs hd
      have hgG : g ∈ compatGroups I.desc.compatibility := by simp [compatGroups, hmode, hg]
      have htup := hI.1.compat g hgG (hI.1.live g hgG)
      obtain ⟨a, ha, hag⟩ := tupleMem_pick g.allowed (roleTuple w g) htup
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
theorem projects_park (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (isCall : Bool) (k : Cont)
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
    (by rw [hph]; intro hbad; cases hbad)
  exact ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab, hpart⟩

/-- An actor awaiting a reply waits on a blocking call edge with the same filter. -/
theorem projects_reply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hph : (w.st id).phase = .awaitReply dst k) :
    ∃ label e, e ∈ I.desc.edges ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧
      e.dst = tname dst ∧ e.kind = .blocking ∧ e.effect = EffectKind.call ∧ e.label = label ∧
      (discharged I.desc e = true ∨
        ((w.st dst).life = .alive → (w.st dst).typestate ∈ targetStates I.desc e)) := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨label, e, he, hsrc, hss, hdstn, hkind, heff, hlab⟩ := described_reply I w hI id dst k hph
  have hpart := partner_mem I hL hG N w hR e he hkind id dst hsrc hss hdstn
    (by rw [hph]; intro hbad; cases hbad)
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

theorem projects (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : Projects I w :=
  ⟨fun id dst isCall k hph => projects_park I hL hG N w hR id dst isCall k hph,
   fun id dst k hph => projects_reply I hL hG N w hR id dst k hph⟩

end Deadlock
