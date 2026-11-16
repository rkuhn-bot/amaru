import Deadlock.Pres
import Deadlock.Mail

set_option autoImplicit false

namespace Deadlock

theorem head_rest (D : Description) (template state : String) (e : Eff) (es : List Eff)
    (h : effectsOk D template state (e :: es) = true) : effectsOk D template state es = true :=
  effectsOk_tail D template state e es h

theorem head_send (D : Description) (t st d l : String) (n : Nat) (es : List Eff)
    (h : effectsOk D t st (.send d l n :: es) = true) :
    hasEdge D t st d .send .blocking l = true ∧ effectsOk D t st es = true := by
  simp [effectsOk, Bool.and_eq_true] at h
  exact h

theorem head_call (D : Description) (t st d l : String) (n : Nat) (es : List Eff)
    (h : effectsOk D t st (.call d l n :: es) = true) :
    hasEdge D t st d .call .blocking l = true ∧ effectsOk D t st es = true := by
  simp [effectsOk, Bool.and_eq_true] at h
  exact h

theorem route_tname (w : World) (D : Description) (dst : String) (hint : Nat) (id : InstId)
    (h : route w D dst hint = some id) : tname id = dst := by
  unfold route at h
  split at h
  · cases h
  · next t _ =>
    cases hm : t.multiplicity with
    | one =>
      rw [hm] at h
      by_cases hl : (w.st (InstId.core dst)).life = .alive
      · simp [hl] at h
        cases h
        rfl
      · simp [hl] at h
    | perPeer =>
      rw [hm] at h
      by_cases hl : (w.st (InstId.peer dst hint)).life = .alive
      · simp [hl] at h
        cases h
        rfl
      · simp [hl] at h

/-- `send`, `call`, `internal`, and `peer` preserve `SemInv`. The running actor is `w.st id`. -/
theorem exec_basic_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hS : SemInv I w) (hphase : (w.st id).phase = .run { k with rest := e :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (e :: es) = true)
    (he : e = .internal ∨ e = .peer ∨
      (∃ d l n, e = .send d l n) ∨ (∃ d l n, e = .call d l n)) :
    SemInv I (execRun I w id (w.st id) { k with rest := e :: es }) := by
  have hty : (w.st id).typestate = k.toState := by
    simpa [contTy, hphase, afterHead] using hS.cont id
  have htail : effectsOk I.desc (tname id) (w.st id).typestate es = true := head_rest _ _ _ e es hprog
  rcases he with he | he | he | he
  · subst he
    simp [execRun]
    apply sem_set I w id { (w.st id) with phase := .awaitEffect (afterHead { k with rest := .internal :: es }) } hS
    · rfl
    · rfl
    · simp [contTy, afterHead, hty]
    · simp [programOk, afterHead, htail]
    · simp [waitEdge]
  · subst he
    simp [execRun]
    apply sem_set I w id { (w.st id) with phase := .awaitPeer (afterHead { k with rest := .peer :: es }) } hS
    · rfl
    · rfl
    · simp [contTy, afterHead, hty]
    · simp [programOk, afterHead, htail]
    · simp [waitEdge]
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    have hhead := head_send _ _ _ d l n es hprog
    cases hr : route w I.desc d n with
    | none =>
      simp [execRun, hr]
      have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .send d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      exact sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    | some dstId =>
      simp [execRun, hr]
      apply enqueue_sem I w id dstId { label := l, sender := id, callFrom := none } false
        (afterHead { k with rest := .send d l n :: es }) hS
      · simp [afterHead, hty]
      · simpa [afterHead] using htail
      · refine ⟨l, ?_⟩
        simpa [route_tname w I.desc d n dstId hr] using hhead.1
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    have hhead := head_call _ _ _ d l n es hprog
    cases hr : route w I.desc d n with
    | none =>
      simp [execRun, hr]
      have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .call d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      exact sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    | some dstId =>
      simp [execRun, hr]
      apply enqueue_sem I w id dstId { label := l, sender := id, callFrom := some id } true
        (afterHead { k with rest := .call d l n :: es }) hS
      · simp [afterHead, hty]
      · simpa [afterHead] using htail
      · refine ⟨l, ?_⟩
        simpa [route_tname w I.desc d n dstId hr] using hhead.1

/-- The same heads, including a send or call that parks, preserve `MailInv`. -/
theorem exec_basic_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := e :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (e :: es) = true)
    (he : e = .internal ∨ e = .peer ∨
      (∃ d l n, e = .send d l n) ∨ (∃ d l n, e = .call d l n)) :
    SemInv I (execRun I w id (w.st id) { k with rest := e :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := e :: es }) := by
  have hsem := exec_basic_sem I w id k e es hS hphase hprog he
  have hfree : notParked (w.st id).phase := by simp [notParked, hphase]
  refine ⟨hsem, ?_⟩
  rcases he with he | he | he | he
  · subst he
    simp [execRun]
    exact mail_set_free w id _ hM hfree (by simp [notParked]) rfl
  · subst he
    simp [execRun]
    exact mail_set_free w id _ hM hfree (by simp [notParked]) rfl
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    cases hr : route w I.desc d n with
    | none =>
      simp [execRun, hr]
      exact mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
    | some dstId =>
      simp [execRun, hr]
      exact enqueue_mail w I.desc id dstId { label := l, sender := id, callFrom := none } false
        (afterHead { k with rest := .send d l n :: es }) hM hfree
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    cases hr : route w I.desc d n with
    | none =>
      simp [execRun, hr]
      exact mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
    | some dstId =>
      simp [execRun, hr]
      exact enqueue_mail w I.desc id dstId { label := l, sender := id, callFrom := some id } true
        (afterHead { k with rest := .call d l n :: es }) hM hfree

theorem exec_done_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (hS : SemInv I w)
    (hphase : (w.st id).phase = .run { k with rest := [] }) :
    SemInv I (execRun I w id (w.st id) { k with rest := [] }) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hphase] using hS.cont id
  simp [execRun]
  apply sem_set I w id { (w.st id) with phase := .idle, typestate := k.toState } hS
  · exact hty.symm
  · rfl
  · simp [contTy]
  · simp [programOk]
  · simp [waitEdge]

theorem exec_done_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := [] }) :
    SemInv I (execRun I w id (w.st id) { k with rest := [] }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := [] }) := by
  refine ⟨exec_done_sem I w id k hS hphase, ?_⟩
  simp [execRun]
  exact mail_set_free w id _ hM (by simp [notParked, hphase]) (by simp [notParked]) rfl

theorem run_not_parked (w : World) (id : InstId) (k : Cont) (h : (w.st id).phase = .run k) :
    notParked (w.st id).phase := by
  simp [notParked, h]

/-- A non-blocking send never parks. It preserves `SemInv` and `MailInv`. -/
theorem exec_try_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (d l : String) (n : Nat)
    (es : List Eff) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .trySend d l n :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (.trySend d l n :: es) = true) :
    SemInv I (execRun I w id (w.st id) { k with rest := .trySend d l n :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .trySend d l n :: es }) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hphase] using hS.cont id
  have htail : effectsOk I.desc (tname id) (w.st id).typestate es = true := head_rest _ _ _ _ es hprog
  have hfree : notParked (w.st id).phase := run_not_parked w id _ hphase
  simp [execRun]
  cases hr : route w I.desc d n with
  | none =>
    simp [hr]
    have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .trySend d l n :: es })
      (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
    refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2, ?_⟩
    exact mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
  | some dstId =>
    simp [hr]
    split
    · -- Room: charge, append to the box, then continue. The sender is running, so it is not parked.
      rename_i hroom
      have hch := charge_ok (w.st id) (tname dstId)
      have hcontC : contTy (chargeSender (w.st id) (tname dstId)) := by
        simpa [chargeSender, bumpToken, contTy] using hS.cont id
      have hprogC : programOk I.desc id (chargeSender (w.st id) (tname dstId)) := by
        simpa [chargeSender, bumpToken, programOk] using hS.prog id
      have hwaitC : waitEdge I.desc id (chargeSender (w.st id) (tname dstId)) := by
        simpa [chargeSender, bumpToken, waitEdge] using hS.waited id
      have hS1 := sem_set I w id (chargeSender (w.st id) (tname dstId)) hS hch.1 hch.2.1 hcontC hprogC hwaitC
      have hM1 := mail_set_same w id (chargeSender (w.st id) (tname dstId)) hM (charge_phase _ _) (charge_parked _ _)
      let w1 := setActor w id (chargeSender (w.st id) (tname dstId))
      let stored : Actor := { (w1.st dstId) with box := (w1.st dstId).box ++ [{ label := l, sender := id, callFrom := none }] }
      have hS2 := sem_set I w1 dstId stored hS1 rfl rfl
        (by simpa [stored, contTy] using hS1.cont dstId)
        (by simpa [stored, programOk] using hS1.prog dstId)
        (by simpa [stored, waitEdge] using hS1.waited dstId)
      have hM2 := mail_set_same w1 dstId stored hM1 rfl rfl
      let w2 := setActor w1 dstId stored
      have hty2 : (w2.st id).typestate = k.toState := by
        by_cases hs : id = dstId
        · subst hs
          simp [w2, w1, stored, setActor, hch.1, hty]
        · simp [w2, w1, stored, setActor, hs, hch.1, hty]
      have htail2 : effectsOk I.desc (tname id) (w2.st id).typestate es = true := by
        rw [hty2]
        simpa [hty] using htail
      have hp := proceed_ok I.desc id (w2.st id) (afterHead { k with rest := .trySend d l n :: es })
        (by simp [afterHead, hty2]) (by simpa [afterHead] using htail2)
      have hfree2 : notParked (w2.st id).phase := by
        by_cases hs : id = dstId
        · subst hs
          simp [w2, w1, stored, setActor, charge_phase, notParked, hphase]
        · simp [w2, w1, stored, setActor, hs, charge_phase, notParked, hphase]
      refine ⟨sem_set I w2 id _ hS2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2,
        mail_set_free w2 id _ hM2 hfree2 (proceed_not_parked _ _) (proceed_parked _ _)⟩
    · have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .trySend d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2, ?_⟩
      exact mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)

theorem exec_sched_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (label : String) (es : List Eff)
    (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .selfSchedule label :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (.selfSchedule label :: es) = true) :
    SemInv I (execRun I w id (w.st id) { k with rest := .selfSchedule label :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .selfSchedule label :: es }) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hphase] using hS.cont id
  have htail : effectsOk I.desc (tname id) (w.st id).typestate es = true := head_rest _ _ _ _ es hprog
  have hfree : notParked (w.st id).phase := run_not_parked w id _ hphase
  simp [execRun]
  split
  · have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .selfSchedule label :: es })
      (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
    refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2,
      mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)⟩
  · split
    · let bumped : Actor :=
        { (w.st id) with prio := upsertPrio (w.st id).prio { label := label, sender := id, callFrom := none } }
      have hp := proceed_ok I.desc id bumped (afterHead { k with rest := .selfSchedule label :: es })
        (by simp [bumped, afterHead, hty]) (by simpa [bumped, afterHead] using htail)
      refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2,
        mail_set_free w id _ hM hfree (proceed_not_parked _ _) (by simp [proceed_parked, bumped])⟩
    · refine ⟨sem_set I w id { (w.st id) with phase := .crashed } hS rfl rfl
        (by simp [contTy]) (by simp [programOk]) (by simp [waitEdge]),
        mail_set_free w id { (w.st id) with phase := .crashed } hM hfree (by simp [notParked]) rfl⟩

theorem proceed_sender (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff)
    (replyTo : Option InstId) (hS : SemInv I w) (hM : MailInv w)
    (hty : (w.st id).typestate = k.toState)
    (htail : effectsOk I.desc (tname id) (w.st id).typestate es = true)
    (hfree : notParked (w.st id).phase) :
    let k' : Cont := { rest := es, toState := k.toState, replyTo := replyTo }
    SemInv I (setActor w id (proceed (w.st id) k')) ∧ MailInv (setActor w id (proceed (w.st id) k')) := by
  intro k'
  have hp := proceed_ok I.desc id (w.st id) k' (by simp [k', hty]) (by simpa [k'] using htail)
  exact ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2,
    mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)⟩

theorem exec_reply_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff)
    (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .reply :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (.reply :: es) = true) :
    SemInv I (execRun I w id (w.st id) { k with rest := .reply :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .reply :: es }) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hphase] using hS.cont id
  have htail : effectsOk I.desc (tname id) (w.st id).typestate es = true := head_rest _ _ _ _ es hprog
  have hfree : notParked (w.st id).phase := run_not_parked w id _ hphase
  simp [execRun, performReply, afterHead]
  cases hto : k.replyTo with
  | none =>
    simpa [hto] using proceed_sender I w id k es none hS hM hty htail hfree
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = id
      · by_cases hc : caller = id
        · rw [hc, hphase] at hph
          cases hph
        · simp [hto, hph, hd]
          have htyC : (w.st caller).typestate = ck.toState := by simpa [contTy, hph] using hS.cont caller
          have hprogC : effectsOk I.desc (tname caller) (w.st caller).typestate ck.rest = true := by
            simpa [programOk, hph] using hS.prog caller
          have hpC := proceed_ok I.desc caller (w.st caller) ck htyC hprogC
          have hfreeC : notParked (w.st caller).phase := by simp [notParked, hph]
          let resumed := proceed (w.st caller) ck
          have hS1 := sem_set I w caller resumed hS hpC.1 hpC.2.1 hpC.2.2.1 hpC.2.2.2.1 hpC.2.2.2.2
          have hM1 := mail_set_free w caller resumed hM hfreeC (proceed_not_parked _ _) (proceed_parked _ _)
          have hother : (setActor w caller resumed).st id = w.st id :=
            setActor_other _ _ _ _ (Ne.symm hc)
          have both := proceed_sender I (setActor w caller resumed) id k es (some caller)
            hS1 hM1 (by simpa [hother] using hty) (by simpa [hother] using htail)
            (by simpa [hother] using hfree)
          simpa [resumed, hother] using both
      · simpa [hto, hph, hd] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | idle =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | run _ =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | parked _ _ _ =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | awaitEffect _ =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | awaitPeer _ =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree
    | crashed =>
      simpa [hto, hph] using proceed_sender I w id k es (some caller) hS hM hty htail hfree

theorem tryWake_inv (I : Impl) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (hS : SemInv I w) (hM : MailInv w) :
    SemInv I (tryWake I.desc w dstId label writer) ∧ MailInv (tryWake I.desc w dstId label writer) := by
  unfold tryWake
  by_cases h :
      ((w.st dstId).life == .alive && decide ((w.st dstId).prio.length < capPrio I.desc w.N dstId) &&
        !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [h]
    refine ⟨?_, ?_⟩
    · apply sem_set
      · exact hS
      · rfl
      · rfl
      · simpa [contTy] using hS.cont dstId
      · simpa [programOk] using hS.prog dstId
      · simpa [waitEdge] using hS.waited dstId
    · apply mail_set_same
      · exact hM
      · rfl
      · rfl
  · have hf :
        ((w.st dstId).life == .alive && decide ((w.st dstId).prio.length < capPrio I.desc w.N dstId) &&
          !((w.st dstId).prio.any fun p => p.label == label)) = false := by
      cases hb :
          ((w.st dstId).life == .alive && decide ((w.st dstId).prio.length < capPrio I.desc w.N dstId) &&
            !((w.st dstId).prio.any fun p => p.label == label)) <;> simp_all
    simp [hf]
    exact ⟨hS, hM⟩

theorem wakes_inv (I : Impl) (w : World) (ids : List InstId) (label : String) (writer : InstId)
    (hS : SemInv I w) (hM : MailInv w) :
    SemInv I (ids.foldl (fun w id => tryWake I.desc w id label writer) w) ∧
      MailInv (ids.foldl (fun w id => tryWake I.desc w id label writer) w) := by
  induction ids generalizing w with
  | nil => simpa using ⟨hS, hM⟩
  | cons i ids ih =>
    rw [List.foldl_cons]
    have h := tryWake_inv I w i label writer hS hM
    exact ih _ h.1 h.2

theorem exec_cell_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (dst label : String)
    (value : Nat) (es : List Eff) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .cell dst label value :: es })
    (hprog : effectsOk I.desc (tname id) (w.st id).typestate (.cell dst label value :: es) = true) :
    SemInv I (execRun I w id (w.st id) { k with rest := .cell dst label value :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .cell dst label value :: es }) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hphase] using hS.cont id
  have htail : effectsOk I.desc (tname id) (w.st id).typestate es = true := head_rest _ _ _ _ es hprog
  have hfree : notParked (w.st id).phase := run_not_parked w id _ hphase
  simp [execRun]
  let w1 := setCell w dst label { value := max (w.cell dst label).value value, dirty := true }
  have hst : ∀ i, w1.st i = w.st i := by intro _; rfl
  have hScell : SemInv I w1 := by
    apply sem_stable I w w1 hS
    · intro _ _ r _; simp [hst]
    · intro _ _ r _; simp [hst]
    · intro i; simpa [hst] using hS.cont i
    · intro i; simpa [hst] using hS.prog i
    · intro i; simpa [hst] using hS.waited i
  have hMcell : MailInv w1 := mail_copy w w1 hM hst
  let stepped := proceed (w1.st id) { rest := es, toState := k.toState, replyTo := k.replyTo }
  have hp := proceed_ok I.desc id (w1.st id) { rest := es, toState := k.toState, replyTo := k.replyTo }
    (by simpa [hst, hty]) (by rw [hst]; simpa [hty] using htail)
  have hS1 := sem_set I w1 id stepped hScell hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  have hM1 := mail_set_free w1 id stepped hMcell (by simpa [hst] using hfree)
    (proceed_not_parked _ _) (proceed_parked _ _)
  split
  · exact ⟨hS1, hM1⟩
  · have hw := wakes_inv I _ (readersOf (setActor w1 id stepped) dst) label id hS1 hM1
    simp [wakeReaders, w1]
    exact hw

theorem credit_mail (I : Impl) (w : World) (tmpl : String) (sender : InstId) (hM : MailInv w) :
    MailInv (creditSender w tmpl sender) := by
  unfold creditSender
  exact mail_set_same w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) hM
    (by simp [bumpToken]) (by simp [bumpToken])

theorem terminable_not_role (I : Impl) (hL : LocalOk I) (r : String) (t : Template)
    (ht : templateOf I.desc r = some t) (hk : t.terminable = true) (g : CompatGroup)
    (hg : g ∈ compatGroups I.desc.compatibility) : r ∉ g.roles := by
  intro hr
  have hw := (compat_group_closed I.desc g (compat_empty_of_local I hL) hg).1
  obtain ⟨t', ht', _, hterm, _⟩ := role_static I.desc g r hw hr
  have : t' = t := by
    rw [ht] at ht'
    cases ht'
    rfl
  rw [this] at hterm
  cases ht : t.terminable <;> simp [hterm] at hk

theorem refund_msgs_inv (I : Impl) (w : World) (dst : String) (ms : List Msg)
    (hS : SemInv I w) (hM : MailInv w) :
    SemInv I (refundMsgs w dst ms) ∧ MailInv (refundMsgs w dst ms) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using ⟨hS, hM⟩
  | cons m ms ih =>
    rw [refundMsgs, List.foldl_cons]
    exact ih _ (credit_sem I w dst m.sender hS) (credit_mail I w dst m.sender hM)

theorem refund_park_inv (I : Impl) (w : World) (dst : String) (ps : List Parked)
    (hS : SemInv I w) (hM : MailInv w) :
    SemInv I (refundParked w dst ps) ∧ MailInv (refundParked w dst ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using ⟨hS, hM⟩
  | cons p ps ih =>
    rw [refundParked, List.foldl_cons]
    exact ih _ (credit_sem I w dst p.msg.sender hS) (credit_mail I w dst p.msg.sender hM)

theorem resume_false_ok (D : Description) (sid : InstId) (a : Actor) (dst : InstId)
    (hc : contTy a) (hg : programOk D sid a) (hw : waitEdge D sid a) :
    let b := resumeSender a false dst
    b.typestate = a.typestate ∧ b.life = a.life ∧ contTy b ∧ programOk D sid b ∧ waitEdge D sid b ∧
      notParked b.phase ∧ b.parked = a.parked := by
  cases hph : a.phase with
  | parked _ _ k =>
    simp [resumeSender, hph]
    have hty : a.typestate = k.toState := by simpa [contTy, hph] using hc
    have hprog : effectsOk D (tname sid) a.typestate k.rest = true := by simpa [programOk, hph] using hg
    have hp := proceed_ok D sid a k hty hprog
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, proceed_not_parked a k, proceed_parked a k⟩
  | idle => simp [resumeSender, hph, notParked, hc, hg, hw]
  | run _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitReply _ _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitEffect _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | awaitPeer _ => simp [resumeSender, hph, notParked, hc, hg, hw]
  | crashed => simp [resumeSender, hph, notParked, hc, hg, hw]

theorem fold_release (I : Impl) (id : InstId) (ps : List Parked) (w : World) (hS : SemInv I w) :
    SemInv I (ps.foldl (fun w p =>
      if (p.isCall || decide (p.sender = id)) = true then w
      else setActor w p.sender (resumeSender (w.st p.sender) false id)) w) := by
  induction ps generalizing w with
  | nil => simpa using hS
  | cons p ps ih =>
    simp only [List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      exact ih _ hS
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      have hr := resume_false_ok I.desc p.sender (w.st p.sender) id (hS.cont _) (hS.prog _) (hS.waited _)
      exact ih _ (sem_set I w p.sender (resumeSender (w.st p.sender) false id) hS hr.1 hr.2.1
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1)

theorem release_sem (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hS : SemInv I w) :
    SemInv I (releaseParked w id ps) := by
  simpa [releaseParked] using fold_release I id ps w hS

private def releaseFold (id : InstId) (ps : List Parked) (w : World) : World :=
  ps.foldl (fun w p =>
    if (p.isCall || decide (p.sender = id)) = true then w
    else setActor w p.sender (resumeSender (w.st p.sender) false id)) w

theorem release_fold_eq (w : World) (id : InstId) (ps : List Parked) :
    releaseParked w id ps = releaseFold id ps w := by
  simp [releaseParked, releaseFold]

theorem release_id_fixed (id : InstId) (ps : List Parked) (w : World)
    (hself : ∀ p ∈ ps, p.sender ≠ id) : (releaseFold id ps w).st id = w.st id := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.sender ≠ id := fun q hq => hself q (List.mem_cons_of_mem _ hq)
    have hp : p.sender ≠ id := hself p List.mem_cons_self
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change (releaseFold id ps w).st id = w.st id
      exact ih _ htail
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change (releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st id =
        w.st id
      rw [ih _ htail]
      exact setActor_other w p.sender id (resumeSender (w.st p.sender) false id) hp.symm

theorem release_parked_other (id : InstId) (ps : List Parked) (i : InstId) (w : World)
    (_hi : i ≠ id) (hs : ∀ p ∈ ps, p.sender ≠ i) :
    ((releaseFold id ps w).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.sender ≠ i := fun q hq => hs q (List.mem_cons_of_mem _ hq)
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change ((releaseFold id ps w).st i).parked = (w.st i).parked
      exact ih _ htail
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change ((releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st i).parked =
        (w.st i).parked
      rw [ih _ htail, setActor_other w p.sender i (resumeSender (w.st p.sender) false id)
        (hs p List.mem_cons_self).symm]

theorem release_st_other (id : InstId) (ps : List Parked) (i : InstId) (w : World)
    (_hi : i ≠ id) (hs : ∀ p ∈ ps, p.sender ≠ i) : (releaseFold id ps w).st i = w.st i := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.sender ≠ i := fun q hq => hs q (List.mem_cons_of_mem _ hq)
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change (releaseFold id ps w).st i = w.st i
      exact ih _ htail
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change (releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st i = w.st i
      rw [ih _ htail, setActor_other w p.sender i (resumeSender (w.st p.sender) false id)
        (hs p List.mem_cons_self).symm]

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
  | nil => simpa [releaseFold] using hf
  | cons p ps ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change notParked ((releaseFold id ps w).st sid).phase
      exact ih _ hf
    · have hfalse : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hfalse]
      change notParked ((releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st sid).phase
      by_cases hwho : p.sender = sid
      · subst hwho
        exact ih _ (by rw [setActor_self]; exact resume_false_free _ _)
      · exact ih _ (by
          rw [setActor_other w p.sender sid (resumeSender (w.st p.sender) false id) (Ne.symm hwho)]
          exact hf)

theorem release_resumed (id : InstId) (ps : List Parked) (w : World) (p : Parked)
    (hp : p ∈ ps) (hc : p.isCall = false) (hs : p.sender ≠ id) :
    notParked ((releaseFold id ps w).st p.sender).phase := by
  induction ps generalizing w with
  | nil => cases hp
  | cons q qs ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (q.isCall || decide (q.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change notParked ((releaseFold id qs w).st p.sender).phase
      have hmem : p ∈ qs := by
        rcases List.mem_cons.mp hp with rfl | hmem
        · have hdec : decide (p.sender = id) = false := decide_eq_false hs
          simp [hc, hdec] at hskip
        · exact hmem
      exact ih _ hmem
    · have hfalse : (q.isCall || decide (q.sender = id)) = false := by
        cases hb : q.isCall || decide (q.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hfalse]
      change notParked
        ((releaseFold id qs (setActor w q.sender (resumeSender (w.st q.sender) false id))).st p.sender).phase
      by_cases hwho : q.sender = p.sender
      · rw [hwho]
        exact release_keeps_free id qs (setActor w p.sender (resumeSender (w.st p.sender) false id)) p.sender
          (by rw [setActor_self]; exact resume_false_free _ _)
      · have hmem : p ∈ qs := by
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact absurd rfl hwho
          · exact hmem
        exact ih _ hmem

theorem release_parked_all (id : InstId) (ps : List Parked) (w : World) (i : InstId) (hi : i ≠ id) :
    ((releaseFold id ps w).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change ((releaseFold id ps w).st i).parked = (w.st i).parked
      exact ih _
    · have hfalse : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hfalse]
      change ((releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st i).parked =
        (w.st i).parked
      by_cases hwho : p.sender = i
      · subst hwho
        rw [ih _, setActor_self, resume_parked]
      · rw [ih _, setActor_other w p.sender i (resumeSender (w.st p.sender) false id) (Ne.symm hwho)]

theorem credit_phase (w : World) (tmpl : String) (sender i : InstId) :
    ((creditSender w tmpl sender).st i).phase = (w.st i).phase ∧
      ((creditSender w tmpl sender).st i).parked = (w.st i).parked := by
  unfold creditSender
  by_cases h : i = sender
  · subst h
    simp [setActor_self, bumpToken]
  · simp [setActor_other w sender i _ h]

theorem refund_msgs_phase (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    have h1 := credit_phase w dst m.sender i
    have h2 := ih (creditSender w dst m.sender)
    change ((refundMsgs (creditSender w dst m.sender) dst ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs (creditSender w dst m.sender) dst ms).st i).parked = (w.st i).parked
    rw [h2.1, h1.1, h2.2, h1.2]
    exact ⟨rfl, rfl⟩

theorem refund_park_phase (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).phase = (w.st i).phase ∧
      ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    have h1 := credit_phase w dst p.msg.sender i
    have h2 := ih (creditSender w dst p.msg.sender)
    change ((refundParked (creditSender w dst p.msg.sender) dst ps).st i).phase = (w.st i).phase ∧
      ((refundParked (creditSender w dst p.msg.sender) dst ps).st i).parked = (w.st i).parked
    rw [h2.1, h1.1, h2.2, h1.2]
    exact ⟨rfl, rfl⟩

theorem no_parked_call (ps : List Parked) (h : hasParkedCall ps = false) (p : Parked) (hp : p ∈ ps) :
    p.isCall = false := by
  cases hc : p.isCall
  · rfl
  · have : hasParkedCall ps = true := by
      simp [hasParkedCall]
      exact ⟨p, hp, hc⟩
    simp [this] at h

/-- Terminate that the template does not allow leaves the world unchanged. -/

theorem exec_term_skip_sem (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff)
    (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .terminate :: es })
    (hno : ∀ t, templateOf I.desc (tname id) = some t →
      ¬ (t.terminable = true ∧ hasParkedCall (w.st id).parked = false)) :
    SemInv I (execRun I w id (w.st id) { k with rest := .terminate :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .terminate :: es }) := by
  simp [execRun]
  cases ht : templateOf I.desc (tname id) with
  | none =>
    simp [ht]
    exact ⟨hS, hM⟩
  | some t =>
    simp [hno t ht]
    exact ⟨hS, hM⟩

/-- Killing terminate refunds the mailbox, installs the dead actor, and resumes
every parked sender together. The queue is empty only after those resumes. -/
theorem exec_term_die_sem (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (t : Template)
    (k : Cont) (es : List Eff) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .terminate :: es })
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hnocall : hasParkedCall (w.st id).parked = false) :
    SemInv I (execRun I w id (w.st id) { k with rest := .terminate :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .terminate :: es }) := by
  let ps := (w.st id).parked
  let wR := readCells I.desc w id
  let wM := refundMsgs wR (tname id) (w.st id).box
  let wP := refundParked wM (tname id) ps
  let dead : Actor :=
    { (wP.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  let wD := setActor wP id dead
  let wF := releaseParked wD id ps
  have heq : execRun I w id (w.st id) { k with rest := .terminate :: es } = wF := by
    simp [execRun, ht, hterm, hnocall, wF, wD, dead, wP, wM, wR, ps]
  have hSR : SemInv I wR := cells_sem I w id hS
  have hMR : MailInv wR := mail_copy w wR hM fun i => readCells_st I.desc w id i
  have hRM := refund_msgs_inv I wR (tname id) (w.st id).box hSR hMR
  have hRP := refund_park_inv I wM (tname id) ps hRM.1 hRM.2
  have hne_role : ∀ (g : CompatGroup) (r : String), g ∈ compatGroups I.desc.compatibility →
      r ∈ g.roles → InstId.core r ≠ id := by
    intro g r hg hr heq
    cases id with
    | core name =>
      cases heq
      exact terminable_not_role I hL r t ht hterm g hg hr
    | peer _ _ => cases heq
  have hSD : SemInv I wD := by
    apply sem_stable I wP wD hRP.1
    · intro g hg r hr
      rw [setActor_other wP id (InstId.core r) dead (hne_role g r hg hr)]
    · intro g hg r hr
      rw [setActor_other wP id (InstId.core r) dead (hne_role g r hg hr)]
    · intro i
      by_cases h : i = id
      · rw [h, setActor_self]; simp [dead, contTy]
      · rw [setActor_other wP id i dead h]; exact hRP.1.cont i
    · intro i
      by_cases h : i = id
      · rw [h, setActor_self]; simp [dead, programOk]
      · rw [setActor_other wP id i dead h]; exact hRP.1.prog i
    · intro i
      by_cases h : i = id
      · rw [h, setActor_self]; simp [dead, waitEdge]
      · rw [setActor_other wP id i dead h]; exact hRP.1.waited i
  have hSF : SemInv I wF := release_sem I wD id ps hSD
  have hphaseP : (wP.st id).phase = (w.st id).phase := by
    rw [(refund_park_phase wM (tname id) ps id).1, (refund_msgs_phase wR (tname id) (w.st id).box id).1,
      readCells_st]
  have hparkP : (wP.st id).parked = ps := by
    rw [(refund_park_phase wM (tname id) ps id).2, (refund_msgs_phase wR (tname id) (w.st id).box id).2,
      readCells_st]
  have hfree : notParked (wP.st id).phase := by
    rw [hphaseP, hphase]
    simp [notParked]
  have hself : ∀ p ∈ ps, p.sender ≠ id := by
    intro p hp
    exact not_queued wP id hRP.2 hfree id p (by simpa [hparkP] using hp)
  have hstId : wF.st id = dead := by
    have hfix := release_id_fixed id ps wD hself
    rw [← release_fold_eq] at hfix
    simpa [wF, wD, setActor_self] using hfix
  have hpk : ∀ i, i ≠ id → (wF.st i).parked = (wP.st i).parked := by
    intro i hi
    have h := release_parked_all id ps wD i hi
    rw [← release_fold_eq] at h
    rw [h, setActor_other wP id i dead hi]
  have hother : ∀ i, i ≠ id → (∀ p ∈ ps, p.sender ≠ i) → (wF.st i).phase = (wP.st i).phase := by
    intro i hi hs
    have h := release_st_other id ps i wD hi hs
    rw [← release_fold_eq] at h
    rw [h, setActor_other wP id i dead hi]
  have hresume : ∀ p ∈ ps, notParked (wF.st p.sender).phase := by
    intro p hp
    have h := release_resumed id ps wD p hp (no_parked_call ps hnocall p hp) (hself p hp)
    rw [← release_fold_eq] at h
    simpa [wF] using h
  have hMF : MailInv wF :=
    mail_of_clear wP wF id ps hRP.2 hfree (fun p hp => no_parked_call ps hnocall p hp)
      (fun p => by rw [hparkP]) (by rw [hstId]) (by rw [hstId]) hpk hresume hother
  simpa [heq] using ⟨hSF, hMF⟩

theorem effects_of_transition (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    effectsOk I.desc tr.template tr.toState tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some _ =>
    simp only [transitionOk, ht] at hok
    rw [Bool.and_eq_true] at hok
    replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    exact hok.2

/-- `resumeSender` with the call bit set turns a parked call into `awaitReply`. -/
theorem resume_call_ok (D : Description) (sid : InstId) (a : Actor) (dst : InstId) (k : Cont)
    (hc : contTy a) (hg : programOk D sid a) (hw : waitEdge D sid a)
    (hph : a.phase = .parked dst true k) :
    let b := resumeSender a true dst
    b.typestate = a.typestate ∧ b.life = a.life ∧ contTy b ∧ programOk D sid b ∧ waitEdge D sid b ∧
      notParked b.phase ∧ b.parked = a.parked := by
  have hty : a.typestate = k.toState := by simpa [contTy, hph] using hc
  have hprog : effectsOk D (tname sid) a.typestate k.rest = true := by simpa [programOk, hph] using hg
  have hwait : ∃ label, hasEdge D (tname sid) a.typestate (tname dst) .call .blocking label = true := by
    simpa [waitEdge, hph] using hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [resumeSender, hph]
  · simp [resumeSender, hph]
  · simp [resumeSender, hph, contTy, hty]
  · simp [resumeSender, hph, programOk]
    exact hprog
  · simp [resumeSender, hph, waitEdge]
    exact hwait
  · simp [resumeSender, hph, notParked]
  · simp [resumeSender, hph]

structure DeliverInv (I : Impl) (w : World) (id : InstId) (a a' : Actor) (w' : World) : Prop where
  sem : SemInv I (setActor w' id a')
  life : a'.life = a.life
  parked : a'.parked = a.parked
  box : a'.box = a.box
  free : notParked a'.phase
  st : ∀ i, w'.st i = w.st i

theorem deliver_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w' : World) (a' : Actor) (hS : SemInv I w) (hlife : a.life = (w.st id).life)
    (hty : a.typestate = (w.st id).typestate) (halive : a.life = .alive) (hphase : a.phase = .idle)
    (h : deliver I w id a m = some (w', a')) : DeliverInv I w id a a' w' := by
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← h.1, ← h.2]
        apply sem_set I _ id _ (cells_sem I w id hS)
        · rw [readCells_st]; exact hty
        · rw [readCells_st, ← halive]; exact hlife
        · simp [contTy]
        · simp [programOk]
        · simp [waitEdge]
      · rw [← h.2, ← halive]
      · rw [← h.2]
      · rw [← h.2]
      · rw [← h.2]; simp [notParked]
      · intro i; rw [← h.1]; exact readCells_st I.desc w id i
  | some tr =>
    simp only [hf] at h
    by_cases href : m.callFrom.isSome = true ∧ tr.acceptsCall = false
    · rw [if_pos href] at h
      cases h
    · rw [if_neg href] at h
      cases h
      have hmem := findTr_mem I (tname id) a.typestate m.label tr hf
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · cases id with
        | core r =>
          apply sem_move I _ r _ tr (cells_sem I w _ hS) hL
          · rw [readCells_st, ← hty, hmem.2.2.1]
          · cases tr.program <;> rfl
          · cases tr.program <;> simp [readCells_st, ← halive, hlife]
          · exact hmem.2.1
          · exact hmem.1
          · cases tr.program <;> simp [contTy]
          · cases hp : tr.program with
            | nil => simp [hp, programOk]
            | cons _ _ =>
              simp [hp, programOk]
              simpa [hp, hmem.2.1] using effects_of_transition I hL tr hmem.1
          · cases tr.program <;> simp [waitEdge]
        | peer name ix =>
          apply sem_stable I _ _ (cells_sem I w _ hS)
          · intro _ _ role _
            rw [setActor_other _ _ (InstId.core role) _ (Ne.symm (peer_ne_core name ix role))]
          · intro _ _ role _
            rw [setActor_other _ _ (InstId.core role) _ (Ne.symm (peer_ne_core name ix role))]
          · intro i
            by_cases hi : i = .peer name ix
            · rw [hi, setActor_self]; cases tr.program <;> simp [contTy]
            · rw [setActor_other _ _ i _ hi]; exact (cells_sem I w _ hS).cont i
          · intro i
            by_cases hi : i = .peer name ix
            · rw [hi, setActor_self]
              cases hp : tr.program with
              | nil => simp [hp, programOk]
              | cons _ _ =>
                simp [hp, programOk]
                simpa [hp, hmem.2.1] using effects_of_transition I hL tr hmem.1
            · rw [setActor_other _ _ i _ hi]; exact (cells_sem I w _ hS).prog i
          · intro i
            by_cases hi : i = .peer name ix
            · rw [hi, setActor_self]; cases tr.program <;> simp [waitEdge]
            · rw [setActor_other _ _ i _ hi]; exact (cells_sem I w _ hS).waited i
      · cases tr.program <;> simp [halive]
      · cases tr.program <;> rfl
      · cases tr.program <;> rfl
      · cases tr.program <;> simp [notParked]
      · intro i; exact readCells_st I.desc w id i

theorem deliver_mail (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w' : World) (a' : Actor) (hS : SemInv I w) (hM : MailInv w) (hlife : a.life = (w.st id).life)
    (hty : a.typestate = (w.st id).typestate) (halive : a.life = .alive) (hphase : a.phase = .idle)
    (hidle : (w.st id).phase = .idle) (hpark : a.parked = (w.st id).parked)
    (h : deliver I w id a m = some (w', a')) : MailInv (setActor w' id a') := by
  have hd := deliver_inv I hL w id a m w' a' hS hlife hty halive hphase h
  have hM1 := mail_copy w w' hM hd.st
  exact mail_set_free w' id a' hM1 (by rw [hd.st, hidle]; simp [notParked]) hd.free
    (by rw [hd.parked, hd.st, hpark])

theorem receive_prio_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (wOut : World)
    (hS : SemInv I w) (hM : MailInv w) (halive : (w.st id).life = .alive)
    (hphase : (w.st id).phase = .idle) (h : receivePrio I w id = some wOut) :
    SemInv I wOut ∧ MailInv wOut := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp only [hp, halive, hphase] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := (w.st id).box, prio := ms,
          parked := (w.st id).parked, tokens := (w.st id).tokens }
        have hdI := deliver_inv I hL w id a0 m w1 a1 hS halive.symm rfl rfl rfl hd
        have hMail := deliver_mail I hL w id a0 m w1 a1 hS hM halive.symm rfl rfl rfl hphase rfl hd
        exact ⟨hdI.sem, hMail⟩

theorem resume_one (I : Impl) (w w1 : World) (id : InstId) (cur : Actor) (p : Parked) (ps : List Parked)
    (who : InstId) (hS : SemInv I (setActor w1 id cur)) (hM : MailInv w) (hst : ∀ i, w1.st i = w.st i)
    (hidle : (w.st id).phase = .idle) (hqueue : (w.st id).parked = p :: ps) (hcurPk : cur.parked = ps)
    (hcurPh : notParked cur.phase) :
    let credited := creditSender (setActor w1 id cur) (tname id) who
    SemInv I (setActor credited p.sender (resumeSender (credited.st p.sender) p.isCall id)) ∧
      MailInv (setActor credited p.sender (resumeSender (credited.st p.sender) p.isCall id)) := by
  let base := setActor w1 id cur
  let credited := creditSender base (tname id) who
  let wOut := setActor credited p.sender (resumeSender (credited.st p.sender) p.isCall id)
  obtain ⟨k, hk⟩ := hM.fwd id p (by rw [hqueue]; exact List.mem_cons_self)
  have hfree : notParked (w.st id).phase := by simp [hidle, notParked]
  have hsnd : p.sender ≠ id :=
    not_queued w id hM hfree id p (by rw [hqueue]; exact List.mem_cons_self)
  have hS1 := credit_sem I (setActor w1 id cur) (tname id) who hS
  have hbase : ((setActor w1 id cur).st p.sender) = w.st p.sender := by
    rw [setActor_other w1 id p.sender cur hsnd, hst]
  have hph : (credited.st p.sender).phase = .parked id p.isCall k := by
    rw [(credit_phase (setActor w1 id cur) (tname id) who p.sender).1, hbase, hk]
  have hpkS : (credited.st p.sender).parked = (w.st p.sender).parked := by
    rw [(credit_phase (setActor w1 id cur) (tname id) who p.sender).2, hbase]
  have htyS : (credited.st p.sender).typestate = (w.st p.sender).typestate := by
    rw [(credit_keeps_ty (setActor w1 id cur) (tname id) who p.sender).2, hbase]
  have hlifeS : (credited.st p.sender).life = (w.st p.sender).life := by
    rw [(credit_keeps_ty (setActor w1 id cur) (tname id) who p.sender).1, hbase]
  have hcont : contTy (credited.st p.sender) := by
    by_cases hwho : p.sender = who
    · subst hwho
      have hb := hS.cont p.sender
      unfold credited; unfold creditSender; rw [ setActor_self]
      exact Eq.mp ((ok_tokens I.desc p.sender ((setActor w1 id cur).st p.sender) (tname id) (.ofNat 1)).1).symm hb
    · unfold credited; unfold creditSender; rw [ setActor_other _ who p.sender _ hwho]
      exact hS.cont p.sender
  have hprog : programOk I.desc p.sender (credited.st p.sender) := by
    by_cases hwho : p.sender = who
    · subst hwho
      have hb := hS.prog p.sender
      unfold credited; unfold creditSender; rw [ setActor_self]
      exact Eq.mp ((ok_tokens I.desc p.sender ((setActor w1 id cur).st p.sender) (tname id) (.ofNat 1)).2.1).symm hb
    · unfold credited; unfold creditSender; rw [ setActor_other _ who p.sender _ hwho]
      exact hS.prog p.sender
  have hwait : waitEdge I.desc p.sender (credited.st p.sender) := by
    by_cases hwho : p.sender = who
    · subst hwho
      have hb := hS.waited p.sender
      unfold credited; unfold creditSender; rw [ setActor_self]
      exact Eq.mp ((ok_tokens I.desc p.sender ((setActor w1 id cur).st p.sender) (tname id) (.ofNat 1)).2.2).symm hb
    · unfold credited; unfold creditSender; rw [ setActor_other _ who p.sender _ hwho]
      exact hS.waited p.sender
  have hstep : SemInv I wOut ∧ notParked (wOut.st p.sender).phase ∧ (wOut.st p.sender).parked = (w.st p.sender).parked := by
    unfold wOut credited
    cases hc : p.isCall with
    | false =>
      have hr := resume_false_ok I.desc p.sender (credited.st p.sender) id hcont hprog hwait
      refine ⟨sem_set I credited p.sender (resumeSender (credited.st p.sender) false id) hS1 hr.1 hr.2.1
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1, ?_, ?_⟩
      · rw [setActor_self]; exact hr.2.2.2.2.2.1
      · rw [setActor_self, hr.2.2.2.2.2.2, hpkS]
    | true =>
      have hr := resume_call_ok I.desc p.sender (credited.st p.sender) id k hcont hprog hwait (by rw [hph, hc])
      refine ⟨sem_set I credited p.sender (resumeSender (credited.st p.sender) true id) hS1 hr.1 hr.2.1
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1, ?_, ?_⟩
      · rw [setActor_self]; exact hr.2.2.2.2.2.1
      · rw [setActor_self, hr.2.2.2.2.2.2, hpkS]
  have hidPh : notParked (wOut.st id).phase := by
    rw [setActor_other _ p.sender id _ hsnd.symm]
    by_cases hwho : id = who
    · subst hwho
      simp [credited, creditSender, base, setActor_self, bumpToken]
      exact hcurPh
    · unfold credited; unfold creditSender; rw [setActor_other _ who id _ hwho, setActor_self]
      exact hcurPh
  have hidPk : (wOut.st id).parked = ps := by
    rw [setActor_other _ p.sender id _ hsnd.symm]
    by_cases hwho : id = who
    · subst hwho
      simp [credited, creditSender, base, setActor_self, bumpToken, hcurPk]
    · unfold credited; unfold creditSender; rw [ setActor_other _ who id _ hwho, setActor_self, hcurPk]
  have hpkO : ∀ i, i ≠ id → (wOut.st i).parked = (w.st i).parked := by
    intro i hi
    by_cases hself : i = p.sender
    · rw [hself]; exact hstep.2.2
    · rw [setActor_other _ p.sender i _ hself]
      by_cases hwho : i = who
      · subst hwho
        unfold credited; unfold creditSender; rw [ setActor_self, setActor_other w1 id i cur hi, hst]
        simp [bumpToken]
      · unfold credited; unfold creditSender; rw [ setActor_other _ who i _ hwho, setActor_other w1 id i cur hi, hst]
  have hother : ∀ i, i ≠ id → i ≠ p.sender → (wOut.st i).phase = (w.st i).phase := by
    intro i hi hs
    rw [setActor_other _ p.sender i _ hs]
    by_cases hwho : i = who
    · subst hwho
      unfold credited; unfold creditSender; rw [ setActor_self, setActor_other w1 id i cur hi, hst]
      simp [bumpToken]
    · unfold credited; unfold creditSender; rw [ setActor_other _ who i _ hwho, setActor_other w1 id i cur hi, hst]
  exact ⟨hstep.1, mail_drop w wOut id p ps hM hfree hqueue hidPh hidPk hpkO hstep.2.1 hother⟩

theorem receive_bulk_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (wOut : World)
    (hS : SemInv I w) (hM : MailInv w) (halive : (w.st id).life = .alive)
    (hphase : (w.st id).phase = .idle) (h : receiveBulk I w id = some wOut) :
    SemInv I wOut ∧ MailInv wOut := by
  unfold receiveBulk at h
  simp only [halive, hphase] at h
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
          parked := ps, tokens := (w.st id).tokens }
        have hdI := deliver_inv I hL w id a0 p.msg w1 a1 hS halive.symm rfl rfl rfl hd
        simpa using resume_one I w w1 id a1 p ps p.msg.sender hdI.sem hM hdI.st hphase hpk hdI.parked hdI.free
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
          parked := [], tokens := (w.st id).tokens }
        have hdI := deliver_inv I hL w id a0 m w1 a1 hS halive.symm rfl rfl rfl hd
        have hMail := deliver_mail I hL w id a0 m w1 a1 hS hM halive.symm rfl rfl rfl hphase (by simp [a0, hpk]) hd
        exact ⟨credit_sem I (setActor w1 id a1) (tname id) m.sender hdI.sem,
          credit_mail I (setActor w1 id a1) (tname id) m.sender hMail⟩
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := ms, prio := (w.st id).prio,
          parked := p :: ps, tokens := (w.st id).tokens }
        have hdI := deliver_inv I hL w id a0 m w1 a1 hS halive.symm rfl rfl rfl hd
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hAd := sem_set I (setActor w1 id a1) id admitted hdI.sem
          (by simp [admitted, setActor_self]) (by simp [admitted, setActor_self])
          (by
            have hc := hdI.sem.cont id
            rw [setActor_self] at hc
            change contTy a1
            exact hc)
          (by
            have hg := hdI.sem.prog id
            rw [setActor_self] at hg
            change programOk I.desc id a1
            exact hg)
          (by
            have hw := hdI.sem.waited id
            rw [setActor_self] at hw
            change waitEdge I.desc id a1
            exact hw)
        have hsame : setActor (setActor w1 id a1) id admitted = setActor w1 id admitted := by
          simp [setActor]
          funext i
          by_cases hi : i = id <;> simp [hi]
        rw [hsame] at hAd
        have hfree : notParked admitted.phase := hdI.free
        simpa using resume_one I w w1 id admitted p ps m.sender hAd hM hdI.st hphase hpk rfl hfree

/-- The peer index spawn overwrites is idle and has an empty parked list. -/
def slotFree (w : World) (template : String) : Prop :=
  (w.st (InstId.peer template (w.nextIx template))).phase = .idle ∧
    (w.st (InstId.peer template (w.nextIx template))).parked = []

def growRoster (w : World) (pid : InstId) (template : String) : World :=
  { w with
    roster := w.roster ++ [pid]
    nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n }

def bornPeer (I : Impl) (template initial : String) : Actor :=
  withTokens I.desc template
    { life := .alive, typestate := initial, phase := .idle, box := [], prio := [], parked := [],
      tokens := fun _ => 0 }

theorem spawn_mail (I : Impl) (w : World) (template : String) (w' : World) (hM : MailInv w)
    (hfree : slotFree w template) (h : spawn I w template = some w') : MailInv w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t _ =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      let pid := InstId.peer template (w.nextIx template)
      have hst : ∀ i, (growRoster w pid template).st i = w.st i := by
        intro _; rfl
      have hMg := mail_copy w _ hM hst
      have hM1 := mail_set_same _ pid (bornPeer I template t.initial) hMg
        (by simp [bornPeer, withTokens, hst]; exact hfree.1.symm)
        (by simp [bornPeer, withTokens, hst]; exact hfree.2)
      exact mail_copy _ _ hM1 fun i => readCells_st I.desc _ pid i
    · simp [hif] at h

theorem spawn_inv (I : Impl) (w : World) (template : String) (w' : World) (hS : SemInv I w)
    (hM : MailInv w) (hfree : slotFree w template) (h : spawn I w template = some w') :
    SemInv I w' ∧ MailInv w' :=
  ⟨spawn_sem I w w' template hS h, spawn_mail I w template w' hM hfree h⟩

theorem finish_inv (I : Impl) (w w' : World) (id : InstId) (hS : SemInv I w) (hM : MailInv w)
    (h : finishWait I w id = some w') : SemInv I w' ∧ MailInv w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
      simpa [programOk, hph] using hS.prog id
    have hfree : notParked (w.st id).phase := by simp [notParked, hph]
    exact proceed_sender I w id k k.rest k.replyTo hS hM hty hprog hfree
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
      simpa [programOk, hph] using hS.prog id
    have hfree : notParked (w.st id).phase := by simp [notParked, hph]
    exact proceed_sender I w id k k.rest k.replyTo hS hM hty hprog hfree
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

/-- One running head: every effect, including a parking send or call and a killing terminate. -/
theorem exec_head_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (w' : World)
    (hS : SemInv I w) (hM : MailInv w) (h : execHead I w id = some w') :
    SemInv I w' ∧ MailInv w' := by
  simp only [execHead] at h
  split at h
  · cases h
  · split at h
    · next k hph =>
      cases h
      have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
        simpa [programOk, hph] using hS.prog id
      cases hk : k.rest with
      | nil =>
        let k' : Cont := { rest := [], toState := k.toState, replyTo := k.replyTo }
        have hk' : k = k' := by
          cases k with
          | mk r t o =>
            simp [k', show r = [] from hk]
        have hphase : (w.st id).phase = .run k' := by rw [hk'] at hph; exact hph
        rw [hk']
        exact exec_done_inv I w id k' hS hM hphase
      | cons e es =>
        let k' : Cont := { rest := e :: es, toState := k.toState, replyTo := k.replyTo }
        have hk' : k = k' := by
          cases k with
          | mk r t o =>
            simp [k', show r = e :: es from hk]
        have hphase : (w.st id).phase = .run k' := by rw [hk'] at hph; exact hph
        have hprog' : effectsOk I.desc (tname id) (w.st id).typestate k'.rest = true := by
          rw [hk'] at hprog; exact hprog
        rw [hk']
        cases e with
        | internal =>
          exact exec_basic_inv I w id k' .internal es hS hM hphase hprog' (Or.inl rfl)
        | peer =>
          exact exec_basic_inv I w id k' .peer es hS hM hphase hprog' (Or.inr (Or.inl rfl))
        | send d l n =>
          exact exec_basic_inv I w id k' (.send d l n) es hS hM hphase hprog'
            (Or.inr (Or.inr (Or.inl ⟨d, l, n, rfl⟩)))
        | call d l n =>
          exact exec_basic_inv I w id k' (.call d l n) es hS hM hphase hprog'
            (Or.inr (Or.inr (Or.inr ⟨d, l, n, rfl⟩)))
        | trySend d l n =>
          exact exec_try_sem I w id k' d l n es hS hM hphase hprog'
        | reply =>
          exact exec_reply_sem I w id k' es hS hM hphase hprog'
        | selfSchedule label =>
          exact exec_sched_sem I w id k' label es hS hM hphase hprog'
        | cell dst label value =>
          exact exec_cell_sem I w id k' dst label value es hS hM hphase hprog'
        | terminate =>
          cases ht : templateOf I.desc (tname id) with
          | none =>
            exact exec_term_skip_sem I w id k' es hS hM hphase
              (by intro _ ht'; simp [ht] at ht')
          | some t =>
            by_cases hkill : t.terminable = true ∧ hasParkedCall (w.st id).parked = false
            · exact exec_term_die_sem I hL w id t k' es hS hM hphase ht hkill.1 hkill.2
            · exact exec_term_skip_sem I w id k' es hS hM hphase
                (by
                  intro t' ht'
                  have : t' = t := by rw [ht] at ht'; cases ht'; rfl
                  simpa [this] using hkill)
    · cases h

/-- Peer indices at or above `nextIx` have not been spawned. -/
def OpenSlots (w : World) : Prop :=
  ∀ template i, w.nextIx template ≤ i →
    (w.st (InstId.peer template i)).life = .absent ∧
      (w.st (InstId.peer template i)).phase = .idle ∧
      (w.st (InstId.peer template i)).parked = []

theorem open_slot (w : World) (h : OpenSlots w) (template : String) : slotFree w template := by
  have h0 := h template (w.nextIx template) (Nat.le_refl _)
  exact ⟨h0.2.1, h0.2.2⟩

theorem not_open (w : World) (h : OpenSlots w) (id : InstId) (template : String) (i : Nat)
    (hi : w.nextIx template ≤ i) (hid : id = InstId.peer template i)
    (hlive : (w.st id).life = .alive) : False := by
  have h0 := h template i hi
  rw [hid] at hlive
  simp [hlive] at h0

theorem read_ix (D : Description) (w : World) (id : InstId) (template : String) :
    (readCells D w id).nextIx template = w.nextIx template := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem actor_ix (w : World) (id : InstId) (a : Actor) (template : String) :
    (setActor w id a).nextIx template = w.nextIx template := by
  simp [setActor]

theorem credit_ix (w : World) (tmpl : String) (sender : InstId) (template : String) :
    (creditSender w tmpl sender).nextIx template = w.nextIx template := by
  simp [creditSender, setActor]

/-- A step is one successful `apply`. -/
def Step (I : Impl) (w w' : World) : Prop :=
  ∃ a, apply I a w = some w'

theorem not_open_phase (w : World) (h : OpenSlots w) (id : InstId) (template : String) (i : Nat)
    (hi : w.nextIx template ≤ i) (hid : id = InstId.peer template i)
    (hph : (w.st id).phase ≠ .idle) : False := by
  have h0 := h template i hi
  rw [hid] at hph
  exact hph h0.2.1

theorem open_set (w : World) (id : InstId) (a : Actor) (hO : OpenSlots w)
    (hkeep : ∀ template i, w.nextIx template ≤ i → id = InstId.peer template i →
      a.life = .absent ∧ a.phase = .idle ∧ a.parked = []) :
    OpenSlots (setActor w id a) := by
  intro template i hi
  rw [actor_ix] at hi
  by_cases hid : id = InstId.peer template i
  · rw [hid, setActor_self]
    exact hkeep template i hi hid
  · rw [setActor_other w id (InstId.peer template i) a (Ne.symm hid)]
    exact hO template i hi

theorem open_alive (w : World) (id : InstId) (a : Actor) (hO : OpenSlots w)
    (hlive : (w.st id).life = .alive) : OpenSlots (setActor w id a) := by
  refine open_set w id a hO ?_
  intro template i hi hid
  exact False.elim (not_open w hO id template i hi hid hlive)

theorem open_busy (w : World) (id : InstId) (a : Actor) (hO : OpenSlots w)
    (hph : (w.st id).phase ≠ .idle) : OpenSlots (setActor w id a) := by
  refine open_set w id a hO ?_
  intro template i hi hid
  exact False.elim (not_open_phase w hO id template i hi hid hph)

theorem open_read (D : Description) (w : World) (id : InstId) (hO : OpenSlots w) :
    OpenSlots (readCells D w id) := by
  intro template i hi
  rw [read_ix] at hi
  rw [readCells_st]
  exact hO template i hi

theorem open_credit (w : World) (tmpl : String) (sender : InstId) (hO : OpenSlots w) :
    OpenSlots (creditSender w tmpl sender) := by
  refine open_set w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) hO ?_
  intro template i hi hid
  rw [hid]
  have h0 := hO template i hi
  simp [bumpToken, h0]

theorem coreRoster_is_core (D : Description) (id : InstId) (h : id ∈ coreRoster D) :
    ∃ name, id = InstId.core name := by
  simp [coreRoster, List.mem_filterMap] at h
  obtain ⟨t, _, ht⟩ := h
  obtain ⟨_, hid⟩ := ht
  exact ⟨t.name, hid.symm⟩

theorem peer_not_roster (D : Description) (template : String) (i : Nat) :
    (coreRoster D).contains (InstId.peer template i) = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  have hmem : InstId.peer template i ∈ coreRoster D := by
    simpa [List.contains_iff_mem] using htrue
  obtain ⟨_, hn⟩ := coreRoster_is_core D _ hmem
  cases hn

theorem foldl_read_ix (D : Description) (ids : List InstId) (w : World) (template : String) :
    ((ids.foldl (fun w id => readCells D w id) w).nextIx template) = w.nextIx template := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    rw [List.foldl_cons, ih (readCells D w id), read_ix]

theorem init_ix (I : Impl) (N : Nat) (template : String) : (initWorld I N).nextIx template = 0 := by
  unfold initWorld
  simpa using foldl_read_ix I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } template

theorem open_init (I : Impl) (N : Nat) : OpenSlots (initWorld I N) := by
  intro template i hi
  rw [init_ix] at hi
  rw [init_base_st]
  rw [peer_not_roster]
  simp [absentActor]

theorem open_grow (w : World) (pid : InstId) (template : String) (hO : OpenSlots w) :
    OpenSlots (growRoster w pid template) := by
  intro t i hi
  by_cases ht : t = template
  · have hi' : w.nextIx t + 1 ≤ i := by simpa [growRoster, ht] using hi
    have hold : w.nextIx t ≤ i := Nat.le_trans (Nat.le_succ _) hi'
    exact hO t i hold
  · have hi' : w.nextIx t ≤ i := by simpa [growRoster, ht] using hi
    exact hO t i hi'

theorem open_spawn (I : Impl) (w : World) (template : String) (w' : World) (hO : OpenSlots w)
    (h : spawn I w template = some w') : OpenSlots w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t _ =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      let pid := InstId.peer template (w.nextIx template)
      have hO1 := open_grow w pid template hO
      have hkeep : ∀ t' i, (growRoster w pid template).nextIx t' ≤ i →
          pid = InstId.peer t' i →
          (bornPeer I template t.initial).life = .absent ∧
            (bornPeer I template t.initial).phase = .idle ∧
            (bornPeer I template t.initial).parked = [] := by
        intro t' i hi hid
        have hpid : pid = InstId.peer template (w.nextIx template) := rfl
        rw [hpid] at hid
        cases hid
        have hi' : w.nextIx template + 1 ≤ w.nextIx template := by simpa [growRoster] using hi
        exact False.elim (Nat.not_succ_le_self _ hi')
      exact open_read I.desc _ pid (open_set _ pid _ hO1 hkeep)
    · simp [hif] at h

theorem open_finish (I : Impl) (w : World) (id : InstId) (w' : World) (hO : OpenSlots w)
    (h : finishWait I w id = some w') : OpenSlots w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    exact open_busy w id _ hO (by rw [hph]; intro hbad; cases hbad)
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    exact open_busy w id _ hO (by rw [hph]; intro hbad; cases hbad)
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem deliver_st (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (i : InstId) (h : deliver I w id a m = some (w1, a1)) : w1.st i = w.st i := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact readCells_st I.desc w id i
    · split at h
      · cases h
      · cases h
        exact readCells_st I.desc w id i

theorem deliver_ix (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (template : String) (h : deliver I w id a m = some (w1, a1)) :
    w1.nextIx template = w.nextIx template := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact read_ix I.desc w id template
    · split at h
      · cases h
      · cases h
        exact read_ix I.desc w id template

theorem receive_ready (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : receiveBulk I w id = some w') :
    (w.st id).life = .alive ∧ (w.st id).phase = .idle := by
  simp only [receiveBulk] at h
  split at h
  · cases h
  · next hf =>
    simp [Bool.or_eq_false_iff] at hf
    have h1 : ¬ (w.st id).life ≠ .alive := by simpa [decide_eq_false_iff_not] using hf.1
    have h2 : ¬ (w.st id).phase ≠ .idle := by simpa [decide_eq_false_iff_not] using hf.2
    exact ⟨by simpa using h1, by simpa using h2⟩

theorem prio_ready (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : receivePrio I w id = some w') :
    (w.st id).life = .alive ∧ (w.st id).phase = .idle := by
  simp only [receivePrio] at h
  split at h
  · cases h
  · split at h
    · cases h
    · next hf =>
      simp [Bool.or_eq_false_iff] at hf
      have h1 : ¬ (w.st id).life ≠ .alive := by simpa [decide_eq_false_iff_not] using hf.1
      have h2 : ¬ (w.st id).phase ≠ .idle := by simpa [decide_eq_false_iff_not] using hf.2
      exact ⟨by simpa using h1, by simpa using h2⟩

theorem open_same (w w' : World) (hO : OpenSlots w) (hn : ∀ t, w'.nextIx t = w.nextIx t)
    (hs : ∀ i, w'.st i = w.st i) : OpenSlots w' := by
  intro t i hi
  rw [hn] at hi
  rw [hs]
  exact hO t i hi

theorem open_resume (w : World) (sid : InstId) (isCall : Bool) (dst : InstId) (hO : OpenSlots w) :
    OpenSlots (setActor w sid (resumeSender (w.st sid) isCall dst)) := by
  by_cases hph : (w.st sid).phase = .idle
  · refine open_set w sid _ hO ?_
    intro template i hi hid
    rw [hid] at hph ⊢
    simp [resumeSender, hph]
    exact ⟨(hO template i hi).1, (hO template i hi).2.2⟩
  · exact open_busy w sid _ hO hph

theorem open_prio (I : Impl) (w : World) (id : InstId) (w' : World) (hO : OpenSlots w)
    (h : receivePrio I w id = some w') : OpenSlots w' := by
  have hready := prio_ready I w id w' h
  simp only [receivePrio] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hO1 := open_same w w1 hO (fun t => deliver_ix I w id _ _ w1 a1 t hd)
          (fun i => deliver_st I w id _ _ w1 a1 i hd)
        have hlive : (w1.st id).life = .alive := by
          rw [deliver_st I w id _ _ w1 a1 id hd]
          exact hready.1
        exact open_alive w1 id a1 hO1 hlive

theorem open_after_deliver (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (hO : OpenSlots w) (hlive : (w.st id).life = .alive)
    (h : deliver I w id a m = some (w1, a1)) : OpenSlots (setActor w1 id a1) := by
  have hO1 := open_same w w1 hO (fun t => deliver_ix I w id a m w1 a1 t h)
    (fun i => deliver_st I w id a m w1 a1 i h)
  have hlive1 : (w1.st id).life = .alive := by rw [deliver_st I w id a m w1 a1 id h]; exact hlive
  exact open_alive w1 id a1 hO1 hlive1

theorem open_bulk (I : Impl) (w : World) (id : InstId) (w' : World) (hO : OpenSlots w)
    (h : receiveBulk I w id = some w') : OpenSlots w' := by
  have hready := receive_ready I w id w' h
  simp only [receiveBulk] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        exact open_credit _ _ _ (open_after_deliver I w id _ _ w1 a1 hO hready.1 hd)
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hbase := open_same w w1 hO (fun t => deliver_ix I w id _ _ w1 a1 t hd)
          (fun i => deliver_st I w id _ _ w1 a1 i hd)
        have hlive1 : (w1.st id).life = .alive := by
          rw [deliver_st I w id _ _ w1 a1 id hd]; exact hready.1
        exact open_resume _ _ _ _ (open_credit _ _ _ (open_alive w1 id _ hbase hlive1))
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        exact open_resume _ _ _ _ (open_credit _ _ _ (open_after_deliver I w id _ _ w1 a1 hO hready.1 hd))
    · cases h

theorem enqueue_open (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (hO : OpenSlots w) (hs : (w.st sender).phase ≠ .idle) :
    OpenSlots (enqueueOrPark w D sender dst msg isCall k) := by
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · simp [halive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      by_cases hsame : sender = dst
      · simp [hsame]
        split
        · exact open_busy w dst _ hO (by simpa [hsame] using hs)
        · exact open_busy w dst _ hO (by simpa [hsame] using hs)
      · simp [hsame]
        split
        · apply open_busy
          · exact open_alive w dst _ hO halive
          · rw [setActor_other _ dst sender _ hsame]
            exact hs
        · apply open_busy
          · exact open_alive w dst _ hO halive
          · rw [setActor_other _ dst sender _ hsame]
            exact hs
    · simp [hroom]
      by_cases hsame : sender = dst
      · simp [hsame]
        exact open_busy w dst _ hO (by simpa [hsame] using hs)
      · simp [hsame]
        apply open_busy
        · exact open_alive w dst _ hO halive
        · rw [setActor_other _ dst sender _ hsame]
          exact hs
  · simp [halive]
    exact open_busy w sender _ hO hs

theorem open_tryWake (D : Description) (w : World) (id : InstId) (label : String) (writer : InstId)
    (hO : OpenSlots w) : OpenSlots (tryWake D w id label writer) := by
  simp only [tryWake]
  split
  · next hcond =>
    apply open_alive
    · exact hO
    · simp [Bool.and_eq_true] at hcond
      exact hcond.1.1
  · exact hO

theorem open_wakes (D : Description) (w : World) (ids : List InstId) (label : String) (writer : InstId)
    (hO : OpenSlots w) : OpenSlots (ids.foldl (fun w i => tryWake D w i label writer) w) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons i ids ih =>
    rw [List.foldl_cons]
    exact ih _ (open_tryWake D w i label writer hO)

theorem open_msgs (w : World) (dst : String) (ms : List Msg) (hO : OpenSlots w) :
    OpenSlots (refundMsgs w dst ms) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using hO
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact ih _ (open_credit w dst m.sender hO)

theorem open_parks (w : World) (dst : String) (ps : List Parked) (hO : OpenSlots w) :
    OpenSlots (refundParked w dst ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hO
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih _ (open_credit w dst p.msg.sender hO)

theorem open_release_fold (id : InstId) (ps : List Parked) (w : World) (hO : OpenSlots w) :
    OpenSlots (releaseFold id ps w) := by
  induction ps generalizing w with
  | nil => simpa [releaseFold] using hO
  | cons p ps ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change OpenSlots (releaseFold id ps w)
      exact ih _ hO
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change OpenSlots (releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id)))
      exact ih _ (open_resume w p.sender false id hO)

theorem open_release (w : World) (id : InstId) (ps : List Parked) (hO : OpenSlots w) :
    OpenSlots (releaseParked w id ps) := by
  simpa [release_fold_eq] using open_release_fold id ps w hO

theorem busy_run (id : InstId) (w : World) (k : Cont) (h : (w.st id).phase = .run k) :
    (w.st id).phase ≠ .idle := by
  rw [h]
  intro hbad
  cases hbad

theorem exec_run_open (I : Impl) (w : World) (id : InstId) (k : Cont) (hO : OpenSlots w)
    (hlive : (w.st id).life = .alive) (hph : (w.st id).phase = .run k) :
    OpenSlots (execRun I w id (w.st id) k) := by
  cases hk : k.rest with
  | nil =>
    simp [execRun, hk]
    exact open_busy w id _ hO (busy_run id w k hph)
  | cons e es =>
    cases e with
    | internal =>
      simp [execRun, hk]
      exact open_busy w id _ hO (busy_run id w k hph)
    | peer =>
      simp [execRun, hk]
      exact open_busy w id _ hO (busy_run id w k hph)
    | send d l n =>
      cases hr : route w I.desc d n with
      | none =>
        simp [execRun, hk, hr]
        exact open_busy w id _ hO (busy_run id w k hph)
      | some dst =>
        simp [execRun, hk, hr]
        exact enqueue_open w I.desc id dst _ false _ hO (busy_run id w k hph)
    | call d l n =>
      cases hr : route w I.desc d n with
      | none =>
        simp [execRun, hk, hr]
        exact open_busy w id _ hO (busy_run id w k hph)
      | some dst =>
        simp [execRun, hk, hr]
        exact enqueue_open w I.desc id dst _ true _ hO (busy_run id w k hph)
    | trySend d l n =>
      cases hr : route w I.desc d n with
      | none =>
        simp [execRun, hk, hr]
        exact open_busy w id _ hO (busy_run id w k hph)
      | some dst =>
        simp [execRun, hk, hr]
        split
        · next hcond =>
          by_cases hsame : dst = id
          · rw [hsame]
            have h1 := open_busy w id (chargeSender (w.st id) (tname id)) hO (busy_run id w k hph)
            have hph1 : ((setActor w id (chargeSender (w.st id) (tname id))).st id).phase ≠ .idle := by
              simp [setActor_self, chargeSender, bumpToken, hph]
            exact open_busy _ id _ (open_busy _ id _ h1 hph1)
              (by simp [setActor_self, chargeSender, bumpToken, hph])
          · exact open_busy _ id _
              (open_alive _ dst _
                (open_busy w id _ hO (busy_run id w k hph))
                (by rw [setActor_other _ id dst _ hsame]; exact hcond.1.1))
              (by rw [setActor_other _ dst id _ (Ne.symm hsame), setActor_self, chargeSender, bumpToken, hph]
                  intro hbad; cases hbad)
        · exact open_busy w id _ hO (busy_run id w k hph)
    | reply =>
      simp [execRun, hk, performReply]
      split
      · exact open_busy w id _ hO (busy_run id w k hph)
      · rename_i caller hto
        split
        all_goals first
          | exact open_busy w id _ hO (busy_run id w k hph)
          | (rename_i dst ck hphc
             split
             · by_cases hsc : caller = id
               · rw [hsc] at hphc ⊢
                 exact open_alive _ id _
                   (open_busy w id _ hO (by rw [hphc]; intro hbad; cases hbad))
                   (by simp [setActor_self, proceed]; split <;> exact hlive)
               · exact open_busy _ id _
                   (open_busy w caller _ hO (by rw [hphc]; intro hbad; cases hbad))
                   (by rw [setActor_other _ caller id _ (Ne.symm hsc)]; exact busy_run id w k hph)
             · exact open_busy w id _ hO (busy_run id w k hph))
    | selfSchedule _ =>
      simp [execRun, hk]
      split <;> try split
      · exact open_busy w id _ hO (busy_run id w k hph)
      · exact open_busy w id _ hO (busy_run id w k hph)
      · exact open_busy w id _ hO (busy_run id w k hph)
    | cell dst label value =>
      simp [execRun, hk]
      have hcell : OpenSlots (setCell w dst label { value := max (w.cell dst label).value value, dirty := true }) := by
        intro t i hi
        simp [setCell] at hi ⊢
        exact hO t i hi
      split
      · exact open_busy _ id _ hcell (by simp [setCell, hph])
      · exact open_wakes I.desc _ (readersOf _ dst) label id
          (open_busy _ id _ hcell (by simp [setCell, hph]))
    | terminate =>
      simp [execRun, hk]
      split
      · next t ht =>
        split
        · have hbase := open_parks _ (tname id) (w.st id).parked
            (open_msgs _ (tname id) (w.st id).box (open_read I.desc w id hO))
          exact open_release _ id (w.st id).parked
            (open_busy _ id _ hbase (by
              rw [(refund_park_phase _ (tname id) (w.st id).parked id).1,
                (refund_msgs_phase _ (tname id) (w.st id).box id).1, readCells_st, hph]
              intro hbad
              cases hbad))
        · exact hO
      · exact hO

theorem exec_head_open (I : Impl) (w : World) (id : InstId) (w' : World) (hO : OpenSlots w)
    (h : execHead I w id = some w') : OpenSlots w' := by
  simp only [execHead] at h
  split at h
  · cases h
  · next hnot =>
    split at h
    · next k hph =>
      cases h
      have hlive : (w.st id).life = .alive := by
        simpa [decide_eq_false_iff_not] using hnot
      exact exec_run_open I w id k hO hlive hph
    · cases h

/-- `SemInv`, `MailInv`, and the unspawned peer indices, together. -/
theorem ingress_parked (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (w'.st i).parked = (w.st i).parked ∧ (w'.st i).phase = (w.st i).phase ∧
      (w'.st i).life = (w.st i).life := by
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
            by_cases hi : i = dst
            · simp [setActor, hi, chargeSender, bumpToken]
            · simp [setActor, hi]

theorem ingress_mail (I : Impl) (w w' : World) (dst : InstId) (label : String) (hM : MailInv w)
    (h : receiveIngress I w dst label = some w') : MailInv w' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    have hpk := (ingress_parked I w w' dst label mb h).1
    rw [hpk] at hp
    obtain ⟨k, hk⟩ := hM.fwd mb p hp
    exact ⟨k, by simpa [(ingress_parked I w w' dst label p.sender h).2.1] using hk⟩
  · intro id mb c k hk
    have hph := (ingress_parked I w w' dst label id h).2.1
    rw [hph] at hk
    obtain ⟨p, hp, hs, hc⟩ := hM.bwd id mb c k hk
    exact ⟨p, by simpa [(ingress_parked I w w' dst label mb h).1] using hp, hs, hc⟩
  · intro mb1 mb2 p1 p2 hp1 hp2 hsame
    have h1 := (ingress_parked I w w' dst label mb1 h).1
    have h2 := (ingress_parked I w w' dst label mb2 h).1
    rw [h1] at hp1
    rw [h2] at hp2
    exact hM.uniq mb1 mb2 p1 p2 hp1 hp2 hsame
  · intro mb
    simpa [(ingress_parked I w w' dst label mb h).1] using hM.once mb

theorem open_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String) (hO : OpenSlots w)
    (h : receiveIngress I w dst label = some w') : OpenSlots w' := by
  intro template i hi
  have hix : w'.nextIx = w.nextIx := (ingress_phase I w w' dst label (InstId.peer template i) h).2.2.2.2.2.2.1
  have hst := ingress_parked I w w' dst label (InstId.peer template i) h
  rw [hix] at hi
  have hold := hO template i hi
  exact ⟨hst.2.2.trans hold.1, hst.2.1.trans hold.2.1, hst.1.trans hold.2.2⟩

def Inv (I : Impl) (w : World) : Prop :=
  SemInv I w ∧ MailInv w ∧ OpenSlots w

theorem step_inv (I : Impl) (hL : LocalOk I) (w w' : World) (hstep : Step I w w')
    (h : Inv I w) : Inv I w' := by
  obtain ⟨a, ha⟩ := hstep
  rcases h with ⟨hS, hM, hO⟩
  cases a with
  | recvBulk id =>
    have hready := receive_ready I w id w' ha
    have hinv := receive_bulk_inv I hL w id w' hS hM hready.1 hready.2 ha
    exact ⟨hinv.1, hinv.2, open_bulk I w id w' hO ha⟩
  | recvPrio id =>
    have hready := prio_ready I w id w' ha
    have hinv := receive_prio_inv I hL w id w' hS hM hready.1 hready.2 ha
    exact ⟨hinv.1, hinv.2, open_prio I w id w' hO ha⟩
  | exec id =>
    exact ⟨(exec_head_inv I hL w id w' hS hM ha).1, (exec_head_inv I hL w id w' hS hM ha).2,
      exec_head_open I w id w' hO ha⟩
  | finish id =>
    exact ⟨(finish_inv I w w' id hS hM ha).1, (finish_inv I w w' id hS hM ha).2, open_finish I w id w' hO ha⟩
  | spawn template =>
    exact ⟨(spawn_inv I w template w' hS hM (open_slot w hO template) ha).1,
      (spawn_inv I w template w' hS hM (open_slot w hO template) ha).2, open_spawn I w template w' hO ha⟩
  | ingress dst label =>
    exact ⟨ingress_sem I w w' dst label hS ha, ingress_mail I w w' dst label hM ha,
      open_ingress I w w' dst label hO ha⟩
  | stutter =>
    cases stutter_unchanged I w w' ha
    exact ⟨hS, hM, hO⟩

theorem inv_init (I : Impl) (N : Nat) (hL : LocalOk I) : Inv I (initWorld I N) :=
  ⟨semInv_init I N hL, mail_init I N, open_init I N⟩

theorem inv_reachable (I : Impl) (N : Nat) (w : World) (hL : LocalOk I) (hR : Reachable I N w) :
    Inv I w := by
  induction hR with
  | init => exact inv_init I N hL
  | step _ _ _ _ ha ih => exact step_inv I hL _ _ ⟨_, ha⟩ ih

theorem effect_beq (a b : EffectKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem kind_beq (a b : EdgeKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem hasEdge_mem (D : Description) (src ss dst : String) (effect : EffectKind) (kind : EdgeKind)
    (label : String) (h : hasEdge D src ss dst effect kind label = true) :
    ∃ e, e ∈ D.edges ∧ e.src = src ∧ e.srcState = ss ∧ e.dst = dst ∧
      e.effect = effect ∧ e.kind = kind ∧ e.label = label := by
  simp [hasEdge, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
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
