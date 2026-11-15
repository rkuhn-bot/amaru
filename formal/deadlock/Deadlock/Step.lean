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

end Deadlock
