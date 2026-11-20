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

/-- A missed route records a failure and does not change any actor. Invariants
that read only `st` carry across. -/
theorem sem_note (I : Impl) (w : World) (sender : InstId) (dst : String) (id : InstId) (a : Actor)
    (hS : SemInv I (setActor w id a)) : SemInv I (setActor (noteStale w sender dst) id a) := by
  apply sem_stable I (setActor w id a) (setActor (noteStale w sender dst) id a) hS
  · intro g _ r _
    simp [setActor, noteStale]
  · intro g _ r _
    simp [setActor, noteStale]
  · intro i
    simpa [setActor, noteStale] using hS.cont i
  · intro i
    simpa [setActor, noteStale] using hS.prog i
  · intro i
    simpa [setActor, noteStale] using hS.waited i
  · intro i h
    simp only [setActor, noteStale] at h ⊢
    exact hS.idleOff i h
  · intro i h
    simp only [setActor, noteStale] at h ⊢
    exact hS.rostered i h
  · intro i h
    simp only [setActor, noteStale] at h ⊢
    exact hS.offEmpty i h

theorem sem_stale (I : Impl) (w : World) (sender : InstId) (dst : String) (hS : SemInv I w) :
    SemInv I (noteStale w sender dst) := by
  apply sem_stable I w (noteStale w sender dst) hS
  · intro g _ r _
    simp [noteStale]
  · intro g _ r _
    simp [noteStale]
  · intro i
    simpa [noteStale] using hS.cont i
  · intro i
    simpa [noteStale] using hS.prog i
  · intro i
    simpa [noteStale] using hS.waited i
  · intro i h
    simp only [noteStale] at h ⊢
    exact hS.idleOff i h
  · intro i h
    simp only [noteStale] at h ⊢
    exact hS.rostered i h
  · intro i h
    simp only [noteStale] at h ⊢
    exact hS.offEmpty i h

theorem mail_stale (w : World) (sender : InstId) (dst : String) (hM : MailInv w) :
    MailInv (noteStale w sender dst) := by
  apply mail_copy w _ hM
  intro i
  simp [noteStale]

theorem resolve_tname (D : Description) (sender : InstId) (dst : String) (id : InstId)
    (h : resolveId D sender dst = some id) : tname id = dst := by
  unfold resolveId at h
  split at h
  · cases h
  · next t _ =>
    cases hm : t.multiplicity with
    | one =>
      simp [hm] at h
      cases h
      rfl
    | perPeer =>
      simp [hm] at h
      split at h
      · cases h
      · cases h
        rfl

theorem mail_note (w : World) (sender : InstId) (dst : String) (id : InstId) (a : Actor)
    (hM : MailInv (setActor w id a)) : MailInv (setActor (noteStale w sender dst) id a) := by
  apply mail_copy (setActor w id a) _ hM
  intro i
  simp [setActor, noteStale]

/-- A name `resolveId` returns is the route when that actor is still alive. -/
theorem route_of_resolve (w : World) (D : Description) (sender : InstId) (dst : String) (id : InstId)
    (h : resolveId D sender dst = some id) (hl : (w.st id).life = .alive) :
    route w D sender dst = some id := by
  unfold resolveId at h
  unfold route
  split at h
  · cases h
  · next t ht =>
    simp [ht]
    cases hm : t.multiplicity with
    | one =>
      simp [hm] at h
      cases h
      have hlive : ((w.st (InstId.core dst)).life == .alive) = true := by simpa [beq_iff_eq] using hl
      simp [hlive]
      exact hl
    | perPeer =>
      simp [hm] at h
      cases hk : memberKey sender with
      | none => simp [hk] at h
      | some k =>
        simp [hk] at h
        cases h
        have hlive : ((w.st (InstId.peer dst k)).life == .alive) = true := by
          simpa [beq_iff_eq] using hl
        simp [hlive]
        exact hl

theorem route_tname (w : World) (D : Description) (sender : InstId) (dst : String) (id : InstId)
    (h : route w D sender dst = some id) : tname id = dst := by
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
      cases hk : memberKey sender with
      | none => simp [hk] at h
      | some k =>
        simp [hk] at h
        by_cases hl : (w.st (InstId.peer dst k)).life = .alive
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
    · exact idleOff_busy I w hS id _ rfl (by simp [hphase])
    · exact Or.inl rfl
  · subst he
    simp [execRun]
    apply sem_set I w id { (w.st id) with phase := .awaitPeer (afterHead { k with rest := .peer :: es }) } hS
    · rfl
    · rfl
    · simp [contTy, afterHead, hty]
    · simp [programOk, afterHead, htail]
    · simp [waitEdge]
    · exact idleOff_busy I w hS id _ rfl (by simp [hphase])
    · exact Or.inl rfl
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    have hhead := head_send _ _ _ d l n es hprog
    cases hr : route w I.desc id d with
    | none =>
      simp [execRun, hr]
      have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .send d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      exact sem_note I w id d id _ (sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        (idleOff_busy I w hS id _ hp.2.1 (by simp [hphase])) (Or.inl (proceed_parked _ _)))
    | some dstId =>
      simp [execRun, hr]
      apply enqueue_sem I w id dstId { label := l, sender := id, callFrom := none } false
        (afterHead { k with rest := .send d l n :: es }) hS
      · simp [afterHead, hty]
      · simpa [afterHead] using htail
      · refine ⟨l, ?_⟩
        simpa [route_tname w I.desc id d dstId hr] using hhead.1
      · exact alive_if_busy I w hS id (by simp [hphase])
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    have hhead := head_call _ _ _ d l n es hprog
    cases hr : resolveId I.desc id d with
    | none =>
      simp [execRun, hr]
      have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .call d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      exact sem_note I w id d id _ (sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        (idleOff_busy I w hS id _ hp.2.1 (by simp [hphase])) (Or.inl (proceed_parked _ _)))
    | some dstId =>
      simp [execRun, hr]
      have hedge : ∃ label, hasEdge I.desc (tname id) (w.st id).typestate (tname dstId) .call .blocking label = true := by
        refine ⟨l, ?_⟩
        simpa [resolve_tname I.desc id d dstId hr] using hhead.1
      apply enqueue_sem I w id dstId { label := l, sender := id, callFrom := some id } true
        (afterHead { k with rest := .call d l n :: es }) hS
      · simp [afterHead, hty]
      · simpa [afterHead] using htail
      · exact hedge
      · exact alive_if_busy I w hS id (by simp [hphase])

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
    exact mail_set_free w id _ hM hfree (by simp [notParked]) rfl rfl
  · subst he
    simp [execRun]
    exact mail_set_free w id _ hM hfree (by simp [notParked]) rfl rfl
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    cases hr : route w I.desc id d with
    | none =>
      simp [execRun, hr]
      exact mail_note w id d id _ (mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
        (proceed_keeps_life _ _))
    | some dstId =>
      simp [execRun, hr]
      exact enqueue_mail w I.desc id dstId { label := l, sender := id, callFrom := none } false
        (afterHead { k with rest := .send d l n :: es }) hM hfree
  · obtain ⟨d, l, n, he⟩ := he
    subst he
    cases hr : resolveId I.desc id d with
    | none =>
      simp [execRun, hr]
      exact mail_note w id d id _ (mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
        (proceed_keeps_life _ _))
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
  · exact idleOff_now _ rfl
  · exact Or.inl rfl

theorem exec_done_inv (I : Impl) (w : World) (id : InstId) (k : Cont) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := [] }) :
    SemInv I (execRun I w id (w.st id) { k with rest := [] }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := [] }) := by
  refine ⟨exec_done_sem I w id k hS hphase, ?_⟩
  simp [execRun]
  exact mail_set_free w id _ hM (by simp [notParked, hphase]) (by simp [notParked]) rfl rfl

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
  cases hr : route w I.desc id d with
  | none =>
    simp [hr]
    have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .trySend d l n :: es })
      (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
    refine ⟨sem_note I w id d id _ (sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_busy I w hS id _ hp.2.1 (by simp [hphase])) (Or.inl (proceed_parked _ _))), ?_⟩
    exact mail_note w id d id _ (mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _)
      (proceed_keeps_life _ _))
  | some dstId =>
    simp [hr]
    split
    · rename_i hroom
      let msg : Msg := { label := l, sender := id, callFrom := none, reliable := false }
      let k' := afterHead { k with rest := .trySend d l n :: es }
      refine ⟨try_room_sem I w id dstId msg k' hS (by simp [k', afterHead, hty])
          (by simpa [k', afterHead] using htail) hroom.1.1 hroom.1.2 hroom.2
          (alive_if_busy I w hS id (by simp [hphase])),
        enqueue_mail w I.desc id dstId msg false k' hM hfree⟩
    · have hp := proceed_ok I.desc id (w.st id) (afterHead { k with rest := .trySend d l n :: es })
        (by simp [afterHead, hty]) (by simpa [afterHead] using htail)
      refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        (idleOff_busy I w hS id _ hp.2.1 (by simp [hphase])) (Or.inl (proceed_parked _ _)), ?_⟩
      exact mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _) (proceed_keeps_life _ _)

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
    refine ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_busy I w hS id _ hp.2.1 (by simp [hphase])) (Or.inl (proceed_parked _ _)),
      mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _) (proceed_keeps_life _ _)⟩
  · split
    · let bumped : Actor :=
        { (w.st id) with
          prio := upsertPrio (w.st id).prio
            { label := label, sender := id, callFrom := none, reliable := true,
              mid := (w.st id).nextMid },
          nextMid := (w.st id).nextMid + 1 }
      have hp := proceed_ok I.desc id bumped (afterHead { k with rest := .selfSchedule label :: es })
        (by simp [bumped, afterHead, hty]) (by simpa [bumped, afterHead] using htail)
      refine ⟨sem_set I w id (proceed bumped _) hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
        (idleOff_alive hp.2.1 (alive_if_busy I w hS id (by simp [hphase])))
        (Or.inl (proceed_parked bumped _)),
        mail_set_free w id (proceed bumped _) hM hfree (proceed_not_parked _ _)
          (by simp [proceed_parked, bumped]) ((proceed_keeps_life _ _).trans (by simp [bumped]))⟩
    · refine ⟨sem_set I w id { (w.st id) with phase := .crashed } hS rfl rfl
        (by simp [contTy]) (by simp [programOk]) (by simp [waitEdge])
        (idleOff_busy I w hS id _ rfl (by simp [hphase])) (Or.inl rfl),
        mail_set_free w id { (w.st id) with phase := .crashed } hM hfree (by simp [notParked]) rfl rfl⟩

theorem proceed_sender (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff)
    (replyTo : Option InstId) (hS : SemInv I w) (hM : MailInv w)
    (hty : (w.st id).typestate = k.toState)
    (htail : effectsOk I.desc (tname id) (w.st id).typestate es = true)
    (hfree : notParked (w.st id).phase) (hbusy : (w.st id).phase ≠ .idle) :
    let k' : Cont := { rest := es, toState := k.toState, replyTo := replyTo }
    SemInv I (setActor w id (proceed (w.st id) k')) ∧ MailInv (setActor w id (proceed (w.st id) k')) := by
  intro k'
  have hp := proceed_ok I.desc id (w.st id) k' (by simp [k', hty]) (by simpa [k'] using htail)
  exact ⟨sem_set I w id _ hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_busy I w hS id _ hp.2.1 hbusy) (Or.inl (proceed_parked _ _)),
    mail_set_free w id _ hM hfree (proceed_not_parked _ _) (proceed_parked _ _) (proceed_keeps_life _ _)⟩

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
    simpa [hto] using proceed_sender I w id k es none hS hM hty htail hfree (by simp [hphase])
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = id
      · by_cases hc : caller = id
        · rw [hc, hphase] at hph
          cases hph
        · simp [hto, hph, hd]
          by_cases hm : (w.st id).oweId = some (w.st caller).waitId
          · simp [hm]
            have htyC : (w.st caller).typestate = ck.toState := by simpa [contTy, hph] using hS.cont caller
            have hprogC : effectsOk I.desc (tname caller) (w.st caller).typestate ck.rest = true := by
              simpa [programOk, hph] using hS.prog caller
            have hpC := proceed_ok I.desc caller (w.st caller) ck htyC hprogC
            have hfreeC : notParked (w.st caller).phase := by simp [notParked, hph]
            let resumed := finishCall (w.st caller) ck .reply
            have hS1 := sem_set I w caller resumed hS
              (by simp [resumed, finishCall]; exact hpC.1)
              (by simp [resumed, finishCall]; exact hpC.2.1)
              (by simp [resumed, finishCall]; exact hpC.2.2.1)
              (by simp [resumed, finishCall]; exact hpC.2.2.2.1)
              (by simp [resumed, finishCall]; exact hpC.2.2.2.2)
              (idleOff_busy I w hS caller _ (by simp [resumed, finishCall]; exact hpC.2.1) (by simp [hph]))
              (Or.inl (by simp [resumed, finishCall, proceed_parked]))
            have hM1 := mail_set_free w caller resumed hM hfreeC
              (by simp [resumed, finishCall]; exact proceed_not_parked _ _)
              (by simp [resumed, finishCall, proceed_parked])
              (by simp [resumed, finishCall]; exact proceed_keeps_life _ _)
            have hother : (setActor w caller resumed).st id = w.st id :=
              setActor_other _ _ _ _ (Ne.symm hc)
            have both := proceed_sender I (setActor w caller resumed) id k es (some caller)
              hS1 hM1 (by simpa [hother] using hty) (by simpa [hother] using htail)
              (by simpa [hother] using hfree) (by simpa [hother, hphase])
            simpa [resumed, hother] using both
          · simp [hm]
            exact proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
      · simpa [hto, hph, hd] using
          proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | idle =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | run _ =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | parked _ _ _ =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | awaitEffect _ =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | awaitPeer _ =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])
    | crashed =>
      simpa [hto, hph] using
        proceed_sender I w id k es (some caller) hS hM hty htail hfree (by simp [hphase])

theorem tryWake_inv (I : Impl) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (hS : SemInv I w) (hM : MailInv w) :
    SemInv I (tryWake I.desc w dstId label writer) ∧ MailInv (tryWake I.desc w dstId label writer) := by
  unfold tryWake
  extract_lets
  split
  · refine ⟨?_, ?_⟩
    · apply sem_set
      · exact hS
      · rfl
      · rfl
      · simpa [contTy] using hS.cont dstId
      · simpa [programOk] using hS.prog dstId
      · simpa [waitEdge] using hS.waited dstId
      · exact idleOff_same I w hS dstId _ rfl rfl
      · exact Or.inl rfl
    · apply mail_set_same
      · exact hM
      · rfl
      · rfl
      · rfl
  · exact ⟨hS, hM⟩

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
    · intro i h
      rw [hst] at h ⊢
      exact hS.idleOff i h
    · intro i h
      rw [hst] at h
      exact hS.rostered i h
    · intro i hmiss
      rw [hst]
      exact hS.offEmpty i hmiss
  have hMcell : MailInv w1 := mail_copy w w1 hM hst
  let stepped := proceed (w1.st id) { rest := es, toState := k.toState, replyTo := k.replyTo }
  have hp := proceed_ok I.desc id (w1.st id) { rest := es, toState := k.toState, replyTo := k.replyTo }
    (by simpa [hst, hty]) (by rw [hst]; simpa [hty] using htail)
  have hS1 := sem_set I w1 id stepped hScell hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    (idleOff_busy I w1 hScell id _ hp.2.1 (by simpa [hst, hphase])) (Or.inl (proceed_parked _ _))
  have hM1 := mail_set_free w1 id stepped hMcell (by simpa [hst] using hfree)
    (proceed_not_parked _ _) (proceed_parked _ _) (proceed_keeps_life _ _)
  split
  · exact ⟨hS1, hM1⟩
  · have hw := wakes_inv I _ (readersOf (setActor w1 id stepped) dst) label id hS1 hM1
    simp [wakeReaders, w1]
    exact hw

theorem credit_mail (I : Impl) (w : World) (tmpl : String) (sender : InstId) (hM : MailInv w) :
    MailInv (creditSender w tmpl sender) := by
  unfold creditSender
  exact mail_set_same w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) hM
    (by simp [bumpToken]) (by simp [bumpToken]) (by simp [bumpToken])

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
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 (idleOff_resume I w hS p.sender false id)
        (Or.inl hr.2.2.2.2.2.2))

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

theorem release_life (id : InstId) (ps : List Parked) (w : World) (i : InstId) :
    ((releaseFold id ps w).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      exact ih _
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      simp only [hf, ite_false]
      change ((releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st i).life =
        (w.st i).life
      rw [ih (setActor w p.sender (resumeSender (w.st p.sender) false id))]
      by_cases hi : i = p.sender
      · rw [hi, setActor_self]
        exact resume_keeps_life _ _ _
      · rw [setActor_other w p.sender i (resumeSender (w.st p.sender) false id) hi]

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
      (t.terminable && (t.subtree != "" || !hasParkedCall (w.st id).parked)) = false) :
    SemInv I (execRun I w id (w.st id) { k with rest := .terminate :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .terminate :: es }) := by
  cases ht : templateOf I.desc (tname id) with
  | none =>
    simp [execRun, ht]
    exact ⟨hS, hM⟩
  | some t =>
    simp only [execRun, ht, hno t ht]
    exact ⟨hS, hM⟩

/-- Killing terminate refunds the mailbox, installs the dead actor, and resumes
every parked sender together. The queue is empty only after those resumes. -/
theorem exec_term_die_sem (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (t : Template)
    (k : Cont) (es : List Eff) (hS : SemInv I w) (hM : MailInv w)
    (hphase : (w.st id).phase = .run { k with rest := .terminate :: es })
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hnocall : hasParkedCall (w.st id).parked = false) (hsub : t.subtree = "")
    (hchild : hasChild I.desc w id = false) :
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
    have hsubB : (t.subtree == "") = true := by simpa [beq_iff_eq] using hsub
    have hgo : (t.terminable && (t.subtree != "" || !hasParkedCall (w.st id).parked)) = true := by
      simp [hterm, hnocall]
    have hno : (!(hasChild I.desc w id)) = true := by simp [hchild]
    simp only [execRun, ht, hgo, hsubB, hno]
    unfold releaseWorld
    simp [wF, wD, dead, wP, wM, wR, ps]
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
    · intro i hdead
      by_cases h : i = id
      · subst h
        simp [wD, setActor_self, dead]
      · rw [setActor_other wP id i dead h] at hdead ⊢
        exact hRP.1.idleOff i hdead
    · intro i hlive
      by_cases h : i = id
      · simp [h, wD, setActor_self, dead] at hlive
      · rw [setActor_other wP id i dead h] at hlive
        exact hRP.1.rostered i hlive
    · intro i hmiss
      by_cases h : i = id
      · simp [h, wD, setActor_self, dead]
      · simp only [wD, setActor] at hmiss
        rw [setActor_other wP id i dead h]
        exact hRP.1.offEmpty i hmiss
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
      (fun p => by rw [hparkP]) (by rw [hstId]) (by rw [hstId]) hpk hresume
      (fun i hi hs => Or.inl (hother i hi hs))
      (fun i hdead0 => by
        by_cases hi : i = id
        · have hfix := release_id_fixed id ps wD hself
          rw [← release_fold_eq] at hfix
          have hst : wF.st id = dead := by simpa [wF, wD, setActor_self] using hfix
          rw [hi]
          simpa [dead] using congrArg (·.life) hst
        · have hl := release_life id ps wD i
          rw [← release_fold_eq] at hl
          have heq : (wF.st i).life = (wP.st i).life := by
            simpa [wF, wD, setActor_other wP id i dead hi] using hl
          rw [heq]
          exact hdead0)
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
        · exact idleOff_now _ rfl
        · exact Or.inr ((cells_sem I w id hS).rostered id
            (by rw [readCells_st]; exact hlife.symm.trans halive))
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
          · intro hbad
            cases hp : tr.program <;> simp [hp] at hbad
          · exact Or.inr ((cells_sem I w (.core r) hS).rostered (.core r)
              (by rw [readCells_st]; exact hlife.symm.trans halive))
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
          · intro i hdead
            by_cases hi : i = .peer name ix
            · rw [hi, setActor_self] at hdead
              cases hp : tr.program <;> simp [hp] at hdead
            · rw [setActor_other _ _ i _ hi] at hdead ⊢
              exact (cells_sem I w (.peer name ix) hS).idleOff i hdead
          · intro i hlive
            by_cases hi : i = .peer name ix
            · rw [hi]
              exact (cells_sem I w (.peer name ix) hS).rostered (.peer name ix)
                (by rw [readCells_st]; exact hlife.symm.trans halive)
            · rw [setActor_other _ _ i _ hi] at hlive
              exact (cells_sem I w (.peer name ix) hS).rostered i hlive
          · intro i hmiss
            by_cases hi : i = .peer name ix
            · rw [hi] at hmiss
              simp only [setActor] at hmiss
              exact False.elim (hmiss ((cells_sem I w (.peer name ix) hS).rostered (.peer name ix)
                (by rw [readCells_st]; exact hlife.symm.trans halive)))
            · simp only [setActor] at hmiss
              rw [setActor_other _ _ i _ hi]
              exact (cells_sem I w (.peer name ix) hS).offEmpty i hmiss
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
    (by rw [hd.parked, hd.st, hpark]) (by rw [hd.st]; exact hd.life.trans hlife)

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
        let a0 : Actor := { (w.st id) with life := .alive, phase := .idle, prio := ms }
        have hdI := deliver_inv I hL w id a0 m w1 a1 hS halive.symm rfl rfl rfl hd
        have hMail := deliver_mail I hL w id a0 m w1 a1 hS hM halive.symm rfl rfl rfl hphase rfl hd
        exact ⟨hdI.sem, hMail⟩

theorem resume_one (I : Impl) (w w1 : World) (id : InstId) (cur : Actor) (p : Parked) (ps : List Parked)
    (who : InstId) (hS : SemInv I (setActor w1 id cur)) (hM : MailInv w) (hst : ∀ i, w1.st i = w.st i)
    (hidle : (w.st id).phase = .idle) (hqueue : (w.st id).parked = p :: ps) (hcurPk : cur.parked = ps)
    (hcurPh : notParked cur.phase) (hcurLife : cur.life = (w.st id).life) :
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
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 (idleOff_resume I credited hS1 p.sender false id)
        (Or.inl hr.2.2.2.2.2.2), ?_, ?_⟩
      · rw [setActor_self]; exact hr.2.2.2.2.2.1
      · rw [setActor_self, hr.2.2.2.2.2.2, hpkS]
    | true =>
      have hr := resume_call_ok I.desc p.sender (credited.st p.sender) id k hcont hprog hwait (by rw [hph, hc])
      refine ⟨sem_set I credited p.sender (resumeSender (credited.st p.sender) true id) hS1 hr.1 hr.2.1
        hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 (idleOff_resume I credited hS1 p.sender true id)
        (Or.inl hr.2.2.2.2.2.2), ?_, ?_⟩
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
  exact ⟨hstep.1, mail_drop w wOut id p ps hM hfree hqueue hidPh hidPk hpkO hstep.2.1 hother
    (fun i hgone => by
      by_cases hs : i = p.sender
      · subst hs
        rw [setActor_self, resume_keeps_life, hlifeS]
        exact hgone
      · rw [setActor_other _ p.sender i _ hs, (credit_phase_life base (tname id) who i).2]
        by_cases hi : i = id
        · subst hi
          rw [setActor_self, hcurLife]
          exact hgone
        · rw [setActor_other w1 id i cur hi, hst]
          exact hgone)⟩

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
        let a0 : Actor := { (w.st id) with life := .alive, phase := .idle, box := [], parked := ps }
        have hdI := deliver_inv I hL w id a0 p.msg w1 a1 hS halive.symm rfl rfl rfl hd
        simpa using resume_one I w w1 id a1 p ps p.msg.sender hdI.sem hM hdI.st hphase hpk hdI.parked
          hdI.free (hdI.life.trans halive.symm)
  | cons m ms =>
    cases hpk : (w.st id).parked with
    | nil =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := { (w.st id) with life := .alive, phase := .idle, box := ms, parked := [] }
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
        let a0 : Actor :=
          { (w.st id) with life := .alive, phase := .idle, box := ms, parked := p :: ps }
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
          (idleOff_life (by
            simp [admitted, setActor_self]
            exact hdI.life.trans (by simp [a0])))
          (Or.inr (hdI.sem.rostered id (by
            rw [setActor_self]
            exact hdI.life.trans (by simp [a0]))))
        have hsame : setActor (setActor w1 id a1) id admitted = setActor w1 id admitted := by
          simp [setActor]
          funext i
          by_cases hi : i = id <;> simp [hi]
        rw [hsame] at hAd
        have hfree : notParked admitted.phase := hdI.free
        simpa using resume_one I w w1 id admitted p ps m.sender hAd hM hdI.st hphase hpk rfl hfree
          (by simp [admitted]; exact hdI.life.trans halive.symm)

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
    (hfree : slotFree w template)
    (hlot : (w.st (InstId.peer template (w.nextIx template))).life ≠ .dead)
    (h : spawn I w template = some w') : MailInv w' := by
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
      have hquiet : ∀ s c k, ((growRoster w pid template).st s).phase = .parked pid c k → False := by
        intro s c k hph
        rcases hM.bwd s pid c k (by simpa [hst] using hph) with ⟨p, hp, _, _⟩ | ⟨_, hdead⟩
        · rw [hfree.2] at hp
          cases hp
        · exact hlot hdead
      have hM1 := mail_awake _ pid (bornPeer I template t.initial) hMg
        (by simp [bornPeer, withTokens, hst]; exact hfree.1.symm)
        (by simp [bornPeer, withTokens, hst]; exact hfree.2)
        hquiet
      exact mail_copy _ _ hM1 fun i => readCells_st I.desc _ pid i
    · simp [hif] at h

theorem spawn_inv (I : Impl) (w : World) (template : String) (w' : World) (hS : SemInv I w)
    (hM : MailInv w) (hfree : slotFree w template)
    (hlot : (w.st (InstId.peer template (w.nextIx template))).life ≠ .dead)
    (h : spawn I w template = some w') :
    SemInv I w' ∧ MailInv w' :=
  ⟨spawn_sem I w w' template hS h, spawn_mail I w template w' hM hfree hlot h⟩

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
    exact proceed_sender I w id k k.rest k.replyTo hS hM hty hprog hfree (by simp [hph])
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
      simpa [programOk, hph] using hS.prog id
    have hfree : notParked (w.st id).phase := by simp [notParked, hph]
    exact proceed_sender I w id k k.rest k.replyTo hS hM hty hprog hfree (by simp [hph])
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

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
    by_cases hcall : isCall = true
    · simp [hcall]
      cases hlife : (w.st dst).life with
      | dead =>
        simp [hlife]
        exact open_busy w sender _ hO hs
      | alive => exact absurd hlife halive
      | absent =>
        simp [hlife]
        exact open_busy w sender _ hO hs
    · simp [hcall]
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
    rcases hM.bwd id mb c k hk with ⟨p, hp, hs, hc⟩ | ⟨hc, hdead⟩
    · exact Or.inl ⟨p, by simpa [(ingress_parked I w w' dst label mb h).1] using hp, hs, hc⟩
    · exact Or.inr ⟨hc, by rw [(ingress_parked I w w' dst label mb h).2.2]; exact hdead⟩
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

/-- Failing one waiter keeps the semantic invariant. A waiter who is not alive is
left alone; a live waiter parked on the member runs its continuation, and a live
call returns to idle. -/
theorem failWaiter_sem (I : Impl) (w : World) (dead i : InstId) (hS : SemInv I w) :
    SemInv I (failWaiter w dead i) := by
  unfold failWaiter
  split
  · exact hS
  · next hlive =>
    have halive : (w.st i).life = .alive := by
      cases hlife : (w.st i).life with
      | alive => rfl
      | absent => simp [hlife, bne] at hlive
      | dead => simp [hlife, bne] at hlive
    cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hph, hd]
          have hty : (w.st i).typestate = k.toState := by simpa [contTy, hph] using hS.cont i
          have hprog : effectsOk I.desc (tname i) (w.st i).typestate k.rest = true := by
            simpa [programOk, hph] using hS.prog i
          have hp := proceed_ok I.desc i (w.st i) k hty hprog
          apply sem_set I w i (proceed (w.st i) k) hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
          · exact idleOff_alive hp.2.1 halive
          · exact Or.inr (hS.rostered i halive)
        · simp [hph, hd]
          exact hS
      | true =>
        simp [hph]
        exact hS
    | awaitReply _ _ => simp [hph]; exact hS
    | idle => simp [hph]; exact hS
    | run _ => simp [hph]; exact hS
    | awaitEffect _ => simp [hph]; exact hS
    | awaitPeer _ => simp [hph]; exact hS
    | crashed => simp [hph]; exact hS

theorem failFold_sem (I : Impl) (w : World) (dead : InstId) (ids : List InstId) (hS : SemInv I w) :
    SemInv I (ids.foldl (fun w i => failWaiter w dead i) w) := by
  induction ids generalizing w with
  | nil => simpa using hS
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (failWaiter_sem I w dead i hS)

theorem open_failWaiter (I : Impl) (w : World) (dead i : InstId) (hO : OpenSlots w) :
    OpenSlots (failWaiter w dead i) := by
  unfold failWaiter
  split
  · exact hO
  · next hlive =>
    have halive : (w.st i).life = .alive := by
      cases hlife : (w.st i).life with
      | alive => rfl
      | absent => simp [hlife, bne] at hlive
      | dead => simp [hlife, bne] at hlive
    cases hph : (w.st i).phase with
    | parked d b _ =>
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hph, hd]
          exact open_alive w i _ hO halive
        · simp [hph, hd]
          exact hO
      | true =>
        simp [hph]
        exact hO
    | awaitReply _ _ => simp [hph]; exact hO
    | idle => simp [hph]; exact hO
    | run _ => simp [hph]; exact hO
    | awaitEffect _ => simp [hph]; exact hO
    | awaitPeer _ => simp [hph]; exact hO
    | crashed => simp [hph]; exact hO

theorem open_failFold (I : Impl) (w : World) (dead : InstId) (ids : List InstId)
    (hO : OpenSlots w) :
    OpenSlots (ids.foldl (fun w i => failWaiter w dead i) w) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (open_failWaiter I w dead i hO)

/-- Dropping the dead sender from one parked list keeps the semantic invariant. -/
theorem forgetAt_sem (I : Impl) (w : World) (dead id : InstId) (hS : SemInv I w)
    (hmem : id ∈ w.roster) :
    SemInv I (let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) := by
  simp only
  split
  · exact hS
  · apply sem_set I w id _ hS
    · rfl
    · rfl
    · simpa [contTy] using hS.cont id
    · simpa [programOk] using hS.prog id
    · simpa [waitEdge] using hS.waited id
    · exact idleOff_same I w hS id _ rfl rfl
    · exact Or.inr hmem

theorem open_forgetAt (w : World) (dead id : InstId) (hO : OpenSlots w) :
    OpenSlots (let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) := by
  simp only
  split
  · exact hO
  · next hdiff =>
    refine open_set w id _ hO ?_
    intro template ix hi hid
    have hempty := (hO template ix hi).2.2
    have hsame : ((w.st id).parked.filter fun p => p.sender != dead) == (w.st id).parked := by
      simp [hid, hempty]
    exact False.elim (hdiff hsame)

theorem forgetFold_sem (I : Impl) (w : World) (dead : InstId) (ids : List InstId) (hS : SemInv I w)
    (hids : ∀ i ∈ ids, i ∈ w.roster) :
    SemInv I (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w) := by
  induction ids generalizing w with
  | nil => simpa using hS
  | cons id ids ih =>
    simp only [List.foldl_cons]
    have hstep := forgetAt_sem I w dead id hS (hids id (List.Mem.head _))
    have hmem : ∀ i ∈ ids, i ∈ (let a := w.st id
        let ps := a.parked.filter fun p => p.sender != dead
        if ps == a.parked then w else setActor w id { a with parked := ps }).roster := by
      intro i hi
      have hrost : (let a := w.st id
          let ps := a.parked.filter fun p => p.sender != dead
          if ps == a.parked then w else setActor w id { a with parked := ps }).roster = w.roster := by
        simp only
        split <;> simp [setActor]
      rw [hrost]
      exact hids i (List.Mem.tail _ hi)
    exact ih _ hstep hmem

theorem open_forgetFold (w : World) (dead : InstId) (ids : List InstId) (hO : OpenSlots w) :
    OpenSlots (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons id ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (open_forgetAt w dead id hO)

theorem member_not_core (D : Description) (id : InstId) (sub : String) (key : Nat) (r : String)
    (h : isMember D id sub key = true) : id ≠ .core r := by
  intro heq
  cases id with
  | core _ => simp [isMember] at h
  | peer _ _ => cases heq

/-- The last write of a kill: the member is dead, idle, and its mailbox is empty.
Cores are untouched because a member is a peer. -/
theorem kill_dead_sem (I : Impl) (w : World) (id : InstId) (hS : SemInv I w)
    (hpeer : ∀ r, id ≠ .core r) :
    SemInv I (setActor w id
      { (w.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }) := by
  apply sem_stable I w _ hS
  · intro _ _ r _
    exact congrArg (·.typestate) (setActor_other w id (.core r) _ (Ne.symm (hpeer r)))
  · intro _ _ r _
    exact congrArg (·.life) (setActor_other w id (.core r) _ (Ne.symm (hpeer r)))
  · intro i
    by_cases h : i = id
    · simp [h, setActor, contTy]
    · rw [setActor_other w id i _ h]; exact hS.cont i
  · intro i
    by_cases h : i = id
    · simp [h, setActor, programOk]
    · rw [setActor_other w id i _ h]; exact hS.prog i
  · intro i
    by_cases h : i = id
    · simp [h, setActor, waitEdge]
    · rw [setActor_other w id i _ h]; exact hS.waited i
  · intro i hdead
    by_cases h : i = id
    · simp [h, setActor]
    · rw [setActor_other w id i _ h] at hdead ⊢
      exact hS.idleOff i hdead
  · intro i hlive
    by_cases h : i = id
    · simp [h, setActor] at hlive
    · simp [setActor, h] at hlive ⊢
      exact hS.rostered i hlive
  · intro i hmiss
    by_cases h : i = id
    · simp [h, setActor]
    · simp [setActor] at hmiss
      rw [setActor_other w id i _ h]
      exact hS.offEmpty i hmiss

theorem open_kill_dead (w : World) (id : InstId) (hO : OpenSlots w)
    (halive : (w.st id).life = .alive) :
    OpenSlots (setActor w id
      { (w.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }) :=
  open_alive w id _ hO halive

/-- Phase and typestate determine the continuation, the program check, and the wait edge. -/
theorem contTy_stable {a b : Actor} (hp : a.phase = b.phase) (ht : a.typestate = b.typestate)
    (h : contTy b) : contTy a := by
  unfold contTy at h ⊢
  rw [hp]
  cases hb : b.phase <;> simp [hb] at h ⊢ <;> rw [ht] <;> exact h

theorem programOk_stable (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate)
    (h : programOk D id b) : programOk D id a := by
  unfold programOk at h ⊢
  rw [hp]
  cases hb : b.phase <;> simp [hb] at h ⊢ <;> rw [ht] <;> exact h

theorem waitEdge_stable (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate)
    (h : waitEdge D id b) : waitEdge D id a := by
  unfold waitEdge at h ⊢
  rw [hp]
  cases hb : b.phase <;> simp [hb] at h ⊢ <;> rw [ht] <;> exact h

/-- Returning outbound slots does not move a phase, a life, or a core. -/
theorem forgetHost_sem (I : Impl) (w : World) (dead host : InstId) (hS : SemInv I w) :
    SemInv I (forgetHost w dead host) := by
  apply sem_stable I w _ hS
  · intro _ _ r _
    exact (forgetHost_stable w dead host (.core r)).2.2.1
  · intro _ _ r _
    exact (forgetHost_stable w dead host (.core r)).2.1
  · intro i
    exact contTy_stable (forgetHost_stable w dead host i).1 (forgetHost_stable w dead host i).2.2.1
      (hS.cont i)
  · intro i
    exact programOk_stable I.desc i (forgetHost_stable w dead host i).1
      (forgetHost_stable w dead host i).2.2.1 (hS.prog i)
  · intro i
    exact waitEdge_stable I.desc i (forgetHost_stable w dead host i).1
      (forgetHost_stable w dead host i).2.2.1 (hS.waited i)
  · intro i hdead
    have hp := (forgetHost_stable w dead host i).1
    have hl := (forgetHost_stable w dead host i).2.1
    rw [hp]
    exact hS.idleOff i (hl.symm ▸ hdead)
  · intro i hlive
    have hl := (forgetHost_stable w dead host i).2.1
    rw [forgetHost_roster]
    exact hS.rostered i (hl.symm.trans hlive)
  · intro i hmiss
    rw [forgetHost_roster] at hmiss
    have hempty := hS.offEmpty i hmiss
    rw [forgetHost_park]
    split
    · rw [hempty]; simp
    · exact hempty

theorem forgetSender_sem (I : Impl) (w : World) (dead : InstId) (hS : SemInv I w) :
    SemInv I (forgetSender w dead) := by
  have hfold : ∀ (ids : List InstId) (w' : World), SemInv I w' →
      SemInv I (ids.foldl (fun w host => forgetHost w dead host) w') := by
    intro ids
    induction ids with
    | nil => intro w' hS'; simpa using hS'
    | cons host ids ih =>
      intro w' hS'
      simp only [List.foldl_cons]
      exact ih _ (forgetHost_sem I w' dead host hS')
  simpa [forgetSender] using hfold w.roster w hS

theorem open_forgetHost (w : World) (dead host : InstId) (hO : OpenSlots w) :
    OpenSlots (forgetHost w dead host) := by
  intro template i hi
  rw [forgetHost_nextIx] at hi
  have h0 := hO template i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [(forgetHost_stable w dead host (.peer template i)).2.1]
    exact h0.1
  · rw [(forgetHost_stable w dead host (.peer template i)).1]
    exact h0.2.1
  · rw [forgetHost_park]
    split
    · rw [h0.2.2]; simp
    · exact h0.2.2

theorem open_forgetSender (w : World) (dead : InstId) (hO : OpenSlots w) :
    OpenSlots (forgetSender w dead) := by
  have hfold : ∀ (ids : List InstId) (w' : World), OpenSlots w' →
      OpenSlots (ids.foldl (fun w host => forgetHost w dead host) w') := by
    intro ids
    induction ids with
    | nil => intro w' hO'; simpa using hO'
    | cons host ids ih =>
      intro w' hO'
      simp only [List.foldl_cons]
      exact ih _ (open_forgetHost w' dead host hO')
  simpa [forgetSender] using hfold w.roster w hO

/-- A failure does not invent a parked phase. -/
theorem failWaiter_park_src (w : World) (dead i s dst : InstId) (c : Bool) (k : Cont)
    (h : ((failWaiter w dead i).st s).phase = .parked dst c k) :
    (w.st s).phase = .parked dst c k := by
  by_cases hs : s = i
  · subst hs
    unfold failWaiter at h
    split at h
    · exact h
    · cases hph : (w.st s).phase with
      | parked d b ck =>
        cases b with
        | false =>
          by_cases hd : d = dead
          · simp [hph, hd] at h
            cases hk : ck.rest <;> simp [setActor, proceed, hk] at h
          · simp [hph, hd] at h
            simp [hph, h]
        | true =>
          simp [hph] at h
          simp [hph, h]
      | awaitReply _ _ =>
        simp [hph] at h
      | idle => simp [hph] at h
      | run _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
  · rw [failWaiter_other w dead i s hs] at h
    exact h

theorem failFold_park_src (w : World) (dead s dst : InstId) (c : Bool) (k : Cont)
    (ids : List InstId)
    (h : ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .parked dst c k) :
    (w.st s).phase = .parked dst c k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons] at h
    exact failWaiter_park_src w dead i s dst c k (ih (failWaiter w dead i) h)

/-- `s` is parked, so it is alive. -/
theorem alive_of_parked (I : Impl) (w : World) (hS : SemInv I w) (s dst : InstId) (c : Bool)
    (k : Cont) (hph : (w.st s).phase = .parked dst c k) : (w.st s).life = .alive := by
  cases hlife : (w.st s).life with
  | alive => rfl
  | absent =>
    exact False.elim ((by
      have hidle := hS.idleOff s (by rw [hlife]; intro h; cases h)
      simp [hidle] at hph) )
  | dead =>
    exact False.elim ((by
      have hidle := hS.idleOff s (by rw [hlife]; intro h; cases h)
      simp [hidle] at hph) )

/-- After waiters are failed and the dead sender is forgotten, clearing the member
restores the mailbox invariant. -/
theorem kill_clear_mail (I : Impl) (w : World) (id : InstId) (hS : SemInv I w) (hM : MailInv w) :
    let failed := failWaiters w id
    let forgotten := forgetSender failed id
    let cleared := setActor forgotten id
      { (forgotten.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
    MailInv cleared := by
  intro failed forgotten cleared
  have hSfail : SemInv I failed := by
    simpa [failed, failWaiters] using failFold_sem I w id w.roster hS
  have hparkF : ∀ s, (failed.st s).parked = (w.st s).parked := by
    intro s
    simpa [failed, failWaiters] using (failFold_mail w id s w.roster).2.2
  have hrostF : failed.roster = w.roster := by
    simpa [failed, failWaiters] using failWaiters_roster w id w.roster
  have hphaseG : ∀ s, (forgotten.st s).phase = (failed.st s).phase := by
    intro s
    simpa [forgotten] using (forget_stable failed id s).1
  have hfinalPhase (s : InstId) (hs : s ≠ id) :
      (cleared.st s).phase = (failed.st s).phase := by
    rw [show cleared = setActor forgotten id _ from rfl, setActor_other _ id s _ hs, hphaseG]
  have hfinalPark (mb : InstId) (hmb : mb ≠ id) :
      (cleared.st mb).parked = (w.st mb).parked.filter fun p => p.sender != id := by
    rw [show cleared = setActor forgotten id _ from rfl, setActor_other _ id mb _ hmb]
    by_cases hin : mb ∈ failed.roster
    · have heq := forget_parked_of_mem failed id mb hin hmb
      have hfilt : (forgotten.st mb).parked =
          (failed.st mb).parked.filter fun p => p.sender != id := by
        simpa [forgotten] using heq
      rw [hfilt, hparkF]
    · have hskip := forget_off failed id mb hin hmb
      have hempty := hSfail.offEmpty mb hin
      have hemptyW : (w.st mb).parked = [] := by simpa [hparkF] using hempty
      have hst : (forgotten.st mb).parked = (failed.st mb).parked := by
        simpa [forgotten] using congrArg (·.parked) hskip
      rw [hst, hempty, hemptyW]
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hmb : mb = id
    · simp [hmb, cleared, setActor] at hp
    · rw [hfinalPark mb hmb] at hp
      have hmem := List.mem_filter.mp hp
      obtain ⟨k, hk⟩ := hM.fwd mb p hmem.1
      have hsender : p.sender ≠ id := by
        intro heq
        simp [heq, bne] at hmem
      have hphF : (failed.st p.sender).phase = (w.st p.sender).phase := by
        simpa [failed, failWaiters] using
          failFold_spares w id p.sender mb w.roster p.isCall k hmb hk
      exact ⟨k, (hfinalPhase p.sender hsender).trans (hphF.trans hk)⟩
  · intro s dst c k hk
    have hs : s ≠ id := by
      intro heq
      simp [heq, cleared, setActor] at hk
    have hphF : (failed.st s).phase = .parked dst c k := (hfinalPhase s hs).symm.trans hk
    have hliveF : (failed.st s).life = .alive :=
      alive_of_parked I failed hSfail s dst c k hphF
    have hmemS : s ∈ failed.roster := hSfail.rostered s hliveF
    have hphW : (w.st s).phase = .parked dst c k :=
      failFold_park_src w id s dst c k w.roster (by simpa [failed, failWaiters] using hphF)
    cases c with
    | false =>
      have hdst : dst ≠ id := by
        intro hdead
        have hgone := failFold_clears w id s w.roster false k (by simpa [hdead] using hphW)
          (by simpa [failed, failWaiters] using
            (failFold_life w id s w.roster).symm.trans hliveF)
          (by simpa [hrostF] using hmemS) rfl k
        exact hgone (by simpa [failed, failWaiters, hdead] using hphF)
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwdSend s dst k hphW
      have hkeep : (p.sender != id) = true := by
        have hne : p.sender ≠ id := by rw [hsender]; exact hs
        cases hbb : p.sender == id
        · simp [bne, hbb]
        · exact absurd (beq_iff_eq.mp hbb) hne
      refine Or.inl ⟨p, ?_, hsender, hc⟩
      rw [hfinalPark dst hdst]
      exact List.mem_filter.mpr ⟨hp, hkeep⟩
    | true =>
      by_cases hdst : dst = id
      · exact Or.inr ⟨rfl, by simp [cleared, setActor, hdst]⟩
      · rcases hM.bwd s dst true k hphW with ⟨p, hp, hsender, hc⟩ | ⟨hc, hdead⟩
        · have hkeep : (p.sender != id) = true := by
            have hne : p.sender ≠ id := by rw [hsender]; exact hs
            cases hbb : p.sender == id
            · simp [bne, hbb]
            · exact absurd (beq_iff_eq.mp hbb) hne
          refine Or.inl ⟨p, ?_, hsender, hc⟩
          rw [hfinalPark dst hdst]
          exact List.mem_filter.mpr ⟨hp, hkeep⟩
        · have hlifeD : (cleared.st dst).life = (w.st dst).life := by
            rw [show cleared = setActor forgotten id _ from rfl, setActor_other _ id dst _ hdst]
            exact (forget_stable failed id dst).2.1.trans
              (by simpa [failed, failWaiters] using failFold_life w id dst w.roster)
          exact Or.inr ⟨hc, by rw [hlifeD]; exact hdead⟩
  · intro mb1 mb2 p1 p2 hp1 hp2 hs
    by_cases h1 : mb1 = id
    · simp [h1, cleared, setActor] at hp1
    · by_cases h2 : mb2 = id
      · simp [h2, cleared, setActor] at hp2
      · rw [hfinalPark mb1 h1] at hp1
        rw [hfinalPark mb2 h2] at hp2
        exact hM.uniq mb1 mb2 p1 p2 (List.mem_filter.mp hp1).1 (List.mem_filter.mp hp2).1 hs
  · intro mb
    by_cases hmb : mb = id
    · simp [hmb, cleared, setActor]
    · rw [hfinalPark mb hmb]
      exact List.Sublist.nodup (filter_sublist (fun p : Parked => p.sender != id) _) (hM.once mb)

/-- One member dies: its credits return, its waiters resume, and it is left idle. -/
theorem killOne_inv (I : Impl) (w : World) (sub : String) (key : Nat) (id : InstId)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w)
    (hmem : isMember I.desc id sub key = true) (halive : (w.st id).life = .alive) :
    SemInv I (killOne w I.desc id) ∧ MailInv (killOne w I.desc id) ∧
      OpenSlots (killOne w I.desc id) := by
  rw [killOne_body]
  let D := I.desc
  let w1 := readCells D w id
  have hS1 : SemInv I w1 := cells_sem I w id hS
  have hM1 : MailInv w1 := mail_copy w w1 hM fun i => readCells_st D w id i
  have hO1 : OpenSlots w1 := open_read D w id hO
  let a0 := w.st id
  let w2 := refundMsgs w1 (tname id) a0.box
  have h2 := refund_msgs_inv I w1 (tname id) a0.box hS1 hM1
  have hO2 : OpenSlots w2 := open_msgs w1 (tname id) a0.box hO1
  let w3 := refundParked w2 (tname id) a0.parked
  have h3 := refund_park_inv I w2 (tname id) a0.parked h2.1 h2.2
  have hO3 : OpenSlots w3 := open_parks w2 (tname id) a0.parked hO2
  let w4 := failWaiters w3 id
  have hS4 : SemInv I w4 := by simpa [w4, failWaiters] using failFold_sem I w3 id w3.roster h3.1
  have hO4 : OpenSlots w4 := by
    simpa [w4, failWaiters] using open_failFold I w3 id w3.roster hO3
  let w5 := forgetSender w4 id
  have hS5 : SemInv I w5 := by
    simpa [w5] using forgetSender_sem I w4 id hS4
  have hO5 : OpenSlots w5 := by simpa [w5] using open_forgetSender w4 id hO4
  have hlife : (w5.st id).life = .alive := by
    have hG : (w5.st id).life = (w4.st id).life := by
      simpa [w5] using (forget_stable w4 id id).2.1
    have hF : (w4.st id).life = (w3.st id).life := by
      simpa [w4, failWaiters] using failFold_life w3 id id w3.roster
    have hP : (w3.st id).life = (w2.st id).life := (refundParked_rest w2 (tname id) a0.parked id).2.1
    have hR : (w2.st id).life = (w1.st id).life := (refundMsgs_rest w1 (tname id) a0.box id).2.1
    have hC : (w1.st id).life = (w.st id).life := congrArg (·.life) (readCells_st D w id id)
    exact hG.trans (hF.trans (hP.trans (hR.trans (hC.trans halive))))
  refine ⟨?_, ?_, ?_⟩
  · exact kill_dead_sem I w5 id hS5 fun r => member_not_core D id sub key r hmem
  · exact kill_clear_mail I w3 id h3.1 h3.2
  · exact open_kill_dead w5 id hO5 hlife

theorem killFold_inv (I : Impl) (w : World) (sub : String) (key : Nat) (ids : List InstId)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) :
    SemInv I (ids.foldl (fun w id =>
      if isMember I.desc id sub key && (w.st id).life == .alive then killOne w I.desc id else w) w) ∧
      MailInv (ids.foldl (fun w id =>
        if isMember I.desc id sub key && (w.st id).life == .alive then killOne w I.desc id else w) w) ∧
      OpenSlots (ids.foldl (fun w id =>
        if isMember I.desc id sub key && (w.st id).life == .alive then killOne w I.desc id else w) w) := by
  induction ids generalizing w with
  | nil => simpa using ⟨hS, hM, hO⟩
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have halive : (w.st id).life = .alive := by simpa [beq_iff_eq] using hparts.2
      have h1 := killOne_inv I w sub key id hS hM hO hparts.1 halive
      exact ih _ h1.1 h1.2.1 h1.2.2
    · exact ih _ hS hM hO

/-- A subtree kill preserves the semantic, mailbox, and open-slot invariants.
`killSubtree` is not a step. It remains as the fold those lemmas talk about. -/
theorem killSubtree_inv (I : Impl) (w : World) (sub : String) (key : Nat)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) :
    SemInv I (killSubtree w I.desc sub key) ∧ MailInv (killSubtree w I.desc sub key) ∧
      OpenSlots (killSubtree w I.desc sub key) := by
  have hK := killFold_inv I w sub key w.roster hS hM hO
  simpa [killSubtree, killMembers] using hK

/-- A phase and typestate determine `contTy`. -/
private theorem contTy_congr {a b : Actor} (hp : a.phase = b.phase) (ht : a.typestate = b.typestate)
    (h : contTy b) : contTy a := by
  cases hb : b.phase with
  | idle => simp [contTy, show a.phase = .idle from by rw [hp, hb]]
  | crashed => simp [contTy, show a.phase = .crashed from by rw [hp, hb]]
  | run k =>
    have ha : a.phase = .run k := by rw [hp, hb]
    simpa [contTy, ha, hb, ht] using h
  | parked d c k =>
    have ha : a.phase = .parked d c k := by rw [hp, hb]
    simpa [contTy, ha, hb, ht] using h
  | awaitReply d k =>
    have ha : a.phase = .awaitReply d k := by rw [hp, hb]
    simpa [contTy, ha, hb, ht] using h
  | awaitEffect k =>
    have ha : a.phase = .awaitEffect k := by rw [hp, hb]
    simpa [contTy, ha, hb, ht] using h
  | awaitPeer k =>
    have ha : a.phase = .awaitPeer k := by rw [hp, hb]
    simpa [contTy, ha, hb, ht] using h

private theorem programOk_congr (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) (h : programOk D id b) :
    programOk D id a := by
  cases hb : b.phase with
  | idle => simp [programOk, show a.phase = .idle from by rw [hp, hb]]
  | crashed => simp [programOk, show a.phase = .crashed from by rw [hp, hb]]
  | run k =>
    have ha : a.phase = .run k := by rw [hp, hb]
    simpa [programOk, ha, hb, ht] using h
  | parked d c k =>
    have ha : a.phase = .parked d c k := by rw [hp, hb]
    simpa [programOk, ha, hb, ht] using h
  | awaitReply d k =>
    have ha : a.phase = .awaitReply d k := by rw [hp, hb]
    simpa [programOk, ha, hb, ht] using h
  | awaitEffect k =>
    have ha : a.phase = .awaitEffect k := by rw [hp, hb]
    simpa [programOk, ha, hb, ht] using h
  | awaitPeer k =>
    have ha : a.phase = .awaitPeer k := by rw [hp, hb]
    simpa [programOk, ha, hb, ht] using h

private theorem waitEdge_congr (D : Description) (id : InstId) {a b : Actor}
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) (h : waitEdge D id b) :
    waitEdge D id a := by
  cases hb : b.phase with
  | idle => simp [waitEdge, show a.phase = .idle from by rw [hp, hb]]
  | crashed => simp [waitEdge, show a.phase = .crashed from by rw [hp, hb]]
  | run k => simp [waitEdge, show a.phase = .run k from by rw [hp, hb]]
  | awaitEffect k => simp [waitEdge, show a.phase = .awaitEffect k from by rw [hp, hb]]
  | awaitPeer k => simp [waitEdge, show a.phase = .awaitPeer k from by rw [hp, hb]]
  | parked d c k =>
    have ha : a.phase = .parked d c k := by rw [hp, hb]
    simpa [waitEdge, ha, hb, ht] using h
  | awaitReply d k =>
    have ha : a.phase = .awaitReply d k := by rw [hp, hb]
    simpa [waitEdge, ha, hb, ht] using h

private theorem childTerminable_spec (D : Description) (child : InstId)
    (h : childTerminable D child = true) :
    ∃ t, templateOf D (tname child) = some t ∧ t.terminable = true := by
  cases ht : templateOf D (tname child) with
  | none => simp [childTerminable, ht] at h
  | some t =>
    refine ⟨t, rfl, ?_⟩
    simpa [childTerminable, ht] using h

private theorem not_open_occupied (w : World) (hO : OpenSlots w) (id : InstId)
    (template : String) (i : Nat) (hi : w.nextIx template ≤ i)
    (hid : id = InstId.peer template i) (hlife : (w.st id).life ≠ .absent) : False := by
  have h0 := hO template i hi
  rw [hid] at hlife
  exact hlife h0.1

private theorem open_occupied (w : World) (id : InstId) (a : Actor) (hO : OpenSlots w)
    (hlife : (w.st id).life ≠ .absent) : OpenSlots (setActor w id a) := by
  refine open_set w id a hO ?_
  intro template i hi hid
  exact False.elim (not_open_occupied w hO id template i hi hid hlife)

private theorem release_spares_id (id : InstId) (ps : List Parked) (w : World) :
    (releaseFold id ps w).st id = w.st id := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change (releaseFold id ps w).st id = w.st id
      exact ih _
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      have hp : p.sender ≠ id := by
        intro h
        have hd : decide (p.sender = id) = true := decide_eq_true h
        simp [hd] at hf
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change (releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st id =
        w.st id
      rw [ih _]
      exact setActor_other w p.sender id (resumeSender (w.st p.sender) false id) hp.symm

private theorem release_skips_sender (id : InstId) (ps : List Parked) (w : World) (sid : InstId)
    (hs : ∀ p ∈ ps, p.sender = sid → p.isCall = true) :
    (releaseFold id ps w).st sid = w.st sid := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q.sender = sid → q.isCall = true :=
      fun q hq => hs q (List.mem_cons_of_mem _ hq)
    simp only [releaseFold, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hskip]
      change (releaseFold id ps w).st sid = w.st sid
      exact ih _ htail
    · have hf : (p.isCall || decide (p.sender = id)) = false := by
        cases hb : p.isCall || decide (p.sender = id) <;> simp_all
      have hwho : p.sender ≠ sid := by
        intro hsid
        have hc := hs p List.mem_cons_self hsid
        simp [hc] at hf
      conv in (List.foldl _ (if _ then _ else _) _) =>
        arg 2
        simp [hf]
      change (releaseFold id ps (setActor w p.sender (resumeSender (w.st p.sender) false id))).st sid =
        w.st sid
      rw [ih _ htail]
      exact setActor_other w p.sender sid (resumeSender (w.st p.sender) false id) hwho.symm

private theorem failWaiter_keeps_free (w : World) (dead i sid : InstId)
    (hf : notParked (w.st sid).phase) : notParked ((failWaiter w dead i).st sid).phase := by
  by_cases h : i = sid
  · rw [h]
    unfold failWaiter
    split
    · exact hf
    · cases hph : (w.st sid).phase with
      | parked _ _ _ =>
        rw [hph] at hf
        simp [notParked] at hf
      | awaitReply _ _ =>
        simp [hph, notParked]
      | idle => simp [hph, notParked]
      | run _ => simp [hph, notParked]
      | awaitEffect _ => simp [hph, notParked]
      | awaitPeer _ => simp [hph, notParked]
      | crashed => simp [hph, notParked]
  · rw [failWaiter_other w dead i sid (Ne.symm h)]
    exact hf

private theorem failFold_keeps_free (w : World) (dead sid : InstId) (ids : List InstId)
    (hf : notParked (w.st sid).phase) :
    notParked ((ids.foldl (fun w i => failWaiter w dead i) w).st sid).phase := by
  induction ids generalizing w with
  | nil => simpa using hf
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (failWaiter_keeps_free w dead i sid hf)

private theorem failFold_dead_phase (w : World) (dead : InstId) (ids : List InstId)
    (h : (w.st dead).life ≠ .alive) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st dead).phase = (w.st dead).phase := by
  induction ids generalizing w with
  | nil => rfl
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hj : j = dead
    · rw [hj]
      have hskip : failWaiter w dead dead = w := by
        unfold failWaiter
        have hb : ((w.st dead).life != .alive) = true := by
          cases hlife : (w.st dead).life <;> simp [hlife, bne] at h ⊢
        simp [hb]
      rw [hskip]
      exact ih _ h
    · have hst := failWaiter_other w dead j dead (Ne.symm hj)
      have hlife : ((failWaiter w dead j).st dead).life ≠ .alive := by
        rw [hst]
        exact h
      exact (ih _ hlife).trans (congrArg (·.phase) hst)

private theorem filter_keep (ps : List Parked) (dead : InstId)
    (h : ∀ p ∈ ps, (p.sender != dead) = true) :
    ps.filter (fun p => p.sender != dead) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp [List.filter, hp, ht]

private theorem filter_ne_idem (ps : List Parked) (dead : InstId) :
    ((ps.filter fun p => p.sender != dead).filter fun p => p.sender != dead) =
      ps.filter fun p => p.sender != dead := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : (p.sender != dead) = true
    · simp [List.filter, hp, ih]
    · simp [List.filter, hp, ih]

private theorem admitHost_filters (w : World) (dead host : InstId) (h : host ≠ dead) :
    ((admitHost w dead host).st host).parked =
      (w.st host).parked.filter fun p => p.sender != dead := by
  unfold admitHost
  have hb : (host == dead) = false := beq_eq_false_iff_ne.mpr h
  simp only [hb]
  by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
  · simp only [hempty, ite_true]
    have hkeep : ∀ p ∈ (w.st host).parked, (p.sender != dead) = true := by
      intro p hp
      by_cases heq : p.sender = dead
      · have hmem : p ∈ (w.st host).parked.filter fun q => q.sender == dead :=
          List.mem_filter.mpr ⟨hp, beq_iff_eq.mpr heq⟩
        have hnil : (w.st host).parked.filter (fun q => q.sender == dead) = [] := by
          cases hlist : (w.st host).parked.filter fun q => q.sender == dead with
          | nil => rfl
          | cons _ _ => simp [List.isEmpty, hlist] at hempty
        simp [hnil] at hmem
      · have hbf : (p.sender == dead) = false := beq_eq_false_iff_ne.mpr heq
        simp [bne, hbf]
    exact (filter_keep _ _ hkeep).symm
  · have hnot : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false := by
      cases hb' : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty
      · rfl
      · exact absurd hb' hempty
    simp [hnot, setActor]

private theorem admitHost_other_parked (w : World) (dead host i : InstId) (h : i ≠ host) :
    ((admitHost w dead host).st i).parked = (w.st i).parked := by
  unfold admitHost
  split
  · rfl
  · split
    · rfl
    · simp [setActor, h]

private theorem admitFold_outside (w : World) (dead i : InstId) (ids : List InstId) (h : i ∉ ids) :
    (ids.foldl (fun w host => admitHost w dead host) w).st i = w.st i := by
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have htail : i ∉ ids := fun hm => h (List.mem_cons_of_mem _ hm)
    have hhost : i ≠ host := by
      intro heq
      exact h (by simp [heq])
    have hstep : (admitHost w dead host).st i = w.st i := by
      unfold admitHost
      split
      · rfl
      · split
        · rfl
        · simp [setActor, hhost]
    exact (ih _ htail).trans hstep

private theorem admitFold_filters (w : World) (dead i : InstId) (ids : List InstId)
    (hne : i ≠ dead) (hmem : i ∈ ids) :
    ((ids.foldl (fun w host => admitHost w dead host) w).st i).parked =
      (w.st i).parked.filter fun p => p.sender != dead := by
  induction ids generalizing w with
  | nil => simp at hmem
  | cons host ids ih =>
    simp only [List.foldl_cons]
    by_cases hhead : i = host
    · rw [← hhead]
      have hstep := admitHost_filters w dead i hne
      by_cases htail : i ∈ ids
      · rw [ih (admitHost w dead i) htail, hstep, filter_ne_idem]
      · rw [admitFold_outside (admitHost w dead i) dead i ids htail, hstep]
    · have hmem' : i ∈ ids := by
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact absurd rfl hhead
        · exact hmem'
      rw [ih (admitHost w dead host) hmem', admitHost_other_parked w dead host i hhead]

private theorem admitFold_dead (w : World) (dead : InstId) (ids : List InstId) :
    ((ids.foldl (fun w host => admitHost w dead host) w).st dead).parked = (w.st dead).parked := by
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    by_cases h : host = dead
    · rw [h]
      have hstep : admitHost w dead dead = w := by
        unfold admitHost
        simp
      rw [hstep]
      exact ih _
    · rw [ih (admitHost w dead host), admitHost_other_parked w dead host dead (Ne.symm h)]

private theorem admitHost_sem (I : Impl) (w : World) (dead host : InstId) (hS : SemInv I w)
    (hmem : host ∈ w.roster) : SemInv I (admitHost w dead host) := by
  unfold admitHost
  split
  · exact hS
  · split
    · exact hS
    · let a : Actor :=
        { (w.st host) with
          box := (w.st host).box ++
            ((w.st host).parked.filter fun p => p.sender == dead).map (·.msg),
          parked := (w.st host).parked.filter fun p => p.sender != dead }
      exact sem_set I w host a hS rfl rfl
        (contTy_congr rfl rfl (hS.cont host))
        (programOk_congr I.desc host rfl rfl (hS.prog host))
        (waitEdge_congr I.desc host rfl rfl (hS.waited host))
        (by
          intro hdead
          exact hS.idleOff host hdead)
        (Or.inr hmem)

private theorem admit_roster (w : World) (dead host : InstId) :
    (admitHost w dead host).roster = w.roster := by
  unfold admitHost
  split
  · rfl
  · split
    · rfl
    · rfl

private theorem admitFold_sem (I : Impl) (w : World) (dead : InstId) (ids : List InstId)
    (hS : SemInv I w) (hsub : ∀ host ∈ ids, host ∈ w.roster) :
    SemInv I (ids.foldl (fun w host => admitHost w dead host) w) := by
  induction ids generalizing w with
  | nil => simpa using hS
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have hS1 := admitHost_sem I w dead host hS (hsub host List.mem_cons_self)
    have hsub' : ∀ h ∈ ids, h ∈ (admitHost w dead host).roster := by
      intro h hm
      rw [admit_roster]
      exact hsub h (List.mem_cons_of_mem _ hm)
    exact ih _ hS1 hsub'

private theorem open_admitHost (w : World) (dead host : InstId) (hO : OpenSlots w) :
    OpenSlots (admitHost w dead host) := by
  unfold admitHost
  split
  · exact hO
  · split
    · exact hO
    · refine open_set w host
        { (w.st host) with
          box := (w.st host).box ++
            ((w.st host).parked.filter fun p => p.sender == dead).map (·.msg),
          parked := (w.st host).parked.filter fun p => p.sender != dead } hO ?_
      intro template i hi hid
      have hold := hO template i hi
      refine ⟨?_, ?_, ?_⟩
      · rw [hid]
        exact hold.1
      · rw [hid]
        exact hold.2.1
      · rw [hid, hold.2.2]
        rfl

private theorem open_admitDead (w : World) (dead : InstId) (hO : OpenSlots w) :
    OpenSlots (admitDead w dead) := by
  have hfold : ∀ (ids : List InstId) (w : World),
      OpenSlots w → OpenSlots (ids.foldl (fun w host => admitHost w dead host) w) := by
    intro ids w
    induction ids generalizing w with
    | nil => intro h; simpa using h
    | cons host ids ih =>
      intro h
      simp only [List.foldl_cons]
      exact ih (admitHost w dead host) (open_admitHost w dead host h)
  simpa [admitDead] using hfold w.roster w hO

/-- Aborting one terminable actor preserves the three step invariants.
Its own mailbox is cleared. A reliable send it had parked on someone else moves
into that target's box, so a live target still has to handle it. -/
private theorem abortActor_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor)
    (t : Template) (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) (ha : a = w.st id)
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hpres : (w.st id).life ≠ .absent) :
    SemInv I (abortActor I.desc w id a) ∧ MailInv (abortActor I.desc w id a) ∧
      OpenSlots (abortActor I.desc w id a) := by
  let D := I.desc
  let ps := a.parked
  let wR := readCells D w id
  let wM := refundMsgs wR (tname id) a.box
  let wP := refundParked wM (tname id) ps
  let dead : Actor :=
    { (wP.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  let wD := setActor wP id dead
  let wRel := releaseParked wD id ps
  let wFail := failWaiters wRel id
  let wEnd := admitDead wFail id
  have hps : ps = (w.st id).parked := by simp [ps, ha]
  have hrel : releaseWorld D w id a = wRel := by
    simp [releaseWorld, wRel, wD, dead, wP, wM, wR, ps]
  have heq : abortActor D w id a = wEnd := by
    simp [abortActor, wEnd, wFail, hrel]
  have hSR : SemInv I wR := cells_sem I w id hS
  have hMR : MailInv wR := mail_copy w wR hM fun i => readCells_st D w id i
  have hRM := refund_msgs_inv I wR (tname id) a.box hSR hMR
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
    · intro i hdead
      by_cases h : i = id
      · subst h
        simp [wD, setActor_self, dead]
      · rw [setActor_other wP id i dead h] at hdead ⊢
        exact hRP.1.idleOff i hdead
    · intro i hlive
      by_cases h : i = id
      · simp [h, wD, setActor_self, dead] at hlive
      · rw [setActor_other wP id i dead h] at hlive
        exact hRP.1.rostered i hlive
    · intro i hmiss
      by_cases h : i = id
      · simp [h, wD, setActor_self, dead]
      · simp only [wD, setActor] at hmiss
        rw [setActor_other wP id i dead h]
        exact hRP.1.offEmpty i hmiss
  have hSRel : SemInv I wRel := release_sem I wD id ps hSD
  have hSFail : SemInv I wFail := by
    simpa [wFail, failWaiters] using failFold_sem I wRel id wRel.roster hSRel
  have hSEnd : SemInv I wEnd := by
    simpa [wEnd, admitDead] using
      admitFold_sem I wFail id wFail.roster hSFail (fun _ h => h)
  have hlifeP : (wP.st id).life ≠ .absent := by
    rw [(refundParked_rest wM (tname id) ps id).2.1,
      (refundMsgs_rest wR (tname id) a.box id).2.1, cellsSt]
    exact hpres
  have hOR := open_read D w id hO
  have hOM := open_msgs wR (tname id) a.box hOR
  have hOP := open_parks wM (tname id) ps hOM
  have hOD := open_occupied wP id dead hOP hlifeP
  have hORel := open_release wD id ps hOD
  have hOFail : OpenSlots wFail := by
    simpa [wFail, failWaiters] using open_failFold I wRel id wRel.roster hORel
  have hOEnd : OpenSlots wEnd := by simpa [wEnd] using open_admitDead wFail id hOFail
  have hstId : wRel.st id = dead := by
    have hfix := release_spares_id id ps wD
    rw [← release_fold_eq] at hfix
    simpa [wRel, wD, setActor_self] using hfix
  have hphId : (wEnd.st id).phase = .idle := by
    have hfail := failFold_dead_phase wRel id wRel.roster (by rw [hstId]; simp [dead])
    have hadmit := (admitDead_phase wFail id id).1
    simpa [wFail, failWaiters, wEnd, hstId] using hadmit.trans hfail
  have hpkId : (wEnd.st id).parked = [] := by
    have hfail := (failFold_mail wRel id id wRel.roster).2.2
    have hadmit := admitFold_dead wFail id wFail.roster
    simpa [wFail, failWaiters, wEnd, admitDead, hstId] using hadmit.trans hfail
  have hparkF : ∀ i, i ≠ id → (wRel.st i).parked = (w.st i).parked := by
    intro i hi
    have h1 : (wR.st i).parked = (w.st i).parked := congrArg (·.parked) (cellsSt D w id i)
    have h2 := (refundMsgs_rest wR (tname id) a.box i).2.2.2.2.1
    have h3 := (refundParked_rest wM (tname id) ps i).2.2.2.2.1
    have h4 : (wD.st i).parked = (wP.st i).parked :=
      congrArg (·.parked) (setActor_other wP id i dead hi)
    have h5 : (wRel.st i).parked = (wD.st i).parked := by
      have h := release_parked_all id ps wD i hi
      rw [← release_fold_eq] at h
      simpa [wRel] using h
    exact h5.trans (h4.trans (h3.trans (h2.trans h1)))
  have hphaseF : ∀ i, i ≠ id → (∀ p ∈ ps, p.sender ≠ i) → (wRel.st i).phase = (w.st i).phase := by
    intro i hi hs
    have hst := release_st_other id ps i wD hi hs
    rw [← release_fold_eq] at hst
    have hD : (wD.st i).phase = (w.st i).phase := by
      rw [setActor_other wP id i dead hi,
        (refundParked_rest wM (tname id) ps i).1,
        (refundMsgs_rest wR (tname id) a.box i).1, cellsSt]
    simpa [wRel] using (congrArg (·.phase) hst).trans hD
  have hpkEnd : ∀ i, i ≠ id →
      (wEnd.st i).parked = (w.st i).parked.filter fun p => p.sender != id := by
    intro i hi
    have hfail : (wFail.st i).parked = (wRel.st i).parked := by
      simpa [wFail, failWaiters] using (failFold_mail wRel id i wRel.roster).2.2
    by_cases hmem : i ∈ wFail.roster
    · have hfilt := admitFold_filters wFail id i wFail.roster hi hmem
      simpa [wEnd, admitDead, hfail, hparkF i hi] using hfilt
    · have hout := admitFold_outside wFail id i wFail.roster hmem
      have hempty := hSFail.offEmpty i hmem
      have hbase : (wFail.st i).parked = (w.st i).parked := hfail.trans (hparkF i hi)
      have hnil : (w.st i).parked = [] := by rw [← hbase]; exact hempty
      simp [wEnd, admitDead, hout, hempty, hnil]
  have hresume : ∀ p ∈ ps, p.isCall = false → notParked (wEnd.st p.sender).phase := by
    intro p hp hc
    by_cases hself : p.sender = id
    · rw [hself, hphId]
      simp [notParked]
    · have hfree := release_resumed id ps wD p hp hc hself
      rw [← release_fold_eq] at hfree
      have hkeep := failFold_keeps_free wRel id p.sender wRel.roster (by simpa [wRel] using hfree)
      have hadmit := (admitDead_phase wFail id p.sender).1
      have hnp : notParked (wFail.st p.sender).phase := by
        simpa [wFail, failWaiters] using hkeep
      rw [← hadmit] at hnp
      simpa [wEnd] using hnp
  have hstay : ∀ p ∈ ps, p.sender ≠ id → p.isCall = true →
      (wEnd.st p.sender).phase = (w.st p.sender).phase := by
    intro p hp hself hc
    have honly : ∀ q ∈ ps, q.sender = p.sender → q.isCall = true := by
      intro q hq heq
      have hq0 : q ∈ (w.st id).parked := by rw [← hps]; exact hq
      have hp0 : p ∈ (w.st id).parked := by rw [← hps]; exact hp
      have hsame := (hM.uniq id id q p hq0 hp0 heq).2
      rw [hsame]
      exact hc
    have hsk := release_skips_sender id ps wD p.sender honly
    rw [← release_fold_eq] at hsk
    obtain ⟨k, hk⟩ := hM.fwd id p (by rw [← hps]; exact hp)
    have hphD : (wD.st p.sender).phase = (w.st p.sender).phase := by
      rw [setActor_other wP id p.sender dead hself,
        (refundParked_rest wM (tname id) ps p.sender).1,
        (refundMsgs_rest wR (tname id) a.box p.sender).1, cellsSt]
    have hphRel : (wRel.st p.sender).phase = (w.st p.sender).phase := by
      simpa [wRel, hphD] using congrArg (·.phase) hsk
    have hkeep := failFold_keeps_call wRel id p.sender id wRel.roster k
      (by simpa [hphRel, hk, hc])
    have hfail : (wFail.st p.sender).phase = (wRel.st p.sender).phase := by
      simpa [wFail, failWaiters] using hkeep
    exact ((admitDead_phase wFail id p.sender).1).trans (hfail.trans hphRel)
  have hdeadLife : (wEnd.st id).life = .dead := by
    have hrel : (wRel.st id).life = .dead := by rw [hstId]
    have hfail : (wFail.st id).life = .dead := by
      simpa [wFail, failWaiters] using (failFold_life wRel id id wRel.roster).trans hrel
    exact ((admitDead_phase wFail id id).2).trans hfail
  have hother : ∀ i, i ≠ id → (∀ p ∈ ps, p.sender ≠ i) →
      (wEnd.st i).phase = (w.st i).phase ∨
        (notParked (w.st i).phase ∧ notParked (wEnd.st i).phase) := by
    intro i hi hs
    have hphRel := hphaseF i hi hs
    have hadmit := (admitDead_phase wFail id i).1
    have hlifeRel : (wRel.st i).life = (w.st i).life := by
      have hst := release_st_other id ps i wD hi hs
      rw [← release_fold_eq] at hst
      have hD : (wD.st i).life = (w.st i).life := by
        rw [setActor_other wP id i dead hi, (refundParked_rest wM (tname id) ps i).2.1,
          (refundMsgs_rest wR (tname id) a.box i).2.1, cellsSt]
      simpa [wRel] using (congrArg (·.life) hst).trans hD
    cases hph : (w.st i).phase with
    | parked dst c k =>
      cases c with
      | true =>
        have hkeep := failFold_keeps_call wRel id i dst wRel.roster k (by simpa [hphRel] using hph)
        have hfail : (wFail.st i).phase = (w.st i).phase := by
          simpa [wFail, failWaiters, hphRel] using hkeep
        exact Or.inl (hph ▸ hadmit.trans hfail)
      | false =>
        have hdst : dst ≠ id := by
          intro heq
          obtain ⟨q, hq, hsender, _⟩ := hM.bwdSend i id k (by simp [hph, heq])
          exact hs q (by rw [hps]; exact hq) hsender
        have hkeep := failFold_spares wRel id i dst wRel.roster false k hdst
          (by simpa [hphRel] using hph)
        have hfail : (wFail.st i).phase = (w.st i).phase := by
          simpa [wFail, failWaiters, hphRel] using hkeep
        exact Or.inl (hph ▸ hadmit.trans hfail)
    | awaitReply dst k =>
      by_cases hdst : dst = id
      · have hlive : (w.st i).life = .alive := by
          cases hlife : (w.st i).life with
          | alive => rfl
          | absent =>
            have hidle := hS.idleOff i (by simp [hlife])
            rw [hph] at hidle
            cases hidle
          | dead =>
            have hidle := hS.idleOff i (by simp [hlife])
            rw [hph] at hidle
            cases hidle
        have hmem := hSRel.rostered i (by simpa [hlifeRel] using hlive)
        have hdrop := failFold_drops_await wRel id i wRel.roster k
          (by simp [hphRel, hph, hdst]) (by simpa [hlifeRel] using hlive) hmem
        have hfail : (wFail.st i).phase = (w.st i).phase := by
          simpa [wFail, failWaiters, hph, hdst] using hdrop
        exact Or.inl (hph ▸ hadmit.trans hfail)
      · have hkeep := failFold_keeps_await wRel id i dst wRel.roster k hdst
          (by simpa [hphRel] using hph)
        have hfail : (wFail.st i).phase = (w.st i).phase := by
          simpa [wFail, failWaiters, hphRel] using hkeep
        exact Or.inl (hph ▸ hadmit.trans hfail)
    | idle =>
      have hh : holdsPhase (wRel.st i).phase = true := by simp [hphRel, hph, holdsPhase]
      have hkeep := (failFold_holds wRel id i wRel.roster hh).1
      have hfail : (wFail.st i).phase = (w.st i).phase := by
        simpa [wFail, failWaiters, hphRel] using hkeep
      exact Or.inl (hph ▸ hadmit.trans hfail)
    | run _ =>
      have hh : holdsPhase (wRel.st i).phase = true := by simp [hphRel, hph, holdsPhase]
      have hkeep := (failFold_holds wRel id i wRel.roster hh).1
      have hfail : (wFail.st i).phase = (w.st i).phase := by
        simpa [wFail, failWaiters, hphRel] using hkeep
      exact Or.inl (hph ▸ hadmit.trans hfail)
    | awaitEffect _ =>
      have hh : holdsPhase (wRel.st i).phase = true := by simp [hphRel, hph, holdsPhase]
      have hkeep := (failFold_holds wRel id i wRel.roster hh).1
      have hfail : (wFail.st i).phase = (w.st i).phase := by
        simpa [wFail, failWaiters, hphRel] using hkeep
      exact Or.inl (hph ▸ hadmit.trans hfail)
    | awaitPeer _ =>
      have hh : holdsPhase (wRel.st i).phase = true := by simp [hphRel, hph, holdsPhase]
      have hkeep := (failFold_holds wRel id i wRel.roster hh).1
      have hfail : (wFail.st i).phase = (w.st i).phase := by
        simpa [wFail, failWaiters, hphRel] using hkeep
      exact Or.inl (hph ▸ hadmit.trans hfail)
    | crashed =>
      have hh : holdsPhase (wRel.st i).phase = true := by simp [hphRel, hph, holdsPhase]
      have hkeep := (failFold_holds wRel id i wRel.roster hh).1
      have hfail : (wFail.st i).phase = (w.st i).phase := by
        simpa [wFail, failWaiters, hphRel] using hkeep
      exact Or.inl (hph ▸ hadmit.trans hfail)
  have hMEnd : MailInv wEnd :=
    mail_of_abort w wEnd id ps hM (fun p => by rw [hps]) hphId hpkId hpkEnd hresume hstay
      hdeadLife hother
      (fun i hgone => by
        by_cases hi : i = id
        · subst hi
          exact hdeadLife
        · have hD : (wD.st i).life = (w.st i).life := by
            rw [setActor_other wP id i dead hi, (refundParked_rest wM (tname id) ps i).2.1,
              (refundMsgs_rest wR (tname id) a.box i).2.1, cellsSt]
          have hrel := release_life id ps wD i
          rw [← release_fold_eq] at hrel
          have hfail := failFold_life wRel id i wRel.roster
          have heq : (wEnd.st i).life = (w.st i).life := by
            simpa [wEnd, wFail, failWaiters, wRel, hD] using
              ((admitDead_phase wFail id i).2).trans (hfail.trans hrel)
          rw [heq]
          exact hgone)
  exact ⟨by rw [heq]; exact hSEnd, by rw [heq]; exact hMEnd, by rw [heq]; exact hOEnd⟩

/-- A tombstone is one more priority message. Phase, life, typestate, and the
parked queue stay, so the three step invariants carry. -/
private theorem enqueueTombstone_inv (I : Impl) (w : World) (child : InstId)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) :
    SemInv I (enqueueTombstone I.desc w child) ∧ MailInv (enqueueTombstone I.desc w child) ∧
      OpenSlots (enqueueTombstone I.desc w child) := by
  cases hsup : supervisorOf I.desc child with
  | none =>
    simp [enqueueTombstone, hsup]
    exact ⟨hS, hM, hO⟩
  | some parent =>
    simp only [enqueueTombstone, hsup]
    by_cases hdead : ((w.st parent).life != .alive) = true
    · simp only [hdead, ite_true]
      exact ⟨hS, hM, hO⟩
    · have hf : ((w.st parent).life != .alive) = false := by
        cases hb : ((w.st parent).life != .alive) with
        | false => rfl
        | true => exact absurd hb hdead
      simp only [hf]
      have hlife : (w.st parent).life = .alive := by
        cases hl : (w.st parent).life with
        | alive => rfl
        | absent => simp [hl, bne] at hf
        | dead => simp [hl, bne] at hf
      refine ⟨?_, ?_, ?_⟩
      · apply sem_set
        · exact hS
        · rfl
        · rfl
        · simpa [contTy] using hS.cont parent
        · simpa [programOk] using hS.prog parent
        · simpa [waitEdge] using hS.waited parent
        · exact idleOff_same I w hS parent _ rfl rfl
        · exact Or.inl rfl
      · apply mail_set_same
        · exact hM
        · rfl
        · rfl
        · rfl
      · exact open_alive w parent _ hO hlife

/-- Aborting descendants preserves the three step invariants. An actor the fold
reaches is dead; every other actor keeps its life. -/
private theorem abortDesc_inv (fuel : Nat) (I : Impl) (hL : LocalOk I) (w : World)
    (parent : InstId) (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) :
    SemInv I (abortDesc fuel I.desc w parent) ∧ MailInv (abortDesc fuel I.desc w parent) ∧
      OpenSlots (abortDesc fuel I.desc w parent) ∧
      ∀ s, ((abortDesc fuel I.desc w parent).st s).life = (w.st s).life ∨
        ((abortDesc fuel I.desc w parent).st s).life = .dead := by
  induction fuel generalizing w parent with
  | zero =>
    refine ⟨hS, hM, hO, ?_⟩
    intro s
    simp [abortDesc]
  | succ fuel ihF =>
    let D := I.desc
    simp only [abortDesc]
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        SemInv I w0 → MailInv w0 → OpenSlots w0 →
        SemInv I (ids.foldl step w0) ∧ MailInv (ids.foldl step w0) ∧
          OpenSlots (ids.foldl step w0) ∧
          ∀ s, ((ids.foldl step w0).st s).life = (w0.st s).life ∨
            ((ids.foldl step w0).st s).life = .dead := by
      intro ids
      induction ids with
      | nil =>
        intro w0 hS0 hM0 hO0
        refine ⟨hS0, hM0, hO0, ?_⟩
        intro s
        simp
      | cons child ids ihL =>
        intro w0 hS0 hM0 hO0
        simp only [List.foldl_cons, step]
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive &&
            childTerminable D child) = true
        · simp only [hcond, ite_true]
          have hparts : (isChild D parent child = true ∧ (w0.st child).life = .alive) ∧
              childTerminable D child = true := by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcond
          obtain ⟨t, ht, hterm⟩ := childTerminable_spec D child hparts.2
          have h1 := ihF w0 child hS0 hM0 hO0
          let wDesc := abortDesc fuel D w0 child
          have hpres : (wDesc.st child).life ≠ .absent := by
            rcases h1.2.2.2 child with heq | hd
            · rw [heq, hparts.1.2]
              intro hbad
              cases hbad
            · rw [hd]
              intro hbad
              cases hbad
          have h2 := abortActor_inv I hL wDesc child (wDesc.st child) t
            h1.1 h1.2.1 h1.2.2.1 rfl ht hterm hpres
          let wAct := abortActor D wDesc child (wDesc.st child)
          have hdead : (wAct.st child).life = .dead := by
            have hrel := releaseWorld_self_dead D wDesc child (wDesc.st child)
            have hfail :=
              (failWaiters_life (releaseWorld D wDesc child (wDesc.st child)) child child).trans hrel
            simpa [abortActor, wAct] using
              (admitDead_phase (failWaiters (releaseWorld D wDesc child (wDesc.st child)) child)
                child child).2.trans hfail
          have htail := ihL wAct h2.1 h2.2.1 h2.2.2
          refine ⟨htail.1, htail.2.1, htail.2.2.1, ?_⟩
          intro s
          rcases htail.2.2.2 s with heq | hd
          · by_cases hs : s = child
            · rw [heq, hs]
              exact Or.inr hdead
            · rw [heq, abortActor_other_life D wDesc child s (wDesc.st child) hs]
              exact h1.2.2.2 s
          · exact Or.inr hd
        · have hf : (isChild D parent child && (w0.st child).life == .alive &&
              childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive &&
                childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf]
          exact ihL w0 hS0 hM0 hO0
    exact hfold w.roster w hS hM hO

/-- Voluntary termination: descendants die in this step, then the stage itself,
then its parent is told. -/
private theorem terminateStage_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId)
    (t : Template) (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w)
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hpres : (w.st id).life ≠ .absent) :
    SemInv I (terminateStage I.desc w id (w.st id)) ∧
      MailInv (terminateStage I.desc w id (w.st id)) ∧
      OpenSlots (terminateStage I.desc w id (w.st id)) := by
  let D := I.desc
  let w1 := abortDesc w.roster.length D w id
  have h1 := abortDesc_inv w.roster.length I hL w id hS hM hO
  have hpres1 : (w1.st id).life ≠ .absent := by
    rcases h1.2.2.2 id with heq | hd
    · rw [heq]
      exact hpres
    · rw [hd]
      intro hbad
      cases hbad
  have h2 := abortActor_inv I hL w1 id (w1.st id) t h1.1 h1.2.1 h1.2.2.1 rfl ht hterm hpres1
  have h3 := enqueueTombstone_inv I (abortActor D w1 id (w1.st id)) id h2.1 h2.2.1 h2.2.2
  simpa [terminateStage, D, w1] using h3

/-- A committing `terminate` that is not the lone childless case aborts descendants. -/
private theorem exec_cascade_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId)
    (t : Template) (k : Cont) (es : List Eff) (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w)
    (hphase : (w.st id).phase = .run { k with rest := .terminate :: es })
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hwhy : t.subtree ≠ "" ∨ hasChild I.desc w id = true)
    (hnocall : t.subtree = "" → hasParkedCall (w.st id).parked = false) :
    SemInv I (execRun I w id (w.st id) { k with rest := .terminate :: es }) ∧
      MailInv (execRun I w id (w.st id) { k with rest := .terminate :: es }) ∧
      OpenSlots (execRun I w id (w.st id) { k with rest := .terminate :: es }) := by
  have hlive : (w.st id).life = .alive :=
    alive_if_busy I w hS id (by rw [hphase]; intro hbad; cases hbad)
  have hgo : (t.terminable && (t.subtree != "" || !hasParkedCall (w.st id).parked)) = true := by
    have hor : (t.subtree != "" || !hasParkedCall (w.st id).parked) = true := by
      rcases hwhy with hsub | _hchild
      · simp [bne, hsub]
      · by_cases hsub : t.subtree = ""
        · have hpk := hnocall hsub
          simp [bne, hsub, hpk]
        · simp [bne, hsub]
    simp [hterm, hor]
  have hlone : (t.subtree == "" && !(hasChild I.desc w id)) = false := by
    rcases hwhy with hsub | hchild
    · simp [beq_iff_eq, hsub]
    · simp [hchild]
  have heq : execRun I w id (w.st id) { k with rest := .terminate :: es } =
      terminateStage I.desc w id (w.st id) := by
    have hred : execRun I w id (w.st id) { k with rest := .terminate :: es } =
        (if t.subtree == "" && !(hasChild I.desc w id) then
          releaseWorld I.desc w id (w.st id)
        else terminateStage I.desc w id (w.st id)) := by
      simp [execRun, ht, hgo]
    rw [hred]
    simp [hlone]
  have hinv := terminateStage_inv I hL w id t hS hM hO ht hterm (by rw [hlive]; intro hbad; cases hbad)
  exact ⟨by rw [heq]; exact hinv.1, by rw [heq]; exact hinv.2.1, by rw [heq]; exact hinv.2.2⟩

theorem exec_head_inv (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (w' : World)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w) (h : execHead I w id = some w') :
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
            by_cases hkill : (t.terminable && (t.subtree != "" || !hasParkedCall (w.st id).parked)) = true
            · have hterm : t.terminable = true := by
                simp [Bool.and_eq_true] at hkill
                exact hkill.1
              by_cases hsub : t.subtree = ""
              · by_cases hchild : hasChild I.desc w id = true
                · have hpk : hasParkedCall (w.st id).parked = false := by
                    simp [Bool.and_eq_true, bne, hsub] at hkill
                    exact hkill.2
                  have hinv := exec_cascade_inv I hL w id t k' es hS hM hO hphase ht hterm
                    (Or.inr hchild) (fun _ => hpk)
                  exact ⟨hinv.1, hinv.2.1⟩
                · have hf : hasChild I.desc w id = false := by
                    cases hb : hasChild I.desc w id with
                    | false => rfl
                    | true => exact absurd hb hchild
                  have hparts : t.terminable = true ∧ hasParkedCall (w.st id).parked = false := by
                    simp [Bool.and_eq_true, bne, hsub] at hkill
                    exact hkill
                  exact exec_term_die_sem I hL w id t k' es hS hM hphase ht hparts.1 hparts.2 hsub hf
              · have hinv := exec_cascade_inv I hL w id t k' es hS hM hO hphase ht hterm
                  (Or.inl hsub) (fun h => absurd h hsub)
                exact ⟨hinv.1, hinv.2.1⟩
            · exact exec_term_skip_sem I w id k' es hS hM hphase
                (by
                  intro t' ht'
                  have : t' = t := by rw [ht] at ht'; cases ht'; rfl
                  simpa [this] using hkill)
    · cases h

theorem exec_run_open (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (k : Cont)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w)
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
      cases hr : route w I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        exact open_busy w id _ hO (busy_run id w k hph)
      | some dst =>
        simp [execRun, hk, hr]
        exact enqueue_open w I.desc id dst _ false _ hO (busy_run id w k hph)
    | call d l n =>
      cases hr : resolveId I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        have hOn : OpenSlots (noteStale w id d) := by
          intro t i hi
          exact hO t i hi
        exact open_busy (noteStale w id d) id _ hOn (by simpa using busy_run id w k hph)
      | some dstId =>
        simp [execRun, hk, hr]
        exact enqueue_open w I.desc id dstId _ true _ hO (busy_run id w k hph)
    | trySend d l n =>
      cases hr : route w I.desc id d with
      | none =>
        simp [execRun, hk, hr]
        exact open_busy w id _ hO (busy_run id w k hph)
      | some dst =>
        simp [execRun, hk, hr]
        split
        · exact enqueue_open w I.desc id dst _ false _ hO (busy_run id w k hph)
        · exact open_busy w id _ hO (busy_run id w k hph)
    | reply =>
      simp [execRun, hk, performReply, afterHead]
      cases hto : k.replyTo with
      | none =>
        simpa [hto] using open_busy w id _ hO (busy_run id w k hph)
      | some caller =>
        cases hphc : (w.st caller).phase with
        | awaitReply dst ck =>
          by_cases hd : dst = id
          · by_cases hc : caller = id
            · rw [hc, hph] at hphc
              cases hphc
            · simp [hto, hphc, hd]
              by_cases hm : (w.st id).oweId = some (w.st caller).waitId
              · simp [hm]
                exact open_busy _ id _
                  (open_busy w caller _ hO (by rw [hphc]; intro hbad; cases hbad))
                  (by rw [setActor_other _ caller id _ (Ne.symm hc)]; exact busy_run id w k hph)
              · simp [hm]
                exact open_busy w id _ hO (busy_run id w k hph)
          · simpa [hto, hphc, hd] using open_busy w id _ hO (busy_run id w k hph)
        | idle =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
        | run _ =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
        | parked _ _ _ =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
        | awaitEffect _ =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
        | awaitPeer _ =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
        | crashed =>
          simpa [hto, hphc] using open_busy w id _ hO (busy_run id w k hph)
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
        · next hgo =>
          split
          · have hbase := open_parks _ (tname id) (w.st id).parked
              (open_msgs _ (tname id) (w.st id).box (open_read I.desc w id hO))
            exact open_release _ id (w.st id).parked
              (open_busy _ id _ hbase (by
                rw [(refund_park_phase _ (tname id) (w.st id).parked id).1,
                  (refund_msgs_phase _ (tname id) (w.st id).box id).1, readCells_st, hph]
                intro hbad
                cases hbad))
          · have hterm : t.terminable = true := hgo.1
            exact (terminateStage_inv I hL w id t hS hM hO ht hterm
              (by intro hbad; rw [hlive] at hbad; cases hbad)).2.2
        · exact hO
      · exact hO

theorem exec_head_open (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (w' : World)
    (hS : SemInv I w) (hM : MailInv w) (hO : OpenSlots w)
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
      exact exec_run_open I hL w id k hS hM hO hlive hph
    · cases h

theorem detachHost_cont (a : Actor) (caller : InstId) (cid : Nat) (h : contTy a) :
    contTy (detachReply (detachBox a caller) caller cid) := by
  unfold detachReply
  split
  · cases hph : a.phase with
    | idle => simp [detachBox, clearReplyPhase, contTy, hph]
    | crashed => simp [detachBox, clearReplyPhase, contTy, hph]
    | run k =>
      simp [detachBox, clearReplyPhase, contTy, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).2]
      exact h
    | parked _ _ k =>
      simp [detachBox, clearReplyPhase, contTy, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).2]
      exact h
    | awaitReply _ k =>
      simp [detachBox, clearReplyPhase, contTy, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).2]
      exact h
    | awaitEffect k =>
      simp [detachBox, clearReplyPhase, contTy, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).2]
      exact h
    | awaitPeer k =>
      simp [detachBox, clearReplyPhase, contTy, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).2]
      exact h
  · cases hph : a.phase <;> simp [detachBox, contTy, hph] at h ⊢ <;> exact h

theorem detachHost_prog (D : Description) (id caller : InstId) (a : Actor) (cid : Nat)
    (h : programOk D id a) : programOk D id (detachReply (detachBox a caller) caller cid) := by
  unfold detachReply
  split
  · cases hph : a.phase with
    | idle => simp [detachBox, clearReplyPhase, programOk, hph]
    | crashed => simp [detachBox, clearReplyPhase, programOk, hph]
    | run k =>
      simp [detachBox, clearReplyPhase, programOk, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).1]
      exact h
    | parked _ _ k =>
      simp [detachBox, clearReplyPhase, programOk, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).1]
      exact h
    | awaitReply _ k =>
      simp [detachBox, clearReplyPhase, programOk, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).1]
      exact h
    | awaitEffect k =>
      simp [detachBox, clearReplyPhase, programOk, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).1]
      exact h
    | awaitPeer k =>
      simp [detachBox, clearReplyPhase, programOk, hph] at h ⊢
      rw [(clearReplyCont_keeps caller k).1]
      exact h
  · cases hph : a.phase <;> simp [detachBox, programOk, hph] at h ⊢ <;> exact h

theorem detachHost_wait (D : Description) (id caller : InstId) (a : Actor) (cid : Nat)
    (h : waitEdge D id a) : waitEdge D id (detachReply (detachBox a caller) caller cid) := by
  unfold detachReply
  split
  · cases hph : a.phase with
    | idle => simp [detachBox, clearReplyPhase, waitEdge, hph]
    | crashed => simp [detachBox, clearReplyPhase, waitEdge, hph]
    | run _ => simp [detachBox, clearReplyPhase, waitEdge, hph]
    | awaitEffect _ => simp [detachBox, clearReplyPhase, waitEdge, hph]
    | awaitPeer _ => simp [detachBox, clearReplyPhase, waitEdge, hph]
    | parked _ _ _ =>
      simp [detachBox, clearReplyPhase, waitEdge, hph] at h ⊢
      exact h
    | awaitReply _ _ =>
      simp [detachBox, clearReplyPhase, waitEdge, hph] at h ⊢
      exact h
  · cases hph : a.phase <;> simp [detachBox, waitEdge, hph] at h ⊢ <;> exact h

theorem detachHost_idle (a : Actor) (caller : InstId) (cid : Nat) (h : a.phase = .idle) :
    (detachReply (detachBox a caller) caller cid).phase = .idle := by
  unfold detachReply
  split
  · simp [detachBox, clearReplyPhase, h]
  · simp [detachBox, h]

private theorem refundCall_sem (I : Impl) (w : World) (caller dst : InstId) (hS : SemInv I w) :
    SemInv I (refundParkedCall w caller dst) := by
  unfold refundParkedCall
  dsimp only
  let pred := fun p : Parked => p.sender == caller && p.isCall
  split
  · exact hS
  · next hgo =>
    have hmem : dst ∈ w.roster := by
      by_cases hnot : dst ∈ w.roster
      · exact hnot
      · have hemptyPk := hS.offEmpty dst hnot
        simp [hemptyPk, pred] at hgo
    let dropped := { (w.st dst) with
      parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
    let base := setActor w dst dropped
    have hS1 : SemInv I base := by
      apply sem_set I w dst dropped hS rfl rfl
      · simpa [dropped, contTy] using hS.cont dst
      · simpa [dropped, programOk] using hS.prog dst
      · simpa [dropped, waitEdge] using hS.waited dst
      · exact idleOff_same I w hS dst dropped rfl rfl
      · exact Or.inr hmem
    have hfold : ∀ (ps : List Parked) (w0 : World), SemInv I w0 →
        SemInv I (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0) := by
      intro ps
      induction ps with
      | nil => intro w0 h; simpa using h
      | cons p ps ih =>
        intro w0 h
        simp only [List.foldl_cons]
        exact ih _ (credit_sem I w0 (tname dst) caller h)
    exact hfold ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall) base hS1

private theorem refundCall_open (w : World) (caller dst : InstId) (hO : OpenSlots w) :
    OpenSlots (refundParkedCall w caller dst) := by
  unfold refundParkedCall
  dsimp only
  let pred := fun p : Parked => p.sender == caller && p.isCall
  split
  · exact hO
  · next hgo =>
    let dropped := { (w.st dst) with
      parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
    let base := setActor w dst dropped
    have hO1 : OpenSlots base := by
      refine open_set w dst dropped hO ?_
      intro template i hi hid
      have h0 := hO template i hi
      simp [dropped, hid, h0.1, h0.2.1, h0.2.2]
    have hfold : ∀ (ps : List Parked) (w0 : World), OpenSlots w0 →
        OpenSlots (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0) := by
      intro ps
      induction ps with
      | nil => intro w0 h; simpa using h
      | cons p ps ih =>
        intro w0 h
        simp only [List.foldl_cons]
        exact ih _ (open_credit w0 (tname dst) caller h)
    exact hfold ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall) base hO1

theorem callTimeout_inv (I : Impl) (w w' : World) (id : InstId) (hS : SemInv I w)
    (hM : MailInv w) (hO : OpenSlots w) (h : callTimeout w id = some w') :
    SemInv I w' ∧ MailInv w' ∧ OpenSlots w' := by
  unfold callTimeout at h
  dsimp only at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hgo : ((w.st id).life != .alive) = false := by simpa [Bool.not_eq_true] using hlive
    have halive : (w.st id).life = .alive := by
      cases hl : (w.st id).life with
      | alive => rfl
      | absent => simp [hl, bne] at hgo
      | dead => simp [hl, bne] at hgo
    simp only [hgo, ite_false] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      cases h
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hrest := detachHost_rest (w.st dst) id cid
      have hS1 := sem_set I w dst host hS hrest.1 hrest.2.1
        (detachHost_cont (w.st dst) id cid (hS.cont dst))
        (detachHost_prog I.desc dst id (w.st dst) cid (hS.prog dst))
        (detachHost_wait I.desc dst id (w.st dst) cid (hS.waited dst))
        (by
          intro hdead
          exact detachHost_idle (w.st dst) id cid
            (hS.idleOff dst (by rw [← hrest.2.1]; exact hdead)))
        (Or.inl hrest.2.2)
      have hM1 := mail_scrub w dst host hM hrest.2.2 hrest.2.1
        (fun dst' c k' hk => (detachHost_park (w.st dst) id cid dst' c).mpr ⟨k', hk⟩)
        (fun dst' c k' hk => (detachHost_park (w.st dst) id cid dst' c).mp ⟨k', hk⟩)
      have hO1 : OpenSlots w1 := by
        refine open_set w dst host hO ?_
        intro template i hi hid
        have h0 := hO template i hi
        simp [host, cid, hid]
        exact ⟨(detachHost_rest (w.st (InstId.peer template i)) id cid).2.1.trans h0.1,
          detachHost_idle (w.st (InstId.peer template i)) id cid h0.2.1,
          (detachHost_rest (w.st (InstId.peer template i)) id cid).2.2.trans h0.2.2⟩
      have hty : (w1.st id).typestate = k.toState := by
        have hty0 : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
        by_cases hself : id = dst
        · rw [hself] at hty0
          simp [w1, host, cid]
          rw [hself, setActor_self]
          exact (detachHost_rest (w.st dst) dst (w.st dst).waitId).1.trans hty0
        · simp [w1, setActor_other w dst id host hself]
          exact hty0
      have hprog : effectsOk I.desc (tname id) (w1.st id).typestate k.rest = true := by
        have hraw : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
          simpa [programOk, hph] using hS.prog id
        by_cases hself : id = dst
        · rw [hself] at hraw
          simp [w1, host, cid]
          rw [hself, setActor_self]
          rw [(detachHost_rest (w.st dst) dst (w.st dst).waitId).1]
          exact hraw
        · simp [w1, setActor_other w dst id host hself]
          exact hraw
      have hlive1 : (w1.st id).life = .alive := by
        by_cases hself : id = dst
        · rw [hself] at halive
          simp [w1, host, cid]
          rw [hself, setActor_self]
          exact (detachHost_rest (w.st dst) dst (w.st dst).waitId).2.1.trans halive
        · simp [w1, setActor_other w dst id host hself]
          exact halive
      have hp := proceed_ok I.desc id (w1.st id) k hty hprog
      let done := finishCall (w1.st id) k .timedOut
      have hS2 := sem_set I w1 id done hS1
        (by simp [done, finishCall]; exact hp.1)
        (by simp [done, finishCall]; exact hp.2.1)
        (by simp [done, finishCall]; exact hp.2.2.1)
        (by simp [done, finishCall]; exact hp.2.2.2.1)
        (by simp [done, finishCall]; exact hp.2.2.2.2)
        (idleOff_life (by simp [done, finishCall]; exact hp.2.1.trans hlive1))
        (Or.inl (by simp [done, finishCall, proceed_parked]))
      have hfree1 : notParked (w1.st id).phase := by
        by_cases hself : id = dst
        · simp [w1, host, cid, detachReply, detachBox]
          rw [hself] at hph ⊢
          rw [setActor_self]
          simp [clearReplyPhase, hph]
          split <;> simp [notParked]
        · simp [w1, setActor_other w dst id host hself, hph, notParked]
      have hM2 := mail_set_free w1 id done hM1 hfree1
        (by simp [done, finishCall]; exact proceed_not_parked _ _)
        (by simp [done, finishCall, proceed_parked])
        (by simp [done, finishCall]; exact proceed_keeps_life _ _)
      have hO2 := open_alive w1 id done hO1 hlive1
      exact ⟨hS2, hM2, hO2⟩
    | parked dst isCall k =>
      cases isCall with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        cases h
        have hSR := refundCall_sem I w id dst hS
        have hOR := refundCall_open w id dst hO
        let done := finishCall ((refundParkedCall w id dst).st id) k .notAdmitted
        have hty : ((refundParkedCall w id dst).st id).typestate = k.toState := by
          rw [(refundCall_fields w id dst id).2.2.1]
          simpa [contTy, hph] using hS.cont id
        have hprog : effectsOk I.desc (tname id) ((refundParkedCall w id dst).st id).typestate k.rest = true := by
          rw [(refundCall_fields w id dst id).2.2.1]
          simpa [programOk, hph] using hS.prog id
        have hp := proceed_ok I.desc id ((refundParkedCall w id dst).st id) k hty hprog
        have hS2 := sem_set I (refundParkedCall w id dst) id done hSR
          (by simp [done, finishCall]; exact hp.1)
          (by simp [done, finishCall]; exact hp.2.1)
          (by simp [done, finishCall]; exact hp.2.2.1)
          (by simp [done, finishCall]; exact hp.2.2.2.1)
          (by simp [done, finishCall]; exact hp.2.2.2.2)
          (idleOff_life (by
            simp [done, finishCall]
            exact hp.2.1.trans ((refundCall_fields w id dst id).2.1.trans halive)))
          (Or.inl (by simp [done, finishCall, proceed_parked]))
        have hM2 := mail_not_admitted w id dst done hM ⟨k, hph⟩
          (by simp [done, finishCall]; exact proceed_not_parked _ _)
          (by
            exact (finishCall_life ((refundParkedCall w id dst).st id) k .notAdmitted).trans
              (refundCall_fields w id dst id).2.1)
          (by simp [done, finishCall, proceed_parked])
        have hO2 := open_alive (refundParkedCall w id dst) id done hOR
          ((refundCall_fields w id dst id).2.1.trans halive)
        exact ⟨hS2, hM2, hO2⟩
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

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
    exact ⟨(exec_head_inv I hL w id w' hS hM hO ha).1, (exec_head_inv I hL w id w' hS hM hO ha).2,
      exec_head_open I hL w id w' hS hM hO ha⟩
  | finish id =>
    exact ⟨(finish_inv I w w' id hS hM ha).1, (finish_inv I w w' id hS hM ha).2, open_finish I w id w' hO ha⟩
  | spawn template =>
    have hlot : (w.st (InstId.peer template (w.nextIx template))).life ≠ .dead := by
      have h0 := hO template (w.nextIx template) (Nat.le_refl _)
      rw [h0.1]
      intro h
      cases h
    exact ⟨(spawn_inv I w template w' hS hM (open_slot w hO template) hlot ha).1,
      (spawn_inv I w template w' hS hM (open_slot w hO template) hlot ha).2,
      open_spawn I w template w' hO ha⟩
  | ingress dst label =>
    exact ⟨ingress_sem I w w' dst label hS ha, ingress_mail I w w' dst label hM ha,
      open_ingress I w w' dst label hO ha⟩
  | callTimeout id =>
    exact callTimeout_inv I w w' id hS hM hO (by simpa [apply] using ha)
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
