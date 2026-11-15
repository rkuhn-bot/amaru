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

end Deadlock
