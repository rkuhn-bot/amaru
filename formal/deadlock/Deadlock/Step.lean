import Deadlock.Pres

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

end Deadlock
