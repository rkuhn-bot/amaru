import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

theorem proceed_not_effect (a : Actor) (k : Cont) :
    waitKind (proceed a k) ≠ some .effect := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem proceed_not_peer (a : Actor) (k : Cont) :
    waitKind (proceed a k) ≠ some .peer := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem wait_effect_phase (a : Actor) (h : waitKind a = some .effect) :
    ∃ k, a.phase = .awaitEffect k := by
  cases hphase : a.phase with
  | parked _ isCall _ => cases isCall <;> simp [waitKind, hphase] at h
  | awaitEffect k => exact ⟨k, rfl⟩
  | idle => simp [waitKind, hphase] at h
  | run _ => simp [waitKind, hphase] at h
  | awaitReply _ _ => simp [waitKind, hphase] at h
  | awaitPeer _ => simp [waitKind, hphase] at h
  | crashed => simp [waitKind, hphase] at h

theorem wait_peer_phase (a : Actor) (h : waitKind a = some .peer) :
    ∃ k, a.phase = .awaitPeer k := by
  cases hphase : a.phase with
  | parked _ isCall _ => cases isCall <;> simp [waitKind, hphase] at h
  | awaitPeer k => exact ⟨k, rfl⟩
  | idle => simp [waitKind, hphase] at h
  | run _ => simp [waitKind, hphase] at h
  | awaitReply _ _ => simp [waitKind, hphase] at h
  | awaitEffect _ => simp [waitKind, hphase] at h
  | crashed => simp [waitKind, hphase] at h

theorem finish_clears_effect (w : World) (s : InstId) (w' : World)
    (h : finishWait w s = some w') (hp : waitKind (w.st s) = some .effect) :
    waitKind (w'.st s) ≠ some .effect := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  simp [finishWait, hk] at h
  subst h
  simpa [setActor_self] using proceed_not_effect (w.st s) k

theorem finish_clears_peer (w : World) (s : InstId) (w' : World)
    (h : finishWait w s = some w') (hp : waitKind (w.st s) = some .peer) :
    waitKind (w'.st s) ≠ some .peer := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  simp [finishWait, hk] at h
  subst h
  simpa [setActor_self] using proceed_not_peer (w.st s) k

theorem enabled_finish_effect (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .effect) : Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  simp [Enabled, apply, finishWait, hk]

theorem enabled_finish_peer (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .peer) : Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  simp [Enabled, apply, finishWait, hk]

theorem not_stuck_effect {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i)
    (hp : waitKind ((ρ.cfg i).st s) = some .effect) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    have hs := h.2 j hj
    simp [SameWait] at hs
    exact hs.1.symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_effect I (ρ.cfg j) s (hall j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_effect (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (s : InstId) (i : Nat) (h : Stuck ρ s i)
    (hp : waitKind ((ρ.cfg i).st s) = some .peer) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    have hs := h.2 j hj
    simp [SameWait] at hs
    exact hs.1.symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_peer I (ρ.cfg j) s (hall j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_peer (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_cell {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i : Nat)
    (hp : waitKind ((ρ.cfg i).st s) = some .cell) : False :=
  waitKind_ne_cell _ hp

/-! Reply oneshot: the caller's bulk mailbox is not an input of the reply step. -/

theorem proceed_ne_run (a : Actor) (k k0 : Cont) (hne : k ≠ k0) :
    (proceed a k).phase ≠ .run k0 := by
  cases hk : k.rest <;> simp [proceed, hk, hne]

theorem afterHead_ne {k : Cont} (h : k.rest ≠ []) : afterHead k ≠ k := by
  cases hk : k.rest with
  | nil => simp [hk] at h
  | cons _ es =>
    intro heq
    have hrest := congrArg Cont.rest heq
    simp [afterHead, hk] at hrest

theorem run_enabled (I : Impl) (w : World) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hl : (w.st s).life = .alive) :
    Enabled I w (.exec s) := by
  simp [Enabled, apply, execHead, hp, hl]

theorem can_receive_enabled (I : Impl) (w : World) (s : InstId) (h : CanReceive w s) :
    Enabled I w (.recvBulk s) := by
  rcases h with ⟨⟨hl, hidle⟩, hwork⟩
  simp [Enabled, apply, receiveBulk, alive] at hl ⊢
  simp [hidle, hl]
  cases hbox : (w.st s).box <;> cases hpark : (w.st s).parked <;> simp_all

/-- Taking a bulk message while `sender` is the head of an empty mailbox resumes it. -/
theorem recv_resumes_head_of_box (I : Impl) (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (hl : (w.st id).life = .alive) (hp : (w.st id).phase = .idle)
    (hpark : (w.st id).parked = p :: ps)
    (w' : World) (h : receiveBulk I w id = some w') :
    (w'.st p.sender).phase = (resumeSender (w.st p.sender) p.isCall id).phase := by
  cases hbox : (w.st id).box with
  | nil =>
    simp [receiveBulk, hl, hp, hbox, hpark, setActor] at h
    subst h
    by_cases hs : p.sender = id
    · simp [hs]
    · simp [hs]
  | cons m ms =>
    simp [receiveBulk, hl, hp, hbox, hpark, setActor] at h
    subst h
    by_cases hs : p.sender = id
    · simp [hs]
    · simp [hs]

theorem recv_resumes_head (I : Impl) (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (hl : (w.st id).life = .alive) (hp : (w.st id).phase = .idle)
    (hbox : (w.st id).box = []) (hpark : (w.st id).parked = p :: ps)
    (w' : World) (h : receiveBulk I w id = some w') :
    (w'.st p.sender).phase = (resumeSender (w.st p.sender) p.isCall id).phase := by
  simp [receiveBulk, hl, hp, hbox, hpark, setActor] at h
  subst h
  by_cases hs : p.sender = id
  · simp [hs]
  · simp [hs]

theorem performReply_caller_box (w : World) (sender caller : InstId) (k ck : Cont)
    (hphase : (w.st caller).phase = .awaitReply sender ck)
    (hreply : k.replyTo = some caller) (hdiff : sender ≠ caller) :
    ((performReply w sender k).st caller).box = (w.st caller).box := by
  have hcaller : caller ≠ sender := hdiff.symm
  simp [performReply, hreply, hphase, setActor, proceed, hcaller]
  cases ck.rest <;> rfl

end Deadlock
