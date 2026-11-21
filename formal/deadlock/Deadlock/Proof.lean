import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

theorem proceed_not_effect (a : Actor) (k : Cont) : waitKind (proceed a k) ≠ some .effect := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem proceed_not_peer (a : Actor) (k : Cont) : waitKind (proceed a k) ≠ some .peer := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem proceed_not_send (a : Actor) (k : Cont) (dst : InstId) :
    waitKind (proceed a k) ≠ some (.blockingSend dst) := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem proceed_not_call (a : Actor) (k : Cont) (dst : InstId) :
    waitKind (proceed a k) ≠ some (.callReply dst) := by
  cases h : k.rest <;> simp [proceed, waitKind, h]

theorem wait_effect_phase (a : Actor) (h : waitKind a = some .effect) : ∃ k, a.phase = .awaitEffect k := by
  cases hphase : a.phase with
  | parked _ isCall _ => cases isCall <;> simp [waitKind, hphase] at h
  | awaitEffect k => exact ⟨k, rfl⟩
  | idle => simp [waitKind, hphase] at h
  | run _ => simp [waitKind, hphase] at h
  | awaitReply _ _ => simp [waitKind, hphase] at h
  | awaitPeer _ => simp [waitKind, hphase] at h
  | crashed => simp [waitKind, hphase] at h

theorem wait_peer_phase (a : Actor) (h : waitKind a = some .peer) : ∃ k, a.phase = .awaitPeer k := by
  cases hphase : a.phase with
  | parked _ isCall _ => cases isCall <;> simp [waitKind, hphase] at h
  | awaitPeer k => exact ⟨k, rfl⟩
  | idle => simp [waitKind, hphase] at h
  | run _ => simp [waitKind, hphase] at h
  | awaitReply _ _ => simp [waitKind, hphase] at h
  | awaitEffect _ => simp [waitKind, hphase] at h
  | crashed => simp [waitKind, hphase] at h

theorem finish_clears_effect (I : Impl) (w : World) (s : InstId) (w' : World)
    (h : finishWait I w s = some w') (hp : waitKind (w.st s) = some .effect) :
    waitKind (w'.st s) ≠ some .effect := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  unfold finishWait at h
  split at h
  · cases h
  · rw [hk] at h
    cases h
    rw [setActor_self]
    exact proceed_not_effect (w.st s) k

theorem finish_clears_peer (I : Impl) (w : World) (s : InstId) (w' : World)
    (h : finishWait I w s = some w') (hp : waitKind (w.st s) = some .peer) :
    waitKind (w'.st s) ≠ some .peer := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  unfold finishWait at h
  split at h
  · cases h
  · rw [hk] at h
    cases h
    rw [setActor_self]
    exact proceed_not_peer (w.st s) k

theorem effect_finish_enabled (I : Impl) (w : World) (id : InstId) (k : Cont)
    (h : (w.st id).phase = .awaitEffect k) (hc : w.crashed = false)
    (hl : (w.st id).life = .alive) : Enabled I w (.finish id) := by
  simp [Enabled, apply, stepWorld, finishWait, h, hc, hl]

theorem peer_finish_enabled (I : Impl) (w : World) (id : InstId) (k : Cont)
    (h : (w.st id).phase = .awaitPeer k) (_hf : peerFinishable I.desc id = true)
    (hc : w.crashed = false) (hl : (w.st id).life = .alive) :
    Enabled I w (.finish id) := by
  simp [Enabled, apply, stepWorld, finishWait, h, hc, hl]

theorem enabled_finish_effect (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .effect) (hc : w.crashed = false)
    (hl : (w.st s).life = .alive) : Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  exact effect_finish_enabled I w s k hk hc hl

theorem enabled_finish_peer (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .peer) (hf : peerFinishable I.desc s = true)
    (hc : w.crashed = false) (hl : (w.st s).life = .alive) :
    Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  exact peer_finish_enabled I w s k hk hf hc hl

/-- Every configuration of a run takes a step, so none of them is crashed. -/
theorem run_uncrashed {I : Impl} {N : Nat} (ρ : Run I N) (j : Nat) : (ρ.cfg j).crashed = false :=
  (apply_step I (ρ.act j) (ρ.cfg j) (ρ.cfg (j + 1)) (ρ.valid j)).1

theorem not_stuck_effect {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_effect I (ρ.cfg j) s (hall j hj) (run_uncrashed ρ j) (hl j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  rw [hact] at happ
  exact finish_clears_effect I (ρ.cfg j) s (ρ.cfg (j + 1)) (apply_step I _ _ _ happ).2 (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer)
    (hf : peerFinishable I.desc s = true)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_peer I (ρ.cfg j) s (hall j hj) hf (run_uncrashed ρ j) (hl j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  rw [hact] at happ
  exact finish_clears_peer I (ρ.cfg j) s (ρ.cfg (j + 1)) (apply_step I _ _ _ happ).2 (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem run_enabled (I : Impl) (w : World) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hl : (w.st s).life = .alive) (hc : w.crashed = false) :
    Enabled I w (.exec s) := by
  simp [Enabled, apply, stepWorld, execHead, hp, hl, hc]

theorem resumeSender_run (a : Actor) (b : Bool) (dst : InstId) (k : Cont)
    (hp : a.phase = .run k) : (resumeSender a b dst).phase = .run k := by
  simp [resumeSender, hp]

theorem performReply_preserves_run (w : World) (sender s : InstId) (k k0 : Cont)
    (hp : (w.st s).phase = .run k0) (hs : s ≠ sender) :
    ((performReply w sender k).st s).phase = .run k0 := by
  unfold performReply
  cases hr : k.replyTo with
  | none => simp [hr, setActor_other, hs, hp]
  | some caller =>
    simp only [hr]
    by_cases hc : caller = s
    · simp [hc, hp, setActor_other, hs]
    · cases hph : (w.st caller).phase with
      | awaitReply dst ck =>
        by_cases hd : dst = sender
        · by_cases hm : (w.st sender).oweId = some (w.st caller).waitId
          · simp [hph, hd, hm, setActor_other, hs]
            rw [setActor_other _ caller s _ (Ne.symm hc)]
            exact hp
          · simp [hph, hd, hm, setActor_other, hs, hp]
        · simp [hph, hd, setActor_other, hs, hp]
      | idle => simp [hph, setActor_other, hs, hp]
      | run _ => simp [hph, setActor_other, hs, hp]
      | awaitEffect _ => simp [hph, setActor_other, hs, hp]
      | awaitPeer _ => simp [hph, setActor_other, hs, hp]
      | parked _ _ _ => simp [hph, setActor_other, hs, hp]
      | crashed => simp [hph, setActor_other, hs, hp]

theorem enqueue_keeps_other_run (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k k0 : Cont) (s : InstId)
    (hp : (w.st s).phase = .run k0) (hs : s ≠ sender) :
    ((enqueueOrPark w D sender dst msg isCall k).st s).phase = .run k0 := by
  unfold enqueueOrPark
  dsimp only
  cases hlife : (w.st dst).life
  · simp [hlife]
    split <;> simp [setActor_other, hs, hp]
  · split
    · rename_i hbad
      exact False.elim (hbad rfl)
    · split
      · rename_i hroom
        split
        · rename_i hsame
          have hse : sender = dst := by simpa using hsame
          by_cases hd : s = dst
          · exact (hs (hse.trans hd.symm).symm).elim
          · by_cases hc : isCall <;> simp [hc, hd, setActor_other, hs, hp]
        · rename_i hdiff
          by_cases hd : s = dst
          · subst hd
            cases hc : isCall
            · split
              · rename_i hbad
                cases hbad
              · rw [setActor_other _ sender s _ hs]
                simp [setActor_self, hp]
            · simp only [hc, ite_true]
              rw [setActor_other _ sender s _ hs]
              simp [setActor_self, hp]
          · by_cases hc : isCall <;> simp [hd, hc, setActor_other, hs, hp]
      · rename_i hfull
        split
        · rename_i hsame
          have hse : sender = dst := by simpa using hsame
          by_cases hd : s = dst
          · exact (hs (hse.trans hd.symm).symm).elim
          · simp [hd, setActor_other, hs, hp]
        · rename_i hdiff
          by_cases hd : s = dst
          · subst hd
            rw [setActor_other _ sender s _ hs]
            simp [setActor_self, hp]
          · simp [hd, setActor_other, hs, hp]
  · simp [hlife]
    split <;> simp [setActor_other, hs, hp]

/-- An actor that a roster crash leaves alive was not touched by it. -/
theorem crashWorld_alive_st (w : World) (i : InstId)
    (h : ((crashWorld w).st i).life = .alive) : (crashWorld w).st i = w.st i := by
  simp only [crashWorld] at h ⊢
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp only [hmem, ite_true, crashActor] at h ⊢
    by_cases hgo : ((w.st i).life == .alive) = true
    · simp [hgo] at h
    · simp [hgo]
  · simp [hmem]

/-- A fold of steps that never revive an actor does not revive it. -/
theorem foldl_life_prev {α : Type} (f : World → α → World) (s : InstId)
    (hf : ∀ w x, ((f w x).st s).life = .alive → (w.st s).life = .alive) :
    ∀ (xs : List α) (w : World), ((xs.foldl f w).st s).life = .alive → (w.st s).life = .alive := by
  intro xs
  induction xs with
  | nil => intro _ h; exact h
  | cons x xs ih =>
    intro w h
    exact hf w x (ih (f w x) h)

/-- A fold of steps that keep a surviving actor's running continuation keeps it too,
provided no step revives an actor. -/
theorem foldl_keeps_run {α : Type} (f : World → α → World) (s : InstId) (k : Cont)
    (hf : ∀ w x, ((f w x).st s).life = .alive → (w.st s).life = .alive)
    (hk : ∀ w x, (w.st s).phase = .run k → ((f w x).st s).life = .alive →
      ((f w x).st s).phase = .run k) :
    ∀ (xs : List α) (w : World), (w.st s).phase = .run k → ((xs.foldl f w).st s).life = .alive →
      ((xs.foldl f w).st s).phase = .run k := by
  intro xs
  induction xs with
  | nil => intro _ hp _; exact hp
  | cons x xs ih =>
    intro w hp h
    exact ih (f w x) (hk w x hp (foldl_life_prev f s hf xs (f w x) h)) h

theorem tryWake_prev (D : Description) (w : World) (dstId : InstId) (label : String) (writer i : InstId)
    (h : ((tryWake D w dstId label writer).st i).life = .alive) : (w.st i).life = .alive := by
  unfold tryWake offerPrio at h
  dsimp only at h
  split at h
  · exact h
  · split at h
    · exact crashWorld_prev w i h
    · by_cases hi : i = dstId
      · rw [hi] at h ⊢
        rw [setActor_self] at h
        exact h
      · rw [setActor_other _ _ _ _ hi] at h
        exact h

/-- A wake keeps a running continuation on every actor it leaves alive. A full
lane crashes the roster, and a crashed actor is not alive. -/
theorem tryWake_preserves_run (D : Description) (w : World) (dstId writer s : InstId) (label : String)
    (k : Cont) (hp : (w.st s).phase = .run k)
    (hfin : ((tryWake D w dstId label writer).st s).life = .alive) :
    ((tryWake D w dstId label writer).st s).phase = .run k := by
  unfold tryWake offerPrio at hfin ⊢
  dsimp only at hfin ⊢
  split
  · exact hp
  · rename_i hgo
    rw [ite_eq_right hgo] at hfin
    split
    · rename_i hfull
      rw [ite_eq_left hfull] at hfin
      rw [crashWorld_alive_st w s hfin]
      exact hp
    · by_cases hs : s = dstId
      · rw [hs] at hp ⊢
        rw [setActor_self]
        exact hp
      · rw [setActor_other _ _ _ _ hs]
        exact hp

theorem fold_tryWake_preserves_run (D : Description) (ids : List InstId) (w : World)
    (label : String) (writer s : InstId) (k : Cont) (hp : (w.st s).phase = .run k)
    (hfin : ((ids.foldl (fun w i => tryWake D w i label writer) w).st s).life = .alive) :
    ((ids.foldl (fun w i => tryWake D w i label writer) w).st s).phase = .run k :=
  foldl_keeps_run (fun w i => tryWake D w i label writer) s k
    (fun w i h => tryWake_prev D w i label writer s h)
    (fun w i hp h => tryWake_preserves_run D w i writer s label k hp h) ids w hp hfin

theorem wakeReaders_preserves_run (D : Description) (w : World) (dst label : String) (writer s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k)
    (hfin : ((wakeReaders D w dst label writer).st s).life = .alive) :
    ((wakeReaders D w dst label writer).st s).phase = .run k :=
  fold_tryWake_preserves_run D (readersOf w dst) w label writer s k hp hfin

theorem credit_preserves_run (w : World) (tmpl : String) (sender s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) :
    ((creditSender w tmpl sender).st s).phase = .run k := by
  unfold creditSender bumpToken
  by_cases hs : s = sender
  · subst hs
    simp [setActor_self]
    exact hp
  · simp [setActor_other, hs, hp]

theorem fold_credit_preserves_run (ms : List Msg) (w : World) (tmpl : String) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) :
    ((ms.foldl (fun w m => creditSender w tmpl m.sender) w).st s).phase = .run k := by
  induction ms generalizing w with
  | nil => simp [hp]
  | cons m ms ih =>
    simp only [List.foldl_cons]
    exact ih _ (credit_preserves_run w tmpl m.sender s k hp)

theorem fold_credit_parked_preserves_run (ps : List Parked) (w : World) (tmpl : String) (s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k) :
    ((ps.foldl (fun w p => creditSender w tmpl p.msg.sender) w).st s).phase = .run k := by
  induction ps generalizing w with
  | nil => simp [hp]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih _ (credit_preserves_run w tmpl p.msg.sender s k hp)

theorem release_preserves_run (w : World) (id : InstId) (ps : List Parked) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hs : s ≠ id) :
    ((releaseParked w id ps).st s).phase = .run k := by
  unfold releaseParked
  induction ps generalizing w with
  | nil => simp [hp]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _ hp
    · by_cases hps : s = p.sender
      · have hrun := resumeSender_run (w.st p.sender) false id k (by simpa [hps] using hp)
        simpa [hps, setActor_self] using ih _ (by simpa [hps, setActor_self] using hrun)
      · exact ih _ (by simp [setActor_other, hps, hp])

theorem readCells_preserves_run (D : Description) (w : World) (id s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) :
    ((readCells D w id).st s).phase = .run k := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp [hp]
  | cons l labs ih =>
    simp only [List.foldl_cons]
    exact ih _ hp

theorem failWaiter_preserves_run (w : World) (dead i s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) : ((failWaiter w dead i).st s).phase = .run k := by
  unfold failWaiter
  split
  · exact hp
  · by_cases hs : s = i
    · rw [hs] at hp ⊢
      cases hph : (w.st i).phase with
      | run _ => exact hp
      | parked _ _ _ => rw [hph] at hp; cases hp
      | awaitReply _ _ => rw [hph] at hp; cases hp
      | idle => rw [hph] at hp; cases hp
      | awaitEffect _ => rw [hph] at hp; cases hp
      | awaitPeer _ => rw [hph] at hp; cases hp
      | crashed => rw [hph] at hp; cases hp
    · cases hph : (w.st i).phase with
      | parked _ b _ =>
        cases b with
        | false =>
          simp [hph]
          split
          · simp [setActor, hs, hp]
          · exact hp
        | true => simp [hph, hp]
      | awaitReply _ _ => simp [hph, hp]
      | idle => simp [hph, hp]
      | run _ => simp [hph, hp]
      | awaitEffect _ => simp [hph, hp]
      | awaitPeer _ => simp [hph, hp]
      | crashed => simp [hph, hp]

theorem failWaiters_preserves_run (w : World) (dead s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) : ((failWaiters w dead).st s).phase = .run k := by
  unfold failWaiters
  suffices ∀ (ids : List InstId) (w : World), (w.st s).phase = .run k →
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .run k from
    this w.roster w hp
  intro ids
  induction ids with
  | nil =>
    intro w hp
    simpa using hp
  | cons i ids ih =>
    intro w hp
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (failWaiter_preserves_run w dead i s k hp)

theorem releaseOutbound_phase (w : World) (dead s : InstId) :
    ((releaseOutbound w dead).st s).phase = (w.st s).phase := by
  unfold releaseOutbound
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w host =>
        if host == dead then w
        else
          let dropped := (w.st host).parked.filter fun p => p.sender == dead
          if dropped.isEmpty then w
          else
            let w := setActor w host
              { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
            setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) w0).st s).phase =
        (w0.st s).phase from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro _; rfl
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    split
    · exact ih _
    · rename_i hnot
      split
      · exact ih _
      · refine (ih _).trans ?_
        have hne : host ≠ dead := by
          intro heq
          apply hnot
          simpa [beq_iff_eq] using heq
        by_cases hs : s = dead
        · simp only [setActor, addTokens, hs, ite_true]
          rw [ite_eq_right (Ne.symm hne)]
        · by_cases hh : s = host
          · simp only [setActor, addTokens, hh, ite_true]
            rw [ite_eq_right hne]
          · simp [setActor, hs, hh, addTokens]

theorem releaseWorld_preserves_run (D : Description) (w : World) (id s : InstId) (a : Actor)
    (k : Cont) (hs : s ≠ id) (hp : (w.st s).phase = .run k) :
    ((releaseWorld D w id a).st s).phase = .run k := by
  simp only [releaseWorld]
  refine release_preserves_run _ id a.parked s k ?_ hs
  rw [setActor_other _ id s _ hs, releaseOutbound_phase, (refundParked_phase_life _ _ _ s).1,
    (refundMsgs_phase_life _ _ _ s).1, cellsSt]
  exact hp

theorem shutdownActor_preserves_run (D : Description) (w : World) (id s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hfin : ((shutdownActor D w id).st s).life = .alive) :
    ((shutdownActor D w id).st s).phase = .run k := by
  unfold shutdownActor at hfin ⊢
  by_cases hlive : ((w.st id).life == .alive) = true
  · rw [ite_eq_left hlive] at hfin ⊢
    unfold sealActor at hfin ⊢
    let w1 := releaseWorld D w id (w.st id)
    have hw1 : w1 = releaseWorld D w id (w.st id) := rfl
    have hs : s ≠ id := by
      intro heq
      subst heq
      have hdead := releaseWorld_self_dead D w s (w.st s)
      have halive := enqueueTombstone_life D w1 s s (by simpa [hw1] using hfin)
      rw [hw1, hdead] at halive
      cases halive
    have hp1 : (w1.st s).phase = .run k := by
      simpa [hw1] using releaseWorld_preserves_run D w id s (w.st id) k hs hp
    unfold enqueueTombstone at hfin ⊢
    cases hpar : ((releaseWorld D w id (w.st id)).st id).parent with
    | none =>
      simpa [hpar, hw1] using hp1
    | some parent =>
      simp only [hpar] at hfin ⊢
      by_cases hplive : (((releaseWorld D w id (w.st id)).st parent).life != .alive) = true
      · rw [ite_eq_left hplive] at hfin ⊢
        simpa [hw1] using hp1
      · rw [ite_eq_right hplive] at hfin ⊢
        by_cases hlab : ((tombstoneMsg D ((releaseWorld D w id (w.st id)).st parent) id).label == "") = true
        · rw [ite_eq_left hlab] at hfin ⊢
          rw [crashWorld_alive_st (releaseWorld D w id (w.st id)) s hfin]
          simpa [hw1] using hp1
        · rw [ite_eq_right hlab] at hfin ⊢
          unfold offerPrio at hfin ⊢
          by_cases hfull :
              decide (prioLoad ((releaseWorld D w id (w.st id)).st parent).prio >=
                  capPrio D (releaseWorld D w id (w.st id)).N parent) = true
          · rw [ite_eq_left hfull] at hfin ⊢
            rw [crashWorld_alive_st (releaseWorld D w id (w.st id)) s hfin]
            simpa [hw1] using hp1
          · rw [ite_eq_right hfull] at hfin ⊢
            by_cases hsp : s = parent
            · subst hsp
              rw [setActor_self]
              simpa [hw1] using hp1
            · rw [setActor_other _ _ _ _ hsp]
              simpa [hw1] using hp1
  · rw [ite_eq_right hlive]
    exact hp

/-- Sealing a branch keeps the running continuation of every actor it leaves alive.
A sealed actor is dead, so the final-alive hypothesis excludes it. -/
theorem sealBranch_preserves_run (fuel : Nat) (D : Description) (s : InstId) (k : Cont) :
    ∀ (id : InstId) (w : World), (w.st s).phase = .run k →
      ((sealBranch fuel D w id).st s).life = .alive →
      ((sealBranch fuel D w id).st s).phase = .run k := by
  induction fuel with
  | zero =>
    intro id w hp _
    simpa [sealBranch] using hp
  | succ fuel ih =>
    intro id w hp hfin
    simp only [sealBranch] at hfin ⊢
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel D w0 child else w0
    have hprev : ∀ w0 child, ((step w0 child).st s).life = .alive → (w0.st s).life = .alive := by
      intro w0 child h0
      simp only [step] at h0
      split at h0
      · exact sealBranch_prev fuel D s child w0 h0
      · exact h0
    have hkeep : ∀ w0 child, (w0.st s).phase = .run k → ((step w0 child).st s).life = .alive →
        ((step w0 child).st s).phase = .run k := by
      intro w0 child hp0 h0
      simp only [step] at h0 ⊢
      split
      · rename_i hc
        rw [ite_eq_left hc] at h0
        exact ih child w0 hp0 h0
      · exact hp0
    let sealed := w.roster.foldl step w
    have hfold := foldl_keeps_run step s k hprev hkeep w.roster w hp
    change ((if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id) else sealed).st s).life = .alive at hfin
    change ((if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id) else sealed).st s).phase = .run k
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · rw [ite_eq_left hgo] at hfin ⊢
      by_cases hsid : s = id
      · rw [hsid, releaseWorld_self_dead] at hfin
        cases hfin
      · exact releaseWorld_preserves_run D sealed id s _ k hsid
          (hfold (releaseWorld_prev D sealed id (sealed.st id) s hfin))
    · rw [ite_eq_right hgo] at hfin ⊢
      exact hfold hfin

/-- Dropping descendants keeps the running continuation of every actor it leaves alive. -/
theorem dropDescendants_preserves_run (D : Description) (w : World) (id s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hfin : ((dropDescendants D w id).st s).life = .alive) :
    ((dropDescendants D w id).st s).phase = .run k := by
  unfold dropDescendants at hfin ⊢
  refine foldl_keeps_run (fun acc child =>
      if isChild acc id child then sealBranch w.roster.length D acc child else acc) s k ?_ ?_
    w.roster w hp hfin
  · intro w0 child h0
    split at h0
    · exact sealBranch_prev _ D s child w0 h0
    · exact h0
  · intro w0 child hp0 h0
    split
    · rename_i hc
      rw [ite_eq_left hc] at h0
      exact sealBranch_preserves_run _ D s k child w0 hp0 h0
    · exact hp0

/-- A parent's abort keeps the running continuation of every actor it leaves alive. -/
theorem abortChildren_preserves_run (D : Description) (w : World) (parent s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hfin : ((abortChildren D w parent).st s).life = .alive) :
    ((abortChildren D w parent).st s).phase = .run k := by
  unfold abortChildren at hfin ⊢
  refine foldl_keeps_run (fun w child =>
      if isChild w parent child && (w.st child).life == .alive then
        shutdownActor D (dropDescendants D w child) child
      else w) s k ?_ ?_ w.roster w hp hfin
  · intro w0 child h0
    split at h0
    · exact dropDescendants_prev D w0 child s (shutdownActor_prev D _ child s h0)
    · exact h0
  · intro w0 child hp0 h0
    split
    · rename_i hc
      rw [ite_eq_left hc] at h0
      exact shutdownActor_preserves_run D _ child s k
        (dropDescendants_preserves_run D w0 child s k hp0 (shutdownActor_prev D _ child s h0)) h0
    · exact hp0

/-- A tombstone enqueue that does not crash the roster leaves every phase alone. -/
theorem enqueueTombstone_phase (D : Description) (w : World) (child s : InstId)
    (hc : (enqueueTombstone D w child).crashed = false) :
    ((enqueueTombstone D w child).st s).phase = (w.st s).phase := by
  unfold enqueueTombstone at hc ⊢
  cases hpar : (w.st child).parent with
  | none => simp
  | some parent =>
    simp only [hpar] at hc ⊢
    by_cases hlive : ((w.st parent).life != .alive) = true
    · rw [ite_eq_left hlive]
    · rw [ite_eq_right hlive] at hc ⊢
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · rw [ite_eq_left hlab] at hc
        simp [crashWorld] at hc
      · rw [ite_eq_right hlab] at hc ⊢
        unfold offerPrio at hc ⊢
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · rw [ite_eq_left hfull] at hc
          simp [crashWorld] at hc
        · rw [ite_eq_right hfull]
          by_cases hi : s = parent
          · rw [hi, setActor_self]
          · rw [setActor_other _ _ _ _ hi]

/-- A stage that terminates leaves every surviving actor on the continuation it
was running. Its descendants are sealed and the stage itself is shutting down,
so neither is alive afterwards. -/
theorem terminateStage_preserves_run (D : Description) (w : World) (id s : InstId) (a : Actor)
    (k : Cont) (_hs : s ≠ id) (hp : (w.st s).phase = .run k)
    (hfin : ((terminateStage D w id a).st s).life = .alive) :
    ((terminateStage D w id a).st s).phase = .run k := by
  simp only [terminateStage] at hfin ⊢
  exact shutdownActor_preserves_run D _ id s k
    (dropDescendants_preserves_run D w id s k hp (shutdownActor_prev D _ id s hfin)) hfin

theorem nat_foldl_ge {α : Type} (f : Nat → α → Nat) (hf : ∀ acc x, acc ≤ f acc x) :
    ∀ (xs : List α) (acc : Nat), acc ≤ xs.foldl f acc := by
  intro xs
  induction xs with
  | nil => intro acc; exact Nat.le_refl acc
  | cons x xs ih =>
    intro acc
    exact Nat.le_trans (hf acc x) (ih (f acc x))

theorem nat_foldl_gt_of_mem {α : Type} (f : Nat → α → Nat) (hf : ∀ acc x, acc ≤ f acc x)
    (y : α) (g : Nat) (hy : ∀ acc, g < f acc y) :
    ∀ (xs : List α) (acc : Nat), y ∈ xs → g < xs.foldl f acc := by
  intro xs
  induction xs with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro acc h
    rcases List.mem_cons.mp h with hx | hx
    · rw [← hx]
      exact Nat.lt_of_lt_of_le (hy acc) (nat_foldl_ge f hf xs (f acc y))
    · exact ih (f acc x) hx

/-- A generation already on the roster is below `maxGen`, so a spawn does not reuse it. -/
theorem maxGen_fresh (w : World) (name : String) (key g : Nat)
    (h : InstId.peer name key g ∈ w.roster) : g < maxGen w name key := by
  simpa [maxGen] using maxGen_gt w.roster name key g h

/-- A child spawn leaves every actor already on the roster as it was. -/
theorem spawnChild_other_st (I : Impl) (w w' : World) (parent : InstId) (child : String) (s : InstId)
    (h : spawnChild I w parent child = some w') (hmem : s ∈ w.roster) : w'.st s = w.st s := by
  have hfresh : ∀ k, s ≠ InstId.peer child k (maxGen w child k) := by
    intro k hs
    rw [hs] at hmem
    exact Nat.lt_irrefl _ (maxGen_fresh w child k _ hmem)
  unfold spawnChild at h
  split at h
  · simp at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h
            simp only [admitBorn, cellsSt]
            rw [setActor_other _ _ _ _ (hfresh _)]
          · cases h
            rfl
        · simp at h
      · split at h
        · split at h
          · cases h
            rfl
          · cases h
            simp only [admitBorn, cellsSt]
            rw [setActor_other _ _ _ _ (hfresh _)]
        · simp at h
    · split at h
      · cases h
        rfl
      · simp at h

/-- Another actor keeps a running continuation through this step when the step
leaves that actor alive. Descendants of a terminating stage, aborted children,
and a crashed roster do not survive, so the survivor hypothesis is what makes
the phase claim true. Roster membership rules out the fresh id of a spawn. -/
theorem execRun_preserves_other_run (I : Impl) (w : World) (id : InstId) (a : Actor) (k k0 : Cont)
    (s : InstId) (hs : s ≠ id) (hp : (w.st s).phase = .run k0)
    (_ha : (w.st id).phase = .run k) (halive : ((execRun I w id a k).st s).life = .alive)
    (hmem : s ∈ w.roster) :
    ((execRun I w id a k).st s).phase = .run k0 := by
  by_cases hliveB : (a.life == .alive) = true
  · cases hk : k.rest with
    | nil =>
      simp [execRun, hliveB, hk, setActor, hs, hp]
    | cons e es =>
      cases e with
      | send dst label hint =>
        simp only [execRun, hliveB, hk, ite_true]
        cases hr : route w I.desc id dst hint with
        | none => simp [setActor, hs, hp]
        | some dstId => exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
      | trySend dst label hint onFull onGone =>
        simp only [execRun, hliveB, hk, ite_true]
        cases hr : route w I.desc id dst hint with
        | none => simp [setActor, hs, hp]
        | some dstId =>
          dsimp only
          split
          · exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
          · split <;> simp [setActor, hs, hp]
      | call dst label hint onNotAdmitted onTimedOut =>
        simp only [execRun, hliveB, hk, ite_true]
        cases hr : resolveId I.desc w id dst hint with
        | none => simp [setActor, hs, hp]
        | some dstId => exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
      | reply =>
        simp only [execRun, hliveB, hk, ite_true]
        exact performReply_preserves_run w id s k k0 hp hs
      | selfSchedule label =>
        simp only [execRun, hliveB, hk, ite_true] at halive ⊢
        by_cases hq : (a.prio.any fun p => p.label == label) = true
        · rw [ite_eq_left hq]
          simp [setActor, hs, hp]
        · rw [ite_eq_right hq] at halive ⊢
          by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
          · rw [ite_eq_left hroom]
            simp [setActor, hs, hp]
          · rw [ite_eq_right hroom] at halive ⊢
            rw [crashWorld_alive_st w s halive]
            exact hp
      | cell dst label value =>
        simp only [execRun, hliveB, hk, ite_true] at halive ⊢
        by_cases hd : (w.cell dst label).dirty = true
        · rw [ite_eq_left hd]
          simp [setActor, setCell, hs, hp]
        · rw [ite_eq_right hd] at halive ⊢
          exact wakeReaders_preserves_run I.desc _ dst label id s k0
            (by simp [setActor, setCell, hs, hp]) halive
      | internal =>
        simp [execRun, hliveB, hk, setActor, hs, hp]
      | peer onTimeout =>
        simp [execRun, hliveB, hk, setActor, hs, hp]
      | abort =>
        simp only [execRun, hliveB, hk, ite_true] at halive ⊢
        rw [setActor_other _ _ _ _ hs] at halive ⊢
        exact abortChildren_preserves_run I.desc w id s k0 hp halive
      | spawn child =>
        simp only [execRun, hliveB, hk, ite_true] at halive ⊢
        cases hsp : spawnChild I w id child with
        | none =>
          simp only [hsp] at halive ⊢
          rw [crashWorld_alive_st w s halive]
          exact hp
        | some w' =>
          simp only
          rw [setActor_other _ _ _ _ hs, spawnChild_other_st I w w' id child s hsp hmem]
          exact hp
      | terminate =>
        have hprop : a.life = .alive := by simpa [beq_iff_eq] using hliveB
        have hstep := exec_term_step I w id a k hprop ⟨es, hk⟩
        generalize hw : execRun I w id a k = wR at hstep halive ⊢
        cases hstep with
        | fall =>
          rw [crashWorld_alive_st w s halive]
          exact hp
        | crash _ _ _ =>
          rw [crashWorld_alive_st w s halive]
          exact hp
        | lone _ _ _ _ _ _ _ =>
          exact shutdownActor_preserves_run I.desc w id s k0 hp halive
        | tree _ _ _ _ =>
          exact terminateStage_preserves_run I.desc w id s a k0 hs hp halive
        | cascade _ _ _ _ _ _ _ =>
          exact terminateStage_preserves_run I.desc w id s a k0 hs hp halive
  · simp [execRun, hliveB, hp]

end Deadlock
