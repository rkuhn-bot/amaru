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
  simp [finishWait, hk] at h
  rcases h with ⟨_, hw⟩
  rw [← hw]
  simpa [setActor_self] using proceed_not_effect (w.st s) k

theorem finish_clears_peer (I : Impl) (w : World) (s : InstId) (w' : World)
    (h : finishWait I w s = some w') (hp : waitKind (w.st s) = some .peer) :
    waitKind (w'.st s) ≠ some .peer := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  simp [finishWait, hk] at h
  rcases h with ⟨_, hw⟩
  rw [← hw]
  simpa [setActor_self] using proceed_not_peer (w.st s) k

theorem enabled_finish_effect (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .effect) (hok : I.env.effectDone w s = true) :
    Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  simp [Enabled, apply, finishWait, hk, hok]

theorem enabled_finish_peer (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .peer) (hok : I.env.peerDone w s = true) :
    Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  simp [Enabled, apply, finishWait, hk, hok]

theorem not_stuck_effect {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect)
    (hok : ∀ j, i ≤ j → I.env.effectDone (ρ.cfg j) s = true) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_effect I (ρ.cfg j) s (hall j hj) (hok j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_effect I (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer)
    (hok : ∀ j, i ≤ j → I.env.peerDone (ρ.cfg j) s = true) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_peer I (ρ.cfg j) s (hall j hj) (hok j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_peer I (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem run_enabled (I : Impl) (w : World) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hl : (w.st s).life = .alive) : Enabled I w (.exec s) := by
  simp [Enabled, apply, execHead, hp, hl]

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
        · simp only [hph, hd, if_true]
          rw [setActor_other _ sender s _ hs, setActor_other _ caller s _ (Ne.symm hc)]
          exact hp
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
  · simp [hlife, setActor_other, hs, hp]
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
  · simp [hlife, setActor_other, hs, hp]

theorem tryWake_preserves_run (D : Description) (w : World) (dstId writer s : InstId) (label : String)
    (k : Cont) (hp : (w.st s).phase = .run k) :
    ((tryWake D w dstId label writer).st s).phase = .run k := by
  unfold tryWake
  dsimp only
  split
  · by_cases hs : s = dstId
    · subst hs
      simp [setActor_self]
      exact hp
    · simp [setActor_other, hs, hp]
  · simp [hp]

theorem fold_tryWake_preserves_run (D : Description) (ids : List InstId) (w : World)
    (label : String) (writer s : InstId) (k : Cont) (hp : (w.st s).phase = .run k) :
    ((ids.foldl (fun w i => tryWake D w i label writer) w).st s).phase = .run k := by
  induction ids generalizing w with
  | nil => simp [hp]
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (tryWake D w i label writer) (tryWake_preserves_run D w i writer s label k hp)

theorem wakeReaders_preserves_run (D : Description) (w : World) (dst label : String) (writer s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k) :
    ((wakeReaders D w dst label writer).st s).phase = .run k := by
  simpa [wakeReaders] using fold_tryWake_preserves_run D (readersOf w dst) w label writer s k hp

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

theorem execRun_preserves_other_run (I : Impl) (w : World) (id : InstId) (a : Actor) (k k0 : Cont)
    (s : InstId) (hs : s ≠ id) (hp : (w.st s).phase = .run k0)
    (_ha : (w.st id).phase = .run k) :
    ((execRun I w id a k).st s).phase = .run k0 := by
  cases hk : k.rest with
  | nil =>
    simp [execRun, hk, setActor_other, hs, hp]
  | cons eff rest =>
    simp [execRun, hk]
    cases eff with
    | send dst label hint =>
      simp
      split
      · simp [setActor_other, hs, hp]
      · exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
    | trySend dst label hint =>
      simp
      split
      · simp [setActor_other, hs, hp]
      · rename_i dstId _
        split
        · by_cases hc : s = dstId
          · by_cases hi : dstId = id
            · exact (hs (hc.trans hi)).elim
            · subst hc
              rw [setActor_other _ id s _ hi]
              simp [setActor_self, setActor_other, hi, hp]
          · rw [setActor_other _ id s _ hs]
            rw [setActor_other _ dstId s _ hc]
            rw [setActor_other _ id s _ hs]
            exact hp
        · simp [setActor_other, hs, hp]
    | call dst label hint =>
      simp
      split
      · simp [setActor_other, hs, hp]
      · exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
    | reply =>
      simpa using performReply_preserves_run w id s k k0 hp hs
    | selfSchedule label =>
      simp
      split
      · simp [setActor_other, hs, hp]
      · split
        · simp [setActor_other, hs, hp]
        · simp [setActor_other, hs, hp]
    | cell dst label value =>
      simp
      split
      · simp [setCell, setActor_other, hs, hp]
      · exact wakeReaders_preserves_run I.desc _ dst label id s k0
          (by simp [setCell, setActor_other, hs, hp])
    | internal =>
      simp [setActor_other, hs, hp]
    | peer =>
      simp [setActor_other, hs, hp]
    | terminate =>
      simp
      split
      · split
        · exact release_preserves_run _ id a.parked s k0 (by
            rw [setActor_other _ id s _ hs]
            exact fold_credit_parked_preserves_run a.parked _ (tname id) s k0
              (fold_credit_preserves_run a.box _ (tname id) s k0
                (readCells_preserves_run I.desc w id s k0 hp))) hs
        · simp [hp]
      · simp [hp]

end Deadlock
