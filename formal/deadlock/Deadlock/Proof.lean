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
  cases h
  simpa [setActor_self] using proceed_not_effect (w.st s) k

theorem finish_clears_peer (I : Impl) (w : World) (s : InstId) (w' : World)
    (h : finishWait I w s = some w') (hp : waitKind (w.st s) = some .peer) :
    waitKind (w'.st s) ≠ some .peer := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  simp [finishWait, hk] at h
  rcases h with ⟨_, hw⟩
  cases hw
  simpa [setActor_self] using proceed_not_peer (w.st s) k

theorem effect_finish_enabled (I : Impl) (w : World) (id : InstId) (k : Cont)
    (h : (w.st id).phase = .awaitEffect k) : Enabled I w (.finish id) := by
  simp [Enabled, apply, finishWait, h]

theorem peer_finish_enabled (I : Impl) (w : World) (id : InstId) (k : Cont)
    (h : (w.st id).phase = .awaitPeer k) (hf : peerFinishable I.desc id = true) :
    Enabled I w (.finish id) := by
  simp [Enabled, apply, finishWait, h, hf]

theorem enabled_finish_effect (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .effect) : Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_effect_phase (w.st s) hp
  exact effect_finish_enabled I w s k hk

theorem enabled_finish_peer (I : Impl) (w : World) (s : InstId)
    (hp : waitKind (w.st s) = some .peer) (hf : peerFinishable I.desc s = true) :
    Enabled I w (.finish s) := by
  obtain ⟨k, hk⟩ := wait_peer_phase (w.st s) hp
  exact peer_finish_enabled I w s k hk hf

theorem not_stuck_effect {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .effect) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .effect := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_effect I (ρ.cfg j) s (hall j hj)
  obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
  have happ := ρ.valid j
  simp [hact] at happ
  exact finish_clears_effect I (ρ.cfg j) s (ρ.cfg (j + 1)) happ (hall j hj)
    (hall (j + 1) (Nat.le_trans hj (Nat.le_succ j)))

theorem not_stuck_peer {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (s : InstId) (i : Nat)
    (h : Stuck ρ s i) (hp : waitKind ((ρ.cfg i).st s) = some .peer)
    (hf : peerFinishable I.desc s = true) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some .peer := by
    intro j hj
    exact ((h.2 j hj).1).symm.trans hp
  have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) :=
    fun j hj => enabled_finish_peer I (ρ.cfg j) s (hall j hj) hf
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
  · simp [hlife]
    split <;> simp [setActor_other, hs, hp]

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

theorem abortActor_preserves_run (D : Description) (w : World) (id s : InstId) (a : Actor)
    (k : Cont) (hs : s ≠ id) (hp : (w.st s).phase = .run k) :
    ((abortActor D w id a).st s).phase = .run k := by
  have hrel : ((releaseWorld D w id a).st s).phase = .run k := by
    simp only [releaseWorld]
    exact release_preserves_run _ id a.parked s k (by
      rw [setActor_other _ id s _ hs]
      exact fold_credit_parked_preserves_run a.parked _ (tname id) s k
        (fold_credit_preserves_run a.box _ (tname id) s k
          (readCells_preserves_run D w id s k hp))) hs
  have hfail : ((failWaiters (releaseWorld D w id a) id).st s).phase = .run k :=
    failWaiters_preserves_run _ id s k hrel
  simpa [abortActor] using (admitDead_phase (failWaiters (releaseWorld D w id a) id) id s).1.trans hfail

theorem enqueueTombstone_phase (D : Description) (w : World) (child s : InstId) :
    ((enqueueTombstone D w child).st s).phase = (w.st s).phase := by
  cases hsup : supervisorOf D child with
  | none => simp [enqueueTombstone, hsup]
  | some parent =>
    simp [enqueueTombstone, hsup]
    split
    · by_cases h : s = parent
      · simp [setActor, h]
      · simp [setActor, h]
    · rfl

theorem abortActor_self_dead (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((abortActor D w id a).st id).life = .dead := by
  have hrel := releaseWorld_self_dead D w id a
  have hfail := (failWaiters_life (releaseWorld D w id a) id id).trans hrel
  simpa [abortActor] using
    (admitDead_phase (failWaiters (releaseWorld D w id a) id) id id).2.trans hfail

theorem releaseWorld_other_life (D : Description) (w : World) (id s : InstId) (a : Actor)
    (hs : s ≠ id) : ((releaseWorld D w id a).st s).life = (w.st s).life := by
  let wCells := readCells D w id
  let wMsgs := refundMsgs wCells (tname id) a.box
  let wPark := refundParked wMsgs (tname id) a.parked
  let dead : Actor :=
    { wPark.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1 : (wCells.st s).life = (w.st s).life :=
    congrArg (fun act => act.life) (cellsSt D w id s)
  have h2 : (wMsgs.st s).life = (wCells.st s).life :=
    (refundMsgs_rest wCells (tname id) a.box s).2.1
  have h3 : (wPark.st s).life = (wMsgs.st s).life :=
    (refundParked_rest wMsgs (tname id) a.parked s).2.1
  have h4 : ((setActor wPark id dead).st s).life = (wPark.st s).life := by
    simp [setActor, dead, hs]
  have h5 : ((releaseParked (setActor wPark id dead) id a.parked).st s).life =
      ((setActor wPark id dead).st s).life :=
    releaseParked_life (setActor wPark id dead) id a.parked s
  have heq : releaseWorld D w id a = releaseParked (setActor wPark id dead) id a.parked := by
    simp [releaseWorld, wCells, wMsgs, wPark, dead]
  simpa [heq] using h5.trans (h4.trans (h3.trans (h2.trans h1)))

theorem abortActor_life_prev (D : Description) (w : World) (id s : InstId) (a : Actor)
    (h : ((abortActor D w id a).st s).life = .alive) : (w.st s).life = .alive := by
  have hfw : ((abortActor D w id a).st s).life = ((releaseWorld D w id a).st s).life := by
    have hfail := failWaiters_life (releaseWorld D w id a) id s
    simpa [abortActor] using
      (admitDead_phase (failWaiters (releaseWorld D w id a) id) id s).2.trans hfail
  rw [hfw] at h
  by_cases hs : s = id
  · rw [hs] at h
    have hdead := releaseWorld_self_dead D w id a
    rw [hdead] at h
    cases h
  · exact (releaseWorld_other_life D w id s a hs).symm.trans h

theorem enqueueTombstone_life (D : Description) (w : World) (child s : InstId) :
    ((enqueueTombstone D w child).st s).life = (w.st s).life := by
  cases hsup : supervisorOf D child with
  | none => simp [enqueueTombstone, hsup]
  | some parent =>
    simp [enqueueTombstone, hsup]
    split
    · by_cases h : s = parent
      · simp [setActor, h]
      · simp [setActor, h]
    · rfl

/-- A descendant fold does not bring an actor to life. -/
theorem abortDesc_life_prev (fuel : Nat) (D : Description) (w : World) (parent s : InstId)
    (h : ((abortDesc fuel D w parent).st s).life = .alive) : (w.st s).life = .alive := by
  induction fuel generalizing w parent with
  | zero => simpa [abortDesc] using h
  | succ fuel ih =>
    simp only [abortDesc] at h
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st s).life = .alive → (w0.st s).life = .alive := by
      intro ids
      induction ids with
      | nil =>
        intro _ h0
        exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = true
        · simp only [hcond, ite_true] at h0
          let wDesc := abortDesc fuel D w0 child
          let wAct := abortActor D wDesc child (wDesc.st child)
          have hActAlive : (wAct.st s).life = .alive := ihids wAct h0
          have hDescAlive := abortActor_life_prev D wDesc child s (wDesc.st child) hActAlive
          exact ih w0 child hDescAlive
        · have hf : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive && childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf] at h0
          exact ihids w0 h0
    exact hfold w.roster w h

/-- A survivor of a descendant abort keeps a running continuation. An actor the
fold aborts is dead, so the final-alive hypothesis excludes it. -/
theorem abortDesc_preserves_run (fuel : Nat) (D : Description) (w : World) (parent s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k)
    (hfin : ((abortDesc fuel D w parent).st s).life = .alive) :
    ((abortDesc fuel D w parent).st s).phase = .run k := by
  induction fuel generalizing w parent with
  | zero => simpa [abortDesc] using hp
  | succ fuel ihFuel =>
    simp only [abortDesc] at hfin ⊢
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w
    have hfoldLife : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st s).life = .alive → (w0.st s).life = .alive := by
      intro ids
      induction ids with
      | nil =>
        intro _ h0
        exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = true
        · simp only [hcond, ite_true] at h0
          let wDesc := abortDesc fuel D w0 child
          let wAct := abortActor D wDesc child (wDesc.st child)
          have hActAlive : (wAct.st s).life = .alive := ihids wAct h0
          have hDescAlive := abortActor_life_prev D wDesc child s (wDesc.st child) hActAlive
          exact abortDesc_life_prev fuel D w0 child s hDescAlive
        · have hf : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive && childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf] at h0
          exact ihids w0 h0
    have hfold : ∀ (ids : List InstId) (w0 : World),
        (w0.st s).phase = .run k →
        ((ids.foldl step w0).st s).life = .alive →
        ((ids.foldl step w0).st s).phase = .run k := by
      intro ids
      induction ids with
      | nil =>
        intro _ hp0 _
        exact hp0
      | cons child ids ihIds =>
        intro w0 hp0 hlive
        simp only [List.foldl_cons, step] at hlive ⊢
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = true
        · simp only [hcond, ite_true] at hlive ⊢
          let wDesc := abortDesc fuel D w0 child
          let wAct := abortActor D wDesc child (wDesc.st child)
          have hActAlive : (wAct.st s).life = .alive := hfoldLife ids wAct hlive
          by_cases hvictim : s = child
          · have hdead : (wAct.st child).life = .dead := by
              simpa [wAct] using abortActor_self_dead D wDesc child (wDesc.st child)
            rw [hvictim] at hActAlive
            rw [hdead] at hActAlive
            cases hActAlive
          · have hDescAlive : (wDesc.st s).life = .alive :=
              (abortActor_other_life D wDesc child s (wDesc.st child) hvictim).symm.trans hActAlive
            have hpDesc := ihFuel w0 child hp0 hDescAlive
            have hpAct :=
              abortActor_preserves_run D wDesc child s (wDesc.st child) k hvictim hpDesc
            exact ihIds wAct hpAct hlive
        · have hf : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive && childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf] at hlive ⊢
          exact ihIds w0 hp0 hlive
    exact hfold w.roster w hp hfin

/-- A stage that dies leaves a surviving actor on the continuation it was running. -/
theorem terminateStage_preserves_run (D : Description) (w : World) (id s : InstId) (a : Actor)
    (k : Cont) (hs : s ≠ id) (hp : (w.st s).phase = .run k)
    (hfin : ((terminateStage D w id a).st s).life = .alive) :
    ((terminateStage D w id a).st s).phase = .run k := by
  let wDesc := abortDesc w.roster.length D w id
  let wAct := abortActor D wDesc id (wDesc.st id)
  have hActAlive : (wAct.st s).life = .alive := by
    have hfin' : ((enqueueTombstone D wAct id).st s).life = .alive := by
      simpa [terminateStage, wDesc, wAct] using hfin
    exact (enqueueTombstone_life D wAct id s).symm.trans hfin'
  have hDescAlive : (wDesc.st s).life = .alive :=
    (abortActor_other_life D wDesc id s (wDesc.st id) hs).symm.trans hActAlive
  have hpAct := abortActor_preserves_run D wDesc id s (wDesc.st id) k hs
    (abortDesc_preserves_run w.roster.length D w id s k hp hDescAlive)
  simpa [terminateStage, wDesc, wAct] using (enqueueTombstone_phase D wAct id s).trans hpAct

/-- Another actor keeps a running continuation through this step when the step
leaves that actor alive. Descendants of a terminating stage do not survive, so
the survivor hypothesis is what makes the phase claim true. -/
theorem execRun_preserves_other_run (I : Impl) (w : World) (id : InstId) (a : Actor) (k k0 : Cont)
    (s : InstId) (hs : s ≠ id) (hp : (w.st s).phase = .run k0)
    (_ha : (w.st id).phase = .run k) (halive : ((execRun I w id a k).st s).life = .alive) :
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
        · exact enqueue_keeps_other_run _ _ _ _ _ _ _ _ _ hp hs
        · simp [setActor_other, hs, hp]
    | call dst label hint =>
      simp
      split
      · simp [noteStale, setActor_other, hs, hp]
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
      cases ht : templateOf I.desc (tname id) with
      | none => simp [ht, hp]
      | some t =>
        simp only [ht]
        split
        · next hgo =>
          by_cases hsub : t.subtree = ""
          · simp [hsub]
            have hpk : hasParkedCall a.parked = false := by
              rcases hgo.2 with hne | hpk
              · exact absurd hsub hne
              · exact hpk
            by_cases hch : hasChild I.desc w id = true
            · simp [hch]
              exact terminateStage_preserves_run I.desc w id s a k0 hs hp (by
                simpa [execRun, hk, ht, hgo, hsub, hch, hpk] using halive)
            · simp [hch]
              exact release_preserves_run _ id a.parked s k0 (by
                rw [setActor_other _ id s _ hs]
                exact fold_credit_parked_preserves_run a.parked _ (tname id) s k0
                  (fold_credit_preserves_run a.box _ (tname id) s k0
                    (readCells_preserves_run I.desc w id s k0 hp))) hs
          · simp [hsub]
            exact terminateStage_preserves_run I.desc w id s a k0 hs hp (by
              simpa [execRun, hk, ht, hgo, hsub] using halive)
        · simp [hp]

end Deadlock
