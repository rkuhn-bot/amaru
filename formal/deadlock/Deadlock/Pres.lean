import Deadlock.RunInv

set_option autoImplicit false

namespace Deadlock

private theorem foldl_read_roster (D : Description) (ids : List InstId) (w : World) :
    (ids.foldl (fun w id => readCells D w id) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.foldl_cons]
    rw [ih, cellsRoster]

private theorem initRoster (I : Impl) (N : Nat) : (initWorld I N).roster = coreRoster I.desc := by
  unfold initWorld
  simpa using foldl_read_roster I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

theorem foldl_read_st (D : Description) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun w id => readCells D w id) w).st i) = w.st i := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    rw [List.foldl_cons]
    simpa [readCells_st] using ih (readCells D w id)

theorem core_mem (xs : List Template) (t : Template) (ht : t ∈ xs)
    (hm : (t.multiplicity == .one) = true) :
    InstId.core t.name ∈
      xs.filterMap fun u => if u.multiplicity == .one then some (InstId.core u.name) else none := by
  induction xs with
  | nil => cases ht
  | cons u us ih =>
    rw [List.filterMap_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · simp only [hm, ite_true]
      exact List.Mem.head _
    · by_cases hb : (u.multiplicity == .one) = true
      · simp only [hb, ite_true]
        exact List.Mem.tail _ (ih ht)
      · have hf : (u.multiplicity == .one) = false := by
          cases hbb : u.multiplicity == .one <;> simp_all
        simp only [hf, ite_false]
        exact ih ht

theorem find_mem (xs : List Template) (r : String) (t : Template)
    (h : xs.findSome? (fun u => if u.name == r then some u else none) = some t) : t ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons u us ih =>
    rw [List.findSome?_cons] at h
    by_cases hn : (u.name == r) = true
    · simp only [hn, ite_true] at h
      cases h
      exact List.Mem.head _
    · have hf : (u.name == r) = false := by
        cases hbb : u.name == r <;> simp_all
      simp only [hf, ite_false] at h
      exact List.Mem.tail _ (ih h)

theorem template_mem (D : Description) (r : String) (t : Template)
    (ht : templateOf D r = some t) : t ∈ D.templates := by
  simpa [templateOf] using find_mem D.templates r t ht

theorem one_beq (t : Template) (h : t.multiplicity = .one) : (t.multiplicity == .one) = true := by
  rw [h]
  decide

theorem init_base_st (I : Impl) (N : Nat) (id : InstId) :
    (initWorld I N).st id =
      if (coreRoster I.desc).contains id then initActor I.desc id else absentActor := by
  unfold initWorld
  simpa using foldl_read_st I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } id

theorem init_phase (I : Impl) (N : Nat) (id : InstId) : ((initWorld I N).st id).phase = .idle := by
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem sem_idle (I : Impl) (N : Nat) :
    (∀ id, contTy ((initWorld I N).st id)) ∧
      (∀ id, programOk I.desc id ((initWorld I N).st id)) ∧
      (∀ id, waitEdge I.desc id ((initWorld I N).st id)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro id
    simp [contTy, init_phase]
  · intro id
    simp [programOk, init_phase]
  · intro id
    simp [waitEdge, init_phase]

theorem tuples_eq (D : Description) (roles : List String) (w : World)
    (h : ∀ r ∈ roles, ∃ t, templateOf D r = some t ∧ (w.st (.core r)).typestate = t.initial) :
    (roles.map fun r => ({ role := r, state := (w.st (.core r)).typestate } : RoleState)) =
      roles.filterMap fun r =>
        match templateOf D r with
        | some t => some { role := r, state := t.initial }
        | none => none := by
  induction roles with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨t, ht, hs⟩ := h r (List.Mem.head _)
    rw [List.map_cons, List.filterMap_cons, ht]
    simp [hs]
    exact ih fun x hx => h x (List.Mem.tail _ hx)

theorem core_ready (D : Description) (g : CompatGroup) (r : String)
    (hw : groupWellformed D g = []) (hr : r ∈ g.roles) :
    ∃ t, templateOf D r = some t ∧ (t.multiplicity == .one) = true ∧ t.terminable = false ∧
      InstId.core r ∈ coreRoster D ∧ t.name = r := by
  obtain ⟨t, ht, hone, hterm, hn⟩ := role_static D g r hw hr
  refine ⟨t, ht, one_beq t hone, hterm, ?_, hn⟩
  simpa [coreRoster, hn] using core_mem D.templates t (template_mem D r t ht) (one_beq t hone)

theorem semInv_init (I : Impl) (N : Nat) (hL : LocalOk I) : SemInv I (initWorld I N) := by
  obtain ⟨hcont, hprog, hwait⟩ := sem_idle I N
  have hempty := compat_empty_of_local I hL
  cases hc : I.desc.compatibility with
  | explicit _ =>
    simp [compatFails, hc] at hempty
  | all =>
    refine ⟨?_, ?_, hcont, hprog, hwait, ?_, ?_⟩
    · intro g hg
      simp [compatGroups, hc] at hg
    · intro g hg
      simp [compatGroups, hc] at hg
    · intro id _
      exact init_phase I N id
    · intro id hlive
      rw [initRoster]
      by_cases hmem : (coreRoster I.desc).contains id = true
      · exact List.contains_iff_mem.mp hmem
      · rw [init_base_st] at hlive
        split at hlive
        · rename_i hmem'
          exact False.elim (hmem hmem')
        · simp [absentActor] at hlive
  | groups gs =>
    refine ⟨?_, ?_, hcont, hprog, hwait, ?_, ?_⟩
    · intro g hg _hlive
      have hw := (compat_group_closed I.desc g hempty hg).1
      have htup : roleTuple (initWorld I N) g = initialTuple I.desc g := by
        unfold roleTuple initialTuple
        apply tuples_eq
        intro r hr
        obtain ⟨t, ht, _, _, hmem, _⟩ := core_ready I.desc g r hw hr
        refine ⟨t, ht, ?_⟩
        rw [init_base_st]
        simp [hmem, initActor, ht, withTokens, tname]
      rw [htup]
      exact init_tuple_mem I.desc g hempty hg
    · intro g hg r hr
      have hw := (compat_group_closed I.desc g hempty hg).1
      obtain ⟨t, ht, _, _, hmem, _⟩ := core_ready I.desc g r hw hr
      rw [init_base_st]
      simp [hmem, initActor, ht, withTokens, tname]
    · intro id _
      exact init_phase I N id
    · intro id hlive
      rw [initRoster]
      by_cases hmem : (coreRoster I.desc).contains id = true
      · exact List.contains_iff_mem.mp hmem
      · rw [init_base_st] at hlive
        split at hlive
        · rename_i hmem'
          exact False.elim (hmem hmem')
        · simp [absentActor] at hlive

theorem roleTuple_stable (w w' : World) (g : CompatGroup)
    (h : ∀ r ∈ g.roles, (w'.st (.core r)).typestate = (w.st (.core r)).typestate) :
    roleTuple w' g = roleTuple w g := by
  unfold roleTuple
  apply map_state_congr
  exact h

theorem live_stable (w w' : World) (g : CompatGroup)
    (h : ∀ r ∈ g.roles, (w'.st (.core r)).life = (w.st (.core r)).life)
    (hl : groupLive w g) : groupLive w' g := by
  intro r hr
  rw [h r hr]
  exact hl r hr

/-- Typestates and lives of group roles are unchanged, and every actor satisfies
the local continuation obligations. -/
theorem sem_stable (I : Impl) (w w' : World) (hS : SemInv I w)
    (ht : ∀ g ∈ compatGroups I.desc.compatibility, ∀ r ∈ g.roles,
      (w'.st (.core r)).typestate = (w.st (.core r)).typestate)
    (hl : ∀ g ∈ compatGroups I.desc.compatibility, ∀ r ∈ g.roles,
      (w'.st (.core r)).life = (w.st (.core r)).life)
    (hcont : ∀ id, contTy (w'.st id))
    (hprog : ∀ id, programOk I.desc id (w'.st id))
    (hwait : ∀ id, waitEdge I.desc id (w'.st id))
    (hoff : ∀ id, (w'.st id).life ≠ .alive → (w'.st id).phase = .idle)
    (hroster : ∀ id, (w'.st id).life = .alive → id ∈ w'.roster) : SemInv I w' := by
  refine ⟨?_, ?_, hcont, hprog, hwait, hoff, hroster⟩
  · intro g hg hlive
    have hold : groupLive w g := by
      intro r hr
      rw [← hl g hg r hr]
      exact hlive r hr
    rw [roleTuple_stable w w' g (ht g hg)]
    exact hS.compat g hg hold
  · intro g hg
    exact live_stable w w' g (hl g hg) (hS.live g hg)

theorem sem_set (I : Impl) (w : World) (id : InstId) (a : Actor) (hS : SemInv I w)
    (hty : a.typestate = (w.st id).typestate) (hlife : a.life = (w.st id).life)
    (hcont : contTy a) (hprog : programOk I.desc id a) (hwait : waitEdge I.desc id a)
    (hoff : a.life ≠ .alive → a.phase = .idle) :
    SemInv I (setActor w id a) := by
  apply sem_stable I w (setActor w id a) hS
  · intro g _ r hr
    by_cases h : InstId.core r = id
    · simp [h, setActor_self, hty]
    · rw [setActor_other w id (.core r) a h]
  · intro g _ r hr
    by_cases h : InstId.core r = id
    · simp [h, setActor_self, hlife]
    · rw [setActor_other w id (.core r) a h]
  · intro i
    by_cases h : i = id
    · rw [h, setActor_self]; exact hcont
    · rw [setActor_other w id i a h]; exact hS.cont i
  · intro i
    by_cases h : i = id
    · rw [h, setActor_self]; exact hprog
    · rw [setActor_other w id i a h]; exact hS.prog i
  · intro i
    by_cases h : i = id
    · rw [h, setActor_self]; exact hwait
    · rw [setActor_other w id i a h]; exact hS.waited i
  · intro i hdead
    by_cases h : i = id
    · rw [h, setActor_self] at hdead ⊢
      exact hoff hdead
    · rw [setActor_other w id i a h] at hdead ⊢
      exact hS.idleOff i hdead
  · intro i hlive
    by_cases h : i = id
    · rw [h] at hlive ⊢
      rw [setActor_self] at hlive
      exact hS.rostered id (hlife.symm.trans hlive)
    · simp only [setActor, h] at hlive ⊢
      exact hS.rostered i hlive

/-- A non-idle actor is alive: an actor that is not alive is idle. -/
theorem alive_if_busy (I : Impl) (w : World) (hS : SemInv I w) (id : InstId)
    (h : (w.st id).phase ≠ .idle) : (w.st id).life = .alive := by
  cases hlife : (w.st id).life with
  | alive => rfl
  | absent => exact False.elim (h (hS.idleOff id (by rw [hlife]; intro he; cases he)))
  | dead => exact False.elim (h (hS.idleOff id (by rw [hlife]; intro he; cases he)))

theorem idleOff_alive {a : Actor} {life : Life} (hl : a.life = life) (ha : life = .alive) :
    a.life ≠ .alive → a.phase = .idle := by
  intro h
  exact absurd (hl.trans ha) h

theorem idleOff_life {a : Actor} (ha : a.life = .alive) : a.life ≠ .alive → a.phase = .idle :=
  idleOff_alive rfl ha

theorem idleOff_same (I : Impl) (w : World) (hS : SemInv I w) (id : InstId) (a : Actor)
    (hl : a.life = (w.st id).life) (hp : a.phase = (w.st id).phase) :
    a.life ≠ .alive → a.phase = .idle := by
  intro h
  have hold : (w.st id).life ≠ .alive := by
    rw [← hl]
    exact h
  rw [hp]
  exact hS.idleOff id hold

theorem idleOff_busy (I : Impl) (w : World) (hS : SemInv I w) (id : InstId) (a : Actor)
    (hl : a.life = (w.st id).life) (hbusy : (w.st id).phase ≠ .idle) :
    a.life ≠ .alive → a.phase = .idle := by
  intro h
  exact absurd (hl.trans (alive_if_busy I w hS id hbusy)) h

theorem idleOff_now (a : Actor) (hp : a.phase = .idle) : a.life ≠ .alive → a.phase = .idle :=
  fun _ => hp

theorem resume_life (a : Actor) (b : Bool) (dst : InstId) :
    (resumeSender a b dst).life = a.life := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases hb : b with
    | false => cases hk : k.rest <;> simp [resumeSender, hph, hb, hk, proceed]
    | true => simp [resumeSender, hph, hb]
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem idleOff_resume (I : Impl) (w : World) (hS : SemInv I w) (id : InstId) (b : Bool)
    (dst : InstId) :
    (resumeSender (w.st id) b dst).life ≠ .alive →
      (resumeSender (w.st id) b dst).phase = .idle := by
  intro h
  by_cases hidle : (w.st id).phase = .idle
  · simp [resumeSender, hidle]
  · have halive := alive_if_busy I w hS id hidle
    have hne : (w.st id).life ≠ .alive := by
      rw [← resume_life (w.st id) b dst]
      exact h
    exact absurd halive hne

theorem bump_keeps (a : Actor) (d : String) (delta : Int) :
    (bumpToken a d delta).typestate = a.typestate ∧ (bumpToken a d delta).life = a.life ∧
      (bumpToken a d delta).phase = a.phase := by
  simp [bumpToken]

theorem ok_tokens (D : Description) (id : InstId) (a : Actor) (d : String) (delta : Int) :
    contTy (bumpToken a d delta) = contTy a ∧
      programOk D id (bumpToken a d delta) = programOk D id a ∧
      waitEdge D id (bumpToken a d delta) = waitEdge D id a := by
  simp [bumpToken, contTy, programOk, waitEdge]

theorem credit_sem (I : Impl) (w : World) (tmpl : String) (sender : InstId) (hS : SemInv I w) :
    SemInv I (creditSender w tmpl sender) := by
  unfold creditSender
  apply sem_set I w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) hS
  · exact (bump_keeps _ _ _).1
  · exact (bump_keeps _ _ _).2.1
  · exact Eq.mp ((ok_tokens I.desc sender (w.st sender) tmpl (.ofNat 1)).1).symm (hS.cont sender)
  · exact Eq.mp ((ok_tokens I.desc sender (w.st sender) tmpl (.ofNat 1)).2.1).symm (hS.prog sender)
  · exact Eq.mp ((ok_tokens I.desc sender (w.st sender) tmpl (.ofNat 1)).2.2).symm (hS.waited sender)
  · exact idleOff_same I w hS sender _ (bump_keeps _ _ _).2.1 (bump_keeps _ _ _).2.2

theorem cells_sem (I : Impl) (w : World) (id : InstId) (hS : SemInv I w) :
    SemInv I (readCells I.desc w id) := by
  apply sem_stable I w (readCells I.desc w id) hS
  · intro _ _ r _
    simp [readCells_st]
  · intro _ _ r _
    simp [readCells_st]
  · intro i
    simpa [readCells_st] using hS.cont i
  · intro i
    simpa [readCells_st] using hS.prog i
  · intro i
    simpa [readCells_st] using hS.waited i
  · intro i h
    rw [readCells_st] at h ⊢
    exact hS.idleOff i h
  · intro i h
    rw [readCells_st] at h
    rw [cellsRoster]
    exact hS.rostered i h

/-- One group role moves along a transition the relation was closed under. -/
theorem sem_move (I : Impl) (w : World) (r : String) (a : Actor) (tr : Transition)
    (hS : SemInv I w) (hL : LocalOk I)
    (hfrom : (w.st (.core r)).typestate = tr.fromState) (hto : a.typestate = tr.toState)
    (hlife : a.life = (w.st (.core r)).life) (htm : tr.template = r)
    (hmem : tr ∈ I.transitions) (hcont : contTy a) (hprog : programOk I.desc (.core r) a)
    (hwait : waitEdge I.desc (.core r) a)
    (hoff : a.life ≠ .alive → a.phase = .idle) : SemInv I (setActor w (.core r) a) := by
  obtain ⟨step, hstep, htmpl, hfroms, htos, _hlab⟩ := stepsCover_of_local I hL tr hmem
  have hempty := compat_empty_of_local I hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hlive
    by_cases hin : r ∈ g.roles
    · rw [roleTuple_update w r a g, hto]
      have hold : groupLive w g := by
        intro role hrole
        by_cases hq : role = r
        · subst hq
          have hliver := hlive role hrole
          rw [setActor_self] at hliver
          rw [← hlife]
          exact hliver
        · have hid : InstId.core role ≠ InstId.core r := by
            intro he
            cases he
            exact hq rfl
          have hliver := hlive role hrole
          rw [setActor_other w (.core r) (.core role) a hid] at hliver
          exact hliver
      have hallowed := hS.compat g hg hold
      have hlook : lookupRole (roleTuple w g) r = some tr.fromState := by
        rw [← hfrom]
        exact lookup_roleTuple w g r hin
      have hbr := step_in_closure I.desc g step hempty hg hstep
      have hrole : g.roles.elem step.template = true := by
        rw [htmpl, htm]
        exact List.elem_iff.mpr hin
      have hf : lookupRole (roleTuple w g) step.template = some step.fromState := by
        simpa [htmpl, htm, hfroms] using hlook
      have hclosed := step_on_observed g step (roleTuple w g) hbr hallowed hrole hf
      simpa [htmpl, htm, htos] using hclosed
    · rw [roleTuple_other w (.core r) a g (fun role hrole he => hin (by cases he; exact hrole))]
      have hold : groupLive w g := by
        intro role hrole
        have hid : InstId.core role ≠ InstId.core r := by
          intro he
          cases he
          exact hin hrole
        have hliver := hlive role hrole
        rw [setActor_other w (.core r) (.core role) a hid] at hliver
        exact hliver
      exact hS.compat g hg hold
  · intro g hg role hrole
    by_cases hq : role = r
    · subst hq
      rw [setActor_self, hlife]
      exact hS.live g hg role hrole
    · have hid : InstId.core role ≠ InstId.core r := by
        intro he
        cases he
        exact hq rfl
      rw [setActor_other w (.core r) (.core role) a hid]
      exact hS.live g hg role hrole
  · intro i
    by_cases h : i = .core r
    · rw [h, setActor_self]; exact hcont
    · rw [setActor_other w (.core r) i a h]; exact hS.cont i
  · intro i
    by_cases h : i = .core r
    · rw [h, setActor_self]; exact hprog
    · rw [setActor_other w (.core r) i a h]; exact hS.prog i
  · intro i
    by_cases h : i = .core r
    · rw [h, setActor_self]; exact hwait
    · rw [setActor_other w (.core r) i a h]; exact hS.waited i
  · intro i hdead
    by_cases h : i = .core r
    · rw [h, setActor_self] at hdead ⊢
      exact hoff hdead
    · rw [setActor_other w (.core r) i a h] at hdead ⊢
      exact hS.idleOff i hdead
  · intro i hlive
    by_cases h : i = .core r
    · rw [h] at hlive ⊢
      rw [setActor_self] at hlive
      exact hS.rostered (.core r) (hlife.symm.trans hlive)
    · simp only [setActor, h] at hlive ⊢
      exact hS.rostered i hlive

theorem proceed_ok (D : Description) (id : InstId) (a : Actor) (k : Cont)
    (hty : a.typestate = k.toState) (hprog : effectsOk D (tname id) a.typestate k.rest = true) :
    (proceed a k).typestate = a.typestate ∧ (proceed a k).life = a.life ∧
      contTy (proceed a k) ∧ programOk D id (proceed a k) ∧ waitEdge D id (proceed a k) := by
  cases hk : k.rest with
  | nil => simp [proceed, hk, contTy, programOk, waitEdge, hty]
  | cons _ _ =>
    simp [proceed, hk, contTy, programOk, waitEdge, hty]
    rw [← hty, ← hk]
    exact hprog

theorem effects_tail_of (D : Description) (template state : String) (e : Eff) (es : List Eff)
    (h : effectsOk D template state (e :: es) = true) : effectsOk D template state es = true :=
  effectsOk_tail D template state e es h

theorem ingress_sem (I : Impl) (w w' : World) (dst : InstId) (label : String) (hS : SemInv I w)
    (h : receiveIngress I w dst label = some w') : SemInv I w' := by
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
            let a0 := w.st dst
            let charged := chargeSender a0 (tname dst)
            let msg : Msg :=
              { label := label, sender := dst, callFrom := none, reliable := true, mid := a0.nextMid }
            let a' : Actor := { charged with box := a0.box ++ [msg], nextMid := a0.nextMid + 1 }
            have hty : a'.typestate = a0.typestate := by simp [a', charged, chargeSender, bumpToken]
            have hlife : a'.life = a0.life := by simp [a', charged, chargeSender, bumpToken]
            have hcont : contTy a' := by
              simpa [contTy, a', charged, chargeSender, bumpToken] using hS.cont dst
            have hprog : programOk I.desc dst a' := by
              simpa [programOk, a', charged, chargeSender, bumpToken] using hS.prog dst
            have hwait : waitEdge I.desc dst a' := by
              simpa [waitEdge, a', charged, chargeSender, bumpToken] using hS.waited dst
            simpa [a', msg, charged, a0] using sem_set I w dst a' hS hty hlife hcont hprog hwait
              (idleOff_same I w hS dst a' hlife (by simp [a', charged, chargeSender, bumpToken, a0]))

theorem finish_sem (I : Impl) (w w' : World) (id : InstId) (hS : SemInv I w)
    (h : finishWait I w id = some w') : SemInv I w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
      simpa [programOk, hph] using hS.prog id
    have hp := proceed_ok I.desc id (w.st id) k hty hprog
    exact sem_set I w id (proceed (w.st id) k) hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_busy I w hS id _ hp.2.1 (by simp [hph]))
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    cases hw
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    have hprog : effectsOk I.desc (tname id) (w.st id).typestate k.rest = true := by
      simpa [programOk, hph] using hS.prog id
    have hp := proceed_ok I.desc id (w.st id) k hty hprog
    exact sem_set I w id (proceed (w.st id) k) hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_busy I w hS id _ hp.2.1 (by simp [hph]))
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem peer_ne_core (template : String) (ix : Nat) (r : String) :
    InstId.peer template ix ≠ InstId.core r := by
  intro h
  cases h

theorem spawn_sem (I : Impl) (w w' : World) (template : String) (hS : SemInv I w)
    (h : spawn I w template = some w') : SemInv I w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t heq =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      apply cells_sem
      apply sem_stable
      · exact hS
      · intro _ _ r _
        have hne := peer_ne_core template (w.nextIx template) r
        simp [setActor, hne]
      · intro _ _ r _
        have hne := peer_ne_core template (w.nextIx template) r
        simp [setActor, hne]
      · intro i
        by_cases hi : i = InstId.peer template (w.nextIx template)
        · simp [hi, setActor, withTokens, contTy]
        · simp [setActor, hi]
          exact hS.cont i
      · intro i
        by_cases hi : i = InstId.peer template (w.nextIx template)
        · simp [hi, setActor, withTokens, programOk]
        · simp [setActor, hi]
          exact hS.prog i
      · intro i
        by_cases hi : i = InstId.peer template (w.nextIx template)
        · simp [hi, setActor, withTokens, waitEdge]
        · simp [setActor, hi]
          exact hS.waited i
      · intro i hdead
        by_cases hi : i = InstId.peer template (w.nextIx template)
        · simp [hi, setActor, withTokens] at hdead
        · simp [setActor, hi] at hdead ⊢
          exact hS.idleOff i hdead
      · intro i hlive
        by_cases hi : i = InstId.peer template (w.nextIx template)
        · simp [hi, setActor]
        · simp [setActor, hi] at hlive
          exact List.mem_append_left _ (hS.rostered i hlive)
    · simp [hif] at h

theorem charge_ok (a : Actor) (d : String) :
    (chargeSender a d).typestate = a.typestate ∧ (chargeSender a d).life = a.life ∧
      (chargeSender a d).phase = a.phase := by
  simp [chargeSender, bumpToken]

theorem enqueue_sem (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (isCall : Bool)
    (k : Cont) (hS : SemInv I w)
    (hty : (w.st sender).typestate = k.toState)
    (htail : effectsOk I.desc (tname sender) (w.st sender).typestate k.rest = true)
    (hedge : ∃ label, hasEdge I.desc (tname sender) (w.st sender).typestate (tname dst)
      (if isCall then .call else .send) .blocking label = true)
    (hsender : (w.st sender).life = .alive) :
    SemInv I (enqueueOrPark w I.desc sender dst msg isCall k) := by
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · simp [halive]
    have hcharge := charge_ok (w.st sender) (tname dst)
    -- The mailbox write keeps the target's phase and typestate; the sender keeps its typestate.
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        -- One actor: charged, box extended, then proceed or await.
        have hty' : (chargeSender (w.st sender) (tname sender)).typestate = k.toState := by
          rw [hcharge.1, hty]
        if hcall : isCall = true then
          simp [hcall]
          apply sem_set I w sender _ hS
          · exact hcharge.1
          · exact hcharge.2.1
          · simp [contTy]
            exact hty'
          · simp [programOk]
            rw [hcharge.1]
            exact htail
          · simp [waitEdge]
            rw [hcharge.1]
            simpa [hcall] using hedge
          · exact idleOff_life hsender
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          have hp := proceed_ok I.desc sender
            { chargeSender (w.st sender) (tname sender) with
                box := (chargeSender (w.st sender) (tname sender)).box ++
                  [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }],
                nextMid := (chargeSender (w.st sender) (tname sender)).nextMid + 1 }
            k (by rw [hcharge.1, hty]) (by simpa [hcharge.1] using htail)
          apply sem_set I w sender _ hS
          · rw [hp.1, hcharge.1]
          · rw [hp.2.1, hcharge.2.1]
          · exact hp.2.2.1
          · exact hp.2.2.2.1
          · exact hp.2.2.2.2
          · exact idleOff_alive hp.2.1 hsender
      · simp [hsame]
        rw [← halive, ← hroom.1]
        -- Destination first, then the sender.
        have hdst : SemInv I (setActor w dst { (w.st dst) with
            box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
            nextMid := (w.st dst).nextMid + 1 }) := by
          apply sem_set I w dst _ hS
          · rfl
          · rfl
          · simpa [contTy] using hS.cont dst
          · simpa [programOk] using hS.prog dst
          · simpa [waitEdge] using hS.waited dst
          · exact idleOff_life halive
        have hty' : (chargeSender (w.st sender) (tname dst)).typestate = k.toState := by
          rw [hcharge.1, hty]
        if hcall : isCall = true then
          simp [hcall]
          apply sem_set I _ sender _ hdst
          · rw [setActor_other _ dst sender _ (hsame)]
            exact hcharge.1
          · rw [setActor_other _ dst sender _ (hsame)]
            exact hcharge.2.1
          · simp [contTy, setActor_other _ dst sender _ hsame]
            exact hty'
          · simp [programOk, setActor_other _ dst sender _ hsame]
            rw [hcharge.1]
            exact htail
          · simp [waitEdge, setActor_other _ dst sender _ hsame]
            rw [hcharge.1]
            simpa [hcall] using hedge
          · exact idleOff_life hsender
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          have hp := proceed_ok I.desc sender (chargeSender (w.st sender) (tname dst)) k
            (by rw [hcharge.1, hty]) (by simpa [hcharge.1] using htail)
          apply sem_set I _ sender _ hdst
          · rw [setActor_other _ dst sender _ hsame]
            rw [hp.1, hcharge.1]
          · rw [setActor_other _ dst sender _ hsame]
            rw [hp.2.1, hcharge.2.1]
          · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.1
          · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.2.1
          · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.2.2
          · exact idleOff_alive (hp.2.1.trans (charge_ok _ _).2.1) hsender
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        simp
        apply sem_set I w sender _ hS
        · exact hcharge.1
        · exact hcharge.2.1
        · simp [contTy]
          rw [hcharge.1]
          exact hty
        · simp [programOk]
          rw [hcharge.1]
          exact htail
        · simp [waitEdge]
          rw [hcharge.1]
          exact hedge
        · exact idleOff_life hsender
      · simp [hsame]
        rw [← halive]
        have hdst : SemInv I (setActor w dst { (w.st dst) with
            parked := (w.st dst).parked ++
              [{ sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := isCall }],
            nextMid := (w.st dst).nextMid + 1 }) := by
          apply sem_set I w dst _ hS
          · rfl
          · rfl
          · simpa [contTy] using hS.cont dst
          · simpa [programOk] using hS.prog dst
          · simpa [waitEdge] using hS.waited dst
          · exact idleOff_life halive
        apply sem_set I _ sender _ hdst
        · rw [setActor_other _ dst sender _ (hsame)]
          exact hcharge.1
        · rw [setActor_other _ dst sender _ (hsame)]
          exact hcharge.2.1
        · simp [contTy, setActor_other _ dst sender _ hsame]
          rw [hcharge.1]
          exact hty
        · simp [programOk, setActor_other _ dst sender _ hsame]
          rw [hcharge.1]
          exact htail
        · simp [waitEdge, setActor_other _ dst sender _ hsame]
          rw [hcharge.1]
          exact hedge
        · exact idleOff_life hsender
  · simp [halive]
    have hp := proceed_ok I.desc sender (w.st sender) k hty htail
    exact sem_set I w sender (proceed (w.st sender) k) hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      (idleOff_alive hp.2.1 hsender)

/-- A fitting `trySend` is an enqueue of an unreliable message, so it needs no blocking edge. -/
theorem try_room_sem (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (hS : SemInv I w) (hty : (w.st sender).typestate = k.toState)
    (htail : effectsOk I.desc (tname sender) (w.st sender).typestate k.rest = true)
    (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst)
    (hsender : (w.st sender).life = .alive) :
    SemInv I (enqueueOrPark w I.desc sender dst msg false k) := by
  unfold enqueueOrPark
  have hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst := ⟨hpark, hcap⟩
  simp [hlive, hroom]
  have hcharge := charge_ok (w.st sender) (tname dst)
  by_cases hsame : sender = dst
  · subst hsame
    simp
    have hp := proceed_ok I.desc sender { chargeSender (w.st sender) (tname sender) with
        box := (chargeSender (w.st sender) (tname sender)).box ++
          [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }],
        nextMid := (chargeSender (w.st sender) (tname sender)).nextMid + 1 } k
      (by rw [hcharge.1, hty]) (by simpa [hcharge.1] using htail)
    apply sem_set I w sender _ hS
    · rw [hp.1, hcharge.1]
    · rw [hp.2.1, hcharge.2.1]
    · exact hp.2.2.1
    · exact hp.2.2.2.1
    · exact hp.2.2.2.2
    · exact idleOff_alive hp.2.1 hsender
  · simp [hsame]
    rw [← hlive, ← hpark]
    have hdst : SemInv I (setActor w dst { (w.st dst) with
        box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
        nextMid := (w.st dst).nextMid + 1 }) := by
      apply sem_set I w dst _ hS
      · rfl
      · rfl
      · simpa [contTy] using hS.cont dst
      · simpa [programOk] using hS.prog dst
      · simpa [waitEdge] using hS.waited dst
      · exact idleOff_life hlive
    have hp := proceed_ok I.desc sender (chargeSender (w.st sender) (tname dst)) k
      (by rw [hcharge.1, hty]) (by simpa [hcharge.1] using htail)
    apply sem_set I _ sender _ hdst
    · rw [setActor_other _ dst sender _ hsame]
      rw [hp.1, hcharge.1]
    · rw [setActor_other _ dst sender _ hsame]
      rw [hp.2.1, hcharge.2.1]
    · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.1
    · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.2.1
    · simpa [setActor_other _ dst sender _ hsame] using hp.2.2.2.2
    · exact idleOff_alive (hp.2.1.trans (charge_ok _ _).2.1) hsender

end Deadlock
