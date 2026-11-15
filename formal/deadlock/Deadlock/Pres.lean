import Deadlock.RunInv

set_option autoImplicit false

namespace Deadlock

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
    refine ⟨?_, ?_, hcont, hprog, hwait⟩
    · intro g hg
      simp [compatGroups, hc] at hg
    · intro g hg
      simp [compatGroups, hc] at hg
  | groups gs =>
    refine ⟨?_, ?_, hcont, hprog, hwait⟩
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

end Deadlock
