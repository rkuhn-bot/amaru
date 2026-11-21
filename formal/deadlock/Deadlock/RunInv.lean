import Deadlock.Compat
import Deadlock.Local

set_option autoImplicit false

namespace Deadlock

/-- The continuation is a checked suffix of a transition. `contTy` says the
actor's typestate is `k.toState`, which is `contAt`'s `here`. Outcome lists
are checked at their own recorded typestate. -/
def programOk (D : Description) (id : InstId) (a : Actor) : Prop :=
  match a.phase with
  | .run k => effectsOk D (tname id) (contAt k) k.rest = true
  | .parked _ _ k => effectsOk D (tname id) (contAt k) k.rest = true
  | .awaitReply _ k => effectsOk D (tname id) (contAt k) k.rest = true
  | .awaitEffect k => effectsOk D (tname id) (contAt k) k.rest = true
  | .awaitPeer k => effectsOk D (tname id) (contAt k) k.rest = true
  | _ => True

/-- The effect that parked this actor, or the call it is awaiting, is still an
edge out of the typestate it moved to before blocking. The continuation no
longer contains that effect. -/
def waitEdge (D : Description) (id : InstId) (a : Actor) : Prop :=
  match a.phase with
  | .parked dst isCall _ =>
    ∃ label, hasEdge D (tname id) a.typestate (tname dst)
      (if isCall then .call else .send) .blocking label = true
  | .awaitReply dst _ =>
    ∃ label, hasEdge D (tname id) a.typestate (tname dst) .call .blocking label = true
  | _ => True

structure SemInv (I : Impl) (w : World) : Prop where
  compat : CompatInv I w
  /-- The role tuple stays in `RowOk`: a stored row, a declared step, or a
  landing state of the transition that produced it. Every role is alive or has
  halted. Halting freezes the typestate. A crashed roster is halted, so the
  tuple is not re-proved from a live group. -/
  live : ∀ g ∈ compatGroups I.desc.compatibility,
    RowOk I g (roleTuple w g) ∧
    ∀ r ∈ g.roles, (w.st (InstId.core r)).life = .alive ∨ Halted (w.st (InstId.core r)).life
  cont : ∀ id, contTy (w.st id)
  prog : ∀ id, programOk I.desc id (w.st id)
  waited : ∀ id, waitEdge I.desc id (w.st id)
  /-- Absent, shutting-down, and sealed actors are idle. A roster crashed by a
  permanent core is dead in the crashed phase, which is the other way an actor
  that is not alive can stand. -/
  idleOff : ∀ id, (w.st id).life ≠ .alive →
    (w.st id).phase = .idle ∨ (w.st id).phase = .crashed
  /-- A live actor is on the roster. A kill folds that roster to fail waiters. -/
  rostered : ∀ id, (w.st id).life = .alive → id ∈ w.roster
  /-- A parked entry lives on a roster actor. A kill folds that roster to drop the dead sender. -/
  offEmpty : ∀ id, id ∉ w.roster → (w.st id).parked = []

theorem effectsOk_tail (D : Description) (template : String) (at_ : BranchAt) (e : Eff) (es : List Eff)
    (h : effectsOk D template at_ (e :: es) = true) : effectsOk D template at_ es = true := by
  simp only [effectsOk, Bool.and_eq_true] at h
  exact h.2

theorem readCells_st (D : Description) (w : World) (id i : InstId) :
    (readCells D w id).st i = w.st i := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

/-- `deliver` reads cells and returns the receiver's next actor. It does not
rewrite anyone's stored actor; the receive installs that actor afterwards. -/
theorem deliver_st (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (i : InstId) (h : deliver I w id a m = some (w1, a1)) :
    w1.st i = w.st i := by
  unfold deliver at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · injection h with hpair
      cases hpair
      exact readCells_st I.desc w id i
    · split at h
      · split at h
        · cases h
        · injection h with hpair
          cases hpair
          exact readCells_st I.desc w id i
      · split at h
        · cases h
        · injection h with hpair
          cases hpair
          exact readCells_st I.desc w id i

theorem findSome_tr (xs : List Transition) (template state label : String) (tr : Transition)
    (h : xs.findSome? (fun a =>
        if a.template == template && a.fromState == state && a.label == label then some a else none) =
      some tr) :
    tr ∈ xs ∧ tr.template = template ∧ tr.fromState = state ∧ tr.label = label := by
  obtain ⟨_l1, a, _l2, heq, hf, _⟩ := (List.findSome?_eq_some_iff).mp h
  subst heq
  have ha : a = tr := by
    by_cases hc : a.template == template && a.fromState == state && a.label == label
    · simp [hc] at hf
      exact hf
    · simp [hc] at hf
  subst ha
  simp [Bool.and_eq_true, beq_iff_eq] at hf
  exact ⟨List.mem_append.mpr (Or.inr (List.Mem.head _)), hf.1, hf.2.1, hf.2.2⟩

theorem findTr_mem (I : Impl) (template state label : String) (tr : Transition)
    (h : findTr I template state label = some tr) :
    tr ∈ I.transitions ∧ tr.template = template ∧ tr.fromState = state ∧ tr.label = label := by
  simpa [findTr] using findSome_tr I.transitions template state label tr h

theorem stepsCover_of_local (I : Impl) (h : LocalOk I) : stepsCover I := by
  have hsc := (local_parts I h).2.2.2.2.2.2.2
  unfold stepsCoverB at hsc
  simp only [List.all_eq_true] at hsc
  intro tr hm
  have hany := hsc tr hm
  simp only [List.any_eq_true] at hany
  obtain ⟨s, hs, hst⟩ := hany
  simp [Bool.and_eq_true, beq_iff_eq] at hst
  exact ⟨s, hs, hst.1.1.1, hst.1.1.2, hst.1.2, hst.2⟩

theorem compat_empty_of_local (I : Impl) (h : LocalOk I) : compatFails I.desc = [] := by
  have hc := (local_parts I h).2.2.2.2.2.2.1
  exact isEmpty_true _ hc

theorem credit_keeps_ty (w : World) (tmpl : String) (sender id : InstId) :
    ((creditSender w tmpl sender).st id).life = (w.st id).life ∧
      ((creditSender w tmpl sender).st id).typestate = (w.st id).typestate := by
  unfold creditSender bumpToken
  by_cases h : id = sender
  · simp [setActor, h]
  · simp [setActor, h]

theorem proceed_keeps_ty (a : Actor) (k : Cont) (h : a.typestate = k.toState) :
    (proceed a k).typestate = a.typestate := by
  cases hk : k.rest <;> simp [proceed, hk, h]

theorem role_unchanged (w : World) (id : InstId) (a : Actor) (r : String) (h : id ≠ .core r) :
    ((setActor w id a).st (.core r)).typestate = (w.st (.core r)).typestate ∧
      ((setActor w id a).st (.core r)).life = (w.st (.core r)).life := by
  rw [setActor_other w id (.core r) a (Ne.symm h)]
  exact ⟨rfl, rfl⟩

theorem substRole_fixed (tup : List RoleState) (role s : String)
    (h : ∀ rs ∈ tup, rs.role = role → rs.state = s) : substRole tup role s = tup := by
  induction tup with
  | nil => rfl
  | cons hd tl ih =>
    unfold substRole
    rw [List.map_cons]
    by_cases hq : hd.role = role
    · have hs : hd.state = s := h hd (List.Mem.head _) hq
      rw [if_pos hq]
      have hhd : { hd with state := s } = hd := by
        cases hd
        subst hs
        rfl
      rw [hhd]
      exact congrArg (fun t => hd :: t) (ih fun rs hrs => h rs (List.Mem.tail _ hrs))
    · rw [if_neg hq]
      exact congrArg (fun t => hd :: t) (ih fun rs hrs => h rs (List.Mem.tail _ hrs))

theorem tuple_role_state (a tup : List RoleState) (role s : String)
    (h : tupleMem [a] tup = true) (hl : lookupRole tup role = some s)
    (rs : RoleState) (hrs : rs ∈ tup) (hr : rs.role = role) : rs.state = s := by
  have hA : lookupRole a role = some s := tuple_agree a tup h role s hl
  simp [tupleMem, List.any_cons, List.any_nil, Bool.and_eq_true, List.all_eq_true] at h
  have hrs' := h.1 rs hrs
  simp [hr, beq_iff_eq] at hrs'
  rw [hA] at hrs'
  cases hrs'
  rfl

theorem tupleMem_pick (allowed : List (List RoleState)) (tup : List RoleState)
    (h : tupleMem allowed tup = true) : ∃ a ∈ allowed, tupleMem [a] tup = true := by
  simp [tupleMem, List.any_eq_true] at h
  obtain ⟨a, ha, hagree⟩ := h
  refine ⟨a, ha, ?_⟩
  simpa [tupleMem, List.any_cons, List.any_nil, Bool.and_eq_true, List.all_eq_true] using hagree

theorem charge_same (a : Actor) (d : String) :
    (chargeSender a d).typestate = a.typestate ∧ (chargeSender a d).life = a.life := by
  simp [chargeSender, bumpToken]

theorem find_name (xs : List Template) (r : String) (h : ∃ t ∈ xs, t.name = r) :
    ∃ t, xs.findSome? (fun t => if t.name == r then some t else none) = some t ∧ t.name = r := by
  induction xs with
  | nil => simp at h
  | cons t ts ih =>
    rw [List.findSome?_cons]
    by_cases hb : (t.name == r) = true
    · simp only [hb]
      exact ⟨t, rfl, beq_iff_eq.mp hb⟩
    · have hf : (t.name == r) = false := by
        cases hbb : t.name == r <;> simp_all
      simp only [hf]
      obtain ⟨u, hu, hn⟩ := h
      rcases List.mem_cons.mp hu with heq | hu
      · subst heq
        exact absurd (beq_iff_eq.mpr hn) hb
      · exact ih ⟨u, hu, hn⟩

theorem templateOf_of_has (D : Description) (r : String) (h : hasTemplate D r = true) :
    ∃ t, templateOf D r = some t ∧ t.name = r := by
  have hmem : ∃ t ∈ D.templates, t.name = r := by
    simpa [hasTemplate, List.any_eq_true, beq_iff_eq] using h
  simpa [templateOf] using find_name D.templates r hmem

theorem not_perPeer (t : Template) (h : (t.multiplicity == .perPeer) = false) : t.multiplicity = .one := by
  cases hm : t.multiplicity with
  | one => rfl
  | perPeer =>
    rw [hm] at h
    have he : (Multiplicity.perPeer == Multiplicity.perPeer) = true := by decide
    rw [he] at h
    cases h

private theorem filters_empty (D : Description) (g : CompatGroup) (h : groupWellformed D g = []) :
    (g.roles.filter fun x => !(hasTemplate D x)).isEmpty = true ∧
      (g.roles.filter fun x =>
        match templateOf D x with
        | some u => u.multiplicity == .perPeer
        | none => false).isEmpty = true ∧
      (g.roles.filter fun x =>
        match templateOf D x with
        | some u => u.terminable
        | none => false).isEmpty = true := by
  unfold groupWellformed at h
  dsimp only at h
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
          · rename_i hlen hdup hunk hpeer hterm
            have to_empty {b : Bool} (hb : ¬ (!b) = true) : b = true := by
              cases b <;> simp_all
            exact ⟨to_empty hunk, to_empty hpeer, to_empty hterm⟩

theorem empty_no_mem {α : Type} (xs : List α) (h : xs.isEmpty = true) (a : α) : a ∉ xs := by
  intro ha
  cases xs with
  | nil => cases ha
  | cons _ _ => simp [List.isEmpty] at h

theorem role_static (D : Description) (g : CompatGroup) (r : String)
    (h : groupWellformed D g = []) (hr : r ∈ g.roles) :
    ∃ t, templateOf D r = some t ∧ t.multiplicity = .one ∧ t.terminable = false ∧ t.name = r := by
  obtain ⟨hunk, hpeer, hterm⟩ := filters_empty D g h
  have hhas : hasTemplate D r = true := by
    cases hb : hasTemplate D r with
    | true => rfl
    | false => exact False.elim (empty_no_mem _ hunk r (List.mem_filter.mpr ⟨hr, by simp [hb]⟩))
  obtain ⟨t, ht, hn⟩ := templateOf_of_has D r hhas
  have hmult : (t.multiplicity == .perPeer) = false := by
    cases hb : t.multiplicity == .perPeer with
    | false => rfl
    | true => exact False.elim (empty_no_mem _ hpeer r (List.mem_filter.mpr ⟨hr, by simp [ht, hb]⟩))
  have hkill : t.terminable = false := by
    cases hb : t.terminable with
    | false => rfl
    | true => exact False.elim (empty_no_mem _ hterm r (List.mem_filter.mpr ⟨hr, by simp [ht, hb]⟩))
  exact ⟨t, ht, not_perPeer t hmult, hkill, hn⟩

theorem init_tuple_mem (D : Description) (g : CompatGroup)
    (h : compatFails D = []) (hg : g ∈ compatGroups D.compatibility) :
    tupleMem g.allowed (initialTuple D g) = true := by
  have hcl := closure_nil D g h hg
  have hw : (groupWellformed D g).isEmpty = true := by
    simp [(compat_group_closed D g h hg).1]
  unfold groupClosure at hcl
  simp only [hw, ite_true] at hcl
  have hinit := append_nil_left hcl
  by_cases ht : tupleMem g.allowed (initialTuple D g) = true
  · exact ht
  · have hfalse : tupleMem g.allowed (initialTuple D g) = false := by
      cases htm : tupleMem g.allowed (initialTuple D g) <;> simp_all
    simp [hfalse] at hinit

theorem tupleMem_trans (allowed : List (List RoleState)) (x y : List RoleState)
    (hx : tupleMem allowed x = true) (hxy : tupleMem [x] y = true) :
    tupleMem allowed y = true := by
  obtain ⟨b, hb, hbx⟩ := tupleMem_pick allowed x hx
  simp [tupleMem, List.any_cons, List.any_nil, Bool.and_eq_true, List.all_eq_true] at hbx hxy ⊢
  refine ⟨b, hb, ?_, ?_⟩
  · intro rs hrs
    have hxlook : lookupRole x rs.role = some rs.state := by
      simpa [beq_iff_eq] using hxy.1 rs hrs
    obtain ⟨rsx, hmem, hrole, hs⟩ := lookup_mem x rs.role rs.state hxlook
    have hblook := hbx.1 rsx hmem
    simpa [hrole, hs, beq_iff_eq] using hblook
  · intro rs hrs
    have hxlook : lookupRole x rs.role = some rs.state := by
      simpa [beq_iff_eq] using hbx.2 rs hrs
    obtain ⟨rsx, hmem, hrole, hs⟩ := lookup_mem x rs.role rs.state hxlook
    have hylook := hxy.2 rsx hmem
    simpa [hrole, hs, beq_iff_eq] using hylook

theorem tupleMem_subst (a tup : List RoleState) (role state s : String)
    (h : tupleMem [a] tup = true) (hl : lookupRole tup role = some s) :
    tupleMem [substRole a role state] (substRole tup role state) = true := by
  have hlook : lookupRole a role = some s := tuple_agree a tup h role s hl
  simp [tupleMem, List.any_cons, List.any_nil, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨?_, ?_⟩
  · intro rs hrs
    rcases List.mem_map.mp hrs with ⟨rs0, hrs0, rfl⟩
    by_cases hrole : rs0.role = role
    · simp [substRole, hrole, beq_iff_eq]
      exact lookup_subst_self a role s state hlook
    · simp only [if_neg hrole]
      have hother := lookup_subst_other a role state rs0.role hrole
      rw [hother]
      exact h.1 rs0 hrs0
  · intro rs hrs
    rcases List.mem_map.mp hrs with ⟨rs0, hrs0, rfl⟩
    by_cases hrole : rs0.role = role
    · simp [substRole, hrole, beq_iff_eq]
      exact lookup_subst_self tup role s state hl
    · simp only [if_neg hrole]
      have hother := lookup_subst_other tup role state rs0.role hrole
      rw [hother]
      exact h.2 rs0 hrs0

/-- Closing a stored tuple that agrees with the observed one closes the observed one. -/
theorem step_on_observed (g : CompatGroup) (step : CompatStep) (tup : List RoleState)
    (hbr : stepBreaks g step false = []) (hmem : tupleMem g.allowed tup = true)
    (hrole : g.roles.elem step.template = true)
    (hf : lookupRole tup step.template = some step.fromState) :
    tupleMem g.allowed (substRole tup step.template step.toState) = true := by
  obtain ⟨a, ha, hag⟩ := tupleMem_pick g.allowed tup hmem
  have hlook : lookupRole a step.template = some step.fromState :=
    tuple_agree a tup hag step.template step.fromState hf
  have hclosed := stepBreaks_closed g step a hbr ha hrole hlook
  have hsub := tupleMem_subst a tup step.template step.toState step.fromState hag hf
  exact tupleMem_trans g.allowed (substRole a step.template step.toState)
    (substRole tup step.template step.toState) hclosed hsub

theorem lookup_mapped (roles : List String) (st : String → String) (r : String) (hr : r ∈ roles) :
    lookupRole (roles.map fun role => { role := role, state := st role }) r = some (st r) := by
  induction roles with
  | nil => cases hr
  | cons role roles ih =>
    rw [List.map_cons]
    simp only [lookupRole, List.findSome?_cons]
    by_cases hq : role = r
    · simp [hq]
    · simp [hq]
      exact ih (by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact absurd rfl hq
        · exact hr)

theorem lookup_roleTuple (w : World) (g : CompatGroup) (r : String) (hr : r ∈ g.roles) :
    lookupRole (roleTuple w g) r = some (w.st (.core r)).typestate := by
  simpa [roleTuple] using lookup_mapped g.roles (fun role => (w.st (.core role)).typestate) r hr

theorem map_state_congr (roles : List String) (st st' : String → String)
    (h : ∀ r ∈ roles, st r = st' r) :
    roles.map (fun r => ({ role := r, state := st r } : RoleState)) =
      roles.map (fun r => { role := r, state := st' r }) := by
  induction roles with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons, List.map_cons, h r (List.Mem.head _)]
    exact congrArg (fun t => { role := r, state := st' r } :: t)
      (ih fun x hx => h x (List.Mem.tail _ hx))

theorem roleTuple_other (w : World) (id : InstId) (a : Actor) (g : CompatGroup)
    (h : ∀ r ∈ g.roles, id ≠ .core r) : roleTuple (setActor w id a) g = roleTuple w g := by
  unfold roleTuple
  apply map_state_congr
  intro r hr
  have hid := h r hr
  simp [setActor, Ne.symm hid]

theorem map_subst (roles : List String) (st : String → String) (r s : String) :
    substRole (roles.map fun role => { role := role, state := st role }) r s =
      roles.map fun role => { role := role, state := if role = r then s else st role } := by
  simp only [substRole, List.map_map]
  apply List.map_congr_left
  intro role _
  by_cases hq : role = r <;> simp [hq]

theorem roleTuple_update (w : World) (r : String) (a : Actor) (g : CompatGroup) :
    roleTuple (setActor w (.core r) a) g = substRole (roleTuple w g) r a.typestate := by
  unfold roleTuple
  rw [map_subst]
  apply map_state_congr
  intro role _
  by_cases hq : role = r
  · simp [setActor, hq]
  · have hid : InstId.core role ≠ InstId.core r := by
      intro he
      cases he
      exact hq rfl
    simp [setActor, hq, hid]

end Deadlock
