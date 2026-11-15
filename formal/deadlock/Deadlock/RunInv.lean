import Deadlock.Compat
import Deadlock.Local

set_option autoImplicit false

namespace Deadlock

/-- The continuation at this program counter is a checked suffix of a transition,
so a blocking effect here is an edge out of the current typestate. -/
def programOk (D : Description) (id : InstId) (a : Actor) : Prop :=
  match a.phase with
  | .run k => effectsOk D (tname id) a.typestate k.rest = true
  | .parked _ _ k => effectsOk D (tname id) a.typestate k.rest = true
  | .awaitReply _ k => effectsOk D (tname id) a.typestate k.rest = true
  | .awaitEffect k => effectsOk D (tname id) a.typestate k.rest = true
  | .awaitPeer k => effectsOk D (tname id) a.typestate k.rest = true
  | _ => True

structure SemInv (I : Impl) (w : World) : Prop where
  compat : CompatInv I.desc w
  live : ∀ g ∈ compatGroups I.desc.compatibility, groupLive w g
  cont : ∀ id, contTy (w.st id)
  prog : ∀ id, programOk I.desc id (w.st id)

theorem effectsOk_tail (D : Description) (template state : String) (e : Eff) (es : List Eff)
    (h : effectsOk D template state (e :: es) = true) : effectsOk D template state es = true := by
  cases e <;> simp [effectsOk] at h <;> simp [h]

theorem readCells_st (D : Description) (w : World) (id i : InstId) :
    (readCells D w id).st i = w.st i := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

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

end Deadlock
