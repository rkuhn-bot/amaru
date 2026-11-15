import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

/-! The group relation is untrusted. `compatFails = []` is a local check that the
initial tuple is allowed and that every listed step and every restart preserves
the set. That is enough for every run, because a step changes at most the
typestate of one live actor, and termination is a restart in the product
(a dead role is read back as its initial state). -/

def observedState (D : Description) (w : World) (role : String) : String :=
  let id := InstId.core role
  if (w.st id).life == .alive then (w.st id).typestate
  else
    match templateOf D role with
    | some t => t.initial
    | none => ""

def observedTuple (D : Description) (w : World) (g : CompatGroup) : List RoleState :=
  g.roles.map fun r => { role := r, state := observedState D w r }

def CompatInv (D : Description) (w : World) : Prop :=
  ∀ g ∈ compatGroups D.compatibility, tupleMem g.allowed (observedTuple D w g) = true

def contTy (a : Actor) : Prop :=
  match a.phase with
  | .run k => a.typestate = k.toState
  | .parked _ _ k => a.typestate = k.toState
  | .awaitReply _ k => a.typestate = k.toState
  | .awaitEffect k => a.typestate = k.toState
  | .awaitPeer k => a.typestate = k.toState
  | _ => True

def CInv (D : Description) (w : World) : Prop :=
  CompatInv D w ∧ ∀ id, contTy (w.st id)

def stepsCover (I : Impl) : Prop :=
  ∀ tr ∈ I.transitions,
    ∃ step ∈ I.desc.steps,
      step.template = tr.template ∧ step.fromState = tr.fromState ∧
        step.toState = tr.toState ∧ step.label = tr.label

theorem append_nil_right {α : Type} {xs ys : List α} (h : xs ++ ys = []) : ys = [] := by
  cases xs with
  | nil => simpa using h
  | cons _ _ => simp at h

theorem append_nil_left {α : Type} {xs ys : List α} (h : xs ++ ys = []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => simp at h

theorem flatMap_nil_mem {α β : Type} (f : α → List β) (xs : List α) (x : α)
    (h : xs.flatMap f = []) (hx : x ∈ xs) : f x = [] := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.flatMap_cons] at h
    cases hx with
    | head => exact append_nil_left h
    | tail _ ht => exact ih (append_nil_right h) ht

theorem compat_group_closed (D : Description) (g : CompatGroup)
    (h : compatFails D = []) (hg : g ∈ compatGroups D.compatibility) :
    groupWellformed D g = [] ∧ groupClosure D g = [] := by
  cases hc : D.compatibility with
  | all => simp [compatGroups, hc] at hg
  | explicit _ => simp [compatGroups, hc] at hg
  | groups gs =>
    simp [compatGroups, hc] at hg
    unfold compatFails at h
    simp only [hc] at h
    have hflat : (gs.flatMap fun g => groupWellformed D g ++ groupClosure D g) = [] :=
      append_nil_left h
    have hone := flatMap_nil_mem (fun g => groupWellformed D g ++ groupClosure D g) gs g hflat hg
    exact ⟨append_nil_left hone, append_nil_right hone⟩

theorem closure_nil (D : Description) (g : CompatGroup)
    (h : compatFails D = []) (hg : g ∈ compatGroups D.compatibility) :
    groupClosure D g = [] :=
  (compat_group_closed D g h hg).2

theorem step_in_closure (D : Description) (g : CompatGroup) (step : CompatStep)
    (h : compatFails D = []) (hg : g ∈ compatGroups D.compatibility) (hs : step ∈ D.steps) :
    stepBreaks g step false = [] := by
  have hcl := closure_nil D g h hg
  have hw : (groupWellformed D g).isEmpty = true := by
    simp [(compat_group_closed D g h hg).1]
  unfold groupClosure at hcl
  simp only [hw, ite_true] at hcl
  exact flatMap_nil_mem (stepBreaks g · false) D.steps step (append_nil_right hcl) hs

/-- A stored tuple whose role is at `from` is sent to another stored tuple. -/
theorem stepBreaks_closed (g : CompatGroup) (step : CompatStep) (tup : List RoleState)
    (h : stepBreaks g step false = []) (ht : tup ∈ g.allowed)
    (hrole : g.roles.elem step.template = true)
    (hf : lookupRole tup step.template = some step.fromState) :
    tupleMem g.allowed (substRole tup step.template step.toState) = true := by
  have hall := (List.filterMap_eq_nil_iff).mp h tup ht
  simp [stepBreaks, hrole, hf] at hall
  exact hall (List.elem_iff.mp hrole)

theorem lookup_subst_other (t : List RoleState) (role state r : String) (h : r ≠ role) :
    lookupRole (substRole t role state) r = lookupRole t r := by
  induction t with
  | nil => simp [substRole, lookupRole]
  | cons rs ts ih =>
    by_cases hq : rs.role = r
    · by_cases hr : rs.role = role
      · exact absurd (hq.symm.trans hr) h
      · simp [substRole, lookupRole, List.findSome?_cons, hr, hq, h]
    · by_cases hr : rs.role = role
      · have hne : role ≠ r := Ne.symm h
        simp [substRole, lookupRole, List.findSome?_cons, hr, hq, hne]
        simpa [lookupRole, substRole] using ih
      · simp [substRole, lookupRole, List.findSome?_cons, hr, hq]
        simpa [lookupRole, substRole] using ih

theorem lookup_subst_self (t : List RoleState) (role s state : String)
    (h : lookupRole t role = some s) :
    lookupRole (substRole t role state) role = some state := by
  induction t with
  | nil => simp [lookupRole] at h
  | cons rs ts ih =>
    by_cases hr : rs.role = role
    · simp [substRole, lookupRole, List.findSome?_cons, hr]
    · simp [substRole, lookupRole, List.findSome?_cons, hr] at h ⊢
      exact ih h

theorem lookup_mem (t : List RoleState) (role s : String) (h : lookupRole t role = some s) :
    ∃ rs ∈ t, rs.role = role ∧ rs.state = s := by
  unfold lookupRole at h
  induction t with
  | nil => simp at h
  | cons rs ts ih =>
    simp [List.findSome?_cons] at h
    by_cases hr : rs.role = role
    · simp [hr] at h
      exact ⟨rs, List.Mem.head _, hr, h⟩
    · simp [hr] at h
      obtain ⟨rs', hm, hrole, hs⟩ := ih h
      exact ⟨rs', List.Mem.tail _ hm, hrole, hs⟩

theorem tuple_agree (a tup : List RoleState) (h : tupleMem [a] tup = true) (role s : String)
    (hl : lookupRole tup role = some s) : lookupRole a role = some s := by
  simp [tupleMem, List.any_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨rs, hrs, hrole, hs⟩ := lookup_mem tup role s hl
  have := h.1 rs hrs
  simpa [hrole, hs, beq_iff_eq] using this

end Deadlock
