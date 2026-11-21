import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

/-! The group relation is untrusted. `compatFails = []` checks the initial tuple
and closure under the listed typestate steps. Outcome landings are not fields of
the description, so that check does not see them. `landingFails` does: every
nonempty `toNotAdmitted` / `toTimedOut` / `toTimeout` / `toFull` / `toGone` is
a state the stored rows must already be closed under, via `pairBreaks`. Absent
and dead roles are not read as `initial`: the tuple is required only while every
role is alive. -/

def roleTuple (w : World) (g : CompatGroup) : List RoleState :=
  g.roles.map fun r => { role := r, state := (w.st (.core r)).typestate }

def groupLive (w : World) (g : CompatGroup) : Prop :=
  ∀ r ∈ g.roles, (w.st (.core r)).life = .alive

/-- `s` is a state `pickState` can write after `tr` has been entered. Empty
outcome fields are not states; they mean `toState`. -/
def landsAt (tr : Transition) (s : String) : Prop :=
  s = tr.toState ∨
    s ≠ "" ∧ (s = tr.toNotAdmitted ∨ s = tr.toTimedOut ∨ s = tr.toTimeout ∨
      s = tr.toFull ∨ s = tr.toGone)

/-- Tuples the checker stored, closed under declared steps and under moves
inside one transition's landing set. A later partner step is included, because
the closure is inductive. -/
inductive RowOk (I : Impl) (g : CompatGroup) : List RoleState → Prop where
  | raw {tup : List RoleState} : tupleMem g.allowed tup = true → RowOk I g tup
  | step {tup : List RoleState} {step : CompatStep} :
      RowOk I g tup →
      step ∈ I.desc.steps →
      g.roles.elem step.template = true →
      lookupRole tup step.template = some step.fromState →
      RowOk I g (substRole tup step.template step.toState)
  | land {tup : List RoleState} {tr : Transition} {s0 s1 : String} :
      RowOk I g tup →
      tr ∈ I.transitions →
      g.roles.elem tr.template = true →
      lookupRole tup tr.template = some s0 →
      landsAt tr s0 →
      landsAt tr s1 →
      RowOk I g (substRole tup tr.template s1)

def CompatInv (I : Impl) (w : World) : Prop :=
  ∀ g ∈ compatGroups I.desc.compatibility, groupLive w g →
    RowOk I g (roleTuple w g)

def contTy (a : Actor) : Prop :=
  match a.phase with
  | .run k => a.typestate = k.toState
  | .parked _ _ k => a.typestate = k.toState
  | .awaitReply _ k => a.typestate = k.toState
  | .awaitEffect k => a.typestate = k.toState
  | .awaitPeer k => a.typestate = k.toState
  | _ => True

def CInv (I : Impl) (w : World) : Prop :=
  CompatInv I w ∧ ∀ id, contTy (w.st id)

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
