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


end Deadlock
