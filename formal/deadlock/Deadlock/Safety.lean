import Deadlock.Local

set_option autoImplicit false

namespace Deadlock

/-- Safety invariant used by deadlock freedom.
`balance` is Lemma 1's accounting: messages a sender has in flight equal the
slots it has spent. `budgetOk` says the program still to run fits in the slots
that state is allowed to spend. -/
structure Hold (I : Impl) (w : World) : Prop where
  nodup : w.roster.Nodup
  aliveIn : ∀ id, (w.st id).life = .alive → id ∈ w.roster
  balance : ∀ s d, s ∈ w.roster →
    owed w.st d s w.roster + (w.st s).tokens d = budget I.desc (tname s) d
  noCrash : ∀ id, (w.st id).phase ≠ .crashed

theorem owed_zero_of_empty (st : InstId → Actor) (dstName : String) (sender : InstId) (ids : List InstId)
    (h : ∀ id ∈ ids, (st id).box = [] ∧ (st id).parked = []) :
    owed st dstName sender ids = 0 := by
  induction ids with
  | nil => rfl
  | cons j js ih =>
    have hj := h j (List.Mem.head _)
    simp only [owed_cons, slot, hj.1, hj.2, countFrom, countParked]
    have ih' := ih (fun id hid => h id (List.Mem.tail _ hid))
    by_cases ht : tname j == dstName
    · simp [ht, ih']
    · simp [ht, ih']

theorem foldDedup_len_le {α : Type} [DecidableEq α] (acc xs : List α) :
    (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length
      ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases hx : acc.elem x
    · simp only [hx, List.length_cons]
      have ih' := ih (acc ++ [x])
      simp [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_left_comm] at ih' ⊢
      rw [show acc.length + (1 + xs.length) = xs.length + (acc.length + 1) from by omega] at ih'
      exact ih'
    · simp only [hx, List.length_cons]
      exact Nat.le_trans (ih acc) (Nat.add_le_add_left (Nat.le_succ xs.length) acc.length)

theorem dedup_length_le {α : Type} [DecidableEq α] (xs : List α) :
    (dedup xs).length ≤ xs.length := by
  simpa [dedup, Nat.zero_add] using foldDedup_len_le ([] : List α) xs

theorem nameFails_len (D : Description) (h : nameFails D = []) :
    (dedup (D.templates.map (·.name))).length = (D.templates.map (·.name)).length := by
  unfold nameFails at h
  by_cases hq : (D.templates.map (·.name)).length == (dedup (D.templates.map (·.name))).length
  · simp only [hq, ite_true] at h
    have heq : (D.templates.map (·.name)).length = (dedup (D.templates.map (·.name))).length :=
      (beq_iff_eq).mp hq
    exact heq.symm
  · simp only [hq, ite_false] at h
    simp at h

end Deadlock
