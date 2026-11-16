import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

def countFrom (sender : InstId) : List Msg → Nat
  | [] => 0
  | m :: ms => (if m.sender = sender then 1 else 0) + countFrom sender ms

def countParked (sender : InstId) : List Parked → Nat
  | [] => 0
  | p :: ps => (if p.sender = sender then 1 else 0) + countParked sender ps

def slot (st : InstId → Actor) (dstName : String) (sender id : InstId) : Nat :=
  if tname id == dstName then countFrom sender (st id).box + countParked sender (st id).parked else 0

def owed (st : InstId → Actor) (dstName : String) (sender : InstId) : List InstId → Nat
  | [] => 0
  | id :: ids => slot st dstName sender id + owed st dstName sender ids

theorem countFrom_append (sender : InstId) (ms : List Msg) (m : Msg) :
    countFrom sender (ms ++ [m]) = countFrom sender ms + if m.sender = sender then 1 else 0 := by
  induction ms with
  | nil => simp [countFrom]
  | cons h t ih => simp [countFrom, ih, Nat.add_assoc, Nat.add_left_comm]

theorem countParked_append (sender : InstId) (ps : List Parked) (p : Parked) :
    countParked sender (ps ++ [p]) = countParked sender ps + if p.sender = sender then 1 else 0 := by
  induction ps with
  | nil => simp [countParked]
  | cons h t ih => simp [countParked, ih, Nat.add_assoc, Nat.add_left_comm]

theorem countParked_zero_sender (sender : InstId) (ps : List Parked)
    (h : countParked sender ps = 0) : ∀ p ∈ ps, p.sender ≠ sender := by
  induction ps with
  | nil =>
    intro p hp
    cases hp
  | cons p ps ih =>
    simp only [countParked] at h
    have hhead : p.sender ≠ sender := by
      intro heq
      simp [heq] at h
    have htail : countParked sender ps = 0 := by
      by_cases heq : p.sender = sender
      · exact absurd heq hhead
      · simp [heq] at h
        exact h
    intro q hq
    cases hq with
    | head => exact hhead
    | tail _ hq => exact ih htail q hq

theorem countFrom_cons_tail (sender : InstId) (m : Msg) (ms : List Msg) :
    countFrom sender (m :: ms) = (if m.sender = sender then 1 else 0) + countFrom sender ms := by
  simp [countFrom]

theorem owed_nil (st : InstId → Actor) (dstName : String) (sender : InstId) :
    owed st dstName sender [] = 0 := rfl

theorem owed_cons (st : InstId → Actor) (dstName : String) (sender id : InstId) (ids : List InstId) :
    owed st dstName sender (id :: ids) = slot st dstName sender id + owed st dstName sender ids := rfl

theorem slot_setActor_other (st : InstId → Actor) (dstName : String) (sender id j : InstId) (a : Actor)
    (h : j ≠ id) :
    slot (fun i => if i = id then a else st i) dstName sender j = slot st dstName sender j := by
  simp [slot, h]

theorem owed_setActor_out (st : InstId → Actor) (dstName : String) (sender id : InstId) (a : Actor)
    (ids : List InstId) (h : id ∉ ids) :
    owed (fun i => if i = id then a else st i) dstName sender ids = owed st dstName sender ids := by
  induction ids with
  | nil => rfl
  | cons j js ih =>
    have hnot : ¬ (id = j ∨ id ∈ js) := by simpa [List.mem_cons] using h
    have hj : j ≠ id := fun heq => hnot (Or.inl heq.symm)
    have hjs : id ∉ js := fun hin => hnot (Or.inr hin)
    simp only [owed_cons, slot_setActor_other _ _ _ _ _ _ hj, ih hjs]

theorem owed_replace_head (st : InstId → Actor) (dstName : String) (sender id : InstId) (a : Actor)
    (ids : List InstId) (h : id ∉ ids) :
    owed (fun i => if i = id then a else st i) dstName sender (id :: ids)
      + slot st dstName sender id
    = owed st dstName sender (id :: ids)
      + slot (fun i => if i = id then a else st i) dstName sender id := by
  simp only [owed_cons, owed_setActor_out _ _ _ _ _ ids h]
  omega

/-- Replacing the unique roster entry `id` changes `owed` exactly by the change in that entry's slot. -/
theorem owed_replace (st : InstId → Actor) (dstName : String) (sender id : InstId) (a : Actor)
    (ids : List InstId) (nodup : ids.Nodup) (hmem : id ∈ ids) :
    owed (fun i => if i = id then a else st i) dstName sender ids + slot st dstName sender id
      = owed st dstName sender ids + slot (fun i => if i = id then a else st i) dstName sender id := by
  induction ids with
  | nil => cases hmem
  | cons j js ih =>
    have hcons := (List.nodup_cons).mp nodup
    cases hmem with
    | head =>
      exact owed_replace_head st dstName sender id a js hcons.1
    | tail _ htail =>
      have hj : j ≠ id := by
        intro heq
        subst heq
        exact hcons.1 htail
      have ih' := ih hcons.2 htail
      simp only [owed_cons, slot_setActor_other _ _ _ _ _ _ hj]
      omega

theorem slot_eq_box (st : InstId → Actor) (dstName : String) (sender id : InstId) (a : Actor)
    (hb : a.box = (st id).box) (hp : a.parked = (st id).parked) :
    slot (fun i => if i = id then a else st i) dstName sender id = slot st dstName sender id := by
  simp [slot, hb, hp]

theorem foldl_max_ge_acc {β : Type} (f : β → Nat) (xs : List β) (acc : Nat) :
    acc ≤ xs.foldl (fun m y => Nat.max m (f y)) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left acc (f y)) (ih _)

theorem mem_le_foldl_max {β : Type} (f : β → Nat) (xs : List β) (x : β) (hx : x ∈ xs) (acc : Nat) :
    f x ≤ xs.foldl (fun m y => Nat.max m (f y)) acc := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases hx with
    | head =>
      exact Nat.le_trans (Nat.le_max_right acc (f x)) (foldl_max_ge_acc f ys _)
    | tail _ h =>
      exact ih h _

theorem debt_le_budget (D : Description) (template state dst : String)
    (h : ∃ t, templateOf D template = some t ∧ state ∈ t.states) :
    debt D template state dst ≤ budget D template dst := by
  obtain ⟨t, ht, hmem⟩ := h
  unfold budget
  simp [ht]
  exact mem_le_foldl_max (fun st => debt D template st dst) t.states state hmem 0

def floorState (D : Description) (template state dst : String) : Nat :=
  budget D template dst - debt D template state dst

theorem floor_le_budget (D : Description) (template state dst : String) :
    floorState D template state dst ≤ budget D template dst :=
  Nat.sub_le _ _

/-- Sum of per-instance debts of the actors currently on the roster, into `dstName`. -/
def debtSum (D : Description) (st : InstId → Actor) (dstName : String) : List InstId → Nat
  | [] => 0
  | id :: ids => debt D (tname id) (st id).typestate dstName + debtSum D st dstName ids

theorem owed_append (st : InstId → Actor) (dstName : String) (sender : InstId) (ids : List InstId) (id : InstId) :
    owed st dstName sender (ids ++ [id]) = owed st dstName sender ids + slot st dstName sender id := by
  induction ids with
  | nil => simp [owed]
  | cons j js ih => simp [owed, ih, Nat.add_assoc]

theorem slot_same_mail (st : InstId → Actor) (dstName : String) (sender id : InstId) (a : Actor)
    (hb : a.box = (st id).box) (hp : a.parked = (st id).parked) :
    slot (fun i => if i = id then a else st i) dstName sender id = slot st dstName sender id :=
  slot_eq_box st dstName sender id a hb hp

theorem countFrom_append_one (sender : InstId) (ms : List Msg) (m : Msg) (h : m.sender = sender) :
    countFrom sender (ms ++ [m]) = countFrom sender ms + 1 := by
  simpa [h] using countFrom_append sender ms m

theorem slot_append_msg (st : InstId → Actor) (dstName : String) (sender id : InstId) (msg : Msg)
    (hname : tname id == dstName) (hs : msg.sender = sender) :
    slot (fun i => if i = id then { st id with box := (st id).box ++ [msg] } else st i) dstName sender id
      = slot st dstName sender id + 1 := by
  have hp : ({ st id with box := (st id).box ++ [msg] }).parked = (st id).parked := rfl
  simp only [slot, hname, hp]
  simp [countFrom_append_one sender (st id).box msg hs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem owed_mail_eq (st1 st2 : InstId → Actor) (dstName : String) (sender : InstId) (ids : List InstId)
    (h : ∀ id ∈ ids, (st1 id).box = (st2 id).box ∧ (st1 id).parked = (st2 id).parked) :
    owed st1 dstName sender ids = owed st2 dstName sender ids := by
  induction ids with
  | nil => rfl
  | cons j js ih =>
    have hj := h j (List.Mem.head _)
    have hjs : ∀ id ∈ js, (st1 id).box = (st2 id).box ∧ (st1 id).parked = (st2 id).parked :=
      fun id hid => h id (List.Mem.tail _ hid)
    simp only [owed_cons, slot]
    rw [hj.1, hj.2, ih hjs]

theorem owed_append_msg (st : InstId → Actor) (dstName : String) (sender dst : InstId) (msg : Msg)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : dst ∈ roster)
    (hname : tname dst == dstName) (hs : msg.sender = sender) :
    owed (fun i => if i = dst then { st dst with box := (st dst).box ++ [msg] } else st i) dstName sender roster
      = owed st dstName sender roster + 1 := by
  have hcross := owed_replace st dstName sender dst { st dst with box := (st dst).box ++ [msg] } roster nodup hmem
  have hslot := slot_append_msg st dstName sender dst msg hname hs
  omega

theorem charge_tokens (a : Actor) (dst : String) (h : 1 ≤ a.tokens dst) :
    (chargeSender a dst).tokens dst + 1 = a.tokens dst := by
  simp [chargeSender, bumpToken]
  omega

end Deadlock
