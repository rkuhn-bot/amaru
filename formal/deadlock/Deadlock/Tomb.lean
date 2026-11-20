/-
One tombstone per child slot, for a world that already satisfies `Hold`.

`tmb_seal_room` is that numeric fact: a pending seal has room on the live
parent's lane when the slot account is inside `prioSized`. It is not true of
every world `GraphOk` and `LocalOk` can reach. Two live generations of one
supervisor can each spawn the same slot, and both seals offer their
tombstone to the older generation. `Deadlock/Counterexample.lean` is that
run; `offerPrio` crashes. The reachable wrapper stays unproved.
-/

import Deadlock.Local

set_option autoImplicit false

namespace Deadlock

/-! List facts. -/

theorem tmb_mem_append_left {α} {xs ys : List α} {x : α} (h : x ∈ xs) : x ∈ xs ++ ys := by
  exact List.mem_append.mpr (Or.inl h)

theorem tmb_mem_append_right {α} {xs ys : List α} {x : α} (h : x ∈ ys) : x ∈ xs ++ ys := by
  exact List.mem_append.mpr (Or.inr h)

theorem tmb_foldl_mem {α} [DecidableEq α] (acc xs : List α) (x : α)
    (h : x ∈ acc ∨ x ∈ xs) :
    x ∈ xs.foldl (fun acc y => if acc.elem y then acc else acc ++ [y]) acc := by
  induction xs generalizing acc with
  | nil =>
    simp at h
    simpa using h
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases h with
    | inl hx =>
      by_cases he : acc.elem y = true
      · simp only [he, ite_true]
        exact ih acc (Or.inl hx)
      · have he' : acc.elem y = false := by
          cases hbit : acc.elem y <;> simp_all
        simp only [he', ite_false]
        exact ih (acc ++ [y]) (Or.inl (List.mem_append_left _ hx))
    | inr hx =>
      by_cases he : acc.elem y = true
      · simp only [he, ite_true]
        cases List.mem_cons.mp hx with
        | inl heq =>
          subst heq
          exact ih acc (Or.inl (List.elem_iff.mp he))
        | inr ht => exact ih acc (Or.inr ht)
      · have he' : acc.elem y = false := by
          cases hbit : acc.elem y <;> simp_all
        simp only [he', ite_false]
        cases List.mem_cons.mp hx with
        | inl heq =>
          subst heq
          exact ih (acc ++ [x]) (Or.inl (List.mem_append_right _ (by simp)))
        | inr ht => exact ih (acc ++ [y]) (Or.inr ht)

theorem tmb_mem_dedup {α} [DecidableEq α] (xs : List α) (x : α) (h : x ∈ xs) : x ∈ dedup xs := by
  simpa [dedup] using tmb_foldl_mem [] xs x (Or.inr h)

theorem tmb_nodup_sub_length {α} [DecidableEq α] (xs ys : List α)
    (hnd : xs.Nodup) (hsub : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ ys := hsub x (List.mem_cons.mpr (Or.inl rfl))
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hfresh : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hsub' : ∀ z, z ∈ xs → z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := by
        intro heq
        exact hfresh (heq ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons.mpr (Or.inr hz)))
    have ih' := ih (ys.erase x) hnd' hsub'
    have herase : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hx
    have hpos : 1 ≤ ys.length := Nat.succ_le_of_lt (List.length_pos_of_mem hx)
    have hsucc : xs.length + 1 ≤ ys.length := by
      have htail : xs.length ≤ ys.length - 1 := by simpa [herase] using ih'
      omega
    simpa using hsucc

theorem tmb_filter_split {α} (p : α → Bool) (xs : List α) :
    xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem tmb_filter_append_false {α} (p : α → Bool) (xs : List α) (x : α) (hp : p x = false) :
    (xs ++ [x]).filter p = xs.filter p := by
  induction xs with
  | nil => simp [hp]
  | cons y ys ih =>
    cases hpy : p y <;> simp [hpy, ih, hp]

/-! Declared priority labels. -/

def tmb_laneLabels (ms : List Msg) : List String :=
  (ms.filter (fun m => !m.tombstone)).map (·.label)

theorem tmb_self_in_collected (trs : List Transition) (template : String) (tr : Transition)
    (hm : tr ∈ trs) (ht : tr.template = template) (l : String) (hl : l ∈ selfLabels tr.program) :
    l ∈ (trs.filterMap fun t =>
      if t.template == template then some (selfLabels t.program) else none).flatten := by
  induction trs with
  | nil => cases hm
  | cons t ts ih =>
    cases hm with
    | head =>
      simp [List.filterMap, List.flatten, ht, hl, List.mem_append]
    | tail _ ht' =>
      have ih' := ih ht'
      by_cases hif : (t.template == template) = true
      · simp [List.filterMap, List.flatten, hif, List.mem_append] at ih' ⊢
        exact Or.inr ih'
      · have hif' : (t.template == template) = false := by
          cases hbit : t.template == template <;> simp_all
        simp [List.filterMap, List.flatten, hif'] at ih' ⊢
        exact ih'

theorem tmb_cell_in_collected (trs : List Transition) (reader : String) (tr : Transition)
    (hm : tr ∈ trs) (l : String) (hl : l ∈ cellWakeLabels reader tr.program) :
    l ∈ (trs.map fun t => cellWakeLabels reader t.program).flatten := by
  induction trs with
  | nil => cases hm
  | cons t ts ih =>
    cases hm with
    | head =>
      simp [List.flatten, hl, List.mem_append]
    | tail _ ht' =>
      have ih' := ih ht'
      simp [List.flatten, List.mem_append] at ih' ⊢
      exact Or.inr ih'

theorem tmb_self_in_prio (I : Impl) (tr : Transition) (hm : tr ∈ I.transitions) (l : String)
    (hl : l ∈ selfLabels tr.program) : l ∈ prioLabels I tr.template := by
  have hcol := tmb_self_in_collected I.transitions tr.template tr hm rfl l hl
  have hmem : l ∈
      (I.transitions.filterMap fun t =>
        if t.template == tr.template then some (selfLabels t.program) else none).flatten ++
      cellLabels I.desc tr.template ++
      (I.transitions.map fun t => cellWakeLabels tr.template t.program).flatten := by
    exact tmb_mem_append_left (tmb_mem_append_left hcol)
  simpa [prioLabels] using tmb_mem_dedup _ l hmem

theorem tmb_cell_in_prio (I : Impl) (reader : String) (tr : Transition) (hm : tr ∈ I.transitions)
    (l : String) (hl : l ∈ cellWakeLabels reader tr.program) : l ∈ prioLabels I reader := by
  have hcol := tmb_cell_in_collected I.transitions reader tr hm l hl
  have hmem : l ∈
      (I.transitions.filterMap fun t =>
        if t.template == reader then some (selfLabels t.program) else none).flatten ++
      cellLabels I.desc reader ++
      (I.transitions.map fun t => cellWakeLabels reader t.program).flatten := by
    exact tmb_mem_append_right hcol
  simpa [prioLabels] using tmb_mem_dedup _ l hmem

theorem tmb_self_cons (e : Eff) (es : List Eff) (l : String) (hl : l ∈ selfLabels es) :
    l ∈ selfLabels (e :: es) := by
  simp [selfLabels, tmb_mem_append_right hl]

theorem tmb_cell_cons (reader : String) (e : Eff) (es : List Eff) (l : String)
    (hl : l ∈ cellWakeLabels reader es) : l ∈ cellWakeLabels reader (e :: es) := by
  simp [cellWakeLabels, tmb_mem_append_right hl]

theorem tmb_self_try_full (d lab : String) (hint : Nat) (onFull onGone es : List Eff) (l : String)
    (hl : l ∈ selfLabels onFull) :
    l ∈ selfLabels (.trySend d lab hint onFull onGone :: es) := by
  simp [selfLabels, effSelf]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_self_try_gone (d lab : String) (hint : Nat) (onFull onGone es : List Eff) (l : String)
    (hl : l ∈ selfLabels onGone) :
    l ∈ selfLabels (.trySend d lab hint onFull onGone :: es) := by
  simp [selfLabels, effSelf]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_self_call_na (d lab : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (l : String) (hl : l ∈ selfLabels onNotAdmitted) :
    l ∈ selfLabels (.call d lab hint onNotAdmitted onTimedOut :: es) := by
  simp [selfLabels, effSelf]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_self_call_to (d lab : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (l : String) (hl : l ∈ selfLabels onTimedOut) :
    l ∈ selfLabels (.call d lab hint onNotAdmitted onTimedOut :: es) := by
  simp [selfLabels, effSelf]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_self_peer (onTimeout es : List Eff) (l : String) (hl : l ∈ selfLabels onTimeout) :
    l ∈ selfLabels (.peer onTimeout :: es) := by
  simp [selfLabels, effSelf]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_cell_try_full (reader d lab : String) (hint : Nat) (onFull onGone es : List Eff)
    (l : String) (hl : l ∈ cellWakeLabels reader onFull) :
    l ∈ cellWakeLabels reader (.trySend d lab hint onFull onGone :: es) := by
  simp [cellWakeLabels, effWake]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_cell_try_gone (reader d lab : String) (hint : Nat) (onFull onGone es : List Eff)
    (l : String) (hl : l ∈ cellWakeLabels reader onGone) :
    l ∈ cellWakeLabels reader (.trySend d lab hint onFull onGone :: es) := by
  simp [cellWakeLabels, effWake]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_cell_call_na (reader d lab : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (l : String) (hl : l ∈ cellWakeLabels reader onNotAdmitted) :
    l ∈ cellWakeLabels reader (.call d lab hint onNotAdmitted onTimedOut :: es) := by
  simp [cellWakeLabels, effWake]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_cell_call_to (reader d lab : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (l : String) (hl : l ∈ cellWakeLabels reader onTimedOut) :
    l ∈ cellWakeLabels reader (.call d lab hint onNotAdmitted onTimedOut :: es) := by
  simp [cellWakeLabels, effWake]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_cell_peer (reader : String) (onTimeout es : List Eff) (l : String)
    (hl : l ∈ cellWakeLabels reader onTimeout) :
    l ∈ cellWakeLabels reader (.peer onTimeout :: es) := by
  simp [cellWakeLabels, effWake]
  first
    | exact Or.inl hl
    | exact Or.inr hl
    | exact Or.inl (Or.inl hl)
    | exact Or.inl (Or.inr hl)
    | exact Or.inr (Or.inl hl)
    | exact Or.inr (Or.inr hl)

theorem tmb_self_head (l : String) (es : List Eff) : l ∈ selfLabels (.selfSchedule l :: es) := by
  simp [selfLabels, effSelf]

theorem tmb_cell_head (dst label : String) (v : Nat) (es : List Eff) :
    label ∈ cellWakeLabels dst (.cell dst label v :: es) := by
  simp [cellWakeLabels, effWake]

structure ListsDeclared (I : Impl) (template : String) (es : List Eff) : Prop where
  sched : ∀ l, l ∈ selfLabels es → l ∈ prioLabels I template
  wake : ∀ reader l, l ∈ cellWakeLabels reader es → l ∈ prioLabels I reader

theorem ListsDeclared.nil (I : Impl) (template : String) : ListsDeclared I template [] := by
  refine ⟨?_, ?_⟩
  · intro l hl
    simp [selfLabels] at hl
  · intro reader l hl
    simp [cellWakeLabels] at hl

theorem ListsDeclared.tail (I : Impl) (template : String) (e : Eff) (es : List Eff)
    (h : ListsDeclared I template (e :: es)) : ListsDeclared I template es := by
  refine ⟨?_, ?_⟩
  · intro l hl
    exact h.sched l (tmb_self_cons e es l hl)
  · intro reader l hl
    exact h.wake reader l (tmb_cell_cons reader e es l hl)

theorem ListsDeclared.of_mem (I : Impl) (tr : Transition) (hm : tr ∈ I.transitions) :
    ListsDeclared I tr.template tr.program := by
  refine ⟨?_, ?_⟩
  · intro l hl
    exact tmb_self_in_prio I tr hm l hl
  · intro reader l hl
    exact tmb_cell_in_prio I reader tr hm l hl

structure ContDeclared (I : Impl) (template : String) (k : Cont) : Prop where
  rest : ListsDeclared I template k.rest
  na : ListsDeclared I template k.onNotAdmitted
  to : ListsDeclared I template k.onTimedOut
  timeout : ListsDeclared I template k.onTimeout

def phaseDeclared (I : Impl) (template : String) : Phase → Prop
  | .run k => ContDeclared I template k
  | .parked _ _ k => ContDeclared I template k
  | .awaitReply _ k => ContDeclared I template k
  | .awaitEffect k => ContDeclared I template k
  | .awaitPeer k => ContDeclared I template k
  | .idle => True
  | .crashed => True

theorem ContDeclared.after (I : Impl) (template : String) (k : Cont) (e : Eff) (es : List Eff)
    (hk : k.rest = e :: es) (h : ContDeclared I template k) :
    ContDeclared I template (afterHead k) := by
  have htail : (afterHead k).rest = es := by simp [afterHead, hk]
  have hna : (afterHead k).onNotAdmitted = k.onNotAdmitted := by simp [afterHead]
  have hto : (afterHead k).onTimedOut = k.onTimedOut := by simp [afterHead]
  have htimeout : (afterHead k).onTimeout = k.onTimeout := by simp [afterHead]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htail]
    have hrest : ListsDeclared I template (e :: es) := by simpa [hk] using h.rest
    exact hrest.tail
  · simpa [hna] using h.na
  · simpa [hto] using h.to
  · simpa [htimeout] using h.timeout

theorem ContDeclared.tryFull (I : Impl) (template : String) (k : Cont)
    (d lab : String) (hint : Nat) (onFull onGone es : List Eff)
    (hk : k.rest = .trySend d lab hint onFull onGone :: es) (h : ContDeclared I template k) :
    ContDeclared I template { afterHead k with rest := onFull } := by
  have hafter := ContDeclared.after I template k _ _ hk h
  have hprog : ListsDeclared I template (.trySend d lab hint onFull onGone :: es) := by
    simpa [hk] using h.rest
  refine ⟨⟨?_, ?_⟩, hafter.na, hafter.to, hafter.timeout⟩
  · intro l hl
    exact hprog.sched l (tmb_self_try_full d lab hint onFull onGone es l hl)
  · intro reader l hl
    exact hprog.wake reader l (tmb_cell_try_full reader d lab hint onFull onGone es l hl)

theorem ContDeclared.tryGone (I : Impl) (template : String) (k : Cont)
    (d lab : String) (hint : Nat) (onFull onGone es : List Eff)
    (hk : k.rest = .trySend d lab hint onFull onGone :: es) (h : ContDeclared I template k) :
    ContDeclared I template { afterHead k with rest := onGone } := by
  have hafter := ContDeclared.after I template k _ _ hk h
  have hprog : ListsDeclared I template (.trySend d lab hint onFull onGone :: es) := by
    simpa [hk] using h.rest
  refine ⟨⟨?_, ?_⟩, hafter.na, hafter.to, hafter.timeout⟩
  · intro l hl
    exact hprog.sched l (tmb_self_try_gone d lab hint onFull onGone es l hl)
  · intro reader l hl
    exact hprog.wake reader l (tmb_cell_try_gone reader d lab hint onFull onGone es l hl)

theorem ContDeclared.callWait (I : Impl) (template : String) (k : Cont)
    (d lab : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (hk : k.rest = .call d lab hint onNotAdmitted onTimedOut :: es)
    (h : ContDeclared I template k) :
    ContDeclared I template
      { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } := by
  have hafter := ContDeclared.after I template k _ _ hk h
  have hprog : ListsDeclared I template (.call d lab hint onNotAdmitted onTimedOut :: es) := by
    simpa [hk] using h.rest
  refine ⟨hafter.rest, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hafter.timeout⟩
  · intro l hl
    exact hprog.sched l (tmb_self_call_na d lab hint onNotAdmitted onTimedOut es l hl)
  · intro reader l hl
    exact hprog.wake reader l (tmb_cell_call_na reader d lab hint onNotAdmitted onTimedOut es l hl)
  · intro l hl
    exact hprog.sched l (tmb_self_call_to d lab hint onNotAdmitted onTimedOut es l hl)
  · intro reader l hl
    exact hprog.wake reader l (tmb_cell_call_to reader d lab hint onNotAdmitted onTimedOut es l hl)

theorem ContDeclared.peerWait (I : Impl) (template : String) (k : Cont) (onTimeout es : List Eff)
    (hk : k.rest = .peer onTimeout :: es) (h : ContDeclared I template k) :
    ContDeclared I template { afterHead k with onTimeout := onTimeout } := by
  have hafter := ContDeclared.after I template k _ _ hk h
  have hprog : ListsDeclared I template (.peer onTimeout :: es) := by simpa [hk] using h.rest
  refine ⟨hafter.rest, hafter.na, hafter.to, ⟨?_, ?_⟩⟩
  · intro l hl
    exact hprog.sched l (tmb_self_peer onTimeout es l hl)
  · intro reader l hl
    exact hprog.wake reader l (tmb_cell_peer reader onTimeout es l hl)

def tmb_programCont (tr : Transition) (replyTo : Option InstId) : Cont where
  rest := tr.program
  toState := tr.toState
  replyTo := replyTo
  toNotAdmitted := tr.toNotAdmitted
  toTimedOut := tr.toTimedOut
  toTimeout := tr.toTimeout
  toFull := tr.toFull
  toGone := tr.toGone

theorem ContDeclared.program (I : Impl) (tr : Transition) (hm : tr ∈ I.transitions)
    (replyTo : Option InstId) : ContDeclared I tr.template (tmb_programCont tr replyTo) := by
  have hprog := ListsDeclared.of_mem I tr hm
  refine ⟨hprog, ListsDeclared.nil I tr.template, ListsDeclared.nil I tr.template,
    ListsDeclared.nil I tr.template⟩

theorem phaseDeclared_idle (I : Impl) (template : String) : phaseDeclared I template .idle := by
  simp [phaseDeclared]

theorem phaseDeclared_run (I : Impl) (template : String) (k : Cont)
    (h : ContDeclared I template k) : phaseDeclared I template (.run k) := h

/-! Slots a parent's lane can be asked to remember. -/

def lifeHold (a : Actor) : Bool :=
  a.life == .alive || (a.life == .shuttingDown && a.pendingTombstone)

def occupant (a : Actor) : Bool :=
  a.life == .alive || a.life == .shuttingDown

/-- `(name, key)` is a child this parent still has to account for: a live or
armed child, or a tombstone still sitting on the lane. -/
def holdsSlot (D : Description) (w : World) (parent : InstId) (name : String) (k : Nat) : Bool :=
  (w.roster.any fun c =>
    isChild D parent c &&
      match c with
      | .peer n key _ => n == name && key == k && lifeHold (w.st c)
      | .core _ => false) ||
    slotTombstoneQueued w parent name k

def legalSlots (D : Description) (parent : InstId) (N : Nat) : List (String × Nat) :=
  D.templates.flatMap fun c =>
    if c.supervisor == tname parent && c.tombstone != "" then
      match parent with
      | .core _ =>
        let n := if c.slots == 0 then N else c.slots
        (List.range n).map fun k => (c.name, k)
      | .peer _ pk _ => [(c.name, pk)]
    else []

def tombSlots (ms : List Msg) : List (String × Nat) :=
  ms.filterMap fun m =>
    if m.tombstone then
      match m.sender with
      | .peer n k _ => some (n, k)
      | .core _ => none
    else none

theorem legal_mem_core (D : Description) (parent child : String) (N k : Nat) (c : Template)
    (hc : c ∈ D.templates) (hname : c.name = child) (hsup : c.supervisor = parent)
    (htomb : c.tombstone ≠ "") (hk : k < (if c.slots == 0 then N else c.slots)) :
    (child, k) ∈ legalSlots D (.core parent) N := by
  have hflat : (child, k) ∈ D.templates.flatMap (fun t =>
      if t.supervisor == parent && t.tombstone != "" then
        (List.range (if t.slots == 0 then N else t.slots)).map fun i => (t.name, i)
      else []) := by
    refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
    have hsupB : (c.supervisor == parent) = true := by simpa [beq_iff_eq] using hsup
    have htombB : (c.tombstone != "") = true := by
      simpa [bne, beq_iff_eq] using htomb
    have hk' : k < if c.slots = 0 then N else c.slots := by
      simpa [beq_iff_eq] using hk
    simp [hsupB, htombB, List.mem_map, List.mem_range, hname, hk']
  simpa [legalSlots, tname] using hflat

theorem legal_mem_peer (D : Description) (parent child : String) (pk N : Nat) (c : Template)
    (hc : c ∈ D.templates) (hname : c.name = child) (hsup : c.supervisor = parent)
    (htomb : c.tombstone ≠ "") :
    (child, pk) ∈ legalSlots D (.peer parent pk 0) N := by
  have hflat : (child, pk) ∈ D.templates.flatMap (fun t =>
      if t.supervisor == parent && t.tombstone != "" then [(t.name, pk)] else []) := by
    refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
    have hsupB : (c.supervisor == parent) = true := by simpa [beq_iff_eq] using hsup
    have htombB : (c.tombstone != "") = true := by
      simpa [bne, beq_iff_eq] using htomb
    simp [hsupB, htombB, hname]
  simpa [legalSlots, tname] using hflat

def tmb_affineStep (sup : Template) (t : Template) (acc : Affine) : Affine :=
  match sup.multiplicity with
  | .perPeer => { a := acc.a, b := acc.b + slotCount t }
  | .one =>
    if t.slots == 0 then { a := acc.a + 1, b := acc.b }
    else { a := acc.a, b := acc.b + t.slots }



theorem tmb_affineStep_eval (sup t : Template) (acc : Affine) (N : Nat) :
    (tmb_affineStep sup t acc).eval N = acc.eval N +
      match sup.multiplicity with
      | .perPeer => slotCount t
      | .one => if t.slots == 0 then N else t.slots := by
  cases hm : sup.multiplicity with
  | perPeer =>
    simp [tmb_affineStep, Affine.eval, hm, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  | one =>
    cases hs : t.slots == 0
    · simp [tmb_affineStep, Affine.eval, hm, hs, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    · simp [tmb_affineStep, Affine.eval, hm, hs, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega

theorem tmb_slotCount_ge_one (t : Template) : 1 ≤ slotCount t := by
  cases h : t.slots == 0 with
  | true => simp [slotCount, h]
  | false =>
    simp [slotCount, h]
    have hne : t.slots ≠ 0 := by
      intro heq
      have : (t.slots == 0) = true := by simpa [beq_iff_eq] using heq
      simp [this] at h
    exact Nat.one_le_iff_ne_zero.mpr hne

def tmb_keep (parent : InstId) (c : Template) : Bool :=
  c.supervisor == tname parent && c.tombstone != ""

def tmb_leg (parent : InstId) (N : Nat) (c : Template) : Nat :=
  if tmb_keep parent c then
    match parent with
    | .core _ => if c.slots == 0 then N else c.slots
    | .peer _ _ _ => 1
  else 0

def tmb_piece (parent : InstId) (N : Nat) (c : Template) : List (String × Nat) :=
  if c.supervisor == tname parent && c.tombstone != "" then
    match parent with
    | .core _ =>
      let n := if c.slots == 0 then N else c.slots
      (List.range n).map fun k => (c.name, k)
    | .peer _ pk _ => [(c.name, pk)]
  else []

theorem tmb_piece_length (parent : InstId) (N : Nat) (c : Template) :
    (tmb_piece parent N c).length = tmb_leg parent N c := by
  unfold tmb_piece tmb_leg tmb_keep
  by_cases hkeep : (c.supervisor == tname parent && c.tombstone != "") = true
  · simp only [hkeep, ite_true]
    cases parent with
    | core _ => simp [List.length_map, List.length_range]
    | peer _ _ _ => simp
  · have hf : (c.supervisor == tname parent && c.tombstone != "") = false := by
      cases hbit : c.supervisor == tname parent && c.tombstone != "" <;> simp_all
    simp [hf]

theorem tmb_foldl_shift (parent : InstId) (N : Nat) :
    ∀ ts : List Template, ∀ start : Nat,
      List.foldl (fun n c => n + tmb_leg parent N c) start ts =
        start + List.foldl (fun n c => n + tmb_leg parent N c) 0 ts := by
  intro ts
  induction ts with
  | nil =>
    intro start
    simp
  | cons c ts ih =>
    intro start
    simp only [List.foldl_cons, Nat.zero_add]
    have hstart := ih (start + tmb_leg parent N c)
    have hleg := ih (tmb_leg parent N c)
    rw [hstart, hleg]
    omega

theorem tmb_legal_length_go (parent : InstId) (N : Nat) :
    ∀ ts : List Template,
      (List.flatMap (tmb_piece parent N) ts).length =
        List.foldl (fun n c => n + tmb_leg parent N c) 0 ts := by
  intro ts
  induction ts with
  | nil => simp
  | cons c ts ih =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons, ih, Nat.zero_add,
      tmb_piece_length]
    rw [tmb_foldl_shift parent N ts (tmb_leg parent N c)]

theorem tmb_legal_length (D : Description) (parent : InstId) (N : Nat) :
    (legalSlots D parent N).length =
      D.templates.foldl (fun n c => n + tmb_leg parent N c) 0 := by
  unfold legalSlots
  simpa [tmb_piece] using tmb_legal_length_go parent N D.templates

theorem tmb_affine_fold (D : Description) (parentName : String) (sup : Template) (N : Nat)
    (ht : templateOf D parentName = some sup) :
    (tombstoneAffine D parentName).eval N =
      (D.templates.foldl (fun acc t =>
        if t.supervisor == parentName && t.tombstone != "" then tmb_affineStep sup t acc else acc)
        Affine.zero).eval N := by
  simp only [tombstoneAffine, ht, tmb_affineStep]
  rfl

def tmb_role (parent : InstId) : Multiplicity :=
  match parent with
  | .core _ => .one
  | .peer _ _ _ => .perPeer

theorem tmb_leg_le (parent : InstId) (sup : Template) (N : Nat) (c : Template) (acc : Affine)
    (hrole : sup.multiplicity = tmb_role parent) :
    tmb_leg parent N c + acc.eval N ≤
      (if c.supervisor == tname parent && c.tombstone != "" then tmb_affineStep sup c acc
        else acc).eval N := by
  by_cases hkeep : (c.supervisor == tname parent && c.tombstone != "") = true
  · cases parent with
    | core _ =>
      have hm : sup.multiplicity = .one := by simpa [tmb_role] using hrole
      have hstep := tmb_affineStep_eval sup c acc N
      simp only [hm] at hstep
      simp only [tmb_leg, tmb_keep, hkeep, ite_true]
      omega
    | peer _ _ _ =>
      have hm : sup.multiplicity = .perPeer := by simpa [tmb_role] using hrole
      have hstep := tmb_affineStep_eval sup c acc N
      simp only [hm] at hstep
      have hone := tmb_slotCount_ge_one c
      simp only [tmb_leg, tmb_keep, hkeep, ite_true]
      omega
  · have hf : (c.supervisor == tname parent && c.tombstone != "") = false := by
      cases hbit : c.supervisor == tname parent && c.tombstone != "" <;> simp_all
    simp [tmb_leg, tmb_keep, hf]

theorem tmb_fold_le (parent : InstId) (sup : Template) (N : Nat)
    (hrole : sup.multiplicity = tmb_role parent) :
    ∀ ts : List Template, ∀ acc : Affine,
      List.foldl (fun n c => n + tmb_leg parent N c) 0 ts + acc.eval N ≤
        (List.foldl (fun a t =>
          if t.supervisor == tname parent && t.tombstone != "" then tmb_affineStep sup t a else a)
          acc ts).eval N := by
  intro ts
  induction ts with
  | nil =>
    intro acc
    simp [Affine.eval]
  | cons c ts ih =>
    intro acc
    simp only [List.foldl_cons, Nat.zero_add]
    have h1 := tmb_leg_le parent sup N c acc hrole
    have h2 := ih (if c.supervisor == tname parent && c.tombstone != "" then
      tmb_affineStep sup c acc else acc)
    have hadd := tmb_foldl_shift parent N ts (tmb_leg parent N c)
    omega

theorem legal_le_affine (D : Description) (parent : InstId) (N : Nat) (sup : Template)
    (ht : templateOf D (tname parent) = some sup)
    (hrole : sup.multiplicity = tmb_role parent) :
    (legalSlots D parent N).length ≤ (tombstoneAffine D (tname parent)).eval N := by
  rw [tmb_legal_length, tmb_affine_fold D (tname parent) sup N ht]
  have h := tmb_fold_le parent sup N hrole D.templates Affine.zero
  simpa [Affine.eval, Affine.zero] using h

theorem freeGo_lt (w : World) (parent : InstId) (name : String) (n fuel k : Nat)
    (hf : fuel ≤ n) (h : freeGo w parent name n fuel = some k) : k < n := by
  induction fuel generalizing k with
  | zero => simp [freeGo] at h
  | succ fuel ih =>
    by_cases hbit : (slotOccupied w name (n - (fuel + 1)) ||
        slotTombstoneQueued w parent name (n - (fuel + 1))) = true
    · have hrec : freeGo w parent name n fuel = some k := by
        simpa [freeGo, hbit] using h
      exact ih k (Nat.le_of_succ_le hf) hrec
    · have hfalse : (slotOccupied w name (n - (fuel + 1)) ||
          slotTombstoneQueued w parent name (n - (fuel + 1))) = false := by
        cases hbb : slotOccupied w name (n - (fuel + 1)) ||
            slotTombstoneQueued w parent name (n - (fuel + 1)) <;> simp_all
      have hk : n - (fuel + 1) = k := by
        simpa [freeGo, hfalse] using h
      subst hk
      have hpos : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos fuel) hf
      exact Nat.sub_lt hpos (Nat.succ_pos fuel)

theorem freeGo_fresh (w : World) (parent : InstId) (name : String) (n fuel k : Nat)
    (h : freeGo w parent name n fuel = some k) :
    slotOccupied w name k = false ∧ slotTombstoneQueued w parent name k = false := by
  induction fuel generalizing k with
  | zero => simp [freeGo] at h
  | succ fuel ih =>
    by_cases hbit : (slotOccupied w name (n - (fuel + 1)) ||
        slotTombstoneQueued w parent name (n - (fuel + 1))) = true
    · have hrec : freeGo w parent name n fuel = some k := by
        simpa [freeGo, hbit] using h
      exact ih k hrec
    · have hfalse : (slotOccupied w name (n - (fuel + 1)) ||
          slotTombstoneQueued w parent name (n - (fuel + 1))) = false := by
        cases hbb : slotOccupied w name (n - (fuel + 1)) ||
            slotTombstoneQueued w parent name (n - (fuel + 1)) <;> simp_all
      have hk : n - (fuel + 1) = k := by
        simpa [freeGo, hfalse] using h
      cases hocc : slotOccupied w name (n - (fuel + 1)) with
      | true => simp [hocc] at hfalse
      | false =>
        cases hq : slotTombstoneQueued w parent name (n - (fuel + 1)) with
        | true => simp [hocc, hq] at hfalse
        | false =>
          subst hk
          exact ⟨hocc, hq⟩

theorem freeSlot_lt (w : World) (parent : InstId) (name : String) (n k : Nat)
    (h : freeSlot w parent name n = some k) : k < n :=
  freeGo_lt w parent name n n k (Nat.le_refl _) (by simpa [freeSlot] using h)

theorem freeSlot_fresh (w : World) (parent : InstId) (name : String) (n k : Nat)
    (h : freeSlot w parent name n = some k) :
    slotOccupied w name k = false ∧ slotTombstoneQueued w parent name k = false :=
  freeGo_fresh w parent name n n k (by simpa [freeSlot] using h)

/-! Wired supervisors. -/

def subtreeEntry (D : Description) (t : Template) : Option String :=
  if t.slots != 0 && (t.multiplicity != .perPeer || t.supervisor == "") then
    some s!"fail: pool {t.name} is a per-peer template with a supervisor"
  else if t.slots != 0 then
    match templateOf D t.supervisor with
    | some s =>
      if s.multiplicity != .one then
        some s!"fail: slots must be 0 under a per-peer parent"
      else if t.subtree != "" && !(supervisorInSubtree D t) then
        some s!"fail: subtree {t.subtree} supervisor {t.supervisor} is not in the subtree"
      else none
    | none => some s!"fail: pool {t.name} names unknown supervisor {t.supervisor}"
  else if t.subtree == "" then
    if t.supervisor != "" then some s!"fail: {t.name} names a supervisor without a subtree"
    else if t.timeoutKills then some s!"fail: {t.name} sets timeoutKills without a subtree"
    else if templatePure D t.name then some (pureKillMsg t.name)
    else none
  else if t.multiplicity != .perPeer then
    some s!"fail: subtree {t.subtree} member {t.name} is not per-peer"
  else if t.supervisor != "" && !supervisorInSubtree D t then
    some s!"fail: subtree {t.subtree} supervisor {t.supervisor} is not in the subtree"
  else none

theorem subtreeFails_entry (D : Description) :
    subtreeFails D = D.templates.filterMap (subtreeEntry D) := rfl

theorem wired_supervisor (D : Description) (hG : GraphOk D) (t : Template)
    (ht : t ∈ D.templates) (hsup : t.supervisor ≠ "") :
    ∃ s, templateOf D t.supervisor = some s ∧ s.name = t.supervisor ∧
      supervisorInSubtree D t = true ∧ t.multiplicity = .perPeer ∧
      (t.slots ≠ 0 → s.multiplicity = .one) ∧
      (s.multiplicity = .perPeer → s.subtree = t.subtree ∧ s.name ≠ t.name ∧ t.subtree ≠ "") := by
  have hE : subtreeEntry D t = none :=
    filterMap_none (subtreeEntry D) D.templates (by simpa [subtreeFails_entry] using hG.subtrees) t ht
  unfold subtreeEntry at hE
  split at hE
  · simp at hE
  · split at hE
    · split at hE
      · rename_i s hs
        split at hE
        · simp at hE
        · rename_i hone
          split at hE
          · simp at hE
          · rename_i hsub
            have hone' : s.multiplicity = .one := by
              cases hm : s.multiplicity with
              | one => rfl
              | perPeer =>
                have hbad : (Multiplicity.perPeer != Multiplicity.one) = true := rfl
                simp [hm, hbad] at hone
            have hname : s.name = t.supervisor := (templateOf_mem D t.supervisor s hs).2
            have hper : t.multiplicity = .perPeer := by
              cases hm : t.multiplicity with
              | perPeer => rfl
              | one =>
                have hbad : (Multiplicity.one != Multiplicity.perPeer) = true := rfl
                simp [hm, hbad] at *
                contradiction
            have hin : supervisorInSubtree D t = true := by
              unfold supervisorInSubtree
              simp only [hs, hone', Bool.or_eq_true]
              exact Or.inl rfl
            refine ⟨s, hs, hname, hin, hper, fun _ => hone', ?_⟩
            intro hm
            have hboth : Multiplicity.one = Multiplicity.perPeer := by simpa [hone'] using hm
            cases hboth
      · simp at hE
    · split at hE
      · split at hE
        · simp at hE
        · rename_i hempty
          have hb : (t.supervisor != "") = false := by simpa using hempty
          have hempty' : t.supervisor = "" := by simpa [bne, beq_iff_eq] using hb
          exact absurd hempty' hsup
      · split at hE
        · simp at hE
        · split at hE
          · simp at hE
          · rename_i hin
            have hper : t.multiplicity = .perPeer := by
              cases hm : t.multiplicity with
              | perPeer => rfl
              | one =>
                have hbad : (Multiplicity.one != Multiplicity.perPeer) = true := rfl
                simp [hm, hbad] at *
            unfold supervisorInSubtree at hin
            cases hs : templateOf D t.supervisor with
            | none => simp [hs, hsup] at hin
            | some s =>
              have hname : s.name = t.supervisor := (templateOf_mem D t.supervisor s hs).2
              have hsubne : t.subtree ≠ "" := by
                cases hbb : t.subtree == "" <;> simp_all
              have hor : (s.multiplicity == .one) = true ∨
                  (s.multiplicity == .perPeer) = true ∧ s.subtree = t.subtree ∧ s.name ≠ t.name := by
                simp [hs, hsup] at hin
                by_cases hone : (s.multiplicity == .one) = true
                · exact Or.inl hone
                · have hnot : (s.multiplicity == .one) = false := by
                    cases hbb : s.multiplicity == .one <;> simp_all
                  have hrest := hin hnot
                  exact Or.inr ⟨hrest.1.1, hrest.1.2, by simpa [bne, beq_iff_eq] using hrest.2⟩
              refine ⟨s, by simpa [hs], hname, ?_, hper, ?_, ?_⟩
              · unfold supervisorInSubtree
                simp [hs]
                cases hor with
                | inl h => exact Or.inl h
                | inr h =>
                  exact Or.inr ⟨⟨h.1, h.2.1⟩, by simpa [bne, beq_iff_eq] using h.2.2⟩
              · intro hslots
                simp_all
              · intro hm
                cases hor with
                | inl hone =>
                  have hone' : s.multiplicity = .one := by
                    cases hmul : s.multiplicity with
                    | one => rfl
                    | perPeer =>
                      have hbad : (Multiplicity.perPeer == Multiplicity.one) = false := rfl
                      simp [hmul, hbad] at hone
                  have hboth : Multiplicity.one = Multiplicity.perPeer := by simpa [hone'] using hm
                  cases hboth
                | inr hrest =>
                  exact ⟨hrest.2.1, hrest.2.2, hsubne⟩
/-! Priority-lane release. -/

def tmb_dropHost (dead : InstId) (w : World) (host : InstId) : World :=
  if host == dead then w
  else
    let dropped := (w.st host).parked.filter fun p => p.sender == dead
    if dropped.isEmpty then w
    else
      let cleared := setActor w host
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      setActor cleared dead (addTokens (cleared.st dead) (tname host) dropped.length)

theorem tmb_dropHost_eq (w : World) (dead : InstId) :
    releaseOutbound w dead = w.roster.foldl (tmb_dropHost dead) w := rfl

theorem tmb_dropHost_prio (dead : InstId) (w : World) (host i : InstId) :
    ((tmb_dropHost dead w host).st i).prio = (w.st i).prio ∧ (tmb_dropHost dead w host).N = w.N := by
  unfold tmb_dropHost
  by_cases hdead : (host == dead) = true
  · simp [hdead]
  · have hf : (host == dead) = false := by
      cases hbb : host == dead <;> simp_all
    simp only [hf, ite_false]
    by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · simp [hempty]
    · have hne : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false := by
        cases hbb : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty <;> simp_all
      simp only [hne, ite_false]
      by_cases hi : i = dead
      · have hnh : host ≠ dead := by
          intro heq
          have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
          simp [hb] at hf
        rw [hi]
        have hdir : dead ≠ host := hnh.symm
        simp [setActor, addTokens, hdir]
      · by_cases hh : i = host
        · have hnd : host ≠ dead := by
            intro heq
            have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
            simp [hb] at hf
          rw [hh]
          simp [setActor, hnd]
        · simp [setActor, hi, hh]

theorem tmb_fold_drop_prio (dead : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (tmb_dropHost dead) w).st i).prio = (w.st i).prio ∧
        (ids.foldl (tmb_dropHost dead) w).N = w.N := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons host ids ih =>
    intro w i
    simp only [List.foldl_cons]
    have h1 := tmb_dropHost_prio dead w host i
    have h2 := ih (tmb_dropHost dead w host) i
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem releaseOutbound_prio (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).prio = (w.st i).prio ∧ (releaseOutbound w dead).N = w.N := by
  simpa [tmb_dropHost_eq] using tmb_fold_drop_prio dead w.roster w i

def tmb_resumeOne (id : InstId) (w : World) (p : Parked) : World :=
  if p.isCall || p.sender = id then w
  else setActor w p.sender (resumeSender (w.st p.sender) false id)

theorem tmb_resumeOne_eq (w : World) (id : InstId) (ps : List Parked) :
    releaseParked w id ps = ps.foldl (tmb_resumeOne id) w := rfl

theorem resumeSender_prio (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).prio = a.prio := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases hk : k.rest <;> cases isCall <;> simp [resumeSender, proceed, hph, hk]
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem tmb_resumeOne_prio (id : InstId) (w : World) (p : Parked) (i : InstId) :
    ((tmb_resumeOne id w p).st i).prio = (w.st i).prio ∧ (tmb_resumeOne id w p).N = w.N := by
  unfold tmb_resumeOne
  split
  · exact ⟨rfl, rfl⟩
  · by_cases hi : i = p.sender
    · subst hi
      simpa [setActor] using resumeSender_prio (w.st p.sender) false id
    · simp [setActor, hi]

theorem tmb_fold_resume_prio (id : InstId) :
    ∀ ps : List Parked, ∀ w : World, ∀ i : InstId,
      ((ps.foldl (tmb_resumeOne id) w).st i).prio = (w.st i).prio ∧
        (ps.foldl (tmb_resumeOne id) w).N = w.N := by
  intro ps
  induction ps with
  | nil => intro w i; simp
  | cons p ps ih =>
    intro w i
    simp only [List.foldl_cons]
    have h1 := tmb_resumeOne_prio id w p i
    have h2 := ih (tmb_resumeOne id w p) i
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem releaseParked_prio (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).prio = (w.st i).prio ∧ (releaseParked w id ps).N = w.N := by
  simpa [tmb_resumeOne_eq] using tmb_fold_resume_prio id ps w i

theorem releaseWorld_prio (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (h : i ≠ id) :
    ((releaseWorld D w id a).st i).prio = (w.st i).prio ∧ (releaseWorld D w id a).N = w.N := by
  unfold releaseWorld
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) a.box
  let w3 := refundParked w2 (tname id) a.parked
  let w4 := releaseOutbound w3 id
  let dead : Actor :=
    { w4.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1p : (w1.st i).prio = (w.st i).prio := by
    have hst := cellsSt D w id i
    simpa [w1] using congrArg (fun a : Actor => a.prio) hst
  have h1n : w1.N = w.N := cellsN D w id
  have h2p : (w2.st i).prio = (w1.st i).prio := (refundMsgs_fields w1 (tname id) a.box i).2.2.2.2
  have h2n : w2.N = w1.N := refundMsgs_N w1 (tname id) a.box
  have h3p : (w3.st i).prio = (w2.st i).prio := (refundParked_fields w2 (tname id) a.parked i).2.2.2.2
  have h3n : w3.N = w2.N := refundParked_N w2 (tname id) a.parked
  have h4 := releaseOutbound_prio w3 id i
  have h5p : ((setActor w4 id dead).st i).prio = (w4.st i).prio := by
    have hst := setActor_other w4 id i dead h
    simpa using congrArg (fun a : Actor => a.prio) hst
  have h5n : (setActor w4 id dead).N = w4.N := rfl
  have h6 := releaseParked_prio (setActor w4 id dead) id a.parked i
  exact ⟨h6.1.trans (h5p.trans (h4.1.trans (h3p.trans (h2p.trans h1p)))),
    h6.2.trans (h5n.trans (h4.2.trans (h3n.trans (h2n.trans h1n))))⟩

/-! A reachable seal still has room for its tombstone. -/

def notifies (D : Description) (child : InstId) : Bool :=
  match templateOf D (tname child) with
  | some t => t.tombstone != ""
  | none => false

theorem tmb_same_refl (id : InstId) : sameSlot id id = true := by
  cases id <;> simp [sameSlot]

theorem tmb_child_ne (D : Description) (parent child : InstId)
    (h : isChild D parent child = true) : child ≠ parent := by
  intro heq
  subst heq
  cases hsup : supervisorOf D child with
  | none => simp [isChild, hsup] at h
  | some p => simp [isChild, hsup, tmb_same_refl] at h

theorem tmb_find_some {α : Type} (p : α → Bool) (xs : List α) (a : α)
    (h : xs.find? p = some a) : a ∈ xs ∧ p a = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp [List.find?] at h
    by_cases hp : p x = true
    · simp [hp] at h
      cases h
      exact ⟨List.mem_cons_self, hp⟩
    · have hf : p x = false := by
        cases hbit : p x <;> simp_all
      simp [hf] at h
      obtain ⟨hm, hpa⟩ := ih h
      exact ⟨List.mem_cons_of_mem x hm, hpa⟩

theorem tmb_findLive_eq (w : World) (name : String) (k : Nat) (id : InstId)
    (h : findLive w name k = some id) : ∃ g, id = .peer name k g ∧ id ∈ w.roster := by
  unfold findLive at h
  have hhit := tmb_find_some _ w.roster id h
  cases id with
  | core _ => simp at hhit
  | peer n key g =>
    simp only [] at hhit
    have hb := hhit.2
    have hsplit : n = name ∧ key = k := by
      have htrue : (n == name && key == k && (w.st (.peer n key g)).life == .alive) = true := hb
      simp [Bool.and_eq_true, beq_iff_eq] at htrue
      exact ⟨htrue.1.1, htrue.1.2⟩
    exact ⟨g, by simp [hsplit], hhit.1⟩

theorem tmb_sup_slot (D : Description) (w : World) (child parent : InstId)
    (h : liveSupervisor D w child = some parent) :
    ∃ canon, supervisorOf D child = some canon ∧ sameSlot canon parent = true := by
  unfold liveSupervisor at h
  cases hsup : supervisorOf D child with
  | none => simp [hsup] at h
  | some canon =>
    simp only [hsup] at h
    cases canon with
    | core n =>
      simp at h
      cases h
      exact ⟨.core n, by rfl, by simp [sameSlot]⟩
    | peer n k g =>
      simp at h
      cases hlive : findLive w n k with
      | none =>
        simp [hlive] at h
        cases h
        exact ⟨.peer n k g, by rfl, tmb_same_refl _⟩
      | some id =>
        simp [hlive] at h
        cases h
        obtain ⟨g', hid, _⟩ := tmb_findLive_eq w n k parent hlive
        subst hid
        exact ⟨.peer n k g, by rfl, by simp [sameSlot]⟩

theorem tmb_notifies_of_label (D : Description) (child : InstId)
    (h : tombstoneLabel D child ≠ "") : notifies D child = true := by
  unfold notifies
  cases ht : templateOf D (tname child) with
  | none =>
    have hempty : tombstoneLabel D child = "" := by simp [tombstoneLabel, ht]
    exact absurd hempty h
  | some t =>
    by_cases hb : (t.tombstone == "") = true
    · have hempty : tombstoneLabel D child = "" := by simp [tombstoneLabel, ht, hb]
      exact absurd hempty h
    · have hf : (t.tombstone == "") = false := by
        cases hbit : t.tombstone == "" <;> simp_all
      simp [ht, hf, bne]

theorem tmb_append_ne (s t : String) (ht : t ≠ "") : s ++ t ≠ "" := by
  intro h
  have hlist : (s ++ t).toList = [] := (String.ext_iff.mp h)
  rw [String.toList_append] at hlist
  cases hs : s.toList with
  | nil =>
    rw [hs, List.nil_append] at hlist
    exact ht (String.ext hlist)
  | cons c cs =>
    rw [hs] at hlist
    simp at hlist

theorem tmb_append_left_ne (s t : String) (hs : s ≠ "") : s ++ t ≠ "" := by
  intro h
  have hlist : (s ++ t).toList = [] := (String.ext_iff.mp h)
  rw [String.toList_append] at hlist
  cases hto : s.toList with
  | nil => exact hs (String.ext hto)
  | cons _ _ =>
    rw [hto] at hlist
    simp at hlist

theorem tmb_hash_ne (base : String) (g : Nat) (hb : base ≠ "") :
    base ++ "#" ++ toString g ≠ "" :=
  tmb_append_left_ne (base ++ "#") (toString g) (tmb_append_left_ne base "#" hb)

theorem tmb_nodup_concat {α : Type} [DecidableEq α] (xs : List α) (x : α)
    (hxs : xs.Nodup) (hx : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hys : ys.Nodup := (List.nodup_cons.mp hxs).2
    have hy : y ∉ ys := (List.nodup_cons.mp hxs).1
    have hx' : x ∉ ys := by
      intro hm
      exact hx (List.mem_cons.mpr (Or.inr hm))
    have hyx : y ≠ x := by
      intro heq
      exact hx (heq ▸ List.mem_cons_self)
    have htail := ih hys hx'
    simp only [List.cons_append]
    refine List.nodup_cons.mpr ⟨?_, htail⟩
    intro hm
    cases List.mem_append.mp hm with
    | inl h => exact hy h
    | inr h =>
      simp at h
      exact hyx h

theorem tmb_tomb_len (ms : List Msg)
    (h : ∀ m ∈ ms, m.tombstone = true → ∃ n k g, m.sender = .peer n k g) :
    (tombSlots ms).length = (ms.filter (·.tombstone)).length := by
  induction ms with
  | nil => simp [tombSlots]
  | cons m ms ih =>
    have ih' := ih (fun m' hm' ht' => h m' (List.mem_cons.mpr (Or.inr hm')) ht')
    cases ht : m.tombstone with
    | false =>
      simp only [tombSlots, List.filterMap_cons, List.filter_cons, ht]
      exact ih'
    | true =>
      obtain ⟨n, k, g, hs⟩ := h m (List.mem_cons.mpr (Or.inl rfl)) ht
      simp only [tombSlots, List.filterMap_cons, List.filter_cons, ht, hs, List.length_cons]
      exact congrArg Nat.succ ih'

theorem tmb_lane_len (ms : List Msg) :
    (tmb_laneLabels ms).length = (ms.filter (fun m => !m.tombstone)).length := by
  simp [tmb_laneLabels, List.length_map]

theorem tmb_load_split (ms : List Msg)
    (h : ∀ m ∈ ms, m.tombstone = true → ∃ n k g, m.sender = .peer n k g) :
    ms.length = (tombSlots ms).length + (tmb_laneLabels ms).length := by
  have hsplit := tmb_filter_split (·.tombstone) ms
  have hlen := tmb_tomb_len ms h
  have hord := tmb_lane_len ms
  omega

def tmb_hit (name : String) (k : Nat) (m : Msg) : Bool :=
  m.tombstone &&
    match m.sender with
    | .peer n key _ => n == name && key == k
    | .core _ => false

theorem tmb_hit_mem (ms : List Msg) (name : String) (k : Nat) :
    (ms.any (tmb_hit name k)) = true ↔ (name, k) ∈ tombSlots ms := by
  induction ms with
  | nil => simp [tombSlots, List.any]
  | cons m ms ih =>
    rw [List.any_cons]
    by_cases hh : tmb_hit name k m = true
    · have hmem : (name, k) ∈ tombSlots (m :: ms) := by
        unfold tmb_hit at hh
        cases ht : m.tombstone with
        | false => simp [ht] at hh
        | true =>
          simp only [ht, Bool.true_and] at hh
          cases hs : m.sender with
          | core _ => simp [hs] at hh
          | peer n key _ =>
            have hnk : n = name ∧ key = k := by
              simpa [hs, Bool.and_eq_true, beq_iff_eq] using hh
            simp [tombSlots, List.filterMap_cons, ht, hs, hnk]
      simp [hh, hmem]
    · have hf : tmb_hit name k m = false := by
        cases hbit : tmb_hit name k m <;> simp_all
      rw [hf, Bool.false_or]
      have hdrop : (name, k) ∈ tombSlots (m :: ms) ↔ (name, k) ∈ tombSlots ms := by
        simp only [tombSlots, List.filterMap_cons]
        cases ht : m.tombstone with
        | false => simp [ht]
        | true =>
          cases hs : m.sender with
          | core _ => simp [ht, hs]
          | peer n key _ =>
            simp only [List.filterMap_cons, ht, hs]
            constructor
            · intro hm
              cases List.mem_cons.mp hm with
              | inl heq =>
                cases heq
                simp [tmb_hit, ht, hs] at hf
              | inr htail => exact htail
            · intro htail
              exact List.mem_cons.mpr (Or.inr htail)
      exact ih.trans hdrop.symm

theorem tmb_queued_iff (w : World) (parent : InstId) (name : String) (k : Nat) :
    slotTombstoneQueued w parent name k = true ↔ (name, k) ∈ tombSlots (w.st parent).prio := by
  unfold slotTombstoneQueued
  exact tmb_hit_mem (w.st parent).prio name k

structure LaneOk (I : Impl) (w : World) (id : InstId) : Prop where
  ordNodup : (tmb_laneLabels (w.st id).prio).Nodup
  ordIn : ∀ l, l ∈ tmb_laneLabels (w.st id).prio → l ∈ prioLabels I (tname id)
  peer : ∀ m, m ∈ (w.st id).prio → m.tombstone = true → ∃ n k g, m.sender = .peer n k g
  tombNodup : (tombSlots (w.st id).prio).Nodup

/-- What a reachable world may hold on a priority lane.
Ordinary labels are declared and distinct. Tombstones are one per child slot,
and a slot that still has a live or armed child does not also have a queued
tombstone. A dead actor keeps an empty lane unless the roster has crashed. -/
structure Hold (I : Impl) (w : World) : Prop where
  rostered : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster
  pend : ∀ id, (w.st id).pendingTombstone = true →
    (w.st id).life = .shuttingDown ∨ (w.st id).life = .dead
  deadPrio : w.crashed = false → ∀ id, (w.st id).life = .dead → (w.st id).prio = []
  role : ∀ id, id ∈ w.roster → ∃ t, templateOf I.desc (tname id) = some t ∧
    t.multiplicity = tmb_role id
  phase : ∀ id, id ∈ w.roster → phaseDeclared I (tname id) (w.st id).phase
  lane : ∀ id, LaneOk I w id
  legalLife : ∀ parent c, c ∈ w.roster → isChild I.desc parent c = true →
    lifeHold (w.st c) = true → notifies I.desc c = true →
    match c with
    | .peer n k _ => (n, k) ∈ legalSlots I.desc parent w.N
    | .core _ => True
  legalTomb : ∀ parent name k, slotTombstoneQueued w parent name k = true →
    (name, k) ∈ legalSlots I.desc parent w.N
  fresh : ∀ parent c, c ∈ w.roster → isChild I.desc parent c = true →
    lifeHold (w.st c) = true → notifies I.desc c = true →
    match c with
    | .peer n k _ => slotTombstoneQueued w parent n k = false
    | .core _ => True
  occ : ∀ c1 c2, c1 ∈ w.roster → c2 ∈ w.roster →
    occupant (w.st c1) = true → occupant (w.st c2) = true →
    sameSlot c1 c2 = true → supervisorOf I.desc c1 ≠ none → c1 = c2

theorem tmb_prio_sized (I : Impl) (hL : LocalOk I) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) :
    prioSized I.desc name (prioSenderBound I name) = true := by
  have hmem : t ∈ I.desc.templates ∧ t.name = name := templateOf_mem I.desc name t ht
  have hempty : prioSizeFails I = [] :=
    isEmpty_true _ (by simpa [prioSizeOk] using prio_size_local I hL)
  unfold prioSizeFails at hempty
  have hnone := filterMap_none
    (fun u => if prioSized I.desc u.name (prioSenderBound I u.name) then none
      else some s!"fail: priority lane {u.name} holds fewer slots than the tombstones and other priority senders it can receive at once")
    I.desc.templates hempty t hmem.1
  by_cases hbit : prioSized I.desc t.name (prioSenderBound I t.name) = true
  · simpa [hmem.2] using hbit
  · have hf : prioSized I.desc t.name (prioSenderBound I t.name) = false := by
      cases hbb : prioSized I.desc t.name (prioSenderBound I t.name) <;> simp_all
    simp [hf] at hnone

theorem tmb_dropHost_keep (dead : InstId) (w : World) (host i : InstId) :
    ((tmb_dropHost dead w host).st i).life = (w.st i).life ∧
      ((tmb_dropHost dead w host).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (tmb_dropHost dead w host).roster = w.roster := by
  unfold tmb_dropHost
  by_cases hdead : (host == dead) = true
  · simp [hdead]
  · have hf : (host == dead) = false := by
      cases hbb : host == dead <;> simp_all
    simp only [hf, ite_false]
    by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · simp [hempty]
    · have hne : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false := by
        cases hbb : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty <;> simp_all
      simp only [hne, ite_false]
      by_cases hi : i = host
      · have hdir : host ≠ dead := by
          intro heq
          have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
          simp [hb] at hf
        simp [setActor, addTokens, hi, hdir, Ne.symm hdir]
      · by_cases hid : i = dead
        · have hdir : dead ≠ host := by
            intro heq
            exact hi (hid.trans heq)
          simp [setActor, addTokens, hi, hid, hdir]
        · simp [setActor, addTokens, hi, hid]

theorem tmb_fold_drop_keep (dead : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (tmb_dropHost dead) w).st i).life = (w.st i).life ∧
        ((ids.foldl (tmb_dropHost dead) w).st i).pendingTombstone =
          (w.st i).pendingTombstone ∧
        (ids.foldl (tmb_dropHost dead) w).roster = w.roster := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons host ids ih =>
    intro w i
    simp only [List.foldl_cons]
    have h1 := tmb_dropHost_keep dead w host i
    have h2 := ih (tmb_dropHost dead w host) i
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem releaseOutbound_keep (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).life = (w.st i).life ∧
      ((releaseOutbound w dead).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (releaseOutbound w dead).roster = w.roster := by
  simpa [tmb_dropHost_eq] using tmb_fold_drop_keep dead w.roster w i

theorem resumeSender_keep (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).life = a.life ∧
      (resumeSender a isCall dst).pendingTombstone = a.pendingTombstone := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases hk : k.rest <;> cases isCall <;> simp [resumeSender, proceed, hph, hk]
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem tmb_resumeOne_keep (id : InstId) (w : World) (p : Parked) (i : InstId) :
    ((tmb_resumeOne id w p).st i).life = (w.st i).life ∧
      ((tmb_resumeOne id w p).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (tmb_resumeOne id w p).roster = w.roster := by
  unfold tmb_resumeOne
  split
  · exact ⟨rfl, rfl, rfl⟩
  · by_cases hi : i = p.sender
    · subst hi
      have h := resumeSender_keep (w.st p.sender) false id
      simp [setActor, h]
    · simp [setActor, hi]

theorem tmb_fold_resume_keep (id : InstId) :
    ∀ ps : List Parked, ∀ w : World, ∀ i : InstId,
      ((ps.foldl (tmb_resumeOne id) w).st i).life = (w.st i).life ∧
        ((ps.foldl (tmb_resumeOne id) w).st i).pendingTombstone =
          (w.st i).pendingTombstone ∧
        (ps.foldl (tmb_resumeOne id) w).roster = w.roster := by
  intro ps
  induction ps with
  | nil => intro w i; simp
  | cons p ps ih =>
    intro w i
    simp only [List.foldl_cons]
    have h1 := tmb_resumeOne_keep id w p i
    have h2 := ih (tmb_resumeOne id w p) i
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem releaseParked_keep (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).life = (w.st i).life ∧
      ((releaseParked w id ps).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (releaseParked w id ps).roster = w.roster := by
  simpa [tmb_resumeOne_eq] using tmb_fold_resume_keep id ps w i

theorem credit_pending (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).pendingTombstone = (w.st i).pendingTombstone := by
  by_cases h : i = sender
  · subst h
    simp [creditSender, setActor, bumpToken]
  · simp [creditSender, setActor, h]

theorem refundMsgs_pending (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).pendingTombstone = (w.st i).pendingTombstone := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact (ih (creditLive w name m.sender)).trans
      (credit_pending w name (budgetHolder w m.sender) i)

theorem refundParked_pending (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).pendingTombstone = (w.st i).pendingTombstone := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact (ih (creditLive w name p.msg.sender)).trans
      (credit_pending w name (budgetHolder w p.msg.sender) i)

theorem releaseWorld_keep (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (h : i ≠ id) :
    ((releaseWorld D w id a).st i).life = (w.st i).life ∧
      ((releaseWorld D w id a).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (releaseWorld D w id a).roster = w.roster := by
  unfold releaseWorld
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) a.box
  let w3 := refundParked w2 (tname id) a.parked
  let w4 := releaseOutbound w3 id
  let dead : Actor :=
    { w4.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1l : (w1.st i).life = (w.st i).life := by
    simpa [w1] using congrArg (fun a : Actor => a.life) (cellsSt D w id i)
  have h1p : (w1.st i).pendingTombstone = (w.st i).pendingTombstone := by
    simpa [w1] using congrArg (fun a : Actor => a.pendingTombstone) (cellsSt D w id i)
  have h1r : w1.roster = w.roster := by simpa [w1] using cellsRoster D w id
  have h2 := refundMsgs_fields w1 (tname id) a.box i
  have h2r : w2.roster = w1.roster := by simpa [w2] using refundMsgs_roster w1 (tname id) a.box
  have h2p : (w2.st i).pendingTombstone = (w1.st i).pendingTombstone := by
    simpa [w2] using refundMsgs_pending w1 (tname id) a.box i
  have h3 := refundParked_fields w2 (tname id) a.parked i
  have h3p : (w3.st i).pendingTombstone = (w2.st i).pendingTombstone := by
    simpa [w3] using refundParked_pending w2 (tname id) a.parked i
  have h3r : w3.roster = w2.roster := by simpa [w3] using refundParked_roster w2 (tname id) a.parked
  have h4 := releaseOutbound_keep w3 id i
  have h5l : ((setActor w4 id dead).st i).life = (w4.st i).life := by
    simpa using congrArg (fun a : Actor => a.life) (setActor_other w4 id i dead h)
  have h5p : ((setActor w4 id dead).st i).pendingTombstone = (w4.st i).pendingTombstone := by
    simpa using congrArg (fun a : Actor => a.pendingTombstone) (setActor_other w4 id i dead h)
  have h5r : (setActor w4 id dead).roster = w4.roster := rfl
  have h6 := releaseParked_keep (setActor w4 id dead) id a.parked i
  exact ⟨h6.1.trans (h5l.trans (h4.1.trans (h3.2.1.trans (h2.2.1.trans h1l)))),
    h6.2.1.trans (h5p.trans (h4.2.1.trans (h3p.trans (h2p.trans h1p)))),
    h6.2.2.trans (h5r.trans (h4.2.2.trans (h3r.trans (h2r.trans h1r))))⟩

theorem supervisorInst_name (D : Description) (child : InstId) (supName n : String) (k g : Nat)
    (h : supervisorInst D child supName = some (.peer n k g)) : n = supName := by
  unfold supervisorInst at h
  cases ht : templateOf D supName with
  | none => simp [ht] at h
  | some s =>
    simp [ht] at h
    cases hm : s.multiplicity with
    | one => simp [hm] at h
    | perPeer =>
      simp [hm] at h
      cases child with
      | core _ => simp at h
      | peer cname ck _ =>
        simp at h
        cases hch : templateOf D cname with
        | none => simp [tname, hch] at h
        | some t =>
          simp [tname, hch] at h
          rcases h with ⟨_, hn, _, _⟩
          exact hn.symm

theorem tmb_live_peer (D : Description) (hG : GraphOk D) (w : World) (child parent : InstId)
    (hrole : ∃ t, templateOf D (tname child) = some t ∧ t.multiplicity = tmb_role child)
    (h : liveSupervisor D w child = some parent) :
    ∃ n k g, child = .peer n k g ∧ isChild D parent child = true := by
  obtain ⟨canon, hcanon, hslot⟩ := tmb_sup_slot D w child parent h
  unfold supervisorOf at hcanon
  cases ht : templateOf D (tname child) with
  | none => simp [ht] at hcanon
  | some t =>
    simp only [ht] at hcanon
    have hnamed : t.supervisor ≠ "" := by
      intro hempty
      have hb : (t.supervisor == "") = true := by simpa [beq_iff_eq] using hempty
      simp [hb] at hcanon
    obtain ⟨s, hs, hname, _, hper, _, hif⟩ :=
      wired_supervisor D hG t (templateOf_mem D (tname child) t ht).1 hnamed
    have hnotCore : ∀ n, child ≠ .core n := by
      intro n heq
      obtain ⟨t', ht', hm'⟩ := hrole
      have hone : t'.multiplicity = .one := by simpa [heq, tmb_role] using hm'
      have ht'' : t' = t := by
        have hsome : templateOf D (tname child) = some t' := ht'
        simp [ht] at hsome
        exact hsome.symm
      simp [ht'', hper] at hone
    cases child with
    | core n => exact absurd rfl (hnotCore n)
    | peer cn ck cg =>
      have hdiff : sameSlot (.peer cn ck cg) parent = false := by
        cases canon with
        | core sn =>
          cases parent with
          | core pn =>
            simp [sameSlot] at hslot
            simp [sameSlot, hslot]
          | peer _ _ _ => simp [sameSlot] at hslot
        | peer sn sk sg =>
          cases parent with
          | core _ => simp [sameSlot] at hslot
          | peer pn pk pg =>
            simp [sameSlot, Bool.and_eq_true, beq_iff_eq] at hslot
            have hsmult : s.multiplicity = .perPeer := by
              cases hm : s.multiplicity with
              | perPeer => rfl
              | one =>
                have hb0 : (t.supervisor == "") = false := by
                  simpa [beq_iff_eq] using hnamed
                simp [supervisorInst, hs, hm, hb0] at hcanon
            have hnames := hif hsmult
            have hchildName : t.name = cn := by
              simpa [tname] using (templateOf_mem D cn t (by simpa [tname] using ht)).2
            have hsn : sn = t.supervisor := by
              have hb0 : (t.supervisor == "") = false := by
                simpa [beq_iff_eq] using hnamed
              have hinst : supervisorInst D (.peer cn ck cg) t.supervisor = some (.peer sn sk sg) := by
                simpa [hb0] using hcanon
              exact supervisorInst_name D (.peer cn ck cg) t.supervisor sn sk sg hinst
            have hcn : cn ≠ pn := by
              intro heq
              apply hnames.2.1
              calc s.name
                _ = t.supervisor := hname
                _ = sn := hsn.symm
                _ = pn := hslot.1
                _ = cn := heq.symm
                _ = t.name := hchildName.symm
            have hbname : (cn == pn) = false := by simpa [beq_iff_eq] using hcn
            simp [sameSlot, hbname]
      have hchild : isChild D parent (.peer cn ck cg) = true := by
        have hb0 : (t.supervisor == "") = false := by simpa [beq_iff_eq] using hnamed
        have hinst : supervisorInst D (.peer cn ck cg) t.supervisor = some canon := by
          simpa [hb0] using hcanon
        unfold isChild supervisorOf
        simp [ht, hnamed, hinst, hslot, hdiff]
      exact ⟨cn, ck, cg, rfl, hchild⟩

/-- Sealing a shutting-down child does not fill its parent's priority lane.
The queued tombstones plus this one are at most the slot bound, and the other
priority messages are within the declared sender count. -/
theorem tmb_seal_room (I : Impl) (w : World) (child : InstId)
    (hG : GraphOk I.desc) (hL : LocalOk I) (hH : Hold I w)
    (hshut : (w.st child).life = .shuttingDown)
    (hpend : (w.st child).pendingTombstone = true) :
    ∀ parent, liveSupervisor I.desc (releaseWorld I.desc w child (w.st child)) child = some parent →
      ((releaseWorld I.desc w child (w.st child)).st parent).life = .alive →
      (tombstoneMsg I.desc ((releaseWorld I.desc w child (w.st child)).st parent) child).label ≠ "" →
      prioLoad ((releaseWorld I.desc w child (w.st child)).st parent).prio <
        capPrio I.desc (releaseWorld I.desc w child (w.st child)).N parent := by
  intro parent hsup halive hlabel
  let sealed := releaseWorld I.desc w child (w.st child)
  have hmem : child ∈ w.roster := hH.rostered child (by rw [hshut]; intro h; cases h)
  have hrole := hH.role child hmem
  obtain ⟨n, k, g, hid, hchild⟩ := tmb_live_peer I.desc hG sealed child parent hrole hsup
  have hne : child ≠ parent := tmb_child_ne I.desc parent child hchild
  have hprio := releaseWorld_prio I.desc w child (w.st child) parent hne.symm
  have hkeep := releaseWorld_keep I.desc w child (w.st child) parent hne.symm
  have hpre : (w.st parent).life = .alive := by
    rw [← hkeep.1]
    exact halive
  have hpmem : parent ∈ w.roster := hH.rostered parent (by rw [hpre]; intro h; cases h)
  obtain ⟨sup, ht, hmult⟩ := hH.role parent hpmem
  have hsized : prioSized I.desc (tname parent) (prioSenderBound I (tname parent)) = true :=
    tmb_prio_sized I hL (tname parent) sup ht
  have hhold : lifeHold (w.st child) = true := by simp [lifeHold, hshut, hpend]
  have hnote : notifies I.desc child = true :=
    tmb_notifies_of_label I.desc child (by simpa [tombstoneMsg] using hlabel)
  have hleg : (n, k) ∈ legalSlots I.desc parent w.N := by
    have hraw := hH.legalLife parent child hmem hchild hhold hnote
    simpa [hid] using hraw
  have hnot : slotTombstoneQueued w parent n k = false := by
    have hraw := hH.fresh parent child hmem hchild hhold hnote
    simpa [hid] using hraw
  have hlane := hH.lane parent
  have hprioEq : (sealed.st parent).prio = (w.st parent).prio := hprio.1
  have hN : sealed.N = w.N := hprio.2
  have htombs : (tombSlots (w.st parent).prio).Nodup := by simpa [hprioEq] using hlane.tombNodup
  have hpeer : ∀ m ∈ (w.st parent).prio, m.tombstone = true → ∃ n k g, m.sender = .peer n k g :=
    hlane.peer
  have hload : prioLoad (w.st parent).prio =
      (tombSlots (w.st parent).prio).length + (tmb_laneLabels (w.st parent).prio).length := by
    simpa [prioLoad] using tmb_load_split (w.st parent).prio hpeer
  have hord : (tmb_laneLabels (w.st parent).prio).length ≤
      (prioLabels I (tname parent)).length :=
    tmb_nodup_sub_length _ _ hlane.ordNodup hlane.ordIn
  have hsend : (prioLabels I (tname parent)).length ≤ prioSenderBound I (tname parent) :=
    Nat.le_max_right _ _
  have hrest : (tmb_laneLabels (w.st parent).prio).length ≤ prioSenderBound I (tname parent) :=
    Nat.le_trans hord hsend
  have hnin : (n, k) ∉ tombSlots (w.st parent).prio := by
    intro hmems
    have htrue := (tmb_queued_iff w parent n k).2 hmems
    simp [hnot] at htrue
  have hcat : (tombSlots (w.st parent).prio ++ [(n, k)]).Nodup :=
    tmb_nodup_concat _ _ htombs hnin
  have hsub : ∀ x, x ∈ tombSlots (w.st parent).prio ++ [(n, k)] →
      x ∈ legalSlots I.desc parent w.N := by
    intro x hx
    cases List.mem_append.mp hx with
    | inl h =>
      have hpair : ∃ name key, x = (name, key) := ⟨x.1, x.2, rfl⟩
      obtain ⟨name, key, hxeq⟩ := hpair
      subst hxeq
      exact hH.legalTomb parent name key ((tmb_queued_iff w parent name key).2 h)
    | inr h =>
      simp at h
      simpa [h] using hleg
  have hcount : (tombSlots (w.st parent).prio).length + 1 ≤
      (legalSlots I.desc parent w.N).length := by
    have hlen := tmb_nodup_sub_length _ _ hcat hsub
    simpa [List.length_append] using hlen
  have haff : (legalSlots I.desc parent w.N).length ≤
      (tombstoneAffine I.desc (tname parent)).eval w.N :=
    legal_le_affine I.desc parent w.N sup ht hmult
  have htombsLe : (tombSlots (w.st parent).prio).length + 1 ≤
      (tombstoneAffine I.desc (tname parent)).eval w.N :=
    Nat.le_trans hcount haff
  have hlt := tombstone_enqueue_room I.desc (tname parent) (prioSenderBound I (tname parent))
    (tombSlots (w.st parent).prio).length (tmb_laneLabels (w.st parent).prio).length w.N sup
    ht hsized hrest htombsLe
  have hcap : capPrio I.desc w.N parent = sup.priorityCapacity.eval w.N := by
    simp [capPrio, ht]
  have hlt' : prioLoad (w.st parent).prio < capPrio I.desc w.N parent := by
    simpa [hload, hcap] using hlt
  simpa [sealed, hprioEq, hN] using hlt'

/-! The lane invariant is preserved by every reachable step. -/

def tmb_dedupFold {α : Type} [DecidableEq α] (acc : List α) (y : α) : List α :=
  if acc.elem y then acc else acc ++ [y]

theorem tmb_elem_of_mem {α : Type} [DecidableEq α] {a : α} {xs : List α} (h : a ∈ xs) :
    xs.elem a = true :=
  List.elem_iff.mpr h

theorem tmb_not_mem_of_elem {α : Type} [DecidableEq α] {a : α} {xs : List α} (h : xs.elem a = false) :
    a ∉ xs := by
  intro hm
  exact absurd (tmb_elem_of_mem hm) (by simpa using h)

theorem tmb_elem_cons_true {α : Type} [DecidableEq α] (x y : α) (acc : List α)
    (h : acc.elem y = true) : (x :: acc).elem y = true :=
  tmb_elem_of_mem (List.mem_cons_of_mem x (List.elem_iff.mp h))

theorem tmb_elem_cons_false {α : Type} [DecidableEq α] (x y : α) (acc : List α)
    (hy : y ≠ x) (h : acc.elem y = false) : (x :: acc).elem y = false := by
  cases hbit : (x :: acc).elem y with
  | false => rfl
  | true =>
    cases List.mem_cons.mp (List.elem_iff.mp hbit) with
    | inl hxy => exact absurd hxy hy
    | inr hacc => exact absurd (tmb_elem_of_mem hacc) (by simpa using h)

theorem tmb_elem_append_true {α : Type} [DecidableEq α] (acc : List α) (x y : α)
    (h : acc.elem x = true) : (acc ++ [y]).elem x = true :=
  tmb_elem_of_mem (List.mem_append_left _ (List.elem_iff.mp h))

theorem tmb_elem_append_false {α : Type} [DecidableEq α] (acc : List α) (x y : α)
    (h : acc.elem x = false) (hy : y ≠ x) : (acc ++ [y]).elem x = false := by
  cases hbit : (acc ++ [y]).elem x with
  | false => rfl
  | true =>
    cases List.mem_append.mp (List.elem_iff.mp hbit) with
    | inl hacc => exact absurd (tmb_elem_of_mem hacc) (by simpa using h)
    | inr hy' =>
      simp at hy'
      exact absurd hy'.symm hy

theorem tmb_dedup_fold_le {α : Type} [DecidableEq α] (acc xs : List α) :
    (xs.foldl tmb_dedupFold acc).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, tmb_dedupFold]
    by_cases he : acc.elem y = true
    · simp only [he, ite_true, List.length_cons]
      exact Nat.le_trans (ih acc) (Nat.add_le_add_left (Nat.le_succ ys.length) acc.length)
    · have he' : acc.elem y = false := by
        cases hbit : acc.elem y <;> simp_all
      simp only [he', ite_false, List.length_cons]
      have h := ih (acc ++ [y])
      simp only [List.length_append, List.length_singleton] at h
      exact Nat.le_trans h (Nat.le_of_eq (by ac_rfl))

theorem tmb_cancel_add (a b : Nat) : a + b = a + (b + 1) - 1 := by
  rw [← Nat.add_assoc, Nat.add_sub_cancel]

theorem tmb_dedup_fold_dup {α : Type} [DecidableEq α] (acc xs : List α) (x : α)
    (hx : x ∈ xs) (hacc : acc.elem x = true) :
    (xs.foldl tmb_dedupFold acc).length ≤ acc.length + xs.length - 1 := by
  induction xs generalizing acc with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons, tmb_dedupFold]
    cases List.mem_cons.mp hx with
    | inl heq =>
      subst heq
      simp only [hacc, ite_true, List.length_cons]
      exact Nat.le_trans (tmb_dedup_fold_le acc ys) (Nat.le_of_eq (tmb_cancel_add _ _))
    | inr htail =>
      by_cases he : acc.elem y = true
      · simp only [he, ite_true, List.length_cons]
        exact Nat.le_trans (Nat.le_trans (ih acc htail hacc) (Nat.sub_le _ _))
          (Nat.le_of_eq (tmb_cancel_add _ _))
      · have he' : acc.elem y = false := by
          cases hbit : acc.elem y <;> simp_all
        simp only [he', ite_false, List.length_cons]
        have hmem : (acc ++ [y]).elem x = true := tmb_elem_append_true acc x y hacc
        have h := ih (acc ++ [y]) htail hmem
        simp only [List.length_append, List.length_singleton] at h
        exact Nat.le_trans h (Nat.le_of_eq (by
          rw [tmb_cancel_add (acc.length + 1) ys.length, tmb_cancel_add acc.length (ys.length + 1)]
          ac_rfl))

theorem tmb_dedup_fold_push {α : Type} [DecidableEq α] (xs acc : List α) (x : α)
    (hx : ∀ y ∈ xs, y ≠ x) (hacc : acc.elem x = false) :
    xs.foldl tmb_dedupFold (x :: acc) = x :: xs.foldl tmb_dedupFold acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    have hy : y ≠ x := hx y List.mem_cons_self
    simp only [List.foldl_cons, tmb_dedupFold]
    by_cases he : acc.elem y = true
    · have he' : (x :: acc).elem y = true := tmb_elem_cons_true x y acc he
      simp only [he, he', ite_true]
      exact ih acc (fun z hz => hx z (List.mem_cons_of_mem y hz)) hacc
    · have he' : acc.elem y = false := by
        cases hbit : acc.elem y <;> simp_all
      have he'' : (x :: acc).elem y = false := tmb_elem_cons_false x y acc hy he'
      simp only [he', he'', ite_false]
      have happ : (x :: acc) ++ [y] = x :: (acc ++ [y]) := by simp
      have hacc' : (acc ++ [y]).elem x = false := tmb_elem_append_false acc x y hacc hy
      simpa [happ] using ih (acc ++ [y]) (fun z hz => hx z (List.mem_cons_of_mem y hz)) hacc'

theorem tmb_dedup_fresh {α : Type} [DecidableEq α] (x : α) (xs : List α) (hx : x ∉ xs) :
    dedup (x :: xs) = x :: dedup xs := by
  unfold dedup
  exact tmb_dedup_fold_push xs [] x (fun y hy heq => hx (heq ▸ hy)) (by simp)

theorem tmb_dedup_short {α : Type} [DecidableEq α] (xs : List α) (h : ¬ xs.Nodup) :
    (dedup xs).length < xs.length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · have hfold : (dedup (x :: xs)).length ≤ xs.length := by
        have hacc : ([x] : List α).elem x = true := by simp
        unfold dedup
        have hdup := tmb_dedup_fold_dup [x] xs x hx hacc
        have hbound : ([x] : List α).length + xs.length - 1 = xs.length := by
          simp [List.length_singleton]
        exact Nat.le_trans hdup (Nat.le_of_eq hbound)
      simp only [List.length_cons]
      exact Nat.lt_succ_of_le hfold
    · have hxs : ¬ xs.Nodup := by
        intro hnd
        exact h (List.nodup_cons.mpr ⟨hx, hnd⟩)
      have ih' := ih hxs
      have heq := tmb_dedup_fresh x xs hx
      simpa [heq, List.length_cons] using Nat.succ_lt_succ ih'

theorem tmb_len_nodup {α : Type} [DecidableEq α] (xs : List α)
    (h : xs.length = (dedup xs).length) : xs.Nodup := by
  by_cases hnd : xs.Nodup
  · exact hnd
  · have hlt := tmb_dedup_short xs hnd
    exact absurd h (Nat.ne_of_lt (by simpa [h] using hlt))

theorem tmb_names_nodup (D : Description) (hG : GraphOk D) :
    (D.templates.map (·.name)).Nodup := by
  have hname : nameFails D = [] := by
    have hstruct : structLines D = [] := hG.struct
    simp [structLines] at hstruct
    exact hstruct.1
  simp [nameFails] at hname
  exact tmb_len_nodup _ (by simpa [List.length_map] using hname)

theorem tmb_find_unique (ts : List Template) (t : Template) (ht : t ∈ ts)
    (hnd : (ts.map (·.name)).Nodup) :
    ts.findSome? (fun u => if u.name == t.name then some u else none) = some t := by
  induction ts with
  | nil => cases ht
  | cons a as ih =>
    rw [List.findSome?_cons]
    cases ht with
    | head => simp
    | tail _ ht =>
      simp [List.map] at hnd
      have hne : a.name ≠ t.name := by
        intro heq
        exact absurd heq.symm (hnd.1 t ht)
      have hb : (a.name == t.name) = false := by simpa [beq_iff_eq] using hne
      simp only [hb, ite_false]
      exact ih ht hnd.2

theorem tmb_template_of_unique (D : Description) (hG : GraphOk D) (t : Template)
    (ht : t ∈ D.templates) : templateOf D t.name = some t := by
  simpa [templateOf] using tmb_find_unique D.templates t ht (tmb_names_nodup D hG)

theorem lane_cast (I : Impl) (w w' : World)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio) (id : InstId)
    (h : LaneOk I w id) : LaneOk I w' id := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hprio id] using h.ordNodup
  · intro l hl
    exact h.ordIn l (by simpa [hprio id] using hl)
  · intro m hm ht
    exact h.peer m (by simpa [hprio id] using hm) ht
  · simpa [hprio id] using h.tombNodup

theorem lifeHold_eq (a b : Actor) (hl : a.life = b.life) (hp : a.pendingTombstone = b.pendingTombstone) :
    lifeHold a = lifeHold b := by
  simp [lifeHold, hl, hp]

theorem occupant_eq (a b : Actor) (hl : a.life = b.life) : occupant a = occupant b := by
  simp [occupant, hl]

/-- A step that keeps every life, priority lane, and tombstone arm, and leaves
every roster phase declared, keeps the lane invariant. -/
theorem hold_actors (I : Impl) (w w' : World) (hH : Hold I w)
    (hN : w'.N = w.N) (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hphase : ∀ id, id ∈ w'.roster → phaseDeclared I (tname id) (w'.st id).phase)
    (hcrash : w'.crashed = false) (hpre : w.crashed = false) : Hold I w' := by
  refine ⟨?_, ?_, ?_, ?_, hphase, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    exact hros ▸ hH.rostered id (by simpa [hlife id] using hl)
  · intro id hp
    have h := hH.pend id (by simpa [hpend id] using hp)
    simpa [hlife id] using h
  · intro _ id hd
    exact hprio id ▸ hH.deadPrio hpre id (by simpa [hlife id] using hd)
  · intro id hid
    exact hH.role id (by simpa [hros] using hid)
  · intro id
    exact lane_cast I w w' hprio id (hH.lane id)
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c) (hpend c)] using hhold
    have hlegal := hH.legalLife parent c (by simpa [hros] using hc) hchild hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hN] using hlegal
  · intro parent name k hq
    have hq' : slotTombstoneQueued w parent name k = true := by
      simpa [slotTombstoneQueued, hprio parent] using hq
    simpa [hN] using hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c) (hpend c)] using hhold
    have hfresh := hH.fresh parent c (by simpa [hros] using hc) hchild hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [slotTombstoneQueued, hprio parent] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    have ho1' : occupant (w.st c1) = true := by
      simpa [occupant_eq (w'.st c1) (w.st c1) (hlife c1)] using ho1
    have ho2' : occupant (w.st c2) = true := by
      simpa [occupant_eq (w'.st c2) (w.st c2) (hlife c2)] using ho2
    exact hH.occ c1 c2 (by simpa [hros] using hc1) (by simpa [hros] using hc2) ho1' ho2' hslot hsup

theorem crash_fields (w : World) (i : InstId) :
    ((crashWorld w).st i).prio = (w.st i).prio ∧
      ((crashWorld w).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      (crashWorld w).roster = w.roster ∧ (crashWorld w).N = w.N ∧
      (crashWorld w).crashed = true := by
  unfold crashWorld
  dsimp
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · by_cases hc : decide (i ∈ w.roster) = true
    · simp only [hc, ite_true, crashActor]
      by_cases hl : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
      · simp [hl]
      · have hf : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = false := by
          cases hbit : (w.st i).life == .alive || (w.st i).life == .shuttingDown <;> simp_all
        simp [hf]
    · have hf : decide (i ∈ w.roster) = false := by
        cases hbit : decide (i ∈ w.roster) <;> simp_all
      simp [hf]
  · by_cases hc : decide (i ∈ w.roster) = true
    · simp only [hc, ite_true, crashActor]
      by_cases hl : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
      · simp [hl]
      · have hf : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = false := by
          cases hbit : (w.st i).life == .alive || (w.st i).life == .shuttingDown <;> simp_all
        simp [hf]
    · have hf : decide (i ∈ w.roster) = false := by
        cases hbit : decide (i ∈ w.roster) <;> simp_all
      simp [hf]

theorem crash_life (w : World) (i : InstId) :
    ((crashWorld w).st i).life =
      if decide (i ∈ w.roster) = true then
        if ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true then .dead
        else (w.st i).life
      else (w.st i).life := by
  unfold crashWorld
  dsimp
  by_cases hc : decide (i ∈ w.roster) = true
  · simp only [hc, ite_true, crashActor]
    by_cases hl : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
    · simp [hl]
    · have hf : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = false := by
        cases hbit : (w.st i).life == .alive || (w.st i).life == .shuttingDown <;> simp_all
      simp [hf]
  · have hf : decide (i ∈ w.roster) = false := by
      cases hbit : decide (i ∈ w.roster) <;> simp_all
    simp [hf]

theorem crash_phase (w : World) (i : InstId) :
    ((crashWorld w).st i).phase =
      if decide (i ∈ w.roster) = true then
        if ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true then .crashed
        else (w.st i).phase
      else (w.st i).phase := by
  unfold crashWorld
  dsimp
  by_cases hc : decide (i ∈ w.roster) = true
  · simp only [hc, ite_true, crashActor]
    by_cases hl : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
    · simp [hl]
    · have hf : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = false := by
        cases hbit : (w.st i).life == .alive || (w.st i).life == .shuttingDown <;> simp_all
      simp [hf]
  · have hf : decide (i ∈ w.roster) = false := by
      cases hbit : decide (i ∈ w.roster) <;> simp_all
    simp [hf]

theorem hold_crash (I : Impl) (w : World) (hH : Hold I w) : Hold I (crashWorld w) := by
  have hf := fun i => crash_fields w i
  have lifeSame (i : InstId)
      (hc : decide (i ∈ w.roster) = false ∨
        ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = false) :
      ((crashWorld w).st i).life = (w.st i).life ∧
        ((crashWorld w).st i).phase = (w.st i).phase := by
    cases hc with
    | inl hdec => exact ⟨by simp [crash_life, hdec], by simp [crash_phase, hdec]⟩
    | inr hlive =>
      by_cases hdec : decide (i ∈ w.roster) = true
      · exact ⟨by simp [crash_life, hdec, hlive], by simp [crash_phase, hdec, hlive]⟩
      · have hno : decide (i ∈ w.roster) = false := by
          cases hbit : decide (i ∈ w.roster) <;> simp_all
        exact ⟨by simp [crash_life, hno], by simp [crash_phase, hno]⟩
  have lifeDead (i : InstId) (hdec : decide (i ∈ w.roster) = true)
      (hlive : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true) :
      ((crashWorld w).st i).life = .dead ∧ ((crashWorld w).st i).phase = .crashed := by
    exact ⟨by simp [crash_life, hdec, hlive], by simp [crash_phase, hdec, hlive]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    by_cases hc : id ∈ w.roster
    · simpa [(hf id).2.2.1] using hc
    · have hst := (lifeSame id (Or.inl (decide_eq_false hc))).1
      exact hH.rostered id (hst ▸ hl)
  · intro id hp
    by_cases hdec : decide (id ∈ w.roster) = true
    · by_cases hlive : ((w.st id).life == .alive || (w.st id).life == .shuttingDown) = true
      · exact Or.inr (lifeDead id hdec hlive).1
      · have hf' : ((w.st id).life == .alive || (w.st id).life == .shuttingDown) = false := by
          cases hbit : (w.st id).life == .alive || (w.st id).life == .shuttingDown <;> simp_all
        have hold := hH.pend id ((hf id).2.1 ▸ hp)
        simpa [(lifeSame id (Or.inr hf')).1] using hold
    · have hno : decide (id ∈ w.roster) = false := by
        cases hbit : decide (id ∈ w.roster) <;> simp_all
      have hold := hH.pend id ((hf id).2.1 ▸ hp)
      simpa [(lifeSame id (Or.inl hno)).1] using hold
  · intro hc
    simp [(hf (.core "")).2.2.2.2] at hc
  · intro id hid
    exact hH.role id (by simpa [(hf id).2.2.1] using hid)
  · intro id hid
    by_cases hdec : decide (id ∈ w.roster) = true
    · by_cases hlive : ((w.st id).life == .alive || (w.st id).life == .shuttingDown) = true
      · simpa [(lifeDead id hdec hlive).2, phaseDeclared]
      · have hf' : ((w.st id).life == .alive || (w.st id).life == .shuttingDown) = false := by
          cases hbit : (w.st id).life == .alive || (w.st id).life == .shuttingDown <;> simp_all
        simpa [(lifeSame id (Or.inr hf')).2] using hH.phase id (by simpa [(hf id).2.2.1] using hid)
    · have hno : decide (id ∈ w.roster) = false := by
        cases hbit : decide (id ∈ w.roster) <;> simp_all
      simpa [(lifeSame id (Or.inl hno)).2] using hH.phase id (by simpa [(hf id).2.2.1] using hid)
  · intro id
    exact lane_cast I w (crashWorld w) (fun i => (hf i).1) id (hH.lane id)
  · intro parent c hc hchild hhold hnote
    by_cases hdec : decide (c ∈ w.roster) = true
    · by_cases hlive : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = true
      · have hdead : lifeHold ((crashWorld w).st c) = false := by
          simp [lifeHold, (lifeDead c hdec hlive).1]
        simp [hdead] at hhold
      · have hf' : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = false := by
          cases hbit : (w.st c).life == .alive || (w.st c).life == .shuttingDown <;> simp_all
        have hhold' : lifeHold (w.st c) = true := by
          simpa [lifeHold, (lifeSame c (Or.inr hf')).1, (hf c).2.1] using hhold
        have hlegal := hH.legalLife parent c (by simpa [(hf c).2.2.1] using hc) hchild hhold' hnote
        have hN : (crashWorld w).N = w.N := (hf c).2.2.2.1
        cases c with
        | core _ => trivial
        | peer n k g => simpa [hN] using hlegal
    · have hno : decide (c ∈ w.roster) = false := by
        cases hbit : decide (c ∈ w.roster) <;> simp_all
      have hhold' : lifeHold (w.st c) = true := by
        simpa [lifeHold, (lifeSame c (Or.inl hno)).1, (hf c).2.1] using hhold
      have hlegal := hH.legalLife parent c (by simpa [(hf c).2.2.1] using hc) hchild hhold' hnote
      have hN : (crashWorld w).N = w.N := (hf c).2.2.2.1
      cases c with
      | core _ => trivial
      | peer n k g => simpa [hN] using hlegal
  · intro parent name k hq
    have hq' : slotTombstoneQueued w parent name k = true := by
      simpa [slotTombstoneQueued, (hf parent).1] using hq
    simpa [(hf parent).2.2.2.1] using hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    by_cases hdec : decide (c ∈ w.roster) = true
    · by_cases hlive : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = true
      · have hdead : lifeHold ((crashWorld w).st c) = false := by
          simp [lifeHold, (lifeDead c hdec hlive).1]
        simp [hdead] at hhold
      · have hf' : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = false := by
          cases hbit : (w.st c).life == .alive || (w.st c).life == .shuttingDown <;> simp_all
        have hhold' : lifeHold (w.st c) = true := by
          simpa [lifeHold, (lifeSame c (Or.inr hf')).1, (hf c).2.1] using hhold
        have hfresh := hH.fresh parent c (by simpa [(hf c).2.2.1] using hc) hchild hhold' hnote
        cases c with
        | core _ => trivial
        | peer n k g => simpa [slotTombstoneQueued, (hf parent).1] using hfresh
    · have hno : decide (c ∈ w.roster) = false := by
        cases hbit : decide (c ∈ w.roster) <;> simp_all
      have hhold' : lifeHold (w.st c) = true := by
        simpa [lifeHold, (lifeSame c (Or.inl hno)).1, (hf c).2.1] using hhold
      have hfresh := hH.fresh parent c (by simpa [(hf c).2.2.1] using hc) hchild hhold' hnote
      cases c with
      | core _ => trivial
      | peer n k g => simpa [slotTombstoneQueued, (hf parent).1] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    have hocc (c : InstId) (ho : occupant ((crashWorld w).st c) = true) : occupant (w.st c) = true := by
      by_cases hdec : decide (c ∈ w.roster) = true
      · by_cases hlive : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = true
        · have hdead : occupant ((crashWorld w).st c) = false := by
            simp [occupant, (lifeDead c hdec hlive).1]
          simp [hdead] at ho
        · have hf' : ((w.st c).life == .alive || (w.st c).life == .shuttingDown) = false := by
            cases hbit : (w.st c).life == .alive || (w.st c).life == .shuttingDown <;> simp_all
          simpa [occupant, (lifeSame c (Or.inr hf')).1] using ho
      · have hno : decide (c ∈ w.roster) = false := by
          cases hbit : decide (c ∈ w.roster) <;> simp_all
        simpa [occupant, (lifeSame c (Or.inl hno)).1] using ho
    exact hH.occ c1 c2 (by simpa [(hf c1).2.2.1] using hc1)
      (by simpa [(hf c2).2.2.1] using hc2) (hocc c1 ho1) (hocc c2 ho2) hslot hsup

theorem lane_nil (I : Impl) (w : World) (id : InstId) (h : (w.st id).prio = []) : LaneOk I w id := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tmb_laneLabels, h]
  · intro l hl
    simp [tmb_laneLabels, h] at hl
  · intro m hm _
    simp [h] at hm
  · simp [tombSlots, h]

theorem tmb_cell_fold_st (D : Description) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun w id => readCells D w id) w).st i) = w.st i := by
  induction ids generalizing w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (ih (readCells D w x)).trans (cellsSt D w x i)

theorem tmb_cell_fold_roster (D : Description) (ids : List InstId) (w : World) :
    (ids.foldl (fun w id => readCells D w id) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (ih (readCells D w x)).trans (cellsRoster D w x)

theorem tmb_cell_fold_N (D : Description) (ids : List InstId) (w : World) :
    (ids.foldl (fun w id => readCells D w id) w).N = w.N := by
  induction ids generalizing w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (ih (readCells D w x)).trans (cellsN D w x)

theorem tmb_core_go (ts : List Template) (id : InstId)
    (h : id ∈ ts.filterMap fun t => if t.multiplicity == .one then some (.core t.name) else none) :
    ∃ t, t ∈ ts ∧ id = .core t.name ∧ t.multiplicity = .one := by
  induction ts with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.filterMap_cons] at h
    by_cases hone : (a.multiplicity == .one) = true
    · simp only [hone, ite_true] at h
      cases List.mem_cons.mp h with
      | inl heq =>
        have hm : a.multiplicity = .one := by
          cases hmul : a.multiplicity with
          | one => rfl
          | perPeer =>
            simp [hmul, show (Multiplicity.perPeer == Multiplicity.one) = false from rfl] at hone
        exact ⟨a, List.mem_cons_self, heq, hm⟩
      | inr htail =>
        obtain ⟨t, ht, hid, hm⟩ := ih htail
        exact ⟨t, List.mem_cons_of_mem _ ht, hid, hm⟩
    · have hf : (a.multiplicity == .one) = false := by
        cases hbit : a.multiplicity == .one <;> simp_all
      simp only [hf, ite_false] at h
      obtain ⟨t, ht, hid, hm⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht, hid, hm⟩

theorem tmb_core_roster (D : Description) (id : InstId) (h : id ∈ coreRoster D) :
    ∃ t, t ∈ D.templates ∧ id = .core t.name ∧ t.multiplicity = .one := by
  simpa [coreRoster] using tmb_core_go D.templates id (by simpa [coreRoster] using h)

theorem hold_init (I : Impl) (N : Nat) (hG : GraphOk I.desc) : Hold I (initWorld I N) := by
  have hfoldSt := fun i =>
    tmb_cell_fold_st I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } i
  have hst (i : InstId) :
      ((initWorld I N).st i) =
        if (coreRoster I.desc).contains i then initActor I.desc i else absentActor := by
    simpa [initWorld] using hfoldSt i
  have hros : (initWorld I N).roster = coreRoster I.desc := by
    simpa [initWorld] using tmb_cell_fold_roster I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }
  have hN : (initWorld I N).N = N := by
    simpa [initWorld] using tmb_cell_fold_N I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }
  have hlife (i : InstId) :
      ((initWorld I N).st i).life =
        if (coreRoster I.desc).contains i then .alive else .absent := by
    rw [hst i]
    by_cases hc : (coreRoster I.desc).contains i = true
    · simp only [hc, ite_true]
      obtain ⟨t, ht, hid, hm⟩ := tmb_core_roster I.desc i (List.elem_iff.mp hc)
      have hlook := tmb_template_of_unique I.desc hG t ht
      cases hid
      rw [initActor]
      simp only [tname, hlook]
      rfl
    · have hf : (coreRoster I.desc).contains i = false := by
        cases hbit : (coreRoster I.desc).contains i <;> simp_all
      have hnin : i ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [hnin, absentActor]
  have hprio (i : InstId) : ((initWorld I N).st i).prio = [] := by
    rw [hst i]
    by_cases hc : (coreRoster I.desc).contains i = true
    · simp only [hc, ite_true]
      obtain ⟨t, ht, hid, _⟩ := tmb_core_roster I.desc i (List.elem_iff.mp hc)
      have hlook := tmb_template_of_unique I.desc hG t ht
      cases hid
      rw [initActor]
      simp only [tname, hlook]
      rfl
    · have hf : (coreRoster I.desc).contains i = false := by
        cases hbit : (coreRoster I.desc).contains i <;> simp_all
      have hnin : i ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [hnin, absentActor]
  have hpend (i : InstId) : ((initWorld I N).st i).pendingTombstone = false := by
    rw [hst i]
    by_cases hc : (coreRoster I.desc).contains i = true
    · simp only [hc, ite_true]
      obtain ⟨t, ht, hid, _⟩ := tmb_core_roster I.desc i (List.elem_iff.mp hc)
      have hlook := tmb_template_of_unique I.desc hG t ht
      cases hid
      rw [initActor]
      simp only [tname, hlook]
      rfl
    · have hf : (coreRoster I.desc).contains i = false := by
        cases hbit : (coreRoster I.desc).contains i <;> simp_all
      have hnin : i ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [hnin, absentActor]
  have hphase (i : InstId) : ((initWorld I N).st i).phase = .idle := by
    rw [hst i]
    by_cases hc : (coreRoster I.desc).contains i = true
    · simp only [hc, ite_true]
      obtain ⟨t, ht, hid, _⟩ := tmb_core_roster I.desc i (List.elem_iff.mp hc)
      have hlook := tmb_template_of_unique I.desc hG t ht
      cases hid
      rw [initActor]
      simp only [tname, hlook]
      rfl
    · have hf : (coreRoster I.desc).contains i = false := by
        cases hbit : (coreRoster I.desc).contains i <;> simp_all
      have hnin : i ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [hnin, absentActor]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    by_cases hc : (coreRoster I.desc).contains id = true
    · exact hros ▸ List.elem_iff.mp hc
    · have hf : (coreRoster I.desc).contains id = false := by
        cases hbit : (coreRoster I.desc).contains id <;> simp_all
      have habs : ((initWorld I N).st id).life = .absent := by
        rw [hlife]
        simp only [hf]
        rfl
      exact absurd habs hl
  · intro id hp
    simp [hpend id] at hp
  · intro _ id hd
    by_cases hc : (coreRoster I.desc).contains id = true
    · rw [hlife] at hd
      simp only [hc] at hd
      cases hd
    · have hf : (coreRoster I.desc).contains id = false := by
        cases hbit : (coreRoster I.desc).contains id <;> simp_all
      rw [hlife] at hd
      simp only [hf] at hd
      cases hd
  · intro id hid
    have hmem : id ∈ coreRoster I.desc := by simpa [hros] using hid
    obtain ⟨t, ht, hidc, hm⟩ := tmb_core_roster I.desc id hmem
    cases hidc
    exact ⟨t, tmb_template_of_unique I.desc hG t ht, by simpa [tmb_role] using hm⟩
  · intro id hid
    simpa [hphase id, phaseDeclared]
  · intro id
    exact lane_nil I (initWorld I N) id (hprio id)
  · intro parent c hc _ hhold _
    have hmem : c ∈ coreRoster I.desc := by simpa [hros] using hc
    cases c with
    | core _ => trivial
    | peer n k g =>
      obtain ⟨_, _, hidc, _⟩ := tmb_core_roster I.desc (.peer n k g) hmem
      cases hidc
  · intro parent name k hq
    have hq' : slotTombstoneQueued (initWorld I N) parent name k = true := hq
    simp [slotTombstoneQueued, hprio parent] at hq'
  · intro parent c hc _ hhold _
    have hmem : c ∈ coreRoster I.desc := by simpa [hros] using hc
    cases c with
    | core _ => trivial
    | peer n k g =>
      obtain ⟨_, _, hidc, _⟩ := tmb_core_roster I.desc (.peer n k g) hmem
      cases hidc
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot _
    obtain ⟨_, _, h1, _⟩ := tmb_core_roster I.desc c1 (by simpa [hros] using hc1)
    obtain ⟨_, _, h2, _⟩ := tmb_core_roster I.desc c2 (by simpa [hros] using hc2)
    cases h1
    cases h2
    simp [sameSlot, beq_iff_eq] at hslot
    exact congrArg InstId.core hslot

theorem hold_set (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (hl : a.life = (w.st id).life) (hp : a.prio = (w.st id).prio)
    (hpe : a.pendingTombstone = (w.st id).pendingTombstone)
    (hph : id ∈ w.roster → phaseDeclared I (tname id) a.phase)
    (hpre : w.crashed = false) : Hold I (setActor w id a) := by
  apply hold_actors I w (setActor w id a) hH rfl rfl
  · intro i
    by_cases h : i = id
    · simp [setActor, h, hl]
    · simp [setActor, h]
  · intro i
    by_cases h : i = id
    · simp [setActor, h, hp]
    · simp [setActor, h]
  · intro i
    by_cases h : i = id
    · simp [setActor, h, hpe]
    · simp [setActor, h]
  · intro i hi
    by_cases h : i = id
    · have hgoal := hph (by simpa [setActor, h] using hi)
      simpa [setActor, h] using hgoal
    · have heq := setActor_other w id i a h
      simpa [heq] using hH.phase i hi
  · simp [setActor, hpre]
  · exact hpre

theorem clear_declared (I : Impl) (template : String) (caller : InstId) (k : Cont)
    (h : ContDeclared I template k) : ContDeclared I template (clearReplyCont caller k) := by
  unfold clearReplyCont
  split
  · exact ⟨h.rest, h.na, h.to, h.timeout⟩
  · exact h

theorem clear_phase_declared (I : Impl) (template : String) (caller : InstId) (ph : Phase)
    (h : phaseDeclared I template ph) : phaseDeclared I template (clearReplyPhase caller ph) := by
  cases ph with
  | run k =>
    simpa [clearReplyPhase, phaseDeclared] using clear_declared I template caller k h
  | parked d c k =>
    simpa [clearReplyPhase, phaseDeclared] using clear_declared I template caller k h
  | awaitReply d k =>
    simpa [clearReplyPhase, phaseDeclared] using clear_declared I template caller k h
  | awaitEffect k =>
    simpa [clearReplyPhase, phaseDeclared] using clear_declared I template caller k h
  | awaitPeer k =>
    simpa [clearReplyPhase, phaseDeclared] using clear_declared I template caller k h
  | idle => simp [clearReplyPhase, phaseDeclared]
  | crashed => simp [clearReplyPhase, phaseDeclared]

theorem proceed_declared (I : Impl) (template : String) (a : Actor) (k : Cont)
    (h : ContDeclared I template k) : phaseDeclared I template (proceed a k).phase := by
  cases hk : k.rest
  · simp [proceed, hk, phaseDeclared]
  · simpa [proceed, hk, phaseDeclared] using h

theorem select_declared (I : Impl) (template : String) (k : Cont) (r : CallResult)
    (h : ContDeclared I template k) : ContDeclared I template (selectCall k r) := by
  cases r with
  | reply => exact h
  | notAdmitted => exact ⟨h.na, h.na, h.to, h.timeout⟩
  | timedOut => exact ⟨h.to, h.na, h.to, h.timeout⟩

theorem finish_declared (I : Impl) (template : String) (a : Actor) (k : Cont) (r : CallResult)
    (h : ContDeclared I template k) : phaseDeclared I template (finishCall a k r).phase := by
  simpa [finishCall] using proceed_declared I template a (selectCall k r) (select_declared I template k r h)

theorem tmb_labels_cons (m : Msg) (ms : List Msg) :
    tmb_laneLabels (m :: ms) =
      if m.tombstone then tmb_laneLabels ms else m.label :: tmb_laneLabels ms := by
  cases ht : m.tombstone <;> simp [tmb_laneLabels, List.filter, ht]

theorem tmb_tombs_cons (m : Msg) (ms : List Msg) :
    tombSlots (m :: ms) =
      (match m.tombstone, m.sender with
        | true, .peer n k _ => [(n, k)]
        | _, _ => []) ++ tombSlots ms := by
  unfold tombSlots
  simp only [List.filterMap_cons]
  cases ht : m.tombstone <;> cases hs : m.sender <;> simp [ht, hs, tombSlots]

theorem lane_of_tail (I : Impl) (template : String) (m : Msg) (ms : List Msg)
    (hnd : (tmb_laneLabels (m :: ms)).Nodup)
    (hin : ∀ l, l ∈ tmb_laneLabels (m :: ms) → l ∈ prioLabels I template)
    (hpeer : ∀ m', m' ∈ m :: ms → m'.tombstone = true → ∃ n k g, m'.sender = .peer n k g)
    (htomb : (tombSlots (m :: ms)).Nodup) :
    (tmb_laneLabels ms).Nodup ∧ (∀ l, l ∈ tmb_laneLabels ms → l ∈ prioLabels I template) ∧
      (∀ m', m' ∈ ms → m'.tombstone = true → ∃ n k g, m'.sender = .peer n k g) ∧
      (tombSlots ms).Nodup := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tmb_labels_cons] at hnd
    cases ht : m.tombstone with
    | true => simpa [ht] using hnd
    | false =>
      simp [ht] at hnd
      exact hnd.2
  · intro l hl
    rw [tmb_labels_cons] at hin
    cases ht : m.tombstone
    · exact hin l (by simp [ht, hl])
    · exact hin l (by simpa [ht] using hl)
  · intro m' hm' ht'
    exact hpeer m' (List.mem_cons_of_mem _ hm') ht'
  · rw [tmb_tombs_cons] at htomb
    cases ht : m.tombstone with
    | false => simpa [ht] using htomb
    | true =>
      cases hs : m.sender with
      | core _ => simpa [ht, hs] using htomb
      | peer n k g =>
        simp [ht, hs] at htomb
        exact htomb.2

/-- Dropping the head of one priority lane preserves the invariant. -/
theorem hold_drop (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (hN : w'.N = w.N) (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hhead : ∃ m, (w.st id).prio = m :: (w'.st id).prio)
    (hother : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio)
    (hphase : ∀ i, i ∈ w'.roster → phaseDeclared I (tname i) (w'.st i).phase)
    (hcrash : w'.crashed = false) (hpre : w.crashed = false) : Hold I w' := by
  obtain ⟨m, hcons⟩ := hhead
  refine ⟨?_, ?_, ?_, ?_, hphase, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    exact hros ▸ hH.rostered i (by simpa [hlife i] using hl)
  · intro i hp
    simpa [hlife i] using hH.pend i (by simpa [hpend i] using hp)
  · intro _ i hd
    by_cases h : i = id
    · have htail := lane_of_tail I (tname id) m (w'.st id).prio
        (by simpa [hcons] using (hH.lane id).ordNodup)
        (by simpa [hcons] using (hH.lane id).ordIn)
        (by simpa [hcons] using (hH.lane id).peer)
        (by simpa [hcons] using (hH.lane id).tombNodup)
      -- a dead actor's whole lane was empty, so it had no head to drop
      have hempty := hH.deadPrio hpre id (by simpa [h, hlife id] using hd)
      simp [h, hcons] at hempty
    · exact hother i h ▸ hH.deadPrio hpre i (by simpa [hlife i] using hd)
  · intro i hid
    exact hH.role i (by simpa [hros] using hid)
  · intro i
    by_cases h : i = id
    · have htail := lane_of_tail I (tname id) m (w'.st id).prio
        (by simpa [hcons] using (hH.lane id).ordNodup)
        (by simpa [hcons] using (hH.lane id).ordIn)
        (by simpa [hcons] using (hH.lane id).peer)
        (by simpa [hcons] using (hH.lane id).tombNodup)
      exact ⟨by simpa [h] using htail.1, by simpa [h] using htail.2.1,
        by simpa [h] using htail.2.2.1, by simpa [h] using htail.2.2.2⟩
    · have hold := hH.lane i
      exact ⟨by simpa [hother i h] using hold.ordNodup,
        fun l hl => hold.ordIn l (by simpa [hother i h] using hl),
        fun msg hm ht => hold.peer msg (by simpa [hother i h] using hm) ht,
        by simpa [hother i h] using hold.tombNodup⟩
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c) (hpend c)] using hhold
    have hlegal := hH.legalLife parent c (by simpa [hros] using hc) hchild hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hN] using hlegal
  · intro parent name k hq
    have hwas : slotTombstoneQueued w parent name k = true := by
      by_cases h : parent = id
      · -- a key queued on the tail was queued on the whole lane
        have hmem : (name, k) ∈ tombSlots (w'.st parent).prio := (tmb_queued_iff w' parent name k).mp hq
        have htail := lane_of_tail I (tname parent) m (w'.st parent).prio
          (by simpa [h, hcons] using (hH.lane id).ordNodup)
          (by simpa [h, hcons] using (hH.lane id).ordIn)
          (by simpa [h, hcons] using (hH.lane id).peer)
          (by simpa [h, hcons] using (hH.lane id).tombNodup)
        have hcons' : tombSlots (w.st parent).prio =
            (match m.tombstone, m.sender with
              | true, .peer n k _ => [(n, k)]
              | _, _ => []) ++ tombSlots (w'.st parent).prio := by
          simpa [h, hcons] using tmb_tombs_cons m (w'.st parent).prio
        have hsub : (name, k) ∈ tombSlots (w.st parent).prio := by
          rw [hcons']
          exact List.mem_append_right _ hmem
        exact (tmb_queued_iff w parent name k).mpr hsub
      · have hq' : slotTombstoneQueued w parent name k = true := by
          simpa [slotTombstoneQueued, hother parent h] using hq
        exact hq'
    simpa [hN] using hH.legalTomb parent name k hwas
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c) (hpend c)] using hhold
    have hfresh := hH.fresh parent c (by simpa [hros] using hc) hchild hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g =>
      by_cases h : parent = id
      · -- not queued on the whole lane, hence not on the tail
        have hnot : slotTombstoneQueued w parent n k = false := by simpa [h] using hfresh
        -- if the tail queued it, the whole lane queued it
        by_cases hq : slotTombstoneQueued w' parent n k = true
        · have hmem : (n, k) ∈ tombSlots (w'.st parent).prio := (tmb_queued_iff w' parent n k).mp hq
          have hcons' : tombSlots (w.st parent).prio =
              (match m.tombstone, m.sender with
                | true, .peer n1 k1 _ => [(n1, k1)]
                | _, _ => []) ++ tombSlots (w'.st parent).prio := by
            simpa [h, hcons] using tmb_tombs_cons m (w'.st parent).prio
          have hwas : (n, k) ∈ tombSlots (w.st parent).prio := by
            rw [hcons']
            exact List.mem_append_right _ hmem
          have htrue : slotTombstoneQueued w parent n k = true := (tmb_queued_iff w parent n k).mpr hwas
          simp [htrue] at hnot
        · have hf : slotTombstoneQueued w' parent n k = false := by
            cases hbit : slotTombstoneQueued w' parent n k <;> simp_all
          simpa [h] using hf
      · simpa [slotTombstoneQueued, hother parent h] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    have ho1' : occupant (w.st c1) = true := by
      simpa [occupant_eq (w'.st c1) (w.st c1) (hlife c1)] using ho1
    have ho2' : occupant (w.st c2) = true := by
      simpa [occupant_eq (w'.st c2) (w.st c2) (hlife c2)] using ho2
    exact hH.occ c1 c2 (by simpa [hros] using hc1) (by simpa [hros] using hc2) ho1' ho2' hslot hsup

/-- A shutdown step: lanes, roster, and population stay, a life only moves from
alive to shutting down, a newly armed actor is shutting down or dead, and a
phase is either untouched or idle. Every life that still holds a slot already
held it. -/
structure Marked (w w' : World) : Prop where
  N : w'.N = w.N
  roster : w'.roster = w.roster
  crashed : w'.crashed = w.crashed
  prio : ∀ i, (w'.st i).prio = (w.st i).prio
  life : ∀ i, (w'.st i).life = (w.st i).life ∨
    ((w.st i).life = .alive ∧ (w'.st i).life = .shuttingDown)
  pend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone ∨
    ((w'.st i).pendingTombstone = true ∧
      ((w'.st i).life = .shuttingDown ∨ (w'.st i).life = .dead))
  phase : ∀ i, (w'.st i).phase = (w.st i).phase ∨ (w'.st i).phase = .idle
  held : ∀ i, lifeHold (w'.st i) = true → lifeHold (w.st i) = true

theorem Marked.refl (w : World) : Marked w w :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun _ h => h⟩

theorem alive_hold (a : Actor) (h : a.life = .alive) : lifeHold a = true := by
  simp [lifeHold, h]

theorem Marked.trans {w w1 w' : World} (h1 : Marked w w1) (h2 : Marked w1 w') : Marked w w' := by
  refine ⟨h2.N.trans h1.N, h2.roster.trans h1.roster, h2.crashed.trans h1.crashed, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (h2.prio i).trans (h1.prio i)
  · intro i
    cases h2.life i with
    | inl heq =>
      cases h1.life i with
      | inl h0 => exact Or.inl (heq.trans h0)
      | inr hch => exact Or.inr ⟨hch.1, heq ▸ hch.2⟩
    | inr hch =>
      cases h1.life i with
      | inl h0 => exact Or.inr ⟨h0 ▸ hch.1, hch.2⟩
      | inr hwas =>
        -- the second step only leaves alive, and the first already left it
        simp [hwas.2] at hch
  · intro i
    cases h2.pend i with
    | inr hset => exact Or.inr hset
    | inl heq =>
      cases h1.pend i with
      | inl h0 => exact Or.inl (heq.trans h0)
      | inr hset =>
        cases h2.life i with
        | inl hl => exact Or.inr ⟨heq ▸ hset.1, by simpa [hl] using hset.2⟩
        | inr hch =>
          cases hset.2 with
          | inl hs => simp [hs] at hch
          | inr hd => simp [hd] at hch
  · intro i
    cases h2.phase i with
    | inl heq =>
      cases h1.phase i with
      | inl h0 => exact Or.inl (heq.trans h0)
      | inr hidle => exact Or.inr (heq ▸ hidle)
    | inr hidle => exact Or.inr hidle
  · intro i hh
    exact h1.held i (h2.held i hh)

theorem hold_marked (I : Impl) (w w' : World) (hH : Hold I w) (hM : Marked w w')
    (hpre : w.crashed = false) : Hold I w' := by
  have hcrash : w'.crashed = false := by simpa [hM.crashed] using hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    have hold : (w.st id).life ≠ .absent := by
      cases hM.life id with
      | inl heq => simpa [heq] using hl
      | inr hch =>
        rw [hch.1]
        intro h
        cases h
    exact hM.roster ▸ hH.rostered id hold
  · intro id hp
    cases hM.pend id with
    | inl heq =>
      have hold := hH.pend id (by simpa [heq] using hp)
      cases hM.life id with
      | inl hl => simpa [hl] using hold
      | inr hch => exact Or.inl hch.2
    | inr hset => exact hset.2
  · intro _ id hd
    cases hM.life id with
    | inl heq => exact hM.prio id ▸ hH.deadPrio hpre id (by simpa [heq] using hd)
    | inr hch => simp [hch.2] at hd
  · intro id hid
    exact hH.role id (by simpa [hM.roster] using hid)
  · intro id hid
    cases hM.phase id with
    | inl heq => simpa [heq] using hH.phase id (by simpa [hM.roster] using hid)
    | inr hidle => simpa [hidle, phaseDeclared]
  · intro id
    have hold := hH.lane id
    exact ⟨by simpa [hM.prio id] using hold.ordNodup,
      fun l hl => hold.ordIn l (by simpa [hM.prio id] using hl),
      fun msg hm ht => hold.peer msg (by simpa [hM.prio id] using hm) ht,
      by simpa [hM.prio id] using hold.tombNodup⟩
  · intro parent c hc hchild hhold hnote
    have hwas := hM.held c hhold
    have hlegal := hH.legalLife parent c (by simpa [hM.roster] using hc) hchild hwas hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hM.N] using hlegal
  · intro parent name k hq
    have hq' : slotTombstoneQueued w parent name k = true := by
      simpa [slotTombstoneQueued, hM.prio parent] using hq
    simpa [hM.N] using hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    have hwas := hM.held c hhold
    have hfresh := hH.fresh parent c (by simpa [hM.roster] using hc) hchild hwas hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [slotTombstoneQueued, hM.prio parent] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    have hold (c : InstId) (ho : occupant (w'.st c) = true) : occupant (w.st c) = true := by
      cases hM.life c with
      | inl heq => simpa [occupant, heq] using ho
      | inr hch => simp [occupant, hch.1]
    exact hH.occ c1 c2 (by simpa [hM.roster] using hc1) (by simpa [hM.roster] using hc2)
      (hold c1 ho1) (hold c2 ho2) hslot hsup

theorem tmb_dropHost_extra (dead : InstId) (w : World) (host i : InstId) :
    ((tmb_dropHost dead w host).st i).phase = (w.st i).phase ∧
      (tmb_dropHost dead w host).crashed = w.crashed := by
  unfold tmb_dropHost
  by_cases hdead : (host == dead) = true
  · simp [hdead]
  · have hf : (host == dead) = false := by
      cases hbb : host == dead <;> simp_all
    simp only [hf, ite_false]
    by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · simp [hempty]
    · have hne : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false := by
        cases hbb : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty <;> simp_all
      simp only [hne, ite_false]
      by_cases hi : i = dead
      · have hnh : host ≠ dead := by
          intro heq
          have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
          simp [hb] at hf
        rw [hi]
        have hdir : dead ≠ host := hnh.symm
        simp [setActor, addTokens, hdir]
      · by_cases hh : i = host
        · have hnd : host ≠ dead := by
            intro heq
            have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
            simp [hb] at hf
          rw [hh]
          simp [setActor, hnd]
        · simp [setActor, hi, hh]

theorem tmb_fold_extra (dead : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (tmb_dropHost dead) w).st i).phase = (w.st i).phase ∧
        (ids.foldl (tmb_dropHost dead) w).crashed = w.crashed := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons host ids ih =>
    intro w i
    simp only [List.foldl_cons]
    have h1 := tmb_dropHost_extra dead w host i
    have h2 := ih (tmb_dropHost dead w host) i
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem release_extra (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).phase = (w.st i).phase ∧
      (releaseOutbound w dead).crashed = w.crashed := by
  simpa [tmb_dropHost_eq] using tmb_fold_extra dead w.roster w i

def tmb_marked (a : Actor) : Actor :=
  { a with life := .shuttingDown, phase := .idle }

def tmb_dead (a : Actor) : Actor :=
  { a with life := .dead, phase := .idle, box := [], prio := [], parked := [] }

def tmb_snoc (w : World) (parent : InstId) (msg : Msg) : World :=
  setActor w parent { (w.st parent) with prio := (w.st parent).prio ++ [msg], nextMid := (w.st parent).nextMid + 1 }

theorem tmb_snoc_life (w : World) (parent : InstId) (msg : Msg) (i : InstId) :
    ((tmb_snoc w parent msg).st i).life = (w.st i).life := by
  unfold tmb_snoc; by_cases hi : i = parent <;> simp [setActor, hi]

theorem tmb_snoc_pend (w : World) (parent : InstId) (msg : Msg) (i : InstId) :
    ((tmb_snoc w parent msg).st i).pendingTombstone = (w.st i).pendingTombstone := by
  unfold tmb_snoc; by_cases hi : i = parent <;> simp [setActor, hi]

theorem tmb_snoc_phase (w : World) (parent : InstId) (msg : Msg) (i : InstId) :
    ((tmb_snoc w parent msg).st i).phase = (w.st i).phase := by
  unfold tmb_snoc; by_cases hi : i = parent <;> simp [setActor, hi]

theorem tmb_snoc_prio_self (w : World) (parent : InstId) (msg : Msg) :
    ((tmb_snoc w parent msg).st parent).prio = (w.st parent).prio ++ [msg] := by
  unfold tmb_snoc; simp [setActor]

theorem tmb_snoc_prio_other (w : World) (parent : InstId) (msg : Msg) (i : InstId) (hi : i ≠ parent) :
    ((tmb_snoc w parent msg).st i).prio = (w.st i).prio := by
  unfold tmb_snoc; simp [setActor, hi]

theorem tmb_snoc_roster (w : World) (parent : InstId) (msg : Msg) :
    (tmb_snoc w parent msg).roster = w.roster := by unfold tmb_snoc; simp [setActor]

theorem tmb_snoc_N (w : World) (parent : InstId) (msg : Msg) :
    (tmb_snoc w parent msg).N = w.N := by unfold tmb_snoc; simp [setActor]

theorem tmb_snoc_crash (w : World) (parent : InstId) (msg : Msg) :
    (tmb_snoc w parent msg).crashed = w.crashed := by unfold tmb_snoc; simp [setActor]

theorem tmb_any_snoc (ms : List Msg) (msg : Msg) (name : String) (k : Nat) :
    ((ms ++ [msg]).any (tmb_hit name k)) = (ms.any (tmb_hit name k) || tmb_hit name k msg) := by
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem tmb_hit_eq (n : String) (k : Nat) (m : Msg) :
    tmb_hit n k m =
      (m.tombstone &&
        match m.sender with
        | .peer a b _ => a == n && b == k
        | .core _ => false) := by
  unfold tmb_hit
  rfl

theorem tmb_any_hit (ms : List Msg) (n : String) (k : Nat) :
    (ms.any fun m =>
      m.tombstone &&
        match m.sender with
        | .peer a b _ => a == n && b == k
        | .core _ => false) = ms.any (tmb_hit n k) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [List.any_cons, tmb_hit_eq n k m, ih]

theorem tmb_queued_self (w : World) (parent : InstId) (msg : Msg) (n : String) (key : Nat) :
    slotTombstoneQueued (tmb_snoc w parent msg) parent n key =
      ((w.st parent).prio ++ [msg]).any (tmb_hit n key) := by
  unfold slotTombstoneQueued
  rw [tmb_snoc_prio_self]
  exact (tmb_any_hit ((w.st parent).prio ++ [msg]) n key).symm

theorem tmb_queued_other (w : World) (parent : InstId) (msg : Msg) (p : InstId)
    (n : String) (key : Nat) (hp : p ≠ parent) :
    slotTombstoneQueued (tmb_snoc w parent msg) p n key = slotTombstoneQueued w p n key := by
  simp only [slotTombstoneQueued, tmb_snoc_prio_other w parent msg p hp]

theorem markShutdown_marked (w : World) (id : InstId) : Marked w (markShutdown w id) := by
  cases hlive : (w.st id).life == .alive
  · rw [show markShutdown w id = w by simp [markShutdown, hlive]]
    exact Marked.refl w
  · have hl : (w.st id).life = .alive := by simpa [beq_iff_eq] using hlive
    suffices Marked w (releaseOutbound (setActor w id (tmb_marked (w.st id))) id) by
      simpa [markShutdown, tmb_marked, hlive] using this
    let w1 := setActor w id (tmb_marked (w.st id))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (releaseOutbound_prio w1 id id).2
    · exact (releaseOutbound_keep w1 id id).2.2
    · exact (release_extra w1 id id).2
    · intro i
      have hr := (releaseOutbound_prio w1 id i).1
      by_cases hi : i = id
      · rw [hr, hi]
        simp [w1, setActor_self, tmb_marked]
      · rw [hr]
        simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
    · intro i
      have hr := (releaseOutbound_keep w1 id i).1
      by_cases hi : i = id
      · refine Or.inr ⟨by simpa [hi] using hl, ?_⟩
        rw [hr, hi]
        simp [w1, setActor_self, tmb_marked]
      · exact Or.inl <| by
          rw [hr]
          simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
    · intro i
      have hr := (releaseOutbound_keep w1 id i).2.1
      exact Or.inl <| by
        rw [hr]
        by_cases hi : i = id
        · rw [hi]
          simp [w1, setActor_self, tmb_marked]
        · simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
    · intro i
      have hr := (release_extra w1 id i).1
      by_cases hi : i = id
      · exact Or.inr <| by
          rw [hr, hi]
          simp [w1, setActor_self, tmb_marked]
      · exact Or.inl <| by
          rw [hr]
          simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
    · intro i hh
      by_cases hi : i = id
      · simpa [hi] using alive_hold (w.st id) hl
      · have hlife : ((releaseOutbound w1 id).st i).life = (w.st i).life := by
          rw [(releaseOutbound_keep w1 id i).1]
          simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
        have hpend : ((releaseOutbound w1 id).st i).pendingTombstone = (w.st i).pendingTombstone := by
          rw [(releaseOutbound_keep w1 id i).2.1]
          simp [w1, setActor_other w id i (tmb_marked (w.st id)) hi]
        exact (lifeHold_eq _ _ hlife hpend).symm ▸ hh

theorem mark_shuts (w : World) (id : InstId) (h : (w.st id).life = .alive) :
    ((markShutdown w id).st id).life = .shuttingDown := by
  have hb : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using h
  suffices ((releaseOutbound (setActor w id (tmb_marked (w.st id))) id).st id).life = .shuttingDown by
    simpa [markShutdown, tmb_marked, hb] using this
  simpa [setActor_self, tmb_marked] using
    (releaseOutbound_keep (setActor w id (tmb_marked (w.st id))) id id).1

theorem mark_fold (fuel : Nat) (D : Description) (root : InstId)
    (ih : ∀ w id, Marked w (markTree fuel D w id)) :
    ∀ ids : List InstId, ∀ w : World,
      Marked w (ids.foldl (fun w child =>
        if isChild D root child then markTree fuel D w child else w) w) := by
  intro ids
  induction ids with
  | nil => intro w; simp; exact Marked.refl w
  | cons child ids ihf =>
    intro w
    simp only [List.foldl_cons]
    cases hc : isChild D root child
    · have hstep : (if false = true then markTree fuel D w child else w) = w := by simp
      rw [hstep]
      exact ihf w
    · have hstep :
        (if true = true then markTree fuel D w child else w) = markTree fuel D w child := by simp
      rw [hstep]
      exact Marked.trans (ih w child) (ihf (markTree fuel D w child))

theorem markTree_marked (fuel : Nat) (D : Description) :
    ∀ w id, Marked w (markTree fuel D w id) := by
  induction fuel with
  | zero =>
    intro w id
    rw [show markTree 0 D w id = w from rfl]
    exact Marked.refl w
  | succ fuel ih =>
    intro w id
    rw [show markTree (fuel + 1) D w id =
        (let marked := markShutdown w id
        marked.roster.foldl (fun w child =>
          if isChild D id child then markTree fuel D w child else w) marked) from rfl]
    exact Marked.trans (markShutdown_marked w id)
      (mark_fold fuel D id ih (markShutdown w id).roster (markShutdown w id))

theorem fold_keeps_shut (fuel : Nat) (D : Description) (root i : InstId) :
    ∀ ids : List InstId, ∀ w : World, (w.st i).life = .shuttingDown →
      ((ids.foldl (fun w child =>
        if isChild D root child then markTree fuel D w child else w) w).st i).life =
        .shuttingDown := by
  intro ids
  induction ids with
  | nil => intro w h; simp [h]
  | cons child ids ih =>
    intro w h
    simp only [List.foldl_cons]
    cases hc : isChild D root child
    · have hstep : (if false = true then markTree fuel D w child else w) = w := by simp
      rw [hstep]
      exact ih w h
    · have hstep :
        (if true = true then markTree fuel D w child else w) = markTree fuel D w child := by simp
      rw [hstep]
      have hM := markTree_marked fuel D w child
      have h1 : ((markTree fuel D w child).st i).life = .shuttingDown := by
        cases hM.life i with
        | inl heq => exact heq ▸ h
        | inr hch => simp [h] at hch
      exact ih (markTree fuel D w child) h1

theorem markTree_shuts (D : Description) (w : World) (id : InstId) (n : Nat)
    (hn : w.roster.length = n + 1) (h : (w.st id).life = .alive) :
    ((markTree (n + 1) D w id).st id).life = .shuttingDown := by
  have hshut := mark_shuts w id h
  have hfold := fold_keeps_shut n D id id w.roster (markShutdown w id) hshut
  have heq : markTree (n + 1) D w id =
      (markShutdown w id).roster.foldl (fun w child =>
        if isChild D id child then markTree n D w child else w) (markShutdown w id) := rfl
  have hros : (markShutdown w id).roster = w.roster := (markShutdown_marked w id).roster
  simpa [heq, hros, hn] using hfold

/-- Arming the actor a shutdown just marked. It was alive, so the slot it
holds afterwards is a slot it already held. -/
theorem arm_after (w w1 : World) (id : InstId) (hM : Marked w w1)
    (halive : (w.st id).life = .alive) (hshut : (w1.st id).life = .shuttingDown) :
    Marked w (armTombstone w1 id) := by
  refine ⟨hM.N, hM.roster, hM.crashed, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = id
    · rw [hi]
      exact (by simp [armTombstone, setActor] :
        ((armTombstone w1 id).st id).prio = (w1.st id).prio).trans (hM.prio id)
    · exact (by simp [armTombstone, setActor, hi] :
        ((armTombstone w1 id).st i).prio = (w1.st i).prio).trans (hM.prio i)
  · intro i
    by_cases hi : i = id
    · exact Or.inr ⟨by simpa [hi] using halive, by simp [armTombstone, setActor, hi, hshut]⟩
    · cases hM.life i with
      | inl heql => exact Or.inl <| by simpa [armTombstone, setActor, hi] using heql
      | inr hch => exact Or.inr ⟨hch.1, by simpa [armTombstone, setActor, hi] using hch.2⟩
  · intro i
    by_cases hi : i = id
    · exact Or.inr ⟨by simp [armTombstone, setActor, hi],
        Or.inl <| by simp [armTombstone, setActor, hi, hshut]⟩
    · cases hM.pend i with
      | inl heql => exact Or.inl <| by simpa [armTombstone, setActor, hi] using heql
      | inr hset => exact Or.inr ⟨by simpa [armTombstone, setActor, hi] using hset.1,
          by simpa [armTombstone, setActor, hi] using hset.2⟩
  · intro i
    by_cases hi : i = id
    · cases hM.phase id with
      | inl heql => exact Or.inl <| by simpa [armTombstone, setActor, hi] using heql
      | inr hidle => exact Or.inr <| by simpa [armTombstone, setActor, hi] using hidle
    · cases hM.phase i with
      | inl heql => exact Or.inl <| by simpa [armTombstone, setActor, hi] using heql
      | inr hidle => exact Or.inr <| by simpa [armTombstone, setActor, hi] using hidle
  · intro i hh
    by_cases hi : i = id
    · simpa [hi] using alive_hold (w.st id) halive
    · have hlife : ((armTombstone w1 id).st i).life = (w1.st i).life := by
        simp [armTombstone, setActor, hi]
      have hpend : ((armTombstone w1 id).st i).pendingTombstone =
          (w1.st i).pendingTombstone := by
        simp [armTombstone, setActor, hi]
      exact hM.held i ((lifeHold_eq _ _ hlife hpend) ▸ hh)

theorem shutdown_marked (D : Description) (w : World) (id : InstId) :
    Marked w (shutdownActor D w id) := by
  cases hlive : (w.st id).life == .alive
  · rw [show shutdownActor D w id = w by simp [shutdownActor, markShutdown, hlive]]
    exact Marked.refl w
  · have hl : (w.st id).life = .alive := by simpa [beq_iff_eq] using hlive
    rw [show shutdownActor D w id = armTombstone (markShutdown w id) id by simp [shutdownActor, hlive]]
    exact arm_after w (markShutdown w id) id (markShutdown_marked w id) hl (mark_shuts w id hl)

theorem terminate_marked (D : Description) (w : World) (id : InstId) (a : Actor)
    (hmem : id ∈ w.roster) : Marked w (terminateStage D w id a) := by
  cases hlive : (w.st id).life == .alive
  · rw [show terminateStage D w id a = markTree w.roster.length D w id by simp [terminateStage, hlive]]
    exact markTree_marked _ D w id
  · have hl : (w.st id).life = .alive := by simpa [beq_iff_eq] using hlive
    cases hr : w.roster with
    | nil => simp [hr] at hmem
    | cons x xs =>
      have hn : w.roster.length = xs.length + 1 := by simp [hr]
      have hshut := markTree_shuts D w id xs.length hn hl
      have hM := markTree_marked w.roster.length D w id
      rw [show terminateStage D w id a =
          armTombstone (markTree w.roster.length D w id) id by simp [terminateStage, hlive]]
      exact arm_after w (markTree w.roster.length D w id) id hM hl (by simpa [hn] using hshut)

theorem abort_fold (D : Description) (parent : InstId) (base : List InstId) :
    ∀ ids : List InstId, ∀ w : World, w.roster = base → (∀ c, c ∈ ids → c ∈ base) →
      Marked w (ids.foldl (fun w child =>
        if isChild D parent child && (w.st child).life == .alive then
          let marked := markTree w.roster.length D w child
          armTombstone marked child
        else w) w) := by
  intro ids
  induction ids with
  | nil => intro w _ _; simp; exact Marked.refl w
  | cons child ids ih =>
    intro w hros hsub
    simp only [List.foldl_cons]
    cases hc : isChild D parent child
    · have hstep : (if (false && (w.st child).life == .alive) = true then
          armTombstone (markTree w.roster.length D w child) child else w) = w := by simp
      rw [hstep]
      exact ih w hros (fun c hm => hsub c (List.mem_cons_of_mem child hm))
    · cases hl : (w.st child).life == .alive
      · have hstep : (if (true && false) = true then
            armTombstone (markTree w.roster.length D w child) child else w) = w := by simp
        rw [hstep]
        exact ih w hros (fun c hm => hsub c (List.mem_cons_of_mem child hm))
      · have hstep : (if (true && true) = true then
            armTombstone (markTree w.roster.length D w child) child else w) =
          armTombstone (markTree w.roster.length D w child) child := by simp
        rw [hstep]
        have hlife : (w.st child).life = .alive := by simpa [beq_iff_eq] using hl
        have hmem : child ∈ w.roster := by
          simpa [hros] using hsub child (by exact List.mem_cons_self)
        have hlen : ∃ n, w.roster.length = n + 1 := by
          cases hr : w.roster with
          | nil => simp [hr] at hmem
          | cons _ xs => exact ⟨xs.length, by simp [hr]⟩
        obtain ⟨n, hn⟩ := hlen
        have hshut := markTree_shuts D w child n hn hlife
        have hstep := arm_after w (markTree w.roster.length D w child) child
          (markTree_marked w.roster.length D w child) hlife (by simpa [hn] using hshut)
        exact Marked.trans hstep (ih (armTombstone (markTree w.roster.length D w child) child)
          (by simpa [hros] using hstep.roster)
          (fun c hm => hsub c (List.mem_cons_of_mem child hm)))

theorem abort_marked (D : Description) (w : World) (parent : InstId) :
    Marked w (abortChildren D w parent) := by
  simpa [abortChildren] using abort_fold D parent w.roster w.roster w rfl (fun _ h => h)

theorem cellsCrash (D : Description) (w : World) (id : InstId) :
    (readCells D w id).crashed = w.crashed := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem deliver_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    a1.life = a.life ∧ a1.prio = a.prio ∧ a1.pendingTombstone = a.pendingTombstone ∧
      (∀ i, (w1.st i).life = (w.st i).life ∧ (w1.st i).prio = (w.st i).prio ∧
        (w1.st i).pendingTombstone = (w.st i).pendingTombstone) ∧
      w1.roster = w.roster ∧ w1.N = w.N ∧ w1.crashed = w.crashed ∧
      (∀ i, w1.st i = w.st i) := by
  simp only [deliver] at h
  have hst : ∀ i, (readCells I.desc w id).st i = w.st i := fun i => cellsSt I.desc w id i
  revert h
  split
  · intro h; cases h
  · intro h
    split at h
    · cases h
      exact ⟨rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
        congrArg Actor.pendingTombstone (hst i)⟩, cellsRoster I.desc w id, cellsN I.desc w id,
        cellsCrash I.desc w id, hst⟩
    · split at h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
            congrArg Actor.pendingTombstone (hst i)⟩, cellsRoster I.desc w id, cellsN I.desc w id,
            cellsCrash I.desc w id, hst⟩
      · split at h
        · cases h
        · cases h
          split <;> exact ⟨rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
            congrArg Actor.pendingTombstone (hst i)⟩, cellsRoster I.desc w id, cellsN I.desc w id,
            cellsCrash I.desc w id, hst⟩

theorem tmb_findSome_mem {α β : Type} (p : α → Option β) (l : List α) (b : β)
    (h : l.findSome? p = some b) : ∃ a, a ∈ l ∧ p a = some b := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp [List.findSome?] at h
    cases hp : p a with
    | none =>
      simp [hp] at h
      obtain ⟨a', ha', hp'⟩ := ih h
      exact ⟨a', List.mem_cons_of_mem a ha', hp'⟩
    | some b' =>
      simp [hp] at h
      cases h
      exact ⟨a, List.mem_cons_self, hp⟩

theorem findTr_mem (I : Impl) (template state label : String) (tr : Transition)
    (h : findTr I template state label = some tr) :
    tr ∈ I.transitions ∧ tr.template = template ∧ tr.fromState = state ∧ tr.label = label := by
  unfold findTr at h
  obtain ⟨tr', hmem, hp⟩ := tmb_findSome_mem _ I.transitions tr h
  cases hcond : (tr'.template == template && tr'.fromState == state && tr'.label == label)
  · simp [hcond] at hp
  · simp [hcond] at hp
    cases hp
    simp [Bool.and_eq_true, beq_iff_eq] at hcond
    exact ⟨hmem, hcond.1.1, hcond.1.2, hcond.2⟩

theorem findDeliver_mem (I : Impl) (template state : String) (m : Msg) (tr : Transition)
    (h : findDeliver I template state m = some tr) :
    tr ∈ I.transitions ∧ tr.template = template ∧ tr.fromState = state ∧
      (tr.label = m.label ∨ tr.label = m.baseLabel) := by
  unfold findDeliver at h
  cases h1 : findTr I template state m.label with
  | some tr' =>
    simp [h1] at h
    cases h
    have hm := findTr_mem I template state m.label tr h1
    exact ⟨hm.1, hm.2.1, hm.2.2.1, Or.inl hm.2.2.2⟩
  | none =>
    simp [h1] at h
    rcases h with ⟨_, hfind⟩
    have hm := findTr_mem I template state m.baseLabel tr hfind
    exact ⟨hm.1, hm.2.1, hm.2.2.1, Or.inr hm.2.2.2⟩

theorem deliver_declared (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    phaseDeclared I (tname id) a1.phase := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · cases h
      simp [phaseDeclared]
    · split at h
      · split at h
        · cases h
        · cases h
          simp [phaseDeclared]
      · rename_i tr hfind
        split at h
        · cases h
        · cases h
          have hm := findDeliver_mem I (tname id) a.typestate m tr hfind
          split
          · simp [phaseDeclared]
          · simp [phaseDeclared, tmb_programCont]
            rw [← hm.2.1]
            exact ContDeclared.program I tr hm.1 m.callFrom

theorem hold_finish (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (h : finishWait I w id = some w') (hpre : w.crashed = false) : Hold I w' := by
  obtain ⟨k, hph, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  apply hold_set I w hH id (proceed (w.st id) k) (proceed_keeps_life _ _) (proceed_keeps_prio _ _)
  · cases hk : k.rest <;> simp [proceed, hk]
  · intro hmem
    have hdec := hH.phase id hmem
    cases hph with
    | inl he =>
      exact proceed_declared I (tname id) (w.st id) k (by simpa [he, phaseDeclared] using hdec)
    | inr he =>
      exact proceed_declared I (tname id) (w.st id) k (by simpa [he, phaseDeclared] using hdec)
  · exact hpre

theorem hold_ingress (I : Impl) (w w' : World) (hH : Hold I w) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') (hpre : w.crashed = false) : Hold I w' := by
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
            apply hold_set I w hH dst
              { chargeSender (w.st dst) (tname dst) with
                box := (w.st dst).box ++
                  [{ label := label, sender := dst, callFrom := none, reliable := true,
                     mid := (w.st dst).nextMid }],
                nextMid := (w.st dst).nextMid + 1 }
            <;> try simp [chargeSender, bumpToken]
            · intro hmem
              simpa [chargeSender, bumpToken] using hH.phase dst hmem
            · exact hpre

theorem hold_recv_prio (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (h : receivePrio I w id = some w') (hpre : w.crashed = false) : Hold I w' := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
    · simp [hp, hready] at h
    · simp [hp, hready] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        rcases deliver_frame I w id { (w.st id) with prio := ms } m w1 a1 hdel with
          ⟨hlife, hprioA, hpendA, hworld, hros, hN, hcrash, hst⟩
        have hdec := deliver_declared I w id { (w.st id) with prio := ms } m w1 a1 hdel
        apply hold_drop I w (setActor w1 id a1) hH id
        · simp [setActor, hN]
        · simp [setActor, hros]
        · intro i
          by_cases hi : i = id
          · rw [hi]
            simpa [setActor] using hlife
          · have hst := (hworld i).1
            simpa [setActor, hi] using hst
        · intro i
          by_cases hi : i = id
          · rw [hi]
            simpa [setActor] using hpendA
          · have hst := (hworld i).2.2
            simpa [setActor, hi] using hst
        · exact ⟨m, by simp [setActor, hp, hprioA]⟩
        · intro i hi
          have hst := (hworld i).2.1
          simpa [setActor, hi] using hst
        · intro i hi
          by_cases heq : i = id
          · simpa [setActor, heq] using hdec
          · have hphaseEq : (w1.st i).phase = (w.st i).phase := congrArg Actor.phase (hst i)
            have hmem : i ∈ w.roster := by simpa [setActor, hros] using hi
            simpa [setActor, heq, hphaseEq] using hH.phase i hmem
        · simpa [setActor, hcrash] using hpre
        · exact hpre

theorem hold_same (I : Impl) (w w' : World) (hH : Hold I w)
    (hst : ∀ i, w'.st i = w.st i) (hros : w'.roster = w.roster) (hN : w'.N = w.N)
    (hcrash : w'.crashed = false) (hpre : w.crashed = false) : Hold I w' := by
  apply hold_actors I w w' hH hN hros
  · intro i; exact congrArg Actor.life (hst i)
  · intro i; exact congrArg Actor.prio (hst i)
  · intro i; exact congrArg Actor.pendingTombstone (hst i)
  · intro i hi
    exact (congrArg Actor.phase (hst i)).symm ▸ hH.phase i (by simpa [hros] using hi)
  · exact hcrash
  · exact hpre

theorem hold_credit (I : Impl) (w : World) (hH : Hold I w) (name : String) (sender : InstId)
    (hpre : w.crashed = false) : Hold I (creditSender w name sender) := by
  apply hold_actors I w (creditSender w name sender) hH rfl rfl
  · intro i; exact (credit_fields w name sender i).2.1
  · intro i; exact (credit_fields w name sender i).2.2.2.2
  · intro i; exact credit_pending w name sender i
  · intro i hi
    exact (credit_fields w name sender i).1 ▸ hH.phase i hi
  · exact hpre
  · exact hpre

theorem resume_declared (I : Impl) (template : String) (a : Actor) (isCall : Bool) (dst : InstId)
    (h : phaseDeclared I template a.phase) :
    phaseDeclared I template (resumeSender a isCall dst).phase := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases isCall with
    | true => simpa [resumeSender, hph, phaseDeclared] using (by simpa [hph, phaseDeclared] using h)
    | false =>
      simpa [resumeSender, hph] using
        proceed_declared I template a k (by simpa [hph, phaseDeclared] using h)
  | idle => simpa [resumeSender, hph] using h
  | run k => simpa [resumeSender, hph] using h
  | awaitReply _ _ => simpa [resumeSender, hph] using h
  | awaitEffect _ => simpa [resumeSender, hph] using h
  | awaitPeer _ => simpa [resumeSender, hph] using h
  | crashed => simpa [resumeSender, hph] using h

theorem hold_install (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (hdel : deliver I w id a m = some (w1, a1))
    (hl : a.life = (w.st id).life) (hp : a.prio = (w.st id).prio)
    (hpe : a.pendingTombstone = (w.st id).pendingTombstone)
    (hpre : w.crashed = false) : Hold I (setActor w1 id a1) := by
  rcases deliver_frame I w id a m w1 a1 hdel with
    ⟨hlife, hprioA, hpendA, _, hros, hN, hcrash, hst⟩
  have hdec := deliver_declared I w id a m w1 a1 hdel
  have hW := hold_same I w w1 hH hst hros hN (hcrash.symm ▸ hpre) hpre
  apply hold_set I w1 hW id a1
  · exact (hlife.trans hl).trans (congrArg Actor.life (hst id)).symm
  · exact (hprioA.trans hp).trans (congrArg Actor.prio (hst id)).symm
  · exact (hpendA.trans hpe).trans (congrArg Actor.pendingTombstone (hst id)).symm
  · intro _; exact hdec
  · exact hcrash.symm ▸ hpre

theorem hold_recv_bulk (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (h : receiveBulk I w id = some w') (hpre : w.crashed = false) : Hold I w' := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rcases deliver_frame I w id _ p.msg w1 a1 hdel with
            ⟨_, _, _, _, hros, _, hcrash, hst⟩
          have hH1 := hold_install I w hH id _ p.msg w1 a1 hdel rfl rfl rfl hpre
          have hpre1 : (setActor w1 id a1).crashed = false := by
            simpa [setActor, hcrash] using hpre
          have hH2 := hold_credit I (setActor w1 id a1) hH1 (tname id)
            (budgetHolder (setActor w1 id a1) p.msg.sender) hpre1
          let credited := creditSender (setActor w1 id a1) (tname id)
            (budgetHolder (setActor w1 id a1) p.msg.sender)
          apply hold_set I credited hH2 p.sender
            (resumeSender (credited.st p.sender) p.isCall id)
            (resumeSender_keep _ _ _).1 (resumeSender_prio _ _ _) (resumeSender_keep _ _ _).2
          · intro hmem
            have hcred := (credit_fields (setActor w1 id a1) (tname id)
              (budgetHolder (setActor w1 id a1) p.msg.sender) p.sender).1
            by_cases hs : p.sender = id
            · rw [hs] at hcred ⊢
              have hbase : ((setActor w1 id a1).st id).phase = a1.phase := by simp [setActor]
              have hph := deliver_declared I w id _ p.msg w1 a1 hdel
              exact resume_declared I (tname id) (credited.st id) p.isCall id
                ((hcred.trans hbase).symm ▸ hph)
            · have hbase : ((setActor w1 id a1).st p.sender).phase = (w.st p.sender).phase := by
                simp [setActor, hs]
                exact congrArg Actor.phase (hst p.sender)
              have hmemW : p.sender ∈ w.roster := by
                simpa [credited, creditSender, setActor, hros] using hmem
              exact resume_declared I (tname p.sender) (credited.st p.sender) p.isCall id
                ((hcred.trans hbase).symm ▸ hH.phase p.sender hmemW)
          · exact hpre1
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rcases deliver_frame I w id _ m w1 a1 hdel with ⟨_, _, _, _, _, _, hcrash, _⟩
          have hH1 := hold_install I w hH id _ m w1 a1 hdel rfl rfl rfl hpre
          have hpre1 : (setActor w1 id a1).crashed = false := by
            simpa [setActor, hcrash] using hpre
          simpa [creditLive] using hold_credit I (setActor w1 id a1) hH1 (tname id)
            (budgetHolder (setActor w1 id a1) m.sender) hpre1
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rcases deliver_frame I w id _ m w1 a1 hdel with
            ⟨_, _, _, _, hros, _, hcrash, hst⟩
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hH1 := hold_install I w hH id _ m w1 a1 hdel rfl rfl rfl hpre
          have hpre1 : (setActor w1 id a1).crashed = false := by
            simpa [setActor, hcrash] using hpre
          have hHad : Hold I (setActor w1 id admitted) := by
            have htwice := by
              apply hold_set I (setActor w1 id a1) hH1 id admitted
              · simp [admitted, setActor]
              · simp [admitted, setActor]
              · simp [admitted, setActor]
              · intro _
                simpa [admitted] using deliver_declared I w id _ m w1 a1 hdel
              · exact hpre1
            have hsame : setActor (setActor w1 id a1) id admitted = setActor w1 id admitted := by
              simp only [setActor]
              congr
              funext i
              by_cases hi : i = id <;> simp [hi]
            exact hsame ▸ htwice
          have hpre2 : (setActor w1 id admitted).crashed = false := by simpa [setActor] using hpre1
          have hH2 := hold_credit I (setActor w1 id admitted) hHad (tname id)
            (budgetHolder (setActor w1 id admitted) m.sender) hpre2
          let credited := creditSender (setActor w1 id admitted) (tname id)
            (budgetHolder (setActor w1 id admitted) m.sender)
          apply hold_set I credited hH2 p.sender
            (resumeSender (credited.st p.sender) p.isCall id)
            (resumeSender_keep _ _ _).1 (resumeSender_prio _ _ _) (resumeSender_keep _ _ _).2
          · intro hmem
            have hcred := (credit_fields (setActor w1 id admitted) (tname id)
              (budgetHolder (setActor w1 id admitted) m.sender) p.sender).1
            by_cases hs : p.sender = id
            · rw [hs] at hcred ⊢
              have hbase : ((setActor w1 id admitted).st id).phase = a1.phase := by
                simp [setActor, admitted]
              have hph := deliver_declared I w id _ m w1 a1 hdel
              exact resume_declared I (tname id) (credited.st id) p.isCall id
                ((hcred.trans hbase).symm ▸ hph)
            · have hbase : ((setActor w1 id admitted).st p.sender).phase =
                  (w.st p.sender).phase := by
                simp [setActor, hs]
                exact congrArg Actor.phase (hst p.sender)
              have hmemW : p.sender ∈ w.roster := by
                simpa [credited, creditSender, setActor, hros] using hmem
              exact resume_declared I (tname p.sender) (credited.st p.sender) p.isCall id
                ((hcred.trans hbase).symm ▸ hH.phase p.sender hmemW)
          · exact hpre2

theorem refund_call_frame (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).life = (w.st i).life ∧
      ((refundParkedCall w caller dst).st i).prio = (w.st i).prio ∧
      ((refundParkedCall w caller dst).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((refundParkedCall w caller dst).st i).phase = (w.st i).phase ∧
      (refundParkedCall w caller dst).roster = w.roster ∧
      (refundParkedCall w caller dst).N = w.N ∧
      (refundParkedCall w caller dst).crashed = w.crashed := by
  unfold refundParkedCall
  by_cases hempty : (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = true
  · simp [hempty]
  · simp only [hempty, ite_false]
    let drop := List.filter (fun p => p.sender == caller && p.isCall) (w.st dst).parked
    let keep := List.filter (fun p => !(p.sender == caller && p.isCall)) (w.st dst).parked
    let base := setActor w dst { (w.st dst) with parked := keep }
    have hbase : (base.st i).life = (w.st i).life ∧ (base.st i).prio = (w.st i).prio ∧
        (base.st i).pendingTombstone = (w.st i).pendingTombstone ∧
        (base.st i).phase = (w.st i).phase ∧ base.roster = w.roster ∧ base.N = w.N ∧
        base.crashed = w.crashed := by
      by_cases hi : i = dst
      · simp [base, setActor, hi]
      · simp [base, setActor, hi]
    have hfold : ∀ (start : World) (ps : List Parked),
        (start.st i).life = (base.st i).life →
        (start.st i).prio = (base.st i).prio →
        (start.st i).pendingTombstone = (base.st i).pendingTombstone →
        (start.st i).phase = (base.st i).phase →
        start.roster = base.roster → start.N = base.N → start.crashed = base.crashed →
        ((ps.foldl (fun w _ => creditSender w (tname dst) caller) start).st i).life = (base.st i).life ∧
        ((ps.foldl (fun w _ => creditSender w (tname dst) caller) start).st i).prio = (base.st i).prio ∧
        ((ps.foldl (fun w _ => creditSender w (tname dst) caller) start).st i).pendingTombstone =
          (base.st i).pendingTombstone ∧
        ((ps.foldl (fun w _ => creditSender w (tname dst) caller) start).st i).phase = (base.st i).phase ∧
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) start).roster = base.roster ∧
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) start).N = base.N ∧
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) start).crashed = base.crashed := by
      intro start ps
      induction ps generalizing start with
      | nil =>
        intro hl hp hpe hph hr hn hc
        exact ⟨hl, hp, hpe, hph, hr, hn, hc⟩
      | cons p ps ih =>
        intro hl hp hpe hph hr hn hc
        simp only [List.foldl_cons]
        exact ih (creditSender start (tname dst) caller)
          ((credit_fields start (tname dst) caller i).2.1.trans hl)
          ((credit_fields start (tname dst) caller i).2.2.2.2.trans hp)
          ((credit_pending start (tname dst) caller i).trans hpe)
          ((credit_fields start (tname dst) caller i).1.trans hph)
          hr hn hc
    have h := hfold base drop rfl rfl rfl rfl rfl rfl rfl
    exact ⟨h.1.trans hbase.1, h.2.1.trans hbase.2.1, h.2.2.1.trans hbase.2.2.1,
      h.2.2.2.1.trans hbase.2.2.2.1, h.2.2.2.2.1.trans hbase.2.2.2.2.1,
      h.2.2.2.2.2.1.trans hbase.2.2.2.2.2.1, h.2.2.2.2.2.2.trans hbase.2.2.2.2.2.2⟩

theorem hold_kill (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false)
    (hlive : (w.st id).life = .alive ∨ (w.st id).life = .shuttingDown) :
    Hold I (setActor w id (tmb_dead (w.st id))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    by_cases hi : i = id
    · have hne : (w.st id).life ≠ .absent := by
        cases hlive with
        | inl h => rw [h]; intro hbad; cases hbad
        | inr h => rw [h]; intro hbad; cases hbad
      simpa [setActor, hi] using hH.rostered id hne
    · exact hH.rostered i (by simpa [setActor, hi] using hl)
  · intro i hp
    by_cases hi : i = id
    · exact Or.inr (by simp [setActor, hi, tmb_dead])
    · have hold := hH.pend i (by simpa [setActor, hi, tmb_dead] using hp)
      simpa [setActor, hi, tmb_dead] using hold
  · intro _ i hd
    by_cases hi : i = id
    · simp [setActor, hi, tmb_dead]
    · simpa [setActor, hi, tmb_dead] using
        hH.deadPrio hpre i (by simpa [setActor, hi, tmb_dead] using hd)
  · intro i hid
    exact hH.role i (by simpa [setActor] using hid)
  · intro i hid
    by_cases hi : i = id
    · simp [setActor, hi, tmb_dead, phaseDeclared]
    · simpa [setActor, hi, tmb_dead] using hH.phase i (by simpa [setActor] using hid)
  · intro i
    by_cases hi : i = id
    · simpa [setActor, hi, tmb_dead] using lane_nil I (setActor w id (tmb_dead (w.st id))) id
        (by simp [setActor, tmb_dead])
    · have hold := hH.lane i
      exact ⟨by simpa [setActor, hi, tmb_dead] using hold.ordNodup,
        fun l hl => hold.ordIn l (by simpa [setActor, hi, tmb_dead] using hl),
        fun msg hm ht => hold.peer msg (by simpa [setActor, hi, tmb_dead] using hm) ht,
        by simpa [setActor, hi, tmb_dead] using hold.tombNodup⟩
  · intro parent c hc hchild hhold hnote
    by_cases hc_id : c = id
    · simp [setActor, hc_id, tmb_dead, lifeHold] at hhold
    · have hwas : lifeHold (w.st c) = true := by
        simpa [lifeHold, setActor, hc_id, tmb_dead] using hhold
      have hlegal := hH.legalLife parent c (by simpa [setActor] using hc) hchild hwas hnote
      cases c with
      | core _ => trivial
      | peer n k g => exact hlegal
  · intro parent name k hq
    by_cases hp : parent = id
    · simp [setActor, hp, tmb_dead, slotTombstoneQueued] at hq
    · have hq' : slotTombstoneQueued w parent name k = true := by
        simpa [slotTombstoneQueued, setActor, hp, tmb_dead] using hq
      exact hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    by_cases hc_id : c = id
    · simp [setActor, hc_id, tmb_dead, lifeHold] at hhold
    · have hwas : lifeHold (w.st c) = true := by
        simpa [lifeHold, setActor, hc_id, tmb_dead] using hhold
      have hfresh := hH.fresh parent c (by simpa [setActor] using hc) hchild hwas hnote
      by_cases hp : parent = id
      · cases c with
        | core _ => trivial
        | peer _ _ _ => simp [setActor, hp, tmb_dead, slotTombstoneQueued]
      · cases c with
        | core _ => trivial
        | peer n k g =>
          simpa [slotTombstoneQueued, setActor, hp, tmb_dead] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    have hold (c : InstId)
        (ho : occupant ((setActor w id (tmb_dead (w.st id))).st c) = true) :
        occupant (w.st c) = true := by
      by_cases hc : c = id
      · simp [setActor, hc, tmb_dead, occupant] at ho
      · simpa [occupant, setActor, hc, tmb_dead] using ho
    exact hH.occ c1 c2 (by simpa [setActor] using hc1) (by simpa [setActor] using hc2)
      (hold c1 ho1) (hold c2 ho2) hslot hsup

theorem hold_refund_msgs (I : Impl) (name : String) :
    ∀ (ms : List Msg) (w : World), Hold I w → w.crashed = false → Hold I (refundMsgs w name ms) := by
  intro ms
  induction ms with
  | nil => intro w hH _; simp [refundMsgs]; exact hH
  | cons m ms ih =>
    intro w hH hpre
    simp only [refundMsgs, List.foldl_cons]
    have h1 := hold_credit I w hH name (budgetHolder w m.sender) hpre
    exact ih (creditLive w name m.sender) h1 (by simpa [creditLive, creditSender, setActor] using hpre)

theorem hold_refund_parked (I : Impl) (name : String) :
    ∀ (ps : List Parked) (w : World), Hold I w → w.crashed = false →
      Hold I (refundParked w name ps) := by
  intro ps
  induction ps with
  | nil => intro w hH _; simp [refundParked]; exact hH
  | cons p ps ih =>
    intro w hH hpre
    simp only [refundParked, List.foldl_cons]
    have h1 := hold_credit I w hH name (budgetHolder w p.msg.sender) hpre
    exact ih (creditLive w name p.msg.sender) h1
      (by simpa [creditLive, creditSender, setActor] using hpre)

theorem hold_outbound (I : Impl) (w : World) (hH : Hold I w) (dead : InstId)
    (hpre : w.crashed = false) : Hold I (releaseOutbound w dead) := by
  apply hold_actors I w (releaseOutbound w dead) hH
    (releaseOutbound_prio w dead dead).2 (releaseOutbound_keep w dead dead).2.2
  · intro i; exact (releaseOutbound_keep w dead i).1
  · intro i; exact (releaseOutbound_prio w dead i).1
  · intro i; exact (releaseOutbound_keep w dead i).2.1
  · intro i hi
    exact (release_extra w dead i).1 ▸ hH.phase i (by
      simpa [(releaseOutbound_keep w dead i).2.2] using hi)
  · exact (release_extra w dead dead).2.symm ▸ hpre
  · exact hpre

theorem hold_resume (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (p : Parked)
    (hpre : w.crashed = false) : Hold I (tmb_resumeOne id w p) := by
  unfold tmb_resumeOne
  split
  · exact hH
  · apply hold_set I w hH p.sender (resumeSender (w.st p.sender) false id)
      (resumeSender_keep _ _ _).1 (resumeSender_prio _ _ _) (resumeSender_keep _ _ _).2
    · intro hmem
      exact resume_declared I (tname p.sender) (w.st p.sender) false id (hH.phase p.sender hmem)
    · exact hpre

theorem hold_release_parked (I : Impl) (id : InstId) :
    ∀ (ps : List Parked) (w : World), Hold I w → w.crashed = false →
      Hold I (releaseParked w id ps) := by
  intro ps
  induction ps with
  | nil => intro w hH _; simp [releaseParked]; exact hH
  | cons p ps ih =>
    intro w hH hpre
    simp only [releaseParked, List.foldl_cons]
    exact ih (tmb_resumeOne id w p) (hold_resume I w hH id p hpre)
      (by simp [tmb_resumeOne]; split <;> simp [setActor, hpre])

theorem refundMsgs_crash (w : World) (name : String) (ms : List Msg) :
    (refundMsgs w name ms).crashed = w.crashed := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact (ih (creditLive w name m.sender)).trans rfl

theorem refundParked_crash (w : World) (name : String) (ps : List Parked) :
    (refundParked w name ps).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact (ih (creditLive w name p.msg.sender)).trans rfl

theorem refundParked_life (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact (ih (creditLive w name p.msg.sender)).trans
      (credit_fields w name (budgetHolder w p.msg.sender) i).2.1

theorem hold_release (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (hpre : w.crashed = false)
    (hlive : (w.st id).life = .alive ∨ (w.st id).life = .shuttingDown) :
    Hold I (releaseWorld I.desc w id a) := by
  unfold releaseWorld
  have hW1 := hold_same I w (readCells I.desc w id) hH (fun i => cellsSt I.desc w id i)
    (cellsRoster I.desc w id) (cellsN I.desc w id) ((cellsCrash I.desc w id).symm ▸ hpre) hpre
  have hpre1 : (readCells I.desc w id).crashed = false := (cellsCrash I.desc w id).symm ▸ hpre
  have hW2 := hold_refund_msgs I (tname id) a.box (readCells I.desc w id) hW1 hpre1
  have hpre2 : (refundMsgs (readCells I.desc w id) (tname id) a.box).crashed = false :=
    (refundMsgs_crash (readCells I.desc w id) (tname id) a.box).symm ▸ hpre1
  have hW3 := hold_refund_parked I (tname id) a.parked
    (refundMsgs (readCells I.desc w id) (tname id) a.box) hW2 hpre2
  let w3 := refundParked (refundMsgs (readCells I.desc w id) (tname id) a.box) (tname id) a.parked
  have hpre3 : w3.crashed = false :=
    (refundParked_crash (refundMsgs (readCells I.desc w id) (tname id) a.box) (tname id) a.parked).symm ▸
      hpre2
  have hW4 := hold_outbound I w3 hW3 id hpre3
  have hpre4 : (releaseOutbound w3 id).crashed = false :=
    (release_extra w3 id id).2.symm ▸ hpre3
  have hlife4 : ((releaseOutbound w3 id).st id).life = (w.st id).life := by
    have hcells := congrArg Actor.life (cellsSt I.desc w id id)
    have hmsgs := (refundMsgs_fields (readCells I.desc w id) (tname id) a.box id).2.1
    have hpark := refundParked_life (refundMsgs (readCells I.desc w id) (tname id) a.box)
      (tname id) a.parked id
    have hout := (releaseOutbound_keep w3 id id).1
    exact hout.trans (hpark.trans (hmsgs.trans hcells))
  have hkill := hold_kill I (releaseOutbound w3 id) hW4 id hpre4 (by
    cases hlive with
    | inl h => exact Or.inl (hlife4.symm ▸ h)
    | inr h => exact Or.inr (hlife4.symm ▸ h))
  exact hold_release_parked I id a.parked
    (setActor (releaseOutbound w3 id) id (tmb_dead ((releaseOutbound w3 id).st id))) hkill
    (by simpa [setActor] using hpre4)

theorem tmb_labels_snoc (ms : List Msg) (msg : Msg) (ht : msg.tombstone = true) :
    tmb_laneLabels (ms ++ [msg]) = tmb_laneLabels ms := by
  simp only [tmb_laneLabels, List.filter_append, List.map_append]
  have : List.filter (fun m => !m.tombstone) [msg] = [] := by simp [ht]
  simp [this]

theorem tomb_snoc (ms : List Msg) (msg : Msg) (name : String) (k g : Nat)
    (ht : msg.tombstone = true) (hs : msg.sender = InstId.peer name k g) :
    tombSlots (ms ++ [msg]) = tombSlots ms ++ [(name, k)] := by
  simp only [tombSlots, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, ht, hs]
  simp

theorem tmb_nodup_snoc {α : Type} (l : List α) (a : α) (hnd : l.Nodup) (hf : a ∉ l) :
    (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    have hpair := List.nodup_cons.mp hnd
    have hnot : a ≠ b := by
      intro heq
      exact hf (heq ▸ List.mem_cons_self)
    have htail : a ∉ bs := by
      intro hm
      exact hf (List.mem_cons_of_mem b hm)
    have hb : b ≠ a := fun h => hnot h.symm
    have hnotb : b ∉ bs ++ [a] := by
      intro hm
      simp [List.mem_append] at hm
      cases hm with
      | inl h => exact hpair.1 h
      | inr h => exact hb h
    exact List.nodup_cons.mpr ⟨hnotb, ih hpair.2 htail⟩

/-- Appending one peer tombstone for a slot that is legal, not already queued,
and held by nobody. -/
theorem hold_snoc (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (msg : Msg) (name : String) (k g : Nat) (hpre : w.crashed = false)
    (halive : (w.st parent).life = .alive)
    (ht : msg.tombstone = true) (hs : msg.sender = .peer name k g)
    (hlegal : (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : slotTombstoneQueued w parent name k = false)
    (hnone : ∀ c, c ∈ w.roster → lifeHold (w.st c) = true → notifies I.desc c = true →
      match c with
      | .peer n key _ => ¬(n = name ∧ key = k)
      | .core _ => True) : Hold I (tmb_snoc w parent msg) := by
  let w' := tmb_snoc w parent msg
  have hlife := tmb_snoc_life w parent msg
  have hpend := tmb_snoc_pend w parent msg
  have hphase := tmb_snoc_phase w parent msg
  have hros := tmb_snoc_roster w parent msg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    exact hH.rostered i (by simpa [w', hlife, hros] using hl)
  · intro i hp
    simpa [hlife i] using hH.pend i (hpend i ▸ hp)
  · intro _ i hd
    by_cases hi : i = parent
    · have : (w.st parent).life = .dead := by simpa [w', hi, hlife] using hd
      simp [halive] at this
    · exact tmb_snoc_prio_other w parent msg i hi ▸ hH.deadPrio hpre i (by simpa [w', hi, hlife] using hd)
  · intro i hid
    exact hH.role i (by simpa [w', hros] using hid)
  · intro i hid
    exact hphase i ▸ hH.phase i (by simpa [w', hros] using hid)
  · intro i
    by_cases hi : i = parent
    · have hold := hH.lane parent
      have hlabels := tmb_labels_snoc (w.st parent).prio msg ht
      have htombs := tomb_snoc (w.st parent).prio msg name k g ht hs
      have hprio := tmb_snoc_prio_self w parent msg
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [w', hi, hprio, hlabels] using hold.ordNodup
      · intro l hl
        have hl' : l ∈ tmb_laneLabels (w.st parent).prio := by
          simpa [w', hi, hprio, hlabels] using hl
        simpa [hi] using hold.ordIn l hl'
      · intro m hm htomb
        have hm' : m ∈ (w.st parent).prio ++ [msg] := by simpa [w', hi, hprio] using hm
        simp [List.mem_append] at hm'
        cases hm' with
        | inl hmem => exact hold.peer m hmem htomb
        | inr hmem =>
          cases hmem
          exact ⟨name, k, g, hs⟩
      · have hnd := tmb_nodup_snoc _ _ hold.tombNodup (by
          intro hmem
          have hq : slotTombstoneQueued w parent name k = true :=
            (tmb_queued_iff w parent name k).mpr hmem
          simp [hq] at hfree)
        simpa [w', hi, hprio, ← htombs] using hnd
    · have hold := hH.lane i
      have hprio := tmb_snoc_prio_other w parent msg i hi
      exact ⟨by simpa [w', hprio] using hold.ordNodup,
        fun l hl => hold.ordIn l (by simpa [w', hprio] using hl),
        fun m hm htomb => hold.peer m (by simpa [w', hprio] using hm) htomb,
        by simpa [w', hprio] using hold.tombNodup⟩
  · intro p c hc hchild hhold hnote
    have hwas : lifeHold (w.st c) = true := by
      simpa [lifeHold, hlife c, hpend c] using hhold
    have hlegal' := hH.legalLife p c (by simpa [w', hros] using hc) hchild hwas hnote
    cases c with
    | core _ => trivial
    | peer _ _ _ => simpa [w', tmb_snoc_N] using hlegal'
  · intro p n key hq
    by_cases hp : p = parent
    · rw [hp, tmb_queued_self, tmb_any_snoc] at hq
      cases hbit : (w.st parent).prio.any (tmb_hit n key)
      · rw [hbit, Bool.false_or] at hq
        simp only [tmb_hit, ht, hs, Bool.and_eq_true, beq_iff_eq] at hq
        rcases hq with ⟨hn, hk⟩
        simpa [hp, hn, hk, tmb_snoc_N] using hlegal
      · have hqbit : slotTombstoneQueued w parent n key = true := by
          unfold slotTombstoneQueued
          exact hbit
        simpa [hp, tmb_snoc_N] using hH.legalTomb parent n key hqbit
    · rw [tmb_queued_other w parent msg p n key hp] at hq
      exact hH.legalTomb p n key hq
  · intro p c hc hchild hhold hnote
    have hwas : lifeHold (w.st c) = true := by
      simpa [lifeHold, hlife c, hpend c] using hhold
    by_cases hp : p = parent
    · cases c with
      | core _ => trivial
      | peer n key gen =>
        dsimp
        have hfresh := hH.fresh parent (InstId.peer n key gen)
          (by simpa [w', hros] using hc) (by simpa [hp] using hchild) hwas hnote
        unfold slotTombstoneQueued at hfresh
        have hfresh' : (w.st parent).prio.any (tmb_hit n key) = false :=
          (tmb_any_hit (w.st parent).prio n key).symm ▸ hfresh
        by_cases hslot : n = name ∧ key = k
        · exact absurd hslot (hnone (InstId.peer n key gen)
            (by simpa [w', hros] using hc) hwas hnote)
        · rw [hp, tmb_queued_self, tmb_any_snoc, hfresh', Bool.false_or]
          simp only [tmb_hit, ht, hs]
          cases hdec : (name == n) <;> cases hkey : (k == key) <;> simp [hdec, hkey]
          have hn : name = n := by simpa [beq_iff_eq] using hdec
          have hk : k = key := by simpa [beq_iff_eq] using hkey
          exact absurd (And.intro hn hk)
            (fun h : name = n ∧ k = key => hslot (And.intro h.1.symm h.2.symm))
    · have hfresh := hH.fresh p c (by simpa [w', hros] using hc) hchild hwas hnote
      cases c with
      | core _ => trivial
      | peer n key _ =>
        dsimp
        rw [tmb_queued_other w parent msg p n key hp]
        simpa [slotTombstoneQueued] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hsup
    exact hH.occ c1 c2 (by simpa [w', hros] using hc1) (by simpa [w', hros] using hc2)
      (by simpa [occupant, w', hlife] using ho1) (by simpa [occupant, w', hlife] using ho2) hslot hsup

theorem hold_offer (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (msg : Msg) (name : String) (k g : Nat) (hpre : w.crashed = false)
    (halive : (w.st parent).life = .alive) (ht : msg.tombstone = true)
    (hs : msg.sender = .peer name k g)
    (hlegal : (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : slotTombstoneQueued w parent name k = false)
    (hnone : ∀ c, c ∈ w.roster → lifeHold (w.st c) = true → notifies I.desc c = true →
      match c with
      | .peer n key _ => ¬(n = name ∧ key = k)
      | .core _ => True) : Hold I (offerPrio I.desc w parent msg) := by
  by_cases hfull : prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent
  · have hdec : decide (prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent) = true := by
      simp [hfull]
    simp only [offerPrio, hdec]
    exact hold_crash I w hH
  · have hdec : decide (prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent) = false :=
      decide_eq_false hfull
    simp only [offerPrio, hdec, tmb_snoc]
    exact hold_snoc I w hH parent msg name k g hpre halive ht hs hlegal hfree hnone

theorem hold_enqueue (I : Impl) (w : World) (hH : Hold I w) (child : InstId)
    (name : String) (k g : Nat) (hpre : w.crashed = false)
    (hchild : child = .peer name k g)
    (hlegal : ∀ parent, liveSupervisor I.desc w child = some parent →
      (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : ∀ parent, liveSupervisor I.desc w child = some parent →
      slotTombstoneQueued w parent name k = false)
    (hnone : ∀ parent, liveSupervisor I.desc w child = some parent →
      ∀ c, c ∈ w.roster → lifeHold (w.st c) = true → notifies I.desc c = true →
        match c with
        | .peer n key _ => ¬(n = name ∧ key = k)
        | .core _ => True) : Hold I (enqueueTombstone I.desc w child) := by
  unfold enqueueTombstone
  split
  · exact hH
  · rename_i parent hsup
    let msg := tombstoneMsg I.desc (w.st parent) child
    cases hcond : ((w.st parent).life != .alive || (tombstoneMsg I.desc (w.st parent) child).label == "")
    · have hpair :
          ((w.st parent).life != .alive) = false ∧ (msg.label == "") = false := by
        simpa [msg, Bool.or_eq_false_iff] using hcond
      have halive : (w.st parent).life = .alive := by
        have hne : ((w.st parent).life == .alive) = true := by
          simpa [bne] using hpair.1
        simpa [beq_iff_eq] using hne
      have ht : msg.tombstone = true := by simp [msg, tombstoneMsg]
      have hs : msg.sender = .peer name k g := by simp [msg, tombstoneMsg, hchild]
      simp only [hcond]
      exact hold_offer I w hH parent msg name k g hpre halive ht hs
        (hlegal parent hsup) (hfree parent hsup) (hnone parent hsup)
    · simp only [hcond]
      exact hold_crash I w hH

theorem resume_crash (id : InstId) (w : World) (p : Parked) :
    (tmb_resumeOne id w p).crashed = w.crashed := by
  unfold tmb_resumeOne
  split <;> simp [setActor]

theorem releaseParked_crash (id : InstId) :
    ∀ (ps : List Parked) (w : World), (releaseParked w id ps).crashed = w.crashed := by
  intro ps
  induction ps with
  | nil => intro w; simp [releaseParked]
  | cons p ps ih =>
    intro w
    simp only [releaseParked, List.foldl_cons]
    exact (ih (tmb_resumeOne id w p)).trans (resume_crash id w p)

theorem releaseParked_roster (id : InstId) :
    ∀ (ps : List Parked) (w : World), (releaseParked w id ps).roster = w.roster := by
  intro ps
  induction ps with
  | nil => intro w; simp [releaseParked]
  | cons p ps ih =>
    intro w
    simp only [releaseParked, List.foldl_cons]
    exact (ih (tmb_resumeOne id w p)).trans (by simp [tmb_resumeOne]; split <;> simp [setActor])

theorem release_crash (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).crashed = w.crashed := by
  have h1 : (readCells D w id).crashed = w.crashed := cellsCrash D w id
  have h2 := (refundMsgs_crash (readCells D w id) (tname id) a.box).trans h1
  let w2 := refundMsgs (readCells D w id) (tname id) a.box
  have h3 := (refundParked_crash w2 (tname id) a.parked).trans h2
  let w3 := refundParked w2 (tname id) a.parked
  have h4 := (release_extra w3 id id).2.trans h3
  let w4 := releaseOutbound w3 id
  have h5 : (setActor w4 id (tmb_dead (w4.st id))).crashed = w.crashed := by
    simpa [setActor] using h4
  simpa [releaseWorld, w2, w3, w4, tmb_dead] using
    (releaseParked_crash id a.parked (setActor w4 id (tmb_dead (w4.st id)))).trans h5

theorem release_roster (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).roster = w.roster := by
  have h1 : (readCells D w id).roster = w.roster := cellsRoster D w id
  have h2 := (refundMsgs_roster (readCells D w id) (tname id) a.box).trans h1
  let w2 := refundMsgs (readCells D w id) (tname id) a.box
  have h3 := (refundParked_roster w2 (tname id) a.parked).trans h2
  let w3 := refundParked w2 (tname id) a.parked
  have h4 := (releaseOutbound_keep w3 id id).2.2.trans h3
  let w4 := releaseOutbound w3 id
  have h5 : (setActor w4 id (tmb_dead (w4.st id))).roster = w.roster := by
    simpa [setActor] using h4
  simpa [releaseWorld, w2, w3, w4, tmb_dead] using
    (releaseParked_roster id a.parked (setActor w4 id (tmb_dead (w4.st id)))).trans h5

theorem silent_label (D : Description) (id : InstId) (h : notifies D id = false) :
    tombstoneLabel D id = "" := by
  unfold notifies at h
  unfold tombstoneLabel
  cases hlook : templateOf D (tname id) with
  | none => simp [hlook]
  | some t =>
    simp only [hlook] at h ⊢
    have hempty : (t.tombstone == "") = true := by
      have hn : (t.tombstone != "") = false := h
      simpa [bne] using hn
    simp [hempty]

theorem hold_seal (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false) (hG : GraphOk I.desc)
    (hshut : (w.st id).life = .shuttingDown) : Hold I (sealActor I.desc w id (w.st id)) := by
  have hrel := hold_release I w hH id (w.st id) hpre (Or.inr hshut)
  unfold sealActor
  cases hpend : (w.st id).pendingTombstone
  · simp only [hpend]
    exact hrel
  · simp only [hpend]
    let sealed := releaseWorld I.desc w id (w.st id)
    have hpreS : sealed.crashed = false := (release_crash I.desc w id (w.st id)).symm ▸ hpre
    have hmem : id ∈ w.roster := hH.rostered id (by simp [hshut])
    cases hsup : liveSupervisor I.desc sealed id with
    | none =>
      simp [enqueueTombstone, sealed] at hsup ⊢
      simp [hsup]
      exact hrel
    | some parent =>
      by_cases hnote : notifies I.desc id = true
      · have hros := release_roster I.desc w id (w.st id)
        have hmemS : id ∈ sealed.roster := by simpa [sealed, hros] using hmem
        have hrole := hrel.role id hmemS
        have hpeer := tmb_live_peer I.desc hG sealed id parent hrole hsup
        obtain ⟨n, k, g, hid, hchild⟩ := hpeer
        have hne : parent ≠ id := (tmb_child_ne I.desc parent id hchild).symm
        have hprio := releaseWorld_prio I.desc w id (w.st id) parent hne
        have hwas : lifeHold (w.st id) = true := by simp [lifeHold, hshut, hpend]
        apply hold_enqueue I sealed hrel id n k g hpreS hid
        · intro p hp
          simp only [hsup] at hp
          injection hp with hp'
          have hleg := hH.legalLife parent id hmem hchild hwas hnote
          simpa [sealed, hid, hp', ← hprio.2] using hleg
        · intro p hp
          simp only [hsup] at hp
          injection hp with hp'
          have hfresh := hH.fresh parent id hmem hchild hwas hnote
          dsimp only [sealed] at hfresh ⊢
          simp only [slotTombstoneQueued] at hfresh ⊢
          rw [← hp', hprio.1]
          simp only [hid] at hfresh
          exact hfresh
        · intro p hp c hc hhold hnote'
          simp only [hsup] at hp
          injection hp with hp'
          cases c with
          | core _ => trivial
          | peer cn ck cg =>
            intro hslot
            by_cases hc_id : InstId.peer cn ck cg = id
            · have hdead := releaseWorld_self_dead I.desc w id (w.st id)
              rw [hc_id] at hhold
              unfold lifeHold at hhold
              simp only [sealed] at hhold
              rw [hdead] at hhold
              simp at hhold
            · have hkeep := releaseWorld_keep I.desc w id (w.st id) (InstId.peer cn ck cg) hc_id
              have hhold0 : lifeHold (w.st (InstId.peer cn ck cg)) = true := by
                dsimp only [sealed] at hhold
                simpa [lifeHold, hkeep.1, hkeep.2.1] using hhold
              have hsame : sameSlot id (InstId.peer cn ck cg) = true := by
                simp [hid, sameSlot, hslot]
              have hsupSome : supervisorOf I.desc id ≠ none := by
                unfold isChild at hchild
                cases hso : supervisorOf I.desc id with
                | none => simp [hso] at hchild
                | some _ => simp [hso]
              have hidc := hH.occ id (InstId.peer cn ck cg) hmem
                (by simpa [sealed, hros] using hc)
                (by simp [occupant, hshut])
                (by simp [occupant, lifeHold] at hhold0; cases hhold0 with
                  | inl h => simp [occupant, h]
                  | inr h => simp [occupant, h.1])
                hsame hsupSome
              exact hc_id hidc.symm
      · have hfalse : notifies I.desc id = false := by
          cases hn : notifies I.desc id
          · rfl
          · exact absurd hn hnote
        have hlab := silent_label I.desc id hfalse
        have hbad : ((sealed.st parent).life != .alive ||
            (tombstoneMsg I.desc (sealed.st parent) id).label == "") = true := by
          simp [tombstoneMsg, hlab]
        have hcrashW : enqueueTombstone I.desc sealed id = crashWorld sealed := by
          unfold enqueueTombstone
          simp [hsup, hbad]
        simpa [sealed, hcrashW] using hold_crash I sealed hrel

theorem proceed_keep (a : Actor) (k : Cont) :
    (proceed a k).life = a.life ∧ (proceed a k).prio = a.prio ∧
      (proceed a k).pendingTombstone = a.pendingTombstone := by
  cases h : k.rest <;> simp [proceed, h]

theorem hold_proceed (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (k : Cont)
    (hpre : w.crashed = false)
    (hph : id ∈ w.roster → phaseDeclared I (tname id) (proceed (w.st id) k).phase) :
    Hold I (setActor w id (proceed (w.st id) k)) := by
  have h := proceed_keep (w.st id) k
  exact hold_set I w hH id (proceed (w.st id) k) h.1 h.2.1 h.2.2 hph hpre

theorem hold_note (I : Impl) (w : World) (hH : Hold I w) (sender : InstId) (dst : String)
    (hpre : w.crashed = false) : Hold I (noteStale w sender dst) :=
  hold_same I w (noteStale w sender dst) hH (fun i => noteStale_st w sender dst i) rfl rfl
    (by simp [noteStale, hpre]) hpre

theorem hold_abort (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (hpre : w.crashed = false) (hlive : a.life = .alive)
    (hk : ∃ tail, k.rest = .abort :: tail) : Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := by simpa [beq_iff_eq] using hlive
  rcases hk with ⟨tail, hk⟩
  simpa [execRun, hgo, hk] using
    hold_marked I w (abortChildren I.desc w id) hH (abort_marked I.desc w id) hpre

theorem hold_terminate (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (k : Cont) (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : ∃ tail, k.rest = .terminate :: tail) : Hold I (execRun I w id a k) := by
  have hmem : id ∈ w.roster := hH.rostered id (by
    intro hbad
    rw [← ha] at hbad
    simp [hlive] at hbad)
  rcases execRun_terminate I w id a k hlive hk with hcrash | hrest
  · simpa [hcrash] using hold_crash I w hH
  rcases hrest with hshut | hrest
  · obtain ⟨_, _, _, _, _, _, heq⟩ := hshut
    simpa [heq] using hold_marked I w (shutdownActor I.desc w id) hH
      (shutdown_marked I.desc w id) hpre
  rcases hrest with htree | hcascade
  · obtain ⟨_, _, _, _, heq⟩ := htree
    simpa [heq] using hold_marked I w (terminateStage I.desc w id a) hH
      (terminate_marked I.desc w id a hmem) hpre
  · obtain ⟨_, _, _, _, _, _, heq⟩ := hcascade
    simpa [heq] using hold_marked I w (terminateStage I.desc w id a) hH
      (terminate_marked I.desc w id a hmem) hpre

/-- `exec` of an actor that is already shutting down seals it, and the seal
preserves the lane invariant. -/
theorem hold_exec_seal (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false) (hG : GraphOk I.desc)
    (hshut : (w.st id).life = .shuttingDown) (w' : World)
    (h : execHead I w id = some w') : Hold I w' := by
  simp [execHead, hshut] at h
  exact h ▸ hold_seal I w hH id hpre hG hshut

theorem finish_keep (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).life = a.life ∧ (finishCall a k r).prio = a.prio ∧
      (finishCall a k r).pendingTombstone = a.pendingTombstone := by
  have h := proceed_keep a (selectCall k r)
  simp [finishCall]
  exact h

theorem issue_keep (a : Actor) :
    (issueCall a).life = a.life ∧ (issueCall a).prio = a.prio ∧
      (issueCall a).pendingTombstone = a.pendingTombstone := by
  simp [issueCall]

theorem charge_keep (a : Actor) (dst : String) :
    (chargeSender a dst).life = a.life ∧ (chargeSender a dst).prio = a.prio ∧
      (chargeSender a dst).pendingTombstone = a.pendingTombstone := by
  simp [chargeSender, bumpToken]

theorem mail_crash (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).crashed = w.crashed := by
  unfold enqueueOrPark
  repeat (first | simp [setActor] | split)

theorem mail_roster (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).roster = w.roster := by
  unfold enqueueOrPark
  repeat (first | simp [setActor] | split)

theorem mail_N (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).N = w.N := by
  unfold enqueueOrPark
  repeat (first | simp [setActor] | split)

theorem mail_life (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).life = (w.st i).life := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · have hfin := (finish_keep (w.st sender) k .notAdmitted).1
    have hpro := (proceed_keep (w.st sender) k).1
    by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
      simp [enqueueOrPark, hdead, hcall, hi, setActor, hfin, hpro] <;>
      first | (subst hi; simp) | exact (proceed_keep _ _).1 |
        exact (finish_keep _ _ _).1.trans (issue_keep _).1 | rfl
  · have hpro := (proceed_keep (chargeSender (issueCall (w.st sender)) (tname dst)) k).1
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hcall, hi, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 |
            exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
                exact (proceed_keep _ _).1.trans ((issue_keep _).1.trans (charge_keep _ _).1) |
                exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).1 |
            exact (finish_keep _ _ _).1.trans (issue_keep _).1 | rfl
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hcall, hi, hd, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 |
            exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
                exact (proceed_keep _ _).1.trans ((issue_keep _).1.trans (charge_keep _ _).1) |
                exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).1 |
            exact (finish_keep _ _ _).1.trans (issue_keep _).1 | rfl
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hi, setActor, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 |
            exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).1.trans (charge_keep _ _).1 |
                exact (proceed_keep _ _).1.trans ((issue_keep _).1.trans (charge_keep _ _).1) |
                exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).1 | rfl
      · by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hi, hd, setActor, issue_keep, charge_keep] <;>
          (by_cases hsd : dst = sender <;> by_cases hc : isCall = true <;> simp [hsd, hc] <;>
            first | exact (issue_keep _).1.trans (charge_keep _ _).1 | exact (charge_keep _ _).1 | rfl)

theorem mail_prio (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).prio = (w.st i).prio := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · have hfin := (finish_keep (w.st sender) k .notAdmitted).2.1
    have hpro := (proceed_keep (w.st sender) k).2.1
    by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
      simp [enqueueOrPark, hdead, hcall, hi, setActor, hfin, hpro] <;>
      first | (subst hi; simp) | exact (proceed_keep _ _).2.1 |
        exact (finish_keep _ _ _).2.1.trans (issue_keep _).2.1 | rfl
  · have hpro := (proceed_keep (chargeSender (issueCall (w.st sender)) (tname dst)) k).2.1
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hcall, hi, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 |
            exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
                exact (proceed_keep _ _).2.1.trans ((issue_keep _).2.1.trans (charge_keep _ _).2.1) |
                exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.1 |
            exact (finish_keep _ _ _).2.1.trans (issue_keep _).2.1 | rfl
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hcall, hi, hd, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 |
            exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
                exact (proceed_keep _ _).2.1.trans ((issue_keep _).2.1.trans (charge_keep _ _).2.1) |
                exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.1 |
            exact (finish_keep _ _ _).2.1.trans (issue_keep _).2.1 | rfl
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hi, setActor, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 |
            exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.1.trans (charge_keep _ _).2.1 |
                exact (proceed_keep _ _).2.1.trans ((issue_keep _).2.1.trans (charge_keep _ _).2.1) |
                exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.1 | rfl
      · by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hi, hd, setActor, issue_keep, charge_keep] <;>
          (by_cases hsd : dst = sender <;> by_cases hc : isCall = true <;> simp [hsd, hc] <;>
            first | exact (issue_keep _).2.1.trans (charge_keep _ _).2.1 | exact (charge_keep _ _).2.1 | rfl)

theorem mail_pend (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).pendingTombstone = (w.st i).pendingTombstone := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · have hfin := (finish_keep (w.st sender) k .notAdmitted).2.2
    have hpro := (proceed_keep (w.st sender) k).2.2
    by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
      simp [enqueueOrPark, hdead, hcall, hi, setActor, hfin, hpro] <;>
      first | (subst hi; simp) | exact (proceed_keep _ _).2.2 |
        exact (finish_keep _ _ _).2.2.trans (issue_keep _).2.2 | rfl
  · have hpro := (proceed_keep (chargeSender (issueCall (w.st sender)) (tname dst)) k).2.2
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hcall, hi, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 |
            exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
                exact (proceed_keep _ _).2.2.trans ((issue_keep _).2.2.trans (charge_keep _ _).2.2) |
                exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.2 |
            exact (finish_keep _ _ _).2.2.trans (issue_keep _).2.2 | rfl
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hcall, hi, hd, setActor, hpro, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 |
            exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
                exact (proceed_keep _ _).2.2.trans ((issue_keep _).2.2.trans (charge_keep _ _).2.2) |
                exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.2 |
            exact (finish_keep _ _ _).2.2.trans (issue_keep _).2.2 | rfl
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hi, setActor, issue_keep, charge_keep] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_keep, charge_keep]) |
            exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 |
            exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2] <;>
              first | exact (proceed_keep _ _).2.2.trans (charge_keep _ _).2.2 |
                exact (proceed_keep _ _).2.2.trans ((issue_keep _).2.2.trans (charge_keep _ _).2.2) |
                exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_keep _ _).2.2 | rfl
      · by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hi, hd, setActor, issue_keep, charge_keep] <;>
          (by_cases hsd : dst = sender <;> by_cases hc : isCall = true <;> simp [hsd, hc] <;>
            first | exact (issue_keep _).2.2.trans (charge_keep _ _).2.2 | exact (charge_keep _ _).2.2 | rfl)

theorem hold_mail (I : Impl) (w : World) (hH : Hold I w) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hpre : w.crashed = false)
    (hph : ∀ i, i ∈ w.roster →
      phaseDeclared I (tname i) ((enqueueOrPark w I.desc sender dst msg isCall k).st i).phase) :
    Hold I (enqueueOrPark w I.desc sender dst msg isCall k) := by
  apply hold_actors I w (enqueueOrPark w I.desc sender dst msg isCall k) hH
    (mail_N w I.desc sender dst msg isCall k) (mail_roster w I.desc sender dst msg isCall k)
  · intro i; exact mail_life w I.desc sender dst msg isCall k i
  · intro i; exact mail_prio w I.desc sender dst msg isCall k i
  · intro i; exact mail_pend w I.desc sender dst msg isCall k i
  · intro i hi
    exact hph i (by simpa [mail_roster w I.desc sender dst msg isCall k] using hi)
  · exact (mail_crash w I.desc sender dst msg isCall k).symm ▸ hpre
  · exact hpre

end Deadlock
