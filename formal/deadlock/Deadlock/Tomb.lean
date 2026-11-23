/-
One tombstone per child slot, for a reachable world.

`Hold` is proved for every enabled step. `Side` carries `IxPast`, `RootPast`,
roster uniqueness, and the off-roster empty lane from the initial world
through every enabled step. `hold_reach` is `Hold` for every reachable world
under `GraphOk`. `Wired` records that a parent field was set by a birth whose
template names that supervisor. `no_tombstone_overflow` is `tmb_seal_room`
for a reachable world under `GraphOk` and `LocalOk`: sealing an alive
child does not fill a live parent's lane. `GraphOk` makes the
supervised template's tombstone nonempty, so the label is not a separate
assumption. `self_schedule_fits` and `cell_wake_fits` are the same lane for
a reachable actor's self-schedule and for a cell wake of one of its readers.
`LocalOk` supplies `prioSized`.
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

/-- One fresh member of `ys` lengthens a duplicate-free sublist by one. -/
theorem tmb_nodup_sub_cons {α} [DecidableEq α] (xs ys : List α) (x : α)
    (hnd : xs.Nodup) (hsub : ∀ z, z ∈ xs → z ∈ ys) (hx : x ∈ ys) (hfresh : x ∉ xs) :
    xs.length + 1 ≤ ys.length := by
  have hnd' : (x :: xs).Nodup := List.nodup_cons.mpr ⟨hfresh, hnd⟩
  have hsub' : ∀ z, z ∈ x :: xs → z ∈ ys := by
    intro z hz
    cases List.mem_cons.mp hz with
    | inl heq => exact heq ▸ hx
    | inr ht => exact hsub z ht
  simpa using tmb_nodup_sub_length (x :: xs) ys hnd' hsub'

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
  a.life == .alive

def occupant (a : Actor) : Bool :=
  a.life == .alive

/-- `(name, key)` is a child this parent still has to account for: a live
child, or a tombstone still sitting on the lane. -/
def holdsSlot (D : Description) (w : World) (parent : InstId) (name : String) (k : Nat) : Bool :=
  (w.roster.any fun c =>
    isChild w parent c &&
      match c with
      | .peer n key _ => n == name && key == k && lifeHold (w.st c)
      | .core _ => false) ||
    slotTombstoneQueued w parent name k

def legalSlots (D : Description) (parent : InstId) (N : Nat) : List (String × Nat) :=
  D.templates.flatMap fun c =>
    if supNamed c.supervisor (tname parent) && c.tombstone != "" then
      match parent with
      | .core _ => (List.range N).map fun k => (c.name, k)
      | .peer _ pk _ => [(c.name, pk)]
    else []

/-- A per-peer child uses a key drawn from `legalSlots`. A scheduler root
takes a fresh key, which need not lie in `0 ..< N`. A core births no child,
so a core parent indexes nothing. -/
def slotIndexed (D : Description) (parent : InstId) (_child : String) : Bool :=
  match parent with
  | .peer _ _ _ => true
  | .core _ => false

def tombSlots (ms : List Msg) : List (String × Nat) :=
  ms.filterMap fun m =>
    if m.tombstone then
      match m.sender with
      | .peer n k _ => some (n, k)
      | .core _ => none
    else none

theorem legal_mem_core (D : Description) (parent child : String) (N k : Nat) (c : Template)
    (hc : c ∈ D.templates) (hname : c.name = child) (hsup : c.supervisor = some parent)
    (htomb : c.tombstone ≠ "") (hk : k < N) :
    (child, k) ∈ legalSlots D (.core parent) N := by
  have hflat : (child, k) ∈ D.templates.flatMap (fun t =>
      if supNamed t.supervisor parent && t.tombstone != "" then
        (List.range N).map fun i => (t.name, i)
      else []) := by
    refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
    have hsupB : supNamed c.supervisor parent = true := by simp [supNamed, hsup]
    have htombB : (c.tombstone != "") = true := by
      simpa [bne, beq_iff_eq] using htomb
    simp [hsupB, htombB, List.mem_map, List.mem_range, hname, hk]
  simpa [legalSlots, tname] using hflat

theorem legal_mem_peer (D : Description) (parent child : String) (pk N : Nat) (c : Template)
    (hc : c ∈ D.templates) (hname : c.name = child) (hsup : c.supervisor = some parent)
    (htomb : c.tombstone ≠ "") :
    (child, pk) ∈ legalSlots D (.peer parent pk 0) N := by
  have hflat : (child, pk) ∈ D.templates.flatMap (fun t =>
      if supNamed t.supervisor parent && t.tombstone != "" then [(t.name, pk)] else []) := by
    refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
    have hsupB : supNamed c.supervisor parent = true := by simp [supNamed, hsup]
    have htombB : (c.tombstone != "") = true := by
      simpa [bne, beq_iff_eq] using htomb
    simp [hsupB, htombB, hname]
  simpa [legalSlots, tname] using hflat

def tmb_affineStep (sup : Template) (_t : Template) (acc : Affine) : Affine :=
  match sup.multiplicity with
  | .perPeer => { a := acc.a, b := acc.b + 1 }
  | .one => { a := acc.a + 1, b := acc.b }

theorem tmb_affineStep_eval (sup t : Template) (acc : Affine) (N : Nat) :
    (tmb_affineStep sup t acc).eval N = acc.eval N +
      match sup.multiplicity with
      | .perPeer => 1
      | .one => N := by
  cases hm : sup.multiplicity with
  | perPeer =>
    simp [tmb_affineStep, Affine.eval, hm, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  | one =>
    simp [tmb_affineStep, Affine.eval, hm, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

def tmb_keep (parent : InstId) (c : Template) : Bool :=
  supNamed c.supervisor (tname parent) && c.tombstone != ""

def tmb_leg (parent : InstId) (N : Nat) (c : Template) : Nat :=
  if tmb_keep parent c then
    match parent with
    | .core _ => N
    | .peer _ _ _ => 1
  else 0

def tmb_piece (parent : InstId) (N : Nat) (c : Template) : List (String × Nat) :=
  if supNamed c.supervisor (tname parent) && c.tombstone != "" then
    match parent with
    | .core _ => (List.range N).map fun k => (c.name, k)
    | .peer _ pk _ => [(c.name, pk)]
  else []

theorem tmb_piece_length (parent : InstId) (N : Nat) (c : Template) :
    (tmb_piece parent N c).length = tmb_leg parent N c := by
  unfold tmb_piece tmb_leg tmb_keep
  by_cases hkeep : (supNamed c.supervisor (tname parent) && c.tombstone != "") = true
  · simp only [hkeep, ite_true]
    cases parent with
    | core _ => simp [List.length_map, List.length_range]
    | peer _ _ _ => simp
  · have hf : (supNamed c.supervisor (tname parent) && c.tombstone != "") = false := by
      cases hbit : supNamed c.supervisor (tname parent) && c.tombstone != "" <;> simp_all
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
        if supNamed t.supervisor parentName && t.tombstone != "" then tmb_affineStep sup t acc else acc)
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
      (if supNamed c.supervisor (tname parent) && c.tombstone != "" then tmb_affineStep sup c acc
        else acc).eval N := by
  by_cases hkeep : (supNamed c.supervisor (tname parent) && c.tombstone != "") = true
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
      simp only [tmb_leg, tmb_keep, hkeep, ite_true]
      omega
  · have hf : (supNamed c.supervisor (tname parent) && c.tombstone != "") = false := by
      cases hbit : supNamed c.supervisor (tname parent) && c.tombstone != "" <;> simp_all
    simp [tmb_leg, tmb_keep, hf]

theorem tmb_fold_le (parent : InstId) (sup : Template) (N : Nat)
    (hrole : sup.multiplicity = tmb_role parent) :
    ∀ ts : List Template, ∀ acc : Affine,
      List.foldl (fun n c => n + tmb_leg parent N c) 0 ts + acc.eval N ≤
        (List.foldl (fun a t =>
          if supNamed t.supervisor (tname parent) && t.tombstone != "" then tmb_affineStep sup t a else a)
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
    have h2 := ih (if supNamed c.supervisor (tname parent) && c.tombstone != "" then
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

/-! Wired supervisors. -/

theorem subtreeFails_entry (D : Description) :
    subtreeFails D = D.templates.filterMap (subtreeEntry D) ++ coreFlagFails D := rfl


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

theorem tmb_dropHost_parent (dead : InstId) (w : World) (host i : InstId) :
    ((tmb_dropHost dead w host).st i).parent = (w.st i).parent := by
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
      have hneq : host ≠ dead := by
        intro heq
        have hb : (host == dead) = true := by simpa [beq_iff_eq] using heq
        simp [hb] at hf
      by_cases hi : i = host
      · simp [setActor, addTokens, hi, hneq]
      · by_cases hid : i = dead
        · have hdir : dead ≠ host := hneq.symm
          simp [setActor, addTokens, hi, hid, hdir]
        · simp [setActor, hi, hid]

theorem tmb_fold_drop_parent (dead : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (tmb_dropHost dead) w).st i).parent = (w.st i).parent := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons host ids ih =>
    intro w i
    simp only [List.foldl_cons]
    exact (ih (tmb_dropHost dead w host) i).trans (tmb_dropHost_parent dead w host i)

theorem credit_parent (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).parent = (w.st i).parent := by
  unfold creditSender
  by_cases hi : i = sender
  · simp [setActor, hi, bumpToken]
  · simp [setActor, hi]

theorem release_parent (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((releaseWorld D w id a).st i).parent = (w.st i).parent := by
  unfold releaseWorld
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) a.box
  let w3 := refundParked w2 (tname id) a.parked
  let w4 := releaseOutbound w3 id
  let dead : Actor :=
    { w4.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1 : (w1.st i).parent = (w.st i).parent := by
    simpa [w1] using congrArg (fun a : Actor => a.parent) (cellsSt D w id i)
  have h2 : (w2.st i).parent = (w1.st i).parent := by
    simpa [w2] using refundMsgs_parent w1 (tname id) a.box i
  have h3 : (w3.st i).parent = (w2.st i).parent := by
    simpa [w3] using refundParked_parent w2 (tname id) a.parked i
  have h4 : (w4.st i).parent = (w3.st i).parent := by
    simpa [w4] using releaseOutbound_parent w3 id i
  have h5 : ((setActor w4 id dead).st i).parent = (w4.st i).parent := by
    by_cases hi : i = id
    · simp [setActor, hi, dead]
    · simp [setActor, hi]
  exact (releaseParked_parent (setActor w4 id dead) id a.parked i).trans
    (h5.trans (h4.trans (h3.trans (h2.trans h1))))

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

def childOpen (D : Description) (w : World) (parent c : InstId) : Bool :=
  isChild w parent c && lifeHold (w.st c) && notifies D c

/-- Live notifying children of `parent`, plus the tombstones already on its lane. -/
def openCount (D : Description) (w : World) (parent : InstId) : Nat :=
  (w.roster.filter (childOpen D w parent)).length + (tombSlots (w.st parent).prio).length

/-- A notifying child of this template, or one of its tombstones. -/
def namedChild (D : Description) (w : World) (parent : InstId) (name : String) (c : InstId) : Bool :=
  childOpen D w parent c &&
    match c with
    | .peer n _ _ => n == name
    | .core _ => false

def namedTombs (ms : List Msg) (name : String) : List (String × Nat) :=
  (tombSlots ms).filter fun s => s.1 == name

def namedOpen (D : Description) (w : World) (parent : InstId) (name : String) : Nat :=
  (w.roster.filter (namedChild D w parent name)).length + (namedTombs (w.st parent).prio name).length

/-- How many of `name` one instance of `parent` may have outstanding. -/
def nameBudget (D : Description) (parent : InstId) (N : Nat) (name : String) : Nat :=
  match templateOf D name with
  | none => 0
  | some t => tmb_leg parent N t

theorem tmb_same_refl (id : InstId) : sameSlot id id = true := by
  cases id <;> simp [sameSlot]

theorem tmb_child_ne (w : World) (parent child : InstId)
    (h : isChild w parent child = true) : child ≠ parent := by
  intro heq
  subst heq
  simp [isChild] at h
  cases hpar : (w.st child).parent <;> simp [hpar, decide_eq_false_iff_not] at h

theorem isChild_eq (w w' : World) (parent child : InstId)
    (h : (w'.st child).parent = (w.st child).parent) :
    isChild w' parent child = isChild w parent child := by
  simp [isChild, h]

theorem child_of (w w' : World) (parent child : InstId)
    (h : (w'.st child).parent = (w.st child).parent)
    (hc : isChild w' parent child = true) : isChild w parent child = true :=
  (isChild_eq w w' parent child h).symm ▸ hc

theorem crash_parent (w : World) (i : InstId) :
    ((crashWorld w).st i).parent = (w.st i).parent := by
  unfold crashWorld crashActor
  dsimp
  split
  · split <;> rfl
  · rfl

theorem tmb_parent_alive (D : Description) (w : World) (child parent : InstId)
    (h : liveSupervisor D w child = some parent) :
    (w.st child).parent = some parent ∧ (w.st parent).life = .alive := by
  unfold liveSupervisor at h
  cases hpar : (w.st child).parent with
  | none => simp [hpar] at h
  | some p =>
    simp only [hpar] at h
    by_cases halive : (w.st p).life = .alive
    · have hbit : ((w.st p).life == .alive) = true := by simpa [beq_iff_eq] using halive
      simp only [hbit, ite_true] at h
      cases h
      exact ⟨rfl, halive⟩
    · have hbit : ((w.st p).life == .alive) = false := by simpa [beq_iff_eq] using halive
      simp only [hbit] at h
      cases h

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
and a slot that still has a live child does not also have a queued
tombstone. A dead actor keeps an empty lane unless the roster has crashed. -/
structure Hold (I : Impl) (w : World) : Prop where
  rostered : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster
  pend : ∀ id, (w.st id).pendingTombstone = true → (w.st id).life = .dead
  deadPrio : w.crashed = false → ∀ id, (w.st id).life = .dead → (w.st id).prio = []
  role : ∀ id, id ∈ w.roster → ∃ t, templateOf I.desc (tname id) = some t ∧
    t.multiplicity = tmb_role id
  phase : ∀ id, id ∈ w.roster → phaseDeclared I (tname id) (w.st id).phase
  lane : ∀ id, LaneOk I w id
  legalLife : ∀ parent c, c ∈ w.roster → isChild w parent c = true →
    lifeHold (w.st c) = true → notifies I.desc c = true →
    match c with
    | .peer n k _ => slotIndexed I.desc parent n = true → (n, k) ∈ legalSlots I.desc parent w.N
    | .core _ => True
  legalTomb : ∀ parent name k, slotTombstoneQueued w parent name k = true →
    slotIndexed I.desc parent name = true → (name, k) ∈ legalSlots I.desc parent w.N
  fresh : ∀ parent c, c ∈ w.roster → isChild w parent c = true →
    lifeHold (w.st c) = true → notifies I.desc c = true →
    match c with
    | .peer n k _ => slotTombstoneQueued w parent n k = false
    | .core _ => True
  /-- Two occupants of one slot are the same actor when they recorded the same
  parent. A descendant sealed with its parent is dead, so it no longer occupies
  the slot a restarted parent reuses. -/
  occ : ∀ c1 c2, c1 ∈ w.roster → c2 ∈ w.roster →
    occupant (w.st c1) = true → occupant (w.st c2) = true →
    sameSlot c1 c2 = true → (w.st c1).parent = (w.st c2).parent → c1 = c2
  /-- A core is born with no parent, and no step wires one. -/
  rooted : ∀ name, (w.st (.core name)).parent = none
  /-- Notifying children and queued tombstones of one template stay within that
  template's allowance. A fresh root key need not lie in `0 ..< N`; the allowance
  is a count, `N` for a scheduler root and one for a per-peer child. -/
  census : ∀ parent name, namedOpen I.desc w parent name ≤ nameBudget I.desc parent w.N name
  /-- A queued tombstone names an actor that is still on the roster. -/
  tombHere : ∀ id m, m ∈ (w.st id).prio → m.tombstone = true → m.sender ∈ w.roster

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

theorem tmb_live_peer (D : Description) (w : World) (child parent : InstId)
    (hroot : ∀ name, (w.st (.core name)).parent = none)
    (hne : child ≠ parent)
    (h : liveSupervisor D w child = some parent) :
    ∃ n k g, child = .peer n k g ∧ isChild w parent child = true := by
  obtain ⟨hpar, _⟩ := tmb_parent_alive D w child parent h
  cases child with
  | core name => simp [hroot name] at hpar
  | peer n k g =>
    refine ⟨n, k, g, rfl, ?_⟩
    simp [isChild, hpar, hne]

/-- Sealing an alive child does not fill its parent's priority lane.
The queued tombstones plus this one are at most the slot bound, and the other
priority messages are within the declared sender count. -/
def tmb_nameIs (name : String) (c : InstId) : Bool :=
  match c with
  | .peer n _ _ => n == name
  | .core _ => false

theorem foldl_add_shift {α : Type} (f : α → Nat) (xs : List α) (start : Nat) :
    xs.foldl (fun n x => n + f x) start = start + xs.foldl (fun n x => n + f x) 0 := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (start + f x), ih (f x)]
    omega

theorem tmb_fold_filter_shift (ts : List Template) (xs : List InstId) (c : InstId)
    (p : InstId → Bool) (hp : p c = true) :
    ts.foldl (fun n t => n + ((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length) 0 =
      (ts.filter (fun t => tmb_nameIs t.name c)).length +
        ts.foldl (fun n t => n + (xs.filter (fun x => p x && tmb_nameIs t.name x)).length) 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift
        (fun u => ((c :: xs).filter (fun x => p x && tmb_nameIs u.name x)).length) ts
        (((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length),
      foldl_add_shift
        (fun u => (xs.filter (fun x => p x && tmb_nameIs u.name x)).length) ts
        ((xs.filter (fun x => p x && tmb_nameIs t.name x)).length), ih]
    by_cases hn : tmb_nameIs t.name c = true
    · have hhead : ((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length =
          (xs.filter (fun x => p x && tmb_nameIs t.name x)).length + 1 := by
        simp [List.filter_cons, hp, hn, Bool.and_true]
      have hbit : ((t :: ts).filter (fun u => tmb_nameIs u.name c)).length =
          (ts.filter (fun u => tmb_nameIs u.name c)).length + 1 := by
        simp [List.filter_cons, hn]
      rw [hhead, hbit]
      omega
    · have hf : tmb_nameIs t.name c = false := by
        cases hbit : tmb_nameIs t.name c <;> simp_all
      have hhead : ((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length =
          (xs.filter (fun x => p x && tmb_nameIs t.name x)).length := by
        simp [List.filter_cons, hp, hf]
      have hbit : ((t :: ts).filter (fun u => tmb_nameIs u.name c)).length =
          (ts.filter (fun u => tmb_nameIs u.name c)).length := by
        simp [List.filter_cons, hf]
      rw [hhead, hbit]
      omega

theorem tmb_roster_le (ts : List Template) (xs : List InstId) (p : InstId → Bool)
    (hcov : ∀ c, c ∈ xs → p c = true → (ts.filter (fun t => tmb_nameIs t.name c)).length ≠ 0) :
    (xs.filter p).length ≤
      ts.foldl (fun n t => n + (xs.filter (fun x => p x && tmb_nameIs t.name x)).length) 0 := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    by_cases hp : p c = true
    · have hlen : ((c :: xs).filter p).length = (xs.filter p).length + 1 := by
        simp [List.filter_cons, hp]
      rw [hlen]
      have hhit : (ts.filter (fun t => tmb_nameIs t.name c)).length ≠ 0 :=
        hcov c List.mem_cons_self hp
      have hpos : 1 ≤ (ts.filter (fun t => tmb_nameIs t.name c)).length :=
        Nat.one_le_iff_ne_zero.mpr hhit
      have hshift := tmb_fold_filter_shift ts xs c p hp
      have htail := ih fun d hd hq => hcov d (List.mem_cons_of_mem c hd) hq
      omega
    · have hf : p c = false := by
        cases hbit : p c <;> simp_all
      have hlen : ((c :: xs).filter p).length = (xs.filter p).length := by
        simp [List.filter_cons, hf]
      rw [hlen]
      have hdrop : ∀ (t : Template),
          (xs.filter (fun x => p x && tmb_nameIs t.name x)).length =
            ((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length := by
        intro t
        rw [List.filter_cons]
        have hneg : ¬ ((p c && tmb_nameIs t.name c) = true) := by
          rw [hf]
          cases tmb_nameIs t.name c <;> decide
        rw [ite_eq_right hneg]
      have htail := ih fun d hd hq => hcov d (List.mem_cons_of_mem c hd) hq
      have heq : ts.foldl (fun n t => n + (xs.filter (fun x => p x && tmb_nameIs t.name x)).length) 0 =
          ts.foldl (fun n t => n + ((c :: xs).filter (fun x => p x && tmb_nameIs t.name x)).length) 0 := by
        congr 1
        funext n t
        exact congrArg (fun k => n + k) (hdrop t)
      exact Nat.le_trans htail (Nat.le_of_eq heq)

theorem tmb_child_covered (D : Description) (w : World) (parent : InstId) (c : InstId)
    (hroot : ∀ name, (w.st (.core name)).parent = none)
    (ho : childOpen D w parent c = true) :
    (D.templates.filter (fun t => tmb_nameIs t.name c)).length ≠ 0 := by
  have ho' : notifies D c = true := by
    simp [childOpen, Bool.and_eq_true] at ho
    exact ho.2
  cases c with
  | core name =>
    simp [childOpen, isChild, hroot name] at ho
  | peer n k g =>
    unfold notifies at ho'
    cases hlook : templateOf D n with
    | none => simp [hlook, tname] at ho'
    | some t =>
      have hmem : t ∈ D.templates ∧ t.name = n := templateOf_mem D n t (by simpa [tname] using hlook)
      have hname : tmb_nameIs t.name (InstId.peer n k g) = true := by
        simp [tmb_nameIs, hmem.2]
      have hhit : t ∈ D.templates.filter (fun u => tmb_nameIs u.name (InstId.peer n k g)) :=
        List.mem_filter.mpr ⟨hmem.1, hname⟩
      exact Nat.ne_of_gt (List.length_pos_of_mem hhit)

theorem tmb_fold_add (ts : List Template) (f g : Template → Nat) :
    ts.foldl (fun n t => n + (f t + g t)) 0 =
      ts.foldl (fun n t => n + f t) 0 + ts.foldl (fun n t => n + g t) 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift (fun u => f u + g u) ts (f t + g t),
      foldl_add_shift f ts (f t), foldl_add_shift g ts (g t), ih]
    omega

theorem tmb_fold_le_of_le (ts : List Template) (f g : Template → Nat)
    (h : ∀ t, t ∈ ts → f t ≤ g t) :
    ts.foldl (fun n t => n + f t) 0 ≤ ts.foldl (fun n t => n + g t) 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift f ts (f t), foldl_add_shift g ts (g t)]
    exact Nat.add_le_add (h t List.mem_cons_self)
      (ih fun u hu => h u (List.mem_cons_of_mem t hu))

def addFirst (acc : List Template) (t : Template) : List Template :=
  if acc.any (fun u => u.name == t.name) then acc else acc ++ [t]

def firstTemplates (ts : List Template) : List Template :=
  ts.foldl addFirst []

theorem addFirst_fold (parent : InstId) (N : Nat) (acc : List Template) (t : Template) :
    (addFirst acc t).foldl (fun n u => n + tmb_leg parent N u) 0 ≤
      acc.foldl (fun n u => n + tmb_leg parent N u) 0 + tmb_leg parent N t := by
  unfold addFirst
  by_cases h : acc.any (fun u => u.name == t.name) = true
  · simp only [h, ite_true]
    exact Nat.le_add_right _ _
  · have hf : acc.any (fun u => u.name == t.name) = false := by
      cases hbit : acc.any (fun u => u.name == t.name) <;> simp_all
    rw [if_neg (by simpa [hf])]
    rw [List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil]

theorem first_fold_le (parent : InstId) (N : Nat) (acc ts : List Template) :
    (ts.foldl addFirst acc).foldl (fun n u => n + tmb_leg parent N u) 0 ≤
      acc.foldl (fun n u => n + tmb_leg parent N u) 0 +
        ts.foldl (fun n u => n + tmb_leg parent N u) 0 := by
  induction ts generalizing acc with
  | nil =>
    simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift (fun u => tmb_leg parent N u) ts (tmb_leg parent N t)]
    have h1 := addFirst_fold parent N acc t
    have h2 := ih (addFirst acc t)
    omega

theorem first_leg_le (parent : InstId) (N : Nat) (ts : List Template) :
    (firstTemplates ts).foldl (fun n u => n + tmb_leg parent N u) 0 ≤
      ts.foldl (fun n u => n + tmb_leg parent N u) 0 := by
  simpa [firstTemplates, List.foldl_nil] using first_fold_le parent N [] ts

theorem nameFails_nil (D : Description) (hG : GraphOk D) : nameFails D = [] := by
  cases h : nameFails D with
  | nil => rfl
  | cons s ss =>
    have hstruct := hG.struct
    simp [structLines, h] at hstruct

theorem dedupStep_le {α : Type} [DecidableEq α] (acc xs : List α) :
    (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length ≤
      acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hmem : acc.elem x = true
    · simp only [hmem, ite_true, List.length_cons]
      exact Nat.le_trans (ih acc) (by omega)
    · have hf : acc.elem x = false := by
        cases hbit : acc.elem x <;> simp_all
      have hneg : ¬ acc.elem x = true := by
        rw [hf]
        decide
      rw [ite_eq_right hneg]
      have hstep := ih (acc ++ [x])
      rw [List.length_append, List.length_cons, List.length_nil] at hstep
      simp only [List.length_cons]
      omega

theorem nodup_of_fold_length {α : Type} [DecidableEq α] (acc xs : List α) (hacc : acc.Nodup)
    (h : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length =
      acc.length + xs.length) :
    xs.Nodup ∧ ∀ x, x ∈ xs → x ∉ acc := by
  induction xs generalizing acc with
  | nil =>
    exact ⟨List.nodup_nil, fun _ hx => nomatch hx⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons] at h
    by_cases hmem : acc.elem x = true
    · simp only [hmem, ite_true] at h
      have hle := dedupStep_le acc xs
      omega
    · have hf : acc.elem x = false := by
        cases hbit : acc.elem x <;> simp_all
      have hneg : ¬ acc.elem x = true := by
        rw [hf]
        decide
      rw [ite_eq_right hneg] at h
      have hx : x ∉ acc := by
        intro hin
        exact hneg (List.elem_iff.mpr hin)
      have hacc' : (acc ++ [x]).Nodup := by
        suffices happend : ∀ ys, ys.Nodup → x ∉ ys → (ys ++ [x]).Nodup by
          exact happend acc hacc hx
        intro ys
        induction ys with
        | nil =>
          intro _ _
          exact List.nodup_cons.mpr ⟨(by intro h; cases h), List.nodup_nil⟩
        | cons y ys ih =>
          intro hys hxout
          have hnd := List.nodup_cons.mp hys
          have hy : y ≠ x := by
            intro heq
            exact hxout (by simp [heq])
          simp only [List.cons_append]
          refine List.nodup_cons.mpr ⟨?_, ih hnd.2 (fun hmem => hxout (List.mem_cons_of_mem y hmem))⟩
          intro hin
          simp [List.mem_append, List.mem_singleton] at hin
          cases hin with
          | inl hys' => exact hnd.1 hys'
          | inr heq => exact hy heq
      have hlen : (xs.foldl (fun acc y => if acc.elem y then acc else acc ++ [y]) (acc ++ [x])).length =
          (acc ++ [x]).length + xs.length := by
        have happ : (acc ++ [x]).length = acc.length + 1 := by
          rw [List.length_append, List.length_cons, List.length_nil]
        exact Eq.trans h (by omega)
      have hrec := ih (acc ++ [x]) hacc' hlen
      refine ⟨List.nodup_cons.mpr ⟨?_, hrec.1⟩, ?_⟩
      · intro hxsin
        exact hrec.2 x hxsin (List.mem_append_right acc (List.mem_singleton.mpr rfl))
      · intro y hy
        cases List.mem_cons.mp hy with
        | inl heq =>
          subst heq
          exact hx
        | inr hys =>
          intro hin
          exact hrec.2 y hys (List.mem_append_left _ hin)

theorem names_nodup (D : Description) (hG : GraphOk D) : (D.templates.map (·.name)).Nodup := by
  have hfail := nameFails_nil D hG
  unfold nameFails at hfail
  dsimp only at hfail
  revert hfail
  generalize hcond : ((D.templates.map (·.name)).length ==
      (dedup (D.templates.map (·.name))).length) = b
  intro hfail
  cases b with
  | true =>
    have hlen : (D.templates.map (·.name)).length =
        (dedup (D.templates.map (·.name))).length := by
      simpa [beq_iff_eq] using hcond
    have hfold := nodup_of_fold_length [] (D.templates.map (·.name)) List.nodup_nil
      (by simpa [dedup, List.length_nil] using hlen.symm)
    exact hfold.1
  | false =>
    simp at hfail

theorem find_unique (ts : List Template) (t : Template) (ht : t ∈ ts)
    (hnodup : (ts.map (·.name)).Nodup) :
    ts.findSome? (fun u => if u.name == t.name then some u else none) = some t := by
  induction ts with
  | nil => cases ht
  | cons u us ih =>
    rw [List.findSome?_cons]
    by_cases hname : (u.name == t.name) = true
    · simp only [hname, ite_true]
      cases List.mem_cons.mp ht with
      | inl heq =>
        subst heq
        rfl
      | inr htail =>
        exfalso
        have hnd := List.nodup_cons.mp hnodup
        have heq : u.name = t.name := by simpa [beq_iff_eq] using hname
        have hin : u.name ∈ us.map (·.name) := by
          rw [heq]
          exact List.mem_map.mpr ⟨t, htail, rfl⟩
        exact hnd.1 hin
    · have hf : (u.name == t.name) = false := by
        cases hbit : u.name == t.name <;> simp_all
      simp only [hf, ite_false]
      have htail : t ∈ us := by
        cases List.mem_cons.mp ht with
        | inl heq =>
          subst heq
          simp at hf
        | inr h => exact h
      exact ih htail (List.nodup_cons.mp hnodup).2

theorem template_unique (D : Description) (hG : GraphOk D) (t : Template) (ht : t ∈ D.templates) :
    templateOf D t.name = some t := by
  simpa [templateOf] using find_unique D.templates t ht (names_nodup D hG)

theorem tmb_fold_slot_shift (ts : List Template) (xs : List (String × Nat)) (s : String × Nat) :
    ts.foldl (fun n t => n + ((s :: xs).filter (fun x => x.1 == t.name)).length) 0 =
      (ts.filter (fun t => s.1 == t.name)).length +
        ts.foldl (fun n t => n + (xs.filter (fun x => x.1 == t.name)).length) 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift (fun u => ((s :: xs).filter (fun x => x.1 == u.name)).length) ts
        (((s :: xs).filter (fun x => x.1 == t.name)).length),
      foldl_add_shift (fun u => (xs.filter (fun x => x.1 == u.name)).length) ts
        ((xs.filter (fun x => x.1 == t.name)).length), ih]
    by_cases hn : (s.1 == t.name) = true
    · have hhead : ((s :: xs).filter (fun x => x.1 == t.name)).length =
          (xs.filter (fun x => x.1 == t.name)).length + 1 := by
        simp [List.filter_cons, hn]
      have hbit : ((t :: ts).filter (fun u => s.1 == u.name)).length =
          (ts.filter (fun u => s.1 == u.name)).length + 1 := by
        simp [List.filter_cons, hn]
      rw [hhead, hbit]
      omega
    · have hf : (s.1 == t.name) = false := by
        cases hbit : s.1 == t.name <;> simp_all
      have hhead : ((s :: xs).filter (fun x => x.1 == t.name)).length =
          (xs.filter (fun x => x.1 == t.name)).length := by
        simp [List.filter_cons, hf]
      have hbit : ((t :: ts).filter (fun u => s.1 == u.name)).length =
          (ts.filter (fun u => s.1 == u.name)).length := by
        simp [List.filter_cons, hf]
      rw [hhead, hbit]
      omega

theorem tmb_slot_le (ts : List Template) (xs : List (String × Nat))
    (hcov : ∀ s, s ∈ xs → (ts.filter (fun t => s.1 == t.name)).length ≠ 0) :
    xs.length ≤ ts.foldl (fun n t => n + (xs.filter (fun x => x.1 == t.name)).length) 0 := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    simp only [List.length_cons]
    have hhit : (ts.filter (fun t => s.1 == t.name)).length ≠ 0 := hcov s List.mem_cons_self
    have hpos : 1 ≤ (ts.filter (fun t => s.1 == t.name)).length :=
      Nat.one_le_iff_ne_zero.mpr hhit
    have hshift := tmb_fold_slot_shift ts xs s
    have htail := ih fun r hr => hcov r (List.mem_cons_of_mem s hr)
    rw [hshift]
    omega

theorem tomb_name_covered (D : Description) (w : World) (parent : InstId)
    (h : ∀ name, namedOpen D w parent name ≤ nameBudget D parent w.N name)
    (s : String × Nat) (hs : s ∈ tombSlots (w.st parent).prio) :
    (D.templates.filter (fun t => s.1 == t.name)).length ≠ 0 := by
  intro h0
  have hempty : D.templates.filter (fun t => s.1 == t.name) = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using h0)
  have hnone : templateOf D s.1 = none := by
    have hgo : ∀ (ts : List Template), ts.filter (fun t => s.1 == t.name) = [] →
        ts.findSome? (fun t => if t.name == s.1 then some t else none) = none := by
      intro ts
      induction ts with
      | nil =>
        intro _
        simp
      | cons t ts ih =>
        intro hempty
        rw [List.filter_cons] at hempty
        by_cases hb : (s.1 == t.name) = true
        · simp only [hb, ite_true] at hempty
          cases hempty
        · have hf : (s.1 == t.name) = false := by
            cases hbit : s.1 == t.name <;> simp_all
          simp only [hf, ite_false] at hempty
          rw [List.findSome?_cons]
          have hne : s.1 ≠ t.name := by
            intro heq
            exact (by simpa [hf] : ¬ (s.1 == t.name) = true) (by simpa [beq_iff_eq, heq])
          have hnot : (t.name == s.1) = false := by
            simpa [beq_iff_eq] using hne.symm
          simp only [hnot, ite_false]
          exact ih hempty
    unfold templateOf
    exact hgo D.templates hempty
  have hmem : s ∈ namedTombs (w.st parent).prio s.1 :=
    List.mem_filter.mpr ⟨hs, by simp⟩
  have hpos : 1 ≤ namedOpen D w parent s.1 := by
    unfold namedOpen
    exact Nat.le_trans (Nat.succ_le_of_lt (List.length_pos_of_mem hmem)) (Nat.le_add_left _ _)
  have hbud := h s.1
  simp [nameBudget, hnone] at hbud
  omega

/-- The per-template count is at most the lane's slot list. Duplicate template
names are rejected by `GraphOk`, so each name is charged once. -/
theorem census_total (D : Description) (w : World) (parent : InstId)
    (hG : GraphOk D) (hroot : ∀ name, (w.st (.core name)).parent = none)
    (h : ∀ name, namedOpen D w parent name ≤ nameBudget D parent w.N name) :
    openCount D w parent ≤ (legalSlots D parent w.N).length := by
  have hchild : (w.roster.filter (childOpen D w parent)).length ≤
      D.templates.foldl (fun n t => n + (w.roster.filter (namedChild D w parent t.name)).length) 0 := by
    have hle := tmb_roster_le D.templates w.roster (childOpen D w parent)
      (fun c _ ho => tmb_child_covered D w parent c hroot ho)
    have heq : D.templates.foldl (fun n t =>
          n + (w.roster.filter (fun x => childOpen D w parent x && tmb_nameIs t.name x)).length) 0 =
        D.templates.foldl (fun n t => n + (w.roster.filter (namedChild D w parent t.name)).length) 0 := by
      congr 1
    exact Nat.le_trans hle (Nat.le_of_eq heq)
  have htomb : (tombSlots (w.st parent).prio).length ≤
      D.templates.foldl (fun n t => n + (namedTombs (w.st parent).prio t.name).length) 0 := by
    have hle := tmb_slot_le D.templates (tombSlots (w.st parent).prio)
      (fun s hs => tomb_name_covered D w parent h s hs)
    have heq : D.templates.foldl (fun n t =>
          n + ((tombSlots (w.st parent).prio).filter (fun x => x.1 == t.name)).length) 0 =
        D.templates.foldl (fun n t => n + (namedTombs (w.st parent).prio t.name).length) 0 := by
      congr 1
    exact Nat.le_trans hle (Nat.le_of_eq heq)
  have hopen : openCount D w parent ≤
      D.templates.foldl (fun n t => n + namedOpen D w parent t.name) 0 := by
    unfold openCount
    have hadd := tmb_fold_add D.templates
      (fun t => (w.roster.filter (namedChild D w parent t.name)).length)
      (fun t => (namedTombs (w.st parent).prio t.name).length)
    have hparts : D.templates.foldl (fun n t =>
        n + ((w.roster.filter (namedChild D w parent t.name)).length +
          (namedTombs (w.st parent).prio t.name).length)) 0 =
        D.templates.foldl (fun n t => n + namedOpen D w parent t.name) 0 := by
      apply congrArg (fun f => D.templates.foldl f 0)
      funext n t
      simp [namedOpen]
    omega
  have hleg : D.templates.foldl (fun n t => n + namedOpen D w parent t.name) 0 ≤
      D.templates.foldl (fun n t => n + tmb_leg parent w.N t) 0 := by
    refine tmb_fold_le_of_le D.templates _ _ ?_
    intro t ht
    have huniq := template_unique D hG t ht
    have hbudget := h t.name
    simpa [nameBudget, huniq] using hbudget
  rw [tmb_legal_length]
  exact Nat.le_trans hopen hleg

theorem tmb_seal_room (I : Impl) (w : World) (child : InstId)
    (hG : GraphOk I.desc) (hL : LocalOk I) (hH : Hold I w)
    (hliveC : (w.st child).life = .alive) :
    ∀ parent, liveSupervisor I.desc (releaseWorld I.desc w child (w.st child)) child = some parent →
      ((releaseWorld I.desc w child (w.st child)).st parent).life = .alive →
      (tombstoneMsg I.desc ((releaseWorld I.desc w child (w.st child)).st parent) child).label ≠ "" →
      prioLoad ((releaseWorld I.desc w child (w.st child)).st parent).prio <
        capPrio I.desc (releaseWorld I.desc w child (w.st child)).N parent := by
  intro parent hsup halive hlabel
  let sealed := releaseWorld I.desc w child (w.st child)
  have hmem : child ∈ w.roster := hH.rostered child (by rw [hliveC]; intro h; cases h)
  have hrole := hH.role child hmem
  have hne : child ≠ parent := by
    intro heq
    have hdead := releaseWorld_self_dead I.desc w child (w.st child)
    have hdead' : ((releaseWorld I.desc w child (w.st child)).st parent).life = .dead := by
      simpa [heq] using hdead
    have hbad := hdead'.symm.trans halive
    cases hbad
  have hroot : ∀ name, (sealed.st (InstId.core name)).parent = none := by
    intro name
    have hpar := release_parent I.desc w child (w.st child) (InstId.core name)
    simpa [sealed, hpar] using hH.rooted name
  obtain ⟨n, k, g, hid, hchild⟩ :=
    tmb_live_peer I.desc sealed child parent hroot hne hsup
  have hchildW : isChild w parent child = true := by
    have hpar := release_parent I.desc w child (w.st child) child
    simpa [isChild_eq w sealed parent child hpar] using hchild
  have hprio := releaseWorld_prio I.desc w child (w.st child) parent hne.symm
  have hkeep := releaseWorld_keep I.desc w child (w.st child) parent hne.symm
  have hpre : (w.st parent).life = .alive := by
    rw [← hkeep.1]
    exact halive
  have hpmem : parent ∈ w.roster := hH.rostered parent (by rw [hpre]; intro h; cases h)
  obtain ⟨sup, ht, hmult⟩ := hH.role parent hpmem
  have hsized : prioSized I.desc (tname parent) (prioSenderBound I (tname parent)) = true :=
    tmb_prio_sized I hL (tname parent) sup ht
  have hhold : lifeHold (w.st child) = true := by simp [lifeHold, hliveC]
  have hnote : notifies I.desc child = true :=
    tmb_notifies_of_label I.desc child (by simpa [tombstoneMsg] using hlabel)
  have hlive : child ∈ w.roster.filter (childOpen I.desc w parent) := by
    refine List.mem_filter.mpr ⟨hmem, ?_⟩
    simp [childOpen, hchildW, hhold, hnote]
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
  have hcount : (tombSlots (w.st parent).prio).length + 1 ≤
      (legalSlots I.desc parent w.N).length := by
    have hpos : 1 ≤ (w.roster.filter (childOpen I.desc w parent)).length :=
      Nat.succ_le_of_lt (List.length_pos_of_mem hlive)
    have hstep : (tombSlots (w.st parent).prio).length + 1 ≤ openCount I.desc w parent := by
      unfold openCount
      omega
    exact Nat.le_trans hstep (census_total I.desc w parent hG hH.rooted (hH.census parent))
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

theorem lifeHold_eq (a b : Actor) (hl : a.life = b.life) :
    lifeHold a = lifeHold b := by
  simp [lifeHold, hl]

theorem occupant_eq (a b : Actor) (hl : a.life = b.life) : occupant a = occupant b := by
  simp [occupant, hl]

theorem openCount_cast (D : Description) (w w' : World) (parent : InstId)
    (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hprio : (w'.st parent).prio = (w.st parent).prio) :
    openCount D w' parent = openCount D w parent := by
  have hpred : ∀ c, childOpen D w' parent c = childOpen D w parent c := by
    intro c
    simp [childOpen, lifeHold, isChild, hlife c, hpend c, hpar c]
  have hfilter : w'.roster.filter (childOpen D w' parent) =
      w.roster.filter (childOpen D w parent) := by
    rw [hros]
    apply List.filter_congr
    intro c _
    exact hpred c
  simp [openCount, hfilter, hprio]

theorem namedOpen_cast (D : Description) (w w' : World) (parent : InstId)
    (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hprio : (w'.st parent).prio = (w.st parent).prio) (name : String) :
    namedOpen D w' parent name = namedOpen D w parent name := by
  have hpred : ∀ c, namedChild D w' parent name c = namedChild D w parent name c := by
    intro c
    simp [namedChild, childOpen, lifeHold, isChild, hlife c, hpend c, hpar c]
  have hfilter : w'.roster.filter (namedChild D w' parent name) =
      w.roster.filter (namedChild D w parent name) := by
    rw [hros]
    apply List.filter_congr
    intro c _
    exact hpred c
  simp [namedOpen, hfilter, hprio, namedTombs]

/-- A step that keeps every life, priority lane, and tombstone arm, and leaves
every roster phase declared, keeps the lane invariant. -/
theorem hold_actors (I : Impl) (w w' : World) (hH : Hold I w)
    (hN : w'.N = w.N) (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hphase : ∀ id, id ∈ w'.roster → phaseDeclared I (tname id) (w'.st id).phase)
    (hcr : w'.crashed = w.crashed) : Hold I w' := by
  refine ⟨?_, ?_, ?_, ?_, hphase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    exact hros ▸ hH.rostered id (by simpa [hlife id] using hl)
  · intro id hp
    have h := hH.pend id (by simpa [hpend id] using hp)
    simpa [hlife id] using h
  · intro hc id hd
    exact hprio id ▸ hH.deadPrio (hcr.symm ▸ hc) id (by simpa [hlife id] using hd)
  · intro id hid
    exact hH.role id (by simpa [hros] using hid)
  · intro id
    exact lane_cast I w w' hprio id (hH.lane id)
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c)] using hhold
    have hchild' : isChild w parent c = true := by
      simpa [isChild_eq w w' parent c (hpar c)] using hchild
    have hlegal := hH.legalLife parent c (by simpa [hros] using hc) hchild' hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hN] using hlegal
  · intro parent name k hq
    have hq' : slotTombstoneQueued w parent name k = true := by
      simpa [slotTombstoneQueued, hprio parent] using hq
    simpa [hN] using hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c)] using hhold
    have hchild' : isChild w parent c = true := by
      simpa [isChild_eq w w' parent c (hpar c)] using hchild
    have hfresh := hH.fresh parent c (by simpa [hros] using hc) hchild' hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [slotTombstoneQueued, hprio parent] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    have ho1' : occupant (w.st c1) = true := by
      simpa [occupant_eq (w'.st c1) (w.st c1) (hlife c1)] using ho1
    have ho2' : occupant (w.st c2) = true := by
      simpa [occupant_eq (w'.st c2) (w.st c2) (hlife c2)] using ho2
    exact hH.occ c1 c2 (by simpa [hros] using hc1) (by simpa [hros] using hc2) ho1' ho2' hslot
      ((hpar c1).symm.trans (hpa.trans (hpar c2)))
  · intro name
    simpa [hpar (.core name)] using hH.rooted name
  · intro parent name
    have hcount := namedOpen_cast I.desc w w' parent hros hlife hpend hpar (hprio parent) name
    simpa [nameBudget, hN, hcount] using hH.census parent name
  · intro id m hm ht
    exact hros ▸ hH.tombHere id m (by simpa [hprio id] using hm) ht

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
      by_cases hl : ((w.st i).life == .alive) = true
      · simp [hl]
      · have hf : ((w.st i).life == .alive) = false := by
          cases hbit : (w.st i).life == .alive <;> simp_all
        simp [hf]
    · have hf : decide (i ∈ w.roster) = false := by
        cases hbit : decide (i ∈ w.roster) <;> simp_all
      simp [hf]
  · by_cases hc : decide (i ∈ w.roster) = true
    · simp only [hc, ite_true, crashActor]
      by_cases hl : ((w.st i).life == .alive) = true
      · simp [hl]
      · have hf : ((w.st i).life == .alive) = false := by
          cases hbit : (w.st i).life == .alive <;> simp_all
        simp [hf]
    · have hf : decide (i ∈ w.roster) = false := by
        cases hbit : decide (i ∈ w.roster) <;> simp_all
      simp [hf]

theorem crash_life (w : World) (i : InstId) :
    ((crashWorld w).st i).life =
      if decide (i ∈ w.roster) = true then
        if ((w.st i).life == .alive) = true then .dead
        else (w.st i).life
      else (w.st i).life := by
  unfold crashWorld
  dsimp
  by_cases hc : decide (i ∈ w.roster) = true
  · simp only [hc, ite_true, crashActor]
    by_cases hl : ((w.st i).life == .alive) = true
    · simp [hl]
    · have hf : ((w.st i).life == .alive) = false := by
        cases hbit : (w.st i).life == .alive <;> simp_all
      simp [hf]
  · have hf : decide (i ∈ w.roster) = false := by
      cases hbit : decide (i ∈ w.roster) <;> simp_all
    simp [hf]

theorem crash_phase (w : World) (i : InstId) :
    ((crashWorld w).st i).phase =
      if decide (i ∈ w.roster) = true then
        if ((w.st i).life == .alive) = true then .crashed
        else (w.st i).phase
      else (w.st i).phase := by
  unfold crashWorld
  dsimp
  by_cases hc : decide (i ∈ w.roster) = true
  · simp only [hc, ite_true, crashActor]
    by_cases hl : ((w.st i).life == .alive) = true
    · simp [hl]
    · have hf : ((w.st i).life == .alive) = false := by
        cases hbit : (w.st i).life == .alive <;> simp_all
      simp [hf]
  · have hf : decide (i ∈ w.roster) = false := by
      cases hbit : decide (i ∈ w.roster) <;> simp_all
    simp [hf]


theorem crash_not_alive (w : World) (i : InstId) (hmem : i ∈ w.roster) :
    ((crashWorld w).st i).life ≠ .alive := by
  have hdec : decide (i ∈ w.roster) = true := decide_eq_true hmem
  cases hlife : (w.st i).life with
  | alive =>
    simp [crashWorld, crashActor, hlife, hmem]
  | dead =>
    simp [crashWorld, hdec, crashActor, hlife]
  | absent =>
    simp [crashWorld, hdec, crashActor, hlife]

theorem hold_crash (I : Impl) (w : World) (hH : Hold I w) : Hold I (crashWorld w) := by
  have hf := fun i => crash_fields w i
  have lifeSame (i : InstId)
      (hc : decide (i ∈ w.roster) = false ∨
        ((w.st i).life == .alive) = false) :
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
      (hlive : ((w.st i).life == .alive) = true) :
      ((crashWorld w).st i).life = .dead ∧ ((crashWorld w).st i).phase = .crashed := by
    exact ⟨by simp [crash_life, hdec, hlive], by simp [crash_phase, hdec, hlive]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    by_cases hc : id ∈ w.roster
    · simpa [(hf id).2.2.1] using hc
    · have hst := (lifeSame id (Or.inl (decide_eq_false hc))).1
      exact hH.rostered id (hst ▸ hl)
  · intro id hp
    by_cases hdec : decide (id ∈ w.roster) = true
    · by_cases hlive : ((w.st id).life == .alive) = true
      · exact (lifeDead id hdec hlive).1
      · have hf' : ((w.st id).life == .alive) = false := by
          cases hbit : (w.st id).life == .alive <;> simp_all
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
    · by_cases hlive : ((w.st id).life == .alive) = true
      · simpa [(lifeDead id hdec hlive).2, phaseDeclared]
      · have hf' : ((w.st id).life == .alive) = false := by
          cases hbit : (w.st id).life == .alive <;> simp_all
        simpa [(lifeSame id (Or.inr hf')).2] using hH.phase id (by simpa [(hf id).2.2.1] using hid)
    · have hno : decide (id ∈ w.roster) = false := by
        cases hbit : decide (id ∈ w.roster) <;> simp_all
      simpa [(lifeSame id (Or.inl hno)).2] using hH.phase id (by simpa [(hf id).2.2.1] using hid)
  · intro id
    exact lane_cast I w (crashWorld w) (fun i => (hf i).1) id (hH.lane id)
  · intro parent c hc hchild hhold hnote
    by_cases hdec : decide (c ∈ w.roster) = true
    · by_cases hlive : ((w.st c).life == .alive) = true
      · have hdead : lifeHold ((crashWorld w).st c) = false := by
          simp [lifeHold, (lifeDead c hdec hlive).1]
        simp [hdead] at hhold
      · have hf' : ((w.st c).life == .alive) = false := by
          cases hbit : (w.st c).life == .alive <;> simp_all
        have hhold' : lifeHold (w.st c) = true := by
          simpa [lifeHold, (lifeSame c (Or.inr hf')).1, (hf c).2.1] using hhold
        have hlegal := hH.legalLife parent c (by simpa [(hf c).2.2.1] using hc)
          (child_of w (crashWorld w) parent c (crash_parent w c) hchild) hhold' hnote
        have hN : (crashWorld w).N = w.N := (hf c).2.2.2.1
        cases c with
        | core _ => trivial
        | peer n k g => simpa [hN] using hlegal
    · have hno : decide (c ∈ w.roster) = false := by
        cases hbit : decide (c ∈ w.roster) <;> simp_all
      have hhold' : lifeHold (w.st c) = true := by
        simpa [lifeHold, (lifeSame c (Or.inl hno)).1, (hf c).2.1] using hhold
      have hlegal := hH.legalLife parent c (by simpa [(hf c).2.2.1] using hc)
          (child_of w (crashWorld w) parent c (crash_parent w c) hchild) hhold' hnote
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
    · by_cases hlive : ((w.st c).life == .alive) = true
      · have hdead : lifeHold ((crashWorld w).st c) = false := by
          simp [lifeHold, (lifeDead c hdec hlive).1]
        simp [hdead] at hhold
      · have hf' : ((w.st c).life == .alive) = false := by
          cases hbit : (w.st c).life == .alive <;> simp_all
        have hhold' : lifeHold (w.st c) = true := by
          simpa [lifeHold, (lifeSame c (Or.inr hf')).1, (hf c).2.1] using hhold
        have hfresh := hH.fresh parent c (by simpa [(hf c).2.2.1] using hc)
          (child_of w (crashWorld w) parent c (crash_parent w c) hchild) hhold' hnote
        cases c with
        | core _ => trivial
        | peer n k g => simpa [slotTombstoneQueued, (hf parent).1] using hfresh
    · have hno : decide (c ∈ w.roster) = false := by
        cases hbit : decide (c ∈ w.roster) <;> simp_all
      have hhold' : lifeHold (w.st c) = true := by
        simpa [lifeHold, (lifeSame c (Or.inl hno)).1, (hf c).2.1] using hhold
      have hfresh := hH.fresh parent c (by simpa [(hf c).2.2.1] using hc)
          (child_of w (crashWorld w) parent c (crash_parent w c) hchild) hhold' hnote
      cases c with
      | core _ => trivial
      | peer n k g => simpa [slotTombstoneQueued, (hf parent).1] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    have hocc (c : InstId) (ho : occupant ((crashWorld w).st c) = true) : occupant (w.st c) = true := by
      by_cases hdec : decide (c ∈ w.roster) = true
      · by_cases hlive : ((w.st c).life == .alive) = true
        · have hdead : occupant ((crashWorld w).st c) = false := by
            simp [occupant, (lifeDead c hdec hlive).1]
          simp [hdead] at ho
        · have hf' : ((w.st c).life == .alive) = false := by
            cases hbit : (w.st c).life == .alive <;> simp_all
          simpa [occupant, (lifeSame c (Or.inr hf')).1] using ho
      · have hno : decide (c ∈ w.roster) = false := by
          cases hbit : decide (c ∈ w.roster) <;> simp_all
        simpa [occupant, (lifeSame c (Or.inl hno)).1] using ho
    exact hH.occ c1 c2 (by simpa [(hf c1).2.2.1] using hc1)
      (by simpa [(hf c2).2.2.1] using hc2) (hocc c1 ho1) (hocc c2 ho2) hslot
      ((crash_parent w c1).symm.trans (hpa.trans (crash_parent w c2)))
  · intro name
    unfold crashWorld
    dsimp
    by_cases hc : decide ((InstId.core name) ∈ w.roster) = true
    · simp only [hc, ite_true, crashActor]
      by_cases hl : (((w.st (.core name)).life == .alive)) = true
      · simpa [hl] using hH.rooted name
      · have hf : (((w.st (.core name)).life == .alive)) = false := by
          cases hbit : ((w.st (.core name)).life == .alive) <;> simp_all
        simpa [hf] using hH.rooted name
    · have hf : decide ((InstId.core name) ∈ w.roster) = false := by
        cases hbit : decide ((InstId.core name) ∈ w.roster) <;> simp_all
      simpa [hf] using hH.rooted name
  · intro parent name
    have hdead : ∀ c, c ∈ (crashWorld w).roster → lifeHold ((crashWorld w).st c) = false := by
      intro c hc
      have hmem : c ∈ w.roster := by simpa [crashWorld] using hc
      cases hlife : (w.st c).life with
      | alive => simp [crashWorld, hmem, crashActor, hlife, lifeHold]
      | dead => simp [crashWorld, hmem, crashActor, hlife, lifeHold]
      | absent => simp [crashWorld, hmem, crashActor, hlife, lifeHold]
    have hfilter : ((crashWorld w).roster.filter (namedChild I.desc (crashWorld w) parent name)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro c hc
      simp [namedChild, childOpen, hdead c hc]
    have hprio : ((crashWorld w).st parent).prio = (w.st parent).prio := by
      simp only [crashWorld]
      by_cases hmem : decide (parent ∈ w.roster) = true
      · simp only [hmem, ite_true, crashActor]
        by_cases hl : ((w.st parent).life == .alive) = true
        · simp [hl]
        · have hf : ((w.st parent).life == .alive) = false := by
            cases hbit : ((w.st parent).life == .alive) <;> simp_all
          simp [hf]
      · have hf : decide (parent ∈ w.roster) = false := by
          cases hbit : decide (parent ∈ w.roster) <;> simp_all
        simp [hf]
    have hN : (crashWorld w).N = w.N := by simp [crashWorld]
    have hle : namedOpen I.desc (crashWorld w) parent name ≤ namedOpen I.desc w parent name := by
      unfold namedOpen
      simp [hfilter, hprio, namedTombs]
    exact Nat.le_trans hle (by simpa [nameBudget, hN] using hH.census parent name)
  · intro id m hm ht
    have hprio : ((crashWorld w).st id).prio = (w.st id).prio := by
      simp only [crashWorld]
      by_cases hmem : decide (id ∈ w.roster) = true
      · simp only [hmem, ite_true, crashActor]
        by_cases hl : ((w.st id).life == .alive) = true
        · simp [hl]
        · have hf : ((w.st id).life == .alive) = false := by
            cases hbit : ((w.st id).life == .alive) <;> simp_all
          simp [hf]
      · have hf : decide (id ∈ w.roster) = false := by
          cases hbit : decide (id ∈ w.roster) <;> simp_all
        simp [hf]
    exact (by simp [crashWorld] : (crashWorld w).roster = w.roster) ▸
      hH.tombHere id m (by simpa [hprio] using hm) ht

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot _hpa
    obtain ⟨_, _, h1, _⟩ := tmb_core_roster I.desc c1 (by simpa [hros] using hc1)
    obtain ⟨_, _, h2, _⟩ := tmb_core_roster I.desc c2 (by simpa [hros] using hc2)
    cases h1
    cases h2
    simp [sameSlot, beq_iff_eq] at hslot
    exact congrArg InstId.core hslot
  · intro name
    rw [hst (.core name)]
    by_cases hc : (coreRoster I.desc).contains (.core name) = true
    · simp only [hc, ite_true]
      obtain ⟨t, ht, hid, _⟩ := tmb_core_roster I.desc (.core name) (List.elem_iff.mp hc)
      have hlook := tmb_template_of_unique I.desc hG t ht
      cases hid
      rw [initActor]
      simp [tname, hlook, withTokens]
    · have hf : (coreRoster I.desc).contains (.core name) = false := by
        cases hbit : (coreRoster I.desc).contains (.core name) <;> simp_all
      have hnin : (.core name) ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [hnin, absentActor]
  · intro parent name
    have hnone : ∀ c, c ∈ coreRoster I.desc → ((initWorld I N).st c).parent = none := by
      intro c hc
      rw [hst c]
      have hbit : (coreRoster I.desc).contains c = true := List.elem_iff.mpr hc
      simp only [hbit, ite_true]
      rw [initActor]
      split
      · simp [withTokens]
      · rfl
    have hfilter : ((initWorld I N).roster.filter (namedChild I.desc (initWorld I N) parent name)) = [] := by
      rw [hros]
      apply List.filter_eq_nil_iff.mpr
      intro c hc
      simp [namedChild, childOpen, isChild, hnone c hc]
    simp [namedOpen, hfilter, hprio parent, namedTombs, tombSlots, nameBudget]
  · intro id m hm _
    have hempty : ((initWorld I N).st id).prio = [] := hprio id
    simp [hempty] at hm

theorem hold_set (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (hl : a.life = (w.st id).life) (hp : a.prio = (w.st id).prio)
    (hpe : a.pendingTombstone = (w.st id).pendingTombstone)
    (hpa : a.parent = (w.st id).parent)
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
  · intro i
    by_cases h : i = id
    · simp [setActor, h, hpa]
    · simp [setActor, h]
  · intro i hi
    by_cases h : i = id
    · have hgoal := hph (by simpa [setActor, h] using hi)
      simpa [setActor, h] using hgoal
    · have heq := setActor_other w id i a h
      simpa [heq] using hH.phase i hi
  · have hc : (setActor w id a).crashed = false := by simpa [setActor] using hpre
    exact hc.trans hpre.symm

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

theorem tombs_append (xs ys : List Msg) :
    tombSlots (xs ++ ys) = tombSlots xs ++ tombSlots ys := by
  induction xs with
  | nil => simp [tombSlots]
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [tmb_tombs_cons, tmb_tombs_cons, ih]
    simp [List.append_assoc]

theorem laneLabels_append (xs ys : List Msg) :
    tmb_laneLabels (xs ++ ys) = tmb_laneLabels xs ++ tmb_laneLabels ys := by
  induction xs with
  | nil => simp [tmb_laneLabels]
  | cons x xs ih =>
    simp only [List.cons_append, tmb_labels_cons, ih]
    cases x.tombstone <;> simp

theorem mem_of_remove {α : Type} (pre suf : List α) (m a : α) (h : a ∈ pre ++ suf) :
    a ∈ pre ++ m :: suf := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem tomb_mem_of_remove (pre suf : List Msg) (m : Msg) (slot : String × Nat)
    (h : slot ∈ tombSlots (pre ++ suf)) :
    slot ∈ tombSlots (pre ++ m :: suf) := by
  rw [tombs_append] at h
  rw [tombs_append]
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · rw [tmb_tombs_cons]
    exact List.mem_append_right _ (List.mem_append_right _ h)

theorem label_mem_of_remove (pre suf : List Msg) (m : Msg) (l : String)
    (h : l ∈ tmb_laneLabels (pre ++ suf)) :
    l ∈ tmb_laneLabels (pre ++ m :: suf) := by
  rw [laneLabels_append] at h
  rw [laneLabels_append]
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · rw [tmb_labels_cons]
    cases hm : m.tombstone with
    | true =>
      exact List.mem_append_right _ h
    | false =>
      exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem namedTombs_remove_le (pre suf : List Msg) (m : Msg) (name : String) :
    (namedTombs (pre ++ suf) name).length ≤ (namedTombs (pre ++ m :: suf) name).length := by
  unfold namedTombs
  rw [tombs_append]
  rw [tombs_append]
  rw [tmb_tombs_cons]
  simp only [List.filter_append, List.length_append]
  omega

/-- Removing one message from a priority lane preserves the lane facts. The
message taken need not be the head: a receive skips a waiting tombstone. -/
theorem lane_of_remove (I : Impl) (template : String) (pre suf : List Msg) (m : Msg)
    (hnd : (tmb_laneLabels (pre ++ m :: suf)).Nodup)
    (hin : ∀ l, l ∈ tmb_laneLabels (pre ++ m :: suf) → l ∈ prioLabels I template)
    (hpeer : ∀ m', m' ∈ pre ++ m :: suf → m'.tombstone = true → ∃ n k g, m'.sender = .peer n k g)
    (htomb : (tombSlots (pre ++ m :: suf)).Nodup) :
    (tmb_laneLabels (pre ++ suf)).Nodup ∧
      (∀ l, l ∈ tmb_laneLabels (pre ++ suf) → l ∈ prioLabels I template) ∧
      (∀ m', m' ∈ pre ++ suf → m'.tombstone = true → ∃ n k g, m'.sender = .peer n k g) ∧
      (tombSlots (pre ++ suf)).Nodup := by
  induction pre with
  | nil =>
    exact lane_of_tail I template m suf hnd hin hpeer htomb
  | cons x xs ih =>
    have htail := lane_of_tail I template x (xs ++ m :: suf) hnd hin hpeer htomb
    have ih' := ih htail.1 htail.2.1 htail.2.2.1 htail.2.2.2
    refine ⟨?nd, ?inn, ?peer, ?tn⟩
    · rw [show (x :: xs) ++ suf = x :: (xs ++ suf) from rfl, tmb_labels_cons]
      cases ht : x.tombstone with
      | true => simpa [ht] using ih'.1
      | false =>
        simp
        refine ⟨?not, ih'.1⟩
        intro hmem
        have hbad : x.label ∈ tmb_laneLabels (xs ++ m :: suf) :=
          label_mem_of_remove xs suf m x.label hmem
        have hnd' : (tmb_laneLabels (x :: (xs ++ m :: suf))).Nodup := by
          simpa [List.cons_append] using hnd
        simp [tmb_labels_cons, ht] at hnd'
        exact hnd'.1 hbad
    · intro l hl
      exact hin l (label_mem_of_remove (x :: xs) suf m l hl)
    · intro m' hm' ht'
      exact hpeer m' (mem_of_remove (x :: xs) suf m m' hm') ht'
    · rw [show (x :: xs) ++ suf = x :: (xs ++ suf) from rfl, tmb_tombs_cons]
      cases ht : x.tombstone with
      | false => simpa [ht] using ih'.2.2.2
      | true =>
        cases hs : x.sender with
        | core _ => simpa [ht, hs] using ih'.2.2.2
        | peer n k g =>
          simp
          refine ⟨?nots, ih'.2.2.2⟩
          intro hmem
          have hbad : (n, k) ∈ tombSlots (xs ++ m :: suf) :=
            tomb_mem_of_remove xs suf m (n, k) hmem
          simp [tmb_tombs_cons, ht, hs] at htomb
          exact htomb.1 hbad

/-- Removing one message from a priority lane preserves the invariant. -/
theorem hold_drop (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (hN : w'.N = w.N) (hros : w'.roster = w.roster)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hpend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone)
    (hhead : ∃ pre m suf, (w.st id).prio = pre ++ m :: suf ∧ (w'.st id).prio = pre ++ suf)
    (hother : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio)
    (hphase : ∀ i, i ∈ w'.roster → phaseDeclared I (tname i) (w'.st i).phase)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hcrash : w'.crashed = false) (hpre : w.crashed = false) : Hold I w' := by
  obtain ⟨pre, m, suf, hcons, hrest⟩ := hhead
  refine ⟨?_, ?_, ?_, ?_, hphase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    exact hros ▸ hH.rostered i (by simpa [hlife i] using hl)
  · intro i hp
    simpa [hlife i] using hH.pend i (by simpa [hpend i] using hp)
  · intro _ i hd
    by_cases h : i = id
    · have hempty := hH.deadPrio hpre id (by simpa [h, hlife id] using hd)
      exfalso
      rw [hcons] at hempty
      exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hempty).2
    · exact hother i h ▸ hH.deadPrio hpre i (by simpa [hlife i] using hd)
  · intro i hid
    exact hH.role i (by simpa [hros] using hid)
  · intro i
    by_cases h : i = id
    · have htail := lane_of_remove I (tname id) pre suf m
        (by simpa [hcons] using (hH.lane id).ordNodup)
        (by simpa [hcons] using (hH.lane id).ordIn)
        (by simpa [hcons] using (hH.lane id).peer)
        (by simpa [hcons] using (hH.lane id).tombNodup)
      exact ⟨by simpa [h, hrest] using htail.1, by simpa [h, hrest] using htail.2.1,
        by simpa [h, hrest] using htail.2.2.1, by simpa [h, hrest] using htail.2.2.2⟩
    · have hold := hH.lane i
      exact ⟨by simpa [hother i h] using hold.ordNodup,
        fun l hl => hold.ordIn l (by simpa [hother i h] using hl),
        fun msg hm ht => hold.peer msg (by simpa [hother i h] using hm) ht,
        by simpa [hother i h] using hold.tombNodup⟩
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c)] using hhold
    have hlegal := hH.legalLife parent c (by simpa [hros] using hc)
      (child_of w w' parent c (hpar c) hchild) hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hN] using hlegal
  · intro parent name k hq
    have hwas : slotTombstoneQueued w parent name k = true := by
      by_cases h : parent = id
      · have hmem : (name, k) ∈ tombSlots (w'.st parent).prio := (tmb_queued_iff w' parent name k).mp hq
        have hsub : (name, k) ∈ tombSlots (w.st parent).prio := by
          rw [h, hcons]
          rw [h, hrest] at hmem
          exact tomb_mem_of_remove pre suf m _ hmem
        exact (tmb_queued_iff w parent name k).mpr hsub
      · have hq' : slotTombstoneQueued w parent name k = true := by
          simpa [slotTombstoneQueued, hother parent h] using hq
        exact hq'
    simpa [hN] using hH.legalTomb parent name k hwas
  · intro parent c hc hchild hhold hnote
    have hhold' : lifeHold (w.st c) = true := by
      simpa [lifeHold_eq (w'.st c) (w.st c) (hlife c)] using hhold
    have hfresh := hH.fresh parent c (by simpa [hros] using hc)
      (child_of w w' parent c (hpar c) hchild) hhold' hnote
    cases c with
    | core _ => trivial
    | peer n k g =>
      by_cases h : parent = id
      · -- not queued on the whole lane, hence not on the tail
        have hnot : slotTombstoneQueued w parent n k = false := by simpa [h] using hfresh
        -- if the tail queued it, the whole lane queued it
        by_cases hq : slotTombstoneQueued w' parent n k = true
        · have hmem : (n, k) ∈ tombSlots (w'.st parent).prio := (tmb_queued_iff w' parent n k).mp hq
          have hwas : (n, k) ∈ tombSlots (w.st parent).prio := by
            rw [h, hcons]
            rw [h, hrest] at hmem
            exact tomb_mem_of_remove pre suf m _ hmem
          have htrue : slotTombstoneQueued w parent n k = true := (tmb_queued_iff w parent n k).mpr hwas
          simp [htrue] at hnot
        · have hf : slotTombstoneQueued w' parent n k = false := by
            cases hbit : slotTombstoneQueued w' parent n k <;> simp_all
          simpa [h] using hf
      · simpa [slotTombstoneQueued, hother parent h] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    have ho1' : occupant (w.st c1) = true := by
      simpa [occupant_eq (w'.st c1) (w.st c1) (hlife c1)] using ho1
    have ho2' : occupant (w.st c2) = true := by
      simpa [occupant_eq (w'.st c2) (w.st c2) (hlife c2)] using ho2
    exact hH.occ c1 c2 (by simpa [hros] using hc1) (by simpa [hros] using hc2) ho1' ho2' hslot
      ((hpar c1).symm.trans (hpa.trans (hpar c2)))
  · intro name
    simpa [hpar] using hH.rooted name
  · intro parent name
    by_cases h : parent = id
    · have hleq : (namedTombs (w'.st parent).prio name).length ≤
          (namedTombs (w.st parent).prio name).length := by
        rw [h, hcons, hrest]
        exact namedTombs_remove_le pre suf m name
      have hsame : ∀ c, c ∈ w.roster →
          namedChild I.desc w' parent name c = namedChild I.desc w parent name c := by
        intro c _
        simp [namedChild, childOpen, isChild, hpar c,
          lifeHold_eq (w'.st c) (w.st c) (hlife c)]
      have hfilter : (w'.roster.filter (namedChild I.desc w' parent name)).length =
          (w.roster.filter (namedChild I.desc w parent name)).length := by
        rw [hros]
        exact congrArg List.length (List.filter_congr hsame)
      have hle : namedOpen I.desc w' parent name ≤ namedOpen I.desc w parent name := by
        unfold namedOpen
        omega
      exact Nat.le_trans hle (by simpa [nameBudget, hN] using hH.census parent name)
    · simpa [namedOpen_cast I.desc w w' parent hros hlife hpend hpar (hother parent h) name,
        nameBudget, hN] using hH.census parent name
  · intro i msg hm ht
    by_cases hi : i = id
    · have hm' : msg ∈ (w'.st id).prio := by simpa [hi] using hm
      have hsub : msg ∈ (w.st id).prio := by
        rw [hcons]
        rw [hrest] at hm'
        exact mem_of_remove pre suf m msg hm'
      exact hros ▸ hH.tombHere id msg hsub ht
    · have hsame := hother i hi
      exact hros ▸ hH.tombHere i msg (by simpa [hsame] using hm) ht

/-- A step that keeps lanes, roster, and population. Life and the tombstone
flag stay as they were, and a phase is either untouched or idle. Every life
that still holds a slot already held it. -/
theorem filter_len_mono {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · have hq : q x = true := h x List.mem_cons_self hp
      simp only [hp, hq, ite_true, List.length_cons]
      exact Nat.succ_le_succ (ih fun y hy => h y (List.mem_cons_of_mem x hy))
    · have hf : p x = false := by
        cases hbit : p x <;> simp_all
      simp only [hf, ite_false]
      by_cases hq : q x = true
      · simp only [hq, ite_true, List.length_cons]
        exact Nat.le_succ_of_le (ih fun y hy => h y (List.mem_cons_of_mem x hy))
      · have hqf : q x = false := by
          cases hbit : q x <;> simp_all
        simp only [hqf, ite_false]
        exact ih fun y hy => h y (List.mem_cons_of_mem x hy)

theorem filter_drop_mem {α : Type} [DecidableEq α] (p q : α → Bool) (xs : List α) (a : α)
    (hmem : a ∈ xs.filter p) (hq : q a = false)
    (hagree : ∀ x, x ∈ xs → x ≠ a → q x = p x) :
    (xs.filter q).length + 1 ≤ (xs.filter p).length := by
  induction xs with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.filter_cons] at hmem ⊢
    by_cases hpx : p x = true
    · simp only [hpx, ite_true] at hmem ⊢
      rw [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        have hxa : x = a := heq.symm
        have hqx : q x = false := hxa ▸ hq
        have hcond : ¬ q x = true := by simpa [hqx]
        simp [hcond, List.length_cons]
        have htail : (xs.filter q).length ≤ (xs.filter p).length :=
          filter_len_mono q p xs fun y hy hqy => by
            by_cases hya : y = a
            · rw [hya] at hqy
              simp [hq] at hqy
            · have hqp := hagree y (List.mem_cons_of_mem x hy) hya
              simpa [hqp] using hqy
        omega
      | inr htail =>
        by_cases hxa : x = a
        · have hqx : q x = false := hxa ▸ hq
          simp only [hqx, ite_false]
          exact Nat.le_trans (ih htail fun y hy hne => hagree y (List.mem_cons_of_mem x hy) hne)
            (Nat.le_succ _)
        · have hqx : q x = true := by simpa [hagree x List.mem_cons_self hxa] using hpx
          simp only [hqx, ite_true, List.length_cons]
          exact Nat.succ_le_succ (ih htail fun y hy hne => hagree y (List.mem_cons_of_mem x hy) hne)
    · have hpf : p x = false := by
        cases hbit : p x <;> simp_all
      simp only [hpf, ite_false] at hmem ⊢
      by_cases hxa : x = a
      · have hqx : q x = false := hxa ▸ hq
        simp only [hqx, ite_false]
        exact ih hmem fun y hy hne => hagree y (List.mem_cons_of_mem x hy) hne
      · have hqx : q x = false := by simpa [hagree x List.mem_cons_self hxa] using hpf
        simp only [hqx, ite_false]
        exact ih hmem fun y hy hne => hagree y (List.mem_cons_of_mem x hy) hne

structure Marked (w w' : World) : Prop where
  N : w'.N = w.N
  roster : w'.roster = w.roster
  crashed : w'.crashed = w.crashed
  prio : ∀ i, (w'.st i).prio = (w.st i).prio
  life : ∀ i, (w'.st i).life = (w.st i).life
  pend : ∀ i, (w'.st i).pendingTombstone = (w.st i).pendingTombstone
  phase : ∀ i, (w'.st i).phase = (w.st i).phase ∨ (w'.st i).phase = .idle
  held : ∀ i, lifeHold (w'.st i) = true → lifeHold (w.st i) = true
  par : ∀ i, (w'.st i).parent = (w.st i).parent

theorem Marked.refl (w : World) : Marked w w :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => Or.inl rfl,
    fun _ h => h, fun _ => rfl⟩

theorem alive_hold (a : Actor) (h : a.life = .alive) : lifeHold a = true := by
  simp [lifeHold, h]

theorem Marked.trans {w w1 w' : World} (h1 : Marked w w1) (h2 : Marked w1 w') : Marked w w' := by
  refine ⟨h2.N.trans h1.N, h2.roster.trans h1.roster, h2.crashed.trans h1.crashed, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (h2.prio i).trans (h1.prio i)
  · intro i
    exact (h2.life i).trans (h1.life i)
  · intro i
    exact (h2.pend i).trans (h1.pend i)
  · intro i
    cases h2.phase i with
    | inl heq =>
      cases h1.phase i with
      | inl h0 => exact Or.inl (heq.trans h0)
      | inr hidle => exact Or.inr (heq ▸ hidle)
    | inr hidle => exact Or.inr hidle
  · intro i hh
    exact h1.held i (h2.held i hh)
  · intro i
    exact (h2.par i).trans (h1.par i)

theorem hold_marked (I : Impl) (w w' : World) (hH : Hold I w) (hM : Marked w w')
    (hpre : w.crashed = false) : Hold I w' := by
  have hcrash : w'.crashed = false := by simpa [hM.crashed] using hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hl
    exact hM.roster ▸ hH.rostered id (by simpa [hM.life id] using hl)
  · intro id hp
    simpa [hM.life id] using hH.pend id (by simpa [hM.pend id] using hp)
  · intro _ id hd
    exact hM.prio id ▸ hH.deadPrio hpre id (by simpa [hM.life id] using hd)
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
    have hlegal := hH.legalLife parent c (by simpa [hM.roster] using hc)
      (child_of w w' parent c (hM.par c) hchild) hwas hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [hM.N] using hlegal
  · intro parent name k hq
    have hq' : slotTombstoneQueued w parent name k = true := by
      simpa [slotTombstoneQueued, hM.prio parent] using hq
    simpa [hM.N] using hH.legalTomb parent name k hq'
  · intro parent c hc hchild hhold hnote
    have hwas := hM.held c hhold
    have hfresh := hH.fresh parent c (by simpa [hM.roster] using hc)
      (child_of w w' parent c (hM.par c) hchild) hwas hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [slotTombstoneQueued, hM.prio parent] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    have hold (c : InstId) (ho : occupant (w'.st c) = true) : occupant (w.st c) = true := by
      simpa [occupant, hM.life c] using ho
    exact hH.occ c1 c2 (by simpa [hM.roster] using hc1) (by simpa [hM.roster] using hc2)
      (hold c1 ho1) (hold c2 ho2) hslot
      ((hM.par c1).symm.trans (hpa.trans (hM.par c2)))
  · intro name
    simpa [hM.par] using hH.rooted name
  · intro parent name
    have hpred : ∀ c, c ∈ w'.roster → namedChild I.desc w' parent name c = true →
        namedChild I.desc w parent name c = true := by
      intro c hc ho
      cases c with
      | core _ =>
        simp [namedChild] at ho
      | peer n k g =>
        simp [namedChild, childOpen] at ho
        have hname := ho.2
        subst hname
        have hlife := hM.held (.peer n k g) ho.1.1.2
        have hchild : isChild w parent (.peer n k g) = true := by
          simpa [isChild_eq w w' parent (.peer n k g) (hM.par _)] using ho.1.1.1
        simp [namedChild, childOpen, hchild, hlife, ho.1.2]
    have hfilter : (w'.roster.filter (namedChild I.desc w' parent name)).length ≤
        (w.roster.filter (namedChild I.desc w parent name)).length := by
      rw [hM.roster]
      exact filter_len_mono _ _ _ (fun c hc ho => hpred c (by simpa [hM.roster] using hc) ho)
    have hle : namedOpen I.desc w' parent name ≤ namedOpen I.desc w parent name := by
      unfold namedOpen
      have htombs : (namedTombs (w'.st parent).prio name).length =
          (namedTombs (w.st parent).prio name).length := by
        simp [namedTombs, hM.prio parent]
      omega
    exact Nat.le_trans hle (by simpa [nameBudget, hM.N] using hH.census parent name)
  · intro id m hm ht
    exact hM.roster ▸ hH.tombHere id m (by simpa [hM.prio id] using hm) ht

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

theorem tmb_snoc_parent (w : World) (parent : InstId) (msg : Msg) (i : InstId) :
    ((tmb_snoc w parent msg).st i).parent = (w.st i).parent := by
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

theorem tombs_append_one (ms : List Msg) (msg : Msg) (name : String) (k g : Nat)
    (ht : msg.tombstone = true) (hs : msg.sender = .peer name k g) :
    (tombSlots (ms ++ [msg])).length = (tombSlots ms).length + 1 := by
  simp [tombSlots, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, ht, hs]

theorem openCount_snoc (D : Description) (w : World) (parent : InstId) (msg : Msg)
    (name : String) (k g : Nat) (ht : msg.tombstone = true) (hs : msg.sender = .peer name k g) :
    openCount D (tmb_snoc w parent msg) parent = openCount D w parent + 1 := by
  have hpred : ∀ c, childOpen D (tmb_snoc w parent msg) parent c = childOpen D w parent c := by
    intro c
    simp [childOpen, lifeHold, isChild, tmb_snoc_life w parent msg c,
      tmb_snoc_pend w parent msg c, tmb_snoc_parent w parent msg c]
  have hfilter : ((tmb_snoc w parent msg).roster.filter
      (childOpen D (tmb_snoc w parent msg) parent)).length =
      (w.roster.filter (childOpen D w parent)).length := by
    rw [tmb_snoc_roster]
    apply congrArg List.length
    apply List.filter_congr
    intro c _
    exact hpred c
  have htombs : (tombSlots ((tmb_snoc w parent msg).st parent).prio).length =
      (tombSlots (w.st parent).prio).length + 1 := by
    rw [tmb_snoc_prio_self]
    exact tombs_append_one _ _ name k g ht hs
  unfold openCount
  omega

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
      a1.parent = a.parent ∧
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
      exact ⟨rfl, rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
        congrArg Actor.pendingTombstone (hst i)⟩, cellsRoster I.desc w id, cellsN I.desc w id,
        cellsCrash I.desc w id, hst⟩
    · split at h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
            congrArg Actor.pendingTombstone (hst i)⟩, cellsRoster I.desc w id, cellsN I.desc w id,
            cellsCrash I.desc w id, hst⟩
      · split at h
        · cases h
        · cases h
          split <;> exact ⟨rfl, rfl, rfl, rfl, fun i => ⟨congrArg Actor.life (hst i), congrArg Actor.prio (hst i),
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
  obtain ⟨m, pre, suf, w1, a1, _, _, hprio, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  rcases deliver_frame I w id { (w.st id) with prio := pre ++ suf } m w1 a1 hdel with
    ⟨hlife, hprioA, hpendA, hparA, hworld, hros, hN, hcrash, hst⟩
  have hdec := deliver_declared I w id { (w.st id) with prio := pre ++ suf } m w1 a1 hdel
  have hHold : Hold I (setActor w1 id a1) := by
    apply hold_drop I w (setActor w1 id a1) hH id
    · simp [setActor, hN]
    · simp [setActor, hros]
    · intro i
      by_cases hi : i = id
      · rw [hi]
        simpa [setActor] using hlife
      · simpa [setActor, hi] using (hworld i).1
    · intro i
      by_cases hi : i = id
      · rw [hi]
        simpa [setActor] using hpendA
      · simpa [setActor, hi] using (hworld i).2.2
    · exact ⟨pre, m, suf, hprio, by simp [setActor, hprioA]⟩
    · intro i hi
      simpa [setActor, hi] using (hworld i).2.1
    · intro i hi
      by_cases heq : i = id
      · simpa [setActor, heq] using hdec
      · have hphaseEq : (w1.st i).phase = (w.st i).phase := congrArg Actor.phase (hst i)
        have hmem : i ∈ w.roster := by simpa [setActor, hros] using hi
        simpa [setActor, heq, hphaseEq] using hH.phase i hmem
    · intro i
      by_cases heq : i = id
      · simp [setActor, heq]
        exact hparA
      · simpa [setActor, heq] using congrArg Actor.parent (hst i)
    · simpa [setActor, hcrash] using hpre
    · exact hpre
  simpa [hw'] using hHold

theorem hold_same (I : Impl) (w w' : World) (hH : Hold I w)
    (hst : ∀ i, w'.st i = w.st i) (hros : w'.roster = w.roster) (hN : w'.N = w.N)
    (hcrash : w'.crashed = false) (hpre : w.crashed = false) : Hold I w' := by
  apply hold_actors I w w' hH hN hros
  · intro i; exact congrArg Actor.life (hst i)
  · intro i; exact congrArg Actor.prio (hst i)
  · intro i; exact congrArg Actor.pendingTombstone (hst i)
  · intro i; exact congrArg Actor.parent (hst i)
  · intro i hi
    exact (congrArg Actor.phase (hst i)).symm ▸ hH.phase i (by simpa [hros] using hi)
  · exact hcrash.trans hpre.symm

theorem hold_credit (I : Impl) (w : World) (hH : Hold I w) (name : String) (sender : InstId)
    (hpre : w.crashed = false) : Hold I (creditSender w name sender) := by
  apply hold_actors I w (creditSender w name sender) hH rfl rfl
  · intro i; exact (credit_fields w name sender i).2.1
  · intro i; exact (credit_fields w name sender i).2.2.2.2
  · intro i; exact credit_pending w name sender i
  · intro i; exact credit_parent w name sender i
  · intro i hi
    exact (credit_fields w name sender i).1 ▸ hH.phase i hi
  · have hc : (creditSender w name sender).crashed = false := by
      simpa [creditSender, setActor] using hpre
    exact hc.trans hpre.symm

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
    (hapa : a.parent = (w.st id).parent)
    (hpre : w.crashed = false) : Hold I (setActor w1 id a1) := by
  rcases deliver_frame I w id a m w1 a1 hdel with
    ⟨hlife, hprioA, hpendA, hparA, _, hros, hN, hcrash, hst⟩
  have hdec := deliver_declared I w id a m w1 a1 hdel
  have hW := hold_same I w w1 hH hst hros hN (hcrash.symm ▸ hpre) hpre
  apply hold_set I w1 hW id a1
  · exact (hlife.trans hl).trans (congrArg Actor.life (hst id)).symm
  · exact (hprioA.trans hp).trans (congrArg Actor.prio (hst id)).symm
  · exact (hpendA.trans hpe).trans (congrArg Actor.pendingTombstone (hst id)).symm
  · exact hparA.trans (hapa.trans (congrArg Actor.parent (hst id)).symm)
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
            ⟨_, _, _, _, _, hros, _, hcrash, hst⟩
          have hH1 := hold_install I w hH id _ p.msg w1 a1 hdel rfl rfl rfl rfl hpre
          have hpre1 : (setActor w1 id a1).crashed = false := by
            simpa [setActor, hcrash] using hpre
          have hH2 := hold_credit I (setActor w1 id a1) hH1 (tname id)
            (budgetHolder (setActor w1 id a1) p.msg.sender) hpre1
          let credited := creditSender (setActor w1 id a1) (tname id)
            (budgetHolder (setActor w1 id a1) p.msg.sender)
          apply hold_set I credited hH2 p.sender
            (resumeSender (credited.st p.sender) p.isCall id)
            (resumeSender_keep _ _ _).1 (resumeSender_prio _ _ _) (resumeSender_keep _ _ _).2
          · cases hph : (credited.st p.sender).phase with
            | parked _ _ k =>
              cases p.isCall <;> cases hk : k.rest <;>
                simp [resumeSender, proceed, hph, hk]
            | idle => simp [resumeSender, hph]
            | run _ => simp [resumeSender, hph]
            | awaitReply _ _ => simp [resumeSender, hph]
            | awaitEffect _ => simp [resumeSender, hph]
            | awaitPeer _ => simp [resumeSender, hph]
            | crashed => simp [resumeSender, hph]
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
          rcases deliver_frame I w id _ m w1 a1 hdel with ⟨_, _, _, _, _, _, _, hcrash, _⟩
          have hH1 := hold_install I w hH id _ m w1 a1 hdel rfl rfl rfl rfl hpre
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
            ⟨_, _, _, _, _, hros, _, hcrash, hst⟩
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hH1 := hold_install I w hH id _ m w1 a1 hdel rfl rfl rfl rfl hpre
          have hpre1 : (setActor w1 id a1).crashed = false := by
            simpa [setActor, hcrash] using hpre
          have hHad : Hold I (setActor w1 id admitted) := by
            have htwice := by
              apply hold_set I (setActor w1 id a1) hH1 id admitted
              · simp [admitted, setActor]
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
          · cases hph : (credited.st p.sender).phase with
            | parked _ _ k =>
              cases p.isCall <;> cases hk : k.rest <;>
                simp [resumeSender, proceed, hph, hk]
            | idle => simp [resumeSender, hph]
            | run _ => simp [resumeSender, hph]
            | awaitReply _ _ => simp [resumeSender, hph]
            | awaitEffect _ => simp [resumeSender, hph]
            | awaitPeer _ => simp [resumeSender, hph]
            | crashed => simp [resumeSender, hph]
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
    (hlive : (w.st id).life = .alive) :
    Hold I (setActor w id (tmb_dead (w.st id))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    by_cases hi : i = id
    · have hne : (w.st id).life ≠ .absent := by
        rw [hlive]
        intro hbad
        cases hbad
      simpa [setActor, hi] using hH.rostered id hne
    · exact hH.rostered i (by simpa [setActor, hi] using hl)
  · intro i hp
    by_cases hi : i = id
    · exact (by simp [setActor, hi, tmb_dead])
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
      have hlegal := hH.legalLife parent c (by simpa [setActor] using hc)
        (child_of w (setActor w id (tmb_dead (w.st id))) parent c
          (by by_cases h : c = id <;> simp [setActor, tmb_dead, h]) hchild) hwas hnote
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
      have hfresh := hH.fresh parent c (by simpa [setActor] using hc)
        (child_of w (setActor w id (tmb_dead (w.st id))) parent c
          (by by_cases h : c = id <;> simp [setActor, tmb_dead, h]) hchild) hwas hnote
      by_cases hp : parent = id
      · cases c with
        | core _ => trivial
        | peer _ _ _ => simp [setActor, hp, tmb_dead, slotTombstoneQueued]
      · cases c with
        | core _ => trivial
        | peer n k g =>
          simpa [slotTombstoneQueued, setActor, hp, tmb_dead] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    have hold (c : InstId)
        (ho : occupant ((setActor w id (tmb_dead (w.st id))).st c) = true) :
        occupant (w.st c) = true := by
      by_cases hc : c = id
      · simp [setActor, hc, tmb_dead, occupant] at ho
      · simpa [occupant, setActor, hc, tmb_dead] using ho
    have hpar (c : InstId) :
        ((setActor w id (tmb_dead (w.st id))).st c).parent = (w.st c).parent := by
      by_cases hc : c = id <;> simp [setActor, tmb_dead, hc]
    exact hH.occ c1 c2 (by simpa [setActor] using hc1) (by simpa [setActor] using hc2)
      (hold c1 ho1) (hold c2 ho2) hslot
      ((hpar c1).symm.trans (hpa.trans (hpar c2)))
  · intro name
    by_cases hi : InstId.core name = id
    · simpa [setActor, hi, tmb_dead] using hH.rooted name
    · simpa [setActor, hi] using hH.rooted name
  · intro parent name
    let w' := setActor w id (tmb_dead (w.st id))
    have hpred : ∀ c, c ∈ w.roster → namedChild I.desc w' parent name c = true →
        namedChild I.desc w parent name c = true := by
      intro c _ ho
      by_cases hc : c = id
      · simp [w', namedChild, childOpen, lifeHold, setActor, hc, tmb_dead] at ho
      · simpa [w', namedChild, childOpen, lifeHold, isChild, setActor, hc, tmb_dead] using ho
    have hfilter : (w'.roster.filter (namedChild I.desc w' parent name)).length ≤
        (w.roster.filter (namedChild I.desc w parent name)).length := by
      have hros : w'.roster = w.roster := by simp [w', setActor]
      rw [hros]
      exact filter_len_mono _ _ _ hpred
    have htombs : (namedTombs (w'.st parent).prio name).length ≤
        (namedTombs (w.st parent).prio name).length := by
      by_cases hp : parent = id
      · simp [w', hp, setActor, tmb_dead, namedTombs, tombSlots]
      · simp [w', hp, setActor, namedTombs]
    have hle : namedOpen I.desc w' parent name ≤ namedOpen I.desc w parent name := by
      unfold namedOpen
      omega
    simpa [w', setActor, nameBudget] using Nat.le_trans hle (hH.census parent name)
  · intro i m hm ht
    by_cases hi : i = id
    · simp [setActor, hi, tmb_dead] at hm
    · have hsame : ((setActor w id (tmb_dead (w.st id))).st i).prio = (w.st i).prio := by
        simp [setActor, hi]
      exact (by simp [setActor] : (setActor w id (tmb_dead (w.st id))).roster = w.roster) ▸
        hH.tombHere i m (by simpa [hsame] using hm) ht

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
  · intro i; exact releaseOutbound_parent w dead i
  · intro i hi
    exact (release_extra w dead i).1 ▸ hH.phase i (by
      simpa [(releaseOutbound_keep w dead i).2.2] using hi)
  · have hc : (releaseOutbound w dead).crashed = false :=
      (release_extra w dead dead).2.symm ▸ hpre
    exact hc.trans hpre.symm

theorem hold_resume (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (p : Parked)
    (hpre : w.crashed = false) : Hold I (tmb_resumeOne id w p) := by
  unfold tmb_resumeOne
  split
  · exact hH
  · apply hold_set I w hH p.sender (resumeSender (w.st p.sender) false id)
      (resumeSender_keep _ _ _).1 (resumeSender_prio _ _ _) (resumeSender_keep _ _ _).2
    · cases hph : (w.st p.sender).phase with
      | parked _ _ k =>
        simp [resumeSender, hph]
        cases hk : k.rest <;> simp [proceed, hk]
      | idle => simp [resumeSender, hph]
      | run _ => simp [resumeSender, hph]
      | awaitReply _ _ => simp [resumeSender, hph]
      | awaitEffect _ => simp [resumeSender, hph]
      | awaitPeer _ => simp [resumeSender, hph]
      | crashed => simp [resumeSender, hph]
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
    (hlive : (w.st id).life = .alive) :
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
  have hkill := hold_kill I (releaseOutbound w3 id) hW4 id hpre4 (hlife4.symm ▸ hlive)
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
    (hlegal : slotIndexed I.desc parent name = true → (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : slotTombstoneQueued w parent name k = false)
    (hnone : ∀ c, c ∈ w.roster → isChild w parent c = true →
      lifeHold (w.st c) = true → notifies I.desc c = true →
      match c with
      | .peer n key _ => ¬(n = name ∧ key = k)
      | .core _ => True)
    (hslack : ∀ nm, namedOpen I.desc (tmb_snoc w parent msg) parent nm ≤
      nameBudget I.desc parent w.N nm)
    (hsend : msg.sender ∈ w.roster) : Hold I (tmb_snoc w parent msg) := by
  let w' := tmb_snoc w parent msg
  have hlife := tmb_snoc_life w parent msg
  have hpend := tmb_snoc_pend w parent msg
  have hphase := tmb_snoc_phase w parent msg
  have hros := tmb_snoc_roster w parent msg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have hlegal' := hH.legalLife p c (by simpa [w', hros] using hc)
      (child_of w (tmb_snoc w parent msg) p c (tmb_snoc_parent w parent msg c) hchild) hwas hnote
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
        have hchildP : isChild (tmb_snoc w parent msg) parent (InstId.peer n key gen) = true := by
          simpa [hp] using hchild
        have hfresh := hH.fresh parent (InstId.peer n key gen)
          (by simpa [w', hros] using hc)
          (child_of w (tmb_snoc w parent msg) parent (InstId.peer n key gen)
            (tmb_snoc_parent w parent msg (InstId.peer n key gen)) hchildP)
          hwas hnote
        unfold slotTombstoneQueued at hfresh
        have hfresh' : (w.st parent).prio.any (tmb_hit n key) = false :=
          (tmb_any_hit (w.st parent).prio n key).symm ▸ hfresh
        by_cases hslot : n = name ∧ key = k
        · exact absurd hslot (hnone (InstId.peer n key gen)
            (by simpa [w', hros] using hc)
            (child_of w (tmb_snoc w parent msg) parent (InstId.peer n key gen)
              (tmb_snoc_parent w parent msg (InstId.peer n key gen)) hchildP)
            hwas hnote)
        · rw [hp, tmb_queued_self, tmb_any_snoc, hfresh', Bool.false_or]
          simp only [tmb_hit, ht, hs]
          cases hdec : (name == n) <;> cases hkey : (k == key) <;> simp [hdec, hkey]
          have hn : name = n := by simpa [beq_iff_eq] using hdec
          have hk : k = key := by simpa [beq_iff_eq] using hkey
          exact absurd (And.intro hn hk)
            (fun h : name = n ∧ k = key => hslot (And.intro h.1.symm h.2.symm))
    · have hfresh := hH.fresh p c (by simpa [w', hros] using hc)
        (child_of w (tmb_snoc w parent msg) p c (tmb_snoc_parent w parent msg c) hchild) hwas hnote
      cases c with
      | core _ => trivial
      | peer n key _ =>
        dsimp
        rw [tmb_queued_other w parent msg p n key hp]
        simpa [slotTombstoneQueued] using hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    exact hH.occ c1 c2 (by simpa [w', hros] using hc1) (by simpa [w', hros] using hc2)
      (by simpa [occupant, w', hlife] using ho1) (by simpa [occupant, w', hlife] using ho2) hslot
      ((tmb_snoc_parent w parent msg c1).symm.trans
        (hpa.trans (tmb_snoc_parent w parent msg c2)))
  · intro name
    simpa [w', tmb_snoc_parent w parent msg] using hH.rooted name
  · intro p nm
    by_cases hp : p = parent
    · subst hp
      simpa [w', tmb_snoc_N, nameBudget] using hslack nm
    · have hprio := tmb_snoc_prio_other w parent msg p hp
      simpa [w', namedOpen_cast I.desc w w' p hros hlife hpend (tmb_snoc_parent w parent msg) hprio nm,
        tmb_snoc_N, nameBudget] using hH.census p nm
  · intro i m hm htomb
    by_cases hi : i = parent
    · have hprio := tmb_snoc_prio_self w parent msg
      have hm' : m ∈ (w.st parent).prio ++ [msg] := by simpa [w', hi, hprio] using hm
      simp [List.mem_append] at hm'
      cases hm' with
      | inl hold => exact hros ▸ hH.tombHere parent m hold htomb
      | inr hnew =>
        rw [hnew]
        exact hros ▸ hsend
    · have hprio := tmb_snoc_prio_other w parent msg i hi
      exact hros ▸ hH.tombHere i m (by simpa [w', hprio] using hm) htomb

theorem hold_offer (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (msg : Msg) (name : String) (k g : Nat) (hpre : w.crashed = false)
    (halive : (w.st parent).life = .alive) (ht : msg.tombstone = true)
    (hs : msg.sender = .peer name k g)
    (hlegal : slotIndexed I.desc parent name = true → (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : slotTombstoneQueued w parent name k = false)
    (hnone : ∀ c, c ∈ w.roster → isChild w parent c = true →
      lifeHold (w.st c) = true → notifies I.desc c = true →
      match c with
      | .peer n key _ => ¬(n = name ∧ key = k)
      | .core _ => True)
    (hslack : ∀ nm, namedOpen I.desc (tmb_snoc w parent msg) parent nm ≤
      nameBudget I.desc parent w.N nm)
    (hsend : msg.sender ∈ w.roster) : Hold I (offerPrio I.desc w parent msg) := by
  by_cases hfull : prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent
  · have hdec : decide (prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent) = true := by
      simp [hfull]
    simp only [offerPrio, hdec]
    exact hold_crash I w hH
  · have hdec : decide (prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent) = false :=
      decide_eq_false hfull
    simp only [offerPrio, hdec, tmb_snoc]
    exact hold_snoc I w hH parent msg name k g hpre halive ht hs hlegal hfree hnone hslack hsend

theorem hold_enqueue (I : Impl) (w : World) (hH : Hold I w) (child : InstId)
    (name : String) (k g : Nat) (hpre : w.crashed = false)
    (hchild : child = .peer name k g)
    (hmem : child ∈ w.roster)
    (hlegal : ∀ parent, liveSupervisor I.desc w child = some parent →
      slotIndexed I.desc parent name = true → (name, k) ∈ legalSlots I.desc parent w.N)
    (hfree : ∀ parent, liveSupervisor I.desc w child = some parent →
      slotTombstoneQueued w parent name k = false)
    (hnone : ∀ parent, liveSupervisor I.desc w child = some parent →
      ∀ c, c ∈ w.roster → isChild w parent c = true →
        lifeHold (w.st c) = true → notifies I.desc c = true →
        match c with
        | .peer n key _ => ¬(n = name ∧ key = k)
        | .core _ => True)
    (hslack : ∀ parent, liveSupervisor I.desc w child = some parent →
      ∀ nm, namedOpen I.desc (tmb_snoc w parent (tombstoneMsg I.desc (w.st parent) child)) parent nm ≤
        nameBudget I.desc parent w.N nm) : Hold I (enqueueTombstone I.desc w child) := by
  unfold enqueueTombstone
  cases hparent : (w.st child).parent with
  | none =>
    simp only [hparent]
    exact hH
  | some parent =>
    simp only [hparent]
    by_cases halive : (w.st parent).life = .alive
    · have hbit : ((w.st parent).life == .alive) = true := by simpa [beq_iff_eq] using halive
      have hdrop : ((w.st parent).life != .alive) = false := by simpa [bne, hbit]
      simp only [hdrop, ite_false]
      by_cases hlab : (tombstoneMsg I.desc (w.st parent) child).label = ""
      · have hbit2 : ((tombstoneMsg I.desc (w.st parent) child).label == "") = true := by
          simpa [beq_iff_eq] using hlab
        simp only [hbit2, ite_true]
        exact hold_crash I w hH
      · have hbit2 : ((tombstoneMsg I.desc (w.st parent) child).label == "") = false := by
          simpa [beq_iff_eq] using hlab
        simp only [hbit2, ite_false]
        let msg := tombstoneMsg I.desc (w.st parent) child
        have hsup : liveSupervisor I.desc w child = some parent := by
          unfold liveSupervisor
          simp [hparent, hbit]
        have ht : msg.tombstone = true := by simp [msg, tombstoneMsg]
        have hs : msg.sender = .peer name k g := by simp [msg, tombstoneMsg, hchild]
        exact hold_offer I w hH parent msg name k g hpre halive ht hs
          (hlegal parent hsup) (hfree parent hsup) (hnone parent hsup) (hslack parent hsup)
          (by simpa [hs, hchild] using hmem)
    · have hbit : ((w.st parent).life == .alive) = false := by simpa [beq_iff_eq] using halive
      have hdrop : ((w.st parent).life != .alive) = true := by simpa [bne, hbit]
      simp only [hdrop, ite_true]
      exact hH

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
    (hpre : w.crashed = false) (halive : (w.st id).life = .alive) :
    Hold I (sealActor I.desc w id (w.st id)) := by
  have hrel := hold_release I w hH id (w.st id) hpre halive
  unfold sealActor
  let sealed := releaseWorld I.desc w id (w.st id)
  have hpreS : sealed.crashed = false := (release_crash I.desc w id (w.st id)).symm ▸ hpre
  have hmem : id ∈ w.roster := hH.rostered id (by simp [halive])
  cases hsup : liveSupervisor I.desc sealed id with
  | none =>
    have hdrop : enqueueTombstone I.desc sealed id = sealed := by
      unfold liveSupervisor at hsup
      unfold enqueueTombstone
      cases hparent : (sealed.st id).parent with
      | none => simp [hparent]
      | some p =>
        simp only [hparent] at hsup ⊢
        by_cases haliveP : (sealed.st p).life = .alive
        · have hbit : ((sealed.st p).life == .alive) = true := by
            simpa [beq_iff_eq] using haliveP
          simp [hbit] at hsup
        · have hbit : ((sealed.st p).life == .alive) = false := by
            simpa [beq_iff_eq] using haliveP
          have hneq : ((sealed.st p).life != .alive) = true := by simpa [bne, hbit]
          simp [hneq]
    exact hdrop.symm ▸ hrel
  | some parent =>
    by_cases hnote : notifies I.desc id = true
    · have hros := release_roster I.desc w id (w.st id)
      have hmemS : id ∈ sealed.roster := by simpa [sealed, hros] using hmem
      have hrole := hrel.role id hmemS
      have hneId : id ≠ parent := by
        intro heq
        have hdead := releaseWorld_self_dead I.desc w id (w.st id)
        have halive := (tmb_parent_alive I.desc sealed id parent hsup).2
        have hdead' : ((releaseWorld I.desc w id (w.st id)).st parent).life = .dead := by
          simpa [heq] using hdead
        have hbad := hdead'.symm.trans halive
        cases hbad
      have hroot : ∀ name, (sealed.st (InstId.core name)).parent = none := by
        intro name
        have hpar := release_parent I.desc w id (w.st id) (InstId.core name)
        simpa [sealed, hpar] using hH.rooted name
      have hpeer := tmb_live_peer I.desc sealed id parent hroot hneId hsup
      obtain ⟨childName, k, g, hid, hchild⟩ := hpeer
      have hchildW : isChild w parent id = true := by
        have hpar := release_parent I.desc w id (w.st id) id
        simpa [isChild_eq w sealed parent id hpar] using hchild
      have hne : parent ≠ id := hneId.symm
      have hprio := releaseWorld_prio I.desc w id (w.st id) parent hne
      have hwas : lifeHold (w.st id) = true := by simp [lifeHold, halive]
      apply hold_enqueue I sealed hrel id childName k g hpreS hid hmemS
      · intro p hp
        simp only [hsup] at hp
        injection hp with hp'
        have hleg := hH.legalLife parent id hmem hchildW hwas hnote
        simpa [sealed, hid, hp', ← hprio.2] using hleg
      · intro p hp
        simp only [hsup] at hp
        injection hp with hp'
        have hfresh := hH.fresh parent id hmem hchildW hwas hnote
        dsimp only [sealed] at hfresh ⊢
        simp only [slotTombstoneQueued] at hfresh ⊢
        rw [← hp', hprio.1]
        simp only [hid] at hfresh
        exact hfresh
      · intro p hp c hc hchildC hhold hnote'
        simp only [hsup] at hp
        injection hp with hp'
        cases c with
        | core _ => trivial
        | peer cn ck cg =>
          intro hslot
          have hchildC : isChild sealed parent (InstId.peer cn ck cg) = true := by
            simpa [hp'] using hchildC
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
            have hparC := release_parent I.desc w id (w.st id) (InstId.peer cn ck cg)
            have hchild0 : isChild w parent (InstId.peer cn ck cg) = true := by
              exact child_of w sealed parent (InstId.peer cn ck cg) hparC hchildC
            have hsame : sameSlot id (InstId.peer cn ck cg) = true := by
              simp [hid, sameSlot, hslot, beq_iff_eq]
            have hparents : (w.st id).parent = (w.st (InstId.peer cn ck cg)).parent := by
              rw [isChild_parent w parent id hchildW,
                isChild_parent w parent (InstId.peer cn ck cg) hchild0]
            have hidc := hH.occ id (InstId.peer cn ck cg) hmem
              (by simpa [sealed, hros] using hc)
              (by simp [occupant, halive])
              (by simpa [occupant, lifeHold] using hhold0)
              hsame hparents
            exact hc_id hidc.symm
      · intro p hp nm
        simp only [hsup] at hp
        injection hp with hp'
        subst hp'
        have ht : (tombstoneMsg I.desc (sealed.st parent) id).tombstone = true := by
          simp [tombstoneMsg]
        have hs : (tombstoneMsg I.desc (sealed.st parent) id).sender = .peer childName k g := by
          simp [tombstoneMsg, hid]
        have hN : sealed.N = w.N := hprio.2
        have hpPrio : (sealed.st parent).prio = (w.st parent).prio := by
          simpa [sealed] using hprio.1
        have hros' : sealed.roster = w.roster := release_roster I.desc w id (w.st id)
        by_cases hnm : nm = childName
        · subst hnm
          have hmemF : id ∈ w.roster.filter (namedChild I.desc w parent nm) := by
            refine List.mem_filter.mpr ⟨hmem, ?_⟩
            simp [namedChild, childOpen, hid]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · simpa [hid] using hchildW
            · simpa [hid] using hwas
            · simpa [hid] using hnote
          have hgone : namedChild I.desc sealed parent nm id = false := by
            simp [namedChild, childOpen, lifeHold, sealed, releaseWorld_self_dead]
          have hkeep : ∀ c, c ∈ w.roster → c ≠ id →
              namedChild I.desc sealed parent nm c = namedChild I.desc w parent nm c := by
            intro c _ hc
            have hk := releaseWorld_keep I.desc w id (w.st id) c hc
            have hp := release_parent I.desc w id (w.st id) c
            simp [namedChild, childOpen, lifeHold, isChild, hk.1, hk.2.1, hp, sealed]
          have hfilter : (sealed.roster.filter (namedChild I.desc sealed parent nm)).length + 1 ≤
              (w.roster.filter (namedChild I.desc w parent nm)).length := by
            rw [hros']
            exact filter_drop_mem (namedChild I.desc w parent nm)
              (namedChild I.desc sealed parent nm) w.roster id hmemF hgone hkeep
          have htombs : (namedTombs ((tmb_snoc sealed parent
              (tombstoneMsg I.desc (sealed.st parent) id)).st parent).prio nm).length =
              (namedTombs (w.st parent).prio nm).length + 1 := by
            rw [tmb_snoc_prio_self, hpPrio]
            simp [namedTombs, tombSlots, List.filterMap_append, List.filter_append, ht, hs]
          have hfiltS : ((tmb_snoc sealed parent (tombstoneMsg I.desc (sealed.st parent) id)).roster.filter
              (namedChild I.desc (tmb_snoc sealed parent (tombstoneMsg I.desc (sealed.st parent) id))
                parent nm)).length =
              (sealed.roster.filter (namedChild I.desc sealed parent nm)).length := by
            have hlife' := tmb_snoc_life sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            have hpend' := tmb_snoc_pend sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            have hpar' := tmb_snoc_parent sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            rw [tmb_snoc_roster]
            apply congrArg List.length
            apply List.filter_congr
            intro c _
            simp [namedChild, childOpen, lifeHold, isChild, hlife', hpend', hpar']
          have hle : namedOpen I.desc (tmb_snoc sealed parent
              (tombstoneMsg I.desc (sealed.st parent) id)) parent nm ≤
              namedOpen I.desc w parent nm := by
            unfold namedOpen
            omega
          exact Nat.le_trans hle (by simpa [nameBudget, hN] using hH.census parent nm)
        · have hsame : ∀ c, namedChild I.desc sealed parent nm c = namedChild I.desc w parent nm c := by
            intro c
            by_cases hc : c = id
            · have hbit : (childName == nm) = false := by
                cases hbb : childName == nm with
                | false => rfl
                | true =>
                  have heq : childName = nm := by simpa [beq_iff_eq] using hbb
                  exact absurd heq.symm hnm
              simp [hc, namedChild, childOpen, hid, hbit, sealed, releaseWorld_self_dead]
            · have hk := releaseWorld_keep I.desc w id (w.st id) c hc
              have hp := release_parent I.desc w id (w.st id) c
              simp [namedChild, childOpen, lifeHold, isChild, hk.1, hk.2.1, hp, sealed]
          have htombs : (namedTombs ((tmb_snoc sealed parent
              (tombstoneMsg I.desc (sealed.st parent) id)).st parent).prio nm).length =
              (namedTombs (w.st parent).prio nm).length := by
            rw [tmb_snoc_prio_self, hpPrio]
            have hbit : (childName == nm) = false := by
              cases hbb : childName == nm with
              | false => rfl
              | true =>
                have heq : childName = nm := by simpa [beq_iff_eq] using hbb
                exact absurd heq.symm hnm
            simp [namedTombs, tombSlots, List.filterMap_append, List.filter_append, ht, hs, hbit]
          have hfilt : ((tmb_snoc sealed parent (tombstoneMsg I.desc (sealed.st parent) id)).roster.filter
              (namedChild I.desc (tmb_snoc sealed parent (tombstoneMsg I.desc (sealed.st parent) id))
                parent nm)).length =
              (w.roster.filter (namedChild I.desc w parent nm)).length := by
            have hlife' := tmb_snoc_life sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            have hpend' := tmb_snoc_pend sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            have hpar' := tmb_snoc_parent sealed parent (tombstoneMsg I.desc (sealed.st parent) id)
            rw [tmb_snoc_roster, hros']
            apply congrArg List.length
            apply List.filter_congr
            intro c _
            have hse := hsame c
            simp only [namedChild, childOpen, lifeHold, isChild, hlife' c, hpend' c, hpar' c] at hse ⊢
            exact hse
          have heq : namedOpen I.desc (tmb_snoc sealed parent
              (tombstoneMsg I.desc (sealed.st parent) id)) parent nm =
              namedOpen I.desc w parent nm := by
            unfold namedOpen
            omega
          simpa [nameBudget, hN, heq] using hH.census parent nm
    · have hfalse : notifies I.desc id = false := by
        cases hn : notifies I.desc id
        · rfl
        · exact absurd hn hnote
      have hlab := silent_label I.desc id hfalse
      have haliveP := (tmb_parent_alive I.desc sealed id parent hsup).2
      have hparP := (tmb_parent_alive I.desc sealed id parent hsup).1
      have hbit : ((sealed.st parent).life == .alive) = true := by
        simpa [beq_iff_eq] using haliveP
      have hlabB : ((tombstoneMsg I.desc (sealed.st parent) id).label == "") = true := by
        simpa [beq_iff_eq, tombstoneMsg, hlab]
      have hdrop : ((sealed.st parent).life != .alive) = false := by simpa [bne, hbit]
      have hcrashW : enqueueTombstone I.desc sealed id = crashWorld sealed := by
        unfold enqueueTombstone
        simp [hparP, hdrop, hlabB]
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
  exact hold_set I w hH id (proceed (w.st id) k) h.1 h.2.1 h.2.2
    (by cases hk : k.rest <;> simp [proceed, hk]) hph hpre

theorem hold_note (I : Impl) (w : World) (hH : Hold I w) (sender : InstId) (dst : String)
    (hpre : w.crashed = false) : Hold I (noteStale w sender dst) :=
  hold_same I w (noteStale w sender dst) hH (fun i => noteStale_st w sender dst i) rfl rfl
    (by simp [noteStale, hpre]) hpre

/-- Sealing one actor and its descendants keeps the lane invariant. The
descendants' tombstones are discarded with the seal. -/
theorem hold_seal_branch (I : Impl) (fuel : Nat) :
    ∀ (w : World) (id : InstId), Hold I w → w.crashed = false →
      Hold I (sealBranch fuel I.desc w id) ∧ (sealBranch fuel I.desc w id).crashed = false := by
  induction fuel with
  | zero =>
    intro w id hH hpre
    simp [sealBranch]
    exact ⟨hH, hpre⟩
  | succ fuel ih =>
    intro w id hH hpre
    simp only [sealBranch]
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel I.desc w0 child else w0
    have hfold : ∀ (ids : List InstId) (w0 : World), Hold I w0 → w0.crashed = false →
        Hold I (ids.foldl step w0) ∧ (ids.foldl step w0).crashed = false := by
      intro ids
      induction ids with
      | nil =>
        intro w0 hH0 hpre0
        simp
        exact ⟨hH0, hpre0⟩
      | cons child ids ihids =>
        intro w0 hH0 hpre0
        simp only [List.foldl_cons, step]
        by_cases hc : isChild w0 id child = true
        · have hstep := ih w0 child hH0 hpre0
          simp only [hc, ite_true]
          exact ihids _ hstep.1 hstep.2
        · have hf : isChild w0 id child = false := by
            cases hb : isChild w0 id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf]
          exact ihids w0 hH0 hpre0
    let sealed := w.roster.foldl step w
    have hmid := hfold w.roster w hH hpre
    change Hold I (if (sealed.st id).life == .alive then
        releaseWorld I.desc sealed id (sealed.st id) else sealed) ∧
      (if (sealed.st id).life == .alive then
        releaseWorld I.desc sealed id (sealed.st id) else sealed).crashed = false
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · have hlive : (sealed.st id).life = .alive := by simpa [beq_iff_eq] using hgo
      simp only [hgo, ite_true]
      exact ⟨hold_release I sealed hmid.1 id (sealed.st id) hmid.2 hlive,
        (release_crash I.desc sealed id (sealed.st id)).symm ▸ hmid.2⟩
    · have hf : ((sealed.st id).life == .alive) = false := by
        cases hb : (sealed.st id).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf]
      exact hmid

/-- Proper descendants are sealed now. The actor itself is unchanged, and the
lane invariant holds of the result. -/
theorem hold_drop_desc (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false) :
    Hold I (dropDescendants I.desc w id) ∧ (dropDescendants I.desc w id).crashed = false := by
  unfold dropDescendants
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 id child then sealBranch w.roster.length I.desc w0 child else w0
  have hfold : ∀ (ids : List InstId) (w0 : World), Hold I w0 → w0.crashed = false →
      Hold I (ids.foldl step w0) ∧ (ids.foldl step w0).crashed = false := by
    intro ids
    induction ids with
    | nil =>
      intro w0 hH0 hpre0
      simp
      exact ⟨hH0, hpre0⟩
    | cons child ids ih =>
      intro w0 hH0 hpre0
      simp only [List.foldl_cons, step]
      by_cases hc : isChild w0 id child = true
      · have hstep := hold_seal_branch I w.roster.length w0 child hH0 hpre0
        simp only [hc, ite_true]
        exact ih _ hstep.1 hstep.2
      · have hf : isChild w0 id child = false := by
          cases hb : isChild w0 id child with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih w0 hH0 hpre0
  exact hfold w.roster w hH hpre

theorem enqueue_roster (D : Description) (w : World) (child : InstId) :
    (enqueueTombstone D w child).roster = w.roster := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simp
  | some parent =>
    by_cases hdead : ((w.st parent).life != .alive) = true
    · simp [hdead]
    · have hf : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hdead
      simp only [hf]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp [hlab, crashWorld]
      · have hlf : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlf, offerPrio]
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp [hfull, crashWorld]
        · have hff : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            cases hb : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) with
            | false => rfl
            | true => exact absurd hb hfull
          simp [hff, setActor]

theorem shutdown_roster (D : Description) (w : World) (id : InstId) :
    (shutdownActor D w id).roster = w.roster := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true, sealActor]
    exact (enqueue_roster D (releaseWorld D w id (w.st id)) id).trans
      (release_roster D w id (w.st id))
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [hf]

theorem enqueue_crashed_dead (D : Description) (w : World) (child : InstId)
    (hpre : w.crashed = false) (hcr : (enqueueTombstone D w child).crashed = true)
    (i : InstId) (hmem : i ∈ w.roster) :
    ((enqueueTombstone D w child).st i).life ≠ .alive := by
  unfold enqueueTombstone at hcr ⊢
  cases hpar : (w.st child).parent with
  | none =>
    simp [hpar] at hcr
    rw [hpre] at hcr
    contradiction
  | some parent =>
    simp only [hpar] at hcr ⊢
    by_cases hdead : ((w.st parent).life != .alive) = true
    · simp [hdead] at hcr
      rw [hpre] at hcr
      contradiction
    · have hf : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hdead
      simp only [hf] at hcr ⊢
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true] at hcr ⊢
        exact crash_not_alive w i hmem
      · have hlf : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlf, ite_false, offerPrio] at hcr ⊢
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp only [hfull, ite_true] at hcr ⊢
          exact crash_not_alive w i hmem
        · have hff : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            cases hb : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) with
            | false => rfl
            | true => exact absurd hb hfull
          simp only [hff, ite_false, setActor] at hcr
          rw [hpre] at hcr
          contradiction

theorem shutdown_dead (D : Description) (w : World) (id : InstId)
    (hpre : w.crashed = false) (hcr : (shutdownActor D w id).crashed = true)
    (i : InstId) (hmem : i ∈ w.roster) :
    ((shutdownActor D w id).st i).life ≠ .alive := by
  unfold shutdownActor at hcr ⊢
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true, sealActor] at hcr ⊢
    have hpreR : (releaseWorld D w id (w.st id)).crashed = false :=
      (release_crash D w id (w.st id)).symm ▸ hpre
    have hmemR : i ∈ (releaseWorld D w id (w.st id)).roster := by
      simpa [release_roster D w id (w.st id)] using hmem
    exact enqueue_crashed_dead D (releaseWorld D w id (w.st id)) id hpreR hcr i hmemR
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    rw [ite_eq_right hlive] at hcr
    rw [hpre] at hcr
    contradiction

theorem seal_roster (D : Description) (fuel : Nat) :
    ∀ w id, (sealBranch fuel D w id).roster = w.roster := by
  induction fuel with
  | zero =>
    intro w id
    simp [sealBranch]
  | succ fuel ih =>
    intro w id
    simp only [sealBranch]
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel D w0 child else w0
    have hfold : ∀ (ids : List InstId) (w0 : World), (List.foldl step w0 ids).roster = w0.roster := by
      intro ids
      induction ids with
      | nil => intro w0; simp
      | cons child ids ihf =>
        intro w0
        simp only [List.foldl_cons, step]
        by_cases hc : isChild w0 id child = true
        · simp only [hc, ite_true]
          exact (ihf _).trans (ih w0 child)
        · have hf : isChild w0 id child = false := by
            cases hb : isChild w0 id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf]
          exact ihf w0
    let sealed := w.roster.foldl step w
    have hmid := hfold w.roster w
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · rw [ite_eq_left hgo]
      exact (release_roster D sealed id (sealed.st id)).trans hmid
    · rw [ite_eq_right hgo]
      exact hmid

theorem drop_roster (D : Description) (w : World) (id : InstId) :
    (dropDescendants D w id).roster = w.roster := by
  unfold dropDescendants
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 id child then sealBranch w.roster.length D w0 child else w0
  have hfold : ∀ (ids : List InstId) (w0 : World), (List.foldl step w0 ids).roster = w0.roster := by
    intro ids
    induction ids with
    | nil => intro w0; simp
    | cons child ids ih =>
      intro w0
      simp only [List.foldl_cons, step]
      by_cases hc : isChild w0 id child = true
      · simp only [hc, ite_true]
        exact (ih _).trans (seal_roster D w.roster.length w0 child)
      · have hf : isChild w0 id child = false := by
          cases hb : isChild w0 id child with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih w0
  exact hfold w.roster w

/-- Once a seal has crashed the roster, no listed actor is still alive, so the
rest of an abort fold does not run. -/
theorem abort_fold_skip (D : Description) (parent : InstId) (ids : List InstId) (w : World)
    (hdead : ∀ c, c ∈ ids → (w.st c).life ≠ .alive) :
    ids.foldl (fun acc child =>
      if isChild acc parent child && (acc.st child).life == .alive then
        shutdownActor D (dropDescendants D acc child) child
      else acc) w = w := by
  induction ids with
  | nil => simp
  | cons c ids ih =>
    simp only [List.foldl_cons]
    have hc : (w.st c).life ≠ .alive := hdead c (List.mem_cons.mpr (Or.inl rfl))
    have hbit : ((w.st c).life == .alive) = false := by simpa [beq_iff_eq] using hc
    have hand : (isChild w parent c && (w.st c).life == .alive) = false := by simp [hbit]
    simp only [hand, ite_false]
    exact ih (fun x hx => hdead x (List.mem_cons_of_mem c hx))

theorem hold_shutdown (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false) : Hold I (shutdownActor I.desc w id) := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true]
    exact hold_seal I w hH id hpre (by simpa [beq_iff_eq] using hlive)
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp only [hf, ite_false]
    exact hH

theorem hold_terminate_stage (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (hpre : w.crashed = false) : Hold I (terminateStage I.desc w id a) := by
  have hD := hold_drop_desc I w hH id hpre
  simpa [terminateStage] using
    hold_shutdown I (dropDescendants I.desc w id) hD.1 id hD.2

theorem hold_abort_children (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (hpre : w.crashed = false) : Hold I (abortChildren I.desc w parent) := by
  unfold abortChildren
  suffices ∀ (ids : List InstId) (w0 : World), Hold I w0 → w0.crashed = false →
      (∀ c, c ∈ ids → c ∈ w0.roster) →
      Hold I (ids.foldl (fun acc child =>
        if isChild acc parent child && (acc.st child).life == .alive then
          shutdownActor I.desc (dropDescendants I.desc acc child) child
        else acc) w0) by
    exact this w.roster w hH hpre (fun _ h => h)
  intro ids
  induction ids with
  | nil =>
    intro w0 hH0 _ _
    simp
    exact hH0
  | cons child ids ih =>
    intro w0 hH0 hpre0 hids
    simp only [List.foldl_cons]
    by_cases hc : (isChild w0 parent child && (w0.st child).life == .alive) = true
    · simp only [hc, ite_true]
      have hD := hold_drop_desc I w0 hH0 child hpre0
      let wD := dropDescendants I.desc w0 child
      let wS := shutdownActor I.desc wD child
      have hS : Hold I wS := hold_shutdown I wD hD.1 child hD.2
      by_cases hcr : wS.crashed = true
      · have hskip := abort_fold_skip I.desc parent ids wS (fun c hcmem => by
          have hmem0 := hids c (List.mem_cons_of_mem child hcmem)
          have hmemD : c ∈ wD.roster := by
            simpa [wD, drop_roster I.desc w0 child] using hmem0
          exact shutdown_dead I.desc wD child hD.2 hcr c hmemD)
        have hHold : Hold I (ids.foldl (fun acc c =>
            if isChild acc parent c && (acc.st c).life == .alive then
              shutdownActor I.desc (dropDescendants I.desc acc c) c
            else acc) wS) := by
          rw [hskip]
          exact hS
        simpa [wS] using hHold
      · have hf : wS.crashed = false := by
          cases h : wS.crashed with
          | false => rfl
          | true => exact absurd h hcr
        exact ih wS hS hf (fun c hcmem => by
          have hmem0 := hids c (List.mem_cons_of_mem child hcmem)
          have hmemD : c ∈ wD.roster := by
            simpa [wD, drop_roster I.desc w0 child] using hmem0
          simpa [wS, wD, shutdown_roster I.desc wD child] using hmemD)
    · have hf : (isChild w0 parent child && (w0.st child).life == .alive) = false := by
        cases hb : isChild w0 parent child && (w0.st child).life == .alive with
        | false => rfl
        | true => exact absurd hb hc
      simp only [hf]
      exact ih w0 hH0 hpre0 (fun c hcmem => hids c (List.mem_cons_of_mem child hcmem))

theorem hold_abort (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (hpre : w.crashed = false) (hlive : a.life = .alive)
    (hk : ∃ tail, k.rest = .abort :: tail) (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := by simpa [beq_iff_eq] using hlive
  rcases hk with ⟨tail, hk⟩
  let k' := afterHead k
  let w' := abortChildren I.desc w id
  have hH' := hold_abort_children I w hH id hpre
  have hbase : execRun I w id a k = commitCont w' id (proceed (w'.st id) k') := by
    simp [execRun, hgo, hk, w', k']
  by_cases hcr : w'.crashed = true
  · simp [hbase, commitCont, hcr]
    exact hH'
  have hcf : w'.crashed = false := by
    cases hb : w'.crashed with
    | false => rfl
    | true => exact absurd hb hcr
  have hrun : execRun I w id a k = setActor w' id (proceed (w'.st id) k') := by
    simp [hbase, commitCont, hcf]
  have hphase : ∀ i, i ∈ (setActor w' id (proceed (w'.st id) k')).roster →
      phaseDeclared I (tname i) ((setActor w' id (proceed (w'.st id) k')).st i).phase := by
    intro i hi
    by_cases heq : i = id
    · have htail := ContDeclared.after I (tname id) k (.abort) tail hk hdec
      simpa [setActor, heq, k'] using proceed_declared I (tname id) (w'.st id) k' htail
    · have hmem : i ∈ w'.roster := by simpa [setActor] using hi
      simpa [setActor, heq] using hH'.phase i hmem
  rw [hrun]
  apply hold_actors I w' (setActor w' id (proceed (w'.st id) k')) hH'
    (by simp [setActor]) (by simp [setActor])
  · intro i
    by_cases h : i = id
    · simp [setActor, h, (proceed_keep (w'.st id) k').1]
    · simp [setActor, h]
  · intro i
    by_cases h : i = id
    · simp [setActor, h, (proceed_keep (w'.st id) k').2.1]
    · simp [setActor, h]
  · intro i
    by_cases h : i = id
    · simp [setActor, h, (proceed_keep (w'.st id) k').2.2]
    · simp [setActor, h]
  · intro i
    by_cases h : i = id
    · simp [setActor, h, proceed_parent]
    · simp [setActor, h]
  · exact hphase
  · simp [setActor]

theorem hold_terminate (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (k : Cont) (hpre : w.crashed = false) (_ha : a = w.st id) (hlive : a.life = .alive)
    (hk : ∃ tail, k.rest = .terminate :: tail) : Hold I (execRun I w id a k) := by
  rcases execRun_terminate I w id a k hlive hk with hcrash | hrest
  · simpa [hcrash] using hold_crash I w hH
  rcases hrest with hshut | hrest
  · obtain ⟨_, _, _, _, _, _, _, heq⟩ := hshut
    simpa [heq] using hold_shutdown I w hH id hpre
  rcases hrest with htree | hcascade
  · obtain ⟨_, _, _, _, heq⟩ := htree
    simpa [heq] using hold_terminate_stage I w hH id a hpre
  · obtain ⟨_, _, _, _, _, _, _, heq⟩ := hcascade
    simpa [heq] using hold_terminate_stage I w hH id a hpre

theorem finish_keep (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).life = a.life ∧ (finishCall a k r).prio = a.prio ∧
      (finishCall a k r).pendingTombstone = a.pendingTombstone := by
  have h := proceed_keep a (selectCall k r)
  simp [finishCall]
  exact h

theorem finish_parent (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).parent = a.parent := by
  simpa [finishCall] using proceed_parent a (selectCall k r)

theorem issue_keep (a : Actor) :
    (issueCall a).life = a.life ∧ (issueCall a).prio = a.prio ∧
      (issueCall a).pendingTombstone = a.pendingTombstone := by
  simp [issueCall]

theorem issue_parent (a : Actor) : (issueCall a).parent = a.parent := by
  simp [issueCall]

theorem charge_keep (a : Actor) (dst : String) :
    (chargeSender a dst).life = a.life ∧ (chargeSender a dst).prio = a.prio ∧
      (chargeSender a dst).pendingTombstone = a.pendingTombstone := by
  simp [chargeSender, bumpToken]

theorem charge_parent (a : Actor) (dst : String) : (chargeSender a dst).parent = a.parent := by
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
theorem mail_parent (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).parent = (w.st i).parent := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · have hfin := finish_parent (w.st sender) k .notAdmitted
    have hpro := proceed_parent (w.st sender) k
    by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
      simp [enqueueOrPark, hdead, hcall, hi, setActor, hfin, hpro] <;>
      first | (subst hi; simp) | exact (proceed_parent _ _) |
        exact (finish_parent _ _ _).trans (issue_parent _) | rfl
  · have hpro := proceed_parent (chargeSender (issueCall (w.st sender)) (tname dst)) k
    by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hcall : isCall = true <;> by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hcall, hi, setActor, hpro, issue_parent, charge_parent, proceed_parent] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_parent, charge_parent, proceed_parent]) |
            exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ |
            exact (proceed_parent _ _).trans (charge_parent _ _) |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2, issue_parent, charge_parent, proceed_parent] <;>
              first | exact (proceed_parent _ _).trans (charge_parent _ _) |
                exact (proceed_parent _ _).trans ((issue_parent _).trans (charge_parent _ _)) |
                exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_parent _ _) |
            exact (finish_parent _ _ _).trans (issue_parent _) | rfl
      · have hdir : dst ≠ sender := by
          intro h
          have hb : decide (sender = dst) = true := decide_eq_true_iff.mpr h.symm
          simp [hb] at hsame
        by_cases hcall : isCall = true <;> by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hcall, hi, hd, hdir, setActor, hpro,
            issue_parent, charge_parent, proceed_parent] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_parent, charge_parent, proceed_parent]) |
            exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ |
            exact (proceed_parent _ _).trans (charge_parent _ _) |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2, issue_parent, charge_parent, proceed_parent] <;>
              first | exact (proceed_parent _ _).trans (charge_parent _ _) |
                exact (proceed_parent _ _).trans ((issue_parent _).trans (charge_parent _ _)) |
                exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_parent _ _) |
            exact (finish_parent _ _ _).trans (issue_parent _) | rfl
    · by_cases hsame : decide (sender = dst) = true
      · by_cases hi : i = sender <;>
          simp [hdead, hroom, hsame, hi, setActor, issue_parent, charge_parent, proceed_parent] <;>
          first | (by_cases hc : isCall = true <;> simp [hc, issue_parent, charge_parent, proceed_parent]) |
            exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ |
            exact (proceed_parent _ _).trans (charge_parent _ _) |
            (by_cases hsd : dst = sender <;> by_cases hc2 : isCall = true <;> simp [hsd, hc2, issue_parent, charge_parent, proceed_parent] <;>
              first | exact (proceed_parent _ _).trans (charge_parent _ _) |
                exact (proceed_parent _ _).trans ((issue_parent _).trans (charge_parent _ _)) |
                exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ | rfl) |
            (subst hi; subst hd; simp) | (subst hi; simp) | exact (proceed_parent _ _) | rfl
      · by_cases hi : i = sender <;> by_cases hd : i = dst <;>
          simp [hdead, hroom, hsame, hi, hd, setActor, issue_keep, charge_keep] <;>
          (by_cases hsd : dst = sender <;> by_cases hc : isCall = true <;> simp [hsd, hc, issue_parent, charge_parent, proceed_parent] <;>
            first | exact (issue_parent _).trans (charge_parent _ _) | exact charge_parent _ _ | rfl)

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
  · intro i; exact mail_parent w I.desc sender dst msg isCall k i
  · intro i hi
    exact hph i (by simpa [mail_roster w I.desc sender dst msg isCall k] using hi)
  · have hc : (enqueueOrPark w I.desc sender dst msg isCall k).crashed = false :=
      (mail_crash w I.desc sender dst msg isCall k).symm ▸ hpre
    exact hc.trans hpre.symm

/-! A fresh birth keeps the lane invariant. The population bound is a count. -/

theorem fold_count {α : Type} (p : α → Bool) (xs : List α) :
    xs.foldl (fun n x => if p x then n + 1 else n) 0 = (xs.filter p).length := by
  have hgen : ∀ (ys : List α) (start : Nat),
      ys.foldl (fun n x => if p x then n + 1 else n) start =
        start + (ys.filter p).length := by
    intro ys
    induction ys with
    | nil =>
      intro start
      simp
    | cons y ys ih =>
      intro start
      simp only [List.foldl_cons, List.filter_cons]
      by_cases hp : p y = true
      · simp only [hp, ite_true, List.length_cons]
        rw [ih (start + 1)]
        omega
      · have hpf : p y = false := by
          cases hbit : p y
          · rfl
          · exact absurd hbit hp
        rw [ite_eq_right (by rw [hpf]; decide)]
        rw [ih start]
        rw [ite_eq_right (by rw [hpf]; decide)]
  have hcount := hgen xs 0
  rw [Nat.zero_add] at hcount
  exact hcount

theorem erase_len {α : Type} [DecidableEq α] (a : α) (l : List α) (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases hbit : x == a with
    | true => simp [List.erase, hbit]
    | false =>
      have hne : a ≠ x := by
        intro heq
        have : (x == a) = true := by simpa [beq_iff_eq, heq] 
        simp [this] at hbit
      have htail : a ∈ xs := by
        cases List.mem_cons.mp h with
        | inl hx => exact absurd hx hne
        | inr ht => exact ht
      simp [List.erase, hbit]
      have := ih htail
      omega

theorem mem_erase_ne {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (hne : a ≠ b) (h : a ∈ l) : a ∈ l.erase b := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases hbit : x == b with
    | true =>
      have hx : x = b := by simpa [beq_iff_eq] using hbit
      simp [List.erase, hbit]
      cases List.mem_cons.mp h with
      | inl ha => exact absurd (ha.trans hx) hne
      | inr ht => exact ht
    | false =>
      simp [List.erase, hbit]
      cases List.mem_cons.mp h with
      | inl ha => exact Or.inl ha
      | inr ht => exact Or.inr (ih ht)

theorem nodup_mem_length {α : Type} [DecidableEq α] (xs ys : List α)
    (hnd : xs.Nodup) (h : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hpair := List.nodup_cons.mp hnd
    have hx : x ∈ ys := h x List.mem_cons_self
    have htail : xs.length ≤ (ys.erase x).length :=
      ih (ys.erase x) hpair.2 (fun y hy =>
        mem_erase_ne (fun heq => hpair.1 (heq ▸ hy)) (h y (List.mem_cons_of_mem x hy)))
    have hlen := erase_len x ys hx
    rw [List.length_cons]
    omega

theorem filter_add {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = true → q x = true → False) :
    (xs.filter p).length + (xs.filter q).length =
      (xs.filter (fun x => p x || q x)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.filter_cons]
    by_cases hp : p x = true
    · have hq : ¬ q x = true := fun ht => h x List.mem_cons_self hp ht
      have hqf : q x = false := by
        cases hbit : q x
        · rfl
        · exact absurd hbit hq
      have hor : (p x || q x) = true := by simp [hp, hqf]
      rw [ite_eq_left hp, ite_eq_right (by rw [hqf]; decide), ite_eq_left hor]
      simp [List.length_cons]
      omega
    · have hpf : p x = false := by
        cases hbit : p x
        · rfl
        · exact absurd hbit hp
      by_cases hq : q x = true
      · have hor : (p x || q x) = true := by simp [hpf, hq]
        rw [ite_eq_right (by rw [hpf]; decide), ite_eq_left hq, ite_eq_left hor]
        simp [List.length_cons]
        omega
      · have hqf : q x = false := by
          cases hbit : q x
          · rfl
          · exact absurd hbit hq
        have hor : (p x || q x) = false := by simp [hpf, hqf]
        rw [ite_eq_right (by rw [hpf]; decide), ite_eq_right (by rw [hqf]; decide),
          ite_eq_right (by rw [hor]; decide)]
        exact ih

theorem split_root (child root : Bool) (h : child = true → root = true) :
    (child || (root && !child)) = root := by
  cases child <;> cases root <;> simp_all

def rootBit (_D : Description) (w : World) (supervisor name : String) (id : InstId) : Bool :=
  match id with
  | .peer child k _ =>
    child == name &&
      ((w.st id).life == .alive ||
        slotTombstoneQueued w (.core supervisor) name k)
  | .core _ => false

theorem foldl_congr {α β : Type} (f g : β → α → β) (xs : List α) (start : β)
    (h : ∀ b a, f b a = g b a) : xs.foldl f start = xs.foldl g start := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h start x]
    exact ih (g start x)

theorem root_step (D : Description) (w : World) (supervisor name : String) (n : Nat) (id : InstId) :
    (match id with
      | InstId.peer child k _ =>
        if child == name &&
            ((w.st id).life == .alive ||
              slotTombstoneQueued w (.core supervisor) name k) then n + 1
        else n
      | InstId.core _ => n) =
      (if rootBit D w supervisor name id then n + 1 else n) := by
  cases id with
  | core _ => simp [rootBit]
  | peer _ _ _ => simp [rootBit]

theorem root_filter (D : Description) (w : World) (supervisor name : String) :
    rootOutstanding D w supervisor name =
      (w.roster.filter (rootBit D w supervisor name)).length := by
  unfold rootOutstanding
  refine Eq.trans
    (foldl_congr _ (fun n id => if rootBit D w supervisor name id then n + 1 else n) w.roster 0
      (fun n id => root_step D w supervisor name n id))
    ?_
  exact fold_count (rootBit D w supervisor name) w.roster

theorem namedChild_parts (D : Description) (w : World) (parent : InstId) (name : String)
    (c : InstId) (h : namedChild D w parent name c = true) :
    isChild w parent c = true ∧ lifeHold (w.st c) = true ∧ notifies D c = true ∧
      ∃ n k g, c = InstId.peer n k g ∧ (n == name) = true := by
  cases c with
  | core _ => simp [namedChild, childOpen] at h
  | peer n k g =>
    simp only [namedChild, childOpen] at h
    have h1 := (Bool.and_eq_true _ _).mp h
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    exact ⟨h3.1, h3.2, h2.2, n, k, g, rfl, h1.2⟩

theorem lifeHold_live (a : Actor) (h : lifeHold a = true) :
    (a.life == .alive) = true := by
  cases hl : a.life with
  | alive => simp [hl]
  | absent => simp [lifeHold, hl] at h
  | dead => simp [lifeHold, hl] at h

theorem named_rootBit (I : Impl) (w : World) (supervisor name : String) (c : InstId)
    (h : namedChild I.desc w (.core supervisor) name c = true) :
    rootBit I.desc w supervisor name c = true := by
  obtain ⟨_, hhold, _, n, k, g, hc, hname⟩ :=
    namedChild_parts I.desc w (.core supervisor) name c h
  subst hc
  have hlive := lifeHold_live (w.st (.peer n k g)) hhold
  simp [rootBit, hname, hlive]

theorem bool_ite_false {α : Type} {b : Bool} {a c : α} (h : b = false) :
    (if b then a else c) = c := by
  subst h
  rfl

theorem bool_ite_true {α : Type} {b : Bool} {a c : α} (h : b = true) :
    (if b then a else c) = a := by
  subst h
  rfl

def nameSenders (ms : List Msg) (name : String) : List InstId :=
  ms.filterMap fun m =>
    if m.tombstone then
      match m.sender with
      | .peer n _ _ => if n == name then some m.sender else none
      | .core _ => none
    else none

theorem nameSenders_cons (m : Msg) (ms : List Msg) (name : String) :
    nameSenders (m :: ms) name =
      (match m.tombstone, m.sender with
        | true, .peer n _ _ => if n == name then [m.sender] else []
        | _, _ => []) ++ nameSenders ms name := by
  unfold nameSenders
  simp only [List.filterMap_cons]
  cases ht : m.tombstone with
  | false => cases hs : m.sender <;> simp [nameSenders, ht, hs]
  | true =>
    cases hs : m.sender with
    | core _ => simp [nameSenders, ht, hs]
    | peer n k g =>
      by_cases hname : (n == name) = true
      · simp only [nameSenders, ht, hs, hname]
        rfl
      · have hf : (n == name) = false := by
          cases hbb : n == name
          · rfl
          · exact absurd hbb hname
        simp only [nameSenders, ht, hs, hf]
        rfl

theorem sender_src (ms : List Msg) (name : String) (s : InstId)
    (h : s ∈ nameSenders ms name) :
    ∃ m k g, m ∈ ms ∧ m.tombstone = true ∧ m.sender = s ∧ s = InstId.peer name k g ∧
      (name, k) ∈ tombSlots ms := by
  induction ms with
  | nil => simp [nameSenders] at h
  | cons m ms ih =>
    rw [nameSenders_cons] at h
    cases List.mem_append.mp h with
    | inl hhead =>
      cases ht : m.tombstone with
      | false => simp [ht] at hhead
      | true =>
        cases hs : m.sender with
        | core _ => simp [ht, hs] at hhead
        | peer n k g =>
          cases hname : n == name with
          | false => simp [ht, hs, hname] at hhead
          | true =>
            simp [ht, hs, hname] at hhead
            have hn : n = name := by simpa [beq_iff_eq] using hname
            subst hn
            refine ⟨m, k, g, List.mem_cons_self, ht, ?_, hhead, ?_⟩
            · simpa [hs] using hhead.symm
            · rw [tmb_tombs_cons]
              simp [ht, hs]
    | inr htail =>
      obtain ⟨m0, k, g, hm, ht, hs, hid, hslot⟩ := ih htail
      refine ⟨m0, k, g, List.mem_cons_of_mem _ hm, ht, hs, hid, ?_⟩
      rw [tmb_tombs_cons]
      exact List.mem_append_right _ hslot

theorem senders_len (ms : List Msg) (name : String) :
    (nameSenders ms name).length = (namedTombs ms name).length := by
  induction ms with
  | nil => simp [nameSenders, namedTombs, tombSlots]
  | cons m ms ih =>
    rw [nameSenders_cons]
    simp only [namedTombs, tmb_tombs_cons, List.filter_append, List.length_append, ih]
    cases ht : m.tombstone with
    | false => simp [List.filter_nil, List.length_nil]
    | true =>
      cases hs : m.sender with
      | core _ => simp [List.filter_nil, List.length_nil]
      | peer n k g =>
        simp only [ht, hs, List.filter_cons, List.filter_nil]
        cases hname : n == name with
        | false =>
          have hF : (false = true) ↔ False := by decide
          simp [hname, hF, List.length_nil]
        | true =>
          have hT : (true = true) ↔ True := by decide
          simp [hname, hT, List.length_singleton, List.length_nil]

theorem senders_nodup (ms : List Msg) (name : String) (h : (tombSlots ms).Nodup) :
    (nameSenders ms name).Nodup := by
  induction ms with
  | nil => simp [nameSenders]
  | cons m ms ih =>
    rw [nameSenders_cons]
    have htombs := tmb_tombs_cons m ms
    rw [htombs] at h
    cases ht : m.tombstone with
    | false =>
      simp only [ht, List.nil_append] at h ⊢
      exact ih h
    | true =>
      cases hs : m.sender with
      | core _ =>
        simp only [ht, hs, List.nil_append] at h ⊢
        exact ih h
      | peer n k g =>
        simp only [ht, hs, List.singleton_append] at h ⊢
        have hpair := List.nodup_cons.mp h
        cases hname : n == name with
        | false =>
          have hF : (false = true) ↔ False := by decide
          simp [hF, List.nil_append]
          exact ih hpair.2
        | true =>
          have hT : (true = true) ↔ True := by decide
          simp [hT, List.singleton_append]
          have hn : n = name := by simpa [beq_iff_eq] using hname
          have hnot : InstId.peer n k g ∉ nameSenders ms name := by
            intro hin
            obtain ⟨_, k', _, _, _, _, hid, hslot⟩ := sender_src ms name (InstId.peer n k g) hin
            have hk : k' = k := by
              cases hid
              rfl
            have hslot' : (n, k) ∈ tombSlots ms := by
              simpa [hn, hk] using hslot
            exact hpair.1 hslot'
          exact ⟨by simpa [hs] using hnot, ih hpair.2⟩

theorem any_tomb (ms : List Msg) (m : Msg) (name : String) (k g : Nat)
    (hm : m ∈ ms) (ht : m.tombstone = true) (hs : m.sender = InstId.peer name k g) :
    (ms.any fun p =>
      p.tombstone &&
        match p.sender with
        | .peer n key _ => n == name && key == k
        | .core _ => false) = true := by
  induction ms with
  | nil => cases hm
  | cons p ps ih =>
    cases List.mem_cons.mp hm with
    | inl heq =>
      subst heq
      simp [List.any_cons, ht, hs]
    | inr htail =>
      have ih' := ih htail
      simp [List.any_cons, ih']

theorem sender_fit (I : Impl) (w : World) (supervisor name : String) (s : InstId)
    (hH : Hold I w) (h : s ∈ nameSenders ((w.st (.core supervisor)).prio) name) :
    s ∈ w.roster ∧ rootBit I.desc w supervisor name s = true ∧
      namedChild I.desc w (.core supervisor) name s = false := by
  obtain ⟨m, k, g, hm, ht, hs, hid, _⟩ := sender_src _ name s h
  cases hid
  have hmem : InstId.peer name k g ∈ w.roster := by
    simpa [hs] using hH.tombHere (.core supervisor) m hm ht
  have hqueued : slotTombstoneQueued w (.core supervisor) name k = true := by
    unfold slotTombstoneQueued
    exact any_tomb _ m name k g hm ht hs
  have hroot : rootBit I.desc w supervisor name (.peer name k g) = true := by
    simp [rootBit, hqueued]
  have hnot : namedChild I.desc w (.core supervisor) name (.peer name k g) = false := by
    cases hbit : namedChild I.desc w (.core supervisor) name (.peer name k g) with
    | false => rfl
    | true =>
      obtain ⟨hchild, hhold, hnote, _, _, _, hc, _⟩ :=
        namedChild_parts I.desc w (.core supervisor) name (.peer name k g) hbit
      cases hc
      have hfresh := hH.fresh (.core supervisor) (.peer name k g) hmem hchild hhold hnote
      dsimp at hfresh
      rw [hqueued] at hfresh
      cases hfresh
  exact ⟨hmem, hroot, hnot⟩

/-- Notifying children of one root, plus the tombstones of that template, are at
most the roots still outstanding: each child is alive, and each
tombstone names a different roster id that is not itself still a notifying child. -/
theorem named_le_root (I : Impl) (w : World) (hH : Hold I w) (supervisor name : String) :
    namedOpen I.desc w (.core supervisor) name ≤ rootOutstanding I.desc w supervisor name := by
  let parent := InstId.core supervisor
  let child := namedChild I.desc w parent name
  let rest := fun c => rootBit I.desc w supervisor name c && !child c
  have hdis : ∀ x, x ∈ w.roster → child x = true → rest x = true → False := by
    intro x _ hc hr
    simp [rest, Bool.and_eq_true] at hr
    exact absurd hc (by simpa using hr.2)
  have hadd := filter_add child rest w.roster hdis
  have hor : ∀ c, (child c || rest c) = rootBit I.desc w supervisor name c := by
    intro c
    exact split_root (child c) (rootBit I.desc w supervisor name c) (fun h => named_rootBit I w supervisor name c h)
  have hfilter : w.roster.filter (fun c => child c || rest c) =
      w.roster.filter (rootBit I.desc w supervisor name) := by
    apply List.filter_congr
    intro c _
    exact hor c
  have hsenders : (nameSenders (w.st parent).prio name).Nodup :=
    senders_nodup _ name (hH.lane parent).tombNodup
  have hfit : ∀ s, s ∈ nameSenders (w.st parent).prio name →
      s ∈ w.roster.filter rest := by
    intro s hs
    have h := sender_fit I w supervisor name s hH hs
    exact List.mem_filter.mpr ⟨h.1, by
      have hnot : child s = false := by simpa [child, parent] using h.2.2
      simp [rest, h.2.1, hnot]⟩
  have hlen := nodup_mem_length _ _ hsenders hfit
  have heq := senders_len (w.st parent).prio name
  have hroot := root_filter I.desc w supervisor name
  have hopen : namedOpen I.desc w parent name =
      (w.roster.filter child).length + (nameSenders (w.st parent).prio name).length := by
    simp [namedOpen, parent, child, heq]
  rw [hopen, hroot]
  have hsum : (w.roster.filter child).length + (w.roster.filter rest).length =
      (w.roster.filter (rootBit I.desc w supervisor name)).length := by
    simpa [hfilter] using hadd
  omega

theorem fold_ge_gen (ids : List InstId) (name : String) (key start : Nat) :
    start ≤ ids.foldl (fun acc id =>
      match id with
      | .peer n k g => if n == name && k == key then max acc (g + 1) else acc
      | .core _ => acc) start := by
  induction ids generalizing start with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    cases id with
    | core _ => exact ih start
    | peer n k g =>
      by_cases hbit : (n == name && k == key) = true
      · simp only [hbit, ite_true]
        exact Nat.le_trans (Nat.le_max_left start (g + 1)) (ih (max start (g + 1)))
      · have hf : (n == name && k == key) = false := by
          cases hbb : n == name && k == key
          · rfl
          · exact absurd hbb hbit
        dsimp
        rw [bool_ite_false hf]
        exact ih start

theorem gen_fresh (w : World) (name : String) (key : Nat) :
    InstId.peer name key (maxGen w name key) ∉ w.roster := by
  intro h
  have hlt := maxGen_gt w.roster name key (maxGen w name key) h
  simp [maxGen] at hlt

theorem fold_ge_key (D : Description) (sub : String) (ids : List InstId) (start : Nat) :
    start ≤ ids.foldl (fun m id =>
      match id with
      | .peer n k _ =>
        if sub != "" && templateSubtree D n == sub then max m (k + 1) else m
      | .core _ => m) start := by
  induction ids generalizing start with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    cases id with
    | core _ => exact ih start
    | peer n k _ =>
      by_cases hbit : (sub != "" && templateSubtree D n == sub) = true
      · simp only [hbit, ite_true]
        exact Nat.le_trans (Nat.le_max_left start (k + 1)) (ih (max start (k + 1)))
      · have hf : (sub != "" && templateSubtree D n == sub) = false := by
          cases hbb : sub != "" && templateSubtree D n == sub
          · rfl
          · exact absurd hbb hbit
        dsimp
        rw [bool_ite_false hf]
        exact ih start

theorem freshKey_gt (D : Description) (w : World) (sub n : String) (k g : Nat)
    (hsub : sub ≠ "") (htree : templateSubtree D n = sub)
    (hmem : InstId.peer n k g ∈ w.roster) : k < freshKey D w sub := by
  have hbit : (sub != "") = true := by simpa [bne, beq_iff_eq] using hsub
  have htreeB : (templateSubtree D n == sub) = true := by simpa [beq_iff_eq] using htree
  have hcond : (sub != "" && templateSubtree D n == sub) = true := by
    simp only [hbit, htreeB, Bool.true_and]
  have hgen : ∀ (ids : List InstId) (start : Nat), InstId.peer n k g ∈ ids →
      k + 1 ≤ ids.foldl (fun m id =>
        match id with
        | .peer n' k' _ =>
          if sub != "" && templateSubtree D n' == sub then max m (k' + 1) else m
        | .core _ => m) start := by
    intro ids
    induction ids with
    | nil =>
      intro _ hbad
      cases hbad
    | cons id ids ih =>
      intro start hmem'
      simp only [List.foldl_cons]
      cases List.mem_cons.mp hmem' with
      | inl heq =>
        cases heq
        simp only [hcond, ite_true]
        exact Nat.le_trans (Nat.le_max_right start (k + 1)) (fold_ge_key D sub ids (max start (k + 1)))
      | inr htail =>
        cases id with
        | core _ => exact ih start htail
        | peer n' k' _ =>
          by_cases hif : (sub != "" && templateSubtree D n' == sub) = true
          · simp only [hif, ite_true]
            exact ih (max start (k' + 1)) htail
          · have hf : (sub != "" && templateSubtree D n' == sub) = false := by
              cases hbb : sub != "" && templateSubtree D n' == sub
              · rfl
              · exact absurd hbb hif
            dsimp
            rw [bool_ite_false hf]
            exact ih start htail
  have hfold := hgen w.roster (w.nextKey sub) hmem
  have hle : k + 1 ≤ freshKey D w sub := by
    unfold freshKey
    exact hfold
  omega

theorem freshKey_empty (D : Description) (w : World) : freshKey D w "" = w.nextKey "" := by
  unfold freshKey
  have hgo : ∀ (ids : List InstId) (start : Nat), ids.foldl (fun m id =>
      match id with
      | .peer n k _ => if ("" != "") && templateSubtree D n == "" then max m (k + 1) else m
      | .core _ => m) start = start := by
    intro ids
    induction ids with
    | nil => intro start; simp
    | cons id ids ih =>
      intro start
      simp only [List.foldl_cons]
      cases id with
      | core _ => exact ih start
      | peer n k g =>
        have hf : (("" != "") && templateSubtree D n == "") = false := by
          have hz : ("" != "") = false := by simp [bne]
          simp only [hz, Bool.false_and]
        have hstep :
            (match InstId.peer n k g with
              | InstId.peer n' k' _ =>
                if ("" != "") && templateSubtree D n' == "" then max start (k' + 1) else start
              | InstId.core _ => start) = start := by
          simp [hf]
        rw [hstep]
        exact ih start
  exact hgo w.roster (w.nextKey "")

/-- Keys a lone unsupervised template has already used sit strictly below `nextIx`. -/
def IxPast (I : Impl) (w : World) : Prop :=
  ∀ n k g, InstId.peer n k g ∈ w.roster →
    ∀ t, templateOf I.desc n = some t →
      t.supervisor = none → t.subtree = "" → k < w.nextIx n

/-- Empty-subtree roots under a core share `nextKey ""`, which only moves forward. -/
def RootPast (I : Impl) (w : World) : Prop :=
  ∀ n k g, InstId.peer n k g ∈ w.roster →
    ∀ t, templateOf I.desc n = some t →
      t.subtree = "" → rootOf I.desc t = true →
        ∀ sup, t.supervisor = some sup → k < w.nextKey ""

theorem ix_stable (I : Impl) (w w' : World) (h : IxPast I w)
    (hros : w'.roster = w.roster) (hix : ∀ n, w'.nextIx n = w.nextIx n) : IxPast I w' := by
  intro n k g hmem t ht hsup hsub
  rw [hros] at hmem
  simpa [hix n] using h n k g hmem t ht hsup hsub

theorem root_stable (I : Impl) (w w' : World) (h : RootPast I w)
    (hros : w'.roster = w.roster) (hkey : w'.nextKey "" = w.nextKey "") : RootPast I w' := by
  intro n k g hmem t ht hsub hroot sup hsup
  rw [hros] at hmem
  simpa [hkey] using h n k g hmem t ht hsub hroot sup hsup

theorem beq_comm {α : Type} [DecidableEq α] (x y : α) : (x == y) = (y == x) := by
  cases h : x == y <;> cases h2 : y == x
  · rfl
  · have hy : y = x := by simpa [beq_iff_eq] using h2
    simp [hy] at h
  · have hx : x = y := by simpa [beq_iff_eq] using h
    simp [hx] at h2
  · rfl

theorem same_comm (a b : InstId) : sameSlot a b = sameSlot b a := by
  cases a <;> cases b <;> simp [sameSlot, beq_comm, Bool.and_comm]

theorem hold_born (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (born : Actor)
    (w' : World) (hpre : w.crashed = false)
    (hst : ∀ i, w'.st i = if i = id then born else w.st i)
    (hros : w'.roster = w.roster ++ [id]) (hN : w'.N = w.N) (hcrash : w'.crashed = false)
    (hlive : born.life = .alive) (hprio0 : born.prio = [])
    (hpend0 : born.pendingTombstone = false)
    (hph : phaseDeclared I (tname id) born.phase)
    (hrole : ∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = tmb_role id)
    (hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true → sameSlot id c = false)
    (hlegal : ∀ parent, isChild w' parent id = true → lifeHold born = true →
      notifies I.desc id = true →
      match id with
      | .peer n k _ => slotIndexed I.desc parent n = true → (n, k) ∈ legalSlots I.desc parent w'.N
      | .core _ => True)
    (hfresh : ∀ parent, isChild w' parent id = true → lifeHold born = true →
      notifies I.desc id = true →
      match id with
      | .peer n k _ => slotTombstoneQueued w' parent n k = false
      | .core _ => True)
    (hroot : ∀ name, id = .core name → born.parent = none)
    (hcensus : ∀ parent name, namedOpen I.desc w' parent name ≤
      nameBudget I.desc parent w'.N name) : Hold I w' := by
  have hnewSt : w'.st id = born := by simpa using hst id
  have hst_old : ∀ i, i ≠ id → w'.st i = w.st i := by
    intro i hne
    have heq := hst i
    rw [ite_eq_right hne] at heq
    exact heq
  have mem_old : ∀ c, c ∈ w'.roster → c ≠ id → c ∈ w.roster := by
    intro c hc hne
    rw [hros] at hc
    cases List.mem_append.mp hc with
    | inl h => exact h
    | inr h =>
      have heq : c = id := by simpa [List.mem_singleton] using h
      exact absurd heq hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcensus, ?_⟩
  · intro i hl
    by_cases hi : i = id
    · simpa [hros, hi] using
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    · have hold := hH.rostered i (by simpa [hst_old i hi] using hl)
      rw [hros]
      exact List.mem_append.mpr (Or.inl hold)
  · intro i hp
    by_cases hi : i = id
    · simp [hi, hnewSt, hpend0] at hp
    · have heq := hst_old i hi
      simpa [heq] using hH.pend i (by simpa [heq] using hp)
  · intro _ i hd
    by_cases hi : i = id
    · simp [hi, hnewSt, hlive] at hd
    · have heq := hst_old i hi
      simpa [heq] using hH.deadPrio hpre i (by simpa [heq] using hd)
  · intro i hi
    by_cases hc : i = id
    · simpa [hc] using hrole
    · exact hH.role i (mem_old i hi hc)
  · intro i hi
    by_cases hc : i = id
    · simpa [hc, hnewSt] using hph
    · simpa [hst_old i hc] using hH.phase i (mem_old i hi hc)
  · intro i
    by_cases hi : i = id
    · have hp : (w'.st i).prio = [] := by simpa [hi, hnewSt] using hprio0
      exact lane_nil I w' i hp
    · have heq := hst_old i hi
      have hlane := hH.lane i
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [heq] using hlane.ordNodup
      · intro l hl
        exact hlane.ordIn l (by simpa [heq] using hl)
      · intro m hm ht
        exact hlane.peer m (by simpa [heq] using hm) ht
      · simpa [heq] using hlane.tombNodup
  · intro parent c hc hchild hhold hnote
    by_cases hcid : c = id
    · have hholdB : lifeHold born = true := by simpa [hcid, hnewSt, lifeHold] using hhold
      have hchildB : isChild w' parent id = true := by simpa [hcid, hnewSt] using hchild
      have hnoteId : notifies I.desc id = true := by simpa [hcid] using hnote
      rw [hcid]
      cases id with
      | core _ => exact hlegal parent hchildB hholdB hnoteId
      | peer n k g =>
        intro hidx
        exact hlegal parent hchildB hholdB hnoteId hidx
    · have heq := hst_old c hcid
      have hchild' : isChild w parent c = true := by
        simpa [isChild_eq w w' parent c (congrArg Actor.parent heq)] using hchild
      have hhold' : lifeHold (w.st c) = true := by simpa [lifeHold, heq] using hhold
      have hlegal' := hH.legalLife parent c (mem_old c hc hcid) hchild' hhold' hnote
      cases c with
      | core _ => trivial
      | peer n k g => simpa [hN] using hlegal'
  · intro parent name k hq hidx
    by_cases hp : parent = id
    · have hnil : (w'.st parent).prio = [] := by simpa [hp, hnewSt] using hprio0
      simp [slotTombstoneQueued, hnil] at hq
    · have heq := hst_old parent hp
      have hq' : slotTombstoneQueued w parent name k = true := by
        simpa [slotTombstoneQueued, heq] using hq
      simpa [hN] using hH.legalTomb parent name k hq' hidx
  · intro parent c hc hchild hhold hnote
    by_cases hcid : c = id
    · have hholdB : lifeHold born = true := by simpa [hcid, hnewSt, lifeHold] using hhold
      have hchildB : isChild w' parent id = true := by simpa [hcid, hnewSt] using hchild
      have hnoteId : notifies I.desc id = true := by simpa [hcid] using hnote
      rw [hcid]
      cases id with
      | core _ => exact hfresh parent hchildB hholdB hnoteId
      | peer n k g => exact hfresh parent hchildB hholdB hnoteId
    · by_cases hp : parent = id
      · cases c with
        | core _ => trivial
        | peer _ _ _ =>
          have hnil : (w'.st parent).prio = [] := by simpa [hp, hnewSt] using hprio0
          simp [slotTombstoneQueued, hnil]
      · have heq := hst_old c hcid
        have hchild' : isChild w parent c = true := by
          simpa [isChild_eq w w' parent c (congrArg Actor.parent heq)] using hchild
        have hhold' : lifeHold (w.st c) = true := by simpa [lifeHold, heq] using hhold
        have hfresh' := hH.fresh parent c (mem_old c hc hcid) hchild' hhold' hnote
        cases c with
        | core _ => trivial
        | peer n k g =>
          simpa [slotTombstoneQueued, hst_old parent hp] using hfresh'
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    by_cases h1 : c1 = id
    · by_cases h2 : c2 = id
      · exact h1.trans h2.symm
      · have ho2' : occupant (w.st c2) = true := by
          simpa [occupant, hst_old c2 h2] using ho2
        have hf := hocc c2 (mem_old c2 hc2 h2) ho2'
        have hslot' : sameSlot id c2 = true := by simpa [h1] using hslot
        simp [hf] at hslot'
    · by_cases h2 : c2 = id
      · have ho1' : occupant (w.st c1) = true := by
          simpa [occupant, hst_old c1 h1] using ho1
        have hf := hocc c1 (mem_old c1 hc1 h1) ho1'
        have hslot' : sameSlot id c1 = true := by
          simpa [same_comm, h2] using hslot
        simp [hf] at hslot'
      · have ho1' : occupant (w.st c1) = true := by
          simpa [occupant, hst_old c1 h1] using ho1
        have ho2' : occupant (w.st c2) = true := by
          simpa [occupant, hst_old c2 h2] using ho2
        exact hH.occ c1 c2 (mem_old c1 hc1 h1) (mem_old c2 hc2 h2) ho1' ho2' hslot
          ((congrArg Actor.parent (hst_old c1 h1)).symm.trans
            (hpa.trans (congrArg Actor.parent (hst_old c2 h2))))
  · intro name
    by_cases hc : id = .core name
    · have hstc : w'.st (.core name) = born := by simpa [hc] using hnewSt
      simpa [hstc] using hroot name hc
    · have hne : InstId.core name ≠ id := fun h => hc h.symm
      simpa [hst_old (.core name) hne] using hH.rooted name
  · intro i m hm ht
    by_cases hi : i = id
    · simp [hi, hnewSt, hprio0] at hm
    · have heq := hst_old i hi
      have hmem := hH.tombHere i m (by simpa [heq] using hm) ht
      rw [hros]
      exact List.mem_append.mpr (Or.inl hmem)

theorem tombs_plain (ms : List Msg) (msg : Msg) (ht : msg.tombstone = false) :
    tombSlots (ms ++ [msg]) = tombSlots ms := by
  simp only [tombSlots, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, ht]
  simp

theorem labels_plain (ms : List Msg) (msg : Msg) (ht : msg.tombstone = false) :
    tmb_laneLabels (ms ++ [msg]) = tmb_laneLabels ms ++ [msg.label] := by
  simp only [tmb_laneLabels, List.filter_append, List.map_append]
  have hkeep : List.filter (fun m => !m.tombstone) [msg] = [msg] := by simp [ht]
  simp [hkeep]

/-- Appending one ordinary priority message does not move the population count.
The label is new on the lane and declared for the receiver. -/
theorem hold_plain (I : Impl) (w : World) (hH : Hold I w) (host : InstId) (msg : Msg)
    (hpre : w.crashed = false) (halive : (w.st host).life = .alive)
    (ht : msg.tombstone = false)
    (hlabel : msg.label ∈ prioLabels I (tname host))
    (hnew : msg.label ∉ tmb_laneLabels ((w.st host).prio)) : Hold I (tmb_snoc w host msg) := by
  let w' := tmb_snoc w host msg
  have hlife := tmb_snoc_life w host msg
  have hpend := tmb_snoc_pend w host msg
  have hpar := tmb_snoc_parent w host msg
  have hphase := tmb_snoc_phase w host msg
  have hros := tmb_snoc_roster w host msg
  have hN := tmb_snoc_N w host msg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hl
    exact hros ▸ hH.rostered i (by simpa [w', hlife i] using hl)
  · intro i hp
    simpa [hlife i] using hH.pend i (hpend i ▸ hp)
  · intro _ i hd
    by_cases hi : i = host
    · have hdead : (w.st host).life = .dead := by simpa [w', hi, hlife] using hd
      simp [halive] at hdead
    · exact tmb_snoc_prio_other w host msg i hi ▸
        hH.deadPrio hpre i (by simpa [w', hi, hlife] using hd)
  · intro i hid
    exact hH.role i (by simpa [w', hros] using hid)
  · intro i hid
    exact hphase i ▸ hH.phase i (by simpa [w', hros] using hid)
  · intro i
    by_cases hi : i = host
    · rw [hi]
      have hold := hH.lane host
      have hprio := tmb_snoc_prio_self w host msg
      have hlabels := labels_plain (w.st host).prio msg ht
      have htombs := tombs_plain (w.st host).prio msg ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [w', hprio, hlabels] using tmb_nodup_snoc _ msg.label hold.ordNodup hnew
      · intro l hl
        have hl' : l ∈ tmb_laneLabels ((w.st host).prio) ++ [msg.label] := by
          simpa [w', hprio, hlabels] using hl
        simp [List.mem_append, List.mem_singleton] at hl'
        cases hl' with
        | inl holdl => exact hold.ordIn l holdl
        | inr heq => simpa [heq] using hlabel
      · intro m hm htm
        have hm' : m ∈ (w.st host).prio ++ [msg] := by simpa [w', hprio] using hm
        simp [List.mem_append, List.mem_singleton] at hm'
        cases hm' with
        | inl holdm => exact hold.peer m holdm htm
        | inr heq => simp [heq, ht] at htm
      · simpa [w', hprio, htombs] using hold.tombNodup
    · have heq := tmb_snoc_prio_other w host msg i hi
      have hold := hH.lane i
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [w', heq] using hold.ordNodup
      · intro l hl
        exact hold.ordIn l (by simpa [w', heq] using hl)
      · intro m hm htm
        exact hold.peer m (by simpa [w', heq] using hm) htm
      · simpa [w', heq] using hold.tombNodup
  · intro parent c hc hchild hhold hnote
    rw [lifeHold_eq (w'.st c) (w.st c) (hlife c)] at hhold
    rw [isChild_eq w w' parent c (hpar c)] at hchild
    have hlegal := hH.legalLife parent c (by simpa [w', hros] using hc) hchild hhold hnote
    cases c with
    | core _ => trivial
    | peer n k g => simpa [w', hN] using hlegal
  · intro parent name k hq hidx
    have hqmem : (name, k) ∈ tombSlots ((w'.st parent).prio) := (tmb_queued_iff w' parent name k).mp hq
    by_cases hp : parent = host
    · have hslots : tombSlots ((w'.st parent).prio) = tombSlots ((w.st parent).prio) := by
        simpa [w', hp, tmb_snoc_prio_self w host msg] using tombs_plain ((w.st host).prio) msg ht
      rw [hslots] at hqmem
      exact hH.legalTomb parent name k ((tmb_queued_iff w parent name k).mpr hqmem) hidx
    · have hslots : tombSlots ((w'.st parent).prio) = tombSlots ((w.st parent).prio) := by
        have heq := tmb_snoc_prio_other w host msg parent hp
        simp [w', heq]
      rw [hslots] at hqmem
      exact hH.legalTomb parent name k ((tmb_queued_iff w parent name k).mpr hqmem) hidx
  · intro parent c hc hchild hhold hnote
    rw [lifeHold_eq (w'.st c) (w.st c) (hlife c)] at hhold
    rw [isChild_eq w w' parent c (hpar c)] at hchild
    have hfresh := hH.fresh parent c (by simpa [w', hros] using hc) hchild hhold hnote
    cases c with
    | core _ => trivial
    | peer n k g =>
      dsimp at hfresh
      cases hbit : slotTombstoneQueued w' parent n k with
      | false => exact hbit
      | true =>
        have hq := (tmb_queued_iff w' parent n k).mp hbit
        have hslots : tombSlots ((w'.st parent).prio) = tombSlots ((w.st parent).prio) := by
          by_cases hp : parent = host
          · simpa [w', hp, tmb_snoc_prio_self w host msg] using tombs_plain ((w.st host).prio) msg ht
          · have heq := tmb_snoc_prio_other w host msg parent hp
            simp [w', heq]
        rw [hslots] at hq
        have holdq := (tmb_queued_iff w parent n k).mpr hq
        rw [holdq] at hfresh
        cases hfresh
  · intro c1 c2 hc1 hc2 ho1 ho2 hslot hpa
    rw [occupant_eq (w'.st c1) (w.st c1) (hlife c1)] at ho1
    rw [occupant_eq (w'.st c2) (w.st c2) (hlife c2)] at ho2
    exact hH.occ c1 c2 (by simpa [w', hros] using hc1) (by simpa [w', hros] using hc2) ho1 ho2 hslot
      ((hpar c1).symm.trans (hpa.trans (hpar c2)))
  · intro name
    simpa [w', hpar (.core name)] using hH.rooted name
  · intro parent name
    by_cases hp : parent = host
    · have hpred : ∀ c, namedChild I.desc w' parent name c = namedChild I.desc w parent name c := by
        intro c
        simp [w', namedChild, childOpen, lifeHold, isChild, hlife c, hpend c, hpar c]
      have hfilter : w'.roster.filter (namedChild I.desc w' parent name) =
          w.roster.filter (namedChild I.desc w parent name) := by
        rw [show w'.roster = w.roster from hros]
        apply List.filter_congr
        intro c _
        exact hpred c
      have htombs : namedTombs ((w'.st parent).prio) name = namedTombs ((w.st parent).prio) name := by
        simpa [w', hp, namedTombs, tmb_snoc_prio_self w host msg, tombs_plain _ msg ht]
      have hopen : namedOpen I.desc w' parent name = namedOpen I.desc w parent name := by
        simp [namedOpen, hfilter, htombs]
      simpa [w', hopen, hN] using hH.census parent name
    · have hprio : (w'.st parent).prio = (w.st parent).prio :=
        tmb_snoc_prio_other w host msg parent hp
      have hopen := namedOpen_cast I.desc w w' parent hros hlife hpend hpar hprio name
      simpa [w', hopen, hN] using hH.census parent name
  · intro i m hm htm
    by_cases hi : i = host
    · have hm' : m ∈ (w.st host).prio ++ [msg] := by simpa [w', hi, tmb_snoc_prio_self w host msg] using hm
      simp [List.mem_append, List.mem_singleton] at hm'
      cases hm' with
      | inl holdm => exact hH.tombHere host m holdm htm
      | inr heq => simp [heq, ht] at htm
    · exact hH.tombHere i m (by simpa [w', tmb_snoc_prio_other w host msg i hi] using hm) htm

/-- `placePeer` is one new actor. The caller supplies the slot and population
facts; installing the actor does not disturb anyone else's lane. -/
theorem hold_place (I : Impl) (w : World) (hH : Hold I w) (template : String) (k : Nat)
    (initial : String) (parent : Option InstId) (next : World → World)
    (hpre : w.crashed = false)
    (hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed)
    (hrole : ∃ t, templateOf I.desc template = some t ∧ t.multiplicity = .perPeer)
    (hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer template k (maxGen w template k)) c = false)
    (hfit : ∀ par, parent = some par →
      notifies I.desc (InstId.peer template k (maxGen w template k)) = true →
      slotIndexed I.desc par template = true → (template, k) ∈ legalSlots I.desc par w.N)
    (hfree : ∀ par, parent = some par → slotTombstoneQueued w par template k = false)
    (hcensus : ∀ par name,
      namedOpen I.desc (placePeer I w template k initial parent next) par name ≤
        nameBudget I.desc par w.N name) :
    Hold I (placePeer I w template k initial parent next) := by
  let id := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  let base := { w with roster := w.roster ++ [id] }
  let mid := next base
  let planted := setActor mid id born
  let w' := readCells I.desc planted id
  have hw' : placePeer I w template k initial parent next = w' := by
    simp [placePeer, id, born, base, mid, planted, w']
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    intro i
    rw [show w'.st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    rw [show w'.roster = planted.roster from cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hNw : w'.N = w.N := by
    rw [show w'.N = planted.N from cellsN I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.2.1, base]
  have hcrash : w'.crashed = false := by
    have hc1 : w'.crashed = planted.crashed := cellsCrash I.desc planted id
    have hc2 : planted.crashed = mid.crashed := by unfold planted setActor; rfl
    have hc3 : mid.crashed = base.crashed := (hnext base id).2.2.2
    have hc4 : base.crashed = false := by unfold base; exact hpre
    exact hc1.trans (hc2.trans (hc3.trans hc4))
  have hlives : born.life = .alive := by simp [born, bornActor, withKeyTokens]
  have hprios : born.prio = [] := by simp [born, bornActor, withKeyTokens]
  have hpends : born.pendingTombstone = false := by simp [born, bornActor, withKeyTokens]
  have hph : phaseDeclared I (tname id) born.phase := by
    simp [born, bornActor, withKeyTokens, phaseDeclared]
  have hrole' : ∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = tmb_role id := by
    simpa [id, tname, tmb_role] using hrole
  have hlegal : ∀ par, isChild w' par id = true → lifeHold born = true →
      notifies I.desc id = true →
      match id with
      | .peer n key _ => slotIndexed I.desc par n = true → (n, key) ∈ legalSlots I.desc par w'.N
      | .core _ => True := by
    intro par hchild _ hnote
    have hpar : born.parent = some par := by
      have hb : born.parent = parent := by simp [born]
      have hstId : w'.st id = born := by rw [hst id]; simp
      rw [isChild, hstId, hb] at hchild
      cases parent with
      | none => simp at hchild
      | some p =>
        simp [Bool.and_eq_true] at hchild
        have heq : p = par := by simpa [beq_iff_eq] using hchild.1
        simp [born, heq]
    intro hidx
    simpa [id, hNw] using hfit par hpar hnote hidx
  have hfreshB : ∀ par, isChild w' par id = true → lifeHold born = true →
      notifies I.desc id = true →
      match id with
      | .peer n key _ => slotTombstoneQueued w' par n key = false
      | .core _ => True := by
    intro par hchild _ hnote
    have hpar : born.parent = some par := by
      have hb : born.parent = parent := by simp [born]
      have hstId : w'.st id = born := by rw [hst id]; simp
      rw [isChild, hstId, hb] at hchild
      cases parent with
      | none => simp at hchild
      | some p =>
        simp [Bool.and_eq_true] at hchild
        have heq : p = par := by simpa [beq_iff_eq] using hchild.1
        simp [born, heq]
    have holdq := hfree par hpar
    have hprio : (w'.st par).prio = (w.st par).prio := by
      have hne : par ≠ id := by
        have hb : born.parent = parent := by simp [born]
        have hstId : w'.st id = born := by rw [hst id]; simp
        rw [isChild, hstId, hb] at hchild
        cases parent with
        | none => simp at hchild
        | some p =>
          simp [Bool.and_eq_true] at hchild
          intro heq
          simp [heq] at hchild
      rw [hst par]
      simp [hne]
    simpa [id, slotTombstoneQueued, hprio] using holdq
  have hcens : ∀ par name, namedOpen I.desc w' par name ≤ nameBudget I.desc par w'.N name := by
    intro par name
    simpa [hw', hNw] using hcensus par name
  exact (hw'.symm ▸
    hold_born I w hH id born w' hpre hst hros hNw hcrash hlives hprios hpends hph hrole'
      hocc hlegal hfreshB (fun name hcore => by simp [id] at hcore) hcens)

theorem filter_snoc_on {α : Type} (p : α → Bool) (xs : List α) (a : α) (ha : p a = true) :
    ((xs ++ [a]).filter p).length = (xs.filter p).length + 1 := by
  induction xs with
  | nil => simp [ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.filter_cons]
    by_cases hp : p x = true
    · rw [ite_eq_left hp, ite_eq_left hp, List.length_cons, List.length_cons, ih]
    · have hpf : p x = false := by
        cases hbit : p x
        · rfl
        · exact absurd hbit hp
      rw [ite_eq_right (by rw [hpf]; decide), ite_eq_right (by rw [hpf]; decide), ih]

theorem filter_snoc_rel {α : Type} (p q : α → Bool) (xs : List α) (a : α)
    (h : ∀ x, x ∈ xs → p x = q x) (ha : p a = true) :
    ((xs ++ [a]).filter p).length = (xs.filter q).length + 1 := by
  induction xs with
  | nil => simp [ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.filter_cons]
    have hx : p x = q x := h x List.mem_cons_self
    have htail : ∀ y, y ∈ xs → p y = q y := fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · have hq : q x = true := by rw [← hx]; exact hp
      rw [ite_eq_left hp, ite_eq_left hq, List.length_cons, List.length_cons, ih htail]
    · have hpf : p x = false := by
        cases hbit : p x
        · rfl
        · exact absurd hbit hp
      have hqf : q x = false := by rw [← hx]; exact hpf
      rw [ite_eq_right (by rw [hpf]; decide), ite_eq_right (by rw [hqf]; decide)]
      exact ih htail

theorem filter_snoc_rel_off {α : Type} (p q : α → Bool) (xs : List α) (a : α)
    (h : ∀ x, x ∈ xs → p x = q x) (ha : p a = false) :
    ((xs ++ [a]).filter p).length = (xs.filter q).length := by
  induction xs with
  | nil => simp [ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.filter_cons]
    have hx : p x = q x := h x List.mem_cons_self
    have htail : ∀ y, y ∈ xs → p y = q y := fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · have hq : q x = true := by rw [← hx]; exact hp
      rw [ite_eq_left hp, ite_eq_left hq, List.length_cons, List.length_cons, ih htail]
    · have hpf : p x = false := by
        cases hbit : p x
        · rfl
        · exact absurd hbit hp
      have hqf : q x = false := by rw [← hx]; exact hpf
      rw [ite_eq_right (by rw [hpf]; decide), ite_eq_right (by rw [hqf]; decide)]
      exact ih htail

/-- A new notifying child of `template` under `par` adds exactly one to that
count. Every other template under the same parent is unchanged. -/
theorem census_born (D : Description) (w w' : World) (id par : InstId) (template : String)
    (hst : ∀ i, w'.st i = if i = id then w'.st id else w.st i)
    (hros : w'.roster = w.roster ++ [id]) (hnew : id ∉ w.roster)
    (hbit : namedChild D w' par template id = true)
    (hprio : (w'.st par).prio = (w.st par).prio) :
    namedOpen D w' par template = namedOpen D w par template + 1 := by
  have hagree : ∀ c, c ∈ w.roster → namedChild D w' par template c = namedChild D w par template c := by
    intro c hc
    have hne : c ≠ id := fun heq => hnew (heq ▸ hc)
    have heq := hst c
    simp [hne] at heq
    simp [namedChild, childOpen, lifeHold, isChild, heq]
  have hfilter := filter_snoc_rel (namedChild D w' par template) (namedChild D w par template)
    w.roster id hagree hbit
  have htombs : namedTombs ((w'.st par).prio) template = namedTombs ((w.st par).prio) template := by
    simp [namedTombs, hprio]
  rw [namedOpen, namedOpen, hros, hfilter, htombs]
  omega

theorem census_born_other (D : Description) (w w' : World) (id par : InstId) (name : String)
    (hst : ∀ i, w'.st i = if i = id then w'.st id else w.st i)
    (hros : w'.roster = w.roster ++ [id]) (hnew : id ∉ w.roster)
    (hbit : namedChild D w' par name id = false)
    (hprio : (w'.st par).prio = (w.st par).prio) :
    namedOpen D w' par name = namedOpen D w par name := by
  have hagree : ∀ c, c ∈ w.roster → namedChild D w' par name c = namedChild D w par name c := by
    intro c hc
    have hne : c ≠ id := fun heq => hnew (heq ▸ hc)
    have heq := hst c
    simp [hne] at heq
    simp [namedChild, childOpen, lifeHold, isChild, heq]
  have hfilter := filter_snoc_rel_off (namedChild D w' par name) (namedChild D w par name)
    w.roster id hagree hbit
  have htombs : namedTombs ((w'.st par).prio) name = namedTombs ((w.st par).prio) name := by
    simp [namedTombs, hprio]
  rw [namedOpen, namedOpen, hros, hfilter, htombs]

/-- A key past every member of a nonempty subtree is not `sameSlot` as any
roster actor. -/
theorem fresh_sameSlot (D : Description) (w : World) (sub template : String) (k : Nat)
    (hsub : sub ≠ "") (htree : templateSubtree D template = sub)
    (hk : k = freshKey D w sub) (c : InstId) (hc : c ∈ w.roster) :
    sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
  cases c with
  | core _ => simp [sameSlot]
  | peer n k' g =>
    by_cases hn : (n == template) = true
    · have hname : n = template := by simpa [beq_iff_eq] using hn
      have hsub' : templateSubtree D n = sub := by simpa [hname] using htree
      have hlt := freshKey_gt D w sub n k' g hsub hsub' hc
      rw [← hk] at hlt
      have hnameB : (template == n) = true := by rw [beq_comm]; exact hn
      have hkb : (k == k') = false := by
        cases hbb : k == k'
        · rfl
        · have heq : k = k' := by simpa [beq_iff_eq] using hbb
          omega
      simp only [sameSlot, hnameB, hkb, Bool.and_false]
    · have hnf : (n == template) = false := by
        cases hbb : n == template
        · rfl
        · exact absurd hbb hn
      have hnameB : (template == n) = false := by rw [beq_comm]; exact hnf
      simp only [sameSlot, hnameB, Bool.false_and]

theorem queued_sender (ms : List Msg) (child : String) (k : Nat)
    (hq : (ms.any fun m =>
      m.tombstone &&
        match m.sender with
        | .peer n key _ => n == child && key == k
        | .core _ => false) = true) :
    ∃ m g, m ∈ ms ∧ m.tombstone = true ∧ m.sender = InstId.peer child k g := by
  induction ms with
  | nil => simp [List.any_nil] at hq
  | cons m ms ih =>
    rw [List.any_cons] at hq
    cases hhead : (m.tombstone &&
        match m.sender with
        | .peer n key _ => n == child && key == k
        | .core _ => false) with
    | true =>
      cases ht : m.tombstone <;> cases hs : m.sender <;> simp [ht, hs, Bool.and_eq_true] at hhead
      rename_i n key g
      have hn : n = child := by simpa [beq_iff_eq] using hhead.1
      have hk : key = k := by simpa [beq_iff_eq] using hhead.2
      exact ⟨m, g, List.mem_cons_self, ht, by simp [hs, hn, hk]⟩
    | false =>
      have htail : (ms.any fun m =>
          m.tombstone &&
            match m.sender with
            | .peer n key _ => n == child && key == k
            | .core _ => false) = true := by
        rw [hhead, Bool.false_or] at hq
        exact hq
      obtain ⟨m0, g, hm, ht, hs⟩ := ih htail
      exact ⟨m0, g, List.mem_cons_of_mem _ hm, ht, hs⟩

theorem may_root_parts (D : Description) (w : World) (template : String) (t : Template)
    (name : String) (ht : templateOf D template = some t)
    (hmay : maySpawnRoot D w template t = true) (hsup : t.supervisor = some name) :
    t.multiplicity = .perPeer ∧ rootOutstanding D w name template < w.N := by
  simp only [maySpawnRoot, hsup, Bool.and_eq_true, decide_eq_true_iff] at hmay
  obtain ⟨⟨⟨hmul, _⟩, _⟩, hlt⟩ := hmay
  refine ⟨?_, hlt⟩
  · cases hm : t.multiplicity with
    | perPeer => rfl
    | one =>
      exfalso
      rw [hm] at hmul
      rw [show (Multiplicity.one == Multiplicity.perPeer) = false from rfl] at hmul
      exact Bool.noConfusion hmul

/-- A supervised root born under its core adds at most one to that core's
count for its own template, and nothing to any other count. The allowance is
`N` when the child notifies and `0` when it does not. -/
theorem census_supervised (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (born : Actor) (template : String) (t : Template) (name : String) (k : Nat)
    (ht : templateOf I.desc template = some t)
    (hsup : t.supervisor = some name) (hlt : rootOutstanding I.desc w name template < w.N)
    (hst : ∀ i, w'.st i = if i = id then born else w.st i)
    (hros : w'.roster = w.roster ++ [id]) (hnew : id ∉ w.roster)
    (hid : id = InstId.peer template k (maxGen w template k))
    (hparent : born.parent = some (.core name)) (hlive : born.life = .alive)
    (hbornPrio : born.prio = (w.st id).prio)
    (hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio) :
    ∀ par nm, namedOpen I.desc w' par nm ≤ nameBudget I.desc par w.N nm := by
  have hst' : ∀ i, w'.st i = if i = id then w'.st id else w.st i := by
    intro i
    by_cases hi : i = id
    · have hborn : w'.st id = born := by simpa [hi] using hst id
      simp [hi, hborn]
    · simp [hi, hst i]
  have hself : w'.st id = born := by simpa using hst id
  intro par nm
  by_cases hpar : par = InstId.core name
  · rw [hpar]
    have hparentPrio : (w'.st (.core name)).prio = (w.st (.core name)).prio := by
      have hne : InstId.core name ≠ id := by
        intro heq
        simp [hid] at heq
      exact hprios (.core name) hne
    by_cases hnm : nm = template
    · rw [hnm]
      by_cases hnote : notifies I.desc id = true
      · have hne : id ≠ InstId.core name := by
          intro heq
          simp [hid] at heq
        have hchild := isChild_recorded w' (.core name) id (by rw [hself]; exact hparent) hne
        have hlife : lifeHold (w'.st id) = true := by
          rw [lifeHold, hself, hlive]
          simp
        have hopen : childOpen I.desc w' (.core name) id = true := by
          unfold childOpen
          rw [hchild, hlife, hnote]
          rfl
        have hbit : namedChild I.desc w' (.core name) template id = true := by
          unfold namedChild
          rw [hopen, hid]
          simp
        have hcount := census_born I.desc w w' id (.core name) template hst' hros hnew hbit hparentPrio
        have hroot := named_le_root I w hH name template
        have hkeep : (t.tombstone != "") = true := by
          have hn := hnote
          rw [hid, notifies, tname, ht] at hn
          exact hn
        have hbudget : nameBudget I.desc (.core name) w.N template = w.N := by
          have hk : tmb_keep (.core name) t = true := by
            unfold tmb_keep
            simp only [supNamed, hsup, tname]
            rw [(beq_iff_eq).mpr (rfl : name = name), hkeep, Bool.true_and]
          simp only [nameBudget, ht, tmb_leg, hk]
          rfl
        rw [hcount, hbudget]
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hroot hlt)
      · have hbit : namedChild I.desc w' (.core name) template id = false := by
          have hnf : notifies I.desc id = false := by
            cases hn : notifies I.desc id with
            | false => rfl
            | true => exact absurd hn hnote
          unfold namedChild childOpen
          rw [hnf]
          simp only [Bool.and_false, Bool.false_and]
        have hcount := census_born_other I.desc w w' id (.core name) template hst' hros hnew hbit
          hparentPrio
        simpa [hcount] using hH.census (.core name) template
    · have hbit : namedChild I.desc w' (.core name) nm id = false := by
        unfold namedChild
        rw [hid]
        have hbb : (template == nm) = false := by
          rw [beq_comm]
          cases hbeq : (nm == template) with
          | false => rfl
          | true => exact absurd ((beq_iff_eq).mp hbeq) hnm
        simp only [hbb, Bool.and_false]
      have hcount := census_born_other I.desc w w' id (.core name) nm hst' hros hnew hbit hparentPrio
      simpa [hcount] using hH.census (.core name) nm
  · have hbit : namedChild I.desc w' par nm id = false := by
      have hchild : isChild w' par id = false := by
        unfold isChild
        rw [hself, hparent]
        have hbb : (InstId.core name == par) = false := by
          cases hbeq : (InstId.core name == par) with
          | false => rfl
          | true => exact absurd ((beq_iff_eq).mp hbeq).symm hpar
        simp only [hbb, Bool.false_and]
      unfold namedChild childOpen
      rw [hchild]
      simp only [Bool.false_and]
    have hprio : (w'.st par).prio = (w.st par).prio := by
      by_cases heq : par = id
      · rw [heq, hself]
        exact hbornPrio
      · exact hprios par heq
    have hcount := census_born_other I.desc w w' id par nm hst' hros hnew hbit hprio
    simpa [hcount] using hH.census par nm

/-- A scheduler spawn of a nonempty subtree under a live core installs one
fresh root and keeps the tombstone count. The key is past every member of
the subtree, so it is not a slot anyone on the roster still holds. -/
theorem hold_spawn_core (I : Impl) (w : World) (hH : Hold I w) (template : String)
    (t : Template) (name : String) (ht : templateOf I.desc template = some t)
    (hmay : maySpawnRoot I.desc w template t = true) (hsup : t.supervisor = some name)
    (hsub : t.subtree ≠ "") (hpre : w.crashed = false)
    (hoff : (w.st (InstId.peer template (freshKey I.desc w t.subtree)
        (maxGen w template (freshKey I.desc w t.subtree)))).prio = []) :
    Hold I (placePeer I w template (freshKey I.desc w t.subtree) t.initial (some (.core name))
      (fun u => { u with nextKey := fun s =>
        if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })) := by
  have ⟨hmul, hlt⟩ := may_root_parts I.desc w template t name ht hmay hsup
  let k := freshKey I.desc w t.subtree
  let id := InstId.peer template k (maxGen w template k)
  let parent : Option InstId := some (.core name)
  let next : World → World := fun u =>
    { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
  let born := { bornActor I.desc w template k t.initial with parent := parent }
  let w' := placePeer I w template k t.initial parent next
  have htree : templateSubtree I.desc template = t.subtree := by simp [templateSubtree, ht]
  have hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed := by
    intro u i
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    intro i
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).roster = planted.roster from cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hnew : id ∉ w.roster := gen_fresh w template k
  have hparent : born.parent = some (.core name) := by simp [born, parent]
  have hlive : born.life = .alive := by simp [born, bornActor, withKeyTokens]
  have hbornPrio : born.prio = (w.st id).prio := by
    have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
    simpa [hp, id, k, hoff]
  have hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio := by
    intro i hne
    have h := hst i
    simp [hne] at h
    rw [h]
  have hcensus := census_supervised I w w' hH id born template t name k ht hsup hlt hst hros
    hnew rfl hparent hlive hbornPrio hprios
  have hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
    intro c hc _
    exact fresh_sameSlot I.desc w t.subtree template k hsub htree rfl c hc
  have hfit : ∀ par, parent = some par →
      notifies I.desc (InstId.peer template k (maxGen w template k)) = true →
      slotIndexed I.desc par template = true → (template, k) ∈ legalSlots I.desc par w.N := by
    intro par hpar _ hidx
    have heq : InstId.core name = par := by simpa [parent] using hpar
    rw [← heq] at hidx
    simp [slotIndexed] at hidx
  have hfree : ∀ par, parent = some par → slotTombstoneQueued w par template k = false := by
    intro par hpar
    have heq : InstId.core name = par := by simpa [parent] using hpar
    rw [← heq]
    cases hq : slotTombstoneQueued w (.core name) template k with
    | false => rfl
    | true =>
      have hq' : ((w.st (.core name)).prio.any fun m =>
          m.tombstone &&
            match m.sender with
            | .peer n key _ => n == template && key == k
            | .core _ => false) = true := by
        unfold slotTombstoneQueued at hq
        exact hq
      obtain ⟨m, g, hm, htomb, hs⟩ := queued_sender (w.st (.core name)).prio template k hq'
      have hmem := hH.tombHere (.core name) m hm htomb
      have hslot := fresh_sameSlot I.desc w t.subtree template k hsub htree rfl m.sender hmem
      rw [hs] at hslot
      simp [sameSlot] at hslot
  have hHold := hold_place I w hH template k t.initial parent next hpre hnext
    ⟨t, ht, hmul⟩ hocc hfit hfree (by simpa [w', k] using hcensus)
  simpa [w', k, parent, next] using hHold

theorem lane_absent (ms : List Msg) (label : String)
    (h : (ms.any fun p => p.label == label) = false) : label ∉ tmb_laneLabels ms := by
  intro hmem
  simp [tmb_laneLabels, List.mem_map] at hmem
  obtain ⟨m, hm, hl⟩ := hmem
  have hany : (ms.any fun p => p.label == label) = true :=
    _root_.List.any_eq_true.mpr ⟨m, hm.1, by rw [hl]; exact (beq_iff_eq).mpr rfl⟩
  simp [hany] at h

/-- Re-arming a label already on the lane leaves the count alone. A new label
appends when the lane has room, and a full lane crashes. Neither grows a
tombstone count past the births already accounted for. -/
theorem hold_self (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor)
    (k : Cont) (label : String) (es : List Eff) (hpre : w.crashed = false)
    (ha : a = w.st id) (hlive : a.life = .alive) (hph : a.phase = .run k)
    (hk : k.rest = .selfSchedule label :: es) (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have htail : ContDeclared I (tname id) k' := ContDeclared.after I (tname id) k _ _ hk hdec
  have hphase : phaseDeclared I (tname id) (proceed a k').phase := by
    cases hr : k'.rest with
    | nil => simp [proceed, hr, phaseDeclared]
    | cons _ _ =>
      simp [proceed, hr, phaseDeclared]
      exact htail
  have hpresent : (a.prio.any fun p => p.label == label) = true →
      Hold I (setActor w id (proceed a k')) := by
    intro _
    have hph' : id ∈ w.roster → phaseDeclared I (tname id) (proceed (w.st id) k').phase := by
      intro _
      simpa [ha] using hphase
    simpa [ha] using hold_proceed I w hH id k' hpre hph'
  by_cases hqueued : (a.prio.any fun p => p.label == label) = true
  · have hrun : execRun I w id a k = setActor w id (proceed a k') := by
      simp [execRun, hgo, hk, hqueued, k']
    exact hrun ▸ hpresent hqueued
  · have hfree : (a.prio.any fun p => p.label == label) = false := by
      cases hbit : (a.prio.any fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hbit hqueued
    let msg : Msg :=
      { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
    have htomb : msg.tombstone = false := by simp [msg]
    have hlabel : msg.label ∈ prioLabels I (tname id) := by
      have hmem : label ∈ selfLabels k.rest := by rw [hk]; exact tmb_self_head label es
      simpa [msg] using hdec.rest.sched label hmem
    by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
    · have hrun : execRun I w id a k =
          setActor w id (proceed { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 } k') := by
        simp [execRun, hgo, hk, hfree, hroom, upsertPrio, msg, k']
      have hnew : msg.label ∉ tmb_laneLabels ((w.st id).prio) := by
        rw [← ha]
        simpa [msg] using lane_absent a.prio label hfree
      have hH' := hold_plain I w hH id msg hpre (by simpa [ha] using hlive) htomb hlabel hnew
      let updated := { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 }
      have hsame : (tmb_snoc w id msg).st id = updated := by
        simp [tmb_snoc, setActor, updated, ha, msg]
      have hkeep := proceed_keep updated k'
      have hphEq : (proceed updated k').phase = (proceed a k').phase := by
        cases hr : k'.rest <;> simp [proceed, hr]
      have hH'' := hold_set I (tmb_snoc w id msg) hH' id (proceed updated k')
        (by rw [hkeep.1, hsame])
        (by rw [hkeep.2.1, hsame])
        (by rw [hkeep.2.2, hsame])
        (by rw [proceed_parent updated k', hsame])
        (fun _ => by simpa [hphEq] using hphase) hpre
      have heq : setActor (tmb_snoc w id msg) id (proceed updated k') =
          setActor w id (proceed updated k') := by
        simp [tmb_snoc, setActor, updated]
        funext i
        by_cases hi : i = id <;> simp [hi]
      simpa [hrun, updated] using (heq ▸ hH'')
    · have hrun : execRun I w id a k = crashWorld w := by
        simp [execRun, hgo, hk, hfree, hroom]
      exact hrun ▸ hold_crash I w hH

theorem hold_idle (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive) (hk : k.rest = []) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  have hrun : execRun I w id a k =
      setActor w id { a with phase := .idle, typestate := k.toState } := by
    simp [execRun, hgo, hk]
  exact hrun ▸ hold_set I w hH id { a with phase := .idle, typestate := k.toState }
    (by simp [ha]) (by simp [ha]) (by simp [ha]) (by simp [ha])
    (fun _ => phaseDeclared_idle I (tname id)) hpre

theorem hold_internal (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (es : List Eff) (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .internal :: es) (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have htail := ContDeclared.after I (tname id) k _ _ hk hdec
  have hrun : execRun I w id a k = setActor w id { a with phase := .awaitEffect k' } := by
    simp [execRun, hgo, hk, k']
  exact hrun ▸ hold_set I w hH id { a with phase := .awaitEffect k' }
    (by simp [ha]) (by simp [ha]) (by simp [ha]) (by simp [ha])
    (fun _ => by simpa [phaseDeclared] using htail) hpre

theorem hold_peer (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (onTimeout es : List Eff) (hpre : w.crashed = false) (ha : a = w.st id)
    (hlive : a.life = .alive) (hk : k.rest = .peer onTimeout :: es)
    (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have hwait := ContDeclared.peerWait I (tname id) k onTimeout es hk hdec
  have hrun : execRun I w id a k =
      setActor w id { a with phase := .awaitPeer { k' with onTimeout := onTimeout } } := by
    simp [execRun, hgo, hk, k']
  exact hrun ▸ hold_set I w hH id { a with phase := .awaitPeer { k' with onTimeout := onTimeout } }
    (by simp [ha]) (by simp [ha]) (by simp [ha]) (by simp [ha])
    (fun _ => by simpa [phaseDeclared, k'] using hwait) hpre

theorem filter_snoc_off {α : Type} (p : α → Bool) (xs : List α) (a : α) (ha : p a = false) :
    ((xs ++ [a]).filter p).length = (xs.filter p).length := by
  induction xs with
  | nil => simp [ha]
  | cons x xs ih =>
    simp only [List.cons_append, List.filter_cons]
    by_cases hp : p x = true
    · rw [ite_eq_left hp, ite_eq_left hp, List.length_cons, List.length_cons, ih]
    · have hpf : p x = false := by
        cases hbit : p x
        · rfl
        · exact absurd hbit hp
      rw [ite_eq_right (by rw [hpf]; decide), ite_eq_right (by rw [hpf]; decide), ih]

/-- A birth with no recorded parent is not anyone's child, so no template
count moves. -/
theorem census_free (I : Impl) (w w' : World) (hH : Hold I w) (id : InstId)
    (born : Actor) (template : String) (k : Nat)
    (hst : ∀ i, w'.st i = if i = id then born else w.st i)
    (hros : w'.roster = w.roster ++ [id]) (hnew : id ∉ w.roster)
    (hparent : born.parent = none) (hbornPrio : born.prio = (w.st id).prio)
    (hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio) :
    ∀ par nm, namedOpen I.desc w' par nm ≤ nameBudget I.desc par w.N nm := by
  have hst' : ∀ i, w'.st i = if i = id then w'.st id else w.st i := by
    intro i
    by_cases hi : i = id
    · have hborn : w'.st id = born := by simpa [hi] using hst id
      simp [hi, hborn]
    · simp [hi, hst i]
  have hself : w'.st id = born := by simpa using hst id
  intro par nm
  have hbit : namedChild I.desc w' par nm id = false := by
    have hchild : isChild w' par id = false := by
      unfold isChild
      rw [hself, hparent]
    unfold namedChild childOpen
    rw [hchild]
    simp only [Bool.false_and]
  have hprio : (w'.st par).prio = (w.st par).prio := by
    by_cases heq : par = id
    · rw [heq, hself]
      exact hbornPrio
    · exact hprios par heq
  have hcount := census_born_other I.desc w w' id par nm hst' hros hnew hbit hprio
  simpa [hcount] using hH.census par nm

/-- `maySpawnRoot` for a template with no supervisor. -/
theorem may_free_parts (D : Description) (w : World) (template : String) (t : Template)
    (hmay : maySpawnRoot D w template t = true) (hsup : t.supervisor = none) :
    t.multiplicity = .perPeer ∧ loneOutstanding D w template < w.N := by
  simp only [maySpawnRoot, hsup, Bool.and_eq_true, decide_eq_true_iff] at hmay
  obtain ⟨⟨⟨hmul, _⟩, _⟩, hlt⟩ := hmay
  refine ⟨?_, hlt⟩
  · cases hm : t.multiplicity with
    | perPeer => rfl
    | one =>
      exfalso
      rw [hm] at hmul
      rw [show (Multiplicity.one == Multiplicity.perPeer) = false from rfl] at hmul
      exact Bool.noConfusion hmul

/-- A scheduler spawn with no supervisor and a nonempty subtree installs one
fresh root. It records no parent, so it is not counted on any lane. -/
theorem hold_spawn_free (I : Impl) (w : World) (hH : Hold I w) (template : String)
    (t : Template) (ht : templateOf I.desc template = some t)
    (hmay : maySpawnRoot I.desc w template t = true) (hsup : t.supervisor = none)
    (hsub : t.subtree ≠ "") (hpre : w.crashed = false)
    (hoff : (w.st (InstId.peer template (freshKey I.desc w t.subtree)
        (maxGen w template (freshKey I.desc w t.subtree)))).prio = []) :
    Hold I (placePeer I w template (freshKey I.desc w t.subtree) t.initial none
      (fun u => { u with nextKey := fun s =>
        if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })) := by
  have ⟨hmul, _⟩ := may_free_parts I.desc w template t hmay hsup
  let k := freshKey I.desc w t.subtree
  let id := InstId.peer template k (maxGen w template k)
  let parent : Option InstId := none
  let next : World → World := fun u =>
    { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
  let born := { bornActor I.desc w template k t.initial with parent := parent }
  let w' := placePeer I w template k t.initial parent next
  have htree : templateSubtree I.desc template = t.subtree := by simp [templateSubtree, ht]
  have hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed := by
    intro u i
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    intro i
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).roster = planted.roster from
      cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hnew : id ∉ w.roster := gen_fresh w template k
  have hparent : born.parent = none := by simp [born, parent]
  have hbornPrio : born.prio = (w.st id).prio := by
    have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
    simpa [hp, id, k, hoff]
  have hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio := by
    intro i hne
    have h := hst i
    simp [hne] at h
    rw [h]
  have hcensus := census_free I w w' hH id born template k hst hros hnew hparent hbornPrio hprios
  have hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
    intro c hc _
    exact fresh_sameSlot I.desc w t.subtree template k hsub htree rfl c hc
  have hfit : ∀ par, parent = some par →
      notifies I.desc (InstId.peer template k (maxGen w template k)) = true →
      slotIndexed I.desc par template = true → (template, k) ∈ legalSlots I.desc par w.N := by
    intro par hpar
    simp [parent] at hpar
  have hfree : ∀ par, parent = some par → slotTombstoneQueued w par template k = false := by
    intro par hpar
    simp [parent] at hpar
  have hHold := hold_place I w hH template k t.initial parent next hpre hnext
    ⟨t, ht, hmul⟩ hocc hfit hfree (by simpa [w', k] using hcensus)
  simpa [w', k, parent, next] using hHold

/-- An unsupervised empty subtree takes keys from `nextIx`, so the next one
is not a slot any roster actor of that template still holds. -/
theorem ix_sameSlot (I : Impl) (w : World) (hI : IxPast I w) (template : String)
    (t : Template) (k : Nat) (ht : templateOf I.desc template = some t)
    (hsup : t.supervisor = none) (hsub : t.subtree = "") (hk : k = w.nextIx template)
    (c : InstId) (hc : c ∈ w.roster) :
    sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
  cases c with
  | core _ => simp [sameSlot]
  | peer n k' g =>
    by_cases hn : (n == template) = true
    · have hname : n = template := by simpa [beq_iff_eq] using hn
      have hlt : k' < k := by
        have hmem : InstId.peer n k' g ∈ w.roster := hc
        rw [hname] at hmem
        simpa [hk] using hI template k' g hmem t ht hsup hsub
      have hnameB : (template == n) = true := by rw [beq_comm]; exact hn
      have hkb : (k == k') = false := by
        cases hbb : k == k'
        · rfl
        · have heq : k = k' := by simpa [beq_iff_eq] using hbb
          omega
      simp only [sameSlot, hnameB, hkb, Bool.and_false]
    · have hnf : (n == template) = false := by
        cases hbb : n == template
        · rfl
        · exact absurd hbb hn
      have hnameB : (template == n) = false := by rw [beq_comm]; exact hnf
      simp only [sameSlot, hnameB, Bool.false_and]

/-- A scheduler spawn with no supervisor and an empty subtree installs one
root at `nextIx`. The key is past every earlier birth of that template. -/
theorem hold_spawn_ix (I : Impl) (w : World) (hH : Hold I w) (hI : IxPast I w)
    (template : String) (t : Template) (ht : templateOf I.desc template = some t)
    (hmay : maySpawnRoot I.desc w template t = true) (hsup : t.supervisor = none)
    (hsub : t.subtree = "") (hpre : w.crashed = false)
    (hoff : (w.st (InstId.peer template (w.nextIx template)
        (maxGen w template (w.nextIx template)))).prio = []) :
    Hold I (placePeer I w template (w.nextIx template) t.initial none
      (fun u => { u with nextIx := fun n =>
        if n = template then w.nextIx template + 1 else u.nextIx n })) := by
  have ⟨hmul, _⟩ := may_free_parts I.desc w template t hmay hsup
  let k := w.nextIx template
  let id := InstId.peer template k (maxGen w template k)
  let parent : Option InstId := none
  let next : World → World := fun u =>
    { u with nextIx := fun n => if n = template then k + 1 else u.nextIx n }
  let born := { bornActor I.desc w template k t.initial with parent := parent }
  let w' := placePeer I w template k t.initial parent next
  have hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed := by
    intro u i
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    intro i
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).roster = planted.roster from
      cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hnew : id ∉ w.roster := gen_fresh w template k
  have hparent : born.parent = none := by simp [born, parent]
  have hbornPrio : born.prio = (w.st id).prio := by
    have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
    simpa [hp, id, k, hoff]
  have hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio := by
    intro i hne
    have h := hst i
    simp [hne] at h
    rw [h]
  have hcensus := census_free I w w' hH id born template k hst hros hnew hparent hbornPrio hprios
  have hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
    intro c hc _
    exact ix_sameSlot I w hI template t k ht hsup hsub rfl c hc
  have hfit : ∀ par, parent = some par →
      notifies I.desc (InstId.peer template k (maxGen w template k)) = true →
      slotIndexed I.desc par template = true → (template, k) ∈ legalSlots I.desc par w.N := by
    intro par hpar
    simp [parent] at hpar
  have hfree : ∀ par, parent = some par → slotTombstoneQueued w par template k = false := by
    intro par hpar
    simp [parent] at hpar
  have hHold := hold_place I w hH template k t.initial parent next hpre hnext
    ⟨t, ht, hmul⟩ hocc hfit hfree (by simpa [w', k] using hcensus)
  simpa [w', k, parent, next] using hHold

/-- Empty-subtree roots under a core share `nextKey ""`. The next key is not a
slot any of them still holds. -/
theorem root_sameSlot (I : Impl) (w : World) (hR : RootPast I w) (template : String)
    (t : Template) (k : Nat) (ht : templateOf I.desc template = some t)
    (hsub : t.subtree = "") (hroot : rootOf I.desc t = true)
    (hsup : ∃ name, t.supervisor = some name) (hk : k = w.nextKey "")
    (c : InstId) (hc : c ∈ w.roster) :
    sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
  cases c with
  | core _ => simp [sameSlot]
  | peer n k' g =>
    by_cases hn : (n == template) = true
    · have hname : n = template := by simpa [beq_iff_eq] using hn
      rcases hsup with ⟨name, hnameSup⟩
      have hlt : k' < k := by
        rw [hname] at hc
        simpa [hk] using hR template k' g hc t ht hsub hroot name hnameSup
      have hnameB : (template == n) = true := by rw [beq_comm]; exact hn
      have hkb : (k == k') = false := by
        cases hbb : k == k'
        · rfl
        · have heq : k = k' := by simpa [beq_iff_eq] using hbb
          omega
      simp only [sameSlot, hnameB, hkb, Bool.and_false]
    · have hnf : (n == template) = false := by
        cases hbb : n == template
        · rfl
        · exact absurd hbb hn
      have hnameB : (template == n) = false := by rw [beq_comm]; exact hnf
      simp only [sameSlot, hnameB, Bool.false_and]

/-- A scheduler spawn of an empty subtree under a live core installs one root
at `nextKey ""`. The key is past every earlier empty-subtree root. -/
theorem hold_spawn_root (I : Impl) (w : World) (hH : Hold I w) (hR : RootPast I w)
    (template : String) (t : Template) (name : String)
    (ht : templateOf I.desc template = some t)
    (hmay : maySpawnRoot I.desc w template t = true) (hsup : t.supervisor = some name)
    (hsub : t.subtree = "") (hpre : w.crashed = false)
    (hoff : (w.st (InstId.peer template (freshKey I.desc w "")
        (maxGen w template (freshKey I.desc w "")))).prio = []) :
    Hold I (placePeer I w template (freshKey I.desc w "") t.initial (some (.core name))
      (fun u => { u with nextKey := fun s =>
        if s = "" then freshKey I.desc w "" + 1 else u.nextKey s })) := by
  have ⟨hmul, hlt⟩ := may_root_parts I.desc w template t name ht hmay hsup
  have hroot : rootOf I.desc t = true := by
    simp only [maySpawnRoot, hsup, Bool.and_eq_true, decide_eq_true_iff] at hmay
    obtain ⟨⟨⟨_, hroot⟩, _⟩, _⟩ := hmay
    exact hroot
  let k := freshKey I.desc w ""
  let id := InstId.peer template k (maxGen w template k)
  let parent : Option InstId := some (.core name)
  let next : World → World := fun u =>
    { u with nextKey := fun s => if s = "" then k + 1 else u.nextKey s }
  let born := { bornActor I.desc w template k t.initial with parent := parent }
  let w' := placePeer I w template k t.initial parent next
  have hk : k = w.nextKey "" := freshKey_empty I.desc w
  have hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed := by
    intro u i
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    intro i
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).roster = planted.roster from
      cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hnew : id ∉ w.roster := gen_fresh w template k
  have hparent : born.parent = some (.core name) := by simp [born, parent]
  have hlive : born.life = .alive := by simp [born, bornActor, withKeyTokens]
  have hbornPrio : born.prio = (w.st id).prio := by
    have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
    simpa [hp, id, k, hoff]
  have hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio := by
    intro i hne
    have h := hst i
    simp [hne] at h
    rw [h]
  have hcensus := census_supervised I w w' hH id born template t name k ht hsup hlt hst hros
    hnew rfl hparent hlive hbornPrio hprios
  have hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer template k (maxGen w template k)) c = false := by
    intro c hc _
    exact root_sameSlot I w hR template t k ht hsub hroot ⟨name, hsup⟩ hk c hc
  have hfit : ∀ par, parent = some par →
      notifies I.desc (InstId.peer template k (maxGen w template k)) = true →
      slotIndexed I.desc par template = true → (template, k) ∈ legalSlots I.desc par w.N := by
    intro par hpar _ hidx
    have heq : InstId.core name = par := by simpa [parent] using hpar
    rw [← heq] at hidx
    simp [slotIndexed] at hidx
  have hfree : ∀ par, parent = some par → slotTombstoneQueued w par template k = false := by
    intro par hpar
    have heq : InstId.core name = par := by simpa [parent] using hpar
    rw [← heq]
    cases hq : slotTombstoneQueued w (.core name) template k with
    | false => rfl
    | true =>
      have hq' : ((w.st (.core name)).prio.any fun m =>
          m.tombstone &&
            match m.sender with
            | .peer n key _ => n == template && key == k
            | .core _ => false) = true := by
        unfold slotTombstoneQueued at hq
        exact hq
      obtain ⟨m, g, hm, htomb, hs⟩ := queued_sender (w.st (.core name)).prio template k hq'
      have hmem := hH.tombHere (.core name) m hm htomb
      have hslot := root_sameSlot I w hR template t k ht hsub hroot ⟨name, hsup⟩ hk
        m.sender hmem
      rw [hs] at hslot
      simp [sameSlot] at hslot
  have hHold := hold_place I w hH template k t.initial parent next hpre hnext
    ⟨t, ht, hmul⟩ hocc hfit hfree (by simpa [w', k] using hcensus)
  simpa [w', k, parent, next, hsub] using hHold

/-- Every scheduler spawn that the runtime accepts keeps the tombstone count.
An empty subtree takes its key from `nextIx` or `nextKey ""`; a nonempty
subtree takes a fresh subtree key. A birth the guard refuses is not a step. -/
theorem hold_spawn (I : Impl) (w w' : World) (hH : Hold I w) (hI : IxPast I w)
    (hR : RootPast I w) (template : String) (hpre : w.crashed = false)
    (hoff : ∀ id, id ∉ w.roster → (w.st id).prio = [])
    (h : spawn I w template = some w') : Hold I w' := by
  cases ht : templateOf I.desc template with
  | none => simp [spawn, ht] at h
  | some t =>
    simp only [spawn, ht] at h
    split at h
    · rename_i hmay
      split at h
      · rename_i name hsup
        by_cases hsub : t.subtree = ""
        · simp [hsub] at h
          have hstep := h.symm
          have hoff' : (w.st (InstId.peer template (freshKey I.desc w "")
              (maxGen w template (freshKey I.desc w "")))).prio = [] :=
            hoff _ (gen_fresh _ _ _)
          have hHold := hold_spawn_root I w hH hR template t name ht hmay hsup hsub hpre hoff'
          simpa [hstep] using hHold
        · simp at h
          have hstep := h.symm
          have hoff' : (w.st (InstId.peer template (freshKey I.desc w t.subtree)
              (maxGen w template (freshKey I.desc w t.subtree)))).prio = [] :=
            hoff _ (gen_fresh _ _ _)
          have hHold := hold_spawn_core I w hH template t name ht hmay hsup hsub hpre hoff'
          simpa [hstep] using hHold
      · rename_i hsup
        split at h
        · rename_i hsubB
          have hsub : t.subtree = "" := by simpa [beq_iff_eq] using hsubB
          simp at h
          have hstep := h.symm
          have hoff' : (w.st (InstId.peer template (w.nextIx template)
              (maxGen w template (w.nextIx template)))).prio = [] :=
            hoff _ (gen_fresh _ _ _)
          have hHold := hold_spawn_ix I w hH hI template t ht hmay hsup hsub hpre hoff'
          simpa [hstep] using hHold
        · rename_i hbit
          have hsub : t.subtree ≠ "" := by
            intro heq
            apply hbit
            simpa [beq_iff_eq] using heq
          simp at h
          have hstep := h.symm
          have hoff' : (w.st (InstId.peer template (freshKey I.desc w t.subtree)
              (maxGen w template (freshKey I.desc w t.subtree)))).prio = [] :=
            hoff _ (gen_fresh _ _ _)
          have hHold := hold_spawn_free I w hH template t ht hmay hsup hsub hpre hoff'
          simpa [hstep] using hHold
    · simp at h

/-- Every legal child of a per-peer parent uses that parent's key. -/
theorem legal_peer_key (D : Description) (pname : String) (pk pg N : Nat)
    (name : String) (k : Nat)
    (h : (name, k) ∈ legalSlots D (.peer pname pk pg) N) : k = pk := by
  simp [legalSlots, List.mem_flatMap, tname] at h
  obtain ⟨_, _, ht⟩ := h
  exact ht.2.2

theorem filter_false {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = false) : (xs.filter p).length = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    rw [ite_eq_right (by rw [hx]; decide)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem lifeHold_occupant (a : Actor) (h : lifeHold a = true) : occupant a = true := by
  cases hlife : a.life with
  | alive => simp [occupant, hlife]
  | dead =>
    unfold lifeHold at h
    simp [hlife] at h
  | absent =>
    unfold lifeHold at h
    simp [hlife] at h

/-- A per-peer parent whose key is free has no outstanding child of `child`
and no tombstone of that name. Every such child would sit at this key. -/
theorem peer_named_zero (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (pname child : String) (pk pg : Nat) (hpar : parent = .peer pname pk pg)
    (hfree : slotOccupied w child pk = false)
    (hq : slotTombstoneQueued w parent child pk = false) :
    namedOpen I.desc w parent child = 0 := by
  have hidx : slotIndexed I.desc parent child = true := by
    rw [hpar]
    simp [slotIndexed]
  have hkids : ∀ c, c ∈ w.roster → namedChild I.desc w parent child c = false := by
    intro c hc
    by_cases hbit : namedChild I.desc w parent child c = true
    · exfalso
      cases c with
      | core _ => simp [namedChild] at hbit
      | peer n key g =>
        have hparts := (Bool.and_eq_true _ _).mp hbit
        have hopen := (Bool.and_eq_true _ _).mp hparts.1
        have hnote := hopen.2
        have hlife := (Bool.and_eq_true _ _).mp hopen.1
        have hchild := hlife.1
        have hhold := hlife.2
        have hname : n = child := by simpa [beq_iff_eq] using hparts.2
        have hidxN : slotIndexed I.desc parent n = true := by
          rw [hpar]
          simp [slotIndexed]
        have hleg := hH.legalLife parent (.peer n key g) hc hchild hhold hnote
        have hmem := hleg hidxN
        have hkey : key = pk := legal_peer_key I.desc pname pk pg w.N n key
          (by simpa [hpar] using hmem)
        have hocc : occupant (w.st (.peer n key g)) = true := lifeHold_occupant _ hhold
        have hslot : slotOccupied w child pk = true := by
          unfold slotOccupied
          refine _root_.List.any_eq_true.mpr ?_
          refine ⟨.peer n key g, hc, ?_⟩
          have hn : (n == child) = true := by rw [hname]; exact (beq_iff_eq).mpr rfl
          have hk : (key == pk) = true := by rw [hkey]; exact (beq_iff_eq).mpr rfl
          cases hlive : (w.st (.peer n key g)).life with
          | alive =>
            simp only [hlive, hn, hk]
            rfl
          | dead =>
            unfold occupant at hocc
            simp [hlive] at hocc
          | absent =>
            unfold occupant at hocc
            simp [hlive] at hocc
        simp [hslot, hname] at hfree
    · cases hbb : namedChild I.desc w parent child c
      · rfl
      · exact absurd hbb hbit
  have hfilter := filter_false (namedChild I.desc w parent child) w.roster hkids
  have htombs : namedTombs ((w.st parent).prio) child = [] := by
    cases hms : namedTombs ((w.st parent).prio) child with
    | nil => rfl
    | cons s ss =>
      exfalso
      have hs : s ∈ namedTombs ((w.st parent).prio) child := by
        rw [hms]
        exact List.mem_cons_self
      simp [namedTombs, List.mem_filter] at hs
      obtain ⟨htomb, hnameB⟩ := hs
      simp [tombSlots, List.mem_filterMap] at htomb
      obtain ⟨m, hm, hbody⟩ := htomb
      cases ht : m.tombstone <;> cases hsend : m.sender <;> simp [ht, hsend] at hbody
      rename_i n key g
      have hpair : n = s.1 ∧ key = s.2 := by
        cases hbody
        exact ⟨rfl, rfl⟩
      have hname : n = child := by
        have hs1 : s.1 = child := by simpa [beq_iff_eq] using hnameB
        simpa [hs1] using hpair.1
      have hkey : key = pk := by
        have hqueued : slotTombstoneQueued w parent n key = true := by
          unfold slotTombstoneQueued
          refine _root_.List.any_eq_true.mpr ?_
          refine ⟨m, hm, ?_⟩
          simp [ht, hsend]
        have hidxN : slotIndexed I.desc parent n = true := by
          rw [hpar]
          simp [slotIndexed]
        have hleg := hH.legalTomb parent n key hqueued hidxN
        exact legal_peer_key I.desc pname pk pg w.N n key (by simpa [hpar] using hleg)
      have hqueued : slotTombstoneQueued w parent child pk = true := by
        unfold slotTombstoneQueued
        refine _root_.List.any_eq_true.mpr ?_
        refine ⟨m, hm, ?_⟩
        have hn : (n == child) = true := by rw [hname]; exact (beq_iff_eq).mpr rfl
        have hk : (key == pk) = true := by rw [hkey]; exact (beq_iff_eq).mpr rfl
        simp [ht, hsend, hn, hk]
      simp [hqueued] at hq
  simp [namedOpen, hfilter, htombs]

/-- A per-peer parent births one child at its own key. The guard has that key
empty, so the birth is the one outstanding child that parent's lane allows. -/
theorem hold_child_peer (I : Impl) (w : World) (hH : Hold I w) (parent : InstId)
    (pname child : String) (t : Template) (pk pg : Nat)
    (ht : templateOf I.desc child = some t) (hmul : t.multiplicity = .perPeer)
    (hsup : supNamed t.supervisor pname = true) (hpar : parent = .peer pname pk pg)
    (hfree : slotOccupied w child pk = false)
    (hq : slotTombstoneQueued w parent child pk = false)
    (halive : (w.st parent).life = .alive) (hpre : w.crashed = false)
    (hoff : (w.st (InstId.peer child pk (maxGen w child pk))).prio = []) :
    Hold I (admitBorn I w (InstId.peer child pk (maxGen w child pk))
      { bornActor I.desc w child pk t.initial with parent := some parent }) := by
  let k := pk
  let id := InstId.peer child k (maxGen w child k)
  let parentO : Option InstId := some parent
  let next : World → World := fun u => u
  let born := { bornActor I.desc w child k t.initial with parent := parentO }
  let w' := placePeer I w child k t.initial parentO next
  have hzero := peer_named_zero I w hH parent pname child pk pg hpar hfree hq
  have hnext : ∀ (u : World) (i : InstId),
      (next u).st i = u.st i ∧ (next u).roster = u.roster ∧ (next u).N = u.N ∧
        (next u).crashed = u.crashed := by
    intro u i
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hst : ∀ i, w'.st i = if i = id then born else w.st i := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    intro i
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, mid, (hnext base i).1, base]
  have hros : w'.roster = w.roster ++ [id] := by
    let base := { w with roster := w.roster ++ [id] }
    let mid := next base
    let planted := setActor mid id born
    have hw' : w' = readCells I.desc planted id := by
      simp [w', placePeer, id, born, base, mid, planted, next, k]
    rw [hw', show (readCells I.desc planted id).roster = planted.roster from
      cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2.1, base]
  have hnew : id ∉ w.roster := gen_fresh w child k
  have hparent : born.parent = some parent := by simp [born, parentO]
  have hlive : born.life = .alive := by simp [born, bornActor, withKeyTokens]
  have hbornPrio : born.prio = (w.st id).prio := by
    have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
    simpa [hp, id, k, hoff]
  have hprios : ∀ i, i ≠ id → (w'.st i).prio = (w.st i).prio := by
    intro i hne
    have h := hst i
    simp [hne] at h
    rw [h]
  have hst' : ∀ i, w'.st i = if i = id then w'.st id else w.st i := by
    intro i
    by_cases hi : i = id
    · have hborn : w'.st id = born := by simpa [hi] using hst id
      simp [hi, hborn]
    · simp [hi, hst i]
  have hself : w'.st id = born := by simpa using hst id
  have hcensus : ∀ par nm, namedOpen I.desc w' par nm ≤ nameBudget I.desc par w.N nm := by
    intro par nm
    by_cases hthis : par = parent
    · rw [hthis]
      by_cases hnm : nm = child
      · rw [hnm]
        by_cases hnote : notifies I.desc id = true
        · have hmemP : parent ∈ w.roster := hH.rostered parent (by
            intro habs
            simp [halive] at habs)
          have hne : id ≠ parent := fun heq => hnew (heq ▸ hmemP)
          have hchild := isChild_recorded w' parent id (by rw [hself]) hne
          have hlifeB : lifeHold (w'.st id) = true := by
            rw [lifeHold, hself, hlive]
            simp
          have hopen : childOpen I.desc w' parent id = true := by
            unfold childOpen
            rw [hchild, hlifeB, hnote]
            rfl
          have hbit : namedChild I.desc w' parent child id = true := by
            unfold namedChild
            rw [hopen]
            simp [id]
          have hparentPrio : (w'.st parent).prio = (w.st parent).prio := by
            have hneP : parent ≠ id := fun heq => hne heq.symm
            exact hprios parent hneP
          have hcount := census_born I.desc w w' id parent child hst' hros hnew hbit hparentPrio
          have hkeep : (t.tombstone != "") = true := by
            simpa only [id, notifies, tname, ht] using hnote
          have hname : tname parent = pname := by simp [hpar, tname]
          have hbudget : nameBudget I.desc parent w.N child = 1 := by
            have hk : tmb_keep parent t = true := by
              unfold tmb_keep
              rw [hname]
              exact (Bool.and_eq_true _ _).mpr ⟨hsup, hkeep⟩
            rw [hpar] at hk
            rw [hpar]
            simp [nameBudget, ht, tmb_leg, hk]
          rw [hcount, hzero, hbudget]
          simp
        · have hbit : namedChild I.desc w' parent child id = false := by
            have hnf : notifies I.desc id = false := by
              cases hn : notifies I.desc id with
              | false => rfl
              | true => exact absurd hn hnote
            unfold namedChild childOpen
            rw [hnf]
            simp only [Bool.and_false, Bool.false_and]
          have hparentPrio : (w'.st parent).prio = (w.st parent).prio := by
            have hmemP : parent ∈ w.roster := hH.rostered parent (by
              intro habs
              simp [halive] at habs)
            exact hprios parent (fun heq => hnew (heq ▸ hmemP))
          have hcount := census_born_other I.desc w w' id parent child hst' hros hnew hbit
            hparentPrio
          have hbudget : nameBudget I.desc parent w.N child = 0 := by
            have hnf : (t.tombstone != "") = false := by
              have hn : notifies I.desc id = false := by
                cases hb : notifies I.desc id with
                | false => rfl
                | true => exact absurd hb hnote
              simpa only [id, notifies, tname, ht] using hn
            rw [hpar]
            simp [nameBudget, ht, tmb_leg, tmb_keep, hnf, Bool.and_false]
          rw [hcount, hzero, hbudget]
          simp
      · have hbit : namedChild I.desc w' parent nm id = false := by
          have hbb : (child == nm) = false := by
            rw [beq_comm]
            cases hbeq : (nm == child) with
            | false => rfl
            | true => exact absurd ((beq_iff_eq).mp hbeq) hnm
          unfold namedChild
          simp [id, hbb]
        have hparentPrio : (w'.st parent).prio = (w.st parent).prio := by
          have hmemP : parent ∈ w.roster := hH.rostered parent (by
            intro habs
            simp [halive] at habs)
          exact hprios parent (fun heq => hnew (heq ▸ hmemP))
        have hcount := census_born_other I.desc w w' id parent nm hst' hros hnew hbit hparentPrio
        simpa [hcount] using hH.census parent nm
    · have hbit : namedChild I.desc w' par nm id = false := by
        have hchild : isChild w' par id = false := by
          unfold isChild
          rw [hself, hparent]
          have hbb : (parent == par) = false := by
            cases hbeq : (parent == par) with
            | false => rfl
            | true => exact absurd ((beq_iff_eq).mp hbeq).symm hthis
          simp only [hbb, Bool.false_and]
        unfold namedChild childOpen
        rw [hchild]
        simp only [Bool.false_and]
      have hprio : (w'.st par).prio = (w.st par).prio := by
        by_cases heq : par = id
        · rw [heq, hself]
          exact hbornPrio
        · exact hprios par heq
      have hcount := census_born_other I.desc w w' id par nm hst' hros hnew hbit hprio
      simpa [hcount] using hH.census par nm
  have hocc : ∀ c, c ∈ w.roster → occupant (w.st c) = true →
      sameSlot (InstId.peer child k (maxGen w child k)) c = false := by
    intro c hc hoccB
    cases c with
    | core _ => simp [sameSlot]
    | peer n key g =>
      by_cases hboth : (n == child && key == k) = true
      · exfalso
        have hparts := (Bool.and_eq_true _ _).mp hboth
        have hname : n = child := by simpa [beq_iff_eq] using hparts.1
        have hkey : key = k := by simpa [beq_iff_eq] using hparts.2
        have hslot : slotOccupied w child pk = true := by
          unfold slotOccupied
          refine _root_.List.any_eq_true.mpr ?_
          refine ⟨.peer n key g, hc, ?_⟩
          have hn : (n == child) = true := by rw [hname]; exact (beq_iff_eq).mpr rfl
          have hk : (key == pk) = true := by rw [hkey]; exact (beq_iff_eq).mpr rfl
          cases hlive : (w.st (.peer n key g)).life with
          | alive =>
            simp only [hlive, hn, hk]
            rfl
          | dead =>
            unfold occupant at hoccB
            simp [hlive] at hoccB
          | absent =>
            unfold occupant at hoccB
            simp [hlive] at hoccB
        simp [hslot] at hfree
      · cases hn : child == n <;> cases hk : k == key
        · simp only [sameSlot, hn, Bool.false_and]
        · simp only [sameSlot, hn, Bool.false_and]
        · simp only [sameSlot, hk, Bool.and_false]
        · exfalso
          have hn' : (n == child) = true := by rw [beq_comm]; exact hn
          have hk' : (key == k) = true := by rw [beq_comm]; exact hk
          apply hboth
          simp [hn', hk']
  have hfit : ∀ par, parentO = some par →
      notifies I.desc (InstId.peer child k (maxGen w child k)) = true →
      slotIndexed I.desc par child = true → (child, k) ∈ legalSlots I.desc par w.N := by
    intro par hsome hnote _
    have heq : parent = par := by simpa [parentO] using hsome
    rw [← heq, hpar]
    have ⟨hmemT, hnameT⟩ := templateOf_mem I.desc child t ht
    have htomb : t.tombstone ≠ "" := by
      have hlab : (t.tombstone != "") = true := by
        simpa only [notifies, tname, ht] using hnote
      simpa [bne, beq_iff_eq] using hlab
    have hsupS : t.supervisor = some pname := by
      cases hts : t.supervisor with
      | none => simp [supNamed, hts] at hsup
      | some n =>
        have hn : n = pname := by simpa [supNamed, hts, beq_iff_eq] using hsup
        simp [hn]
    have hgen : legalSlots I.desc (.peer pname pk pg) w.N =
        legalSlots I.desc (.peer pname pk 0) w.N := by
      simp [legalSlots, tname]
    rw [hgen]
    simpa [k] using legal_mem_peer I.desc pname child pk w.N t hmemT hnameT hsupS htomb
  have hfreeQ : ∀ par, parentO = some par →
      slotTombstoneQueued w par child k = false := by
    intro par hsome
    have heq : parent = par := by simpa [parentO] using hsome
    simpa [heq, k] using hq
  have hHold := hold_place I w hH child k t.initial parentO next hpre hnext
    ⟨t, ht, hmul⟩ hocc hfit hfreeQ (by simpa [w', k] using hcensus)
  have hadmit : admitBorn I w id born = w' := by
    simp [admitBorn, w', placePeer, id, born, parentO, next, k]
  simpa [hadmit, id, born, parentO, k] using hHold

/-! The phase a continuation reaches is one the static check already allowed. -/

theorem resumed_declared (I : Impl) (template : String) (k : Cont)
    (h : ContDeclared I template k) : phaseDeclared I template (resumed k) := by
  cases hr : k.rest with
  | nil => simp [resumed, hr, phaseDeclared]
  | cons _ _ =>
    simp [resumed, hr, phaseDeclared]
    exact h

theorem mail_phase_other (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hne : i ≠ sender) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).phase = (w.st i).phase := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · cases isCall with
    | true => simp [hdead, hne, setActor]
    | false => simp [hdead, hne, setActor]
  · by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk D w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · cases isCall with
        | true => simp [hdead, hroom, hsame, hne, setActor]
        | false => simp [hdead, hroom, hsame, hne, setActor]
      · have hdir : ¬ dst = sender := by
          intro heq
          exact hsame (decide_eq_true_iff.mpr heq.symm)
        cases isCall with
        | true =>
          by_cases hd : i = dst
          · simp [hdead, hroom, hsame, hd, setActor, hdir]
          · simp [hdead, hroom, hsame, hd, hne, setActor]
        | false =>
          by_cases hd : i = dst
          · simp [hdead, hroom, hsame, hd, setActor, hdir]
          · simp [hdead, hroom, hsame, hd, hne, setActor]
    · by_cases hsame : decide (sender = dst) = true
      · simp [hdead, hroom, hsame, hne, setActor]
      · have hdir : ¬ dst = sender := by
          intro heq
          exact hsame (decide_eq_true_iff.mpr heq.symm)
        by_cases hd : i = dst
        · simp [hdead, hroom, hsame, hd, setActor, hdir]
        · simp [hdead, hroom, hsame, hd, hne, setActor]

theorem mail_sender_phase (I : Impl) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hdec : ContDeclared I (tname sender) k) :
    phaseDeclared I (tname sender)
      ((enqueueOrPark w I.desc sender dst msg isCall k).st sender).phase := by
  unfold enqueueOrPark
  by_cases hdead : (w.st dst).life ≠ .alive
  · cases isCall with
    | true =>
      simp [hdead, setActor]
      exact finish_declared I (tname sender) (issueCall (w.st sender)) k .notAdmitted hdec
    | false =>
      simp [hdead, setActor, proceed_resumed]
      exact resumed_declared I (tname sender) k hdec
  · by_cases hroom : (decide ((w.st dst).parked = []) &&
        decide ((w.st dst).box.length < capBulk I.desc w.N dst)) = true
    · by_cases hsame : decide (sender = dst) = true
      · cases isCall with
        | true =>
          simp [hdead, hroom, hsame, setActor, phaseDeclared]
          exact hdec
        | false =>
          simp [hdead, hroom, hsame, setActor, proceed_resumed]
          exact resumed_declared I (tname sender) k hdec
      · cases isCall with
        | true =>
          simp [hdead, hroom, hsame, setActor, phaseDeclared]
          exact hdec
        | false =>
          simp [hdead, hroom, hsame, setActor, proceed_resumed]
          exact resumed_declared I (tname sender) k hdec
    · by_cases hsame : decide (sender = dst) = true
      · simp [hdead, hroom, hsame, setActor, phaseDeclared]
        exact hdec
      · simp [hdead, hroom, hsame, setActor, phaseDeclared]
        exact hdec

theorem hold_send (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (dst label : String) (hint : Nat) (es : List Eff) (hpre : w.crashed = false)
    (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .send dst label hint :: es) (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have htail := ContDeclared.after I (tname id) k _ _ hk hdec
  cases hroute : route w I.desc id dst hint with
  | none =>
    have hrun : execRun I w id a k = setActor (noteStale w id dst) id (proceed a k') := by
      simp [execRun, hgo, hk, hroute, k']
    have hN := hold_note I w hH id dst hpre
    have hph : id ∈ (noteStale w id dst).roster →
        phaseDeclared I (tname id) (proceed ((noteStale w id dst).st id) k').phase := by
      intro _
      simpa [noteStale_st, ha, proceed_resumed] using resumed_declared I (tname id) k' htail
    have hP := hold_proceed I (noteStale w id dst) hN id k' (by simp [noteStale, hpre]) hph
    have hP' : Hold I (setActor (noteStale w id dst) id (proceed a k')) := by
      simpa [noteStale_st, ← ha] using hP
    exact hrun.symm ▸ hP'
  | some dstId =>
    let msg : Msg := { label := label, sender := id, callFrom := none }
    have hrun : execRun I w id a k = enqueueOrPark w I.desc id dstId msg false k' := by
      simp [execRun, hgo, hk, hroute, k', msg]
    have hph : ∀ i, i ∈ w.roster →
        phaseDeclared I (tname i) ((enqueueOrPark w I.desc id dstId msg false k').st i).phase := by
      intro i hi
      by_cases hwho : i = id
      · rw [hwho]
        exact mail_sender_phase I w id dstId msg false k' htail
      · rw [mail_phase_other w I.desc id dstId msg false k' i hwho]
        exact hH.phase i hi
    exact hrun.symm ▸ hold_mail I w hH id dstId msg false k' hpre hph

theorem cont_full (I : Impl) (template : String) (k : Cont) (dst label : String) (hint : Nat)
    (onFull onGone es : List Eff) (hk : k.rest = .trySend dst label hint onFull onGone :: es)
    (hdec : ContDeclared I template k) :
    ContDeclared I template
      { afterHead k with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull } := by
  have h := ContDeclared.tryFull I template k dst label hint onFull onGone es hk hdec
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.rest
  · simpa using h.na
  · simpa using h.to
  · simpa using h.timeout

theorem cont_gone (I : Impl) (template : String) (k : Cont) (dst label : String) (hint : Nat)
    (onFull onGone es : List Eff) (hk : k.rest = .trySend dst label hint onFull onGone :: es)
    (hdec : ContDeclared I template k) :
    ContDeclared I template
      { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone } := by
  have h := ContDeclared.tryGone I template k dst label hint onFull onGone es hk hdec
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.rest
  · simpa using h.na
  · simpa using h.to
  · simpa using h.timeout

theorem hold_try (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (dst label : String) (hint : Nat) (onFull onGone es : List Eff)
    (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .trySend dst label hint onFull onGone :: es)
    (hdec : ContDeclared I (tname id) k) : Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  let kFull := { k' with rest := onFull, toState := pickState k'.toState k'.toFull }
  let kGone := { k' with rest := onGone, toState := pickState k'.toState k'.toGone }
  have hF := cont_full I (tname id) k dst label hint onFull onGone es hk hdec
  have hG := cont_gone I (tname id) k dst label hint onFull onGone es hk hdec
  have hphF : id ∈ w.roster → phaseDeclared I (tname id) (proceed a kFull).phase := by
    intro _
    simpa [ha, proceed_resumed, kFull, k'] using resumed_declared I (tname id) _ hF
  have hphG : id ∈ w.roster → phaseDeclared I (tname id) (proceed a kGone).phase := by
    intro _
    simpa [ha, proceed_resumed, kGone, k'] using resumed_declared I (tname id) _ hG
  cases hroute : route w I.desc id dst hint with
  | none =>
    have hrun : execRun I w id a k =
        setActor (noteStale w id dst) id (proceed a kGone) := by
      simp [execRun, hgo, hk, hroute, k', kGone]
    have hN := hold_note I w hH id dst hpre
    have hph : id ∈ (noteStale w id dst).roster →
        phaseDeclared I (tname id) (proceed ((noteStale w id dst).st id) kGone).phase := by
      intro _
      simpa [noteStale_st, ha, proceed_resumed, kGone, k'] using
        resumed_declared I (tname id) _ hG
    have hP := hold_proceed I (noteStale w id dst) hN id kGone (by simp [noteStale, hpre]) hph
    have hP' : Hold I (setActor (noteStale w id dst) id (proceed a kGone)) := by
      simpa [noteStale_st, ← ha] using hP
    exact hrun.symm ▸ hP'
  | some dstId =>
    let target := w.st dstId
    let cap := capBulk I.desc w.N dstId
    by_cases hliveB : (target.life == .alive) = true
    · by_cases hempty : decide (target.parked = []) = true
      · by_cases hlen : decide (target.box.length < cap) = true
        · let msg : Msg := { label := label, sender := id, callFrom := none, reliable := false }
          have hroom : (target.life == .alive && decide (target.parked = []) &&
              decide (target.box.length < cap)) = true := by
            simp [hliveB, hempty, hlen]
          have hrun : execRun I w id a k = enqueueOrPark w I.desc id dstId msg false k' := by
            simp [execRun, hgo, hk, hroute, hroom, k', msg, target, cap]
          have htail := ContDeclared.after I (tname id) k _ _ hk hdec
          have hph : ∀ i, i ∈ w.roster →
              phaseDeclared I (tname i) ((enqueueOrPark w I.desc id dstId msg false k').st i).phase := by
            intro i hi
            by_cases hwho : i = id
            · rw [hwho]
              exact mail_sender_phase I w id dstId msg false k' htail
            · rw [mail_phase_other w I.desc id dstId msg false k' i hwho]
              exact hH.phase i hi
          exact hrun.symm ▸ hold_mail I w hH id dstId msg false k' hpre hph
        · have hlenF : decide (target.box.length < cap) = false := by
            cases hbit : decide (target.box.length < cap) with
            | false => rfl
            | true => exact absurd hbit hlen
          have hrun : execRun I w id a k = setActor w id (proceed a kFull) := by
            simp [execRun, hgo, hk, hroute, hliveB, hempty, hlenF, k', kFull, target, cap]
          have hph : id ∈ w.roster →
              phaseDeclared I (tname id) (proceed (w.st id) kFull).phase := by
            intro hmem
            simpa [ha] using hphF hmem
          have hP := hold_proceed I w hH id kFull hpre hph
          have hP' : Hold I (setActor w id (proceed a kFull)) := by simpa [← ha] using hP
          exact hrun.symm ▸ hP'
      · have hemptyF : decide (target.parked = []) = false := by
          cases hbit : decide (target.parked = []) with
          | false => rfl
          | true => exact absurd hbit hempty
        have hrun : execRun I w id a k = setActor w id (proceed a kFull) := by
          simp [execRun, hgo, hk, hroute, hliveB, hemptyF, k', kFull, target, cap]
        have hph : id ∈ w.roster →
            phaseDeclared I (tname id) (proceed (w.st id) kFull).phase := by
          intro hmem
          simpa [ha] using hphF hmem
        have hP := hold_proceed I w hH id kFull hpre hph
        have hP' : Hold I (setActor w id (proceed a kFull)) := by simpa [← ha] using hP
        exact hrun.symm ▸ hP'
    · have hdeadT : (target.life == .alive) = false := by
        cases hbit : target.life == .alive with
        | false => rfl
        | true => exact absurd hbit hliveB
      have hrun : execRun I w id a k = setActor w id (proceed a kGone) := by
        simp [execRun, hgo, hk, hroute, hdeadT, k', kGone, target, cap]
      have hph : id ∈ w.roster →
          phaseDeclared I (tname id) (proceed (w.st id) kGone).phase := by
        intro hmem
        simpa [ha] using hphG hmem
      have hP := hold_proceed I w hH id kGone hpre hph
      have hP' : Hold I (setActor w id (proceed a kGone)) := by simpa [← ha] using hP
      exact hrun.symm ▸ hP'

theorem hold_call (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (dst label : String) (hint : Nat) (onNotAdmitted onTimedOut es : List Eff)
    (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .call dst label hint onNotAdmitted onTimedOut :: es)
    (hdec : ContDeclared I (tname id) k) : Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  let kWait := { k' with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
  have hwait := ContDeclared.callWait I (tname id) k dst label hint onNotAdmitted onTimedOut es hk hdec
  cases hres : resolveId I.desc w id dst hint with
  | none =>
    have hrun : execRun I w id a k =
        setActor (noteStale w id dst) id (finishCall (issueCall a) kWait .notAdmitted) := by
      simp [execRun, hgo, hk, hres, k', kWait]
    let done := finishCall (issueCall a) kWait .notAdmitted
    have hN := hold_note I w hH id dst hpre
    have hl : done.life = ((noteStale w id dst).st id).life := by
      simpa [done, noteStale_st, ha] using
        (finish_keep (issueCall a) kWait .notAdmitted).1.trans (issue_keep a).1
    have hp : done.prio = ((noteStale w id dst).st id).prio := by
      simpa [done, noteStale_st, ha] using
        (finish_keep (issueCall a) kWait .notAdmitted).2.1.trans (issue_keep a).2.1
    have hpe : done.pendingTombstone = ((noteStale w id dst).st id).pendingTombstone := by
      simpa [done, noteStale_st, ha] using
        (finish_keep (issueCall a) kWait .notAdmitted).2.2.trans (issue_keep a).2.2
    have hpa : done.parent = ((noteStale w id dst).st id).parent := by
      simpa [done, noteStale_st, ha] using
        (finish_parent (issueCall a) kWait .notAdmitted).trans (issue_parent a)
    have hph : id ∈ (noteStale w id dst).roster →
        phaseDeclared I (tname id) done.phase := by
      intro _
      exact finish_declared I (tname id) (issueCall a) kWait .notAdmitted
        (by simpa [kWait, k'] using hwait)
    have hS := hold_set I (noteStale w id dst) hN id done hl hp hpe hpa hph (by simp [noteStale, hpre])
    exact hrun.symm ▸ hS
  | some dstId =>
    let msg : Msg := { label := label, sender := id, callFrom := some id }
    have hrun : execRun I w id a k = enqueueOrPark w I.desc id dstId msg true kWait := by
      simp [execRun, hgo, hk, hres, k', kWait, msg]
    have hph : ∀ i, i ∈ w.roster →
        phaseDeclared I (tname i)
          ((enqueueOrPark w I.desc id dstId msg true kWait).st i).phase := by
      intro i hi
      by_cases hwho : i = id
      · rw [hwho]
        exact mail_sender_phase I w id dstId msg true kWait (by simpa [kWait, k'] using hwait)
      · rw [mail_phase_other w I.desc id dstId msg true kWait i hwho]
        exact hH.phase i hi
    exact hrun.symm ▸ hold_mail I w hH id dstId msg true kWait hpre hph

theorem hold_reply_proceed (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (k : Cont)
    (hpre : w.crashed = false) (hdec : ContDeclared I (tname id) k) :
    Hold I (setActor w id (proceed (w.st id) k)) := by
  have hph : id ∈ w.roster → phaseDeclared I (tname id) (proceed (w.st id) k).phase := by
    intro _
    simpa [proceed_resumed] using resumed_declared I (tname id) k hdec
  exact hold_proceed I w hH id k hpre hph

theorem hold_reply (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (es : List Eff) (hpre : w.crashed = false) (_ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .reply :: es) (hdec : ContDeclared I (tname id) k) :
    Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  have hrun : execRun I w id a k = performReply w id k := by
    simp [execRun, hgo, hk]
  let k' := afterHead k
  have htail := ContDeclared.after I (tname id) k _ _ hk hdec
  have hplain : performReply w id k = setActor w id (proceed (w.st id) k') →
      Hold I (performReply w id k) := by
    intro heq
    have hP := hold_reply_proceed I w hH id k' hpre (by simpa [k'] using htail)
    simpa [heq, k'] using hP
  cases hto : k.replyTo with
  | none =>
    exact hrun.symm ▸ hplain (by simp [performReply, hto, k'])
  | some caller =>
    cases hphase : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hdst : dst = id
      · by_cases howe : (w.st id).oweId = some (w.st caller).waitId
        · have hif : (decide (dst = id) &&
              decide ((w.st id).oweId = some (w.st caller).waitId)) = true := by
            simp [hdst, howe]
          let done := finishCall (w.st caller) ck .reply
          let w1 := setActor w caller done
          have hrun1 : performReply w id k =
              setActor w1 id (proceed (w1.st id) k') := by
            simp [performReply, hto, hphase, hif, k', done, w1]
          have hl : done.life = (w.st caller).life := (finish_keep (w.st caller) ck .reply).1
          have hp : done.prio = (w.st caller).prio := (finish_keep (w.st caller) ck .reply).2.1
          have hpe : done.pendingTombstone = (w.st caller).pendingTombstone :=
            (finish_keep (w.st caller) ck .reply).2.2
          have hpa : done.parent = (w.st caller).parent := finish_parent (w.st caller) ck .reply
          have hphC : caller ∈ w.roster →
              phaseDeclared I (tname caller) done.phase := by
            intro hmem
            have hcont : ContDeclared I (tname caller) ck := by
              simpa [hphase, phaseDeclared] using hH.phase caller hmem
            exact finish_declared I (tname caller) (w.st caller) ck .reply hcont
          have hW1 := hold_set I w hH caller done hl hp hpe hpa hphC hpre
          by_cases hsame : caller = id
          · have hst : w1.st id = done := by simpa [w1, hsame] using setActor_self w caller done
            have hph : id ∈ w1.roster →
                phaseDeclared I (tname id) (proceed (w1.st id) k').phase := by
              intro _
              simpa [hst, proceed_resumed, k'] using resumed_declared I (tname id) k' htail
            have hpre1 : w1.crashed = false := by simp [w1, setActor, hpre]
            have hP := hold_proceed I w1 hW1 id k' hpre1 hph
            exact hrun.symm ▸ hrun1.symm ▸ hP
          · have hst : w1.st id = w.st id := setActor_other w caller id done (Ne.symm hsame)
            have hph : id ∈ w1.roster →
                phaseDeclared I (tname id) (proceed (w1.st id) k').phase := by
              intro _
              simpa [hst, proceed_resumed, k'] using resumed_declared I (tname id) k' htail
            have hpre1 : w1.crashed = false := by simp [w1, setActor, hpre]
            have hP := hold_proceed I w1 hW1 id k' hpre1 hph
            exact hrun.symm ▸ hrun1.symm ▸ hP
        · have hif : (decide (dst = id) &&
              decide ((w.st id).oweId = some (w.st caller).waitId)) = false := by
            simp [hdst, howe]
          exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, hif, k'])
      · have hif : (decide (dst = id) &&
            decide ((w.st id).oweId = some (w.st caller).waitId)) = false := by
          simp [hdst]
        exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, hif, k'])
    | idle =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])
    | run _ =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])
    | parked _ _ _ =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])
    | awaitEffect _ =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])
    | awaitPeer _ =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])
    | crashed =>
      exact hrun.symm ▸ hplain (by simp [performReply, hto, hphase, k'])

/-- A cell write does not touch an actor, so the lane invariant is the same one. -/
theorem hold_setCell (I : Impl) (w : World) (hH : Hold I w) (dst label : String) (c : Cell) :
    Hold I (setCell w dst label c) := by
  have hlane : ∀ id, LaneOk I (setCell w dst label c) id := by
    intro id
    have h := hH.lane id
    have hst : (setCell w dst label c).st id = w.st id := by simp [setCell]
    exact ⟨by simpa [hst] using h.ordNodup,
      fun l hl => h.ordIn l (by simpa [hst] using hl),
      fun m hm ht => h.peer m (by simpa [hst] using hm) ht,
      by simpa [hst] using h.tombNodup⟩
  exact ⟨hH.rostered, hH.pend, hH.deadPrio, hH.role, hH.phase, hlane, hH.legalLife,
    hH.legalTomb, hH.fresh, hH.occ, hH.rooted, hH.census, hH.tombHere⟩

theorem crash_kills_alive (w : World) (i : InstId) (hmem : i ∈ w.roster)
    (hlive : (w.st i).life = .alive) : ((crashWorld w).st i).life = .dead := by
  have hdec : decide (i ∈ w.roster) = true := decide_eq_true hmem
  have hbit : ((w.st i).life == .alive) = true := (beq_iff_eq).mpr hlive
  simp [crash_life, hdec, hbit]

/-- A wake aimed at an actor that is no longer alive leaves the world alone.
After a full lane crashes the roster, every later reader in the same fold is
already dead, so the fold stops there. -/
theorem tryWake_dead (D : Description) (w : World) (id : InstId) (label : String)
    (writer : InstId) (h : (w.st id).life ≠ .alive) : tryWake D w id label writer = w := by
  have hbit : ((w.st id).life != .alive) = true := by simpa [bne, beq_iff_eq] using h
  simp [tryWake, hbit]

theorem wakes_dead (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer : InstId) (h : ∀ id, id ∈ ids → (w.st id).life ≠ .alive) :
    ids.foldl (fun acc i => tryWake D acc i label writer) w = w := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    have hhead : id ∈ id :: ids := List.mem_cons_self
    rw [List.foldl_cons, tryWake_dead D w id label writer (h id hhead)]
    exact ih fun i hi => h i (List.mem_cons.mpr (Or.inr hi))

/-- One cell wake appends a declared label, or crashes the roster when the lane
is already full. A label that is already queued is not a second message. -/
theorem hold_wakes (I : Impl) (ids : List InstId) (w : World) (hH : Hold I w)
    (label : String) (writer : InstId) (hpre : w.crashed = false)
    (halive : ∀ id, id ∈ ids → (w.st id).life = .alive)
    (hmem : ∀ id, id ∈ ids → id ∈ w.roster)
    (hlabel : ∀ id, id ∈ ids → label ∈ prioLabels I (tname id)) :
    Hold I (ids.foldl (fun acc i => tryWake I.desc acc i label writer) w) := by
  induction ids generalizing w with
  | nil =>
    simp
    exact hH
  | cons i ids ih =>
    have hhead : i ∈ i :: ids := List.mem_cons_self
    have hlive : (w.st i).life = .alive := halive i hhead
    have hbit : ((w.st i).life == .alive) = true := (beq_iff_eq).mpr hlive
    have hdrop : ((w.st i).life != .alive) = false := by simp [bne, hbit]
    have tailAlive : ∀ id, id ∈ ids → (w.st id).life = .alive :=
      fun id hid => halive id (List.mem_cons.mpr (Or.inr hid))
    have tailMem : ∀ id, id ∈ ids → id ∈ w.roster :=
      fun id hid => hmem id (List.mem_cons.mpr (Or.inr hid))
    have tailLabel : ∀ id, id ∈ ids → label ∈ prioLabels I (tname id) :=
      fun id hid => hlabel id (List.mem_cons.mpr (Or.inr hid))
    by_cases hqueued : ((w.st i).prio.any fun p => p.label == label) = true
    · have hor : (((w.st i).life != .alive) ||
          ((w.st i).prio.any fun p => p.label == label)) = true := by simp [hdrop, hqueued]
      have hstep : tryWake I.desc w i label writer = w := by simp [tryWake, hor]
      simp only [List.foldl_cons, hstep]
      exact ih w hH hpre tailAlive tailMem tailLabel
    · have hfree : ((w.st i).prio.any fun p => p.label == label) = false := by
        cases hbitq : (w.st i).prio.any fun p => p.label == label with
        | false => rfl
        | true => exact absurd hbitq hqueued
      have hor : (((w.st i).life != .alive) ||
          ((w.st i).prio.any fun p => p.label == label)) = false := by simp [hdrop, hfree]
      let wake : Msg :=
        { label := label, sender := writer, callFrom := none, reliable := false,
          mid := (w.st i).nextMid }
      have htry : tryWake I.desc w i label writer = offerPrio I.desc w i wake := by
        simp [tryWake, hor, wake]
      by_cases hfull : prioLoad (w.st i).prio ≥ capPrio I.desc w.N i
      · have hdec : decide (prioLoad (w.st i).prio ≥ capPrio I.desc w.N i) = true := by
          simp [hfull]
        have hcrashW : offerPrio I.desc w i wake = crashWorld w := by simp [offerPrio, hdec]
        have hdead : ∀ id, id ∈ ids → ((crashWorld w).st id).life ≠ .alive := by
          intro id hid
          rw [crash_kills_alive w id (tailMem id hid) (tailAlive id hid)]
          intro h
          cases h
        have hfold := wakes_dead I.desc ids (crashWorld w) label writer hdead
        simp only [List.foldl_cons, htry, hcrashW, hfold]
        exact hold_crash I w hH
      · have hdec : decide (prioLoad (w.st i).prio ≥ capPrio I.desc w.N i) = false :=
          decide_eq_false hfull
        have hsnoc : offerPrio I.desc w i wake = tmb_snoc w i wake := by
          simp [offerPrio, hdec, tmb_snoc]
        have ht : wake.tombstone = false := by simp [wake]
        have hnew : wake.label ∉ tmb_laneLabels ((w.st i).prio) := by
          simpa [wake] using lane_absent (w.st i).prio label hfree
        have hH' := hold_plain I w hH i wake hpre hlive ht
          (by simpa [wake] using hlabel i hhead) hnew
        let w' := tmb_snoc w i wake
        have hpre' : w'.crashed = false := by simpa [w', tmb_snoc_crash] using hpre
        have halive' : ∀ id, id ∈ ids → (w'.st id).life = .alive := by
          intro id hid
          simpa [w', tmb_snoc_life] using tailAlive id hid
        have hmem' : ∀ id, id ∈ ids → id ∈ w'.roster := by
          intro id hid
          simpa [w', tmb_snoc_roster] using tailMem id hid
        simp only [List.foldl_cons, htry, hsnoc]
        exact ih w' hH' hpre' halive' hmem' tailLabel

theorem hold_cell (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (dst label : String) (value : Nat) (es : List Eff) (hpre : w.crashed = false)
    (_ha : a = w.st id) (hlive : a.life = .alive) (hk : k.rest = .cell dst label value :: es)
    (hdec : ContDeclared I (tname id) k) : Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have htail := ContDeclared.after I (tname id) k _ _ hk hdec
  let previous := w.cell dst label
  let written := max previous.value value
  let wC := setCell w dst label { value := written, dirty := true }
  have hpreC : wC.crashed = false := by simp [wC, setCell, hpre]
  have hC := hold_setCell I w hH dst label { value := written, dirty := true }
  have hP := hold_reply_proceed I wC hC id k' hpreC (by simpa [k'] using htail)
  let wP := setActor wC id (proceed (wC.st id) k')
  have hread (i : InstId) (hi : i ∈ readersOf wP dst) :
      i ∈ wP.roster ∧ (wP.st i).life = .alive ∧ tname i = dst := by
    have hall := List.mem_filter.mp hi
    have hand := hall.2
    simp [Bool.and_eq_true, beq_iff_eq] at hand
    exact ⟨hall.1, hand.2, hand.1⟩
  have hlabel : ∀ i, i ∈ readersOf wP dst → label ∈ prioLabels I (tname i) := by
    intro i hi
    have hwake : label ∈ cellWakeLabels dst k.rest := by
      rw [hk]
      simp [cellWakeLabels, effWake]
    have hin := hdec.rest.wake dst label hwake
    simpa [(hread i hi).2.2] using hin
  by_cases hdirty : previous.dirty = true
  · have hrun : execRun I w id a k = wP := by
      simp [execRun, hgo, hk, k', previous, written, wC, wP, hdirty]
    exact hrun.symm ▸ hP
  · have hclean : previous.dirty = false := by
      cases hbit : previous.dirty with
      | false => rfl
      | true => exact absurd hbit hdirty
    have hrun : execRun I w id a k = wakeReaders I.desc wP dst label id := by
      simp [execRun, hgo, hk, k', previous, written, wC, wP, hclean]
    have halive : ∀ i, i ∈ readersOf wP dst → (wP.st i).life = .alive :=
      fun i hi => (hread i hi).2.1
    have hmem : ∀ i, i ∈ readersOf wP dst → i ∈ wP.roster :=
      fun i hi => (hread i hi).1
    have hpreP : wP.crashed = false := by simp [wP, setActor, hpreC]
    have hW := hold_wakes I (readersOf wP dst) wP hP label id hpreP halive hmem hlabel
    simpa [hrun, wakeReaders] using hW

theorem read_crash (D : Description) (w : World) (id : InstId) :
    (readCells D w id).crashed = w.crashed := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons]
    let mid := setObserved
      (setCell w (tname id) l { (w.cell (tname id) l) with dirty := false }) id l
      (w.cell (tname id) l).value
    have hmid : mid.crashed = w.crashed := by simp [mid, setCell, setObserved]
    exact (ih mid).trans hmid

theorem admit_crash (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).crashed = w.crashed := by
  simp [admitBorn, read_crash, setActor]

/-- A child the template allows is born, and the parent proceeds. A full slot
is a no-op. A spawn the template does not allow crashes the roster. -/
theorem hold_spawn_child (I : Impl) (w : World) (hH : Hold I w) (hG : GraphOk I.desc)
    (hnd : w.roster.Nodup) (id : InstId) (a : Actor) (k : Cont) (child : String)
    (es : List Eff) (hpre : w.crashed = false) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .spawn child :: es) (hdec : ContDeclared I (tname id) k)
    (hoff : ∀ i, i ∉ w.roster → (w.st i).prio = []) : Hold I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have htail := ContDeclared.after I (tname id) k _ _ hk hdec
  have hphase (w1 : World) : id ∈ w1.roster →
      phaseDeclared I (tname id) (proceed (w1.st id) k').phase := by
    intro _
    simpa [proceed_resumed] using resumed_declared I (tname id) k' htail
  have hlifeB : ((w.st id).life == .alive) = true := by simpa [ha, beq_iff_eq] using hlive
  have hparent : (w.st id).life = .alive := by simpa [ha] using hlive
  cases ht : templateOf I.desc child with
  | none =>
    have hsc : spawnChild I w id child = none := by simp [spawnChild, ht]
    have hrun : execRun I w id a k = crashWorld w := by simp [execRun, hgo, hk, hsc]
    exact hrun.symm ▸ hold_crash I w hH
  | some t =>
    let gate := t.multiplicity == .perPeer && supNamed t.supervisor (tname id) &&
      ((w.st id).life == .alive)
    by_cases hok : gate = true
    · have hmul : t.multiplicity = .perPeer := by
        cases hm : t.multiplicity with
        | perPeer => rfl
        | one =>
          have hb : (Multiplicity.one == .perPeer) = false := by decide
          simp [gate, hm, hb] at hok
      have hsupn : supNamed t.supervisor (tname id) = true := by
        cases hs : supNamed t.supervisor (tname id) with
        | true => rfl
        | false => simp [gate, hs] at hok
      cases id with
      | core pname =>
        have hsc : spawnChild I w (.core pname) child = none := by
          simp [spawnChild, ht, gate, hok]
        have hrun : execRun I w (.core pname) a k = crashWorld w := by
          simp [execRun, hgo, hk, hsc]
        exact hrun.symm ▸ hold_crash I w hH
      | peer pname pk pg =>
        have hsup : supNamed t.supervisor pname = true := by simpa [tname] using hsupn
        by_cases hbusy : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = true
        · have hsc : spawnChild I w (.peer pname pk pg) child = some w := by
            simp [spawnChild, ht, gate, hok, hbusy]
          have hrun : execRun I w (.peer pname pk pg) a k =
              setActor w (.peer pname pk pg) (proceed (w.st (.peer pname pk pg)) k') := by
            simp [execRun, hgo, hk, hsc, k', commitCont, hpre]
          exact hrun.symm ▸ hold_proceed I w hH (.peer pname pk pg) k' hpre (hphase w)
        · have hfalse : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk <;> simp_all
          have hclear := slotRespawnBlocked_clear I.desc w (.peer pname pk pg) child pk hfalse
          have hocc : slotOccupied w child pk = false := hclear.1
          have hq : slotTombstoneQueued w (.peer pname pk pg) child pk = false := hclear.2
          let bornId := InstId.peer child pk (maxGen w child pk)
          let born := { bornActor I.desc w child pk t.initial with parent := some (.peer pname pk pg) }
          let wB := admitBorn I w bornId born
          have hsc : spawnChild I w (.peer pname pk pg) child = some wB := by
            simp [spawnChild, ht, gate, hok, hfalse, bornId, born, wB]
          have hB := hold_child_peer I w hH (.peer pname pk pg) pname child t pk pg ht hmul hsup
            rfl hocc hq hparent hpre (hoff bornId (gen_fresh w child pk))
          have hpreB : wB.crashed = false := by simpa [wB, admit_crash] using hpre
          have hP := hold_proceed I wB hB (.peer pname pk pg) k' hpreB (hphase wB)
          have hrun : execRun I w (.peer pname pk pg) a k =
              setActor wB (.peer pname pk pg) (proceed (wB.st (.peer pname pk pg)) k') := by
            simp [execRun, hgo, hk, hsc, k', commitCont, hpreB]
          exact hrun.symm ▸ hP
    · have hgate : (t.multiplicity == .perPeer && supNamed t.supervisor (tname id)) = false := by
        cases hg : (t.multiplicity == .perPeer && supNamed t.supervisor (tname id)) with
        | false => rfl
        | true =>
          have htrue : gate = true := by simp [gate, hg, hlifeB]
          exact absurd htrue hok
      have hsc : spawnChild I w id child = none := by simp [spawnChild, ht, hgate]
      have hrun : execRun I w id a k = crashWorld w := by simp [execRun, hgo, hk, hsc]
      exact hrun.symm ▸ hold_crash I w hH

/-- One running step keeps the lane invariant. -/
theorem hold_exec (I : Impl) (w : World) (hH : Hold I w) (hG : GraphOk I.desc)
    (hnd : w.roster.Nodup) (id : InstId) (hpre : w.crashed = false)
    (hoff : ∀ i, i ∉ w.roster → (w.st i).prio = []) (w' : World)
    (h : execHead I w id = some w') : Hold I w' := by
  unfold execHead at h
  have halive : (w.st id).life = .alive := by
    by_cases ha : (w.st id).life = .alive
    · exact ha
    · simp [ha] at h
  have hliveP : ¬((w.st id).life ≠ .alive) := fun hn => hn halive
  simp only [hliveP, ite_false] at h
  let a := w.st id
  have ha : a = w.st id := rfl
  have hlive : a.life = .alive := by simpa [a] using halive
  cases hph : (w.st id).phase with
  | run k =>
    simp only [hph] at h
    have hmem : id ∈ w.roster := hH.rostered id (by simp [halive])
    have hdec : ContDeclared I (tname id) k := by
      simpa [hph, phaseDeclared] using hH.phase id hmem
    have hrun : a.phase = .run k := by simpa [a] using hph
    have heq : w' = execRun I w id a k := by
      simpa [a, Option.some.injEq] using h.symm
    cases hk : k.rest with
    | nil =>
      exact heq ▸ hold_idle I w hH id a k hpre ha hlive hk
    | cons e es =>
      cases e with
      | send dst label hint =>
        exact heq ▸ hold_send I w hH id a k dst label hint es hpre ha hlive hk hdec
      | trySend dst label hint onFull onGone =>
        exact heq ▸ hold_try I w hH id a k dst label hint onFull onGone es hpre ha hlive hk hdec
      | call dst label hint onNotAdmitted onTimedOut =>
        exact heq ▸
          hold_call I w hH id a k dst label hint onNotAdmitted onTimedOut es hpre ha hlive hk hdec
      | reply =>
        exact heq ▸ hold_reply I w hH id a k es hpre ha hlive hk hdec
      | selfSchedule label =>
        exact heq ▸ hold_self I w hH id a k label es hpre ha hlive hrun hk hdec
      | cell dst label value =>
        exact heq ▸ hold_cell I w hH id a k dst label value es hpre ha hlive hk hdec
      | internal =>
        exact heq ▸ hold_internal I w hH id a k es hpre ha hlive hk hdec
      | peer onTimeout =>
        exact heq ▸ hold_peer I w hH id a k onTimeout es hpre ha hlive hk hdec
      | abort =>
        exact heq ▸ hold_abort I w hH id a k hpre hlive ⟨es, hk⟩ hdec
      | spawn child =>
        exact heq ▸
          hold_spawn_child I w hH hG hnd id a k child es hpre ha hlive hk hdec hoff
      | terminate =>
        exact heq ▸ hold_terminate I w hH id a k hpre ha hlive ⟨es, hk⟩
  | idle => simp [hph] at h
  | parked _ _ _ => simp [hph] at h
  | awaitReply _ _ => simp [hph] at h
  | awaitEffect _ => simp [hph] at h
  | awaitPeer _ => simp [hph] at h
  | crashed => simp [hph] at h

theorem detach_keep (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).life = a.life ∧
      (detachReply (detachBox a caller) caller cid).prio = a.prio ∧
      (detachReply (detachBox a caller) caller cid).pendingTombstone = a.pendingTombstone ∧
      (detachReply (detachBox a caller) caller cid).parent = a.parent := by
  unfold detachReply detachBox
  split <;> simp

theorem detach_phase (I : Impl) (template : String) (a : Actor) (caller : InstId) (cid : Nat)
    (h : phaseDeclared I template a.phase) :
    phaseDeclared I template (detachReply (detachBox a caller) caller cid).phase := by
  unfold detachReply
  split
  · simpa [detachBox] using clear_phase_declared I template caller a.phase (by simpa [detachBox] using h)
  · simpa [detachBox] using h

theorem hold_credits (I : Impl) (ps : List Parked) (w : World) (hH : Hold I w)
    (name : String) (sender : InstId) (hpre : w.crashed = false) :
    Hold I (ps.foldl (fun acc _ => creditSender acc name sender) w) := by
  induction ps generalizing w with
  | nil => simpa using hH
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih (creditSender w name sender) (hold_credit I w hH name sender hpre)
      (by simp [creditSender, setActor, hpre])

theorem hold_refund_call (I : Impl) (w : World) (hH : Hold I w) (caller dst : InstId)
    (hpre : w.crashed = false) : Hold I (refundParkedCall w caller dst) := by
  unfold refundParkedCall
  by_cases hempty :
      (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = true
  · simp [hempty]
    exact hH
  · simp only [hempty]
    let keep := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall)
    let base := setActor w dst { (w.st dst) with parked := keep }
    have hB := hold_set I w hH dst { (w.st dst) with parked := keep }
      (by simp) (by simp) (by simp) (by simp)
      (fun hmem => by simpa using hH.phase dst hmem) hpre
    have hpreB : base.crashed = false := by simp [base, setActor, hpre]
    simpa [keep, base] using hold_credits I
      ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall)
      base hB (tname dst) caller hpreB

theorem timeout_declared (I : Impl) (template : String) (k : Cont)
    (h : ContDeclared I template k) : ContDeclared I template
      { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout } :=
  ⟨h.timeout, h.na, h.to, h.timeout⟩

/-- A deadline keeps the lane invariant. The caller finishes on the continuation
the static check allowed, and a parked call returns its token. -/
theorem hold_timeout (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hpre : w.crashed = false) (w' : World) (h : callTimeout w id = some w') : Hold I w' := by
  unfold callTimeout at h
  by_cases hlive : (w.st id).life = .alive
  · have hbit : ((w.st id).life != .alive) = false := by simpa [bne, beq_iff_eq] using hlive
    simp only [hbit] at h
    have hmem : id ∈ w.roster := hH.rostered id (by simp [hlive])
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      have hdec : ContDeclared I (tname id) k := by
        simpa [hph, phaseDeclared] using hH.phase id hmem
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hkeep := detach_keep (w.st dst) id cid
      have h1 := hold_set I w hH dst host hkeep.1 hkeep.2.1 hkeep.2.2.1 hkeep.2.2.2
        (fun hdst => detach_phase I (tname dst) (w.st dst) id cid (hH.phase dst hdst)) hpre
      have hpre1 : w1.crashed = false := by simp [w1, setActor, hpre]
      have hdone := hold_set I w1 h1 id (finishCall (w1.st id) k .timedOut)
        (finish_keep (w1.st id) k .timedOut).1
        (finish_keep (w1.st id) k .timedOut).2.1
        (finish_keep (w1.st id) k .timedOut).2.2
        (finish_parent (w1.st id) k .timedOut)
        (fun _ => finish_declared I (tname id) (w1.st id) k .timedOut hdec) hpre1
      have heq : w' = setActor w1 id (finishCall (w1.st id) k .timedOut) := by
        simpa [cid, host, w1, Option.some.injEq] using h.symm
      exact heq ▸ hdone
    | parked dst c k =>
      cases c with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        have hdec : ContDeclared I (tname id) k := by
          simpa [hph, phaseDeclared] using hH.phase id hmem
        let wR := refundParkedCall w id dst
        have hR := hold_refund_call I w hH id dst hpre
        have hpreR : wR.crashed = false := by
          simpa [wR, (refund_call_frame w id dst id).2.2.2.2.2.2] using hpre
        have hdone := hold_set I wR hR id (finishCall (wR.st id) k .notAdmitted)
          (finish_keep (wR.st id) k .notAdmitted).1
          (finish_keep (wR.st id) k .notAdmitted).2.1
          (finish_keep (wR.st id) k .notAdmitted).2.2
          (finish_parent (wR.st id) k .notAdmitted)
          (fun _ => finish_declared I (tname id) (wR.st id) k .notAdmitted hdec) hpreR
        have heq : w' = setActor wR id (finishCall (wR.st id) k .notAdmitted) := by
          simpa [wR, Option.some.injEq] using h.symm
        exact heq ▸ hdone
    | awaitPeer k =>
      simp only [hph] at h
      have hdec : ContDeclared I (tname id) k := by
        simpa [hph, phaseDeclared] using hH.phase id hmem
      let kT := { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }
      have hto := timeout_declared I (tname id) k hdec
      have hP := hold_reply_proceed I w hH id kT hpre hto
      have heq : w' = setActor w id (proceed (w.st id) kT) := by
        simpa [kT, Option.some.injEq] using h.symm
      exact heq ▸ hP
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | crashed => simp [hph] at h
  · have hbit : ((w.st id).life != .alive) = true := by simpa [bne, beq_iff_eq] using hlive
    simp [hbit] at h

/-- Every enabled step keeps the lane invariant. A scheduler spawn is the step
that spends `IxPast` and `RootPast`. A per-peer child spawn spends one key. -/
theorem hold_step (I : Impl) (w w' : World) (hH : Hold I w) (hG : GraphOk I.desc)
    (hnd : w.roster.Nodup) (hI : IxPast I w) (hR : RootPast I w)
    (hoff : ∀ i, i ∉ w.roster → (w.st i).prio = []) (a : Action)
    (h : apply I a w = some w') : Hold I w' := by
  have hpre : w.crashed = false := (apply_step I a w w' h).1
  have hstep : stepWorld I a w = some w' := (apply_step I a w w' h).2
  cases a with
  | recvBulk s =>
    exact hold_recv_bulk I w w' hH s (by simpa [stepWorld] using hstep) hpre
  | recvPrio s =>
    exact hold_recv_prio I w w' hH s (by simpa [stepWorld] using hstep) hpre
  | exec s =>
    exact hold_exec I w hH hG hnd s hpre hoff w' (by simpa [stepWorld] using hstep)
  | finish s =>
    exact hold_finish I w w' hH s (by simpa [stepWorld] using hstep) hpre
  | spawn template =>
    exact hold_spawn I w w' hH hI hR template hpre hoff (by simpa [stepWorld] using hstep)
  | ingress dst label =>
    exact hold_ingress I w w' hH dst label (by simpa [stepWorld] using hstep) hpre
  | callTimeout s =>
    exact hold_timeout I w hH s hpre w' (by simpa [stepWorld] using hstep)
  | stutter =>
    exact (stutter_unchanged I w w' h).symm ▸ hH

/-! Keys already handed out, a duplicate-free roster, and an empty lane off it.
`hold_step` consumes this. A reachable world keeps it, which is what lets the
seal bound run on every world a run can reach. -/

/-- A world reached from the initial roster. `ix` and `root` are the counters
`spawn` has already stepped past. An id that is not on the roster still has
the empty priority lane it was born without. -/
structure Side (I : Impl) (w : World) : Prop where
  ix : IxPast I w
  root : RootPast I w
  nd : w.roster.Nodup
  off : ∀ i, i ∉ w.roster → (w.st i).prio = []

/-- `w'` is `w` with the same roster and the same key counters. An id off the
roster keeps the priority lane it had. -/
structure Frame (w w' : World) : Prop where
  ros : w'.roster = w.roster
  ix : ∀ n, w'.nextIx n = w.nextIx n
  key : ∀ s, w'.nextKey s = w.nextKey s
  off : ∀ i, i ∉ w.roster → (w'.st i).prio = (w.st i).prio

/-- An alive actor is on the roster. `Hold.rostered` gives this. -/
def OnRoster (w : World) : Prop := ∀ i, (w.st i).life = .alive → i ∈ w.roster

theorem frame_refl (w : World) : Frame w w :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem frame_trans {w1 w2 w3 : World} (h12 : Frame w1 w2) (h23 : Frame w2 w3) : Frame w1 w3 :=
  ⟨h23.ros.trans h12.ros, fun n => (h23.ix n).trans (h12.ix n),
   fun s => (h23.key s).trans (h12.key s), fun i hi => by
     have hi2 : i ∉ w2.roster := by
       intro h
       exact hi (by simpa [h12.ros] using h)
     exact (h23.off i hi2).trans (h12.off i hi)⟩

theorem frame_keep (w : World) (id : InstId) (a : Actor) (hp : a.prio = (w.st id).prio) :
    Frame w (setActor w id a) := by
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro i _
  by_cases h : i = id
  · simp [setActor, h, hp]
  · simp [setActor, h]

theorem frame_touch (w : World) (id : InstId) (a : Actor) (hid : id ∈ w.roster) :
    Frame w (setActor w id a) := by
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro i hi
  have hne : i ≠ id := by
    intro heq
    exact hi (heq ▸ hid)
  simp [setActor, hne]

theorem frame_crash (w : World) : Frame w (crashWorld w) := by
  unfold crashWorld
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro i hi
  have hd : decide (i ∈ w.roster) = false := by
    cases hbit : decide (i ∈ w.roster) with
    | false => rfl
    | true => exact absurd (of_decide_eq_true hbit) hi
  simp [hd]

theorem side_frame (I : Impl) (w w' : World) (hS : Side I w) (hF : Frame w w') : Side I w' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n k g hmem t ht hsup hsub
    have hmem0 : InstId.peer n k g ∈ w.roster := by simpa [hF.ros] using hmem
    simpa [hF.ix n] using hS.ix n k g hmem0 t ht hsup hsub
  · intro n k g hmem t ht hsub hroot sup hsup
    have hmem0 : InstId.peer n k g ∈ w.roster := by simpa [hF.ros] using hmem
    simpa [hF.key ""] using hS.root n k g hmem0 t ht hsub hroot sup hsup
  · simpa [hF.ros] using hS.nd
  · intro i hi
    have hi0 : i ∉ w.roster := by
      intro h
      exact hi (by simpa [hF.ros] using h)
    rw [hF.off i hi0]
    exact hS.off i hi0

theorem readCells_nextKey (D : Description) (w : World) (id : InstId) (name : String) :
    (readCells D w id).nextKey name = w.nextKey name := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem cells_frame (D : Description) (w : World) (id : InstId) : Frame w (readCells D w id) :=
  ⟨cellsRoster D w id, fun n => readCells_nextIx D w id n, fun s => readCells_nextKey D w id s,
   fun i _ => congrArg Actor.prio (cellsSt D w id i)⟩

theorem cell_frame (w : World) (dst label : String) (c : Cell) : Frame w (setCell w dst label c) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem note_frame (w : World) (id : InstId) (dst : String) : Frame w (noteStale w id dst) := by
  refine ⟨noteStale_roster w id dst, ?_, ?_, ?_⟩
  · intro n
    simp [noteStale]
  · intro s
    simp [noteStale]
  · intro i _
    simp [noteStale]

theorem credit_frame (w : World) (name : String) (s : InstId) : Frame w (creditSender w name s) := by
  refine ⟨by simp [creditSender, setActor], fun _ => by simp [creditSender, setActor],
    fun _ => by simp [creditSender, setActor], ?_⟩
  intro i _
  by_cases h : i = s
  · simp [creditSender, setActor, bumpToken, h]
  · simp [creditSender, setActor, h]

theorem live_frame (w : World) (name : String) (s : InstId) : Frame w (creditLive w name s) := by
  simpa [creditLive] using credit_frame w name (budgetHolder w s)

theorem msgs_frame (w : World) (name : String) (ms : List Msg) : Frame w (refundMsgs w name ms) := by
  unfold refundMsgs
  induction ms generalizing w with
  | nil =>
    simp
    exact frame_refl w
  | cons m ms ih =>
    simp only [List.foldl_cons]
    exact frame_trans (live_frame w name m.sender) (ih _)

theorem parkedRefund_frame (w : World) (name : String) (ps : List Parked) :
    Frame w (refundParked w name ps) := by
  unfold refundParked
  induction ps generalizing w with
  | nil =>
    simp
    exact frame_refl w
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact frame_trans (live_frame w name p.msg.sender) (ih _)

theorem outbound_step_frame (w : World) (dead host : InstId) : Frame w
    (if host == dead then w
     else
       let dropped := (w.st host).parked.filter fun p => p.sender == dead
       if dropped.isEmpty then w
       else
         let w := setActor w host
           { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
         setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) := by
  by_cases hhost : (host == dead) = true
  · simp only [hhost, ite_true]
    exact frame_refl w
  · have hf : (host == dead) = false := by
      cases hb : host == dead with
      | false => rfl
      | true => exact absurd hb hhost
    simp only [hf]
    by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · simp only [hempty, ite_true]
      exact frame_refl w
    · have hne : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false := by
        cases hb : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty with
        | false => rfl
        | true => exact absurd hb hempty
      simp only [hne]
      let hostA : Actor :=
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      let wH := setActor w host hostA
      let n := ((w.st host).parked.filter fun p => p.sender == dead).length
      exact frame_trans (frame_keep w host hostA (by simp [hostA]))
        (frame_keep wH dead (addTokens (wH.st dead) (tname host) n) (by simp [addTokens]))

theorem outbound_frame (w : World) (dead : InstId) : Frame w (releaseOutbound w dead) := by
  unfold releaseOutbound
  suffices ∀ (ids : List InstId) (w0 : World), Frame w0 (ids.foldl (fun w host =>
      if host == dead then w
      else
        let dropped := (w.st host).parked.filter fun p => p.sender == dead
        if dropped.isEmpty then w
        else
          let w := setActor w host
            { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
          setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) w0) by
    exact this w.roster w
  intro ids
  induction ids with
  | nil =>
    intro w0
    simp
    exact frame_refl w0
  | cons host hosts ih =>
    intro w0
    simp only [List.foldl_cons]
    exact frame_trans (outbound_step_frame w0 dead host) (ih _)

theorem resumeOne_frame (id : InstId) (p : Parked) (w : World) : Frame w (tmb_resumeOne id w p) := by
  unfold tmb_resumeOne
  by_cases hskip : (p.isCall || p.sender = id) = true
  · simp only [hskip, ite_true]
    exact frame_refl w
  · have hf : (p.isCall || p.sender = id) = false := by
      cases hb : p.isCall || p.sender = id with
      | false => rfl
      | true => exact absurd hb hskip
    simp only [hf]
    exact frame_keep w p.sender (resumeSender (w.st p.sender) false id)
      (by simpa using resumeSender_prio (w.st p.sender) false id)

theorem parked_frame (w : World) (id : InstId) (ps : List Parked) : Frame w (releaseParked w id ps) := by
  rw [tmb_resumeOne_eq w id ps]
  induction ps generalizing w with
  | nil =>
    simp
    exact frame_refl w
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact frame_trans (resumeOne_frame id p w) (ih _)

theorem release_frame (D : Description) (w : World) (id : InstId) (a : Actor) (hid : id ∈ w.roster) :
    Frame w (releaseWorld D w id a) := by
  unfold releaseWorld
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) a.box
  let w3 := refundParked w2 (tname id) a.parked
  let w4 := releaseOutbound w3 id
  let dead : Actor := { w4.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1 : Frame w w1 := by simpa [w1] using cells_frame D w id
  have h2 : Frame w1 w2 := by simpa [w2] using msgs_frame w1 (tname id) a.box
  have h3 : Frame w2 w3 := by simpa [w3] using parkedRefund_frame w2 (tname id) a.parked
  have h4 : Frame w3 w4 := by simpa [w4] using outbound_frame w3 id
  have hid4 : id ∈ w4.roster := by
    simpa [h4.ros, h3.ros, h2.ros, h1.ros] using hid
  have h5 : Frame w4 (setActor w4 id dead) := frame_touch w4 id dead hid4
  have h6 : Frame (setActor w4 id dead) (releaseParked (setActor w4 id dead) id a.parked) :=
    parked_frame _ id a.parked
  exact frame_trans h1 (frame_trans h2 (frame_trans h3 (frame_trans h4 (frame_trans h5 h6))))

theorem on_release (D : Description) (w : World) (id : InstId) (a : Actor)
    (hid : id ∈ w.roster) (hA : OnRoster w) : OnRoster (releaseWorld D w id a) := by
  intro i hi
  have hF := release_frame D w id a hid
  simpa [hF.ros] using hA i (releaseWorld_prev D w id a i hi)

theorem offer_frame (D : Description) (w : World) (host : InstId) (msg : Msg) (h : host ∈ w.roster) :
    Frame w (offerPrio D w host msg) := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = true
  · simp only [hfull, ite_true]
    exact frame_crash w
  · have hf : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = false := by
      cases hb : decide (prioLoad (w.st host).prio >= capPrio D w.N host) with
      | false => rfl
      | true => exact absurd hb hfull
    simp only [hf]
    exact frame_touch w host
      { (w.st host) with prio := (w.st host).prio ++ [msg], nextMid := (w.st host).nextMid + 1 } h

theorem enqueue_frame (D : Description) (w : World) (child : InstId) (hA : OnRoster w) :
    Frame w (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none =>
    exact frame_refl w
  | some parent =>
    by_cases hdead : ((w.st parent).life != .alive) = true
    · simp only [hdead, ite_true]
      exact frame_refl w
    · have hlive : (w.st parent).life = .alive := by simpa [bne, beq_iff_eq] using hdead
      have hmem : parent ∈ w.roster := hA parent hlive
      by_cases hlabel : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hdead, hlabel, ite_true]
        exact frame_crash w
      · have hf : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlabel
        simp only [hdead, hf]
        exact offer_frame D w parent (tombstoneMsg D (w.st parent) child) hmem

theorem seal_actor_frame (D : Description) (w : World) (id : InstId) (a : Actor)
    (hid : id ∈ w.roster) (hA : OnRoster w) : Frame w (sealActor D w id a) := by
  unfold sealActor
  exact frame_trans (release_frame D w id a hid)
    (enqueue_frame D (releaseWorld D w id a) id (on_release D w id a hid hA))


theorem shutdown_frame (D : Description) (w : World) (id : InstId) (hA : OnRoster w) :
    Frame w (shutdownActor D w id) := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true]
    have hl : (w.st id).life = .alive := by simpa [beq_iff_eq] using hlive
    exact seal_actor_frame D w id (w.st id) (hA id hl) hA
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp only [hf, ite_false]
    exact frame_refl w

theorem seal_frame (fuel : Nat) (D : Description) :
    ∀ w id, id ∈ w.roster → Frame w (sealBranch fuel D w id) := by
  induction fuel with
  | zero =>
    intro w id _
    simp [sealBranch]
    exact frame_refl w
  | succ fuel ih =>
    intro w id hid
    simp only [sealBranch]
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel D w0 child else w0
    have hfold : ∀ (ids : List InstId) (w0 : World), (∀ c, c ∈ ids → c ∈ w0.roster) →
      Frame w0 (ids.foldl step w0) := by
      intro ids
      induction ids with
      | nil =>
        intro w0 _
        simp
        exact frame_refl w0
      | cons child ids ihids =>
        intro w0 hids
        simp only [List.foldl_cons, step]
        by_cases hc : isChild w0 id child = true
        · have hhead : child ∈ child :: ids := List.mem_cons_self
          have hmem : child ∈ w0.roster := hids child hhead
          have hstep := ih w0 child hmem
          simp only [hc, ite_true]
          have hids' : ∀ c, c ∈ ids → c ∈ (sealBranch fuel D w0 child).roster := by
            intro c hcmem
            simpa [hstep.ros] using hids c (List.mem_cons_of_mem child hcmem)
          exact frame_trans hstep (ihids _ hids')
        · have hf : isChild w0 id child = false := by
            cases hb : isChild w0 id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf]
          exact ihids w0 (fun c hcmem => hids c (List.mem_cons_of_mem child hcmem))
    let sealed := w.roster.foldl step w
    have hmid := hfold w.roster w (fun _ h => h)
    have hidS : id ∈ sealed.roster := by
      rw [hmid.ros]
      exact hid
    change Frame w (if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id) else sealed)
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · simp only [hgo, ite_true]
      exact frame_trans hmid (release_frame D sealed id (sealed.st id) hidS)
    · have hf : ((sealed.st id).life == .alive) = false := by
        cases hb : (sealed.st id).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf]
      exact hmid

theorem drop_frame (D : Description) (w : World) (id : InstId) : Frame w (dropDescendants D w id) := by
  unfold dropDescendants
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 id child then sealBranch w.roster.length D w0 child else w0
  have hfold : ∀ (ids : List InstId) (w0 : World), (∀ c, c ∈ ids → c ∈ w0.roster) →
      Frame w0 (ids.foldl step w0) := by
    intro ids
    induction ids with
    | nil =>
      intro w0 _
      simp
      exact frame_refl w0
    | cons child ids ih =>
      intro w0 hids
      simp only [List.foldl_cons, step]
      by_cases hc : isChild w0 id child = true
      · have hhead : child ∈ child :: ids := List.mem_cons_self
        have hmem : child ∈ w0.roster := hids child hhead
        have hstep := seal_frame w.roster.length D w0 child hmem
        simp only [hc, ite_true]
        have hids' : ∀ c, c ∈ ids → c ∈ (sealBranch w.roster.length D w0 child).roster := by
          intro c hcmem
          simpa [hstep.ros] using hids c (List.mem_cons_of_mem child hcmem)
        exact frame_trans hstep (ih _ hids')
      · have hf : isChild w0 id child = false := by
          cases hb : isChild w0 id child with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih w0 (fun c hcmem => hids c (List.mem_cons_of_mem child hcmem))
  exact hfold w.roster w (fun _ h => h)

theorem on_of (w w' : World) (hA : OnRoster w) (hros : w'.roster = w.roster)
    (hlive : ∀ i, (w'.st i).life = .alive → (w.st i).life = .alive) : OnRoster w' := by
  intro i hi
  exact hros.symm ▸ hA i (hlive i hi)

theorem drop_on (D : Description) (w : World) (id : InstId) (hA : OnRoster w) :
    OnRoster (dropDescendants D w id) :=
  on_of w (dropDescendants D w id) hA (drop_roster D w id)
    (fun i hi => dropDescendants_prev D w id i hi)

theorem shutdown_on (D : Description) (w : World) (id : InstId) (hA : OnRoster w) :
    OnRoster (shutdownActor D w id) :=
  on_of w (shutdownActor D w id) hA (shutdown_roster D w id)
    (fun i hi => shutdownActor_prev D w id i hi)

theorem abort_frame (D : Description) (w : World) (parent : InstId) (hA : OnRoster w) :
    Frame w (abortChildren D w parent) := by
  unfold abortChildren
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 parent child && (w0.st child).life == .alive then
      shutdownActor D (dropDescendants D w0 child) child
    else w0
  have hfold : ∀ (ids : List InstId) (w0 : World), OnRoster w0 → (∀ c, c ∈ ids → c ∈ w0.roster) →
      Frame w0 (ids.foldl step w0) := by
    intro ids
    induction ids with
    | nil =>
      intro w0 _ _
      simp
      exact frame_refl w0
    | cons child ids ih =>
      intro w0 hA0 hids
      simp only [List.foldl_cons, step]
      by_cases hc : (isChild w0 parent child && (w0.st child).life == .alive) = true
      · simp only [hc, ite_true]
        have hDrop := drop_frame D w0 child
        have hA1 : OnRoster (dropDescendants D w0 child) := drop_on D w0 child hA0
        have hShut := shutdown_frame D (dropDescendants D w0 child) child hA1
        have hA2 : OnRoster (shutdownActor D (dropDescendants D w0 child) child) :=
          shutdown_on D (dropDescendants D w0 child) child hA1
        exact frame_trans (frame_trans hDrop hShut)
          (ih _ hA2 (fun c hcmem => by
            have hmem := hids c (List.mem_cons_of_mem child hcmem)
            simpa [hShut.ros, hDrop.ros] using hmem))
      · have hf : (isChild w0 parent child && (w0.st child).life == .alive) = false := by
          cases hb : isChild w0 parent child && (w0.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih w0 hA0 (fun c hcmem => hids c (List.mem_cons_of_mem child hcmem))
  exact hfold w.roster w hA (fun _ h => h)

theorem stage_frame (D : Description) (w : World) (id : InstId) (a : Actor) (hA : OnRoster w) :
    Frame w (terminateStage D w id a) := by
  unfold terminateStage
  exact frame_trans (drop_frame D w id)
    (shutdown_frame D (dropDescendants D w id) id (drop_on D w id hA))

theorem side_core_is_core (D : Description) (id : InstId) (h : id ∈ coreRoster D) :
    ∃ name, id = InstId.core name := by
  unfold coreRoster at h
  rw [List.mem_filterMap] at h
  obtain ⟨t, _, hif⟩ := h
  by_cases hb : (t.multiplicity == .one) = true
  · simp only [hb, ite_true] at hif
    injection hif with hid
    exact ⟨t.name, hid.symm⟩
  · have hf : (t.multiplicity == .one) = false := by
      cases hbb : t.multiplicity == .one with
      | false => rfl
      | true => exact absurd hbb hb
    simp only [hf] at hif
    simp at hif

theorem side_peer_not_core (D : Description) (n : String) (k g : Nat) :
    InstId.peer n k g ∉ coreRoster D := by
  intro h
  obtain ⟨name, hid⟩ := side_core_is_core D _ h
  cases hid

theorem side_core_filter_nodup (xs : List Template) (h : (xs.map (·.name)).Nodup) :
    (xs.filterMap fun t => if t.multiplicity == .one then some (InstId.core t.name) else none).Nodup := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    have hcons := List.nodup_cons.mp h
    rw [List.filterMap_cons]
    by_cases hb : (t.multiplicity == .one) = true
    · simp only [hb, ite_true]
      refine List.nodup_cons.mpr ⟨?_, ih hcons.2⟩
      intro hin
      have hname : t.name ∈ ts.map (·.name) := by
        rw [List.mem_filterMap] at hin
        obtain ⟨u, hu, hif⟩ := hin
        cases hub : u.multiplicity == .one <;> rw [hub] at hif
        · simp at hif
        · simp at hif
          exact List.mem_map.mpr ⟨u, hu, hif⟩
      exact hcons.1 hname
    · have hf : (t.multiplicity == .one) = false := by
        cases hbb : t.multiplicity == .one <;> simp_all
      simp only [hf]
      exact ih hcons.2

theorem side_core_nodup (D : Description) (hG : GraphOk D) : (coreRoster D).Nodup := by
  simpa [coreRoster] using side_core_filter_nodup D.templates (names_nodup D hG)

theorem side_init (I : Impl) (N : Nat) (hG : GraphOk I.desc) : Side I (initWorld I N) := by
  have hst (i : InstId) :
      ((initWorld I N).st i) =
        if (coreRoster I.desc).contains i then initActor I.desc i else absentActor := by
    simpa [initWorld] using tmb_cell_fold_st I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } i
  have hros : (initWorld I N).roster = coreRoster I.desc := by
    simpa [initWorld] using tmb_cell_fold_roster I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n k g hmem _ _ _ _
    exact absurd (by simpa [hros] using hmem) (side_peer_not_core I.desc n k g)
  · intro n k g hmem _ _ _ _ _ _
    exact absurd (by simpa [hros] using hmem) (side_peer_not_core I.desc n k g)
  · simpa [hros] using side_core_nodup I.desc hG
  · intro i hi
    have hnin : i ∉ coreRoster I.desc := by simpa [hros] using hi
    rw [hst i]
    by_cases hc : (coreRoster I.desc).contains i = true
    · exact absurd (List.elem_iff.mp hc) hnin
    · have hf : (coreRoster I.desc).contains i = false := by
        cases hbit : (coreRoster I.desc).contains i <;> simp_all
      have houtside : i ∉ coreRoster I.desc := by
        intro hin
        exact absurd (List.elem_iff.mpr hin) (by simpa using hf)
      simp [houtside, absentActor]

theorem sup_is_some (s : Option String) (name : String) (h : supNamed s name = true) : s = some name := by
  cases s with
  | none => simp [supNamed] at h
  | some n => simpa [supNamed, beq_iff_eq] using h

theorem peer_not_root (I : Impl) (w : World) (parent : InstId) (t : Template)
    (hH : Hold I w) (hmem : parent ∈ w.roster) (hp : ∃ n k g, parent = InstId.peer n k g)
    (hsup : t.supervisor = some (tname parent)) : rootOf I.desc t = false := by
  rcases hp with ⟨_, _, _, hp⟩
  unfold rootOf
  simp only [hsup]
  cases ht : templateOf I.desc (tname parent) with
  | none => rfl
  | some sup =>
    dsimp
    obtain ⟨t', ht', hmul⟩ := hH.role parent hmem
    have hsame : t' = sup := by
      rw [ht'] at ht
      injection ht
    rw [hp] at hmul
    have hper : sup.multiplicity = Multiplicity.perPeer := by simpa [hsame, tmb_role] using hmul
    rw [hper]
    decide

theorem place_facts (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster) :
    (∀ i, (placePeer I w template k initial parent next).st i =
        if i = InstId.peer template k (maxGen w template k) then
          { bornActor I.desc w template k initial with parent := parent } else w.st i) ∧
      (placePeer I w template k initial parent next).roster =
        w.roster ++ [InstId.peer template k (maxGen w template k)] ∧
      (∀ n, (placePeer I w template k initial parent next).nextIx n =
        (next { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] }).nextIx n) ∧
      (∀ s, (placePeer I w template k initial parent next).nextKey s =
        (next { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] }).nextKey s) := by
  let id := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  let base := { w with roster := w.roster ++ [id] }
  let mid := next base
  let planted := setActor mid id born
  have hw' : placePeer I w template k initial parent next = readCells I.desc planted id := by
    simp [placePeer, id, born, base, mid, planted]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hw', show (readCells I.desc planted id).st i = planted.st i from cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h, id, born]
    · simp [planted, setActor, h, mid, (hnext base i).1, base, id, born]
  · rw [hw', show (readCells I.desc planted id).roster = planted.roster from cellsRoster I.desc planted id]
    simp [planted, setActor, mid, (hnext base id).2, base, id]
  · intro n
    rw [hw']
    simpa [planted, setActor, mid] using readCells_nextIx I.desc planted id n
  · intro s
    rw [hw']
    simpa [planted, setActor, mid] using readCells_nextKey I.desc planted id s

theorem birth_pack (I : Impl) (w w' : World) (id : InstId) (hS : Side I w)
    (hros : w'.roster = w.roster ++ [id]) (hnew : id ∉ w.roster)
    (hst : ∀ i, i ≠ id → w'.st i = w.st i) (hix : IxPast I w') (hroot : RootPast I w') :
    Side I w' := by
  refine ⟨hix, hroot, ?_, ?_⟩
  · simpa [hros] using tmb_nodup_concat w.roster id hS.nd hnew
  · intro i hi
    have hne : i ≠ id := by
      intro heq
      apply hi
      rw [hros, heq]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hold : i ∉ w.roster := by
      intro hm
      apply hi
      rw [hros]
      exact List.mem_append_left _ hm
    rw [hst i hne]
    exact hS.off i hold

/-- A birth into a nonempty subtree does not spend `IxPast` or `RootPast`.
Both counters those predicates read stay where they were, and the new id's
subtree is not the empty one. -/
theorem later_side (I : Impl) (w : World) (hS : Side I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hsub : t.subtree ≠ "") (parent : Option InstId) :
    Side I (placePeer I w template (freshKey I.desc w t.subtree) t.initial parent
      (fun u => { u with nextKey := fun s =>
        if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })) := by
  let k := freshKey I.desc w t.subtree
  let id := InstId.peer template k (maxGen w template k)
  let next : World → World := fun u =>
    { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
  let w' := placePeer I w template k t.initial parent next
  have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster := by
    intro _ _; exact ⟨rfl, rfl⟩
  have hf := place_facts I w template k t.initial parent next hnext
  have hros : w'.roster = w.roster ++ [id] := by simpa [w', id] using hf.2.1
  have hixU (n : String) : w'.nextIx n = w.nextIx n := by simpa [w', next] using hf.2.2.1 n
  have hneS : "" ≠ t.subtree := fun h => hsub h.symm
  have hkeyU : w'.nextKey "" = w.nextKey "" := by
    have hpt := hf.2.2.2 ""
    simp only [next, hneS] at hpt
    simpa using hpt
  have hix : IxPast I w' := by
    intro n key g hmem t' ht' hsup' hsub'
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      rw [hixU n]
      exact hS.ix n key g hold t' ht' hsup' hsub'
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rw [heqt] at hsub'
      exact absurd hsub' hsub
  have hroot : RootPast I w' := by
    intro n key g hmem t' ht' hsub' hrootB sup hsome
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      rw [hkeyU]
      exact hS.root n key g hold t' ht' hsub' hrootB sup hsome
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rw [heqt] at hsub'
      exact absurd hsub' hsub
  have hst : ∀ i, i ≠ id → w'.st i = w.st i := by
    intro i hne
    have h := hf.1 i
    simp [id, hne] at h
    exact h
  simpa [w', k, next] using birth_pack I w w' id hS hros (gen_fresh w template k) hst hix hroot

/-- An unsupervised empty subtree takes its next key from `nextIx`. -/
theorem ix_side (I : Impl) (w : World) (hS : Side I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hsup : t.supervisor = none) :
    Side I (placePeer I w template (w.nextIx template) t.initial none
      (fun u => { u with nextIx := fun n =>
        if n = template then w.nextIx template + 1 else u.nextIx n })) := by
  let k := w.nextIx template
  let id := InstId.peer template k (maxGen w template k)
  let next : World → World := fun u =>
    { u with nextIx := fun n => if n = template then k + 1 else u.nextIx n }
  let w' := placePeer I w template k t.initial none next
  have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster := by
    intro _ _; exact ⟨rfl, rfl⟩
  have hf := place_facts I w template k t.initial none next hnext
  have hros : w'.roster = w.roster ++ [id] := by simpa [w', id] using hf.2.1
  have hixU (n : String) : w'.nextIx n = if n = template then k + 1 else w.nextIx n := by
    simpa [w', next] using hf.2.2.1 n
  have hkeyU : w'.nextKey "" = w.nextKey "" := by simpa [w', next] using hf.2.2.2 ""
  have hix : IxPast I w' := by
    intro n key g hmem t' ht' hsup' hsub'
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      by_cases hn : n = template
      · have hlt := hS.ix n key g hold t' ht' hsup' hsub'
        rw [hn] at hlt
        rw [hixU n, hn]
        simp
        omega
      · rw [hixU n]
        simp [hn]
        exact hS.ix n key g hold t' ht' hsup' hsub'
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn hk _
      rw [hixU n]
      simp [hn, hk]
  have hrootP : RootPast I w' := by
    intro n key g hmem t' ht' hsub' hrootB sup hsome
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      rw [hkeyU]
      exact hS.root n key g hold t' ht' hsub' hrootB sup hsome
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rw [heqt] at hsome
      rw [hsup] at hsome
      cases hsome
  have hst : ∀ i, i ≠ id → w'.st i = w.st i := by
    intro i hne
    have h := hf.1 i
    simp [id, hne] at h
    exact h
  simpa [w', k, next] using birth_pack I w w' id hS hros (gen_fresh w template k) hst hix hrootP

/-- An empty subtree under a core takes its next key from `nextKey ""`. -/
theorem root_side (I : Impl) (w : World) (hS : Side I w) (template : String) (t : Template)
    (name : String) (ht : templateOf I.desc template = some t) (hsup : t.supervisor = some name) :
    Side I (placePeer I w template (freshKey I.desc w "") t.initial (some (.core name))
      (fun u => { u with nextKey := fun s =>
        if s = "" then freshKey I.desc w "" + 1 else u.nextKey s })) := by
  let k := freshKey I.desc w ""
  have hk : k = w.nextKey "" := freshKey_empty I.desc w
  let id := InstId.peer template k (maxGen w template k)
  let next : World → World := fun u =>
    { u with nextKey := fun s => if s = "" then k + 1 else u.nextKey s }
  let w' := placePeer I w template k t.initial (some (.core name)) next
  have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster := by
    intro _ _; exact ⟨rfl, rfl⟩
  have hf := place_facts I w template k t.initial (some (.core name)) next hnext
  have hros : w'.roster = w.roster ++ [id] := by simpa [w', id] using hf.2.1
  have hixU (n : String) : w'.nextIx n = w.nextIx n := by simpa [w', next] using hf.2.2.1 n
  have hkeyU : w'.nextKey "" = k + 1 := by simpa [w', next] using hf.2.2.2 ""
  have hix : IxPast I w' := by
    intro n key g hmem t' ht' hnone hsub'
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      rw [hixU n]
      exact hS.ix n key g hold t' ht' hnone hsub'
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rw [heqt] at hnone
      rw [hsup] at hnone
      cases hnone
  have hrootP : RootPast I w' := by
    intro n key g hmem t' ht' hsub' hrootB sup hsome
    rw [hros] at hmem
    cases List.mem_append.mp hmem with
    | inl hold =>
      have hlt := hS.root n key g hold t' ht' hsub' hrootB sup hsome
      rw [← hk] at hlt
      rw [hkeyU]
      omega
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with _ hk' _
      rw [hkeyU, hk']
      omega
  have hst : ∀ i, i ≠ id → w'.st i = w.st i := by
    intro i hne
    have h := hf.1 i
    simp [id, hne] at h
    exact h
  simpa [w', k, next] using
    birth_pack I w w' id hS hros (gen_fresh w template k) hst hix hrootP

theorem spawn_side (I : Impl) (w w' : World) (hS : Side I w) (template : String)
    (h : spawn I w template = some w') : Side I w' := by
  cases ht : templateOf I.desc template with
  | none => simp [spawn, ht] at h
  | some t =>
    simp only [spawn, ht] at h
    split at h
    · rename_i hmay
      clear hmay
      split at h
      · rename_i name hsup
        by_cases hsub : t.subtree = ""
        · simp [hsub] at h
          have hstep := h.symm
          have hSide := root_side I w hS template t name ht hsup
          simpa [hstep] using hSide
        · simp at h
          have hstep := h.symm
          have hSide := later_side I w hS template t ht hsub (some (.core name))
          simpa [hstep] using hSide
      · rename_i hsup
        split at h
        · rename_i hsubB
          clear hsubB
          simp at h
          have hstep := h.symm
          have hSide := ix_side I w hS template t ht hsup
          simpa [hstep] using hSide
        · rename_i hbit
          have hsub : t.subtree ≠ "" := by
            intro heq
            apply hbit
            simpa [beq_iff_eq] using heq
          simp at h
          have hstep := h.symm
          have hSide := later_side I w hS template t ht hsub none
          simpa [hstep] using hSide
    · simp at h

theorem hold_on (I : Impl) (w : World) (hH : Hold I w) : OnRoster w := by
  intro i hlive
  exact hH.rostered i (by rw [hlive]; intro h; cases h)

theorem mail_ix (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (n : String) :
    (enqueueOrPark w D sender dst msg isCall k).nextIx n = w.nextIx n := by
  unfold enqueueOrPark
  repeat (first | simp [setActor] | split)

theorem mail_key (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (s : String) :
    (enqueueOrPark w D sender dst msg isCall k).nextKey s = w.nextKey s := by
  unfold enqueueOrPark
  repeat (first | simp [setActor] | split)

theorem mail_frame (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : Frame w (enqueueOrPark w D sender dst msg isCall k) :=
  ⟨mail_roster w D sender dst msg isCall k,
   fun n => mail_ix w D sender dst msg isCall k n,
   fun s => mail_key w D sender dst msg isCall k s,
   fun i _ => mail_prio w D sender dst msg isCall k i⟩

theorem deliver_cells (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a' : Actor) (h : deliver I w id a m = some (w1, a')) :
    w1 = readCells I.desc w id ∧ a'.prio = a.prio := by
  unfold deliver at h
  dsimp at h
  split at h
  · simp at h
  · split at h
    · have heq := by simpa [Option.some.injEq] using h
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · split at h
      · split at h
        · simp at h
        · have heq := by simpa [Option.some.injEq] using h
          rcases heq with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      · split at h
        · simp at h
        · split at h
          · have heq := by simpa [Option.some.injEq] using h
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩
          · have heq := by simpa [Option.some.injEq] using h
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩

theorem install_head (w : World) (id : InstId) (a' : Actor) (name : String) (sender : InstId)
    (hp : a'.prio = (w.st id).prio) : Frame w (creditLive (setActor w id a') name sender) :=
  frame_trans (frame_keep w id a' hp) (live_frame (setActor w id a') name sender)

theorem install_parked (w : World) (id : InstId) (a' : Actor) (name : String) (credited resumed : InstId)
    (isCall : Bool) (hp : a'.prio = (w.st id).prio) :
    Frame w (setActor (creditLive (setActor w id a') name credited) resumed
      (resumeSender ((creditLive (setActor w id a') name credited).st resumed) isCall id)) := by
  apply frame_trans
  · exact install_head w id a' name credited hp
  · apply frame_keep
    exact resumeSender_prio _ isCall id

theorem same_prio (w1 : World) (D : Description) (w : World) (id : InstId) (a' : Actor)
    (hc : w1 = readCells D w id) (hp : a'.prio = (w.st id).prio) : a'.prio = (w1.st id).prio := by
  rw [hc]
  simpa [cellsSt] using hp

theorem bulk_frame (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w') :
    Frame w w' := by
  unfold receiveBulk at h
  dsimp at h
  split at h
  · simp at h
  · cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with parked := ps }) p.msg with
        | none =>
          simp only [hbox] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hbox] at hd
          rw [hd] at h
          have hw' : w' = setActor (creditLive (setActor w1 id a') (tname id) p.msg.sender) p.sender
              (resumeSender ((creditLive (setActor w1 id a') (tname id) p.msg.sender).st p.sender)
                p.isCall id) := by
            simpa [Option.some.injEq] using h.symm
          have ⟨hc, hp⟩ := deliver_cells I w id _ p.msg w1 a' hd
          exact hw' ▸ frame_trans (hc ▸ cells_frame I.desc w id)
            (install_parked w1 id a' (tname id) p.msg.sender p.sender p.isCall
              (same_prio w1 I.desc w id a' hc (by simpa using hp)))
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          have hw' : w' = creditLive (setActor w1 id a') (tname id) m.sender := by
            simpa [Option.some.injEq] using h.symm
          have ⟨hc, hp⟩ := deliver_cells I w id _ m w1 a' hd
          exact hw' ▸ frame_trans (hc ▸ cells_frame I.desc w id)
            (install_head w1 id a' (tname id) m.sender
              (same_prio w1 I.desc w id a' hc (by simpa using hp)))
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          have hw' : w' =
              setActor
                (creditLive
                  (setActor w1 id { a' with box := a'.box ++ [p.msg], parked := ps }) (tname id) m.sender)
                p.sender
                (resumeSender
                  ((creditLive
                      (setActor w1 id { a' with box := a'.box ++ [p.msg], parked := ps })
                      (tname id) m.sender).st p.sender) p.isCall id) := by
            simpa [Option.some.injEq] using h.symm
          have ⟨hc, hp⟩ := deliver_cells I w id _ m w1 a' hd
          have hadmit : ({ a' with box := a'.box ++ [p.msg], parked := ps }).prio = a'.prio := rfl
          exact hw' ▸ frame_trans (hc ▸ cells_frame I.desc w id)
            (install_parked w1 id { a' with box := a'.box ++ [p.msg], parked := ps }
              (tname id) m.sender p.sender p.isCall
              (same_prio w1 I.desc w id _ hc (by simpa [hadmit] using hp)))

theorem prio_alive (w : World) (id : InstId)
    (hf : ¬(decide (¬(w.st id).life = .alive) || decide (¬(w.st id).phase = .idle)) = true) :
    (w.st id).life = .alive := by
  have hbit : (decide (¬(w.st id).life = .alive) || decide (¬(w.st id).phase = .idle)) = false := by
    cases hb : decide (¬(w.st id).life = .alive) || decide (¬(w.st id).phase = .idle) with
    | false => rfl
    | true =>
      exfalso
      exact hf hb
  have hL : decide (¬(w.st id).life = .alive) = false := by
    cases hb : decide (¬(w.st id).life = .alive) with
    | false => rfl
    | true => simp [hb] at hbit
  have hnot : ¬(¬(w.st id).life = .alive) := of_decide_eq_false hL
  cases hlife : (w.st id).life with
  | alive => rfl
  | dead =>
    exfalso
    exact hnot (by rw [hlife]; intro h; cases h)
  | absent =>
    exfalso
    exact hnot (by rw [hlife]; intro h; cases h)

theorem prio_frame (I : Impl) (w : World) (hH : Hold I w) (w' : World) (id : InstId)
    (h : receivePrio I w id = some w') : Frame w w' := by
  obtain ⟨m, pre, suf, w1, a', hlive, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  have ⟨hc, _hp⟩ :=
    deliver_cells I w id ({ (w.st id) with prio := pre ++ suf }) m w1 a' hdel
  have hmem : id ∈ w.roster :=
    hH.rostered id (by rw [hlive]; intro hne; cases hne)
  exact hw' ▸ frame_trans (hc ▸ cells_frame I.desc w id)
    (frame_touch w1 id a' (by simpa [hc, cellsRoster] using hmem))

theorem finish_frame (I : Impl) (w w' : World) (id : InstId) (h : finishWait I w id = some w') :
    Frame w w' := by
  unfold finishWait at h
  split at h
  · simp at h
  · cases hph : (w.st id).phase with
    | awaitEffect k =>
      simp [hph] at h
      cases h
      apply frame_keep
      exact proceed_keeps_prio (w.st id) k
    | awaitPeer k =>
      simp [hph] at h
      cases h
      apply frame_keep
      exact proceed_keeps_prio (w.st id) k
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem credits_frame (ps : List Parked) (w : World) (name : String) (sender : InstId) :
    Frame w (ps.foldl (fun acc _ => creditSender acc name sender) w) := by
  induction ps generalizing w with
  | nil =>
    simp
    exact frame_refl w
  | cons _ ps ih =>
    simp only [List.foldl_cons]
    exact frame_trans (credit_frame w name sender) (ih _)

theorem refund_frame (w : World) (caller dst : InstId) : Frame w (refundParkedCall w caller dst) := by
  unfold refundParkedCall
  by_cases hempty :
      (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = true
  · simp only [hempty, ite_true]
    exact frame_refl w
  · have hf :
        (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = false := by
      cases hb : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty with
      | false => rfl
      | true => exact absurd hb hempty
    simp only [hf]
    exact frame_trans
      (frame_keep w dst
        { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) } rfl)
      (credits_frame ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall)
        (setActor w dst
          { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) })
        (tname dst) caller)

theorem timeout_frame (w w' : World) (id : InstId) (h : callTimeout w id = some w') : Frame w w' := by
  dsimp [callTimeout] at h
  split at h
  · simp at h
  · cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp [hph] at h
      cases h
      apply frame_trans
      · apply frame_keep
        exact (detach_keep (w.st dst) id (w.st id).waitId).2.1
      · apply frame_keep
        exact (finish_keep _ k .timedOut).2.1
    | parked dst isCall k =>
      simp [hph] at h
      cases isCall with
      | false => simp at h
      | true =>
        cases h
        apply frame_trans
        · exact refund_frame w id dst
        · apply frame_keep
          exact (finish_keep _ k .notAdmitted).2.1
    | awaitPeer k =>
      simp [hph] at h
      cases h
      apply frame_keep
      exact proceed_keeps_prio (w.st id) _
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem ingress_key (I : Impl) (w w' : World) (dst : InstId) (label s : String)
    (h : receiveIngress I w dst label = some w') : w'.nextKey s = w.nextKey s := by
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
            simp [setActor]

theorem ingress_frame (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') : Frame w w' := by
  refine ⟨(ingress_phase I w w' dst label dst h).2.2.2.2.1, ?_, ?_, ?_⟩
  · intro n
    exact congrFun (ingress_phase I w w' dst label dst h).2.2.2.2.2.2.1 n
  · intro s
    exact ingress_key I w w' dst label s h
  · intro i _
    exact (ingress_phase I w w' dst label i h).2.2.1

theorem try_wake_frame (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (hmem : dstId ∈ w.roster) : Frame w (tryWake D w dstId label writer) := by
  unfold tryWake
  by_cases hskip :
      ((w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp only [hskip, ite_true]
    exact frame_refl w
  · have hf :
        ((w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      cases hb : (w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hskip
    simp only [hf]
    exact offer_frame D w dstId
      { label := label, sender := writer, callFrom := none, reliable := false, mid := (w.st dstId).nextMid }
      hmem

theorem wake_fold (D : Description) (ids : List InstId) (w : World) (label : String) (writer : InstId)
    (hids : ∀ id, id ∈ ids → id ∈ w.roster) :
    Frame w (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil =>
    simp
    exact frame_refl w
  | cons id ids ih =>
    simp only [List.foldl_cons]
    have h1 := try_wake_frame D w id label writer (hids id (List.mem_cons_self))
    exact frame_trans h1 (ih (tryWake D w id label writer) (fun c hc => by
      have hmem := hids c (List.mem_cons_of_mem id hc)
      simpa [h1.ros] using hmem))

theorem wake_frame (D : Description) (w : World) (dst label : String) (writer : InstId) :
    Frame w (wakeReaders D w dst label writer) := by
  unfold wakeReaders
  exact wake_fold D (readersOf w dst) w label writer (fun id h => (List.mem_filter.mp h).1)

theorem reply_frame (w : World) (sender : InstId) (k : Cont) : Frame w (performReply w sender k) := by
  unfold performReply
  cases hto : k.replyTo with
  | none =>
    simp
    apply frame_keep
    exact proceed_keeps_prio (w.st sender) (afterHead k)
  | some caller =>
    simp
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      simp
      split
      · apply frame_trans
        · apply frame_keep
          exact (finish_keep (w.st caller) ck .reply).2.1
        · apply frame_keep
          exact proceed_keeps_prio _ (afterHead k)
      · apply frame_keep
        exact proceed_keeps_prio (w.st sender) (afterHead k)
    | idle =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)
    | run _ =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)
    | parked _ _ _ =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)
    | awaitEffect _ =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)
    | awaitPeer _ =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)
    | crashed =>
      simp
      apply frame_keep
      exact proceed_keeps_prio (w.st sender) (afterHead k)

theorem term_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hlive : a.life = .alive) (hk : ∃ tail, k.rest = .terminate :: tail)
    (hA : OnRoster w) :
    Frame w (execRun I w id a k) := by
  have hstep := exec_term_step I w id a k hlive hk
  generalize hw : execRun I w id a k = wR at hstep
  cases hstep with
  | fall =>
    clear hw
    exact frame_crash w
  | crash _ _ _ =>
    clear hw
    exact frame_crash w
  | lone _ _ _ _ _ _ _ =>
    clear hw
    exact shutdown_frame I.desc w id hA
  | tree _ _ _ _ =>
    clear hw
    exact stage_frame I.desc w id a hA
  | cascade _ _ _ _ _ _ _ =>
    clear hw
    exact stage_frame I.desc w id a hA

theorem alive_mem (I : Impl) (w : World) (hH : Hold I w) (id : InstId)
    (hlive : (w.st id).life = .alive) : id ∈ w.roster :=
  hH.rostered id (by rw [hlive]; intro h; cases h)

theorem admit_view (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (∀ i, (admitBorn I w id a).st i = if i = id then a else w.st i) ∧
      (admitBorn I w id a).roster = w.roster ++ [id] ∧
      (∀ n, (admitBorn I w id a).nextIx n = w.nextIx n) ∧
      (∀ s, (admitBorn I w id a).nextKey s = w.nextKey s) := by
  let base := { w with roster := w.roster ++ [id] }
  let planted := setActor base id a
  have hw : admitBorn I w id a = readCells I.desc planted id := by
    simp [admitBorn, base, planted]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hw]
    rw [cellsSt I.desc planted id i]
    by_cases h : i = id
    · simp [planted, setActor, h]
    · simp [planted, setActor, h, base]
  · rw [hw]
    rw [cellsRoster I.desc planted id]
    simp [planted, setActor, base]
  · intro n
    rw [hw]
    simpa [planted, setActor, base] using readCells_nextIx I.desc planted id n
  · intro s
    rw [hw]
    simpa [planted, setActor, base] using readCells_nextKey I.desc planted id s

/-- A supervised child is not an `IxPast` witness and not a `RootPast` witness.
A peer's child is not a subtree root. -/
theorem admit_side (I : Impl) (w : World) (hH : Hold I w) (hS : Side I w) (child : String)
    (k : Nat) (parent : InstId) (t : Template) (ht : templateOf I.desc child = some t)
    (hsup : supNamed t.supervisor (tname parent) = true)
    (hpeer : ∃ n kk g, parent = InstId.peer n kk g) (hmem : parent ∈ w.roster) :
    Side I (admitBorn I w (InstId.peer child k (maxGen w child k))
      { bornActor I.desc w child k t.initial with parent := some parent }) := by
  let id := InstId.peer child k (maxGen w child k)
  let born := { bornActor I.desc w child k t.initial with parent := some parent }
  let w' := admitBorn I w id born
  have hv := admit_view I w id born
  have hros : w'.roster = w.roster ++ [id] := by simpa [w'] using hv.2.1
  have hixU (n : String) : w'.nextIx n = w.nextIx n := by simpa [w'] using hv.2.2.1 n
  have hkeyU : w'.nextKey "" = w.nextKey "" := by simpa [w'] using hv.2.2.2 ""
  have hix : IxPast I w' := by
    intro n key g hmemR t' ht' hnone hsub'
    rw [hros] at hmemR
    cases List.mem_append.mp hmemR with
    | inl hold =>
      rw [hixU n]
      exact hS.ix n key g hold t' ht' hnone hsub'
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rw [heqt] at hnone
      have hsome := sup_is_some t.supervisor (tname parent) hsup
      rw [hsome] at hnone
      cases hnone
  have hrootP : RootPast I w' := by
    intro n key g hmemR t' ht' hsub' hrootB sup hsome
    rw [hros] at hmemR
    cases List.mem_append.mp hmemR with
    | inl hold =>
      rw [hkeyU]
      exact hS.root n key g hold t' ht' hsub' hrootB sup hsome
    | inr hone =>
      have heq : InstId.peer n key g = id := List.mem_singleton.mp hone
      injection heq with hn _ _
      rw [hn] at ht'
      have heqt : t' = t := by injection ht'.symm.trans ht
      rcases hpeer with ⟨pn, pk, pg, hp⟩
      rw [heqt] at hrootB
      have hrootF := peer_not_root I w parent t hH hmem ⟨pn, pk, pg, hp⟩
        (sup_is_some t.supervisor (tname parent) hsup)
      rw [hrootF] at hrootB
      cases hrootB
  have hst : ∀ i, i ≠ id → w'.st i = w.st i := by
    intro i hne
    have h := hv.1 i
    simp [hne] at h
    exact h
  simpa [w', id, born] using
    birth_pack I w w' id hS hros (gen_fresh w child k) hst hix hrootP

theorem spawn_effect_side (I : Impl) (w : World) (hH : Hold I w) (hS : Side I w) (id : InstId)
    (a : Actor) (k : Cont) (child : String) (es : List Eff) (ha : a = w.st id)
    (hlive : a.life = .alive) (hk : k.rest = .spawn child :: es) : Side I (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  let k' := afterHead k
  have hparent : (w.st id).life = .alive := by simpa [ha] using hlive
  cases ht : templateOf I.desc child with
  | none =>
    have hsc : spawnChild I w id child = none := by simp [spawnChild, ht]
    have hrun : execRun I w id a k = crashWorld w := by simp [execRun, hgo, hk, hsc]
    exact hrun.symm ▸ side_frame I w _ hS (frame_crash w)
  | some t =>
    let gate := t.multiplicity == .perPeer && supNamed t.supervisor (tname id) &&
      ((w.st id).life == .alive)
    by_cases hok : gate = true
    · have hmul : t.multiplicity = .perPeer := by
        cases hm : t.multiplicity with
        | perPeer => rfl
        | one =>
          have hb : (Multiplicity.one == .perPeer) = false := by decide
          simp [gate, hm, hb] at hok
      have hsupn : supNamed t.supervisor (tname id) = true := by
        cases hs : supNamed t.supervisor (tname id) with
        | true => rfl
        | false => simp [gate, hs] at hok
      cases id with
      | core pname =>
        have hsc : spawnChild I w (.core pname) child = none := by
          simp [spawnChild, ht, gate, hok]
        have hrun : execRun I w (.core pname) a k = crashWorld w := by
          simp [execRun, hgo, hk, hsc]
        exact hrun.symm ▸ side_frame I w _ hS (frame_crash w)
      | peer pname pk pg =>
        have hsup : supNamed t.supervisor pname = true := by simpa [tname] using hsupn
        by_cases hbusy : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = true
        · have hsc : spawnChild I w (.peer pname pk pg) child = some w := by
            simp [spawnChild, ht, gate, hok, hbusy]
          have hbase : execRun I w (.peer pname pk pg) a k =
              commitCont w (.peer pname pk pg) (proceed (w.st (.peer pname pk pg)) k') := by
            simp [execRun, hgo, hk, hsc, k']
          by_cases hcr : w.crashed = true
          · simp [hbase, commitCont, hcr]
            exact hS
          have hcf : w.crashed = false := by
            cases hb : w.crashed with
            | false => rfl
            | true => exact absurd hb hcr
          have hrun : execRun I w (.peer pname pk pg) a k =
              setActor w (.peer pname pk pg) (proceed (w.st (.peer pname pk pg)) k') := by
            simp [hbase, commitCont, hcf]
          exact hrun.symm ▸ side_frame I w _ hS
            (frame_keep w (.peer pname pk pg) (proceed (w.st (.peer pname pk pg)) k')
              (by simp [proceed_keeps_prio]))
        · have hfalse : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk <;> simp_all
          let bornId := InstId.peer child pk (maxGen w child pk)
          let born := { bornActor I.desc w child pk t.initial with parent := some (.peer pname pk pg) }
          let wB := admitBorn I w bornId born
          have hsc : spawnChild I w (.peer pname pk pg) child = some wB := by
            simp [spawnChild, ht, gate, hok, hfalse, bornId, born, wB]
          have hB := admit_side I w hH hS child pk (.peer pname pk pg) t ht hsup
            ⟨pname, pk, pg, rfl⟩ (alive_mem I w hH (.peer pname pk pg) hparent)
          have hbase : execRun I w (.peer pname pk pg) a k =
              commitCont wB (.peer pname pk pg) (proceed (wB.st (.peer pname pk pg)) k') := by
            simp [execRun, hgo, hk, hsc, k']
          by_cases hcr : wB.crashed = true
          · simp [hbase, commitCont, hcr]
            simpa [wB, bornId, born] using hB
          have hcf : wB.crashed = false := by
            cases hb : wB.crashed with
            | false => rfl
            | true => exact absurd hb hcr
          have hrun : execRun I w (.peer pname pk pg) a k =
              setActor wB (.peer pname pk pg) (proceed (wB.st (.peer pname pk pg)) k') := by
            simp [hbase, commitCont, hcf]
          exact hrun.symm ▸ side_frame I wB _ (by simpa [wB, bornId, born] using hB)
            (frame_keep wB (.peer pname pk pg) (proceed (wB.st (.peer pname pk pg)) k')
              (by simp [proceed_keeps_prio]))
    · have hlifeB : ((w.st id).life == .alive) = true := by simpa [ha, beq_iff_eq] using hlive
      have hgate : (t.multiplicity == .perPeer && supNamed t.supervisor (tname id)) = false := by
        cases hg : (t.multiplicity == .perPeer && supNamed t.supervisor (tname id)) with
        | false => rfl
        | true =>
          have htrue : gate = true := by simp [gate, hg, hlifeB]
          exact absurd htrue hok
      have hsc : spawnChild I w id child = none := by simp [spawnChild, ht, hgate]
      have hrun : execRun I w id a k = crashWorld w := by simp [execRun, hgo, hk, hsc]
      exact hrun.symm ▸ side_frame I w _ hS (frame_crash w)

theorem send_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (dst label : String)
    (hint : Nat) (es : List Eff) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .send dst label hint :: es) : Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  unfold execRun
  simp only [hgo, hk]
  cases hr : route w I.desc id dst hint with
  | none =>
    exact frame_trans (note_frame w id dst)
      (frame_keep (noteStale w id dst) id (proceed a (afterHead k))
        (by simp [ha, proceed_keeps_prio, noteStale]))
  | some dstId =>
    exact mail_frame w I.desc id dstId { label := label, sender := id, callFrom := none } false (afterHead k)

theorem try_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (dst label : String)
    (hint : Nat) (onFull onGone es : List Eff) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .trySend dst label hint onFull onGone :: es) : Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  unfold execRun
  simp only [hgo, hk]
  cases hr : route w I.desc id dst hint with
  | none =>
    exact frame_trans (note_frame w id dst)
      (frame_keep (noteStale w id dst) id (proceed a _) (by simp [ha, proceed_keeps_prio, noteStale]))
  | some dstId =>
    by_cases hroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
        decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
    · simp only [hroom]
      exact mail_frame w I.desc id dstId
        { label := label, sender := id, callFrom := none, reliable := false } false (afterHead k)
    · have hfroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
          decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = false := by
        cases hb : (w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
            decide ((w.st dstId).box.length < capBulk I.desc w.N dstId) with
        | false => rfl
        | true => exact absurd hb hroom
      simp only [hfroom]
      by_cases haliveT : ((w.st dstId).life == .alive) = true
      · simp only [haliveT]
        apply frame_keep
        simp [ha, proceed_keeps_prio]
      · have hdead : ((w.st dstId).life == .alive) = false := by
          cases hb : (w.st dstId).life == .alive with
          | false => rfl
          | true => exact absurd hb haliveT
        simp only [hdead]
        apply frame_keep
        simp [ha, proceed_keeps_prio]

theorem call_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (dst label : String)
    (hint : Nat) (onNotAdmitted onTimedOut es : List Eff) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .call dst label hint onNotAdmitted onTimedOut :: es) :
    Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  unfold execRun
  simp only [hgo, hk]
  cases hr : resolveId I.desc w id dst hint with
  | none =>
    exact frame_trans (note_frame w id dst)
      (frame_keep (noteStale w id dst) id (finishCall (issueCall a) _ .notAdmitted)
        (by simp [ha, noteStale, finish_keep, issue_keep]))
  | some dstId =>
    exact mail_frame w I.desc id dstId { label := label, sender := id, callFrom := some id } true _

theorem self_frame (I : Impl) (w : World) (hH : Hold I w) (id : InstId) (a : Actor) (k : Cont)
    (label : String) (es : List Eff) (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .selfSchedule label :: es) : Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  have hmem : id ∈ w.roster := alive_mem I w hH id (by simpa [ha] using hlive)
  unfold execRun
  simp only [hgo, hk]
  by_cases hany : (a.prio.any (fun p => p.label == label)) = true
  · simp only [hany]
    apply frame_keep
    simp [ha, proceed_keeps_prio]
  · have hfany : (a.prio.any (fun p => p.label == label)) = false := by
      cases hb : a.prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hany
    simp only [hfany]
    by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
    · simp only [hroom]
      apply frame_touch
      exact hmem
    · simp only [hroom]
      exact frame_crash w

theorem cell_exec (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (dst label : String)
    (value : Nat) (es : List Eff) (_ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = .cell dst label value :: es) : Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  unfold execRun
  simp only [hgo, hk]
  let previous := w.cell dst label
  let written := max previous.value value
  let w1 := setCell w dst label { value := written, dirty := true }
  let w2 := setActor w1 id (proceed (w1.st id) (afterHead k))
  have h2 : Frame w w2 :=
    frame_trans (cell_frame w dst label { value := written, dirty := true })
      (frame_keep w1 id (proceed (w1.st id) (afterHead k)) (by simp [proceed_keeps_prio]))
  by_cases hdirty : (w.cell dst label).dirty = true
  · simp only [hdirty]
    exact h2
  · have hf : (w.cell dst label).dirty = false := by
      cases hb : (w.cell dst label).dirty with
      | false => rfl
      | true => exact absurd hb hdirty
    simp only [hf]
    exact frame_trans h2 (wake_frame I.desc w2 dst label id)

theorem plain_frame (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (ha : a = w.st id) (hlive : a.life = .alive)
    (hk : k.rest = [] ∨ (∃ es, k.rest = .internal :: es) ∨ (∃ onTimeout es, k.rest = .peer onTimeout :: es)) :
    Frame w (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  rcases hk with hk | hk | hk
  · unfold execRun
    simp only [hgo, hk]
    apply frame_keep
    simp [ha]
  · rcases hk with ⟨es, hk⟩
    unfold execRun
    simp only [hgo, hk]
    apply frame_keep
    simp [ha]
  · rcases hk with ⟨onTimeout, es, hk⟩
    unfold execRun
    simp only [hgo, hk]
    apply frame_keep
    simp [ha]

theorem exec_live (I : Impl) (w : World) (hH : Hold I w) (hS : Side I w) (id : InstId) (a : Actor)
    (k : Cont) (ha : a = w.st id) (hlive : a.life = .alive) : Side I (execRun I w id a k) := by
  cases hk : k.rest with
  | nil =>
    exact side_frame I w _ hS (plain_frame I w id a k ha hlive (Or.inl hk))
  | cons e es =>
    cases e with
    | send dst label hint =>
      exact side_frame I w _ hS (send_frame I w id a k dst label hint es ha hlive hk)
    | trySend dst label hint onFull onGone =>
      exact side_frame I w _ hS (try_frame I w id a k dst label hint onFull onGone es ha hlive hk)
    | call dst label hint onNotAdmitted onTimedOut =>
      exact side_frame I w _ hS
        (call_frame I w id a k dst label hint onNotAdmitted onTimedOut es ha hlive hk)
    | reply =>
      have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
      have hrun : execRun I w id a k = performReply w id k := by simp [execRun, hgo, hk]
      exact hrun.symm ▸ side_frame I w _ hS (reply_frame w id k)
    | selfSchedule label =>
      exact side_frame I w _ hS (self_frame I w hH id a k label es ha hlive hk)
    | cell dst label value =>
      exact side_frame I w _ hS (cell_exec I w id a k dst label value es ha hlive hk)
    | internal =>
      exact side_frame I w _ hS (plain_frame I w id a k ha hlive (Or.inr (Or.inl ⟨es, hk⟩)))
    | peer onTimeout =>
      exact side_frame I w _ hS
        (plain_frame I w id a k ha hlive (Or.inr (Or.inr ⟨onTimeout, es, hk⟩)))
    | abort =>
      have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
      let wA := abortChildren I.desc w id
      have hbase : execRun I w id a k =
          commitCont wA id (proceed (wA.st id) (afterHead k)) := by
        simp [execRun, hgo, hk, wA]
      by_cases hcr : wA.crashed = true
      · simp [hbase, commitCont, hcr]
        exact side_frame I w wA hS (abort_frame I.desc w id (hold_on I w hH))
      · have hcf : wA.crashed = false := by
          cases hb : wA.crashed with
          | false => rfl
          | true => exact absurd hb hcr
        have hrun : execRun I w id a k =
            setActor wA id (proceed (wA.st id) (afterHead k)) := by
          simp [hbase, commitCont, hcf]
        exact hrun.symm ▸ side_frame I w _ hS
          (frame_trans (abort_frame I.desc w id (hold_on I w hH))
            (frame_keep wA id (proceed (wA.st id) (afterHead k)) (proceed_keeps_prio _ _)))
    | spawn child =>
      exact spawn_effect_side I w hH hS id a k child es ha hlive hk
    | terminate =>
      exact side_frame I w _ hS (term_frame I w id a k hlive ⟨es, hk⟩ (hold_on I w hH))

theorem exec_side (I : Impl) (w : World) (hH : Hold I w) (hS : Side I w) (id : InstId) (a : Actor)
    (k : Cont) (ha : a = w.st id) : Side I (execRun I w id a k) := by
  by_cases hlive : a.life = .alive
  · exact exec_live I w hH hS id a k ha hlive
  · have hgo : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hb) hlive
    simp [execRun, hgo]
    exact hS

theorem exec_head_side (I : Impl) (w : World) (hH : Hold I w) (hS : Side I w) (id : InstId) (w' : World)
    (h : execHead I w id = some w') : Side I w' := by
  unfold execHead at h
  have halive : (w.st id).life = .alive := by
    by_cases ha : (w.st id).life = .alive
    · exact ha
    · simp [ha] at h
  have hliveP : ¬((w.st id).life ≠ .alive) := fun hn => hn halive
  simp only [hliveP, ite_false] at h
  cases hph : (w.st id).phase with
  | run k =>
    simp only [hph] at h
    have heq : w' = execRun I w id (w.st id) k := by simpa [Option.some.injEq] using h.symm
    exact heq ▸ exec_side I w hH hS id (w.st id) k rfl
  | idle => simp [hph] at h
  | parked _ _ _ => simp [hph] at h
  | awaitReply _ _ => simp [hph] at h
  | awaitEffect _ => simp [hph] at h
  | awaitPeer _ => simp [hph] at h
  | crashed => simp [hph] at h

theorem side_step (I : Impl) (w w' : World) (hH : Hold I w) (hS : Side I w) (a : Action)
    (h : apply I a w = some w') : Side I w' := by
  have hstep : stepWorld I a w = some w' := (apply_step I a w w' h).2
  cases a with
  | recvBulk s =>
    exact side_frame I w w' hS (bulk_frame I w w' s (by simpa [stepWorld] using hstep))
  | recvPrio s =>
    exact side_frame I w w' hS (prio_frame I w hH w' s (by simpa [stepWorld] using hstep))
  | exec s =>
    exact exec_head_side I w hH hS s w' (by simpa [stepWorld] using hstep)
  | finish s =>
    exact side_frame I w w' hS (finish_frame I w w' s (by simpa [stepWorld] using hstep))
  | spawn template =>
    exact spawn_side I w w' hS template (by simpa [stepWorld] using hstep)
  | ingress dst label =>
    exact side_frame I w w' hS (ingress_frame I w w' dst label (by simpa [stepWorld] using hstep))
  | callTimeout s =>
    exact side_frame I w w' hS (timeout_frame w w' s (by simpa [stepWorld] using hstep))
  | stutter =>
    exact (stutter_unchanged I w w' h).symm ▸ hS

theorem reach_pack (I : Impl) (N : Nat) (w : World) (hG : GraphOk I.desc) (hR : Reachable I N w) :
    Hold I w ∧ Side I w := by
  induction hR with
  | init => exact ⟨hold_init I N hG, side_init I N hG⟩
  | step w w' a prev happ ih =>
    rcases ih with ⟨hH, hS⟩
    exact ⟨hold_step I w w' hH hG hS.nd hS.ix hS.root hS.off a happ, side_step I w w' hH hS a happ⟩

/-- `Hold` for every world a run can reach under `GraphOk`. -/
theorem hold_reach (I : Impl) (N : Nat) (w : World) (hG : GraphOk I.desc) (hR : Reachable I N w) :
    Hold I w :=
  (reach_pack I N w hG hR).1

/-! A recorded parent was wired by the template that names it. -/

theorem set_parent (w : World) (id : InstId) (a : Actor) (i : InstId)
    (hp : a.parent = (w.st id).parent) :
    ((setActor w id a).st i).parent = (w.st i).parent := by
  by_cases hi : i = id
  · simp [setActor, hi, hp]
  · simp [setActor, hi]

theorem resume_parent (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).parent = a.parent := by
  cases hph : a.phase with
  | parked _ _ _ =>
    simp only [resumeSender, hph]
    split <;> simp [proceed_parent]
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem live_parent (w : World) (name : String) (sender i : InstId) :
    ((creditLive w name sender).st i).parent = (w.st i).parent := by
  simpa [creditLive] using credit_parent w name (budgetHolder w sender) i

theorem perform_parent (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).parent = (w.st i).parent := by
  unfold performReply
  cases hto : k.replyTo with
  | none =>
    simp
    exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
  | some caller =>
    simp
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      simp
      split
      · exact (set_parent (setActor w caller (finishCall (w.st caller) ck .reply)) sender
            (proceed ((setActor w caller (finishCall (w.st caller) ck .reply)).st sender)
              (afterHead k)) i (proceed_parent _ _)).trans
          (set_parent w caller (finishCall (w.st caller) ck .reply) i (finish_parent _ _ _))
      · exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | idle =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | run _ =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | parked _ _ _ =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | awaitEffect _ =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | awaitPeer _ =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)
    | crashed =>
      simp
      exact set_parent w sender (proceed (w.st sender) (afterHead k)) i (proceed_parent _ _)

theorem credit_fold_parent (name : String) (caller : InstId) :
    ∀ ps : List Parked, ∀ w : World, ∀ i : InstId,
      ((ps.foldl (fun w _ => creditSender w name caller) w).st i).parent =
        (w.st i).parent := by
  intro ps
  induction ps with
  | nil => intro w i; simp
  | cons _ ps ih =>
    intro w i
    simp only [List.foldl_cons]
    exact (ih _ i).trans (credit_parent w name caller i)

theorem refund_call_parent (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).parent = (w.st i).parent := by
  unfold refundParkedCall
  dsimp
  by_cases hempty :
      (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = true
  · simp [hempty]
  · have hf :
        (((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty) = false := by
      cases hb : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty with
      | false => rfl
      | true => exact absurd hb hempty
    simp only [hf]
    let drop := (w.st dst).parked.filter fun p => p.sender == caller && p.isCall
    let keep := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall)
    exact (credit_fold_parent (tname dst) caller drop
        (setActor w dst { (w.st dst) with parked := keep }) i).trans
      (set_parent w dst { (w.st dst) with parked := keep } i (by simp))

theorem offer_parent (D : Description) (w : World) (host : InstId) (msg : Msg) (i : InstId) :
    ((offerPrio D w host msg).st i).parent = (w.st i).parent := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp [hfull]
    exact crash_parent w i
  · have hf : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = false := by
      cases hb : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) with
      | false => rfl
      | true => exact absurd hb hfull
    simp [hf, setActor]
    by_cases hi : i = host <;> simp [hi]

theorem try_parent (D : Description) (w : World) (dst : InstId) (label : String)
    (writer i : InstId) :
    ((tryWake D w dst label writer).st i).parent = (w.st i).parent := by
  unfold tryWake
  by_cases hskip : ((w.st dst).life != .alive ||
      (w.st dst).prio.any (fun p => p.label == label)) = true
  · simp [hskip]
  · have hf : ((w.st dst).life != .alive ||
        (w.st dst).prio.any (fun p => p.label == label)) = false := by
      cases hb : (w.st dst).life != .alive || (w.st dst).prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hskip
    simp [hf]
    exact offer_parent D w dst _ i

theorem wakes_go_parent (D : Description) (label : String) (writer : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).parent =
        (w.st i).parent := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons id ids ih =>
    intro w i
    simp only [List.foldl_cons]
    exact (ih _ i).trans (try_parent D w id label writer i)

theorem enqueue_parent (D : Description) (w : World) (child i : InstId) :
    ((enqueueTombstone D w child).st i).parent = (w.st i).parent := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simp
  | some parent =>
    by_cases halive : ((w.st parent).life != .alive) = true
    · simp [halive]
    · have hf : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb halive
      simp only [hf]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp [hlab]
        exact crash_parent w i
      · have hlf : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp [hlf]
        exact offer_parent D w parent _ i

theorem shutdown_parent (D : Description) (w : World) (id i : InstId) :
    ((shutdownActor D w id).st i).parent = (w.st i).parent := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true, sealActor]
    exact (enqueue_parent D (releaseWorld D w id (w.st id)) id i).trans
      (release_parent D w id (w.st id) i)
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [hf]

theorem seal_go_parent (fuel : Nat) (D : Description) (id : InstId)
    (ih : ∀ w c i, ((sealBranch fuel D w c).st i).parent = (w.st i).parent) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch fuel D acc child else acc) w).st i).parent =
        (w.st i).parent := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons c cs ihf =>
    intro w i
    simp only [List.foldl_cons]
    split
    · exact (ihf _ i).trans (ih w c i)
    · exact ihf w i

theorem seal_branch_parent (fuel : Nat) (D : Description) :
    ∀ w id i, ((sealBranch fuel D w id).st i).parent = (w.st i).parent := by
  induction fuel with
  | zero => intro w id i; simp [sealBranch]
  | succ fuel ih =>
    intro w id i
    simp only [sealBranch]
    split
    · exact (release_parent D _ id _ i).trans
        (seal_go_parent fuel D id ih w.roster w i)
    · exact seal_go_parent fuel D id ih w.roster w i

theorem drop_parent (D : Description) (w : World) (id i : InstId) :
    ((dropDescendants D w id).st i).parent = (w.st i).parent := by
  unfold dropDescendants
  exact seal_go_parent w.roster.length D id
    (fun acc c j => seal_branch_parent w.roster.length D acc c j) w.roster w i

theorem abort_go_parent (D : Description) (parent : InstId) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w).st i).parent = (w.st i).parent := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons c cs ih =>
    intro w i
    simp only [List.foldl_cons]
    split
    · exact (ih _ i).trans
        ((shutdown_parent D (dropDescendants D w c) c i).trans (drop_parent D w c i))
    · exact ih w i

theorem abort_parent (D : Description) (w : World) (parent i : InstId) :
    ((abortChildren D w parent).st i).parent = (w.st i).parent := by
  simpa [abortChildren] using abort_go_parent D parent w.roster w i

theorem terminate_parent (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((terminateStage D w id a).st i).parent = (w.st i).parent := by
  unfold terminateStage
  exact (shutdown_parent D (dropDescendants D w id) id i).trans (drop_parent D w id i)

theorem seal_actor_parent (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((sealActor D w id a).st i).parent = (w.st i).parent := by
  unfold sealActor
  exact (enqueue_parent D (releaseWorld D w id a) id i).trans (release_parent D w id a i)

/-- A parent field names the supervisor the child's template declared. -/
def Wired (D : Description) (w : World) : Prop :=
  ∀ id p, (w.st id).parent = some p →
    ∃ t, templateOf D (tname id) = some t ∧ t.supervisor = some (tname p)

theorem wired_stable (D : Description) (w w' : World) (hW : Wired D w)
    (h : ∀ i, (w'.st i).parent = (w.st i).parent) : Wired D w' := by
  intro i p hp
  exact hW i p (by rw [← h i]; exact hp)

theorem wired_set (D : Description) (w : World) (hW : Wired D w) (jid : InstId) (a : Actor)
    (hp : a.parent = (w.st jid).parent) : Wired D (setActor w jid a) := by
  intro i p h
  by_cases hi : i = jid
  · rw [hi] at h ⊢
    rw [setActor_self] at h
    exact hW jid p (hp ▸ h)
  · rw [setActor_other w jid i a hi] at h
    exact hW i p h

theorem wired_crash (D : Description) (w : World) (hW : Wired D w) : Wired D (crashWorld w) :=
  wired_stable D w _ hW (fun i => crash_parent w i)

theorem deliver_parent (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a' : Actor) (h : deliver I w id a m = some (w1, a')) :
    a'.parent = a.parent ∧ ∀ i, (w1.st i).parent = (w.st i).parent := by
  unfold deliver at h
  dsimp at h
  split at h
  · simp at h
  · split at h
    · have heq := by simpa [Option.some.injEq] using h
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨by simp, fun i => congrArg Actor.parent (cellsSt I.desc w id i)⟩
    · split at h
      · split at h
        · simp at h
        · have heq := by simpa [Option.some.injEq] using h
          rcases heq with ⟨rfl, rfl⟩
          exact ⟨by simp, fun i => congrArg Actor.parent (cellsSt I.desc w id i)⟩
      · split at h
        · simp at h
        · split at h
          · have heq := by simpa [Option.some.injEq] using h
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨by simp, fun i => congrArg Actor.parent (cellsSt I.desc w id i)⟩
          · have heq := by simpa [Option.some.injEq] using h
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨by simp, fun i => congrArg Actor.parent (cellsSt I.desc w id i)⟩

theorem bulk_parent (I : Impl) (w w' : World) (id i : InstId)
    (h : receiveBulk I w id = some w') :
    (w'.st i).parent = (w.st i).parent := by
  unfold receiveBulk at h
  dsimp at h
  split at h
  · simp at h
  · cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with parked := ps }) p.msg with
        | none =>
          simp only [hbox] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hbox] at hd
          rw [hd] at h
          have hw' : w' = setActor (creditLive (setActor w1 id a') (tname id) p.msg.sender) p.sender
              (resumeSender ((creditLive (setActor w1 id a') (tname id) p.msg.sender).st p.sender)
                p.isCall id) := by simpa [Option.some.injEq] using h.symm
          have ⟨hpa, hst⟩ := deliver_parent I w id _ p.msg w1 a' hd
          have hset := set_parent w1 id a' i (by rw [hpa]; simp [hst])
          let wA := setActor w1 id a'
          let wC := creditLive wA (tname id) p.msg.sender
          have hlive := live_parent wA (tname id) p.msg.sender i
          have hres := set_parent wC p.sender
            (resumeSender (wC.st p.sender) p.isCall id) i (resume_parent _ _ _)
          exact hw' ▸ hres.trans (hlive.trans (hset.trans (hst i)))
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          have hw' : w' = creditLive (setActor w1 id a') (tname id) m.sender := by
            simpa [Option.some.injEq] using h.symm
          have ⟨hpa, hst⟩ := deliver_parent I w id _ m w1 a' hd
          have hset := set_parent w1 id a' i (by rw [hpa]; simp [hst])
          exact hw' ▸ (live_parent _ (tname id) m.sender i).trans (hset.trans (hst i))
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          let admitted := { a' with box := a'.box ++ [p.msg], parked := ps }
          have hw' : w' = setActor (creditLive (setActor w1 id admitted) (tname id) m.sender) p.sender
              (resumeSender ((creditLive (setActor w1 id admitted) (tname id) m.sender).st p.sender)
                p.isCall id) := by simpa [Option.some.injEq, admitted] using h.symm
          have ⟨hpa, hst⟩ := deliver_parent I w id _ m w1 a' hd
          have hadmit : admitted.parent = a'.parent := by simp [admitted]
          have hset := set_parent w1 id admitted i (by rw [hadmit, hpa]; simp [hst])
          let wA := setActor w1 id admitted
          let wC := creditLive wA (tname id) m.sender
          have hres := set_parent wC p.sender
            (resumeSender (wC.st p.sender) p.isCall id) i (resume_parent _ _ _)
          exact hw' ▸ hres.trans
            ((live_parent wA (tname id) m.sender i).trans (hset.trans (hst i)))

theorem prio_parent (I : Impl) (w w' : World) (id i : InstId)
    (h : receivePrio I w id = some w') :
    (w'.st i).parent = (w.st i).parent := by
  obtain ⟨m, pre, suf, w1, a', _, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  have ⟨hpa, hst⟩ :=
    deliver_parent I w id ({ (w.st id) with prio := pre ++ suf }) m w1 a' hdel
  exact hw' ▸ (set_parent w1 id a' i (by rw [hpa]; simp [hst])).trans (hst i)

theorem ingress_parent (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (w'.st i).parent = (w.st i).parent := by
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
            exact set_parent w dst _ i (by simp [charge_parent])

theorem finish_wait_parent (I : Impl) (w w' : World) (id i : InstId)
    (h : finishWait I w id = some w') :
    (w'.st i).parent = (w.st i).parent := by
  obtain ⟨_, _, heq⟩ := finish_proceed I w w' id h
  exact heq ▸ set_parent w id _ i (proceed_parent _ _)

theorem timeout_parent (w w' : World) (id i : InstId) (h : callTimeout w id = some w') :
    (w'.st i).parent = (w.st i).parent := by
  unfold callTimeout at h
  dsimp at h
  split at h
  · simp at h
  · split at h
    · have heq := by simpa [Option.some.injEq] using h
      subst heq
      exact (set_parent _ id _ i (finish_parent _ _ _)).trans
        (set_parent w _ _ i ((detach_keep _ id _).2.2.2))
    · have heq := by simpa [Option.some.injEq] using h
      subst heq
      exact (set_parent _ id _ i (finish_parent _ _ _)).trans (refund_call_parent w id _ i)
    · have heq := by simpa [Option.some.injEq] using h
      subst heq
      exact set_parent w id _ i (proceed_parent _ _)
    · simp at h

theorem admit_parent (I : Impl) (w : World) (id : InstId) (born : Actor) (i : InstId) :
    ((admitBorn I w id born).st i).parent = (if i = id then born else w.st i).parent := by
  have heq : admitBorn I w id born =
      readCells I.desc (setActor { w with roster := w.roster ++ [id] } id born) id := rfl
  rw [heq, cellsSt]
  by_cases hi : i = id
  · simp [setActor, hi]
  · simp [setActor, hi]

theorem wired_birth (I : Impl) (w : World) (hW : Wired I.desc w) (id : InstId) (born : Actor)
    (hnew : ∀ p, born.parent = some p →
      ∃ t, templateOf I.desc (tname id) = some t ∧ t.supervisor = some (tname p)) :
    Wired I.desc (admitBorn I w id born) := by
  intro i p hp
  have hst := admit_parent I w id born i
  by_cases hi : i = id
  · subst hi
    rw [hst] at hp
    simp at hp
    exact hnew p hp
  · rw [hst] at hp
    simp [hi] at hp
    exact hW i p hp

theorem spawn_child_wired (I : Impl) (w : World) (hW : Wired I.desc w) (parent : InstId)
    (child : String) (w' : World) (h : spawnChild I w parent child = some w') :
    Wired I.desc w' := by
  cases ht : templateOf I.desc child with
  | none => simp [spawnChild, ht] at h
  | some t =>
    let gate := t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
      ((w.st parent).life == .alive)
    by_cases hok : gate = true
    · have hsupn : supNamed t.supervisor (tname parent) = true := by
        cases hs : supNamed t.supervisor (tname parent) with
        | true => rfl
        | false => simp [gate, hs] at hok
      cases parent with
      | core _ =>
        simp [spawnChild, ht, gate, hok] at h
      | peer pname pk pg =>
        have hsup : supNamed t.supervisor pname = true := by simpa [tname] using hsupn
        by_cases hbusy : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = true
        · have hsc : spawnChild I w (.peer pname pk pg) child = some w := by
            simp [spawnChild, ht, gate, hok, hbusy]
          have hw' : w = w' := by simpa [hsc] using h
          exact hw'.symm ▸ hW
        · have hfalse : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (.peer pname pk pg) child pk <;> simp_all
          let bornId := InstId.peer child pk (maxGen w child pk)
          let born := { bornActor I.desc w child pk t.initial with
            parent := some (.peer pname pk pg) }
          have hsc : spawnChild I w (.peer pname pk pg) child =
              some (admitBorn I w bornId born) := by
            simp [spawnChild, ht, gate, hok, hfalse, bornId, born]
          have hw' : admitBorn I w bornId born = w' := by simpa [hsc] using h
          have hnew : ∀ q, born.parent = some q →
              ∃ t, templateOf I.desc (tname bornId) = some t ∧ t.supervisor = some (tname q) := by
            intro q hqb
            have hflip : .peer pname pk pg = q := by simpa [born] using hqb
            have hq' : q = .peer pname pk pg := hflip.symm
            subst hq'
            exact ⟨t, ht, sup_is_some _ _ hsup⟩
          exact hw'.symm ▸ wired_birth I w hW bornId born hnew
    · by_cases hpre : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · by_cases hlife : ((w.st parent).life == .alive) = true
        · have hgate : gate = true := by simp [gate, hpre, hlife]
          exact absurd hgate hok
        · have hdead : ((w.st parent).life == .alive) = false := by
            cases hbit : ((w.st parent).life == .alive) with
            | false => rfl
            | true => exact absurd hbit hlife
          simp [spawnChild, ht, hdead, hpre] at h
          have hw' : w = w' := by simpa [Option.some.injEq] using h
          exact hw'.symm ▸ hW
      · have hpref : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hbit : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) with
          | false => rfl
          | true => exact absurd hbit hpre
        simp [spawnChild, ht, hpref] at h

theorem wired_place (I : Impl) (w : World) (hW : Wired I.desc w) (template : String) (k : Nat)
    (initial : String) (parent : Option InstId) (next : World → World)
    (hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster)
    (hnew : ∀ p, parent = some p →
      ∃ t, templateOf I.desc template = some t ∧ t.supervisor = some (tname p)) :
    Wired I.desc (placePeer I w template k initial parent next) := by
  intro i q hq
  have hst := (place_facts I w template k initial parent next hnext).1 i
  by_cases hi : i = InstId.peer template k (maxGen w template k)
  · rw [hi] at hq ⊢
    simp [hi] at hst
    rw [hst] at hq
    exact hnew q (by simpa using hq)
  · simp [hi] at hst
    rw [hst] at hq
    exact hW i q hq

theorem spawn_wired (I : Impl) (w w' : World) (hW : Wired I.desc w) (template : String)
    (h : spawn I w template = some w') : Wired I.desc w' := by
  cases ht : templateOf I.desc template with
  | none => simp [spawn, ht] at h
  | some t =>
    simp only [spawn, ht] at h
    split at h
    · rename_i hmay
      clear hmay
      split at h
      · rename_i name hsup
        let k := freshKey I.desc w t.subtree
        let next : World → World := fun u =>
          { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
        have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster :=
          fun _ _ => ⟨rfl, rfl⟩
        have hw' : w' = placePeer I w template k t.initial (some (.core name)) next := by
          simpa [Option.some.injEq] using h.symm
        have hnew : ∀ q, some (.core name) = some q →
            ∃ t, templateOf I.desc template = some t ∧ t.supervisor = some (tname q) := by
          intro q hq
          have hflip : .core name = q := by simpa using hq
          have hq' : q = .core name := hflip.symm
          subst hq'
          exact ⟨t, ht, hsup⟩
        exact hw' ▸ wired_place I w hW template k t.initial (some (.core name)) next hnext hnew
      · rename_i hsup
        split at h
        · let k := w.nextIx template
          let next : World → World := fun u =>
            { u with nextIx := fun n => if n = template then k + 1 else u.nextIx n }
          have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster :=
            fun _ _ => ⟨rfl, rfl⟩
          have hw' : w' = placePeer I w template k t.initial none next := by
            simpa [Option.some.injEq] using h.symm
          exact hw' ▸ wired_place I w hW template k t.initial none next hnext
            (fun _ hq => by cases hq)
        · let k := freshKey I.desc w t.subtree
          let next : World → World := fun u =>
            { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
          have hnext : ∀ u i, (next u).st i = u.st i ∧ (next u).roster = u.roster :=
            fun _ _ => ⟨rfl, rfl⟩
          have hw' : w' = placePeer I w template k t.initial none next := by
            simpa [Option.some.injEq] using h.symm
          exact hw' ▸ wired_place I w hW template k t.initial none next hnext
            (fun _ hq => by cases hq)
    · simp at h

theorem exec_wired (I : Impl) (w : World) (hW : Wired I.desc w) (id : InstId) (a : Actor)
    (k : Cont) (ha : a = w.st id) : Wired I.desc (execRun I w id a k) := by
  by_cases hlive : a.life = .alive
  · have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
    cases hk : k.rest with
    | nil =>
      unfold execRun
      simp only [hgo, hk]
      exact wired_set I.desc w hW id _ (by simp [ha])
    | cons e es =>
      cases e with
      | send dst label hint =>
        unfold execRun
        simp only [hgo, hk]
        cases hr : route w I.desc id dst hint with
        | none =>
          exact wired_stable I.desc w _ hW fun i =>
            (set_parent (noteStale w id dst) id (proceed a (afterHead k)) i
              (by simp [proceed_parent, ha, noteStale_st])).trans
              (congrArg Actor.parent (noteStale_st w id dst i))
        | some dstId =>
          exact wired_stable I.desc w _ hW fun i =>
            mail_parent w I.desc id dstId { label := label, sender := id, callFrom := none }
              false (afterHead k) i
      | trySend dst label hint onFull onGone =>
        unfold execRun
        simp only [hgo, hk]
        cases hr : route w I.desc id dst hint with
        | none =>
          exact wired_stable I.desc w _ hW fun i =>
            (set_parent (noteStale w id dst) id (proceed a _) i
              (by simp [proceed_parent, ha, noteStale_st])).trans
              (congrArg Actor.parent (noteStale_st w id dst i))
        | some dstId =>
          by_cases hroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
          · simp only [hroom]
            exact wired_stable I.desc w _ hW fun i =>
              mail_parent w I.desc id dstId
                { label := label, sender := id, callFrom := none, reliable := false }
                false (afterHead k) i
          · have hfroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
                decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = false := by
              cases hb : (w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
                  decide ((w.st dstId).box.length < capBulk I.desc w.N dstId) with
              | false => rfl
              | true => exact absurd hb hroom
            simp only [hfroom]
            by_cases haliveT : ((w.st dstId).life == .alive) = true
            · simp only [haliveT]
              exact wired_set I.desc w hW id _ (by simp [proceed_parent, ha])
            · have hdead : ((w.st dstId).life == .alive) = false := by
                cases hb : (w.st dstId).life == .alive with
                | false => rfl
                | true => exact absurd hb haliveT
              simp only [hdead]
              exact wired_set I.desc w hW id _ (by simp [proceed_parent, ha])
      | call dst label hint onNotAdmitted onTimedOut =>
        unfold execRun
        simp only [hgo, hk]
        cases hr : resolveId I.desc w id dst hint with
        | none =>
          exact wired_stable I.desc w _ hW fun i =>
            (set_parent (noteStale w id dst) id (finishCall (issueCall a) _ .notAdmitted) i
              (by simp [finish_parent, issue_parent, ha, noteStale_st])).trans
              (congrArg Actor.parent (noteStale_st w id dst i))
        | some dstId =>
          exact wired_stable I.desc w _ hW fun i =>
            mail_parent w I.desc id dstId { label := label, sender := id, callFrom := some id }
              true _ i
      | reply =>
        unfold execRun
        simp only [hgo, hk]
        exact wired_stable I.desc w _ hW fun i => perform_parent w id k i
      | selfSchedule label =>
        unfold execRun
        simp only [hgo, hk]
        by_cases hany : (a.prio.any (fun p => p.label == label)) = true
        · simp only [hany]
          exact wired_set I.desc w hW id _ (by simp [proceed_parent, ha])
        · have hfany : (a.prio.any (fun p => p.label == label)) = false := by
            cases hb : a.prio.any (fun p => p.label == label) with
            | false => rfl
            | true => exact absurd hb hany
          simp only [hfany]
          by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
          · simp only [hroom]
            exact wired_set I.desc w hW id _ (by simp [proceed_parent, ha])
          · simp only [hroom]
            exact wired_crash I.desc w hW
      | cell dst label value =>
        unfold execRun
        simp only [hgo, hk]
        let previous := w.cell dst label
        let wC := setCell w dst label { value := max previous.value value, dirty := true }
        have hC : ∀ i, (wC.st i).parent = (w.st i).parent := fun _ => rfl
        let wP := setActor wC id (proceed (wC.st id) (afterHead k))
        have hP : Wired I.desc wP :=
          wired_set I.desc wC (wired_stable I.desc w wC hW hC) id _
            (by simp [proceed_parent])
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp only [hdirty]
          exact hP
        · have hf : (w.cell dst label).dirty = false := by
            cases hb : (w.cell dst label).dirty with
            | false => rfl
            | true => exact absurd hb hdirty
          simp only [hf]
          exact wired_stable I.desc wP _ hP fun i =>
            wakes_go_parent I.desc label id (readersOf wP dst) wP i
      | internal =>
        unfold execRun
        simp only [hgo, hk]
        exact wired_set I.desc w hW id _ (by simp [ha])
      | peer onTimeout =>
        unfold execRun
        simp only [hgo, hk]
        exact wired_set I.desc w hW id _ (by simp [ha])
      | abort =>
        unfold execRun
        simp only [hgo, hk, ite_true]
        let wA := abortChildren I.desc w id
        by_cases hcr : wA.crashed = true
        · simp [commitCont, wA, hcr]
          exact wired_stable I.desc w wA hW fun i => abort_parent I.desc w id i
        · have hcf : wA.crashed = false := by
            cases hb : wA.crashed with
            | false => rfl
            | true => exact absurd hb hcr
          simp [commitCont, wA, hcf]
          exact wired_set I.desc wA
            (wired_stable I.desc w wA hW fun i => abort_parent I.desc w id i)
            id _ (proceed_parent _ _)
      | spawn child =>
        unfold execRun
        simp only [hgo, hk, ite_true]
        cases hsp : spawnChild I w id child with
        | none =>
          exact wired_crash I.desc w hW
        | some w' =>
          by_cases hcr : w'.crashed = true
          · simp [commitCont, hsp, hcr]
            exact spawn_child_wired I w hW id child w' hsp
          · have hcf : w'.crashed = false := by
              cases hb : w'.crashed with
              | false => rfl
              | true => exact absurd hb hcr
            simp [commitCont, hsp, hcf]
            exact wired_set I.desc w' (spawn_child_wired I w hW id child w' hsp) id _
              (proceed_parent _ _)
      | terminate =>
        rcases execRun_terminate I w id a k hlive ⟨es, hk⟩ with hcrash | hshut | htree | hcascade
        · exact hcrash ▸ wired_crash I.desc w hW
        · rcases hshut with ⟨_, _, _, _, _, _, _, heq⟩
          exact heq ▸ wired_stable I.desc w _ hW fun i => shutdown_parent I.desc w id i
        · rcases htree with ⟨_, _, _, _, heq⟩
          exact heq ▸ wired_stable I.desc w _ hW fun i => terminate_parent I.desc w id a i
        · rcases hcascade with ⟨_, _, _, _, _, _, _, heq⟩
          exact heq ▸ wired_stable I.desc w _ hW fun i => terminate_parent I.desc w id a i
  · have hgo : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hb) hlive
    simp [execRun, hgo]
    exact hW

theorem exec_head_wired (I : Impl) (w : World) (hW : Wired I.desc w) (id : InstId) (w' : World)
    (h : execHead I w id = some w') : Wired I.desc w' := by
  unfold execHead at h
  have halive : (w.st id).life = .alive := by
    by_cases ha : (w.st id).life = .alive
    · exact ha
    · simp [ha] at h
  have hliveP : ¬((w.st id).life ≠ .alive) := fun hn => hn halive
  simp only [hliveP, ite_false] at h
  cases hph : (w.st id).phase with
  | run k =>
    simp only [hph] at h
    have heq : w' = execRun I w id (w.st id) k := by simpa [Option.some.injEq] using h.symm
    exact heq ▸ exec_wired I w hW id (w.st id) k rfl
  | idle => simp [hph] at h
  | parked _ _ _ => simp [hph] at h
  | awaitReply _ _ => simp [hph] at h
  | awaitEffect _ => simp [hph] at h
  | awaitPeer _ => simp [hph] at h
  | crashed => simp [hph] at h

theorem wire_step (I : Impl) (w w' : World) (hW : Wired I.desc w) (a : Action)
    (h : apply I a w = some w') : Wired I.desc w' := by
  have hstep : stepWorld I a w = some w' := (apply_step I a w w' h).2
  cases a with
  | recvBulk s =>
    exact wired_stable I.desc w w' hW fun i =>
      bulk_parent I w w' s i (by simpa [stepWorld] using hstep)
  | recvPrio s =>
    exact wired_stable I.desc w w' hW fun i =>
      prio_parent I w w' s i (by simpa [stepWorld] using hstep)
  | exec s =>
    exact exec_head_wired I w hW s w' (by simpa [stepWorld] using hstep)
  | finish s =>
    exact wired_stable I.desc w w' hW fun i =>
      finish_wait_parent I w w' s i (by simpa [stepWorld] using hstep)
  | spawn template =>
    exact spawn_wired I w w' hW template (by simpa [stepWorld] using hstep)
  | ingress dst label =>
    exact wired_stable I.desc w w' hW fun i =>
      ingress_parent I w w' dst label i (by simpa [stepWorld] using hstep)
  | callTimeout s =>
    exact wired_stable I.desc w w' hW fun i =>
      timeout_parent w w' s i (by simpa [stepWorld] using hstep)
  | stutter =>
    exact (stutter_unchanged I w w' h).symm ▸ hW

theorem read_fold_st (D : Description) :
    ∀ ids : List InstId, ∀ w : World, ∀ i : InstId,
      ((ids.foldl (fun w id => readCells D w id) w).st i) = w.st i := by
  intro ids
  induction ids with
  | nil => intro w i; simp
  | cons id ids ih =>
    intro w i
    simp only [List.foldl_cons]
    rw [ih (readCells D w id) i, cellsSt]

theorem init_actor_parent (D : Description) (id : InstId) : (initActor D id).parent = none := by
  cases h : templateOf D (tname id) <;> simp [initActor, h, withTokens, absentActor]

theorem wired_init (I : Impl) (N : Nat) : Wired I.desc (initWorld I N) := by
  intro id p hp
  unfold initWorld at hp
  rw [read_fold_st I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun i => if (coreRoster I.desc).contains i then initActor I.desc i else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } id] at hp
  by_cases hm : id ∈ coreRoster I.desc
  · simp [hm, init_actor_parent] at hp
  · simp [hm, absentActor] at hp

theorem wire_reach (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) : Wired I.desc w := by
  induction hR with
  | init => exact wired_init I N
  | step _ _ _ _ happ ih => exact wire_step I _ _ ih _ happ

/-- `GraphOk` rejects a supervised template with an empty tombstone, on every
arm of `subtreeEntry`. A recorded parent is that supervisor, so the label the
seal would enqueue is nonempty. -/
theorem tombstone_label_ne (D : Description) (hG : GraphOk D) (w : World) (hW : Wired D w)
    (child p : InstId) (hpar : (w.st child).parent = some p) :
    tombstoneLabel D child ≠ "" := by
  obtain ⟨t, ht, hsup⟩ := hW child p hpar
  have hmap : D.templates.filterMap (subtreeEntry D) = [] := by
    have h := hG.subtrees
    rw [subtreeFails_entry] at h
    exact (List.append_eq_nil_iff.mp h).1
  have hentry := filterMap_none (subtreeEntry D) D.templates hmap t
    (templateOf_mem D (tname child) t ht).1
  have hne := subtreeEntry_tombstone D t (tname p) hentry hsup
  unfold tombstoneLabel
  simp only [ht]
  have hb : (t.tombstone == "") = false := by
    cases hbit : t.tombstone == "" with
    | false => rfl
    | true => exact absurd ((beq_iff_eq).mp hbit) hne
  simp only [hb]
  cases child with
  | core _ => exact hne
  | peer _ _ g => exact tmb_hash_ne t.tombstone g hne

/-- One more declared ordinary label fits. Tombstones already queued are within
the slot bound, and a label that is not on the lane is one more sender inside
`prioLabels`, which `prioSized` counted. -/
theorem lane_room (I : Impl) (w : World) (hG : GraphOk I.desc) (hL : LocalOk I)
    (hH : Hold I w) (id : InstId) (label : String) (hmem : id ∈ w.roster)
    (hlabel : label ∈ prioLabels I (tname id))
    (habsent : label ∉ tmb_laneLabels (w.st id).prio) :
    prioLoad (w.st id).prio < capPrio I.desc w.N id := by
  obtain ⟨sup, ht, hmult⟩ := hH.role id hmem
  have hsized := tmb_prio_sized I hL (tname id) sup ht
  have hlane := hH.lane id
  have hload : prioLoad (w.st id).prio =
      (tombSlots (w.st id).prio).length + (tmb_laneLabels (w.st id).prio).length := by
    simpa [prioLoad] using tmb_load_split (w.st id).prio hlane.peer
  have hord : (tmb_laneLabels (w.st id).prio).length + 1 ≤ (prioLabels I (tname id)).length :=
    tmb_nodup_sub_cons _ _ label hlane.ordNodup hlane.ordIn hlabel habsent
  have hrest : (tmb_laneLabels (w.st id).prio).length + 1 ≤ prioSenderBound I (tname id) :=
    Nat.le_trans hord (Nat.le_max_right _ _)
  have htombs : (tombSlots (w.st id).prio).length ≤ openCount I.desc w id := by
    unfold openCount
    exact Nat.le_add_left _ _
  have haff := legal_le_affine I.desc id w.N sup ht hmult
  have htombsLe : (tombSlots (w.st id).prio).length ≤
      (tombstoneAffine I.desc (tname id)).eval w.N :=
    Nat.le_trans (Nat.le_trans htombs (census_total I.desc w id hG hH.rooted (hH.census id))) haff
  have hlt := ordinary_enqueue_room I.desc (tname id) (prioSenderBound I (tname id))
    (tombSlots (w.st id).prio).length (tmb_laneLabels (w.st id).prio).length w.N sup
    ht hsized hrest htombsLe
  simpa [hload, capPrio, ht] using hlt

/-- A reachable actor's self-schedule is already on its priority lane, or the
lane is strictly under `capPrio`. The label is one `prioLabels` counted. -/
theorem self_schedule_fits (I : Impl) (N : Nat) (w : World)
    (hG : GraphOk I.desc) (hL : LocalOk I) (hReach : Reachable I N w)
    (id : InstId) (k : Cont) (label : String) (es : List Eff)
    (hlive : (w.st id).life = .alive) (hph : (w.st id).phase = .run k)
    (hk : k.rest = .selfSchedule label :: es) :
    ((w.st id).prio.any (fun p => p.label == label)) = true ∨
      prioLoad (w.st id).prio < capPrio I.desc w.N id := by
  have hH := hold_reach I N w hG hReach
  have hmem : id ∈ w.roster := hH.rostered id (by rw [hlive]; intro h; cases h)
  have hdec : ContDeclared I (tname id) k := by
    simpa [phaseDeclared, hph] using hH.phase id hmem
  have hlabel : label ∈ prioLabels I (tname id) :=
    hdec.rest.sched label (by simpa [hk] using tmb_self_head label es)
  by_cases hqueued : ((w.st id).prio.any (fun p => p.label == label)) = true
  · exact Or.inl hqueued
  · have hfree : ((w.st id).prio.any (fun p => p.label == label)) = false := by
      cases hbit : ((w.st id).prio.any (fun p => p.label == label)) with
      | false => rfl
      | true => exact absurd hbit hqueued
    exact Or.inr (lane_room I w hG hL hH id label hmem hlabel
      (lane_absent (w.st id).prio label hfree))

/-- A cell wake on a reachable reader is already on that reader's priority lane,
or the lane is strictly under `capPrio`. The writer's continuation declared
the label for this reader. -/
theorem cell_wake_fits (I : Impl) (N : Nat) (w : World)
    (hG : GraphOk I.desc) (hL : LocalOk I) (hReach : Reachable I N w)
    (writer : InstId) (k : Cont) (dst label : String) (value : Nat) (es : List Eff)
    (hliveW : (w.st writer).life = .alive) (hph : (w.st writer).phase = .run k)
    (hk : k.rest = .cell dst label value :: es) (reader : InstId)
    (hliveR : (w.st reader).life = .alive) (hname : tname reader = dst) :
    ((w.st reader).prio.any (fun p => p.label == label)) = true ∨
      prioLoad (w.st reader).prio < capPrio I.desc w.N reader := by
  have hH := hold_reach I N w hG hReach
  have hmemW : writer ∈ w.roster := hH.rostered writer (by rw [hliveW]; intro h; cases h)
  have hdec : ContDeclared I (tname writer) k := by
    simpa [phaseDeclared, hph] using hH.phase writer hmemW
  have hwake : label ∈ cellWakeLabels dst k.rest := by
    simpa [hk] using tmb_cell_head dst label value es
  have hlabel : label ∈ prioLabels I (tname reader) := by
    simpa [hname] using hdec.rest.wake dst label hwake
  have hmemR : reader ∈ w.roster := hH.rostered reader (by rw [hliveR]; intro h; cases h)
  by_cases hqueued : ((w.st reader).prio.any (fun p => p.label == label)) = true
  · exact Or.inl hqueued
  · have hfree : ((w.st reader).prio.any (fun p => p.label == label)) = false := by
      cases hbit : ((w.st reader).prio.any (fun p => p.label == label)) with
      | false => rfl
      | true => exact absurd hbit hqueued
    exact Or.inr (lane_room I w hG hL hH reader label hmemR hlabel
      (lane_absent (w.st reader).prio label hfree))

theorem self_schedule_safe (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (label : String) (es : List Eff) (hlive : a.life = .alive)
    (hk : k.rest = .selfSchedule label :: es) (hcrash : w.crashed = false)
    (hfit : (a.prio.any (fun p => p.label == label)) = true ∨
      prioLoad a.prio < capPrio I.desc w.N id) :
    (execRun I w id a k).crashed = false := by
  have hgo : (a.life == .alive) = true := (beq_iff_eq).mpr hlive
  unfold execRun
  simp only [hgo, hk]
  by_cases hany : (a.prio.any (fun p => p.label == label)) = true
  · simp [hany, setActor, hcrash]
  · have hfany : (a.prio.any (fun p => p.label == label)) = false := by
      cases hb : a.prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hany
    simp [hfany]
    by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
    · simp [hroom, setActor, hcrash]
    · rcases hfit with hqueued | hlt
      · exact absurd hqueued (by simp [hfany])
      · exact absurd hlt hroom

/-- A reachable world under `GraphOk` and `LocalOk` never overflows a live
parent's priority lane. `GraphOk` makes the supervised template's tombstone
nonempty, and `Wired` says a recorded parent is that supervisor. `LocalOk`
supplies `prioSized` (`tmb_prio_sized`). The offer stays strictly below
`capPrio`. -/
theorem no_tombstone_overflow (I : Impl) (N : Nat) (w : World) (child : InstId)
    (hG : GraphOk I.desc) (hL : LocalOk I) (hReach : Reachable I N w)
    (hliveC : (w.st child).life = .alive) :
    ∀ parent, liveSupervisor I.desc (releaseWorld I.desc w child (w.st child)) child = some parent →
      ((releaseWorld I.desc w child (w.st child)).st parent).life = .alive →
      prioLoad ((releaseWorld I.desc w child (w.st child)).st parent).prio <
        capPrio I.desc (releaseWorld I.desc w child (w.st child)).N parent := by
  intro parent hsup halive
  have hH := hold_reach I N w hG hReach
  have hW := wire_reach I N w hReach
  let sealed := releaseWorld I.desc w child (w.st child)
  have hparS : (sealed.st child).parent = (w.st child).parent :=
    release_parent I.desc w child (w.st child) child
  have hlive := tmb_parent_alive I.desc sealed child parent hsup
  have hpar : (w.st child).parent = some parent := by
    rw [← hparS]
    exact hlive.1
  have hlabel := tombstone_label_ne I.desc hG w hW child parent hpar
  have hmsg : (tombstoneMsg I.desc (sealed.st parent) child).label ≠ "" := by
    simpa [tombstoneMsg] using hlabel
  exact tmb_seal_room I w child hG hL hH hliveC parent hsup halive hmsg

end Deadlock
