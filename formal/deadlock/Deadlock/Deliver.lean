-- Copyright 2026 PRAGMA
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import Deadlock.Rank

set_option autoImplicit false

namespace Deadlock

/-- Receives of `id` since `start` that found `hot` true. `hot` is the mailbox
still holding an entry (the bulk box, or the parked list). -/
def drainDrops {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (start : Nat)
    (hot : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    drainDrops ρ id start hot k +
      if (ρ.act (start + k) == .recvBulk id) && hot (start + k) then 1 else 0

/-- Every bulk entry and every parked entry is taken by a later `recvBulk`, or
the list that held it is cleared. Every admitted call leaves `awaitReply`.

The index `n` is a position, not a message value: a later equal message is a
new acceptance and does not keep the old entry alive. Appends sit behind the
entries already present, so each counted receive consumes one earlier index. -/
def Delivered {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  (∀ i id n, n < ((ρ.cfg i).st id).box.length →
    ∃ j, i ≤ j ∧
      (n < drainDrops ρ id i (fun t => !((ρ.cfg t).st id).box.isEmpty) (j - i) ∨
        ((ρ.cfg j).st id).box = [])) ∧
  (∀ i id n, n < ((ρ.cfg i).st id).parked.length →
    ∃ j, i ≤ j ∧
      (n < drainDrops ρ id i (fun t => !((ρ.cfg t).st id).parked.isEmpty) (j - i) ∨
        ((ρ.cfg j).st id).parked = [])) ∧
  (∀ i c d k, ((ρ.cfg i).st c).phase = .awaitReply d k →
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k)

/-- An admitted call does not stay in `awaitReply`. Leaving that phase is the
reply: `await_next` either keeps the wait or runs the caller's continuation. -/
theorem call_answered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (c d : InstId) (k : Cont)
    (hph : ((ρ.cfg i).st c).phase = .awaitReply d k) :
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k := by
  cases Classical.em (∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k) with
  | inl h => exact h
  | inr hno =>
    have hstay : ∀ j, i ≤ j → ((ρ.cfg j).st c).phase = .awaitReply d k := by
      intro j hj
      by_cases hphj : ((ρ.cfg j).st c).phase = .awaitReply d k
      · exact hphj
      · exact False.elim (hno ⟨j, hj, hphj⟩)
    have hS : Stuck ρ c i := by
      refine ⟨?_, ?_⟩
      · simp [SameWait, waitKind, hph]
      · intro j hj
        simp [SameWait, waitKind, hstay j hj, hph]
    exact False.elim (never_stuck I hL hG hA ρ hF c i hS)

theorem drops_succ {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (start k : Nat)
    (hot : Nat → Bool) (hact : ρ.act (start + k) = .recvBulk id) (hhot : hot (start + k) = true) :
    drainDrops ρ id start hot (k + 1) = drainDrops ρ id start hot k + 1 := by
  simp [drainDrops, hact, hhot]

theorem drops_mono {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (start : Nat)
    (hot : Nat → Bool) (k k' : Nat) (h : k ≤ k') :
    drainDrops ρ id start hot k ≤ drainDrops ρ id start hot k' := by
  induction k' with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    simp [hk, drainDrops]
  | succ k' ih =>
    by_cases hk : k ≤ k'
    · have hle := ih hk
      simp [drainDrops]
      omega
    · have hk' : k = k' + 1 := by omega
      simp [hk']

theorem enough_drops {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (start : Nat)
    (hot : Nat → Bool)
    (hio : ∀ t, start ≤ t → ∃ j, t ≤ j ∧ ρ.act j = .recvBulk id ∧ hot j = true) :
    ∀ n, ∃ k, n < drainDrops ρ id start hot k := by
  intro n
  induction n with
  | zero =>
    obtain ⟨j, hj, hact, hhot⟩ := hio start (Nat.le_refl _)
    have hstep := drops_succ ρ id start (j - start) hot
      (by simpa [Nat.add_sub_of_le hj] using hact)
      (by simpa [Nat.add_sub_of_le hj] using hhot)
    refine ⟨j - start + 1, ?_⟩
    omega
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj, hact, hhot⟩ := hio (start + k) (Nat.le_add_right _ _)
    have hfrom : start ≤ j := Nat.le_trans (Nat.le_add_right start k) hj
    have hge : k ≤ j - start := by
      have hsum : start + (j - start) = j := Nat.add_sub_of_le hfrom
      omega
    have hstep := drops_succ ρ id start (j - start) hot
      (by simpa [Nat.add_sub_of_le hfrom] using hact)
      (by simpa [Nat.add_sub_of_le hfrom] using hhot)
    have hmono := drops_mono ρ id start hot k (j - start) hge
    refine ⟨j - start + 1, ?_⟩
    omega

/-- A reachable actor that is not alive has an empty bulk box. Killing
`terminate` clears it, and a non-alive actor does not acquire mail. -/
theorem dead_box_empty (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (hdead : (w.st id).life ≠ .alive) : (w.st id).box = [] := by
  induction hR generalizing id with
  | init => exact (init_box I N id).1
  | step w w' a _ ha ih =>
    by_cases hprev : (w.st id).life = .alive
    · obtain ⟨tail, toState, replyTo, t, hact, hrun, ht, hflag⟩ :=
        only_terminate_kills I a w w' id ha hprev hdead
      have hstep : w' = execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ := by
        simp [apply, hact, execHead, hprev, hrun] at ha
        exact ha.symm
      rw [hstep]
      exact kill_box_empty I w id t tail toState replyTo ht hflag
    · exact dead_no_box I a w w' id ha hprev (ih id hprev)

theorem mail_alive (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (hne : (w.st id).box ≠ []) : (w.st id).life = .alive := by
  by_cases hl : (w.st id).life = .alive
  · exact hl
  · exact False.elim (hne (dead_box_empty I N w hR id hl))

/-- The largest height recorded for the residual graph. A missing node reads as 0. -/
def maxHeight : List (Node × Nat) → Nat
  | [] => 0
  | (_, h) :: hs => Nat.max h (maxHeight hs)

theorem lookup_le (hs : List (Node × Nat)) (n : Node) (v : Nat) (h : alistGet hs n = some v) :
    v ≤ maxHeight hs := by
  induction hs with
  | nil => simp [alistGet] at h
  | cons p hs ih =>
    cases p with
    | mk a b =>
      simp [alistGet] at h
      by_cases heq : a = n
      · simp [heq] at h
        cases h
        simp [maxHeight]
        exact Nat.le_max_left _ _
      · simp [heq] at h
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem rank_bound (hs : List (Node × Nat)) (w : World) (id : InstId) :
    rankAt hs w id < maxHeight hs + 1 := by
  unfold rankAt
  have hle : heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) ≤
      maxHeight hs := by
    unfold heightOf
    cases hlu : alistGet hs ({ template := tname id, state := (w.st id).typestate } : Node) with
    | none => simp [Option.getD]
    | some v =>
      simp [Option.getD]
      exact lookup_le hs _ v hlu
  omega

theorem alive_while_box {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (i : Nat)
    (h0 : ((ρ.cfg i).st id).life = .alive)
    (hne : ∀ j, i ≤ j → ((ρ.cfg j).st id).box ≠ []) :
    ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive := by
  intro t ht
  have hall : ∀ n, ((ρ.cfg (i + n)).st id).life = .alive := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      by_cases hlive : ((ρ.cfg (i + n + 1)).st id).life = .alive
      · exact hlive
      · have hempty : ((ρ.cfg (i + n + 1)).st id).box = [] := by
          obtain ⟨tail, toState, replyTo, t, hact, hrun, htpl, hflag⟩ :=
            only_terminate_kills I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) id
              (ρ.valid (i + n)) ih hlive
          have hstep : ρ.cfg (i + n + 1) =
              execRun I (ρ.cfg (i + n)) id ((ρ.cfg (i + n)).st id)
                ⟨.terminate :: tail, toState, replyTo⟩ := by
            have hv := ρ.valid (i + n)
            simp [apply, hact, execHead, ih, hrun] at hv
            exact hv.symm
          rw [hstep]
          exact kill_box_empty I (ρ.cfg (i + n)) id t tail toState replyTo htpl hflag
        exact False.elim (hne (i + n + 1) (by omega) hempty)
  simpa [Nat.add_sub_of_le ht] using hall (t - i)

theorem alive_while_parked {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (i : Nat)
    (h0 : ((ρ.cfg i).st id).life = .alive)
    (hne : ∀ j, i ≤ j → ((ρ.cfg j).st id).parked ≠ []) :
    ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive := by
  intro t ht
  have hall : ∀ n, ((ρ.cfg (i + n)).st id).life = .alive := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      by_cases hlive : ((ρ.cfg (i + n + 1)).st id).life = .alive
      · exact hlive
      · have hempty : ((ρ.cfg (i + n + 1)).st id).parked = [] := by
          obtain ⟨tail, toState, replyTo, t, hact, hrun, htpl, hflag⟩ :=
            only_terminate_kills I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) id
              (ρ.valid (i + n)) ih hlive
          have hstep : ρ.cfg (i + n + 1) =
              execRun I (ρ.cfg (i + n)) id ((ρ.cfg (i + n)).st id)
                ⟨.terminate :: tail, toState, replyTo⟩ := by
            have hv := ρ.valid (i + n)
            simp [apply, hact, execHead, ih, hrun] at hv
            exact hv.symm
          rw [hstep]
          exact kill_park_empty I (ρ.cfg (i + n)) id t tail toState replyTo htpl hflag
        exact False.elim (hne (i + n + 1) (by omega) hempty)
  simpa [Nat.add_sub_of_le ht] using hall (t - i)

theorem fair_box (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId) (n : Nat)
    (hn : n < ((ρ.cfg i).st id).box.length) :
    ∃ j, i ≤ j ∧
      (n < drainDrops ρ id i (fun t => !((ρ.cfg t).st id).box.isEmpty) (j - i) ∨
        ((ρ.cfg j).st id).box = []) := by
  cases Classical.em (∃ j, i ≤ j ∧ ((ρ.cfg j).st id).box = []) with
  | inl h =>
    obtain ⟨j, hj, hempty⟩ := h
    exact ⟨j, hj, Or.inr hempty⟩
  | inr hnever =>
    have hne : ∀ j, i ≤ j → ((ρ.cfg j).st id).box ≠ [] := by
      intro j hj hempty
      exact hnever ⟨j, hj, hempty⟩
    have hlive0 : ((ρ.cfg i).st id).life = .alive :=
      mail_alive I N (ρ.cfg i) (cfg_reachable ρ i) id (fun hempty => by simp [hempty] at hn)
    have halive := alive_while_box ρ id i hlive0 hne
    obtain ⟨hs, hok⟩ := hG.ranked
    let hot : Nat → Bool := fun t => !((ρ.cfg t).st id).box.isEmpty
    have hio : ∀ t, ∃ j, t ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk id) := by
      intro t
      let u := Nat.max t i
      obtain ⟨j, hj, hId⟩ := below_idle I hL hG hA ρ hF hs hok (maxHeight hs + 1) i id
        (rank_bound hs (ρ.cfg i) id) halive (fun u _ => rank_bound hs (ρ.cfg u) id)
        u (Nat.le_max_right _ _)
      have hbox : ((ρ.cfg j).st id).box ≠ [] :=
        hne j (Nat.le_trans (Nat.le_max_right t i) hj)
      exact ⟨j, Nat.le_trans (Nat.le_max_left t i) hj,
        enabled_of_can I hL hG N (ρ.cfg j) (cfg_reachable ρ j) id ⟨hId, Or.inl hbox⟩⟩
    have htake : ∀ t, i ≤ t → ∃ j, t ≤ j ∧ ρ.act j = .recvBulk id ∧ hot j = true := by
      intro t ht
      obtain ⟨j, hj, hact⟩ := hF.bulk id hio t
      have hbox : ((ρ.cfg j).st id).box ≠ [] := hne j (Nat.le_trans ht hj)
      have hhot : hot j = true := by
        cases hb : ((ρ.cfg j).st id).box with
        | nil => exact absurd hb hbox
        | cons _ _ => simp [hot, hb, List.isEmpty]
      exact ⟨j, hj, hact, hhot⟩
    obtain ⟨k, hk⟩ := enough_drops ρ id i hot htake n
    refine ⟨i + k, Nat.le_add_right _ _, Or.inl ?_⟩
    simpa [Nat.add_sub_cancel_left] using hk

theorem fair_parked (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId) (n : Nat)
    (hn : n < ((ρ.cfg i).st id).parked.length) :
    ∃ j, i ≤ j ∧
      (n < drainDrops ρ id i (fun t => !((ρ.cfg t).st id).parked.isEmpty) (j - i) ∨
        ((ρ.cfg j).st id).parked = []) := by
  cases Classical.em (∃ j, i ≤ j ∧ ((ρ.cfg j).st id).parked = []) with
  | inl h =>
    obtain ⟨j, hj, hempty⟩ := h
    exact ⟨j, hj, Or.inr hempty⟩
  | inr hnever =>
    have hne : ∀ j, i ≤ j → ((ρ.cfg j).st id).parked ≠ [] := by
      intro j hj hempty
      exact hnever ⟨j, hj, hempty⟩
    have hlive0 : ((ρ.cfg i).st id).life = .alive :=
      mailbox_alive I hL N (ρ.cfg i) (cfg_reachable ρ i) id (fun hempty => by simp [hempty] at hn)
    have halive := alive_while_parked ρ id i hlive0 hne
    obtain ⟨hs, hok⟩ := hG.ranked
    let hot : Nat → Bool := fun t => !((ρ.cfg t).st id).parked.isEmpty
    have hio : ∀ t, ∃ j, t ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk id) := by
      intro t
      let u := Nat.max t i
      obtain ⟨j, hj, hId⟩ := below_idle I hL hG hA ρ hF hs hok (maxHeight hs + 1) i id
        (rank_bound hs (ρ.cfg i) id) halive (fun u _ => rank_bound hs (ρ.cfg u) id)
        u (Nat.le_max_right _ _)
      have hpark : ((ρ.cfg j).st id).parked ≠ [] :=
        hne j (Nat.le_trans (Nat.le_max_right t i) hj)
      exact ⟨j, Nat.le_trans (Nat.le_max_left t i) hj,
        enabled_of_can I hL hG N (ρ.cfg j) (cfg_reachable ρ j) id ⟨hId, Or.inr hpark⟩⟩
    have htake : ∀ t, i ≤ t → ∃ j, t ≤ j ∧ ρ.act j = .recvBulk id ∧ hot j = true := by
      intro t ht
      obtain ⟨j, hj, hact⟩ := hF.bulk id hio t
      have hpark : ((ρ.cfg j).st id).parked ≠ [] := hne j (Nat.le_trans ht hj)
      have hhot : hot j = true := by
        cases hb : ((ρ.cfg j).st id).parked with
        | nil => exact absurd hb hpark
        | cons _ _ => simp [hot, hb, List.isEmpty]
      exact ⟨j, hj, hact, hhot⟩
    obtain ⟨k, hk⟩ := enough_drops ρ id i hot htake n
    refine ⟨i + k, Nat.le_add_right _ _, Or.inl ?_⟩
    simpa [Nat.add_sub_cancel_left] using hk

/-- A fair run under a checked graph delivers bulk mail, parked mail, and call
replies. `Assumptions` is only `rust_refines`. -/
theorem fair_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) : Delivered ρ :=
  ⟨fun i id n hn => fair_box I hL hG hA ρ hF i id n hn,
   fun i id n hn => fair_parked I hL hG hA ρ hF i id n hn,
   fun i c d k hph => call_answered I hL hG hA ρ hF i c d k hph⟩

end Deadlock
