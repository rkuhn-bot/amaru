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

import Deadlock.Progress

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
    exact False.elim (never_stuck I hL hG hA ρ hF c i hS (Or.inr (by simp [waitKind, hph])))

/-- Bulk mail in delivery order: the box, then parked messages. -/
def bulkQ (a : Actor) : List Msg := a.box ++ a.parked.map (·.msg)

/-- Index of the first message carrying `mid`. `0` when the list is empty. -/
def posOf (mid : Nat) : List Msg → Nat
  | [] => 0
  | m :: ms => if m.mid = mid then 0 else posOf mid ms + 1

theorem pos_cons_eq (m : Msg) (ms : List Msg) (mid : Nat) (h : m.mid = mid) :
    posOf mid (m :: ms) = 0 := by simp [posOf, h]

theorem pos_cons_ne (m : Msg) (ms : List Msg) (mid : Nat) (h : m.mid ≠ mid) :
    posOf mid (m :: ms) = posOf mid ms + 1 := by simp [posOf, h]

theorem pos_append (mid : Nat) (ms extra : List Msg) (h : posOf mid ms < ms.length) :
    posOf mid (ms ++ extra) = posOf mid ms := by
  induction ms with
  | nil => simp [posOf] at h
  | cons m ms ih =>
    by_cases hm : m.mid = mid
    · simp [posOf, hm]
    · have hlt : posOf mid ms < ms.length := by
        simp [posOf, hm, List.length_cons] at h
        omega
      simp [posOf, hm, ih hlt]

theorem pos_mem (mid : Nat) (ms : List Msg) (m : Msg) (hm : m ∈ ms) (hid : m.mid = mid) :
    posOf mid ms < ms.length := by
  induction ms with
  | nil => cases hm
  | cons x xs ih =>
    by_cases hx : x.mid = mid
    · simp [posOf, hx]
    · simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact absurd hid hx
      · have := ih hm
        simp [posOf, hx]
        omega

theorem pos_tail_drop (mid : Nat) (ms : List Msg) (hpos : 0 < posOf mid ms)
    (hlen : posOf mid ms < ms.length) :
    posOf mid ms.tail = posOf mid ms - 1 ∧ posOf mid ms.tail < ms.tail.length := by
  cases ms with
  | nil => simp [posOf] at hpos
  | cons m ms =>
    by_cases hm : m.mid = mid
    · simp [posOf, hm] at hpos
    · simp [posOf, hm, List.tail_cons] at hpos hlen ⊢
      omega

theorem mem_of_pos (mid : Nat) (ms : List Msg) (h : posOf mid ms < ms.length) :
    ∃ m, m ∈ ms ∧ m.mid = mid := by
  induction ms with
  | nil => simp [posOf] at h
  | cons m ms ih =>
    by_cases hm : m.mid = mid
    · exact ⟨m, List.Mem.head _, hm⟩
    · simp [posOf, hm] at h
      obtain ⟨m', hm', hid⟩ := ih (by omega)
      exact ⟨m', List.mem_cons_of_mem _ hm', hid⟩

theorem bulkQ_charge (a : Actor) (d : String) : bulkQ (chargeSender a d) = bulkQ a := by
  simp [bulkQ, charge_box, charge_parked]

theorem bulkQ_proceed (a : Actor) (k : Cont) : bulkQ (proceed a k) = bulkQ a := by
  simp [bulkQ, proceed_box, proceed_parked]

theorem bulkQ_resume (a : Actor) (isCall : Bool) (dst : InstId) :
    bulkQ (resumeSender a isCall dst) = bulkQ a := by
  simp [bulkQ, resume_box, resume_parked]

theorem bulkQ_credit (w : World) (dst : String) (sender i : InstId) :
    bulkQ ((creditSender w dst sender).st i) = bulkQ (w.st i) := by
  simp [bulkQ, credit_box, credit_park]

theorem mem_box_bulk (a : Actor) (m : Msg) (hm : m ∈ a.box) : m ∈ bulkQ a :=
  List.mem_append_left _ hm

theorem mem_park_bulk (a : Actor) (p : Parked) (hp : p ∈ a.parked) : p.msg ∈ bulkQ a :=
  List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- A stored copy keeps the reliability of the message that was offered. -/
theorem issued_reliable (msg : Msg) (n : Nat) :
    ({ msg with mid := n }).reliable = msg.reliable := rfl

/-- Enqueue appends at most one message, and only at the end of the bulk queue.
The room test stores it on the box when the parked list is empty, so the box
append is also a bulk-queue append. Parking appends the parked lane instead. -/
theorem nil_bulk (ms : List Msg) :
    ∃ extra, ms = ms ++ extra ∧ ∀ m ∈ extra, m.reliable = true :=
  ⟨[], by simp, fun _ hm => by cases hm⟩

theorem enqueue_bulk (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ∃ extra, bulkQ ((enqueueOrPark w D sender dst msg isCall k).st i) =
        bulkQ (w.st i) ++ extra ∧ ∀ m ∈ extra, m.reliable = msg.reliable := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall with
      | false =>
        by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            refine ⟨[{ msg with mid := (chargeSender (w.st dst) (tname dst)).nextMid }], ?_, ?_⟩
            · simp [setActor, charge_box, charge_parked, proceed_box, proceed_parked, bulkQ, hroom.1,
                chargeSender, bumpToken]
            · intro m hm; simp at hm; simp [hm]
          · refine ⟨[], ?_, fun _ hm => by cases hm⟩
            simp [setActor, hi, bulkQ]
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬dst = sender := fun h => hsame h.symm
            refine ⟨[{ msg with mid := (w.st dst).nextMid }], ?_, ?_⟩
            · simp [setActor, hsame, hflip, bulkQ, hroom.1]
            · intro m hm; simp at hm; simp [hm]
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              refine ⟨[], ?_, fun _ hm => by cases hm⟩
              simp [setActor, hi, bulkQ, charge_box, charge_parked, proceed_box, proceed_parked]
            · rw [if_neg hsame]
              refine ⟨[], ?_, fun _ hm => by cases hm⟩
              simp [setActor, hi, his, bulkQ]
      | true =>
        by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            refine ⟨[{ msg with mid := (chargeSender (w.st dst) (tname dst)).nextMid }], ?_, ?_⟩
            · simp [setActor, charge_box, charge_parked, bulkQ, hroom.1, chargeSender, bumpToken]
            · intro m hm; simp at hm; simp [hm]
          · refine ⟨[], ?_, fun _ hm => by cases hm⟩
            simp [setActor, hi, bulkQ]
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬dst = sender := fun h => hsame h.symm
            refine ⟨[{ msg with mid := (w.st dst).nextMid }], ?_, ?_⟩
            · simp [setActor, hsame, hflip, bulkQ, hroom.1]
            · intro m hm; simp at hm; simp [hm]
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              refine ⟨[], ?_, fun _ hm => by cases hm⟩
              simp [setActor, hi, bulkQ, charge_box, charge_parked]
            · rw [if_neg hsame]
              refine ⟨[], ?_, fun _ hm => by cases hm⟩
              simp [setActor, hi, his, bulkQ]
    · simp [hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        by_cases hi : i = dst
        · rw [hi]
          refine ⟨[{ msg with mid := (chargeSender (w.st dst) (tname dst)).nextMid }], ?_, ?_⟩
          · simp [setActor, charge_box, charge_parked, bulkQ, List.map_append, List.append_assoc]
          · intro m hm; simp at hm; simp [hm]
        · refine ⟨[], ?_, fun _ hm => by cases hm⟩
          simp [setActor, hi, bulkQ]
      · by_cases hi : i = dst
        · rw [if_neg hsame, hi]
          have hflip : ¬dst = sender := fun h => hsame h.symm
          refine ⟨[{ msg with mid := (w.st dst).nextMid }], ?_, ?_⟩
          · simp [setActor, hsame, hflip, bulkQ]
          · intro m hm; simp at hm; simp [hm]
        · by_cases his : i = sender
          · rw [his, if_neg hsame]
            refine ⟨[], ?_, fun _ hm => by cases hm⟩
            simp [setActor, hi, bulkQ, charge_box, charge_parked]
          · rw [if_neg hsame]
            refine ⟨[], ?_, fun _ hm => by cases hm⟩
            simp [setActor, hi, his, bulkQ]
  · simp [hlive]
    by_cases hi : i = sender
    · rw [hi]
      refine ⟨[], ?_, fun _ hm => by cases hm⟩
      simp [setActor, bulkQ_proceed]
    · refine ⟨[], ?_, fun _ hm => by cases hm⟩
      simp [setActor, hi, bulkQ]

theorem set_resume_bulk (w : World) (id other : InstId) (isCall : Bool) (dst : InstId) (i : InstId) :
    bulkQ ((setActor w other (resumeSender (w.st other) isCall dst)).st i) = bulkQ (w.st i) := by
  by_cases hi : i = other
  · rw [hi, setActor_self, bulkQ_resume]
  · rw [setActor_other _ _ _ _ hi]

/-- A successful bulk receive drops the logical head and leaves the tail.
When both lanes are occupied the parked head is admitted at the end of the box
tail, which is the same order as the old tail. -/
theorem bulk_recv_tail (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w') :
    bulkQ (w'.st id) = (bulkQ (w.st id)).tail := by
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
          have hd := deliver_box_of I w id _ p.msg w1 a1 hdel
          have hcred := bulkQ_credit (setActor w1 id a1) (tname id) p.msg.sender id
          rw [setActor_self] at hcred
          have hstep := set_resume_bulk (creditSender (setActor w1 id a1) (tname id) p.msg.sender)
            id p.sender p.isCall id id
          rw [hstep, hcred]
          simp [bulkQ, hd.1, hd.2, hbox, hpark, List.tail_cons]
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hd := deliver_box_of I w id _ m w1 a1 hdel
          have hcred := bulkQ_credit (setActor w1 id a1) (tname id) m.sender id
          rw [setActor_self] at hcred
          rw [hcred]
          simp [bulkQ, hd.1, hd.2, hbox, hpark, List.map_nil, List.append_nil]
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hd := deliver_box_of I w id _ m w1 a1 hdel
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hcred := bulkQ_credit (setActor w1 id admitted) (tname id) m.sender id
          rw [setActor_self] at hcred
          have hstep := set_resume_bulk (creditSender (setActor w1 id admitted) (tname id) m.sender)
            id p.sender p.isCall id id
          rw [hstep, hcred]
          simp [admitted, bulkQ, hd.1, hd.2, hbox, hpark, List.tail_cons, List.map_append,
            List.append_assoc, List.map_cons]

theorem prio_recv_tail (I : Impl) (w w' : World) (id : InstId) (h : receivePrio I w id = some w') :
    (w'.st id).prio = (w.st id).prio.tail ∧ bulkQ (w'.st id) = bulkQ (w.st id) := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp [hp] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      rcases h with ⟨_, hw⟩
      injection hw with hw
      have hpr := deliver_prio I w id _ m w1 a1 hdel
      have hd := deliver_box_of I w id _ m w1 a1 hdel
      rw [← hw]
      simp [setActor_self]
      dsimp at hpr hd
      simp [hpr, hd.1, hd.2, bulkQ, hp]

theorem pos_grow (old new : List Msg) (mid : Nat) (h : BoxGrow old new)
    (hin : posOf mid old < old.length) :
    posOf mid new = posOf mid old ∧ posOf mid new < new.length := by
  rcases h with h | ⟨m, h⟩
  · rw [h]
    exact ⟨rfl, hin⟩
  · rw [h, pos_append mid old [m] hin, List.length_append]
    refine ⟨rfl, ?_⟩
    simp
    omega

theorem set_resume_box (w : World) (id other : InstId) (isCall : Bool) (dst : InstId) :
    ((setActor w other (resumeSender (w.st other) isCall dst)).st id).box = (w.st id).box := by
  by_cases h : id = other
  · rw [h, setActor_self, resume_box]
  · rw [setActor_other _ _ _ _ h]

/-- A bulk receive takes the box head. A parked head waiting behind a nonempty
box is admitted at the end, so every message that was already in the box moves
exactly one place closer to the head. -/
theorem box_recv_drop (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (m : Msg) (ms : List Msg) (hbox : (w.st id).box = m :: ms) :
    (w'.st id).box = ms ∨ ∃ p, (w'.st id).box = ms ++ [p] := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hpark : (w.st id).parked with
    | nil =>
      simp [hbox, hpark] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hd := deliver_box_of I w id _ m w1 a1 hdel
        have hcred := credit_box (setActor w1 id a1) (tname id) m.sender id
        rw [setActor_self] at hcred
        rw [hcred]
        simp [hd.1]
    | cons p ps =>
      simp [hbox, hpark] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hd := deliver_box_of I w id _ m w1 a1 hdel
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hcred := credit_box (setActor w1 id admitted) (tname id) m.sender id
        rw [setActor_self] at hcred
        have hres := set_resume_box (creditSender (setActor w1 id admitted) (tname id) m.sender)
          id p.sender p.isCall id
        rw [hres, hcred]
        simp [admitted, hd.1]

/-- Outside this actor's own `recvBulk`, the box only grows at the end. -/
theorem box_grow_step (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hOcc : OccInv I w) (d : InstId) (hnot : a ≠ .recvBulk d) (halive : (w'.st d).life = .alive) :
    BoxGrow (w.st d).box (w'.st d).box := by
  cases a with
  | stutter =>
    cases stutter_unchanged I w w' h
    exact Or.inl rfl
  | ingress who label =>
    rcases ingress_box I w w' who label d (by simpa [apply] using h) with ⟨_, hbox⟩ | ⟨_, hbox⟩
    · exact Or.inr ⟨{ label := label, sender := who, callFrom := none, reliable := true, mid := (w.st who).nextMid }, hbox⟩
    · exact Or.inl hbox
  | recvBulk id =>
    have hid : id ≠ d := by
      intro heq
      exact hnot (by simp [heq])
    exact Or.inl (bulk_other_box I w w' id d (by simpa [apply] using h) hid.symm)
  | recvPrio id =>
    exact Or.inl (prio_box I w w' id d (by simpa [apply] using h))
  | finish id =>
    exact Or.inl (finish_box I w w' id d (by simpa [apply] using h))
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hrun : (w.st id).life = .alive
    · simp [hrun] at h
      cases hphase : (w.st id).phase with
      | run k =>
        simp [hphase] at h
        cases h
        exact exec_box I w id k d halive
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hrun] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n =>
          if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template
          { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [],
            parked := [], tokens := fun _ => 0 }
        by_cases hd : d = nid
        · have hnin : nid ∉ w.roster := by
            intro hmem
            have hix := hOcc.indexed template (w.nextIx template) hmem
            omega
          have hold := (hOcc.offEmpty nid hnin).1
          have hnew : ((readCells I.desc (setActor wR nid born) nid).st d).box = [] := by
            rw [hd, readCells_st, setActor_self]
            simp [born, withTokens]
          rw [hd] at hnew ⊢
          rw [hold, hnew]
          exact Or.inl rfl
        · have hs := readCells_st I.desc (setActor wR nid born) nid d
          rw [hs]
          simp [wR, setActor, hd]
          exact Or.inl rfl
      · cases h

theorem box_mid_mono (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (d : InstId) (mid : Nat) (i n : Nat)
    (halive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st d).life = .alive)
    (hnorecv : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .recvBulk d)
    (hin : posOf mid ((ρ.cfg i).st d).box < ((ρ.cfg i).st d).box.length) :
    posOf mid ((ρ.cfg (i + n)).st d).box = posOf mid ((ρ.cfg i).st d).box ∧
      posOf mid ((ρ.cfg (i + n)).st d).box < ((ρ.cfg (i + n)).st d).box.length := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact ⟨rfl, hin⟩
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => halive t h1 (Nat.le_trans h2 (Nat.le_succ _)))
      (fun t h1 h2 => hnorecv t h1 (by omega))
    have hOcc := (inv2_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).2.1
    have hgrow := box_grow_step I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1))
      (ρ.valid (i + n)) hOcc d
      (hnorecv (i + n) (Nat.le_add_right i n) (by omega))
      (halive (i + n + 1) (by omega) (by omega))
    have hstep := pos_grow _ _ mid hgrow hprev.2
    exact ⟨hstep.1.trans hprev.1, hstep.2⟩

theorem no_snoc {α : Type} (a : List α) (m : α) (h : a = a ++ [m]) : False := by
  have hlen := congrArg List.length h
  simp at hlen

theorem mem_grow {α : Type} (old new : List α) (m : α)
    (h : new = old ∨ ∃ e, new = old ++ [e]) (hm : m ∈ new) :
    m ∈ old ∨ new = old ++ [m] := by
  rcases h with rfl | ⟨e, rfl⟩
  · exact Or.inl hm
  · simp [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact Or.inl hm
    · exact Or.inr rfl

theorem enqueue_box_off (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hne : i ≠ dst) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).box = (w.st i).box := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall <;> by_cases hsame : sender = dst
      · rw [hsame]
        simp [setActor_other _ dst i _ hne, proceed_box]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, proceed_box, charge_box]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
      · rw [hsame]
        simp [setActor_other _ dst i _ hne]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, charge_box]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
    · simp [hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        simp [setActor_other _ dst i _ hne]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, charge_box]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
  · simp [hlive]
    by_cases hi : i = sender
    · rw [hi, setActor_self]
      exact proceed_box _ _
    · rw [setActor_other _ sender i _ hi]

theorem enqueue_park_off (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hne : i ≠ dst) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).parked = (w.st i).parked := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall <;> by_cases hsame : sender = dst
      · rw [hsame]
        simp [setActor_other _ dst i _ hne, proceed_parked]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, proceed_parked, charge_parked]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
      · rw [hsame]
        simp [setActor_other _ dst i _ hne]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, charge_parked]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
    · simp [hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        simp [setActor_other _ dst i _ hne]
      · simp [hsame]
        by_cases hi : i = sender
        · have hns : sender ≠ dst := hsame
          rw [hi]
          simp [setActor_self, setActor_other _ dst sender _ hns, charge_parked]
        · simp [setActor_other _ sender i _ hi, setActor_other _ dst i _ hne]
  · simp [hlive]
    by_cases hi : i = sender
    · rw [hi, setActor_self]
      exact proceed_parked _ _
    · rw [setActor_other _ sender i _ hi]

/-- The bulk message a `recvBulk` consumes: the box head, otherwise the parked head. -/
def takenBulk (a : Actor) (mid : Nat) : Prop :=
  match a.box, a.parked with
  | m :: _, _ => m.mid = mid
  | [], p :: _ => p.msg.mid = mid
  | [], [] => False

/-- The priority message a `recvPrio` consumes. -/
def takenPrio (a : Actor) (mid : Nat) : Prop :=
  match a.prio with
  | m :: _ => m.mid = mid
  | [] => False

/-- Every reliable message is later the head consumed by `recvBulk` or `recvPrio`,
matched by the id the storing actor assigned. A try-drop send and a superseding
cell wake are not obligations. An admitted call leaves `awaitReply`. -/
def Delivered {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  (∀ i id m, m ∈ ((ρ.cfg i).st id).box → m.reliable = true →
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) m.mid) ∧
  (∀ i id p, p ∈ ((ρ.cfg i).st id).parked → p.msg.reliable = true →
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) p.msg.mid) ∧
  (∀ i id m, m ∈ ((ρ.cfg i).st id).prio → m.reliable = true →
    ∃ j, i ≤ j ∧ ρ.act j = .recvPrio id ∧ takenPrio ((ρ.cfg j).st id) m.mid) ∧
  (∀ i c d k, ((ρ.cfg i).st c).phase = .awaitReply d k →
    ∃ j, i ≤ j ∧ ((ρ.cfg j).st c).phase ≠ .awaitReply d k)

theorem nonterm_stays {I : Impl} {N : Nat} (ρ : Run I N) (id : InstId) (i : Nat)
    (h0 : ((ρ.cfg i).st id).life = .alive) (hterm : terminableB I.desc (tname id) = false) :
    ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive := by
  intro t ht
  have hall : ∀ n, ((ρ.cfg (i + n)).st id).life = .alive := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      by_cases hlive : ((ρ.cfg (i + n + 1)).st id).life = .alive
      · exact hlive
      · obtain ⟨_, _, _, tpl, _, _, htpl, hflag⟩ :=
          only_terminate_kills I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) id
            (ρ.valid (i + n)) ih hlive
        simp [Bool.and_eq_true] at hflag
        simp [terminableB, htpl, hflag.1] at hterm
  simpa [Nat.add_sub_of_le ht] using hall (t - i)

theorem pos_drop (mid : Nat) (m : Msg) (ms new : List Msg) (hne : m.mid ≠ mid)
    (hold : posOf mid (m :: ms) < (m :: ms).length)
    (h : new = ms ∨ ∃ p, new = ms ++ [p]) :
    posOf mid new = posOf mid (m :: ms) - 1 ∧ posOf mid new < new.length := by
  have hlt : posOf mid ms < ms.length := by
    simp [posOf, hne, List.length_cons] at hold
    omega
  have hpos : posOf mid (m :: ms) = posOf mid ms + 1 := pos_cons_ne m ms mid hne
  rcases h with rfl | ⟨_, rfl⟩
  · rw [hpos]
    exact ⟨by omega, by simpa using hlt⟩
  · rw [pos_append mid ms _ hlt, hpos, List.length_append]
    simp
    omega

/-- A reliable-free template stays alive, so a message that keeps its box index is
received. `n` is that index. Each bulk receive before it is the head moves it
one place forward, and the receive that finds it at the head consumes it. -/
theorem box_mid_taken (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (id : InstId) (mid : Nat) (i : Nat)
    (hterm : terminableB I.desc (tname id) = false)
    (hlive : ((ρ.cfg i).st id).life = .alive)
    (hpos : posOf mid ((ρ.cfg i).st id).box < ((ρ.cfg i).st id).box.length) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) mid := by
  suffices ∀ n i, posOf mid ((ρ.cfg i).st id).box = n →
      posOf mid ((ρ.cfg i).st id).box < ((ρ.cfg i).st id).box.length →
      ((ρ.cfg i).st id).life = .alive →
      ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) mid by
    exact this _ i rfl hpos hlive
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hpeq hlt hlive0
    have halive : ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive :=
      nonterm_stays ρ id i hlive0 hterm
    have hstill : ∀ t, i ≤ t → (∀ u, i ≤ u → u < t → ρ.act u ≠ .recvBulk id) →
        posOf mid ((ρ.cfg t).st id).box = n ∧
          posOf mid ((ρ.cfg t).st id).box < ((ρ.cfg t).st id).box.length := by
      intro t ht hnorecv
      have hm := box_mid_mono I hL hG ρ id mid i (t - i)
        (fun u hu _ => halive u hu) (fun u hu hlt' => hnorecv u hu (by omega)) (by simpa [hpeq] using hlt)
      have hsum : i + (t - i) = t := Nat.add_sub_of_le ht
      simpa [hsum, hpeq] using hm
    by_cases hex : ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id
    · obtain ⟨j0, hj0, hact0⟩ := hex
      have hscan := scanAct_spec ρ.act (.recvBulk id) (j0 - i) i
        ⟨j0 - i, Nat.le_refl _, by simpa [Nat.add_sub_of_le hj0] using hact0⟩
      let j := scanAct ρ.act (.recvBulk id) (j0 - i) i
      have hj : i ≤ j := hscan.1
      have hact : ρ.act j = .recvBulk id := hscan.2.1
      have hfirst : ∀ t, i ≤ t → t < j → ρ.act t ≠ .recvBulk id := hscan.2.2
      have hat := hstill j hj hfirst
      have hv := ρ.valid j
      simp [apply, hact] at hv
      cases hbox : ((ρ.cfg j).st id).box with
      | nil =>
        simp [hbox, posOf] at hat
      | cons m ms =>
        by_cases hm : m.mid = mid
        · refine ⟨j, hj, hact, ?_⟩
          simp [takenBulk, hbox, hm]
        · have hgt : 0 < n := by
            have hposj : posOf mid ((ρ.cfg j).st id).box = n := hat.1
            simp [hbox, posOf, hm] at hposj
            omega
          have hdrop := box_recv_drop I (ρ.cfg j) (ρ.cfg (j + 1)) id hv m ms hbox
          have hdec := pos_drop mid m ms _ hm (by simpa [hbox] using hat.2) hdrop
          have hnext : posOf mid ((ρ.cfg (j + 1)).st id).box = n - 1 := by
            have hhead : posOf mid (m :: ms) = n := by simpa [hbox] using hat.1
            rw [hdec.1, hhead]
          have hlt' : posOf mid ((ρ.cfg (j + 1)).st id).box <
              ((ρ.cfg (j + 1)).st id).box.length := hdec.2
          have hlive' : ((ρ.cfg (j + 1)).st id).life = .alive :=
            halive (j + 1) (Nat.le_trans hj (Nat.le_succ _))
          obtain ⟨k, hk, hactk, htaken⟩ :=
            ih (n - 1) (by omega) (j + 1) hnext hlt' hlive'
          exact ⟨k, Nat.le_trans hj (Nat.le_trans (Nat.le_succ _) hk), hactk, htaken⟩
    · have hnever : ∀ t, i ≤ t → ρ.act t ≠ .recvBulk id := by
        intro t ht hact
        exact hex ⟨t, ht, hact⟩
      have hfree : ∀ t, i ≤ t → ¬Stuck ρ id t := fun t ht hS =>
        never_stuck I hL hG hA ρ hF id t hS
          (Or.inl (permanent_finishable I.desc hG.peers id hterm))
      have hio : ∀ s, ∃ j, s ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk id) := by
        intro s
        obtain ⟨j, hj, hId⟩ := idle_when_free I hL hG hA ρ hF id i halive hfree
          (Nat.max s i) (Nat.le_max_right _ _)
        have hmail := hstill j (Nat.le_trans (Nat.le_max_right s i) hj)
          (fun u hu _ => hnever u hu)
        have hne : ((ρ.cfg j).st id).box ≠ [] := by
          intro hempty
          simp [hempty, posOf] at hmail
        exact ⟨j, Nat.le_trans (Nat.le_max_left s i) hj,
          enabled_of_can I hL hG N (ρ.cfg j) (cfg_reachable ρ j) id ⟨hId, Or.inl hne⟩⟩
      obtain ⟨j, hj, hact⟩ := hF.bulk id hio i
      exact False.elim (hex ⟨j, hj, hact⟩)

theorem terminable_name_iff (D : Description) (name : String) :
    terminableB D name = true ↔ terminableName D name := by
  unfold terminableB terminableName
  cases templateOf D name with
  | none => simp
  | some t =>
    constructor
    · intro h
      exact ⟨t, rfl, h⟩
    · intro ⟨t', ht, htm⟩
      cases ht
      exact htm

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
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId)
    (hf : peerFinishable I.desc id = true) (n : Nat)
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
      obtain ⟨j, hj, hset⟩ := below_idle I hL hG hA ρ hF hs hok (maxHeight hs + 1) i id
        (rank_bound hs (ρ.cfg i) id) halive (fun u _ => rank_bound hs (ρ.cfg u) id)
        u (Nat.le_max_right _ _)
      have hId : Idle (ρ.cfg j) id := by
        rcases hset with hId | ⟨_, _, hp⟩
        · exact hId
        · simp [hf] at hp
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
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId)
    (hf : peerFinishable I.desc id = true) (n : Nat)
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
      obtain ⟨j, hj, hset⟩ := below_idle I hL hG hA ρ hF hs hok (maxHeight hs + 1) i id
        (rank_bound hs (ρ.cfg i) id) halive (fun u _ => rank_bound hs (ρ.cfg u) id)
        u (Nat.le_max_right _ _)
      have hId : Idle (ρ.cfg j) id := by
        rcases hset with hId | ⟨_, _, hp⟩
        · exact hId
        · simp [hf] at hp
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

/-- A terminable actor stores no reliable message. A try-send and a cell wake
may sit in its lanes; a reliable send, call, ingress, or self-schedule may not. -/
def ReliableFree (a : Actor) : Prop :=
  (∀ m ∈ a.box, m.reliable = false) ∧
  (∀ p ∈ a.parked, p.msg.reliable = false) ∧
  (∀ m ∈ a.prio, m.reliable = false)

theorem transport_free {a b : Actor} (h : ReliableFree a)
    (hbox : b.box = a.box) (hpark : b.parked = a.parked) (hprio : b.prio = a.prio) :
    ReliableFree b := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    rw [hbox] at hm
    exact h.1 m hm
  · intro p hp
    rw [hpark] at hp
    exact h.2.1 p hp
  · intro m hm
    rw [hprio] at hm
    exact h.2.2 m hm

theorem reliable_free_init (I : Impl) (N : Nat) (id : InstId) :
    ReliableFree ((initWorld I N).st id) := by
  have h := init_box I N id
  have hp := init_prio_empty I N id
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp [h.1] at hm
  · intro p hp
    simp [h.2] at hp
  · intro m hm
    simp [hp] at hm

theorem mem_tail {α : Type} (xs : List α) (m : α) (hm : m ∈ xs.tail) : m ∈ xs := by
  cases xs with
  | nil => simp at hm
  | cons x xs =>
    simp at hm
    exact List.mem_cons_of_mem x hm

theorem set_proceed_box (w : World) (id : InstId) (k : Cont) (i : InstId) :
    ((setActor w id (proceed (w.st id) k)).st i).box = (w.st i).box := by
  by_cases hi : i = id
  · rw [hi, setActor_self, proceed_box]
  · rw [setActor_other _ _ _ _ hi]

theorem set_proceed_parked (w : World) (id : InstId) (k : Cont) (i : InstId) :
    ((setActor w id (proceed (w.st id) k)).st i).parked = (w.st i).parked := by
  by_cases hi : i = id
  · rw [hi, setActor_self, proceed_parked]
  · rw [setActor_other _ _ _ _ hi]

theorem set_proceed_prio (w : World) (id : InstId) (k : Cont) (i : InstId) :
    ((setActor w id (proceed (w.st id) k)).st i).prio = (w.st i).prio := by
  by_cases hi : i = id
  · rw [hi, setActor_self, proceed_prio]
  · rw [setActor_other _ _ _ _ hi]

theorem reply_box (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).box = (w.st i).box := by
  unfold performReply
  cases hto : k.replyTo with
  | none =>
    simpa [hto] using set_proceed_box w sender (afterHead k) i
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · simp only [hto, hph, hd, if_true]
        let inner := setActor w caller (proceed (w.st caller) ck)
        by_cases hs : i = sender
        · rw [hs, setActor_self, proceed_box]
          exact set_proceed_box w caller ck sender
        · rw [setActor_other _ sender i _ hs]
          exact set_proceed_box w caller ck i
      · simpa [hto, hph, hd] using set_proceed_box w sender (afterHead k) i
    | idle => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i
    | run _ => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i
    | parked _ _ _ => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i
    | awaitEffect _ => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i
    | awaitPeer _ => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i
    | crashed => simpa [hto, hph] using set_proceed_box w sender (afterHead k) i

theorem reply_parked (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).parked = (w.st i).parked := by
  unfold performReply
  cases hto : k.replyTo with
  | none =>
    simpa [hto] using set_proceed_parked w sender (afterHead k) i
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · simp only [hto, hph, hd, if_true]
        by_cases hs : i = sender
        · rw [hs, setActor_self, proceed_parked]
          exact set_proceed_parked w caller ck sender
        · rw [setActor_other _ sender i _ hs]
          exact set_proceed_parked w caller ck i
      · simpa [hto, hph, hd] using set_proceed_parked w sender (afterHead k) i
    | idle => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i
    | run _ => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i
    | parked _ _ _ => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i
    | awaitEffect _ => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i
    | awaitPeer _ => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i
    | crashed => simpa [hto, hph] using set_proceed_parked w sender (afterHead k) i

theorem reply_parked_prio (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).prio = (w.st i).prio := by
  unfold performReply
  cases hto : k.replyTo with
  | none =>
    simpa [hto] using set_proceed_prio w sender (afterHead k) i
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · simp only [hto, hph, hd, if_true]
        by_cases hs : i = sender
        · rw [hs, setActor_self, proceed_prio]
          exact set_proceed_prio w caller ck sender
        · rw [setActor_other _ sender i _ hs]
          exact set_proceed_prio w caller ck i
      · simpa [hto, hph, hd] using set_proceed_prio w sender (afterHead k) i
    | idle => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i
    | run _ => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i
    | parked _ _ _ => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i
    | awaitEffect _ => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i
    | awaitPeer _ => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i
    | crashed => simpa [hto, hph] using set_proceed_prio w sender (afterHead k) i

theorem finish_prio (I : Impl) (w w' : World) (id i : InstId) (h : finishWait I w id = some w') :
    (w'.st i).prio = (w.st i).prio := by
  obtain ⟨_, _, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  by_cases hi : i = id <;> simp [setActor, hi, proceed_prio]

theorem enqueue_unreliable (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hrel : msg.reliable = false)
    (hfree : ReliableFree (w.st i)) :
    ReliableFree ((enqueueOrPark w D sender dst msg isCall k).st i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    rcases enqueue_box_mem w D sender dst msg isCall k i m hm with hm | ⟨_, heq, _⟩
    · exact hfree.1 m hm
    · rw [heq, issued_reliable, hrel]
  · intro p hp
    rcases enqueue_parked_mem w D sender dst msg isCall k i p hp with hp | ⟨_, _, heq, _, _⟩
    · exact hfree.2.1 p hp
    · rw [heq, issued_reliable, hrel]
  · intro m hm
    rw [enqueue_prio w D sender dst msg isCall k i] at hm
    exact hfree.2.2 m hm

/-- A blocking send from a checked program lands on a template that does not die. -/
theorem send_lands_permanent (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hS : SemInv I w) (who : InstId) (k : Cont) (dst label : String) (hint : Nat) (es : List Eff)
    (hph : (w.st who).phase = .run k) (hk : k.rest = .send dst label hint :: es)
    (dstId : InstId) (hr : route w I.desc dst hint = some dstId) :
    terminableB I.desc (tname dstId) = false := by
  have hprog : effectsOk I.desc (tname who) (w.st who).typestate k.rest = true := by
    simpa [programOk, hph] using hS.prog who
  rw [hk] at hprog
  have hhead := head_send I.desc (tname who) (w.st who).typestate dst label hint es hprog
  obtain ⟨e, he, _, _, hdst, heff, _, _⟩ :=
    hasEdge_mem I.desc (tname who) (w.st who).typestate dst .send .blocking label hhead.1
  obtain ⟨t, ht, _, htm⟩ := wait_template I hL hG e he (Or.inl heff)
  have hname := route_tname w I.desc dst hint dstId hr
  have hto : templateOf I.desc (tname dstId) = some t := by
    rw [hname, ← hdst]
    exact ht
  simp [terminableB, hto, htm]

/-- A blocking call from a checked program lands on a template that does not die. -/
theorem call_lands_permanent (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hS : SemInv I w) (who : InstId) (k : Cont) (dst label : String) (hint : Nat) (es : List Eff)
    (hph : (w.st who).phase = .run k) (hk : k.rest = .call dst label hint :: es)
    (dstId : InstId) (hr : route w I.desc dst hint = some dstId) :
    terminableB I.desc (tname dstId) = false := by
  have hprog : effectsOk I.desc (tname who) (w.st who).typestate k.rest = true := by
    simpa [programOk, hph] using hS.prog who
  rw [hk] at hprog
  have hhead := head_call I.desc (tname who) (w.st who).typestate dst label hint es hprog
  obtain ⟨e, he, _, _, hdst, heff, _, _⟩ :=
    hasEdge_mem I.desc (tname who) (w.st who).typestate dst .call .blocking label hhead.1
  obtain ⟨t, ht, _, htm⟩ := wait_template I hL hG e he (Or.inr heff)
  have hname := route_tname w I.desc dst hint dstId hr
  have hto : templateOf I.desc (tname dstId) = some t := by
    rw [hname, ← hdst]
    exact ht
  simp [terminableB, hto, htm]

theorem kill_prio_empty (I : Impl) (w : World) (id : InstId) (t : Template) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (ht : templateOf I.desc (tname id) = some t)
    (hflag : (t.terminable && !hasParkedCall (w.st id).parked) = true) :
    ((execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩).st id).prio = [] := by
  let base :=
    refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
      (w.st id).parked
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hstep : execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ =
      releaseParked (setActor base id dead) id (w.st id).parked := by
    simp [execRun, ht, hflag, base, dead]
  rw [hstep, release_prio]
  simp [setActor, dead]

theorem kill_off (I : Impl) (w : World) (who i : InstId) (t : Template) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (ht : templateOf I.desc (tname who) = some t)
    (hflag : (t.terminable && !hasParkedCall (w.st who).parked) = true) (hne : i ≠ who) :
    ((execRun I w who (w.st who) ⟨.terminate :: tail, toState, replyTo⟩).st i).box = (w.st i).box ∧
      ((execRun I w who (w.st who) ⟨.terminate :: tail, toState, replyTo⟩).st i).parked =
        (w.st i).parked ∧
      ((execRun I w who (w.st who) ⟨.terminate :: tail, toState, replyTo⟩).st i).prio =
        (w.st i).prio := by
  let base :=
    refundParked (refundMsgs (readCells I.desc w who) (tname who) (w.st who).box) (tname who)
      (w.st who).parked
  let dead : Actor :=
    { base.st who with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hstep : execRun I w who (w.st who) ⟨.terminate :: tail, toState, replyTo⟩ =
      releaseParked (setActor base who dead) who (w.st who).parked := by
    simp [execRun, ht, hflag, base, dead]
  refine ⟨?_, ?_, ?_⟩
  · rw [hstep, release_box, setActor_other _ who i dead hne]
    simp [base, refundP_box, refund_box, readCells_st]
  · rw [hstep, release_preserves_parked, setActor_other _ who i dead hne]
    simp [base, refundP_park, refund_park, readCells_st]
  · rw [hstep, release_prio, setActor_other _ who i dead hne]
    simp [base, refundP_prio, refund_prio, readCells_st]

theorem try_wake_free (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) (h : ReliableFree (w.st i)) :
    ReliableFree ((tryWake D w dstId label writer).st i) := by
  have hbox := try_wake_box D w dstId label writer i
  have hpark := try_wake_parked D w dstId label writer i
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    rw [hbox] at hm
    exact h.1 m hm
  · intro p hp
    rw [hpark] at hp
    exact h.2.1 p hp
  · intro m hm
    by_cases hif : ((w.st dstId).life == .alive &&
        decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
        !((w.st dstId).prio.any fun p => p.label == label)) = true
    · simp [tryWake, hif] at hm
      by_cases hi : i = dstId
      · rw [hi, setActor_self] at hm
        simp only [Bool.and_eq_true] at hif
        have hfalse : ((w.st dstId).prio.any fun p => p.label == label) = false := by
          simpa [Bool.not_eq_true] using hif.2
        have happ : upsertPrio (w.st dstId).prio
            { label := label, sender := writer, callFrom := none, reliable := false,
              mid := (w.st dstId).nextMid } =
            (w.st dstId).prio ++
              [{ label := label, sender := writer, callFrom := none, reliable := false,
                 mid := (w.st dstId).nextMid }] := by
          simp [upsertPrio, hfalse]
        rw [happ, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact h.2.2 m (by simpa [hi] using hm)
        · rfl
      · rw [setActor_other _ dstId i _ hi] at hm
        exact h.2.2 m hm
    · simp [tryWake, hif] at hm
      exact h.2.2 m hm

theorem wakes_free (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer i : InstId) (h : ReliableFree (w.st i)) :
    ReliableFree ((ids.foldl (fun w id => tryWake D w id label writer) w).st i) := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact ih _ (try_wake_free D w j label writer i h)

theorem proceed_free (w : World) (who : InstId) (k : Cont) (i : InstId)
    (h : ReliableFree (w.st i)) :
    ReliableFree ((setActor w who (proceed (w.st who) k)).st i) :=
  transport_free h (set_proceed_box w who k i) (set_proceed_parked w who k i)
    (set_proceed_prio w who k i)

/-- One step keeps every terminable actor free of reliable mail. -/
theorem reliable_free_step (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w w' : World) (a : Action) (hR : Reachable I N w) (h : apply I a w = some w')
    (ih : ∀ id, terminableB I.desc (tname id) = true → ReliableFree (w.st id))
    (id : InstId) (hterm : terminableB I.desc (tname id) = true) :
    ReliableFree (w'.st id) := by
  have hS : SemInv I w := (inv_reachable I N w hL hR).1
  have hB : BulkFree I w := (inv2_reachable I hL hG N w hR).2.2.2
  have hold : ReliableFree (w.st id) := ih id hterm
  cases a with
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hold
  | ingress who label =>
    have hrec : receiveIngress I w who label = some w' := by simpa [apply] using h
    by_cases hi : id = who
    · have hopen := ingress_open I w w' who label hrec
      rw [hi] at hterm
      rw [hopen.2.2.1] at hterm
      cases hterm
    · rcases ingress_box I w w' who label id hrec with ⟨heq, _⟩ | ⟨_, hbox⟩
      · exact absurd heq hi
      · exact transport_free hold hbox (ingress_parked I w w' who label id hrec).1
          (ingress_phase I w w' who label id hrec).2.2.1
  | recvBulk j =>
    have hrec : receiveBulk I w j = some w' := by simpa [apply] using h
    by_cases hi : id = j
    · have htail := bulk_recv_tail I w w' j hrec
      have hprio := bulk_prio_eq I w w' j id hrec
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m ∈ (w'.st j).box := by simpa [hi] using hm
        have hmem : m ∈ bulkQ (w'.st j) := mem_box_bulk _ m hm'
        rw [htail] at hmem
        have holdm := mem_tail _ m hmem
        simp [bulkQ, List.mem_append, List.mem_map] at holdm
        rcases holdm with hbox | ⟨p, hp, hmsg⟩
        · exact hold.1 m (by simpa [hi] using hbox)
        · have hp' : p ∈ (w.st id).parked := by simpa [hi] using hp
          rw [← hmsg]
          exact hold.2.1 p hp'
      · intro p hp
        have hp' : p ∈ (w'.st j).parked := by simpa [hi] using hp
        have hmem : p.msg ∈ bulkQ (w'.st j) := mem_park_bulk _ p hp'
        rw [htail] at hmem
        have holdm := mem_tail _ p.msg hmem
        simp [bulkQ, List.mem_append, List.mem_map] at holdm
        rcases holdm with hbox | ⟨q, hq, hmsg⟩
        · exact hold.1 p.msg (by simpa [hi] using hbox)
        · have hq' : q ∈ (w.st id).parked := by simpa [hi] using hq
          rw [← hmsg]
          exact hold.2.1 q hq'
      · intro m hm
        rw [hprio] at hm
        exact hold.2.2 m hm
    · exact transport_free hold (bulk_other_box I w w' j id hrec hi)
        (bulk_other_parked I w w' j id hrec hi) (bulk_prio_eq I w w' j id hrec)
  | recvPrio j =>
    have hrec : receivePrio I w j = some w' := by simpa [apply] using h
    have hbox := prio_box I w w' j id hrec
    have hpark := prio_parked I w w' j id hrec
    by_cases hi : id = j
    · have htail := prio_recv_tail I w w' j hrec
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        rw [hbox] at hm
        exact hold.1 m hm
      · intro p hp
        rw [hpark] at hp
        exact hold.2.1 p hp
      · intro m hm
        have hm' : m ∈ (w'.st j).prio := by simpa [hi] using hm
        rw [htail.1] at hm'
        exact hold.2.2 m (mem_tail _ m (by simpa [hi] using hm'))
    · have hpr : (w'.st id).prio = (w.st id).prio := by
        unfold receivePrio at hrec
        cases hp : (w.st j).prio with
        | nil => simp [hp] at hrec
        | cons m ms =>
          simp [hp] at hrec
          split at hrec
          · simp at hrec
          · next w1 a1 hdel =>
            cases hrec.2
            have hst := deliver_st I w j _ m w1 a1 id hdel
            simp [setActor, hi, hst]
      exact transport_free hold hbox hpark hpr
  | finish who =>
    have hfin : finishWait I w who = some w' := by simpa [apply] using h
    exact transport_free hold (finish_box I w w' who id hfin)
      (finish_parked I w w' who id hfin) (finish_prio I w w' who id hfin)
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n =>
          if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template
          { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [],
            parked := [], tokens := fun _ => 0 }
        by_cases hd : id = nid
        · rw [hd, readCells_st, setActor_self]
          refine ⟨?_, ?_, ?_⟩
          · intro m hm
            simp [born, withTokens] at hm
          · intro p hp
            simp [born, withTokens] at hp
          · intro m hm
            simp [born, withTokens] at hm
        · rw [readCells_st, setActor_other _ nid id born hd]
          simp [wR]
          exact hold
      · cases h
  | exec who =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hrun : (w.st who).life = .alive
    · simp [hrun] at h
      cases hphase : (w.st who).phase with
      | run k =>
        simp [hphase] at h
        cases h
        cases hk : k.rest with
        | nil =>
          simp [execRun, hk]
          exact transport_free hold
            (by by_cases hi : id = who <;> simp [setActor, hi])
            (by by_cases hi : id = who <;> simp [setActor, hi])
            (by by_cases hi : id = who <;> simp [setActor, hi])
        | cons e es =>
          cases e with
          | send dst label hint =>
            simp only [execRun, hk]
            cases hr : route w I.desc dst hint with
            | none =>
              simpa [hr] using proceed_free w who (afterHead k) id hold
            | some dstId =>
              simp only [hr]
              by_cases hid : id = dstId
              · have hbad := send_lands_permanent I hL hG w hS who k dst label hint es hphase hk
                  dstId hr
                rw [← hid] at hbad
                rw [hbad] at hterm
                cases hterm
              · exact transport_free hold
                  (enqueue_box_off w I.desc who dstId
                    { label := label, sender := who, callFrom := none } false (afterHead k) id hid)
                  (enqueue_park_off w I.desc who dstId
                    { label := label, sender := who, callFrom := none } false (afterHead k) id hid)
                  (enqueue_prio w I.desc who dstId
                    { label := label, sender := who, callFrom := none } false (afterHead k) id)
          | call dst label hint =>
            simp only [execRun, hk]
            cases hr : route w I.desc dst hint with
            | none =>
              simpa [hr] using proceed_free w who (afterHead k) id hold
            | some dstId =>
              simp only [hr]
              by_cases hid : id = dstId
              · have hbad := call_lands_permanent I hL hG w hS who k dst label hint es hphase hk
                  dstId hr
                rw [← hid] at hbad
                rw [hbad] at hterm
                cases hterm
              · exact transport_free hold
                  (enqueue_box_off w I.desc who dstId
                    { label := label, sender := who, callFrom := some who } true (afterHead k) id hid)
                  (enqueue_park_off w I.desc who dstId
                    { label := label, sender := who, callFrom := some who } true (afterHead k) id hid)
                  (enqueue_prio w I.desc who dstId
                    { label := label, sender := who, callFrom := some who } true (afterHead k) id)
          | trySend dst label hint =>
            simp only [execRun, hk]
            cases hr : route w I.desc dst hint with
            | none =>
              simpa [hr] using proceed_free w who (afterHead k) id hold
            | some dstId =>
              simp only [hr]
              split
              · exact enqueue_unreliable w I.desc who dstId
                  { label := label, sender := who, callFrom := none, reliable := false } false
                  (afterHead k) id rfl hold
              · exact proceed_free w who (afterHead k) id hold
          | reply =>
            simp only [execRun, hk]
            exact transport_free hold (reply_box w who k id) (reply_parked w who k id)
              (reply_parked_prio w who k id)
          | selfSchedule label =>
            by_cases hi : id = who
            · have hbad := hB id ((terminable_name_iff I.desc (tname id)).mp hterm)
              simp [hi, contRest, hphase, hk, noBulkSend] at hbad
            · simp only [execRun, hk]
              split
              · simpa [setActor, hi, proceed_box, proceed_parked, proceed_prio] using hold
              · split
                · simpa [setActor, hi, proceed_box, proceed_parked, proceed_prio] using hold
                · simpa [setActor, hi] using hold
          | cell dst label value =>
            simp only [execRun, hk]
            let baseW :=
              setActor (setCell w dst label
                  { value := max (w.cell dst label).value value, dirty := true }) who
                (proceed ((setCell w dst label
                    { value := max (w.cell dst label).value value, dirty := true }).st who)
                  (afterHead k))
            have hbase : ReliableFree (baseW.st id) := by
              by_cases hi : id = who
              · rw [hi, setActor_self]
                apply transport_free (by simpa [hi] using hold)
                · simp [baseW, proceed_box, setCell]
                · simp [baseW, proceed_parked, setCell]
                · simp [baseW, proceed_prio, setCell]
              · simp [baseW, setActor, setCell, hi]
                exact hold
            split
            · exact hbase
            · simp only [wakeReaders]
              exact wakes_free I.desc (readersOf baseW dst) baseW label who id hbase
          | internal =>
            simp only [execRun, hk]
            exact transport_free hold
              (by by_cases hi : id = who <;> simp [setActor, hi])
              (by by_cases hi : id = who <;> simp [setActor, hi])
              (by by_cases hi : id = who <;> simp [setActor, hi])
          | peer =>
            simp only [execRun, hk]
            exact transport_free hold
              (by by_cases hi : id = who <;> simp [setActor, hi])
              (by by_cases hi : id = who <;> simp [setActor, hi])
              (by by_cases hi : id = who <;> simp [setActor, hi])
          | terminate =>
            have hcont : execRun I w who (w.st who) k =
                execRun I w who (w.st who) ⟨.terminate :: es, k.toState, k.replyTo⟩ := by
              cases k
              simp at hk
              simp [hk]
            rw [hcont]
            cases ht : templateOf I.desc (tname who) with
            | none =>
              simp [execRun, ht]
              exact hold
            | some t =>
              by_cases hflag : (t.terminable && !hasParkedCall (w.st who).parked) = true
              · by_cases hi : id = who
                · refine ⟨?_, ?_, ?_⟩
                  · intro m hm
                    rw [hi, kill_box_empty I w who t es k.toState k.replyTo ht hflag] at hm
                    cases hm
                  · intro p hp
                    rw [hi, kill_park_empty I w who t es k.toState k.replyTo ht hflag] at hp
                    cases hp
                  · intro m hm
                    rw [hi, kill_prio_empty I w who t es k.toState k.replyTo ht hflag] at hm
                    cases hm
                · have hoff := kill_off I w who id t es k.toState k.replyTo ht hflag hi
                  exact transport_free hold hoff.1 hoff.2.1 hoff.2.2
              · have hfalse : (t.terminable && !hasParkedCall (w.st who).parked) = false := by
                  cases hb : (t.terminable && !hasParkedCall (w.st who).parked) <;> simp_all
                simp [execRun, ht, hfalse]
                exact hold
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hrun] at h

theorem reliable_free_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) :
    ∀ id, terminableB I.desc (tname id) = true → ReliableFree (w.st id) := by
  induction hR with
  | init =>
    intro id _
    exact reliable_free_init I N id
  | step w w' a prev ha ih =>
    intro id hterm
    exact reliable_free_step I hL hG N w w' a prev ha ih id hterm

/-- A reliable message cannot sit on a template the checker allows to die. -/
theorem reliable_permanent (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id : InstId) (hheld : ¬ReliableFree (w.st id)) :
    terminableB I.desc (tname id) = false := by
  cases hb : terminableB I.desc (tname id) with
  | false => rfl
  | true => exact absurd (reliable_free_reachable I hL hG N w hR id hb) hheld

theorem pos_queue (mid : Nat) (old new : List Parked) (h : QueueGrow old new)
    (hin : posOf mid (old.map (·.msg)) < old.length) :
    posOf mid (new.map (·.msg)) = posOf mid (old.map (·.msg)) ∧
      posOf mid (new.map (·.msg)) < new.length := by
  rcases h with rfl | ⟨a, rfl⟩
  · exact ⟨rfl, hin⟩
  · have hin' : posOf mid (old.map (·.msg)) < (old.map (·.msg)).length := by simpa using hin
    rw [List.map_append, pos_append mid _ _ hin']
    refine ⟨rfl, ?_⟩
    simpa using Nat.lt_succ_of_lt hin

theorem park_pos_drop (mid : Nat) (p : Parked) (ps : List Parked) (hne : p.msg.mid ≠ mid)
    (hlen : posOf mid ((p :: ps).map (·.msg)) < (p :: ps).length) :
    posOf mid (ps.map (·.msg)) = posOf mid ((p :: ps).map (·.msg)) - 1 ∧
      posOf mid (ps.map (·.msg)) < ps.length := by
  simp [List.map_cons, posOf, hne, List.length_cons] at hlen ⊢
  omega

/-- Outside this actor's own `recvBulk`, parked mail only grows at the end. -/
theorem park_grow_step (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hOcc : OccInv I w) (d : InstId) (hnot : a ≠ .recvBulk d) (halive : (w'.st d).life = .alive) :
    QueueGrow (w.st d).parked (w'.st d).parked := by
  cases a with
  | stutter =>
    cases stutter_unchanged I w w' h
    exact Or.inl rfl
  | ingress who label =>
    exact Or.inl (ingress_parked I w w' who label d (by simpa [apply] using h)).1
  | recvBulk id =>
    have hid : id ≠ d := by
      intro heq
      exact hnot (by simp [heq])
    exact Or.inl (bulk_other_parked I w w' id d (by simpa [apply] using h) hid.symm)
  | recvPrio id =>
    exact Or.inl (prio_parked I w w' id d (by simpa [apply] using h))
  | finish id =>
    exact Or.inl (finish_parked I w w' id d (by simpa [apply] using h))
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hrun : (w.st id).life = .alive
    · simp [hrun] at h
      cases hphase : (w.st id).phase with
      | run k =>
        simp [hphase] at h
        cases h
        exact exec_queue I w id k d halive
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hrun] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n =>
          if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template
          { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [],
            parked := [], tokens := fun _ => 0 }
        by_cases hd : d = nid
        · have hnin : nid ∉ w.roster := by
            intro hmem
            have hix := hOcc.indexed template (w.nextIx template) hmem
            omega
          have hempty := (hOcc.offEmpty nid hnin).2
          have hnew : ((readCells I.desc (setActor wR nid born) nid).st d).parked = [] := by
            rw [hd, readCells_st, setActor_self]
            simp [born, withTokens]
          rw [hd] at hnew ⊢
          rw [hempty, hnew]
          exact Or.inl rfl
        · have hs := readCells_st I.desc (setActor wR nid born) nid d
          rw [hs]
          simp [wR, setActor, hd]
          exact Or.inl rfl
      · cases h

theorem park_pos_mono (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (d : InstId) (mid : Nat) (i n : Nat)
    (halive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st d).life = .alive)
    (hnorecv : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .recvBulk d)
    (hin : posOf mid (((ρ.cfg i).st d).parked.map (·.msg)) < ((ρ.cfg i).st d).parked.length) :
    posOf mid (((ρ.cfg (i + n)).st d).parked.map (·.msg)) =
        posOf mid (((ρ.cfg i).st d).parked.map (·.msg)) ∧
      posOf mid (((ρ.cfg (i + n)).st d).parked.map (·.msg)) <
        ((ρ.cfg (i + n)).st d).parked.length := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact ⟨rfl, hin⟩
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => halive t h1 (Nat.le_trans h2 (Nat.le_succ _)))
      (fun t h1 h2 => hnorecv t h1 (by omega))
    have hOcc := (inv2_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).2.1
    have hgrow := park_grow_step I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1))
      (ρ.valid (i + n)) hOcc d
      (hnorecv (i + n) (Nat.le_add_right i n) (by omega))
      (halive (i + n + 1) (by omega) (by omega))
    have hstep := pos_queue mid _ _ hgrow hprev.2
    exact ⟨hstep.1.trans hprev.1, hstep.2⟩

/-- A bulk receive that finds a parked head behind a nonempty box admits that
message at the end of the box. -/
theorem admit_park_box (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (m : Msg) (ms : List Msg) (p : Parked) (ps : List Parked)
    (hbox : (w.st id).box = m :: ms) (hpark : (w.st id).parked = p :: ps) :
    (w'.st id).box = ms ++ [p.msg] := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    simp [hbox, hpark] at h
    split at h
    · cases h
    · next w1 a1 hdel =>
      cases h
      have hd := deliver_box_of I w id _ m w1 a1 hdel
      let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
      have hcred := credit_box (setActor w1 id admitted) (tname id) m.sender id
      rw [setActor_self] at hcred
      have hres := set_resume_box (creditSender (setActor w1 id admitted) (tname id) m.sender)
        id p.sender p.isCall id
      rw [hres, hcred]
      simp [admitted, hd.1]

/-- A reliable parked message is later the bulk head. While it waits, only a
bulk receive removes the parked head; the head itself is either consumed or
admitted onto the box, which `box_mid_taken` then delivers. -/
theorem park_mid_taken (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (id : InstId) (mid : Nat) (i : Nat)
    (hterm : terminableB I.desc (tname id) = false)
    (hlive : ((ρ.cfg i).st id).life = .alive)
    (hpos : posOf mid (((ρ.cfg i).st id).parked.map (·.msg)) < ((ρ.cfg i).st id).parked.length) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) mid := by
  suffices ∀ n i, posOf mid (((ρ.cfg i).st id).parked.map (·.msg)) = n →
      posOf mid (((ρ.cfg i).st id).parked.map (·.msg)) < ((ρ.cfg i).st id).parked.length →
      ((ρ.cfg i).st id).life = .alive →
      ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) mid by
    exact this _ i rfl hpos hlive
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hpeq hlt hlive0
    have halive : ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive :=
      nonterm_stays ρ id i hlive0 hterm
    have hstill : ∀ t, i ≤ t → (∀ u, i ≤ u → u < t → ρ.act u ≠ .recvBulk id) →
        posOf mid (((ρ.cfg t).st id).parked.map (·.msg)) = n ∧
          posOf mid (((ρ.cfg t).st id).parked.map (·.msg)) < ((ρ.cfg t).st id).parked.length := by
      intro t ht hnorecv
      have hm := park_pos_mono I hL hG ρ id mid i (t - i)
        (fun u hu _ => halive u hu) (fun u hu hlt' => hnorecv u hu (by omega))
        (by simpa [hpeq] using hlt)
      have hsum : i + (t - i) = t := Nat.add_sub_of_le ht
      simpa [hsum, hpeq] using hm
    by_cases hex : ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id
    · obtain ⟨j0, hj0, hact0⟩ := hex
      have hscan := scanAct_spec ρ.act (.recvBulk id) (j0 - i) i
        ⟨j0 - i, Nat.le_refl _, by simpa [Nat.add_sub_of_le hj0] using hact0⟩
      let j := scanAct ρ.act (.recvBulk id) (j0 - i) i
      have hj : i ≤ j := hscan.1
      have hact : ρ.act j = .recvBulk id := hscan.2.1
      have hfirst : ∀ t, i ≤ t → t < j → ρ.act t ≠ .recvBulk id := hscan.2.2
      have hat := hstill j hj hfirst
      have hv := ρ.valid j
      simp [apply, hact] at hv
      cases hpark : ((ρ.cfg j).st id).parked with
      | nil => simp [hpark, posOf] at hat
      | cons p ps =>
        by_cases hp : p.msg.mid = mid
        · cases hbox : ((ρ.cfg j).st id).box with
          | nil =>
            refine ⟨j, hj, hact, ?_⟩
            simp [takenBulk, hbox, hpark, hp]
          | cons m ms =>
            have hbox' := admit_park_box I (ρ.cfg j) (ρ.cfg (j + 1)) id hv m ms p ps hbox hpark
            have hmem : p.msg ∈ ((ρ.cfg (j + 1)).st id).box := by
              rw [hbox']
              exact List.mem_append_right _ (by simp)
            have hposb := pos_mem mid _ p.msg hmem hp
            obtain ⟨k, hk, hactk, htaken⟩ := box_mid_taken I hL hG hA ρ hF id mid (j + 1) hterm
              (halive (j + 1) (Nat.le_trans hj (Nat.le_succ _))) hposb
            exact ⟨k, Nat.le_trans (Nat.le_trans hj (Nat.le_succ _)) hk, hactk, htaken⟩
        · have hgt : 0 < n := by
            have hposj : posOf mid (((ρ.cfg j).st id).parked.map (·.msg)) = n := hat.1
            simp [hpark, List.map_cons, posOf, hp] at hposj
            omega
          have hdrop := bulk_drops_head I (ρ.cfg j) (ρ.cfg (j + 1)) id hv p ps hpark
          have hdec := park_pos_drop mid p ps hp (by simpa [hpark] using hat.2)
          have hnext : posOf mid (((ρ.cfg (j + 1)).st id).parked.map (·.msg)) = n - 1 := by
            rw [hdrop]
            have hhead : posOf mid ((p :: ps).map (·.msg)) = n := by simpa [hpark] using hat.1
            rw [hdec.1, hhead]
          have hlt' : posOf mid (((ρ.cfg (j + 1)).st id).parked.map (·.msg)) <
              ((ρ.cfg (j + 1)).st id).parked.length := by
            rw [hdrop]
            simpa using hdec.2
          have hlive' : ((ρ.cfg (j + 1)).st id).life = .alive :=
            halive (j + 1) (Nat.le_trans hj (Nat.le_succ _))
          obtain ⟨k, hk, hactk, htaken⟩ :=
            ih (n - 1) (by omega) (j + 1) hnext hlt' hlive'
          exact ⟨k, Nat.le_trans hj (Nat.le_trans (Nat.le_succ _) hk), hactk, htaken⟩
    · have hnever : ∀ t, i ≤ t → ρ.act t ≠ .recvBulk id := by
        intro t ht hact
        exact hex ⟨t, ht, hact⟩
      have hfree : ∀ t, i ≤ t → ¬Stuck ρ id t := fun t ht hS =>
        never_stuck I hL hG hA ρ hF id t hS
          (Or.inl (permanent_finishable I.desc hG.peers id hterm))
      have hio : ∀ s, ∃ j, s ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk id) := by
        intro s
        obtain ⟨j, hj, hId⟩ := idle_when_free I hL hG hA ρ hF id i halive hfree
          (Nat.max s i) (Nat.le_max_right _ _)
        have hmail := hstill j (Nat.le_trans (Nat.le_max_right s i) hj)
          (fun u hu _ => hnever u hu)
        have hne : ((ρ.cfg j).st id).parked ≠ [] := by
          intro hempty
          simp [hempty, posOf] at hmail
        exact ⟨j, Nat.le_trans (Nat.le_max_left s i) hj,
          enabled_of_can I hL hG N (ρ.cfg j) (cfg_reachable ρ j) id ⟨hId, Or.inr hne⟩⟩
      obtain ⟨j, hj, hact⟩ := hF.bulk id hio i
      exact False.elim (hex ⟨j, hj, hact⟩)

/-- Appending keeps every earlier priority message at its index. -/
def LaneSuffix (old new : List Msg) : Prop :=
  ∃ extra, new = old ++ extra

theorem lane_refl (ms : List Msg) : LaneSuffix ms ms :=
  ⟨[], by simp⟩

theorem suffix_of_eq {a b : List Msg} (h : b = a) : LaneSuffix a b := by
  rw [h]
  exact lane_refl _

theorem lane_trans {a b c : List Msg} (h1 : LaneSuffix a b) (h2 : LaneSuffix b c) : LaneSuffix a c := by
  obtain ⟨e1, rfl⟩ := h1
  obtain ⟨e2, h⟩ := h2
  exact ⟨e1 ++ e2, by simp [h, List.append_assoc]⟩

theorem lane_pos (old new : List Msg) (mid : Nat) (h : LaneSuffix old new)
    (hin : posOf mid old < old.length) :
    posOf mid new = posOf mid old ∧ posOf mid new < new.length := by
  obtain ⟨extra, rfl⟩ := h
  rw [pos_append mid old extra hin, List.length_append]
  exact ⟨rfl, by omega⟩

theorem upsert_suffix (prio : List Msg) (m : Msg) : LaneSuffix prio (upsertPrio prio m) := by
  cases h : prio.any (fun p => p.label == m.label) <;> simp [upsertPrio, h]
  · exact ⟨[m], rfl⟩
  · exact lane_refl _

theorem tryWake_suffix (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) :
    LaneSuffix ((w.st i).prio) ((tryWake D w dstId label writer).st i).prio := by
  unfold tryWake
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [hif]
    by_cases hi : i = dstId
    · rw [hi, setActor_self]
      exact upsert_suffix _ _
    · rw [setActor_other _ dstId i _ hi]
      exact lane_refl _
  · simp [hif]
    exact lane_refl _

theorem wake_suffix (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer i : InstId) :
    LaneSuffix ((w.st i).prio)
      ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).prio := by
  induction ids generalizing w with
  | nil =>
    simp
    exact lane_refl _
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact lane_trans (tryWake_suffix D w j label writer i) (ih _)

theorem tryWake_dead_prio (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) (hdead : (w.st i).life ≠ .alive) :
    ((tryWake D w dstId label writer).st i).prio = (w.st i).prio := by
  unfold tryWake
  by_cases hi : i = dstId
  · rw [hi] at hdead ⊢
    cases hlife : (w.st dstId).life with
    | alive => exact absurd hlife hdead
    | dead =>
      have hff : ((w.st dstId).life == .alive) = false := by simp [hlife]
      simp [hff]
    | absent =>
      have hff : ((w.st dstId).life == .alive) = false := by simp [hlife]
      simp [hff]
  · by_cases hif : ((w.st dstId).life == .alive &&
        decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
        !((w.st dstId).prio.any fun p => p.label == label)) = true
    · simp [hif, setActor_other _ dstId i _ hi]
    · simp [hif]

theorem wake_dead_prio (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer i : InstId) (hdead : (w.st i).life ≠ .alive) (hempty : (w.st i).prio = []) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).prio = [] := by
  induction ids generalizing w with
  | nil => simpa using hempty
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact ih _ (by rw [try_wake_life]; exact hdead) (tryWake_dead_prio D w j label writer i hdead ▸ hempty)

theorem exec_keeps_dead_prio (I : Impl) (w : World) (id : InstId) (k : Cont) (i : InstId)
    (hdead : (w.st i).life ≠ .alive) (hne : i ≠ id) (hempty : (w.st i).prio = []) :
    ((execRun I w id (w.st id) k).st i).prio = [] := by
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil => simp [execRun, setActor, hne, hempty]
    | cons e tail =>
      cases e with
      | send dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed_prio, hempty]
        | some dstId =>
          simpa [hr, hempty] using enqueue_prio w I.desc id dstId
            { label := label, sender := id, callFrom := none } false
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) i
      | call dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed_prio, hempty]
        | some dstId =>
          simpa [hr, hempty] using enqueue_prio w I.desc id dstId
            { label := label, sender := id, callFrom := some id } true
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) i
      | trySend dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed_prio, hempty]
        | some dstId =>
          simp only [hr]
          split
          · simpa [hempty] using enqueue_prio w I.desc id dstId
              { label := label, sender := id, callFrom := none, reliable := false } false
              (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩) i
          · simp [setActor, hne, proceed_prio, hempty]
      | reply =>
        simpa [execRun, hempty] using reply_prio w id ⟨.reply :: tail, toState, replyTo⟩ i
      | internal => simp [execRun, setActor, hne, hempty]
      | peer => simp [execRun, setActor, hne, hempty]
      | selfSchedule label =>
        simp only [execRun]
        by_cases hany : ((w.st id).prio.any fun p => p.label == label) = true
        · simp [hany, setActor, hne, proceed_prio, hempty]
        · by_cases hlt : (w.st id).prio.length < capPrio I.desc w.N id
          · simp [hany, hlt, setActor, hne, proceed_prio, hempty]
          · simp [hany, hlt, setActor, hne, hempty]
      | cell dst label value =>
        simp only [execRun]
        cases hdirty : (w.cell dst label).dirty with
        | true => simp [hdirty, setCell, setActor, hne, proceed_prio, hempty]
        | false =>
          simp [hdirty, setCell, setActor, wakeReaders, hne]
          refine wake_dead_prio I.desc (readersOf _ dst) _ label id i ?_ ?_
          · simp [setCell, setActor, hne, proceed_life, hdead]
          · simp [setCell, setActor, hne, proceed_prio, hempty]
      | terminate =>
        simp only [execRun]
        cases htpl : templateOf I.desc (tname id) with
        | none => simp [htpl, hempty]
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill, readCells_st, refund_prio, refundP_prio, setActor, hne, release_prio, hempty]
          · simp [htpl, hkill, hempty]

/-- A non-alive actor with an empty priority lane does not acquire one. -/
theorem no_prio_gain_dead (I : Impl) (a : Action) (w w' : World) (id : InstId)
    (h : apply I a w = some w') (hdead : (w.st id).life ≠ .alive)
    (hempty : (w.st id).prio = []) : (w'.st id).prio = [] := by
  cases a with
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hempty
  | ingress who label =>
    simpa [hempty] using (ingress_phase I w w' who label id (by simpa [apply] using h)).2.2.1
  | finish j => simpa [hempty] using finish_prio I w w' j id (by simpa [apply] using h)
  | recvBulk j => simpa [hempty] using bulk_prio_eq I w w' j id (by simpa [apply] using h)
  | recvPrio j =>
    have hrec : receivePrio I w j = some w' := by simpa [apply] using h
    have halive := (prio_ready I w j w' hrec).1
    by_cases hji : id = j
    · exact absurd (hji ▸ halive) hdead
    · unfold receivePrio at hrec
      cases hp : (w.st j).prio with
      | nil => simp [hp] at hrec
      | cons m ms =>
        simp [hp] at hrec
        split at hrec
        · simp at hrec
        · next w1 a1 hdel =>
          rcases hrec with ⟨_, hw⟩
          injection hw with hw
          have hst := deliver_st I w j ({ (w.st j) with prio := ms }) m w1 a1 id hdel
          rw [← hw, setActor_other w1 j id a1 hji, hst]
          exact hempty
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        simp only [readCells_st]
        by_cases hi : id = InstId.peer template (w.nextIx template)
        · simp [setActor, hi, withTokens]
        · simpa [setActor, hi] using hempty
      · cases h
  | exec j =>
    by_cases hji : id = j
    · rw [hji] at hdead
      simp only [apply] at h
      unfold execHead at h
      simp [hdead] at h
    · simp only [apply] at h
      unfold execHead at h
      by_cases hlj : (w.st j).life = .alive
      · simp [hlj] at h
        cases hph : (w.st j).phase with
        | run k =>
          simp [hph] at h
          cases h
          exact exec_keeps_dead_prio I w j k id hdead hji hempty
        | idle => simp [hph] at h
        | parked _ _ _ => simp [hph] at h
        | awaitReply _ _ => simp [hph] at h
        | awaitEffect _ => simp [hph] at h
        | awaitPeer _ => simp [hph] at h
        | crashed => simp [hph] at h
      · simp [hlj] at h

/-- A non-terminable actor that still holds priority mail is alive. -/
theorem prio_permanent_alive (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) (id : InstId)
    (hterm : terminableB I.desc (tname id) = false) (hne : (w.st id).prio ≠ []) :
    (w.st id).life = .alive := by
  induction hR generalizing id with
  | init => exact absurd (init_prio_empty I N id) hne
  | step w w' a prev ha ih =>
    by_cases hpre : (w.st id).life = .alive
    · by_cases hlive : (w'.st id).life = .alive
      · exact hlive
      · obtain ⟨_, _, _, _, _, _, ht, hflag⟩ := only_terminate_kills I a w w' id ha hpre hlive
        simp [Bool.and_eq_true] at hflag
        simp [terminableB, ht, hflag.1] at hterm
    · have hempty : (w.st id).prio = [] := by
        by_cases hp : (w.st id).prio = []
        · exact hp
        · exact absurd (ih id hterm hp) hpre
      exact absurd (no_prio_gain_dead I a w w' id ha hpre hempty) hne

theorem exec_prio_suffix (I : Impl) (w : World) (id : InstId) (k : Cont) (mb : InstId)
    (hlive : ((execRun I w id (w.st id) k).st mb).life = .alive) :
    LaneSuffix ((w.st mb).prio) ((execRun I w id (w.st id) k).st mb).prio := by
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil =>
      exact suffix_of_eq (by
        by_cases hmb : mb = id
        · rw [hmb]; simp [execRun, setActor]
        · simp [execRun, setActor, hmb])
    | cons e tail =>
      cases e with
      | send dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          exact suffix_of_eq (by
            simp [hr]
            by_cases hmb : mb = id
            · rw [hmb]; simp [setActor, proceed_prio]
            · simp [setActor, hmb, proceed_prio])
        | some dstId =>
          exact suffix_of_eq (by
            simpa [hr] using enqueue_prio w I.desc id dstId
              { label := label, sender := id, callFrom := none } false
              (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) mb)
      | call dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          exact suffix_of_eq (by
            simp [hr]
            by_cases hmb : mb = id
            · rw [hmb]; simp [setActor, proceed_prio]
            · simp [setActor, hmb, proceed_prio])
        | some dstId =>
          exact suffix_of_eq (by
            simpa [hr] using enqueue_prio w I.desc id dstId
              { label := label, sender := id, callFrom := some id } true
              (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) mb)
      | trySend dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          exact suffix_of_eq (by
            simp [hr]
            by_cases hmb : mb = id
            · rw [hmb]; simp [setActor, proceed_prio]
            · simp [setActor, hmb, proceed_prio])
        | some dstId =>
          simp only [hr]
          split
          · exact suffix_of_eq (enqueue_prio w I.desc id dstId
              { label := label, sender := id, callFrom := none, reliable := false } false
              (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩) mb)
          · exact suffix_of_eq (by
              by_cases hmb : mb = id
              · rw [hmb]; simp [setActor, proceed_prio]
              · simp [setActor, hmb, proceed_prio])
      | reply =>
        exact suffix_of_eq (by simpa [execRun] using reply_prio w id ⟨.reply :: tail, toState, replyTo⟩ mb)
      | internal =>
        exact suffix_of_eq (by
          simp [execRun]
          by_cases hmb : mb = id
          · rw [hmb]; simp [setActor]
          · simp [setActor, hmb])
      | peer =>
        exact suffix_of_eq (by
          simp [execRun]
          by_cases hmb : mb = id
          · rw [hmb]; simp [setActor]
          · simp [setActor, hmb])
      | selfSchedule label =>
        simp only [execRun]
        by_cases hany : ((w.st id).prio.any fun p => p.label == label) = true
        · have hsame : ((setActor w id (proceed (w.st id)
              (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩))).st mb).prio =
              (w.st mb).prio := by
            by_cases hmb : mb = id
            · rw [hmb, setActor_self, proceed_prio]
            · rw [setActor_other _ id mb _ hmb]
          simpa [hany] using suffix_of_eq hsame
        · by_cases hlt : (w.st id).prio.length < capPrio I.desc w.N id
          · let grown : Actor :=
              { (w.st id) with
                prio := upsertPrio (w.st id).prio
                  { label := label, sender := id, callFrom := none, reliable := true,
                    mid := (w.st id).nextMid },
                nextMid := (w.st id).nextMid + 1 }
            have hsuf : LaneSuffix ((w.st mb).prio)
                ((setActor w id (proceed grown
                  (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩))).st mb).prio := by
              by_cases hmb : mb = id
              · rw [hmb, setActor_self, proceed_prio]
                exact upsert_suffix _ _
              · rw [setActor_other _ id mb _ hmb]
                exact lane_refl _
            simpa [hany, hlt, grown] using hsuf
          · let crashed : Actor := { (w.st id) with phase := .crashed }
            have hsame : ((setActor w id crashed).st mb).prio = (w.st mb).prio := by
              by_cases hmb : mb = id
              · rw [hmb, setActor_self]
              · rw [setActor_other _ id mb _ hmb]
            simpa [hany, hlt, crashed] using suffix_of_eq hsame
      | cell dst label value =>
        simp only [execRun]
        cases hdirty : (w.cell dst label).dirty with
        | true =>
          exact suffix_of_eq (by
            simp [hdirty, setCell]
            by_cases hmb : mb = id
            · rw [hmb, setActor_self, proceed_prio]
            · simp [setActor, hmb, proceed_prio])
        | false =>
          simp [hdirty, setCell, wakeReaders]
          refine lane_trans ?_ (wake_suffix I.desc (readersOf _ dst) _ label id mb)
          exact suffix_of_eq (by
            by_cases hmb : mb = id
            · rw [hmb, setActor_self, proceed_prio]
            · simp [setActor, setCell, hmb, proceed_prio])
      | terminate =>
        simp only [execRun]
        cases htpl : templateOf I.desc (tname id) with
        | none => exact suffix_of_eq (by simp [htpl])
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill]
            by_cases hmb : mb = id
            · exfalso
              rw [hmb] at hlive
              simp [execRun, htpl, hkill] at hlive
              rw [release_life_self] at hlive
              simp [setActor] at hlive
            · exact suffix_of_eq (by
                simp [readCells_st, refund_prio, refundP_prio, setActor, hmb, release_prio])
          · exact suffix_of_eq (by simp [htpl, hkill])

theorem prio_suffix_step (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hOcc : OccInv I w) (d : InstId) (hpre : (w.st d).life = .alive) (hnot : a ≠ .recvPrio d)
    (halive : (w'.st d).life = .alive) :
    LaneSuffix ((w.st d).prio) ((w'.st d).prio) := by
  cases a with
  | stutter =>
    cases stutter_unchanged I w w' h
    exact lane_refl _
  | ingress who label =>
    exact suffix_of_eq (ingress_phase I w w' who label d (by simpa [apply] using h)).2.2.1
  | recvBulk id =>
    exact suffix_of_eq (bulk_prio_eq I w w' id d (by simpa [apply] using h))
  | recvPrio id =>
    have hid : id ≠ d := by
      intro heq
      exact hnot (by simp [heq])
    have hrec : receivePrio I w id = some w' := by simpa [apply] using h
    unfold receivePrio at hrec
    cases hp : (w.st id).prio with
    | nil => simp [hp] at hrec
    | cons m ms =>
      simp [hp] at hrec
      split at hrec
      · simp at hrec
      · next w1 a1 hdel =>
        rcases hrec with ⟨_, hw⟩
        injection hw with hw
        have hst := deliver_st I w id ({ (w.st id) with prio := ms }) m w1 a1 d hdel
        exact suffix_of_eq (by rw [← hw, setActor_other w1 id d a1 hid.symm, hst])
  | finish id =>
    exact suffix_of_eq (finish_prio I w w' id d (by simpa [apply] using h))
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hrun : (w.st id).life = .alive
    · simp [hrun] at h
      cases hphase : (w.st id).phase with
      | run k =>
        simp [hphase] at h
        cases h
        exact exec_prio_suffix I w id k d halive
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hrun] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        have hnin : nid ∉ w.roster := by
          intro hmem
          have hix := hOcc.indexed template (w.nextIx template) hmem
          omega
        have hmem := hOcc.aliveIn d hpre
        have hne : d ≠ nid := by
          intro hd
          exact hnin (by simpa [hd] using hmem)
        let wR : World := { w with roster := w.roster ++ [nid], nextIx := fun n =>
          if n = template then w.nextIx n + 1 else w.nextIx n }
        let born : Actor := withTokens I.desc template
          { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [],
            parked := [], tokens := fun _ => 0 }
        have hs := readCells_st I.desc (setActor wR nid born) nid d
        rw [hs]
        simp [wR, setActor, hne]
        exact lane_refl _
      · cases h

theorem prio_pos_mono (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (d : InstId) (mid : Nat) (i n : Nat)
    (halive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st d).life = .alive)
    (hnorecv : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .recvPrio d)
    (hin : posOf mid ((ρ.cfg i).st d).prio < ((ρ.cfg i).st d).prio.length) :
    posOf mid ((ρ.cfg (i + n)).st d).prio = posOf mid ((ρ.cfg i).st d).prio ∧
      posOf mid ((ρ.cfg (i + n)).st d).prio < ((ρ.cfg (i + n)).st d).prio.length := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact ⟨rfl, hin⟩
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => halive t h1 (Nat.le_trans h2 (Nat.le_succ _)))
      (fun t h1 h2 => hnorecv t h1 (by omega))
    have hOcc := (inv2_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).2.1
    have hgrow := prio_suffix_step I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1))
      (ρ.valid (i + n)) hOcc d
      (halive (i + n) (by omega) (by omega))
      (hnorecv (i + n) (Nat.le_add_right i n) (by omega))
      (halive (i + n + 1) (by omega) (by omega))
    have hstep := lane_pos _ _ mid hgrow hprev.2
    exact ⟨hstep.1.trans hprev.1, hstep.2⟩

/-- A reliable priority message reaches the head and is received. A cell wake is
not reliable, so it is not an instance of this obligation. -/
theorem prio_mid_taken (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (id : InstId) (mid : Nat) (i : Nat)
    (hterm : terminableB I.desc (tname id) = false)
    (hlive : ((ρ.cfg i).st id).life = .alive)
    (hpos : posOf mid ((ρ.cfg i).st id).prio < ((ρ.cfg i).st id).prio.length) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvPrio id ∧ takenPrio ((ρ.cfg j).st id) mid := by
  suffices ∀ n i, posOf mid ((ρ.cfg i).st id).prio = n →
      posOf mid ((ρ.cfg i).st id).prio < ((ρ.cfg i).st id).prio.length →
      ((ρ.cfg i).st id).life = .alive →
      ∃ j, i ≤ j ∧ ρ.act j = .recvPrio id ∧ takenPrio ((ρ.cfg j).st id) mid by
    exact this _ i rfl hpos hlive
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hpeq hlt hlive0
    have halive : ∀ t, i ≤ t → ((ρ.cfg t).st id).life = .alive :=
      nonterm_stays ρ id i hlive0 hterm
    have hstill : ∀ t, i ≤ t → (∀ u, i ≤ u → u < t → ρ.act u ≠ .recvPrio id) →
        posOf mid ((ρ.cfg t).st id).prio = n ∧
          posOf mid ((ρ.cfg t).st id).prio < ((ρ.cfg t).st id).prio.length := by
      intro t ht hnorecv
      have hm := prio_pos_mono I hL hG ρ id mid i (t - i)
        (fun u hu _ => halive u hu) (fun u hu hlt' => hnorecv u hu (by omega))
        (by simpa [hpeq] using hlt)
      have hsum : i + (t - i) = t := Nat.add_sub_of_le ht
      simpa [hsum, hpeq] using hm
    by_cases hex : ∃ j, i ≤ j ∧ ρ.act j = .recvPrio id
    · obtain ⟨j0, hj0, hact0⟩ := hex
      have hscan := scanAct_spec ρ.act (.recvPrio id) (j0 - i) i
        ⟨j0 - i, Nat.le_refl _, by simpa [Nat.add_sub_of_le hj0] using hact0⟩
      let j := scanAct ρ.act (.recvPrio id) (j0 - i) i
      have hj : i ≤ j := hscan.1
      have hact : ρ.act j = .recvPrio id := hscan.2.1
      have hfirst : ∀ t, i ≤ t → t < j → ρ.act t ≠ .recvPrio id := hscan.2.2
      have hat := hstill j hj hfirst
      have hv := ρ.valid j
      simp [apply, hact] at hv
      cases hp : ((ρ.cfg j).st id).prio with
      | nil => simp [hp, posOf] at hat
      | cons m ms =>
        by_cases hm : m.mid = mid
        · refine ⟨j, hj, hact, ?_⟩
          simp [takenPrio, hp, hm]
        · have hgt : 0 < n := by
            have hposj : posOf mid ((ρ.cfg j).st id).prio = n := hat.1
            simp [hp, posOf, hm] at hposj
            omega
          have htail := (prio_recv_tail I (ρ.cfg j) (ρ.cfg (j + 1)) id hv).1
          have hnew : ((ρ.cfg (j + 1)).st id).prio = ms := by simpa [hp] using htail
          have hdec := pos_drop mid m ms ((ρ.cfg (j + 1)).st id).prio hm
            (by simpa [hp] using hat.2) (Or.inl hnew)
          have hnext : posOf mid ((ρ.cfg (j + 1)).st id).prio = n - 1 := by
            have hhead : posOf mid (m :: ms) = n := by simpa [hp] using hat.1
            rw [hdec.1, hhead]
          have hlt' := hdec.2
          have hlive' : ((ρ.cfg (j + 1)).st id).life = .alive :=
            halive (j + 1) (Nat.le_trans hj (Nat.le_succ _))
          obtain ⟨k, hk, hactk, htaken⟩ :=
            ih (n - 1) (by omega) (j + 1) hnext hlt' hlive'
          exact ⟨k, Nat.le_trans hj (Nat.le_trans (Nat.le_succ _) hk), hactk, htaken⟩
    · have hnever : ∀ t, i ≤ t → ρ.act t ≠ .recvPrio id := by
        intro t ht hact
        exact hex ⟨t, ht, hact⟩
      have hfree : ∀ t, i ≤ t → ¬Stuck ρ id t := fun t ht hS =>
        never_stuck I hL hG hA ρ hF id t hS
          (Or.inl (permanent_finishable I.desc hG.peers id hterm))
      have hio : ∀ s, ∃ j, s ≤ j ∧ Enabled I (ρ.cfg j) (.recvPrio id) := by
        intro s
        obtain ⟨j, hj, hId⟩ := idle_when_free I hL hG hA ρ hF id i halive hfree
          (Nat.max s i) (Nat.le_max_right _ _)
        have hmail := hstill j (Nat.le_trans (Nat.le_max_right s i) hj)
          (fun u hu _ => hnever u hu)
        cases hp : ((ρ.cfg j).st id).prio with
        | nil => simp [hp, posOf] at hmail
        | cons m ms =>
          exact ⟨j, Nat.le_trans (Nat.le_max_left s i) hj,
            recv_prio_enabled I (ρ.cfg j) id m.label
              (call_tag_reachable I hL hG N (ρ.cfg j) (cfg_reachable ρ j))
              hId.1 hId.2 ⟨m, by simp [hp], rfl⟩⟩
      obtain ⟨j, hj, hact⟩ := hF.prio id hio i
      exact False.elim (hex ⟨j, hj, hact⟩)

theorem box_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId) (m : Msg)
    (hm : m ∈ ((ρ.cfg i).st id).box) (hr : m.reliable = true) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) m.mid := by
  have hR := cfg_reachable ρ i
  have hterm := reliable_permanent I hL hG N (ρ.cfg i) hR id (by
    intro hf
    have hbad := hf.1 m hm
    simp [hr] at hbad)
  have hlive := mail_alive I N (ρ.cfg i) hR id (by intro hempty; simp [hempty] at hm)
  have hpos := pos_mem m.mid _ m hm rfl
  exact box_mid_taken I hL hG hA ρ hF id m.mid i hterm hlive hpos

theorem park_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId) (p : Parked)
    (hp : p ∈ ((ρ.cfg i).st id).parked) (hr : p.msg.reliable = true) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk id ∧ takenBulk ((ρ.cfg j).st id) p.msg.mid := by
  have hR := cfg_reachable ρ i
  have hterm := reliable_permanent I hL hG N (ρ.cfg i) hR id (by
    intro hf
    have hbad := hf.2.1 p hp
    simp [hr] at hbad)
  have hlive := mailbox_alive I hL N (ρ.cfg i) hR id (by intro hempty; simp [hempty] at hp)
  have hpos := pos_mem p.msg.mid _ p.msg (by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩) rfl
  have hpos' : posOf p.msg.mid (((ρ.cfg i).st id).parked.map (·.msg)) <
      ((ρ.cfg i).st id).parked.length := by simpa using hpos
  exact park_mid_taken I hL hG hA ρ hF id p.msg.mid i hterm hlive hpos'

theorem prio_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (i : Nat) (id : InstId) (m : Msg)
    (hm : m ∈ ((ρ.cfg i).st id).prio) (hr : m.reliable = true) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvPrio id ∧ takenPrio ((ρ.cfg j).st id) m.mid := by
  have hR := cfg_reachable ρ i
  have hterm := reliable_permanent I hL hG N (ρ.cfg i) hR id (by
    intro hf
    have hbad := hf.2.2 m hm
    simp [hr] at hbad)
  have hlive := prio_permanent_alive I N (ρ.cfg i) hR id hterm (by intro hempty; simp [hempty] at hm)
  have hpos := pos_mem m.mid _ m hm rfl
  exact prio_mid_taken I hL hG hA ρ hF id m.mid i hterm hlive hpos

/-- A fair run of a checked graph delivers every reliable message, matched by the
id of the actor that accepted it, and every admitted call leaves `awaitReply`.
`Assumptions` is only `rust_refines`. -/
theorem fair_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) : Delivered ρ :=
  ⟨fun i id m hm hr => box_delivered I hL hG hA ρ hF i id m hm hr,
   fun i id p hp hr => park_delivered I hL hG hA ρ hF i id p hp hr,
   fun i id m hm hr => prio_delivered I hL hG hA ρ hF i id m hm hr,
   fun i c d k hph => call_answered I hL hG hA ρ hF i c d k hph⟩

end Deadlock
