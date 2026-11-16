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
