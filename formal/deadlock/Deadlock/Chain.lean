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
import Deadlock.Witness

set_option autoImplicit false

namespace Deadlock

/-- Longest transition program. Every continuation in a reachable world is a
suffix of one of these, so `work` is bounded by it. -/
def progBound (I : Impl) : Nat :=
  I.transitions.foldl (fun n tr => max n tr.program.length) 0

theorem fold_ge (acc : Nat) (ts : List Transition) :
    acc ≤ ts.foldl (fun n t => max n t.program.length) acc := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp [List.foldl]
    exact Nat.le_trans (Nat.le_max_left acc t.program.length) (ih (max acc t.program.length))

theorem progBound_mem (I : Impl) (tr : Transition) (h : tr ∈ I.transitions) :
    tr.program.length ≤ progBound I := by
  have hgo : ∀ acc (ts : List Transition), tr ∈ ts →
      tr.program.length ≤ ts.foldl (fun n t => max n t.program.length) acc := by
    intro acc ts hm
    induction ts generalizing acc with
    | nil => cases hm
    | cons t ts ih =>
      cases hm with
      | head =>
        simp [List.foldl]
        exact Nat.le_trans (Nat.le_max_right acc tr.program.length) (fold_ge _ ts)
      | tail _ ht =>
        simp [List.foldl]
        exact ih _ ht
  exact hgo 0 I.transitions h

/-- Strictly larger than `work` of any reachable actor. -/
def slotOf (I : Impl) : Nat := 2 * progBound I + 3

/-- One more than `phaseFuel` on a running actor, and one more than a wait, so
leaving a wait or emptying a program both decrease it. Idle is `0`. -/
def work (ph : Phase) : Nat :=
  match ph with
  | .idle | .crashed => 0
  | .run k => phaseFuel (.run k) + 1
  | .parked dst c k => phaseFuel (.parked dst c k) + 1
  | .awaitReply dst k => phaseFuel (.awaitReply dst k) + 1
  | .awaitEffect k => phaseFuel (.awaitEffect k) + 1
  | .awaitPeer k => phaseFuel (.awaitPeer k) + 1

theorem work_proceed (a : Actor) (dst : InstId) (c : Bool) (k : Cont) :
    work (proceed a k).phase < work (.parked dst c k) := by
  cases hk : k.rest <;> simp [proceed, work, phaseFuel, hk]

theorem work_proceed_effect (a : Actor) (k : Cont) :
    work (proceed a k).phase < work (.awaitEffect k) := by
  cases hk : k.rest <;> simp [proceed, work, phaseFuel, hk]

theorem work_proceed_peer (a : Actor) (k : Cont) :
    work (proceed a k).phase < work (.awaitPeer k) := by
  cases hk : k.rest <;> simp [proceed, work, phaseFuel, hk]

theorem work_proceed_reply (a : Actor) (dst : InstId) (k : Cont) :
    work (proceed a k).phase < work (.awaitReply dst k) := by
  cases hk : k.rest <;> simp [proceed, work, phaseFuel, hk]

theorem suffix_le {α : Type} (pre es : List α) (prog : List α) (h : pre ++ es = prog) :
    es.length ≤ prog.length := by
  have hlen := congrArg List.length h
  simp [List.length_append] at hlen
  omega

theorem phase_le (I : Impl) (w : World) (hS : ProgSrc I w) (id : InstId) :
    phaseFuel ((w.st id).phase) ≤ 2 * progBound I + 1 := by
  cases hph : (w.st id).phase with
  | idle => simp [phaseFuel, hph]
  | crashed => simp [phaseFuel, hph]
  | run k =>
    obtain ⟨tr, hm, _, pre, happ⟩ := hS id k.rest (by simp [carried, hph])
    have hlen := suffix_le pre k.rest tr.program happ
    have htr := progBound_mem I tr hm
    simp [phaseFuel, hph]
    omega
  | parked _ _ k =>
    obtain ⟨tr, hm, _, pre, happ⟩ := hS id k.rest (by simp [carried, hph])
    have hlen := suffix_le pre k.rest tr.program happ
    have htr := progBound_mem I tr hm
    simp [phaseFuel, hph]
    omega
  | awaitReply _ k =>
    obtain ⟨tr, hm, _, pre, happ⟩ := hS id k.rest (by simp [carried, hph])
    have hlen := suffix_le pre k.rest tr.program happ
    have htr := progBound_mem I tr hm
    simp [phaseFuel, hph]
    omega
  | awaitEffect k =>
    obtain ⟨tr, hm, _, pre, happ⟩ := hS id k.rest (by simp [carried, hph])
    have hlen := suffix_le pre k.rest tr.program happ
    have htr := progBound_mem I tr hm
    simp [phaseFuel, hph]
    omega
  | awaitPeer k =>
    obtain ⟨tr, hm, _, pre, happ⟩ := hS id k.rest (by simp [carried, hph])
    have hlen := suffix_le pre k.rest tr.program happ
    have htr := progBound_mem I tr hm
    simp [phaseFuel, hph]
    omega

theorem work_slot (I : Impl) (w : World) (hS : ProgSrc I w) (id : InstId) :
    work ((w.st id).phase) + 1 ≤ slotOf I := by
  have hpf := phase_le I w hS id
  cases hph : (w.st id).phase <;> simp [work, slotOf, hph] at hpf ⊢ <;> omega

theorem work_exec (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id : InstId) (k : Cont)
    (hph : (w.st id).phase = .run k) (hl : (w.st id).life = .alive)
    (w' : World) (h : execHead I w id = some w') :
    work ((w'.st id).phase) < work ((w.st id).phase) := by
  cases hrest : k.rest with
  | nil =>
    simp [execHead, execRun, hph, hl, hrest] at h
    cases h
    simp [work, phaseFuel, setActor_self, hph]
  | cons _ _ =>
    have hdrop := exec_drops I hL hG N w hR id k hph hl (by simp [hrest])
    have hw : w' = execRun I w id (w.st id) k := by
      simp [execHead, hph, hl] at h
      exact h.symm
    rw [hw]
    have hfuel : phaseFuel ((execRun I w id (w.st id) k).st id).phase <
        phaseFuel ((w.st id).phase) := hdrop
    cases hph' : ((execRun I w id (w.st id) k).st id).phase <;>
      simp [work, hph, hph'] at hfuel ⊢ <;> omega

/-- Where the awaited call sits in the callee's box. `0` once it has been dequeued. -/
def queuePos (w : World) (c d : InstId) : Nat :=
  let box := (w.st d).box
  if callPos box c < box.length then callPos box c + 1 else 0

/-- Messages ahead of a parked sender, then the partner's remaining program. -/
def sendDebt (I : Impl) (w : World) (id dst : InstId) : Nat :=
  parkIndex ((w.st dst).parked) id * slotOf I + work ((w.st dst).phase)

/-- A parked call still has to be admitted before the reply, so it sits strictly
above the `awaitReply` debt of the same partner state. -/
def callParkDebt (I : Impl) (w : World) (id dst : InstId) : Nat :=
  (parkIndex ((w.st dst).parked) id + 1) * slotOf I + work ((w.st dst).phase)

def replyDebt (I : Impl) (w : World) (id dst : InstId) : Nat :=
  queuePos w id dst * slotOf I + work ((w.st dst).phase)

def waitDebt (I : Impl) (w : World) (id : InstId) : Nat :=
  match (w.st id).phase with
  | .parked dst false _ => sendDebt I w id dst
  | .parked dst true _ => callParkDebt I w id dst
  | .awaitReply dst _ => replyDebt I w id dst
  | _ => 0

theorem chain_run (I : Impl) (root : InstId) (w : World) (acts : List Action)
    (h : ChainRun I root w acts) : ∃ w', runFrom I (some w) acts = some w' := by
  induction h with
  | nil w => exact ⟨w, rfl⟩
  | cons w a w' as _ hA _ ih =>
    obtain ⟨w'', hr⟩ := ih
    simp [runFrom, hA, hr]

theorem run_determ (I : Impl) (w0 : World) (acts : List Action) (w1 w2 : World)
    (h1 : runFrom I (some w0) acts = some w1) (h2 : runFrom I (some w0) acts = some w2) :
    w1 = w2 := by
  rw [h1] at h2
  cases h2
  rfl

theorem chain_append (I : Impl) (root : InstId) (w : World) (acts1 : List Action) (w1 : World)
    (acts2 : List Action) (h1 : ChainRun I root w acts1)
    (hrun : runFrom I (some w) acts1 = some w1) (h2 : ChainRun I root w1 acts2) :
    ChainRun I root w (acts1 ++ acts2) := by
  induction h1 with
  | nil w =>
    simp [runFrom] at hrun
    cases hrun
    simpa using h2
  | cons w a w' as hC hA hRest ih =>
    simp [runFrom, hA] at hrun
    exact ChainRun.cons w a w' (as ++ acts2) hC hA (ih hrun)

theorem finish_unblocks (I : Impl) (w w' : World) (id : InstId)
    (h : finishWait I w id = some w') (hB : Blocked w id) : ¬ Blocked w' id ∧
      work ((w'.st id).phase) < work ((w.st id).phase) := by
  obtain ⟨k, hph, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  refine ⟨?_, ?_⟩
  · intro hB'
    have hph' : ((setActor w id (proceed (w.st id) k)).st id).phase = (proceed (w.st id) k).phase := by
      simp [setActor_self]
    cases hk : k.rest with
    | nil =>
      simp [Blocked, setActor_self, proceed, hk] at hB'
    | cons _ _ =>
      simp [Blocked, setActor_self, proceed, hk] at hB'
  · rcases hph with hph | hph
    · have hwk : work ((w.st id).phase) = work (.awaitEffect k) := by simp [hph]
      rw [hwk]
      simpa [setActor_self] using work_proceed_effect (w.st id) k
    · have hwk : work ((w.st id).phase) = work (.awaitPeer k) := by simp [hph]
      rw [hwk]
      simpa [setActor_self] using work_proceed_peer (w.st id) k

/-- While `root` stays parked on `dst`, every step of `dst`'s chain is on `root`'s
chain. The list stops at the step that runs `root`'s continuation. If `root` is
still parked at the end, the parked index has not grown. -/
theorem absorb_send (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (dst root : InstId) (k : Cont) (w : World) (acts : List Action)
    (hC : ChainRun I dst w acts) (hR : Reachable I N w)
    (hph : (w.st root).phase = .parked dst false k) :
    ∃ acts1 w1, ChainRun I root w acts1 ∧ runFrom I (some w) acts1 = some w1 ∧
      Reachable I N w1 ∧
      (¬ Blocked w1 root ∧ work ((w1.st root).phase) < work ((w.st root).phase) ∨
        runFrom I (some w) acts = some w1 ∧ (w1.st root).phase = .parked dst false k ∧
          parkIndex ((w1.st dst).parked) root ≤ parkIndex ((w.st dst).parked) root ∧
          (w1.st root).typestate = (w.st root).typestate) := by
  induction hC with
  | nil w =>
    exact ⟨[], w, ChainRun.nil w, rfl, hR, Or.inr ⟨rfl, hph, Nat.le_refl _, rfl⟩⟩
  | cons w a w' as hOn hA hRest ih =>
    have hInv := inv_reachable I N w hL hR
    have hnext := blocking_next I a w w' root dst k hInv.2.1 hInv.2.2 hA hph
    have hlift := on_partner w root dst a (waits_on_park w root dst false k hph) hOn
    rcases hnext with hstay | hgo
    · have hR' := Reachable.step w w' a hR hA
      have hlive := park_target_alive I hL hG N w hR root dst false k hph
      have hlive' := park_target_alive I hL hG N w' hR' root dst false k hstay
      obtain ⟨p, hp, hsender, _⟩ := hInv.2.1.bwd root dst false k hph
      have hin : parkIndex ((w.st dst).parked) root < ((w.st dst).parked).length :=
        parkIndex_of_mem _ root ⟨p, hp, hsender⟩
      have hidx := (step_index I a w w' hA hInv.2.2 root dst false k k hph hstay hlive hlive' hin).1
      have hidx' : parkIndex ((w'.st dst).parked) root ≤ parkIndex ((w.st dst).parked) root := hidx
      obtain ⟨acts1, w1, hC1, hrun1, hR1, hor⟩ := ih hR' hstay
      rcases hor with hdone | hfull
      · refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1, Or.inl ?_⟩
        · simp [runFrom, hA, hrun1]
        · have hwk : work ((w'.st root).phase) = work ((w.st root).phase) := by simp [hstay, hph]
          rcases hdone with ⟨hnot, hlt⟩
          exact ⟨hnot, Nat.lt_of_lt_of_eq hlt hwk⟩
      · rcases hfull with ⟨hrest, hph1, hle, hty1⟩
        have hty := waiting_ty_step I a w w' root hA
          (Or.inl ⟨dst, false, k, hph⟩) (Or.inl ⟨dst, false, k, hstay⟩)
        refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1, Or.inr ⟨?_, hph1, ?_, ?_⟩⟩
        · simp [runFrom, hA, hrun1]
        · simp [runFrom, hA, hrest]
        · exact Nat.le_trans hle hidx'
        · exact hty1.trans hty
    · have hnot : ¬ Blocked w' root := by
        intro hB
        simp [Blocked, hgo] at hB
        cases hk : k.rest <;> simp [proceed, hk] at hB
      have hwk : work ((w'.st root).phase) < work ((w.st root).phase) := by
        have heq : work ((w'.st root).phase) = work (proceed (w.st root) k).phase := by simp [hgo]
        rw [heq]
        have hsrc : work ((w.st root).phase) = work (.parked dst false k) := by simp [hph]
        rw [hsrc]
        exact work_proceed (w.st root) dst false k
      refine ⟨[a], w', ChainRun.cons w a w' [] hlift hA (ChainRun.nil w'), ?_,
        Reachable.step w w' a hR hA, Or.inl ⟨hnot, hwk⟩⟩
      · simp [runFrom, hA]

theorem debt_index (slot idx workNow : Nat) (hslot : workNow + 1 ≤ slot) :
    idx * slot + workNow < (idx + 1) * slot := by
  rw [Nat.succ_mul]
  exact Nat.add_lt_add_left (Nat.lt_of_succ_le hslot) (idx * slot)

theorem send_debt_drop_index (I : Impl) (w w' : World) (id dst : InstId)
    (hS : ProgSrc I w') (hidx : parkIndex ((w'.st dst).parked) id + 1 = parkIndex ((w.st dst).parked) id) :
    sendDebt I w' id dst < sendDebt I w id dst := by
  have hw := work_slot I w' hS dst
  unfold sendDebt
  have hidx' : parkIndex ((w.st dst).parked) id = parkIndex ((w'.st dst).parked) id + 1 := hidx.symm
  rw [hidx']
  exact Nat.lt_of_lt_of_le
    (debt_index (slotOf I) (parkIndex ((w'.st dst).parked) id) (work ((w'.st dst).phase)) hw)
    (Nat.le_add_right _ (work ((w.st dst).phase)))

theorem send_debt_drop_work (I : Impl) (w w' : World) (id dst : InstId)
    (hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id)
    (hwork : work ((w'.st dst).phase) < work ((w.st dst).phase)) :
    sendDebt I w' id dst < sendDebt I w id dst := by
  unfold sendDebt
  have hmul : parkIndex ((w'.st dst).parked) id * slotOf I ≤
      parkIndex ((w.st dst).parked) id * slotOf I :=
    Nat.mul_le_mul_right _ hidx
  have hle : parkIndex ((w'.st dst).parked) id * slotOf I + work ((w'.st dst).phase) ≤
      parkIndex ((w.st dst).parked) id * slotOf I + work ((w'.st dst).phase) :=
    Nat.add_le_add_right hmul _
  have hlt : parkIndex ((w.st dst).parked) id * slotOf I + work ((w'.st dst).phase) <
      parkIndex ((w.st dst).parked) id * slotOf I + work ((w.st dst).phase) :=
    Nat.add_lt_add_left hwork _
  exact Nat.lt_of_le_of_lt hle hlt

/-- `runFrom` of a concatenation, once each piece has a result. -/
theorem run_append_some (I : Impl) (w : World) (acts1 acts2 : List Action) (w1 w2 : World)
    (h1 : runFrom I (some w) acts1 = some w1) (h2 : runFrom I (some w1) acts2 = some w2) :
    runFrom I (some w) (acts1 ++ acts2) = some w2 := by
  induction acts1 generalizing w with
  | nil =>
    simp [runFrom] at h1
    cases h1
    simpa using h2
  | cons a as ih =>
    simp [runFrom] at h1
    cases ha : apply I a w with
    | none =>
      cases as <;> simp [runFrom, ha] at h1
    | some w' =>
      simp [ha] at h1
      simp [runFrom, ha]
      exact ih w' h1

theorem callPos_absent (ms : List Msg) (c : InstId)
    (h : ∀ m ∈ ms, m.callFrom ≠ some c) : callPos ms c = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hm : m.callFrom ≠ some c := h m (by simp)
    simp [callPos, hm, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons]

theorem queue_zero_of_no_mail (w : World) (c d : InstId) (h : ¬ mailCall w d c) :
    queuePos w c d = 0 := by
  have hno : ∀ m ∈ (w.st d).box, m.callFrom ≠ some c := by
    intro m hm hc
    exact h (Or.inl ⟨m, hm, hc⟩)
  have hpos := callPos_absent (w.st d).box c hno
  simp [queuePos, hpos, Nat.lt_irrefl]

theorem reply_debt_drop (I : Impl) (w w' : World) (id dst : InstId)
    (hq : queuePos w' id dst ≤ queuePos w id dst)
    (hwork : work ((w'.st dst).phase) < work ((w.st dst).phase))
    (hS : ProgSrc I w') : replyDebt I w' id dst < replyDebt I w id dst := by
  unfold replyDebt
  have hw := work_slot I w' hS dst
  by_cases hlt : queuePos w' id dst < queuePos w id dst
  · have hbound : work ((w'.st dst).phase) + 1 ≤ slotOf I := hw
    have hdec : queuePos w' id dst + 1 ≤ queuePos w id dst := Nat.succ_le_of_lt hlt
    have hleft : queuePos w' id dst * slotOf I + work ((w'.st dst).phase) <
        (queuePos w' id dst + 1) * slotOf I :=
      debt_index (slotOf I) (queuePos w' id dst) (work ((w'.st dst).phase)) hbound
    have hmul : (queuePos w' id dst + 1) * slotOf I ≤ queuePos w id dst * slotOf I :=
      Nat.mul_le_mul_right _ hdec
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hleft hmul)
      (Nat.le_add_right _ (work ((w.st dst).phase)))
  · have heq : queuePos w' id dst = queuePos w id dst := Nat.le_antisymm hq (Nat.le_of_not_lt hlt)
    rw [heq]
    exact Nat.add_lt_add_left hwork _

theorem not_mail_not_any (w : World) (hT : CallTagInv w) (c d : InstId) (k : Cont)
    (hph : (w.st c).phase = .awaitReply d k) (hno : ¬ mailCall w d c) : ¬ anyCall w c := by
  intro h
  rcases h with ⟨i, m, hm, hc⟩ | ⟨i, p, hp, hc⟩
  · rcases hT.msgOwner i c (Or.inl ⟨m, hm, hc⟩) with ⟨k', hk⟩ | ⟨k', hk⟩
    · rw [hph] at hk
      cases hk
      exact hno (Or.inl ⟨m, hm, hc⟩)
    · simp [hph] at hk
  · rcases hT.msgOwner i c (Or.inr ⟨p, hp, hc⟩) with ⟨k', hk⟩ | ⟨k', hk⟩
    · rw [hph] at hk
      cases hk
      exact hno (Or.inr ⟨p, hp, hc⟩)
    · rw [hph] at hk
      cases hk

/-- A step that leaves the caller in `awaitReply` does not move the call further back. -/
theorem queue_mono (I : Impl) (hL : LocalOk I) (a : Action) (w w' : World) (id dst : InstId) (k : Cont)
    (h : apply I a w = some w') (hph : (w.st id).phase = .awaitReply dst k)
    (hph' : (w'.st id).phase = .awaitReply dst k) (hM : MailInv w) (hT : CallTagInv w)
    (hOcc : OccInv I w) (hlive' : (w'.st dst).life = .alive) :
    queuePos w' id dst ≤ queuePos w id dst := by
  by_cases hq : callPos ((w.st dst).box) id < ((w.st dst).box).length
  · by_cases hrecv : a = .recvBulk dst
    · subst hrecv
      rcases recv_box_progress I hL w w' dst id k (by simpa [apply] using h) hM hT hph hq with
        hhand | hcloser
      · have hzero := queue_zero_of_no_mail w' id dst hhand.2.1
        rw [hzero]
        exact Nat.zero_le _
      · have hlt := hcloser.2.2
        have hnew : queuePos w' id dst ≤ callPos ((w'.st dst).box) id + 1 := by
          by_cases hpos : callPos ((w'.st dst).box) id < ((w'.st dst).box).length
          · simp [queuePos, hpos]
          · simp [queuePos, hpos]
        have hold : queuePos w id dst = callPos ((w.st dst).box) id + 1 := by
          simp [queuePos, hq]
        rw [hold]
        exact Nat.le_trans hnew (Nat.succ_le_succ (Nat.le_of_lt hlt))
    · have hkeep := box_pos_mono I a w w' h hOcc dst id hrecv hlive' hq
      simp [queuePos, hq, hkeep.2]
      rw [hkeep.1]
      exact Nat.le_refl _
  · have hmail : ¬ mailCall w dst id := by
      intro hm
      exact hq (await_mail_in_box w hT id dst k hph hm).1
    have hany := not_mail_not_any w hT id dst k hph hmail
    have hany' := no_new_mailCall I a w w' id dst k h hph hph' hany
    have hmail' : ¬ mailCall w' dst id := fun hm => hany' (anyCall_mail w' dst id hm)
    have hz := queue_zero_of_no_mail w id dst hmail
    have hz' := queue_zero_of_no_mail w' id dst hmail'
    simp [hz, hz']

theorem prepend_work (w w' w2 : World) (id : InstId)
    (hph : (w'.st id).phase = (w.st id).phase)
    (hwk : work ((w2.st id).phase) < work ((w'.st id).phase)) :
    work ((w2.st id).phase) < work ((w.st id).phase) := by
  exact Nat.lt_of_lt_of_eq hwk (by simp [hph])

theorem height_same (hs : List (Node × Nat)) (w w' : World) (id : InstId) (n : Nat)
    (hty : (w'.st id).typestate = (w.st id).typestate)
    (hn : heightOf hs (nodeAt w id) < n) : heightOf hs (nodeAt w' id) < n := by
  simpa [nodeAt, hty] using hn

/-- Drain a blocking send by steps on its chain. `ihn` unblocks a strictly shorter partner. -/
theorem send_go (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (N : Nat)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (n : Nat)
    (ihn : ∀ m w id, m < n → heightOf hs (nodeAt w id) < m → Reachable I N w → Blocked w id →
      ¬ PurePeerEnd I.desc w id →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase))
    (fuel : Nat) : ∀ w id dst k, heightOf hs (nodeAt w id) < n →
      (w.st id).phase = .parked dst false k → Reachable I N w →
      sendDebt I w id dst ≤ fuel →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro w id dst k hn hph hR hdebt
    have hliveD := park_target_alive I hL hG N w hR id dst false k hph
    have hbelow := park_below I hL hG N w hR ((inv3_reachable I hL hG N w hR).1.2.1)
      id dst k hs hok hph hliveD
    have hInv := inv_reachable I N w hL hR
    cases hphD : (w.st dst).phase with
    | crashed =>
      exact False.elim ((reachable_not_crashed I hL hG N w hR) dst (by simp [hphD]))
    | idle =>
      have hmail : (w.st dst).box ≠ [] ∨ (w.st dst).parked ≠ [] := by
        obtain ⟨p, hp, _, _⟩ := hInv.2.1.bwd id dst false k hph
        exact Or.inr (fun hempty => by simp [hempty] at hp)
      have hen := can_receive_enabled I hL w dst
        ((inv3_reachable I hL hG N w hR).1.2.2.1) (mail_accepted_reachable I hL N w hR)
        ⟨⟨hliveD, hphD⟩, hmail⟩
      cases happ : apply I (.recvBulk dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := blocking_next I (.recvBulk dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.recvBulk dst) (waits_on_park w id dst false k hph)
          (on_self_bulk w dst)
        rcases hnext with hstay | hgo
        · obtain ⟨p, hp, hsender, _⟩ := hInv.2.1.bwd id dst false k hph
          cases hpList : (w.st dst).parked with
          | nil => simp [hpList] at hp
          | cons q qs =>
            have hne : id ≠ dst := by
              intro heq
              have hbad := hbelow
              simp [nodeAt, heq] at hbad
            by_cases hhead : q.sender = id
            · exact False.elim (bulk_head_leaves I w w' dst (by simpa [apply] using happ) q qs hpList
                id hhead.symm hne false k hph dst false k hstay)
            · have hin := parkIndex_of_mem (q :: qs) id ⟨p, by simpa [hpList] using hp, hsender⟩
              have hcloser := recv_closer I w w' dst (by simpa [apply] using happ) q qs hpList id hhead
                (by simpa [hpList] using hin)
              have hidx : parkIndex ((w'.st dst).parked) id + 1 = parkIndex ((w.st dst).parked) id := by
                simpa [hpList] using hcloser.1
              have hR' := Reachable.step w w' (.recvBulk dst) hR happ
              have hdebt' := send_debt_drop_index I w w' id dst (prog_src_reachable I N w' hR') hidx
              have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
              have hty := waiting_ty_step I (.recvBulk dst) w w' id happ
                (Or.inl ⟨dst, false, k, hph⟩) (Or.inl ⟨dst, false, k, hstay⟩)
              obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
                ihf (sendDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
                  (Nat.le_refl _)
              refine ⟨.recvBulk dst :: acts, w2, ChainRun.cons w (.recvBulk dst) w' acts hchain happ hC, ?_,
                hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
              simp [runFrom, happ, hrun]
        · have hnot : ¬ Blocked w' id := by
            intro hB
            simp [Blocked, hgo] at hB
            cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            have heq : work ((w'.st id).phase) = work (proceed (w.st id) k).phase := by simp [hgo]
            rw [heq]
            have hsrc : work ((w.st id).phase) = work (.parked dst false k) := by simp [hph]
            rw [hsrc]
            exact work_proceed (w.st id) dst false k
          refine ⟨[.recvBulk dst], w', ChainRun.cons w (.recvBulk dst) w' [] hchain happ (ChainRun.nil w'), ?_,
            Reachable.step w w' (.recvBulk dst) hR happ, hnot, hwk⟩
          simp [runFrom, happ]
    | run kD =>
      have hen := run_enabled I w dst kD hphD hliveD
      cases happ : apply I (.exec dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := blocking_next I (.exec dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.exec dst) (waits_on_park w id dst false k hph)
          (on_self_exec w dst)
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.exec dst) hR happ
          have hlive' := park_target_alive I hL hG N w' hR' id dst false k hstay
          obtain ⟨p, hp, hsender, _⟩ := hInv.2.1.bwd id dst false k hph
          have hin := parkIndex_of_mem _ id ⟨p, hp, hsender⟩
          have hidx := (step_index I (.exec dst) w w' happ hInv.2.2 id dst false k k hph hstay hliveD hlive' hin).1
          have hwork := work_exec I hL hG N w hR dst kD hphD hliveD w' (by simpa [apply] using happ)
          have hdebt' := send_debt_drop_work I w w' id dst hidx hwork
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.exec dst) w w' id happ
            (Or.inl ⟨dst, false, k, hph⟩) (Or.inl ⟨dst, false, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (sendDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          refine ⟨.exec dst :: acts, w2, ChainRun.cons w (.exec dst) w' acts hchain happ hC, ?_,
            hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
          simp [runFrom, happ, hrun]
        · have hnot : ¬ Blocked w' id := by
            intro hB
            simp [Blocked, hgo] at hB
            cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            have heq : work ((w'.st id).phase) = work (proceed (w.st id) k).phase := by simp [hgo]
            rw [heq]
            simp [hph, work_proceed]
          refine ⟨[.exec dst], w', ChainRun.cons w (.exec dst) w' [] hchain happ (ChainRun.nil w'), ?_,
            Reachable.step w w' (.exec dst) hR happ, hnot, hwk⟩
          simp [runFrom, happ]
    | awaitEffect kD =>
      have hen := effect_finish_enabled I w dst kD hphD
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := blocking_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_park w id dst false k hph)
          (on_finish_self w dst)
        obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
          ⟨hliveD, by simp [hphD]⟩
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hpk := finish_parked I w w' dst dst (by simpa [apply] using happ)
          have hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id := by
            simp [hpk]
          have hdebt' := send_debt_drop_work I w w' id dst hidx hworkD
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, false, k, hph⟩) (Or.inl ⟨dst, false, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (sendDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          refine ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC, ?_,
            hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
          simp [runFrom, happ, hrun]
        · have hnot : ¬ Blocked w' id := by
            intro hB
            simp [Blocked, hgo] at hB
            cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph, work_proceed]
          refine ⟨[.finish dst], w', ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'), ?_,
            Reachable.step w w' (.finish dst) hR happ, hnot, hwk⟩
          simp [runFrom, happ]
    | awaitPeer kD =>
      have hfin := target_finishable I hG w (inv_reachable I N w hL hR) id dst
        (Or.inl ⟨false, k, hph⟩)
      have hen := peer_finish_enabled I w dst kD hphD hfin
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := blocking_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_park w id dst false k hph)
          (on_finish_self w dst)
        obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
          ⟨hliveD, by simp [hphD]⟩
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hpk := finish_parked I w w' dst dst (by simpa [apply] using happ)
          have hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id := by
            simp [hpk]
          have hdebt' := send_debt_drop_work I w w' id dst hidx hworkD
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, false, k, hph⟩) (Or.inl ⟨dst, false, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (sendDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          refine ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC, ?_,
            hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
          simp [runFrom, happ, hrun]
        · have hnot : ¬ Blocked w' id := by
            intro hB
            simp [Blocked, hgo] at hB
            cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph, work_proceed]
          refine ⟨[.finish dst], w', ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'), ?_,
            Reachable.step w w' (.finish dst) hR happ, hnot, hwk⟩
          simp [runFrom, happ]
    | parked _ _ _ =>
      have hnD : heightOf hs (nodeAt w dst) + 1 < n :=
        Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hbelow) hn
      obtain ⟨acts, w1, hC, hrun, hR1, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hnD (Nat.lt_succ_self _) hR ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := absorb_send I hL hG N dst id k w acts hC hR hph
      rcases hor with hdone | hfull
      · rcases hdone with ⟨hnot, hwk⟩
        exact ⟨acts1, wA, hC1, hrun1, hRA, hnot, hwk⟩
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := send_debt_drop_work I w wA id dst hle (by simpa [hwA] using hworkD)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (sendDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        refine ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩
    | awaitReply _ _ =>
      have hnD : heightOf hs (nodeAt w dst) + 1 < n :=
        Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hbelow) hn
      obtain ⟨acts, w1, hC, hrun, hR1, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hnD (Nat.lt_succ_self _) hR ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := absorb_send I hL hG N dst id k w acts hC hR hph
      rcases hor with hdone | hfull
      · rcases hdone with ⟨hnot, hwk⟩
        exact ⟨acts1, wA, hC1, hrun1, hRA, hnot, hwk⟩
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := send_debt_drop_work I w wA id dst hle (by simpa [hwA] using hworkD)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (sendDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        refine ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩

theorem reply_absorb (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (dst root : InstId) (k : Cont) (w : World) (acts : List Action)
    (hC : ChainRun I dst w acts) (hR : Reachable I N w)
    (hph : (w.st root).phase = .awaitReply dst k) :
    ∃ acts1 w1, ChainRun I root w acts1 ∧ runFrom I (some w) acts1 = some w1 ∧
      Reachable I N w1 ∧
      (¬ Blocked w1 root ∧ work ((w1.st root).phase) < work ((w.st root).phase) ∨
        runFrom I (some w) acts = some w1 ∧ (w1.st root).phase = .awaitReply dst k ∧
          queuePos w1 root dst ≤ queuePos w root dst ∧
          (w1.st root).typestate = (w.st root).typestate) := by
  induction hC with
  | nil w =>
    exact ⟨[], w, ChainRun.nil w, rfl, hR, Or.inr ⟨rfl, hph, Nat.le_refl _, rfl⟩⟩
  | cons w a w' as hOn hA hRest ih =>
    have hInv := inv_reachable I N w hL hR
    have hnext := await_next I a w w' root dst k hInv.2.1 hInv.2.2 hA hph
    have hlift := on_partner w root dst a (waits_on_reply w root dst k hph) hOn
    rcases hnext with hstay | hgo
    · have hR' := Reachable.step w w' a hR hA
      have hlive' := reply_target_alive I hL hG N w' hR' root dst k hstay
      have hT := call_tag_reachable I hL hG N w hR
      have hq := queue_mono I hL a w w' root dst k hA hph hstay hInv.2.1 hT
        ((inv3_reachable I hL hG N w hR).1.2.1) hlive'
      obtain ⟨acts1, w1, hC1, hrun1, hR1, hor⟩ := ih hR' hstay
      rcases hor with hdone | hfull
      · refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1, Or.inl ?_⟩
        · simp [runFrom, hA, hrun1]
        · rcases hdone with ⟨hnot, hlt⟩
          exact ⟨hnot, Nat.lt_of_lt_of_eq hlt (by simp [hstay, hph])⟩
      · rcases hfull with ⟨hrest, hph1, hle, hty1⟩
        have hty := waiting_ty_step I a w w' root hA
          (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
        refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1,
          Or.inr ⟨?_, hph1, ?_, ?_⟩⟩
        · simp [runFrom, hA, hrun1]
        · simp [runFrom, hA, hrest]
        · exact Nat.le_trans hle hq
        · exact hty1.trans hty
    · have hnot : ¬ Blocked w' root := by
        intro hB
        simp [Blocked, hgo] at hB
        cases hk : k.rest <;> simp [proceed, hk] at hB
      have hwk : work ((w'.st root).phase) < work ((w.st root).phase) := by
        have heq : work ((w'.st root).phase) = work (proceed (w.st root) k).phase := by simp [hgo]
        rw [heq]
        simp [hph]
        exact work_proceed_reply (w.st root) dst k
      refine ⟨[a], w', ChainRun.cons w a w' [] hlift hA (ChainRun.nil w'), ?_,
        Reachable.step w w' a hR hA, Or.inl ⟨hnot, hwk⟩⟩
      · simp [runFrom, hA]

theorem reply_debt_queue (I : Impl) (w w' : World) (id dst : InstId) (hS : ProgSrc I w')
    (hq : queuePos w' id dst < queuePos w id dst) : replyDebt I w' id dst < replyDebt I w id dst := by
  have hw := work_slot I w' hS dst
  unfold replyDebt
  have hdec : queuePos w' id dst + 1 ≤ queuePos w id dst := Nat.succ_le_of_lt hq
  have hleft : queuePos w' id dst * slotOf I + work ((w'.st dst).phase) <
      (queuePos w' id dst + 1) * slotOf I :=
    debt_index (slotOf I) (queuePos w' id dst) (work ((w'.st dst).phase)) hw
  have hmul : (queuePos w' id dst + 1) * slotOf I ≤ queuePos w id dst * slotOf I :=
    Nat.mul_le_mul_right _ hdec
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hleft hmul) (Nat.le_add_right _ _)

/-- Drain an `awaitReply` by steps on its chain. -/
theorem reply_go (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (N : Nat)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (n : Nat)
    (ihn : ∀ m w id, m < n → heightOf hs (nodeAt w id) < m → Reachable I N w → Blocked w id →
      ¬ PurePeerEnd I.desc w id →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase))
    (fuel : Nat) : ∀ w id dst k, heightOf hs (nodeAt w id) < n →
      (w.st id).phase = .awaitReply dst k → Reachable I N w →
      replyDebt I w id dst ≤ fuel →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro w id dst k hn hph hR hdebt
    have hliveD := reply_target_alive I hL hG N w hR id dst k hph
    have hbelow := reply_below I hL hG N w hR id dst k hs hok hph hliveD
    have hInv := inv_reachable I N w hL hR
    have hbelowN : heightOf hs (nodeAt w dst) + 1 < n :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hbelow) hn
    cases hphD : (w.st dst).phase with
    | crashed =>
      exact False.elim ((reachable_not_crashed I hL hG N w hR) dst (by simp [hphD]))
    | parked _ _ _ =>
      obtain ⟨acts, w1, hC, hrun, _, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hbelowN (Nat.lt_succ_self _) hR
          ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := reply_absorb I hL hG N dst id k w acts hC hR hph
      rcases hor with hdone | hfull
      · rcases hdone with ⟨hnot, hwk⟩
        exact ⟨acts1, wA, hC1, hrun1, hRA, hnot, hwk⟩
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := reply_debt_drop I w wA id dst hle (by simpa [hwA] using hworkD)
          (prog_src_reachable I N wA hRA)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (replyDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        exact ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩
    | awaitReply _ _ =>
      obtain ⟨acts, w1, hC, hrun, _, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hbelowN (Nat.lt_succ_self _) hR
          ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := reply_absorb I hL hG N dst id k w acts hC hR hph
      rcases hor with hdone | hfull
      · rcases hdone with ⟨hnot, hwk⟩
        exact ⟨acts1, wA, hC1, hrun1, hRA, hnot, hwk⟩
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := reply_debt_drop I w wA id dst hle (by simpa [hwA] using hworkD)
          (prog_src_reachable I N wA hRA)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (replyDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        exact ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩
    | awaitEffect kD =>
      have hen := effect_finish_enabled I w dst kD hphD
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := await_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_reply w id dst k hph)
          (on_finish_self w dst)
        obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
          ⟨hliveD, by simp [hphD]⟩
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hlive' := reply_target_alive I hL hG N w' hR' id dst k hstay
          have hq := queue_mono I hL (.finish dst) w w' id dst k happ hph hstay hInv.2.1
            (call_tag_reachable I hL hG N w hR) ((inv3_reachable I hL hG N w hR).1.2.1) hlive'
          have hdebt' := reply_debt_drop I w w' id dst hq hworkD (prog_src_reachable I N w' hR')
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (replyDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          exact ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hnot : ¬ Blocked w' id := by
            intro hB; simp [Blocked, hgo] at hB; cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph]; exact work_proceed_reply (w.st id) dst k
          exact ⟨[.finish dst], w', ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'),
            by simp [runFrom, happ], Reachable.step w w' (.finish dst) hR happ, hnot, hwk⟩
    | awaitPeer kD =>
      have hfin := target_finishable I hG w (inv_reachable I N w hL hR) id dst
        (Or.inr ⟨k, hph⟩)
      have hen := peer_finish_enabled I w dst kD hphD hfin
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := await_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_reply w id dst k hph)
          (on_finish_self w dst)
        obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
          ⟨hliveD, by simp [hphD]⟩
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hlive' := reply_target_alive I hL hG N w' hR' id dst k hstay
          have hq := queue_mono I hL (.finish dst) w w' id dst k happ hph hstay hInv.2.1
            (call_tag_reachable I hL hG N w hR) ((inv3_reachable I hL hG N w hR).1.2.1) hlive'
          have hdebt' := reply_debt_drop I w w' id dst hq hworkD (prog_src_reachable I N w' hR')
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (replyDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          exact ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hnot : ¬ Blocked w' id := by
            intro hB; simp [Blocked, hgo] at hB; cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph]; exact work_proceed_reply (w.st id) dst k
          exact ⟨[.finish dst], w', ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'),
            by simp [runFrom, happ], Reachable.step w w' (.finish dst) hR happ, hnot, hwk⟩
    | run kD =>
      have hen := run_enabled I w dst kD hphD hliveD
      cases happ : apply I (.exec dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := await_next I (.exec dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.exec dst) (waits_on_reply w id dst k hph) (on_self_exec w dst)
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.exec dst) hR happ
          have hlive' := reply_target_alive I hL hG N w' hR' id dst k hstay
          have hq := queue_mono I hL (.exec dst) w w' id dst k happ hph hstay hInv.2.1
            (call_tag_reachable I hL hG N w hR) ((inv3_reachable I hL hG N w hR).1.2.1) hlive'
          have hworkD := work_exec I hL hG N w hR dst kD hphD hliveD w' (by simpa [apply] using happ)
          have hdebt' := reply_debt_drop I w w' id dst hq hworkD (prog_src_reachable I N w' hR')
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.exec dst) w w' id happ
            (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (replyDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
              (Nat.le_refl _)
          exact ⟨.exec dst :: acts, w2, ChainRun.cons w (.exec dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hnot : ¬ Blocked w' id := by
            intro hB; simp [Blocked, hgo] at hB; cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph]; exact work_proceed_reply (w.st id) dst k
          exact ⟨[.exec dst], w', ChainRun.cons w (.exec dst) w' [] hchain happ (ChainRun.nil w'),
            by simp [runFrom, happ], Reachable.step w w' (.exec dst) hR happ, hnot, hwk⟩
    | idle =>
      have hT := call_tag_reachable I hL hG N w hR
      have hmail : (w.st dst).box ≠ [] ∨ (w.st dst).parked ≠ [] := by
        rcases hT.awaiting id dst k hph with hmail | hhand | hpend
        · rcases hmail.1 with ⟨m, hm, _⟩ | ⟨p, hp, _⟩
          · exact Or.inl (fun hempty => by simp [hempty] at hm)
          · exact Or.inr (fun hempty => by simp [hempty] at hp)
        · rcases hhand.2.1 with ⟨_, hcar, _⟩
          simp [carriedCont, hphD] at hcar
        · rcases hpend.2.2 with ⟨_, hcar, _⟩
          simp [carriedCont, hphD] at hcar
      have hen := can_receive_enabled I hL w dst
        ((inv3_reachable I hL hG N w hR).1.2.2.1) (mail_accepted_reachable I hL N w hR)
        ⟨⟨hliveD, hphD⟩, hmail⟩
      cases happ : apply I (.recvBulk dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := await_next I (.recvBulk dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.recvBulk dst) (waits_on_reply w id dst k hph)
          (on_self_bulk w dst)
        rcases hnext with hstay | hgo
        · have hpos : callPos ((w.st dst).box) id < ((w.st dst).box).length := by
            rcases hT.awaiting id dst k hph with hmailA | hhand | hpend
            · exact (await_mail_in_box w hT id dst k hph hmailA.1).1
            · rcases hhand.2.1 with ⟨_, hcar, _⟩
              simp [carriedCont, hphD] at hcar
            · rcases hpend.2.2 with ⟨_, hcar, _⟩
              simp [carriedCont, hphD] at hcar
          have hR' := Reachable.step w w' (.recvBulk dst) hR happ
          rcases recv_box_progress I hL w w' dst id k (by simpa [apply] using happ) hInv.2.1 hT hph hpos with
            hhand | hcloser
          · have hzero := queue_zero_of_no_mail w' id dst hhand.2.1
            have hold : 0 < queuePos w id dst := by
              simp [queuePos, hpos]
            have hq : queuePos w' id dst < queuePos w id dst := by
              rw [hzero]; exact hold
            have hdebt' := reply_debt_queue I w w' id dst (prog_src_reachable I N w' hR') hq
            have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
            have hty := waiting_ty_step I (.recvBulk dst) w w' id happ
              (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
            obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
              ihf (replyDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
                (Nat.le_refl _)
            exact ⟨.recvBulk dst :: acts, w2, ChainRun.cons w (.recvBulk dst) w' acts hchain happ hC,
              by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
          · have hlt := hcloser.2.2
            have hnew : queuePos w' id dst ≤ callPos ((w'.st dst).box) id + 1 := by
              by_cases hp : callPos ((w'.st dst).box) id < ((w'.st dst).box).length
              · simp [queuePos, hp]
              · simp [queuePos, hp]
            have hold : queuePos w id dst = callPos ((w.st dst).box) id + 1 := by simp [queuePos, hpos]
            have hq : queuePos w' id dst < queuePos w id dst := by
              rw [hold]
              exact Nat.lt_of_le_of_lt (Nat.le_trans hnew (Nat.succ_le_of_lt hlt)) (Nat.lt_succ_self _)
            have hdebt' := reply_debt_queue I w w' id dst (prog_src_reachable I N w' hR') hq
            have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
            have hty := waiting_ty_step I (.recvBulk dst) w w' id happ
              (Or.inr ⟨dst, k, hph⟩) (Or.inr ⟨dst, k, hstay⟩)
            obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
              ihf (replyDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay hR'
                (Nat.le_refl _)
            exact ⟨.recvBulk dst :: acts, w2, ChainRun.cons w (.recvBulk dst) w' acts hchain happ hC,
              by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hnot : ¬ Blocked w' id := by
            intro hB; simp [Blocked, hgo] at hB; cases hk : k.rest <;> simp [proceed, hk] at hB
          have hwk : work ((w'.st id).phase) < work ((w.st id).phase) := by
            simp [hgo, hph]; exact work_proceed_reply (w.st id) dst k
          exact ⟨[.recvBulk dst], w', ChainRun.cons w (.recvBulk dst) w' [] hchain happ (ChainRun.nil w'),
            by simp [runFrom, happ], Reachable.step w w' (.recvBulk dst) hR happ, hnot, hwk⟩

theorem call_absorb (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (dst root : InstId) (k : Cont) (w : World) (acts : List Action)
    (hC : ChainRun I dst w acts) (hR : Reachable I N w)
    (hph : (w.st root).phase = .parked dst true k) :
    ∃ acts1 w1, ChainRun I root w acts1 ∧ runFrom I (some w) acts1 = some w1 ∧
      Reachable I N w1 ∧
      ((w1.st root).phase = .awaitReply dst k ∧ (w1.st root).typestate = (w.st root).typestate ∨
        runFrom I (some w) acts = some w1 ∧ (w1.st root).phase = .parked dst true k ∧
          parkIndex ((w1.st dst).parked) root ≤ parkIndex ((w.st dst).parked) root ∧
          (w1.st root).typestate = (w.st root).typestate) := by
  induction hC with
  | nil w =>
    exact ⟨[], w, ChainRun.nil w, rfl, hR, Or.inr ⟨rfl, hph, Nat.le_refl _, rfl⟩⟩
  | cons w a w' as hOn hA hRest ih =>
    have hInv := inv_reachable I N w hL hR
    have hnext := call_park_next I a w w' root dst k hInv.2.1 hInv.2.2 hA hph
    have hlift := on_partner w root dst a (waits_on_park w root dst true k hph) hOn
    rcases hnext with hstay | hgo
    · have hR' := Reachable.step w w' a hR hA
      have hlive := park_target_alive I hL hG N w hR root dst true k hph
      have hlive' := park_target_alive I hL hG N w' hR' root dst true k hstay
      obtain ⟨p, hp, hsender, _⟩ := hInv.2.1.bwd root dst true k hph
      have hin := parkIndex_of_mem _ root ⟨p, hp, hsender⟩
      have hidx := (step_index I a w w' hA hInv.2.2 root dst true k k hph hstay hlive hlive' hin).1
      obtain ⟨acts1, w1, hC1, hrun1, hR1, hor⟩ := ih hR' hstay
      rcases hor with hadmit | hfull
      · refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1, Or.inl ?_⟩
        · simp [runFrom, hA, hrun1]
        · have hty := waiting_ty_step I a w w' root hA
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
          exact ⟨hadmit.1, hadmit.2.trans hty⟩
      · rcases hfull with ⟨hrest, hph1, hle, hty1⟩
        have hty := waiting_ty_step I a w w' root hA
          (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
        refine ⟨a :: acts1, w1, ChainRun.cons w a w' acts1 hlift hA hC1, ?_, hR1,
          Or.inr ⟨?_, hph1, ?_, ?_⟩⟩
        · simp [runFrom, hA, hrun1]
        · simp [runFrom, hA, hrest]
        · exact Nat.le_trans hle hidx
        · exact hty1.trans hty
    · have hty := waiting_ty_step I a w w' root hA
        (Or.inl ⟨dst, true, k, hph⟩) (Or.inr ⟨dst, k, hgo⟩)
      refine ⟨[a], w', ChainRun.cons w a w' [] hlift hA (ChainRun.nil w'), ?_,
        Reachable.step w w' a hR hA, Or.inl ⟨hgo, hty⟩⟩
      · simp [runFrom, hA]

theorem call_debt_drop_index (I : Impl) (w w' : World) (id dst : InstId) (hS : ProgSrc I w')
    (hidx : parkIndex ((w'.st dst).parked) id + 1 = parkIndex ((w.st dst).parked) id) :
    callParkDebt I w' id dst < callParkDebt I w id dst := by
  have hw := work_slot I w' hS dst
  unfold callParkDebt
  have hidx' : parkIndex ((w.st dst).parked) id = parkIndex ((w'.st dst).parked) id + 1 := hidx.symm
  rw [hidx']
  have hlt : work ((w'.st dst).phase) < slotOf I := Nat.lt_of_succ_le hw
  have hnew : (parkIndex ((w'.st dst).parked) id + 1) * slotOf I + work ((w'.st dst).phase) <
      (parkIndex ((w'.st dst).parked) id + 1) * slotOf I + slotOf I :=
    Nat.add_lt_add_left hlt _
  have heq : (parkIndex ((w'.st dst).parked) id + 1) * slotOf I + slotOf I =
      (parkIndex ((w'.st dst).parked) id + 2) * slotOf I :=
    (Nat.succ_mul (parkIndex ((w'.st dst).parked) id + 1) (slotOf I)).symm
  rw [heq] at hnew
  exact Nat.lt_of_lt_of_le hnew (Nat.le_add_right _ (work ((w.st dst).phase)))

theorem call_debt_drop_work (I : Impl) (w w' : World) (id dst : InstId)
    (hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id)
    (hwork : work ((w'.st dst).phase) < work ((w.st dst).phase)) :
    callParkDebt I w' id dst < callParkDebt I w id dst := by
  unfold callParkDebt
  have hmul : (parkIndex ((w'.st dst).parked) id + 1) * slotOf I ≤
      (parkIndex ((w.st dst).parked) id + 1) * slotOf I :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hidx)
  have hle := Nat.add_le_add_right hmul (work ((w'.st dst).phase))
  have hlt := Nat.add_lt_add_left hwork
    ((parkIndex ((w.st dst).parked) id + 1) * slotOf I)
  exact Nat.lt_of_le_of_lt hle hlt

/-- A finite chain execution from a reachable blocked actor that is not a pure
untimed peer end. Every step's subject is on that actor's wait chain. Internal
effects and a finishable peer wait are ordinary steps. The actor is not blocked
at the end. A partner in `awaitPeer` is finishable: a pure untimed template is
not a legal wait target. -/
theorem call_go (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (N : Nat)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (n : Nat)
    (ihn : ∀ m w id, m < n → heightOf hs (nodeAt w id) < m → Reachable I N w → Blocked w id →
      ¬ PurePeerEnd I.desc w id →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase))
    (fuel : Nat) : ∀ w id dst k, heightOf hs (nodeAt w id) < n →
      (w.st id).phase = .parked dst true k → Reachable I N w →
      callParkDebt I w id dst ≤ fuel →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro w id dst k hn hph hR hdebt
    have hliveD := park_target_alive I hL hG N w hR id dst true k hph
    have hbelow := call_below I hL hG N w hR id dst k hs hok hph hliveD
    have hInv := inv_reachable I N w hL hR
    have hbelowN : heightOf hs (nodeAt w dst) + 1 < n :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hbelow) hn
    have finishReply (w1 : World) (acts1 : List Action)
        (hC1 : ChainRun I id w acts1) (hrun1 : runFrom I (some w) acts1 = some w1)
        (hR1 : Reachable I N w1) (hph1 : (w1.st id).phase = .awaitReply dst k)
        (hty : (w1.st id).typestate = (w.st id).typestate) :
        ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
          Reachable I N w' ∧ ¬ Blocked w' id ∧
          work ((w'.st id).phase) < work ((w.st id).phase) := by
      obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
        reply_go I hG hL N hs hok n ihn (replyDebt I w1 id dst) w1 id dst k
          (height_same hs w w1 id n hty hn) hph1 hR1 (Nat.le_refl _)
      refine ⟨acts1 ++ acts2, w2, chain_append I id w acts1 w1 acts2 hC1 hrun1 hC2,
        run_append_some I w acts1 acts2 w1 w2 hrun1 hrun2, hR2, hnot, ?_⟩
      have heq : work ((w1.st id).phase) = work ((w.st id).phase) := by
        simp [hph1, hph, work, phaseFuel]
      exact Nat.lt_of_lt_of_eq hwk heq
    cases hphD : (w.st dst).phase with
    | crashed =>
      exact False.elim ((reachable_not_crashed I hL hG N w hR) dst (by simp [hphD]))
    | parked _ _ _ =>
      obtain ⟨acts, w1, hC, hrun, _, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hbelowN (Nat.lt_succ_self _) hR
          ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := call_absorb I hL hG N dst id k w acts hC hR hph
      rcases hor with hadmit | hfull
      · exact finishReply wA acts1 hC1 hrun1 hRA hadmit.1 hadmit.2
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := call_debt_drop_work I w wA id dst hle (by simpa [hwA] using hworkD)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (callParkDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        exact ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩
    | awaitReply _ _ =>
      obtain ⟨acts, w1, hC, hrun, _, _, hworkD⟩ :=
        ihn (heightOf hs (nodeAt w dst) + 1) w dst hbelowN (Nat.lt_succ_self _) hR
          ⟨hliveD, by simp [hphD]⟩
          (by intro ⟨kP, hkP, _⟩; rw [hphD] at hkP; cases hkP)
      obtain ⟨acts1, wA, hC1, hrun1, hRA, hor⟩ := call_absorb I hL hG N dst id k w acts hC hR hph
      rcases hor with hadmit | hfull
      · exact finishReply wA acts1 hC1 hrun1 hRA hadmit.1 hadmit.2
      · rcases hfull with ⟨hrunAll, hphA, hle, hty⟩
        have hwA : wA = w1 := run_determ I w acts wA w1 hrunAll hrun
        have hdebt' := call_debt_drop_work I w wA id dst hle (by simpa [hwA] using hworkD)
        have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
        obtain ⟨acts2, w2, hC2, hrun2, hR2, hnot, hwk⟩ :=
          ihf (callParkDebt I wA id dst) hfuel wA id dst k (height_same hs w wA id n hty hn) hphA hRA
            (Nat.le_refl _)
        exact ⟨acts1 ++ acts2, w2, chain_append I id w acts1 wA acts2 hC1 hrun1 hC2,
          run_append_some I w acts1 acts2 wA w2 hrun1 hrun2, hR2, hnot,
          prepend_work w wA w2 id (by simp [hphA, hph]) hwk⟩
    | awaitEffect kD =>
      have hen := effect_finish_enabled I w dst kD hphD
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := call_park_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_park w id dst true k hph)
          (on_finish_self w dst)
        rcases hnext with hstay | hgo
        · obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
            ⟨hliveD, by simp [hphD]⟩
          have hR' := Reachable.step w w' (.finish dst) hR happ
          have hpk := finish_parked I w w' dst dst (by simpa [apply] using happ)
          have hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id := by
            simp [hpk]
          have hdebt' := call_debt_drop_work I w w' id dst hidx hworkD
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (callParkDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay
              hR' (Nat.le_refl _)
          exact ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inr ⟨dst, k, hgo⟩)
          exact finishReply w' [.finish dst]
            (ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'))
            (by simp [runFrom, happ]) hR' hgo hty
    | awaitPeer kD =>
      have hfin := target_finishable I hG w (inv_reachable I N w hL hR) id dst
        (Or.inl ⟨true, k, hph⟩)
      have hen := peer_finish_enabled I w dst kD hphD hfin
      cases happ : apply I (.finish dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := call_park_next I (.finish dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.finish dst) (waits_on_park w id dst true k hph)
          (on_finish_self w dst)
        rcases hnext with hstay | hgo
        · obtain ⟨_, hworkD⟩ := finish_unblocks I w w' dst (by simpa [apply] using happ)
            ⟨hliveD, by simp [hphD]⟩
          have hR' := Reachable.step w w' (.finish dst) hR happ
          have hpk := finish_parked I w w' dst dst (by simpa [apply] using happ)
          have hidx : parkIndex ((w'.st dst).parked) id ≤ parkIndex ((w.st dst).parked) id := by
            simp [hpk]
          have hdebt' := call_debt_drop_work I w w' id dst hidx hworkD
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (callParkDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay
              hR' (Nat.le_refl _)
          exact ⟨.finish dst :: acts, w2, ChainRun.cons w (.finish dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hR' := Reachable.step w w' (.finish dst) hR happ
          have hty := waiting_ty_step I (.finish dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inr ⟨dst, k, hgo⟩)
          exact finishReply w' [.finish dst]
            (ChainRun.cons w (.finish dst) w' [] hchain happ (ChainRun.nil w'))
            (by simp [runFrom, happ]) hR' hgo hty
    | run kD =>
      have hen := run_enabled I w dst kD hphD hliveD
      cases happ : apply I (.exec dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := call_park_next I (.exec dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.exec dst) (waits_on_park w id dst true k hph)
          (on_self_exec w dst)
        rcases hnext with hstay | hgo
        · have hR' := Reachable.step w w' (.exec dst) hR happ
          have hlive' := park_target_alive I hL hG N w' hR' id dst true k hstay
          obtain ⟨p, hp, hsender, _⟩ := hInv.2.1.bwd id dst true k hph
          have hin := parkIndex_of_mem _ id ⟨p, hp, hsender⟩
          have hidx := (step_index I (.exec dst) w w' happ hInv.2.2 id dst true k k hph hstay
            hliveD hlive' hin).1
          have hworkD := work_exec I hL hG N w hR dst kD hphD hliveD w' (by simpa [apply] using happ)
          have hdebt' := call_debt_drop_work I w w' id dst hidx hworkD
          have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
          have hty := waiting_ty_step I (.exec dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
          obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
            ihf (callParkDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn) hstay
              hR' (Nat.le_refl _)
          exact ⟨.exec dst :: acts, w2, ChainRun.cons w (.exec dst) w' acts hchain happ hC,
            by simp [runFrom, happ, hrun], hR2, hnot, prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hR' := Reachable.step w w' (.exec dst) hR happ
          have hty := waiting_ty_step I (.exec dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inr ⟨dst, k, hgo⟩)
          exact finishReply w' [.exec dst]
            (ChainRun.cons w (.exec dst) w' [] hchain happ (ChainRun.nil w'))
            (by simp [runFrom, happ]) hR' hgo hty
    | idle =>
      have hmail : (w.st dst).box ≠ [] ∨ (w.st dst).parked ≠ [] := by
        obtain ⟨p, hp, _, _⟩ := hInv.2.1.bwd id dst true k hph
        exact Or.inr (fun hempty => by simp [hempty] at hp)
      have hen := can_receive_enabled I hL w dst
        ((inv3_reachable I hL hG N w hR).1.2.2.1) (mail_accepted_reachable I hL N w hR)
        ⟨⟨hliveD, hphD⟩, hmail⟩
      cases happ : apply I (.recvBulk dst) w with
      | none => exact False.elim (hen happ)
      | some w' =>
        have hnext := call_park_next I (.recvBulk dst) w w' id dst k hInv.2.1 hInv.2.2 happ hph
        have hchain := on_partner w id dst (.recvBulk dst) (waits_on_park w id dst true k hph)
          (on_self_bulk w dst)
        rcases hnext with hstay | hgo
        · obtain ⟨p, hp, hsender, hc⟩ := hInv.2.1.bwd id dst true k hph
          cases hpList : (w.st dst).parked with
          | nil => simp [hpList] at hp
          | cons q qs =>
            have hne : id ≠ dst := by
              intro heq
              simp [nodeAt, heq] at hbelow
            by_cases hhead : q.sender = id
            · have hsame := (hInv.2.1.uniq dst dst q p (by simp [hpList]) hp
                (hhead.trans hsender.symm)).2
              exact False.elim (by
                have hphase := bulk_admits_call I w w' dst (by simpa [apply] using happ) q qs hpList
                  id hhead.symm hne k hph (by simpa [hsame] using hc)
                simp [hphase] at hstay)
            · have hin := parkIndex_of_mem (q :: qs) id ⟨p, by simpa [hpList] using hp, hsender⟩
              have hcloser := recv_closer I w w' dst (by simpa [apply] using happ) q qs hpList id hhead
                (by simpa [hpList] using hin)
              have hidx : parkIndex ((w'.st dst).parked) id + 1 = parkIndex ((w.st dst).parked) id := by
                simpa [hpList] using hcloser.1
              have hR' := Reachable.step w w' (.recvBulk dst) hR happ
              have hdebt' := call_debt_drop_index I w w' id dst (prog_src_reachable I N w' hR') hidx
              have hfuel := Nat.lt_of_lt_of_le hdebt' hdebt
              have hty := waiting_ty_step I (.recvBulk dst) w w' id happ
                (Or.inl ⟨dst, true, k, hph⟩) (Or.inl ⟨dst, true, k, hstay⟩)
              obtain ⟨acts, w2, hC, hrun, hR2, hnot, hwk⟩ :=
                ihf (callParkDebt I w' id dst) hfuel w' id dst k (height_same hs w w' id n hty hn)
                  hstay hR' (Nat.le_refl _)
              exact ⟨.recvBulk dst :: acts, w2,
                ChainRun.cons w (.recvBulk dst) w' acts hchain happ hC,
                by simp [runFrom, happ, hrun], hR2, hnot,
                prepend_work w w' w2 id (by simp [hstay, hph]) hwk⟩
        · have hR' := Reachable.step w w' (.recvBulk dst) hR happ
          have hty := waiting_ty_step I (.recvBulk dst) w w' id happ
            (Or.inl ⟨dst, true, k, hph⟩) (Or.inr ⟨dst, k, hgo⟩)
          exact finishReply w' [.recvBulk dst]
            (ChainRun.cons w (.recvBulk dst) w' [] hchain happ (ChainRun.nil w'))
            (by simp [runFrom, happ]) hR' hgo hty

theorem blocked_unblocks (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (_hA : Assumptions I)
    (N : Nat) (w : World) (hR : Reachable I N w) (id : InstId) (hB : Blocked w id)
    (hnotP : ¬ PurePeerEnd I.desc w id) :
    ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
      Reachable I N w' ∧ ¬ Blocked w' id := by
  obtain ⟨hs, hok⟩ := hG.ranked
  have hfull : ∀ n w id, heightOf hs (nodeAt w id) < n → Reachable I N w → Blocked w id →
      ¬ PurePeerEnd I.desc w id →
      ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
        Reachable I N w' ∧ ¬ Blocked w' id ∧
        work ((w'.st id).phase) < work ((w.st id).phase) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ihn =>
      intro w id hn hR hB hnotP
      cases hph : (w.st id).phase with
      | idle => simp [Blocked, hph] at hB
      | crashed => simp [Blocked, hph] at hB
      | run _ => simp [Blocked, hph] at hB
      | awaitEffect k =>
        have hfin : apply I (.finish id) w = some (setActor w id (proceed (w.st id) k)) := by
          simp [apply, finishWait, hph]
        obtain ⟨hnot, hwk⟩ := finish_unblocks I w _ id (by simpa [apply] using hfin) hB
        exact ⟨[.finish id], _, ChainRun.cons w (.finish id) _ [] (on_finish_self w id) hfin (ChainRun.nil _),
          by simp [runFrom, hfin], Reachable.step w _ (.finish id) hR hfin, hnot, by simpa [hph] using hwk⟩
      | awaitPeer k =>
        have hf : peerFinishable I.desc id = true := by
          cases hf : peerFinishable I.desc id with
          | true => rfl
          | false => exact False.elim (hnotP ⟨k, hph, hf⟩)
        have hfin : apply I (.finish id) w = some (setActor w id (proceed (w.st id) k)) := by
          simp [apply, finishWait, hph, hf]
        obtain ⟨hnot, hwk⟩ := finish_unblocks I w _ id (by simpa [apply] using hfin) hB
        exact ⟨[.finish id], _, ChainRun.cons w (.finish id) _ [] (on_finish_self w id) hfin (ChainRun.nil _),
          by simp [runFrom, hfin], Reachable.step w _ (.finish id) hR hfin, hnot, by simpa [hph] using hwk⟩
      | parked dst isCall k =>
        cases isCall with
        | false =>
          simpa [hph] using send_go I hG hL N hs hok n
            (fun m w id hm hlt hR hB hnot => ihn m hm w id hlt hR hB hnot)
            (sendDebt I w id dst) w id dst k hn hph hR (Nat.le_refl _)
        | true =>
          simpa [hph] using call_go I hG hL N hs hok n
            (fun m w id hm hlt hR hB hnot => ihn m hm w id hlt hR hB hnot)
            (callParkDebt I w id dst) w id dst k hn hph hR (Nat.le_refl _)
      | awaitReply dst k =>
        simpa [hph] using reply_go I hG hL N hs hok n
          (fun m w id hm hlt hR hB hnot => ihn m hm w id hlt hR hB hnot)
          (replyDebt I w id dst) w id dst k hn hph hR (Nat.le_refl _)
  obtain ⟨acts, w', hC, hrun, hR', hnot, _⟩ :=
    hfull (heightOf hs (nodeAt w id) + 1) w id (Nat.lt_succ_self _) hR hB hnotP
  exact ⟨acts, w', hC, hrun, hR', hnot⟩

/-- The chain stops when `id` is no longer blocked, or when `id` itself is a
pure untimed peer end. That end is legitimate: `finish` is disabled, and no
timed peer in the cohort can end it. It is not an interior wait. `peerFails`
rejects a blocking send or call into a pure untimed template, and a cohort
that contains a timed peer makes the waiter finishable, so the chain continues
through `blocked_unblocks`. -/
theorem blocked_chain (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    (N : Nat) (w : World) (hR : Reachable I N w) (id : InstId) (hB : Blocked w id) :
    ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
      Reachable I N w' ∧
      (¬ Blocked w' id ∨ ∃ s k, InChain w' id s ∧ (w'.st s).phase = .awaitPeer k ∧
        peerUntimed I.desc s = true ∧ peerFinishable I.desc s = false) := by
  by_cases hpure : PurePeerEnd I.desc w id
  · obtain ⟨k, hph, hf⟩ := hpure
    exact ⟨[], w, ChainRun.nil w, rfl, hR,
      Or.inr ⟨id, k, InChain.refl id, hph, untimed_of_silent I.desc id hf, hf⟩⟩
  · obtain ⟨acts, w', hC, hrun, hR', hnot⟩ :=
      blocked_unblocks I hG hL hA N w hR id hB hpure
    exact ⟨acts, w', hC, hrun, hR', Or.inl hnot⟩
end Deadlock
