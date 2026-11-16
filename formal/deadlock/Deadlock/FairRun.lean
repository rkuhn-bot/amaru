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
import Deadlock.Deliver

set_option autoImplicit false

namespace Deadlock

/-- Ingress, spawn, and stutter are not demanded by fairness. A quiet peer is
allowed to stay silent, and the scheduler may idle once nothing forced is enabled. -/
theorem forced_env_free (id : InstId) (label template : String) :
    forced (.ingress id label) = false ∧ forced (.spawn template) = false ∧
      forced .stutter = false := by
  simp [forced]

/-- A finite schedule, then stutter. `cfg` repeats the last world once the
schedule ends and `runtimeBusy` is false. -/
def nthAct (acts : List Action) (i : Nat) : Action :=
  if h : i < acts.length then acts[i] else .stutter

def replayCfg (I : Impl) (acts : List Action) : Nat → World
  | 0 => initWorld I 0
  | n + 1 => (apply I (nthAct acts n) (replayCfg I acts n)).getD (replayCfg I acts n)

theorem replay_valid (I : Impl) (acts : List Action)
    (hok : ∀ i, (apply I (nthAct acts i) (replayCfg I acts i)).isSome = true) (i : Nat) :
    apply I (nthAct acts i) (replayCfg I acts i) = some (replayCfg I acts (i + 1)) := by
  have hs := hok i
  cases h : apply I (nthAct acts i) (replayCfg I acts i) with
  | none => simp [h] at hs
  | some w => simp [replayCfg, h, Option.getD]

def cellFlags : CellFlags where
  singleWriter := true
  orderMonotone := true
  noPerMessageObligation := true
  visibility := true
  readPoints := true
  idempotent := true
  dirtyBit := true

def demoDesc : Description where
  name := "fair-run"
  freshNames := true
  templates :=
    [tpl "prod" 4 ["idle", "busy"] "idle" true,
     tpl "sink" 1 ["idle"] "idle" false,
     tpl "caller" 4 ["idle", "wait"] "idle" true,
     tpl "rep" 4 ["idle"] "idle" false,
     tpl "writer" 4 ["idle"] "idle" true,
     tpl "reader" 4 ["idle"] "idle" true]
  edges :=
    [{ (sendEdge "prod" "idle" "prod" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     { (sendEdge "prod" "busy" "prod" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     sendEdge "prod" "busy" "sink" "M" 2,
     { (sendEdge "caller" "idle" "caller" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     { (sendEdge "caller" "wait" "caller" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     { (sendEdge "caller" "wait" "rep" "Q" 1) with effect := .call, repliesInDequeue := true },
     { (sendEdge "writer" "idle" "writer" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     { (sendEdge "writer" "idle" "reader" "Flag" 1) with
        kind := .nonBlocking, reliability := .superseding, effect := .cell, cell := cellFlags }]
  compatibility := .all
  steps :=
    [{ template := "prod", fromState := "idle", toState := "busy", label := "Go" },
     { template := "prod", fromState := "busy", toState := "busy", label := "Go" },
     { template := "sink", fromState := "idle", toState := "idle", label := "M" },
     { template := "caller", fromState := "idle", toState := "wait", label := "Go" },
     { template := "caller", fromState := "wait", toState := "wait", label := "Go" },
     { template := "rep", fromState := "idle", toState := "idle", label := "Q" },
     { template := "writer", fromState := "idle", toState := "idle", label := "Go" },
     { template := "reader", fromState := "idle", toState := "idle", label := "Flag" }]

def demoTr (template fromState label toState : String) (program : List Eff) (call : Bool) : Transition where
  template := template
  fromState := fromState
  label := label
  program := program
  toState := toState
  acceptsCall := call
  release := 1

def demoImpl : Impl where
  desc := demoDesc
  transitions :=
    [demoTr "prod" "idle" "Go" "busy" [.send "sink" "M" 0, .send "sink" "M" 0] false,
     demoTr "prod" "busy" "Go" "busy" [] false,
     demoTr "sink" "idle" "M" "idle" [] false,
     demoTr "caller" "idle" "Go" "wait" [.call "rep" "Q" 0] false,
     demoTr "caller" "wait" "Go" "wait" [] false,
     demoTr "rep" "idle" "Q" "idle" [.reply] true,
     demoTr "writer" "idle" "Go" "idle" [.cell "reader" "Flag" 1] false,
     demoTr "reader" "idle" "Flag" "idle" [] false]

theorem demo_graph : checkBool demoDesc = true := by decide

theorem demo_local : localOkB demoImpl = true := by decide

theorem demo_graph_ok : GraphOk demoDesc := checkBool_sound demoDesc demo_graph

theorem demo_local_ok : LocalOk demoImpl := demo_local

def prodId : InstId := .core "prod"
def sinkIdD : InstId := .core "sink"
def callerId : InstId := .core "caller"
def repId : InstId := .core "rep"
def writerId : InstId := .core "writer"
def readerId : InstId := .core "reader"

def demoActs : List Action :=
  [.ingress prodId "Go", .recvBulk prodId, .exec prodId, .exec prodId,
   .recvBulk sinkIdD, .recvBulk sinkIdD,
   .ingress callerId "Go", .recvBulk callerId, .exec callerId,
   .recvBulk repId, .exec repId,
   .ingress writerId "Go", .recvBulk writerId, .exec writerId,
   .recvPrio readerId]

def phaseCode (p : Phase) : Nat :=
  match p with
  | .parked _ false _ => 1
  | .awaitReply _ _ => 2
  | .idle => 3
  | .run _ => 4
  | _ => 0

def demoCode (i : Nat) (id : InstId) : Nat :=
  phaseCode ((replayCfg demoImpl demoActs i).st id).phase

theorem demo_parked : demoCode 4 prodId = 1 := by decide

theorem demo_awaiting : demoCode 9 callerId = 2 := by decide

theorem demo_answered : demoCode 11 callerId = 3 := by decide

theorem demo_woken : ((replayCfg demoImpl demoActs 15).st readerId).prio = [] ∧
    ((replayCfg demoImpl demoActs 14).st readerId).prio ≠ [] := by decide

theorem demo_roster : coreRoster demoDesc = [prodId, sinkIdD, callerId, repId, writerId, readerId] := by
  decide

theorem demo_not_core (id : InstId) (hp : id ≠ prodId) (hs : id ≠ sinkIdD) (hc : id ≠ callerId)
    (hr : id ≠ repId) (hw : id ≠ writerId) (hread : id ≠ readerId) :
    id ∉ coreRoster demoDesc := by
  intro hmem
  rw [demo_roster] at hmem
  simp [List.mem_cons, List.mem_singleton, hp, hs, hc, hr, hw, hread] at hmem

theorem demo_quiet : runtimeBusy demoImpl (replayCfg demoImpl demoActs demoActs.length) = false := by
  decide

def demoStepsOk : Bool :=
  (List.range (demoActs.length + 1)).all fun i =>
    (apply demoImpl (nthAct demoActs i) (replayCfg demoImpl demoActs i)).isSome

theorem demo_steps_ok : demoStepsOk = true := by decide

theorem demo_step_before (i : Nat) (hi : i < demoActs.length + 1) :
    (apply demoImpl (nthAct demoActs i) (replayCfg demoImpl demoActs i)).isSome = true := by
  have hmem : i ∈ List.range (demoActs.length + 1) := List.mem_range.mpr hi
  have hall : ∀ j ∈ List.range (demoActs.length + 1),
      (apply demoImpl (nthAct demoActs j) (replayCfg demoImpl demoActs j)).isSome = true := by
    simpa [demoStepsOk, List.all_eq_true] using demo_steps_ok
  exact hall i hmem

theorem demo_tail (i : Nat) (hi : demoActs.length ≤ i) :
    replayCfg demoImpl demoActs i = replayCfg demoImpl demoActs demoActs.length ∧
      runtimeBusy demoImpl (replayCfg demoImpl demoActs i) = false := by
  induction i with
  | zero =>
    simp [demoActs] at hi
  | succ i ih =>
    by_cases hle : demoActs.length ≤ i
    · obtain ⟨heq, hb⟩ := ih hle
      have hact : nthAct demoActs i = .stutter := by simp [nthAct, Nat.not_lt_of_le hle]
      have hb' : runtimeBusy demoImpl (replayCfg demoImpl demoActs demoActs.length) = false := by
        rw [← heq]
        exact hb
      rw [replayCfg, hact, apply, heq, hb']
      simp [Option.getD, Bool.false_eq_true, hb']
    · have heq : i + 1 = demoActs.length := by omega
      simpa [heq] using demo_quiet

theorem demo_is_some (i : Nat) :
    (apply demoImpl (nthAct demoActs i) (replayCfg demoImpl demoActs i)).isSome = true := by
  by_cases hi : i < demoActs.length + 1
  · exact demo_step_before i hi
  · have hle : demoActs.length ≤ i := by omega
    obtain ⟨heq, hb⟩ := demo_tail i hle
    simp [nthAct, Nat.not_lt_of_le hle, apply, hb]

def demoRun : Run demoImpl 0 where
  cfg := replayCfg demoImpl demoActs
  act := nthAct demoActs
  startN := rfl
  start := rfl
  valid := replay_valid demoImpl demoActs demo_is_some

/-- The quiet demo trace is a finite execution: it stops when `runtimeBusy` is false. -/
def demoExec : FinExec demoImpl 0 where
  cfg := replayCfg demoImpl demoActs
  act := nthAct demoActs
  len := demoActs.length
  start := rfl
  valid := fun i _ => replay_valid demoImpl demoActs demo_is_some i
  maximal := demo_quiet

theorem demo_fin_exec : Nonempty (FinExec demoImpl 0) :=
  ⟨demoExec⟩

/-- After the last real step the run only stutters, so no forced action stays
enabled. Bulk and priority hypotheses fail for the same reason: a quiet world
does not enable them. -/
theorem demo_fair : Fair demoRun := by
  have hquiet (j : Nat) (hj : demoActs.length ≤ j) :
      runtimeBusy demoImpl (demoRun.cfg j) = false ∧
        (∀ id, id ∉ (demoRun.cfg j).roster →
          ((demoRun.cfg j).st id).phase = .idle ∧ ((demoRun.cfg j).st id).life ≠ .alive) := by
    obtain ⟨heq, hb⟩ := demo_tail j hj
    refine ⟨hb, ?_⟩
    intro id hid
    have hR := cfg_reachable demoRun j
    exact off_idle_reachable demoImpl 0 (demoRun.cfg j) hR id hid
  refine ⟨?_, ?_, ?_⟩
  · intro a i hf hen
    let j := Nat.max i demoActs.length
    have hj : demoActs.length ≤ j := Nat.le_max_right _ _
    have hle : i ≤ j := Nat.le_max_left _ _
    obtain ⟨hb, hoff⟩ := hquiet j hj
    exact False.elim (quiet_no_forced demoImpl (demoRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb a hf (hen j hle))
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i demoActs.length)
    have hlen : demoActs.length ≤ j := Nat.le_trans (Nat.le_max_right _ _) hj
    obtain ⟨hb, hoff⟩ := hquiet j hlen
    exact False.elim (quiet_no_forced demoImpl (demoRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb (.recvBulk s) rfl hen)
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i demoActs.length)
    have hlen : demoActs.length ≤ j := Nat.le_trans (Nat.le_max_right _ _) hj
    obtain ⟨hb, hoff⟩ := hquiet j hlen
    exact False.elim (quiet_no_forced demoImpl (demoRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb (.recvPrio s) rfl hen)

/-- A terminable actor accepts a reliable message and then kills itself.
The message is in the box at step 5 and is gone after the killing `exec`.
This description is not `LocalOk`: a checked graph does not put reliable mail
on a template that can die. -/
def lossTpl : Template := { tpl "loss" 4 ["idle"] "idle" true with terminable := true }

def lossDesc : Description where
  name := "loss-run"
  freshNames := true
  templates := [tpl "prod" 4 ["idle", "busy"] "idle" true, lossTpl]
  edges :=
    [{ (sendEdge "prod" "idle" "prod" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) }]
  compatibility := .all
  steps := [{ template := "prod", fromState := "idle", toState := "busy", label := "Go" }]

def lossImpl : Impl where
  desc := lossDesc
  transitions :=
    [demoTr "prod" "idle" "Go" "busy" [.send "loss" "Start" 0] false,
     demoTr "loss" "idle" "Start" "idle" [.send "loss" "M" 0, .terminate] false]

def lossProd : InstId := .core "prod"
def lossId : InstId := .core "loss"

def lossActs : List Action :=
  [.ingress lossProd "Go", .recvBulk lossProd, .exec lossProd,
   .recvBulk lossId, .exec lossId, .exec lossId]

def lossHeld : Bool :=
  match ((replayCfg lossImpl lossActs 5).st lossId).box with
  | m :: _ => m.reliable
  | [] => false

def lossStepsOk : Bool :=
  (List.range (lossActs.length + 1)).all fun i =>
    (apply lossImpl (nthAct lossActs i) (replayCfg lossImpl lossActs i)).isSome

theorem loss_steps_ok : lossStepsOk = true := by decide

theorem loss_step_before (i : Nat) (hi : i < lossActs.length + 1) :
    (apply lossImpl (nthAct lossActs i) (replayCfg lossImpl lossActs i)).isSome = true := by
  have hmem : i ∈ List.range (lossActs.length + 1) := List.mem_range.mpr hi
  have hall : ∀ j ∈ List.range (lossActs.length + 1),
      (apply lossImpl (nthAct lossActs j) (replayCfg lossImpl lossActs j)).isSome = true := by
    simpa [lossStepsOk, List.all_eq_true] using loss_steps_ok
  exact hall i hmem

theorem loss_quiet : runtimeBusy lossImpl (replayCfg lossImpl lossActs lossActs.length) = false := by
  decide

theorem loss_held : lossHeld = true := by decide

theorem loss_tail (i : Nat) (hi : lossActs.length ≤ i) :
    replayCfg lossImpl lossActs i = replayCfg lossImpl lossActs lossActs.length ∧
      runtimeBusy lossImpl (replayCfg lossImpl lossActs i) = false := by
  induction i with
  | zero =>
    simp [lossActs] at hi
  | succ i ih =>
    by_cases hle : lossActs.length ≤ i
    · obtain ⟨heq, hb⟩ := ih hle
      have hact : nthAct lossActs i = .stutter := by simp [nthAct, Nat.not_lt_of_le hle]
      have hb' : runtimeBusy lossImpl (replayCfg lossImpl lossActs lossActs.length) = false := by
        rw [← heq]
        exact hb
      rw [replayCfg, hact, apply, heq, hb']
      simp [Option.getD, Bool.false_eq_true, hb']
    · have heq : i + 1 = lossActs.length := by omega
      simpa [heq] using loss_quiet

theorem loss_is_some (i : Nat) :
    (apply lossImpl (nthAct lossActs i) (replayCfg lossImpl lossActs i)).isSome = true := by
  by_cases hi : i < lossActs.length + 1
  · exact loss_step_before i hi
  · have hle : lossActs.length ≤ i := by omega
    obtain ⟨heq, hb⟩ := loss_tail i hle
    simp [nthAct, Nat.not_lt_of_le hle, apply, hb]

def lossRun : Run lossImpl 0 where
  cfg := replayCfg lossImpl lossActs
  act := nthAct lossActs
  startN := rfl
  start := rfl
  valid := replay_valid lossImpl lossActs loss_is_some

theorem loss_act_not_recv (j : Nat) (hj : 5 ≤ j) : nthAct lossActs j ≠ .recvBulk lossId := by
  by_cases hlt : j < lossActs.length
  · have hj5 : j = 5 := by
      simp [lossActs] at hlt
      omega
    simp [hj5, nthAct, lossActs]
  · simp [nthAct, hlt]

/-- The killing run is fair: after the mailbox is cleared, nothing forced stays enabled. -/
theorem loss_fair : Fair lossRun := by
  have hquiet (j : Nat) (hj : lossActs.length ≤ j) :
      runtimeBusy lossImpl (lossRun.cfg j) = false ∧
        (∀ id, id ∉ (lossRun.cfg j).roster →
          ((lossRun.cfg j).st id).phase = .idle ∧ ((lossRun.cfg j).st id).life ≠ .alive) := by
    obtain ⟨heq, hb⟩ := loss_tail j hj
    refine ⟨hb, ?_⟩
    intro id hid
    have hR := cfg_reachable lossRun j
    exact off_idle_reachable lossImpl 0 (lossRun.cfg j) hR id hid
  refine ⟨?_, ?_, ?_⟩
  · intro a i hf hen
    let j := Nat.max i lossActs.length
    have hj : lossActs.length ≤ j := Nat.le_max_right _ _
    have hle : i ≤ j := Nat.le_max_left _ _
    obtain ⟨hb, hoff⟩ := hquiet j hj
    exact False.elim (quiet_no_forced lossImpl (lossRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb a hf (hen j hle))
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i lossActs.length)
    have hlen : lossActs.length ≤ j := Nat.le_trans (Nat.le_max_right _ _) hj
    obtain ⟨hb, hoff⟩ := hquiet j hlen
    exact False.elim (quiet_no_forced lossImpl (lossRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb (.recvBulk s) rfl hen)
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i lossActs.length)
    have hlen : lossActs.length ≤ j := Nat.le_trans (Nat.le_max_right _ _) hj
    obtain ⟨hb, hoff⟩ := hquiet j hlen
    exact False.elim (quiet_no_forced lossImpl (lossRun.cfg j)
      (fun id hid => And.intro (hoff id hid).2 (hoff id hid).1) hb (.recvPrio s) rfl hen)

theorem loss_not_delivered : ¬ Delivered lossRun := by
  intro hD
  have hheld := loss_held
  cases hbox : ((replayCfg lossImpl lossActs 5).st lossId).box with
  | nil => simp [lossHeld, hbox] at hheld
  | cons m ms =>
    have hr : m.reliable = true := by
      simp [lossHeld, hbox] at hheld
      exact hheld
    obtain ⟨j, hj, hact, _⟩ := hD.1 5 lossId m (by simp [lossRun, hbox]) hr
    exact loss_act_not_recv j hj (by simpa [lossRun] using hact)

end Deadlock
