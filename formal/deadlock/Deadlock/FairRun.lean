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
import Deadlock.Witness

set_option autoImplicit false

namespace Deadlock

/-- Ingress, spawn, and stutter are not demanded by fairness. A quiet peer is
allowed to stay silent, and the scheduler may idle once nothing forced is enabled. -/
theorem forced_env_free (id : InstId) (label template : String) :
    forced (.ingress id label) = false ∧ forced (.spawn template) = false ∧
      forced .stutter = false := by
  simp [forced]

theorem runtimeBusy_roster (I : Impl) (w : World) (hb : runtimeBusy I w = false) (id : InstId)
    (hid : id ∈ w.roster) :
    receiveBulk I w id = none ∧ receivePrio I w id = none ∧
      execHead I w id = none ∧ finishWait I w id = none := by
  have hall : ∀ x ∈ w.roster,
      ((receiveBulk I w x).isSome || (receivePrio I w x).isSome ||
        (execHead I w x).isSome || (finishWait I w x).isSome) = false := by
    simpa [runtimeBusy] using (List.any_eq_false.mp hb)
  have hfalse := hall id hid
  rw [Bool.or_eq_false_iff] at hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  rcases hfalse with ⟨⟨⟨hr, hp⟩, he⟩, hf⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : receiveBulk I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hr
  · cases h : receivePrio I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hp
  · cases h : execHead I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at he
  · cases h : finishWait I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hf

theorem quiet_no_forced (I : Impl) (w : World)
    (hoff : ∀ id, id ∉ w.roster → (w.st id).life ≠ .alive ∧ (w.st id).phase = .idle)
    (hb : runtimeBusy I w = false) (a : Action) (hf : forced a = true) : ¬ Enabled I w a := by
  cases a with
  | spawn _ => simp [forced] at hf
  | ingress _ _ => simp [forced] at hf
  | stutter => simp [forced] at hf
  | recvBulk s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      simp [Enabled, apply, receiveBulk, hdead] at hen
  | recvPrio s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      cases hp : (w.st s).prio with
      | nil => simp [Enabled, apply, receivePrio, hp] at hen
      | cons _ _ => simp [Enabled, apply, receivePrio, hp, hdead] at hen
  | exec s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.2.1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      simp [Enabled, apply, execHead, hdead] at hen
  | finish s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.2.2
      simp [Enabled, apply, hnone] at hen
    · have hidle := (hoff s hid).2
      simp [Enabled, apply, finishWait, hidle] at hen

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
    omega
  | succ i ih =>
    by_cases hle : demoActs.length ≤ i
    · obtain ⟨heq, hb⟩ := ih hle
      have hact : nthAct demoActs i = .stutter := by simp [nthAct, Nat.not_lt_of_le hle]
      simp [replayCfg, hact, apply, hb, heq, Option.getD]
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

end Deadlock
