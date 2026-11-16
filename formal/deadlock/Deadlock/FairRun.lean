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

/-- An id that the initial roster does not name is the absent actor. -/
theorem off_idle_init (I : Impl) (N : Nat) (id : InstId) (h : id ∉ (initWorld I N).roster) :
    ((initWorld I N).st id).phase = .idle ∧ ((initWorld I N).st id).life ≠ .alive := by
  refine ⟨init_phase I N id, ?_⟩
  rw [init_roster] at h
  rw [init_base_st]
  split
  · next hc => exact False.elim (h (List.contains_iff_mem.mp hc))
  · simp [absentActor]

/-- A step does not wake an actor that is off the roster. Spawn puts the new id
on the roster, and every other step leaves that actor idle and not alive. -/
theorem off_idle_step (I : Impl) (a : Action) (w w' : World)
    (hoff : ∀ id, id ∉ w.roster → (w.st id).phase = .idle ∧ (w.st id).life ≠ .alive)
    (h : apply I a w = some w') (s : InstId) (hs : s ∉ w'.roster) :
    (w'.st s).phase = .idle ∧ (w'.st s).life ≠ .alive := by
  cases a with
  | stutter =>
    have heq := stutter_unchanged I w w' h
    subst heq
    exact hoff s hs
  | ingress dst label =>
    have hkeep := ingress_phase I w w' dst label s (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hkeep.2.2.2.2.1] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    refine ⟨hkeep.1.trans hidle, ?_⟩
    rw [hkeep.2.1]
    exact hdead
  | finish id =>
    have hr := finish_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    obtain ⟨k, hph, hw⟩ := finish_proceed I w w' id (by simpa [apply] using h)
    have hne : s ≠ id := by
      intro heq
      rcases hph with hph | hph
      · rw [← heq, hidle] at hph
        cases hph
      · rw [← heq, hidle] at hph
        cases hph
    rw [hw]
    refine ⟨?_, ?_⟩
    · simp [setActor, hne, hidle]
    · simp [setActor, hne]
      exact hdead
  | recvPrio id =>
    have hr := prio_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    have hrecv : receivePrio I w id = some w' := by simpa [apply] using h
    unfold receivePrio at hrecv
    cases hp : (w.st id).prio with
    | nil => simp [hp] at hrecv
    | cons m ms =>
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hp, hready] at hrecv
      · simp [hp, hready] at hrecv
        split at hrecv
        · cases hrecv
        · next w1 a1 hdel =>
          cases hrecv
          have hlid : (w.st id).life = .alive := by
            by_cases hl : (w.st id).life = .alive
            · exact hl
            · exact False.elim (hready (Or.inl hl))
          have hne : s ≠ id := by
            intro heq
            exact hdead (by simpa [heq] using hlid)
          have hst := deliver_st I w id ({ (w.st id) with prio := ms }) m w1 a1 s hdel
          refine ⟨?_, ?_⟩
          · simp [setActor, hne, hst, hidle]
          · simp [setActor, hne, hst]
            exact hdead
  | recvBulk id =>
    have hr := bulk_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    have hrecv : receiveBulk I w id = some w' := by simpa [apply] using h
    have hlid : (w.st id).life = .alive := by
      unfold receiveBulk at hrecv
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hready] at hrecv
      · by_cases hl : (w.st id).life = .alive
        · exact hl
        · exact False.elim (hready (Or.inl hl))
    have hne : s ≠ id := by
      intro heq
      exact hdead (by simpa [heq] using hlid)
    have hnpark : ∀ d c k, (w.st s).phase ≠ .parked d c k := by
      intro d c k hbad
      rw [hidle] at hbad
      cases hbad
    have hkeep := bulk_keeps_quiet I w id w' s hne hnpark hrecv
    refine ⟨hkeep.1.trans hidle, ?_⟩
    rw [hkeep.2]
    exact hdead
  | exec id =>
    have hr := head_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    simp only [apply] at h
    unfold execHead at h
    by_cases hlid : (w.st id).life = .alive
    · simp [hlid] at h
      cases hph : (w.st id).phase with
      | run k =>
        simp [hph] at h
        cases h
        have hne : s ≠ id := by
          intro heq
          exact hdead (by simpa [heq] using hlid)
        have hnpark : ∀ d c ck, (w.st s).phase ≠ .parked d c ck := by
          intro d c ck hbad
          rw [hidle] at hbad
          cases hbad
        have hnreply : ∀ d ck, (w.st s).phase ≠ .awaitReply d ck := by
          intro d ck hbad
          rw [hidle] at hbad
          cases hbad
        have hkeep := exec_keeps_quiet I w id (w.st id) k s hne hnpark hnreply
        refine ⟨hkeep.1.trans hidle, ?_⟩
        rw [hkeep.2]
        exact hdead
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlid] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    cases ht : templateOf I.desc template with
    | none => simp [ht] at h
    | some t =>
      by_cases hgo : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
      · simp [ht, hgo] at h
        cases h
        simp only [readCells_st]
        by_cases hfresh : s = InstId.peer template (w.nextIx template)
        · exfalso
          apply hs
          simp [readCells_roster, setActor, hfresh, List.mem_append]
        · have hold : s ∉ w.roster := by
            intro hin
            apply hs
            simp [readCells_roster, setActor, List.mem_append, hin]
          obtain ⟨hidle, hdead⟩ := hoff s hold
          refine ⟨?_, ?_⟩
          · simpa [setActor, hfresh] using hidle
          · simpa [setActor, hfresh] using hdead
      · simp [ht, hgo] at h

theorem off_idle_reachable (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (h : id ∉ w.roster) :
    (w.st id).phase = .idle ∧ (w.st id).life ≠ .alive := by
  induction hR generalizing id with
  | init => exact off_idle_init I N id h
  | step w w' a _ ha ih =>
    exact off_idle_step I a w w' ih ha id h

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

end Deadlock
