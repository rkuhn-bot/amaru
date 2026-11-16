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
set_option maxRecDepth 100000

namespace Deadlock

/-! The old `∃ act, Enabled` reading of progress is witnessed by an ingress that
is not on the blocked actor's wait chain. A mutual park of A and B is rejected
by the checker. -/

def ing (t label : String) : Edge where
  src := t
  srcState := "idle"
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := .ofNat 1
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat 1)
  cell := .none

def ctr (t label : String) (p : List Eff) : Transition :=
  { template := t, fromState := "idle", label := label, program := p, toState := "idle",
    acceptsCall := false, release := 1 }

def cycDesc : Description where
  name := "cycle-plus-clock"
  freshNames := true
  templates := [tpl "A" 1 ["idle"] "idle" false, tpl "B" 1 ["idle"] "idle" false,
                tpl "C" 1 ["idle"] "idle" true]
  edges := [ing "A" "Go", ing "B" "Go", ing "C" "Tick",
            sendEdge "A" "idle" "B" "M" 2, sendEdge "B" "idle" "A" "M" 2]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "idle", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Go" },
            { template := "B", fromState := "idle", toState := "idle", label := "M" },
            { template := "C", fromState := "idle", toState := "idle", label := "Tick" }]

def cycImpl : Impl where
  desc := cycDesc
  transitions := [ctr "A" "Go" [.send "B" "M" 0, .send "B" "M" 0], ctr "A" "M" [],
                  ctr "B" "Go" [.send "A" "M" 0, .send "A" "M" 0], ctr "B" "M" [],
                  ctr "C" "Tick" []]

def coreA : InstId := .core "A"
def coreB : InstId := .core "B"
def coreC : InstId := .core "C"

theorem cycle_not_checked : checkBool cycDesc = false := by decide

def cycActs : List Action :=
  [.ingress coreA "Go", .ingress coreB "Go", .recvBulk coreA, .recvBulk coreB,
   .exec coreA, .exec coreB, .exec coreA, .exec coreB]

def afterCyc (acts : List Action) : Option World :=
  runFrom cycImpl (some (initWorld cycImpl 0)) acts

def parkTag (w : Option World) (x : InstId) : Nat :=
  match w with
  | none => 0
  | some w => match (w.st x).phase with
    | .parked d false _ => if d = coreA then 10 else if d = coreB then 11 else 1
    | .idle => 2
    | .run _ => 3
    | _ => 0

theorem mutual_park : parkTag (afterCyc cycActs) coreA = 11 ∧ parkTag (afterCyc cycActs) coreB = 10 := by
  decide

theorem clock_enabled :
    ((afterCyc cycActs).bind (apply cycImpl (.ingress coreC "Tick"))).isSome = true := by
  decide

/-- A and B are parked on each other, the world is reachable, and `ingress C`
is enabled. That ingress is not on A's chain, so it does not satisfy `OnChain`. -/
theorem cycle_off_chain : ∃ w, afterCyc cycActs = some w ∧ Reachable cycImpl 0 w ∧
    Blocked w coreA ∧ Enabled cycImpl w (.ingress coreC "Tick") ∧
    ¬ OnChain w coreA (.ingress coreC "Tick") := by
  have hm := mutual_park
  have hc := clock_enabled
  cases hw : afterCyc cycActs with
  | none => simp [parkTag, hw] at hm
  | some w =>
    have hR := run_reachable cycImpl 0 (initWorld cycImpl 0) Reachable.init cycActs w
      (by simpa [afterCyc] using hw)
    refine ⟨w, rfl, hR, ?_, ?_, ingress_off_chain w coreA coreC "Tick"⟩
    · simp only [parkTag, hw] at hm
      refine ⟨?_, ?_⟩
      · have hl : ((afterCyc cycActs).map (fun w => decide ((w.st coreA).life = .alive))) = some true := by
          decide
        simp [hw] at hl
        exact hl
      · split at hm <;> simp_all
    · simp only [hw, Option.bind] at hc
      intro hnone
      simp [hnone] at hc

def parkClockDesc : Description :=
  { parkDesc with
    templates := parkDesc.templates ++ [tpl "clock" 1 ["idle"] "idle" true]
    edges := parkDesc.edges ++ [ing "clock" "Tick"]
    steps := parkDesc.steps ++
      [{ template := "clock", fromState := "idle", toState := "idle", label := "Tick" }] }

def parkClockImpl : Impl where
  desc := parkClockDesc
  transitions := parkImpl.transitions ++ [ctr "clock" "Tick" []]

theorem clock_graph : checkBool parkClockDesc = true := by decide

theorem clock_local : localOkB parkClockImpl = true := by decide

theorem clock_ingress_enabled :
    ((runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs).bind
      (apply parkClockImpl (.ingress (.core "clock") "Tick"))).isSome = true := by decide

theorem clock_producer_parked :
    (match runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs with
     | some w => phaseTag ((w.st producerId).phase)
     | none => 0) = 1 := by decide

/-- A checked world in which the producer is parked and an unrelated ingress is
enabled. The ingress is not on the producer's chain. -/
theorem checked_off_chain : ∃ w, Reachable parkClockImpl 0 w ∧ Blocked w producerId ∧
    Enabled parkClockImpl w (.ingress (.core "clock") "Tick") ∧
    ¬ OnChain w producerId (.ingress (.core "clock") "Tick") ∧
    GraphOk parkClockDesc ∧ LocalOk parkClockImpl := by
  have hg : GraphOk parkClockDesc := checkBool_sound parkClockDesc clock_graph
  have hl : LocalOk parkClockImpl := clock_local
  have htag := clock_producer_parked
  have hen := clock_ingress_enabled
  cases hw : runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs with
  | none => simp [hw] at htag
  | some w =>
    have hR := run_reachable parkClockImpl 0 (initWorld parkClockImpl 0) Reachable.init parkActs w hw
    refine ⟨w, hR, ?_, ?_, ingress_off_chain w producerId (.core "clock") "Tick", hg, hl⟩
    · simp [phaseTag, hw] at htag
      cases hph : (w.st producerId).phase with
      | parked _ _ _ =>
        have hlfe : ((w.st producerId).life = .alive) := by
          have hdec : decide ((w.st producerId).life = .alive) = true := by
            have hlife :
                (match runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs with
                 | some w => decide ((w.st producerId).life = .alive)
                 | none => false) = true := by decide
            simpa [hw] using hlife
          simpa using hdec
        exact ⟨hlfe, by simp [hph]⟩
      | idle => simp [phaseTag, hph] at htag
      | run _ => simp [phaseTag, hph] at htag
      | awaitReply _ _ => simp [phaseTag, hph] at htag
      | awaitEffect _ => simp [phaseTag, hph] at htag
      | awaitPeer _ => simp [phaseTag, hph] at htag
      | crashed => simp [phaseTag, hph] at htag
    · simp [hw, Option.bind] at hen
      intro hnone
      simp [hnone] at hen

end Deadlock
