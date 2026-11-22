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

import Deadlock.Local
import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

/-! A pool admit past `N`, and the live-debt sum that bound was protecting.

`N` is the root population. `W` is a core-supervised pool of two slots, so
its population is `slots`, not `N`. At `N = 1` the `Go` program spawns `W`
twice. Both children stay alive. Each idle child owes one self-ingress, so
the live sum into `W` is 2 while `(totalOcc "W").eval 1` is 1 and Lemma 1
holds. Each child's own token reserve still fits. -/

private def base (name : String) : Template where
  name := name
  multiplicity := .one
  capacity := { a := 1, b := 1 }
  priorityCapacity := { a := 0, b := 8 }
  priorityBound := { a := 0, b := 4 }
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

private def countW : Template :=
  { base "W" with
    multiplicity := .perPeer
    slots := 2
    supervisor := some "C"
    tombstone := "dead/W"
    capacity := { a := 1, b := 0 } }

private def countC : Template :=
  { base "C" with
    states := ["boot", "idle"]
    initial := "boot"
    capacity := { a := 0, b := 2 } }

private def countIngC : Edge where
  src := "C"
  srcState := "boot"
  dst := "C"
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := "Go"
  scope := .intra
  occupancy := { a := 0, b := 1 }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat 1)
  cell := .none

private def countIngIdle : Edge :=
  { countIngC with srcState := "idle" }

private def countIngW : Edge where
  src := "W"
  srcState := "idle"
  dst := "W"
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := "Go"
  scope := .intra
  occupancy := { a := 1, b := 0 }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some { a := 1, b := 0 }
  cell := .none

private def countStep (template src dst label : String) : CompatStep where
  template := template
  fromState := src
  toState := dst
  label := label

private def countDesc : Description where
  name := "spawn-count"
  freshNames := true
  templates := [countC, countW]
  edges := [countIngC, countIngIdle, countIngW]
  compatibility := .all
  steps :=
    [ countStep "C" "boot" "idle" "Go"
    , countStep "C" "idle" "idle" "Go"
    , countStep "C" "boot" "boot" "dead/W"
    , countStep "C" "idle" "idle" "dead/W"
    , countStep "W" "idle" "idle" "Go" ]

private def countGo (src dst : String) (program : List Eff) : Transition where
  template := "C"
  fromState := src
  toState := dst
  label := "Go"
  acceptsCall := false
  release := 1
  program := program

private def countTomb (st : String) : Transition where
  template := "C"
  fromState := st
  toState := st
  label := "dead/W"
  acceptsCall := false
  release := 1
  program := []

private def countImpl : Impl where
  desc := countDesc
  transitions :=
    [ countGo "boot" "idle" [.spawn "W", .spawn "W"]
    , countGo "idle" "idle" []
    , countTomb "boot"
    , countTomb "idle"
    , { template := "W", fromState := "idle", label := "Go", toState := "idle",
        acceptsCall := false, release := 1, program := [] } ]

private def countRun (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply countImpl a)) (some (initWorld countImpl 1))

private def countCId : InstId := .core "C"
private def countW0 : InstId := .peer "W" 0 0
private def countW1 : InstId := .peer "W" 1 0

private def countFirst : List Action :=
  [.ingress countCId "Go", .recvBulk countCId, .exec countCId]

private def countActs : List Action :=
  countFirst ++ [.exec countCId]

private def countAt (acts : List Action) (k : Nat) (alive : Bool) : Bool :=
  match countRun acts with
  | none => false
  | some w =>
    !w.crashed && decide (w.N = 1) && decide (aliveCount w "W" = k) &&
      (w.st countW0).life == .alive &&
        ((w.st countW1).life == .alive) == alive

theorem count_check : checkBool countDesc = true := by
  decide

theorem count_local : localOkB countImpl = true := by
  decide

/-- After the first spawn, one child is alive and the count is `N`. -/
theorem count_at_bound : countAt countFirst 1 false = true := by
  decide

/-- The next exec admits another generation. The count is no longer below `N`. -/
theorem count_past_bound : countAt countActs 2 true = true := by
  decide

/-- Live per-instance debt summed over both children, against the affine total.
Each child's own tokens still cover `tokenHold`. Lemma 1 holds for `W`. -/
private def countSum : Bool :=
  match countRun countActs with
  | none => false
  | some w =>
    let owed := debt countDesc "W" (w.st countW0).typestate "W" +
      debt countDesc "W" (w.st countW1).typestate "W"
    let bound := (totalOcc countDesc "W").eval w.N
    decide (owed = 2) && decide (bound = 1) && decide (bound < owed) &&
      decide (l1 countDesc "W" = true) &&
      decide (capBulk countDesc w.N countW0 = 1) &&
      decide (budget countDesc "W" "W" = 1) &&
      decide ((w.st countW0).tokens "W" = 1) &&
      decide ((w.st countW1).tokens "W" = 1) &&
      decide (queuedFromKey w "W" 0 "W" = 0) &&
      decide (queuedFromKey w "W" 1 "W" = 0) &&
      decide (tokenHold countDesc "W" "W" (w.st countW0) = 0) &&
      decide (tokenHold countDesc "W" "W" (w.st countW1) = 0)

theorem count_live_sum : countSum = true := by
  decide

end Deadlock
