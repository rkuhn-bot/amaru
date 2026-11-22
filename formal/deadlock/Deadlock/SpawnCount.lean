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

/-! A pool admit at `aliveCount = N`.

`W` has two slots under core `C`. `N = 1`. The `Go` program spawns `W`
twice and does not abort. The first exec admits generation 0. `aliveCount`
is then `N`, and the second exec admits generation 1 anyway. Both stay
alive, and the world has not crashed. -/

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

end Deadlock
