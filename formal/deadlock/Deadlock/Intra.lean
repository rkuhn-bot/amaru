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

import Deadlock.Examples
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Deadlock

/-! Two members of one subtree may exchange a reliable send or a call.
A third witness is mux, then handler, then connection, in that subtree.
A lone terminable is still not allowed to send. -/

def intraFlags : CellFlags where
  singleWriter := true
  orderMonotone := true
  noPerMessageObligation := true
  visibility := true
  readPoints := true
  idempotent := true
  dirtyBit := true

def intraWake : Edge :=
  { (sendEdge "opener" "idle" "a" "Start" 0) with
      kind := .nonBlocking, effect := .cell, reliability := .superseding, cell := intraFlags }

def intraSend : Edge :=
  { (sendEdge "a" "busy" "b" "M" 1) with occupancy := { a := 1, b := 0 } }

def intraCall : Edge :=
  { (sendEdge "a" "busy" "b" "Q" 1) with
      effect := .call, repliesInDequeue := true, occupancy := { a := 1, b := 0 } }

def intraTr (t f label to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := label, program := p, toState := to,
    acceptsCall := false, release := 1 }

def pairDesc (e : Edge) : Description where
  name := "intra-subtree"
  freshNames := true
  templates :=
    [openerTpl, connRole "timer" false true,
     { connRole "a" false false with states := ["idle", "busy"] }, connRole "b" false false]
  edges := [muxIngress, intraWake, { intraWake with srcState := "idle" }, e, selfPeer "timer" "Timeout"]
  compatibility := .all
  steps :=
    [{ template := "opener", fromState := "idle", toState := "idle", label := "Go" },
     { template := "a", fromState := "idle", toState := "busy", label := "Start" },
     { template := "a", fromState := "busy", toState := "busy", label := "Start" },
     { template := "b", fromState := "idle", toState := "idle", label := e.label }]

def sendPair : Impl where
  desc := pairDesc intraSend
  transitions :=
    [intraTr "opener" "idle" "Go" "idle" [.cell "a" "Start" 1],
     intraTr "a" "idle" "Start" "busy" [.send "b" "M" 0],
     intraTr "a" "busy" "Start" "busy" [],
     intraTr "b" "idle" "M" "idle" []]

def callPair : Impl where
  desc := pairDesc intraCall
  transitions :=
    [intraTr "opener" "idle" "Go" "idle" [.cell "a" "Start" 1],
     intraTr "a" "idle" "Start" "busy" [.call "b" "Q" 0],
     intraTr "a" "busy" "Start" "busy" [],
     { intraTr "b" "idle" "Q" "idle" [.reply] with acceptsCall := true }]

theorem intra_send_graph : checkBool sendPair.desc = true := by decide

theorem intra_send_local : localOkB sendPair = true := by decide

theorem intra_send_issues : localIssues sendPair = [] := by decide

theorem intra_call_graph : checkBool callPair.desc = true := by decide

theorem intra_call_local : localOkB callPair = true := by decide

theorem intra_call_issues : localIssues callPair = [] := by decide

def muxWake : Edge :=
  { (sendEdge "opener" "idle" "mux" "Start" 0) with
      kind := .nonBlocking, effect := .cell, reliability := .superseding, cell := intraFlags }

def muxToHandler : Edge :=
  { (sendEdge "mux" "busy" "handler" "H" 1) with occupancy := { a := 1, b := 0 } }

def handlerToConn : Edge :=
  { (sendEdge "handler" "busy" "connection" "Q" 1) with
      effect := .call, repliesInDequeue := true, occupancy := { a := 1, b := 0 } }

def muxChainDesc : Description where
  name := "mux-handler-connection"
  freshNames := true
  templates :=
    [openerTpl, connRole "timer" false true,
     { connRole "mux" false false with states := ["idle", "busy"] },
     { connRole "handler" false false with states := ["idle", "busy"] },
     connRole "connection" false false]
  edges := [muxIngress, muxWake, muxToHandler, handlerToConn, selfPeer "timer" "Timeout"]
  compatibility := .all
  steps :=
    [{ template := "opener", fromState := "idle", toState := "idle", label := "Go" },
     { template := "mux", fromState := "idle", toState := "busy", label := "Start" },
     { template := "mux", fromState := "busy", toState := "busy", label := "Start" },
     { template := "handler", fromState := "idle", toState := "busy", label := "H" },
     { template := "handler", fromState := "busy", toState := "busy", label := "H" },
     { template := "connection", fromState := "idle", toState := "idle", label := "Q" }]

/-- `mux` sends to `handler`, which calls `connection`. All three die together. -/
def muxChain : Impl where
  desc := muxChainDesc
  transitions :=
    [intraTr "opener" "idle" "Go" "idle" [.cell "mux" "Start" 1],
     intraTr "mux" "idle" "Start" "busy" [.send "handler" "H" 0],
     intraTr "mux" "busy" "Start" "busy" [],
     intraTr "handler" "idle" "H" "busy" [.call "connection" "Q" 0],
     intraTr "handler" "busy" "H" "busy" [],
     { intraTr "connection" "idle" "Q" "idle" [.reply] with acceptsCall := true }]

theorem mux_chain_graph : checkBool muxChain.desc = true := by decide

theorem mux_chain_local : localOkB muxChain = true := by decide

theorem mux_chain_issues : localIssues muxChain = [] := by decide

/-- A terminable per-peer with an empty subtree is still not allowed to send. -/
def loneSend : Impl where
  desc :=
    { name := "lone-send"
      freshNames := true
      templates := [{ tpl "a" 2 ["idle"] "idle" false with
        multiplicity := .perPeer, terminable := true }]
      edges := [sendEdge "a" "idle" "a" "M" 0]
      compatibility := .all
      steps := [{ template := "a", fromState := "idle", toState := "idle", label := "M" }] }
  transitions := [intraTr "a" "idle" "M" "idle" [.send "a" "M" 0]]

theorem lone_send_rejected : localOkB loneSend = false := by decide

end Deadlock
