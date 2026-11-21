import Deadlock.Examples
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Deadlock

def plainTr (template fromState label toState : String) (program : List Eff) : Transition where
  template := template
  fromState := fromState
  label := label
  program := program
  toState := toState
  acceptsCall := false
  release := 1

/-- Two transitions share `(template, fromState, label)`. `findTr` keeps only the
first, so `callTotal` can accept a call that `deliver` refuses. -/
def dupKeyImpl : Impl where
  desc := safeDesc
  transitions :=
    [plainTr "source" "idle" "Ping" "idle" [.send "sink" "Ping" 0],
     plainTr "source" "idle" "Ping" "idle" []]

theorem duplicate_key_fails : uniqueKeys dupKeyImpl = false := by decide

/-- The sink never handles `Ping`, so a delivered message is consumed with no
transition. -/
def unknownLabelImpl : Impl where
  desc := safeDesc
  transitions := []

theorem unknown_label_fails : labelHandled unknownLabelImpl = false := by decide

/-- A reliable send to a terminable per-peer outside the sender's subtree. -/
def terminableTargetDesc : Description where
  name := "terminable-target"
  freshNames := true
  templates :=
    [tpl "boss" 1 ["idle"] "idle" true,
     { tpl "worker" 1 ["idle"] "idle" true with
         multiplicity := .perPeer, terminable := true }]
  edges := [sendEdge "boss" "idle" "worker" "Stop" 1]
  compatibility := .all
  steps := []

def terminableTargetImpl : Impl where
  desc := terminableTargetDesc
  transitions := []

theorem terminable_target_fails : permanentTarget terminableTargetImpl = false := by decide

/-- A core that sets `terminable` is rejected. The flag is a per-peer shutdown. -/
def coreFlagDesc : Description where
  name := "core-flag"
  freshNames := true
  templates := [{ tpl "worker" 1 ["idle"] "idle" true with terminable := true }]
  edges := []
  compatibility := .all
  steps := []

theorem core_terminable_rejected : subtreeFails coreFlagDesc =
    ["fail: core worker sets terminable; a core terminate crashes the node"] := by decide

/-- A core may `terminate`. The effect crashes the node, and `LocalOk` allows it. -/
def coreDieImpl : Impl where
  desc := {
    name := "core-die"
    freshNames := true
    templates := [tpl "node" 1 ["idle"] "idle" true]
    edges := []
    compatibility := .all
    steps := [{ template := "node", fromState := "idle", toState := "idle", label := "Stop" }]
  }
  transitions := [plainTr "node" "idle" "Stop" "idle" [.terminate]]

theorem core_terminate_local :
    checkBool coreDieImpl.desc = true ∧ localOkB coreDieImpl = true := by
  decide

def perPeerTargetDesc : Description where
  name := "per-peer-target"
  freshNames := true
  templates :=
    [tpl "boss" 1 ["idle"] "idle" true,
     { tpl "session" 1 ["idle"] "idle" true with multiplicity := .perPeer }]
  edges := [sendEdge "boss" "idle" "session" "Open" 1]
  compatibility := .all
  steps := []

def perPeerTargetImpl : Impl where
  desc := perPeerTargetDesc
  transitions := []

theorem per_peer_target_fails : permanentTarget perPeerTargetImpl = false := by decide

end Deadlock
