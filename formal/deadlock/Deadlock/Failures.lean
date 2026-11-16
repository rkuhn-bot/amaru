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

def terminableTargetDesc : Description where
  name := "terminable-target"
  freshNames := true
  templates :=
    [tpl "boss" 1 ["idle"] "idle" true,
     { tpl "worker" 1 ["idle"] "idle" true with terminable := true }]
  edges := [sendEdge "boss" "idle" "worker" "Stop" 1]
  compatibility := .all
  steps := []

def terminableTargetImpl : Impl where
  desc := terminableTargetDesc
  transitions := []

theorem terminable_target_fails : permanentTarget terminableTargetImpl = false := by decide

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
