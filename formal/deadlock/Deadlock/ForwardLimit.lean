import Deadlock.Local

set_option autoImplicit false

namespace Deadlock.ForwardLimit

open Deadlock

/-!
A core cannot forward on every message forever.

`sendsOk` requires `pathReserve(program) ≤ floorState(fromState)`.
`floorState` is `budget - debt`. A straight send reserves
`1 + landFloor(landing)`, and `landFloor` is that same floor, so an
admitted send needs `debt(landing) ≥ debt(from) + 1` whenever both
debts sit under the budget. Debt is at most the budget, so the state
whose debt equals the budget has floor 0 and cannot be the source of
a send.

A one-state loop fails at once: the send needs `1 ≤ 0`. A two-state
machine can send only toward the strictly higher debt, and cannot
return. `localOk`, the checker, and the step semantics are unchanged.
-/

def fwdT : Template where
  name := "fwd"
  multiplicity := .one
  capacity := Affine.ofNat 1
  priorityCapacity := Affine.ofNat 1
  priorityBound := Affine.ofNat 1
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

def fwdEdge : Edge where
  src := "fwd"
  srcState := "idle"
  dst := "fwd"
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := "Out"
  scope := .intra
  occupancy := Affine.ofNat 1
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

def fwdTr : Transition where
  template := "fwd"
  fromState := "idle"
  label := "In"
  program := [.send "fwd" "Out" 0]
  toState := "idle"
  acceptsCall := false
  release := 1

def fwdDesc : Description where
  name := "fwd"
  freshNames := true
  templates := [fwdT]
  edges := [fwdEdge]
  compatibility := .all
  steps := []

def fwdImpl : Impl where
  desc := fwdDesc
  transitions := [fwdTr]

/-- The only state already owes the message it would send, so the send is refused. -/
theorem forward_sends_fail : sendsOk fwdDesc "fwd" fwdTr = false := by
  decide

/-- The same program fails the local check. The failure is `sendsOk`. -/
theorem forward_local_fail : localOkB fwdImpl = false := by
  decide

end Deadlock.ForwardLimit
