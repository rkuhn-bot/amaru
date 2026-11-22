import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

/-! A pool parks on a Lemma-1 mailbox.

The core's capacity is `1*N+1` and the only bulk edge into it, apart from
its own ingress, is one per-peer send of coefficient 1. At `N = 1` the
concrete cap is 2, and Lemma 1 holds. The pool has three slots. The core
births a child, the child sends, and the core seals it and births the next
slot, twice. The third send finds the box full and parks. The world is not
crashed. Alive children of the pool never exceed `N`: each child is sealed
before the next is born. -/

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

private def poolParkW : Template :=
  { base "W" with
    multiplicity := .perPeer
    slots := 3
    supervisor := some "C"
    tombstone := "dead/W"
    capacity := { a := 1, b := 0 } }

private def poolParkC : Template :=
  { base "C" with capacity := { a := 1, b := 1 } }

private def poolIng (src : String) (a b : Nat) : Edge where
  src := src
  srcState := "idle"
  dst := src
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := "Go"
  scope := .intra
  occupancy := { a := a, b := b }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat 1)
  cell := .none

private def poolSend : Edge where
  src := "W"
  srcState := "idle"
  dst := "C"
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := "M"
  scope := .cross
  occupancy := { a := 1, b := 0 }
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

private def poolDesc : Description where
  name := "pool-park"
  freshNames := true
  templates := [poolParkC, poolParkW]
  edges := [poolIng "C" 0 1, poolIng "W" 1 0, poolSend]
  compatibility := .all
  steps := []

private def poolImpl : Impl where
  desc := poolDesc
  transitions :=
    [ { template := "C", fromState := "idle", label := "Go", toState := "idle",
        acceptsCall := false, release := 1,
        program := [.spawn "W", .abort, .spawn "W", .abort, .spawn "W"] },
      { template := "W", fromState := "idle", label := "Go", toState := "idle",
        acceptsCall := false, release := 1,
        program := [.send "C" "M" 0] } ]

private def poolRun (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply poolImpl a)) (some (initWorld poolImpl 1))

private def poolC : InstId := .core "C"
private def poolW0 : InstId := .peer "W" 0 0
private def poolW1 : InstId := .peer "W" 1 0
private def poolW2 : InstId := .peer "W" 2 0

private def poolWake (id : InstId) : List Action := [.ingress id "Go", .recvBulk id, .exec id]

private def poolActs : List Action :=
  poolWake poolC ++ poolWake poolW0 ++ [.exec poolC, .exec poolC] ++
    poolWake poolW1 ++ [.exec poolC, .exec poolC] ++ poolWake poolW2

private def poolParked (w : World) : Bool :=
  match (w.st poolW2).phase with
  | .parked _ _ _ => true
  | _ => false

private def poolExceeds : Bool :=
  l1 poolDesc "C" && decide (capBulk poolDesc 1 poolC = 2) &&
    decide ((totalOcc poolDesc "C").eval 1 = 2) &&
      match poolRun poolActs with
      | none => false
      | some w =>
        decide ((w.st poolC).box.length = 2) && decide ((w.st poolC).parked.length = 1) &&
          !w.crashed && (w.st poolW0).life == .dead && (w.st poolW1).life == .dead &&
          (w.st poolW2).life == .alive && poolParked w

/-- Lemma 1 holds and the cap is 2, but the reachable mailbox holds two queued
messages and one parked send. -/
theorem pool_park_exceeds : poolExceeds = true := by
  decide

end Deadlock
