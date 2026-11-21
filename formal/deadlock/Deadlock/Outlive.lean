/-
Mail from a non-terminable child outlives the child.

`X` is a non-terminable per-peer child of the terminable root `R`. It sends
one `M` to each of the cores `K` and `H`. `R`'s `terminate` seals
`X` in that step and does not remove those messages. After four such births
both cores hold a `Ping` plus four `M`s, which is their whole capacity. The
next `X` parks on `K`. Each core then runs `Ping`, whose program is a blocking
send of `P` to the other core, and that send parks. The checker accepts the
description: a non-terminable member is not confined to its subtree.

Each birth is generation 0 of a fresh subtree key, not a later occupant of
an old slot. `slotCoreMail` does not refuse these spawns. The mail in `H`
and `K` is from five different slots, and the cores still park on each other.
-/
import Deadlock.Graph
import Deadlock.Local

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Deadlock.Outlive
open Deadlock

def core (name : String) : Template where
  name := name
  multiplicity := .one
  capacity := { a := 1, b := 3 }
  priorityCapacity := { a := 0, b := 1 }
  priorityBound := { a := 0, b := 1 }
  states := ["idle", "sent"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true

def tR : Template where
  name := "R"
  multiplicity := .perPeer
  capacity := { a := 4, b := 1 }
  priorityCapacity := { a := 0, b := 1 }
  priorityBound := { a := 0, b := 1 }
  states := ["idle", "up"]
  initial := "idle"
  terminable := true
  untimedPeer := false
  mustFit := true
  subtree := "c"

def tX : Template where
  name := "X"
  multiplicity := .perPeer
  capacity := { a := 2, b := 1 }
  priorityCapacity := { a := 0, b := 1 }
  priorityBound := { a := 0, b := 1 }
  states := ["idle", "sent"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true
  subtree := "c"
  supervisor := some "R"
  tombstone := "dead/X"

def ping (t st : String) : Edge where
  src := t
  srcState := st
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := "Ping"
  scope := .intra
  occupancy := { a := 0, b := 1 }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some { a := 0, b := 1 }
  cell := .none

def go (t st : String) : Edge where
  src := t
  srcState := st
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := "Go"
  scope := .intra
  occupancy := { a := 1, b := 0 }
  repliesInDequeue := false
  ingress := true
  ingressLegal := some { a := 0, b := 1 }
  cell := .none

def blk (src ss dst label : String) (scope : Scope) (occ : Affine) : Edge where
  src := src
  srcState := ss
  dst := dst
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := label
  scope := scope
  occupancy := occ
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

def outDesc : Description where
  name := "outlive"
  freshNames := true
  templates := [core "H", core "K", tR, tX]
  edges :=
    [ping "H" "idle", ping "H" "sent", ping "K" "idle", ping "K" "sent",
     go "R" "idle", go "R" "up", go "X" "idle", go "X" "sent",
     blk "H" "sent" "K" "P" .intra { a := 0, b := 1 },
     blk "K" "sent" "H" "P" .intra { a := 0, b := 1 },
     blk "X" "sent" "K" "M" .coreInst { a := 1, b := 0 },
     blk "X" "sent" "H" "M" .coreInst { a := 1, b := 0 }]
  compatibility := .all
  steps :=
    [step "H" "idle" "Ping" "sent", step "H" "sent" "Ping" "sent",
     step "H" "idle" "P" "idle", step "H" "sent" "P" "sent",
     step "H" "idle" "M" "idle", step "H" "sent" "M" "sent",
     step "K" "idle" "Ping" "sent", step "K" "sent" "Ping" "sent",
     step "K" "idle" "P" "idle", step "K" "sent" "P" "sent",
     step "K" "idle" "M" "idle", step "K" "sent" "M" "sent",
     step "R" "idle" "Go" "up", step "R" "up" "Go" "up",
     step "R" "idle" "dead/X" "idle", step "R" "up" "dead/X" "up",
     step "X" "idle" "Go" "sent", step "X" "sent" "Go" "sent"]
where
  step (t f l to : String) : CompatStep :=
    { template := t, fromState := f, toState := to, label := l }

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := false, release := 1 }

def outImpl : Impl where
  desc := outDesc
  transitions :=
    [tr "H" "idle" "Ping" "sent" [.send "K" "P" 0],
     tr "H" "sent" "Ping" "sent" [],
     tr "H" "idle" "P" "idle" [], tr "H" "sent" "P" "sent" [],
     tr "H" "idle" "M" "idle" [], tr "H" "sent" "M" "sent" [],
     tr "K" "idle" "Ping" "sent" [.send "H" "P" 0],
     tr "K" "sent" "Ping" "sent" [],
     tr "K" "idle" "P" "idle" [], tr "K" "sent" "P" "sent" [],
     tr "K" "idle" "M" "idle" [], tr "K" "sent" "M" "sent" [],
     tr "R" "idle" "Go" "up" [.spawn "X"],
     tr "R" "up" "Go" "up" [.terminate],
     tr "R" "idle" "dead/X" "idle" [],
     tr "R" "up" "dead/X" "up" [],
     tr "X" "idle" "Go" "sent" [.send "K" "M" 0, .send "H" "M" 0],
     tr "X" "sent" "Go" "sent" []]

def Hc : InstId := .core "H"
def Kc : InstId := .core "K"
def Rk (k : Nat) : InstId := .peer "R" k 0
def Xk (k : Nat) : InstId := .peer "X" k 0

def runAt (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply outImpl a)) (some (initWorld outImpl 2))

def gen (k : Nat) : List Action :=
  [.spawn "R",
   .ingress (Rk k) "Go", .recvBulk (Rk k), .exec (Rk k),
   .ingress (Xk k) "Go", .recvBulk (Xk k), .exec (Xk k), .exec (Xk k),
   .ingress (Rk k) "Go", .recvBulk (Rk k), .exec (Rk k), .exec (Rk k)]

def parkedOn (a : Actor) (dst : InstId) : Bool :=
  match a.phase with
  | .parked d _ _ => d == dst
  | _ => false

def early : List Action :=
  [.ingress Hc "Ping", .ingress Kc "Ping"] ++ gen 0 ++ gen 1 ++ gen 2 ++ gen 3

def fifth : List Action :=
  [.spawn "R",
   .ingress (Rk 4) "Go", .recvBulk (Rk 4), .exec (Rk 4),
   .ingress (Xk 4) "Go", .recvBulk (Xk 4), .exec (Xk 4)]

def tail : List Action :=
  [.recvBulk Hc, .exec Hc, .recvBulk Kc, .exec (Xk 4), .exec Kc]

def outliveActs : List Action := early ++ fifth ++ tail

theorem outlive_checked : GraphOk outDesc ∧ LocalOk outImpl ∧ render outDesc = "pass" ∧
    l1 outDesc "H" = true ∧ l1 outDesc "K" = true := by
  have hcheck : checkBool outDesc = true := by decide
  refine ⟨checkBool_sound _ hcheck, by decide, ?_, by decide, by decide⟩
  simp [render, hcheck]

/-- Both cores are parked on each other, each mailbox holds five messages, and
the roster has not crashed. No runtime step is enabled. Stutter is. -/
theorem outlive_stuck :
    (match runAt outliveActs with
      | none => false
      | some w =>
        parkedOn (w.st Hc) Kc && parkedOn (w.st Kc) Hc &&
          decide ((w.st Hc).box.length = 5) && decide ((w.st Kc).box.length = 5) &&
          !w.crashed && !runtimeBusy outImpl w && (apply outImpl .stutter w).isSome) = true := by
  decide

/-- Each `X` and `R` in that run is generation 0 of its own key. The respawn
guard looks at earlier occupants of the same key, so it does not refuse
these births. -/
theorem outlive_first_generation :
    (match runAt outliveActs with
      | none => false
      | some w =>
        decide (maxGen w "X" 0 = 1) && decide (maxGen w "X" 1 = 1) &&
          decide (maxGen w "X" 2 = 1) && decide (maxGen w "X" 3 = 1) &&
          decide (maxGen w "X" 4 = 1) &&
          decide (maxGen w "R" 0 = 1) && decide (maxGen w "R" 1 = 1) &&
          decide (maxGen w "R" 2 = 1) && decide (maxGen w "R" 3 = 1) &&
          decide (maxGen w "R" 4 = 1)) = true := by
  decide
