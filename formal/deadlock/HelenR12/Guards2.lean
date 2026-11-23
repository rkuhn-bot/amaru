import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12g2
open Deadlock Deadlock.Outlive
/-! Per-peer child C under root R. A descendant mails core H. The
supervisor's tombstone stays queued until H takes that mail. The following
spawn then births the next generation. -/
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
def st (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }
def ingA (t s l : String) : Edge := { go t s with label := l, occupancy := { a := 1, b := 0 } }
def ingB (t s l : String) : Edge := { go t s with label := l, occupancy := { a := 0, b := 1 } }
def tH : Template := let b := core "H"; { b with states := ["idle"], capacity := { a := 4, b := 4 } }
def pp (n : String) (sub : String) (sup : Option String) (sts : List String) (term : Bool) : Template :=
  let b := core n
  { b with multiplicity := .perPeer, supervisor := sup, tombstone := (match sup with | some _ => "dead/" ++ n | none => ""), subtree := sub, states := sts, initial := sts.headD "idle", capacity := { a := 3, b := 1 }, priorityCapacity := { a := 0, b := 2 }, priorityBound := { a := 0, b := 2 }, terminable := term }
def tRr := pp "R" "s" none ["boot", "up", "wait"] true
def tC := pp "C" "s" (some "R") ["idle", "up"] true
def tXc := pp "X" "s" (some "C") ["idle", "sent"] false
def two (t f l to : String) : List CompatStep := [st t f l to]
def gDesc : Description where
  name := "guards"
  freshNames := true
  templates := [tH, tRr, tC, tXc]
  edges := [ingA "R" "boot" "Go", ingA "R" "up" "Go", ingA "R" "wait" "Go",
            ingA "C" "idle" "Go", ingA "C" "up" "Go",
            ingA "X" "idle" "Go", ingA "X" "sent" "Go",
            blk "X" "sent" "H" "M" .coreInst { a := 1, b := 0 }]
  compatibility := .all
  steps := [st "R" "boot" "Go" "up", st "R" "up" "Go" "up", st "R" "wait" "Go" "up",
            st "R" "boot" "dead/C" "boot", st "R" "up" "dead/C" "wait", st "R" "wait" "dead/C" "wait",
            st "C" "idle" "Go" "up", st "C" "up" "Go" "up", st "C" "idle" "dead/X" "idle", st "C" "up" "dead/X" "up",
            st "X" "idle" "Go" "sent", st "X" "sent" "Go" "sent",
            st "H" "idle" "M" "idle"]
def gImpl : Impl where
  desc := gDesc
  transitions := [tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "up" "Go" "up" [], tr "R" "wait" "Go" "up" [.spawn "C"],
      tr "R" "boot" "dead/C" "boot" [], tr "R" "up" "dead/C" "wait" [], tr "R" "wait" "dead/C" "wait" [],
      tr "C" "idle" "Go" "up" [.spawn "X"], tr "C" "up" "Go" "up" [.terminate],
      tr "C" "idle" "dead/X" "idle" [], tr "C" "up" "dead/X" "up" [],
      tr "X" "idle" "Go" "sent" [.send "H" "M" 0], tr "X" "sent" "Go" "sent" [],
      tr "H" "idle" "M" "idle" []]
#eval (render gDesc, localIssues gImpl)

def run (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply gImpl a)) (some (initWorld gImpl 2))
def Hc : InstId := .core "H"
def P (n : String) (g : Nat) : InstId := .peer n 0 g
-- Per-peer child C under root R: X (child of C) mails H, C terminates, R respawns C.
def preA : List Action :=
  [.spawn "R", .ingress (P "R" 0) "Go", .recvBulk (P "R" 0), .exec (P "R" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0),
   .ingress (P "X" 0) "Go", .recvBulk (P "X" 0), .exec (P "X" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0), .exec (P "C" 0),
   .recvPrio (P "R" 0), .ingress (P "R" 0) "Go", .recvBulk (P "R" 0)]
def infoA (w : World) :=
  (lifeTag (w.st (P "C" 0)).life, lifeTag (w.st (P "X" 0)).life, lifeTag (w.st (P "C" 1)).life,
   (w.st Hc).box.map (·.label), slotRespawnBlocked gDesc w (P "R" 0) "C" 0, slotMailHeld gDesc w "C" 0, w.crashed)
def sealA : List Action :=
  [.spawn "R", .ingress (P "R" 0) "Go", .recvBulk (P "R" 0), .exec (P "R" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0),
   .ingress (P "X" 0) "Go", .recvBulk (P "X" 0), .exec (P "X" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0), .exec (P "C" 0)]
def readyA : List Action := sealA ++ [.recvBulk Hc, .recvPrio (P "R" 0)]
def bornA : List Action :=
  readyA ++ [.ingress (P "R" 0) "Go", .recvBulk (P "R" 0), .exec (P "R" 0)]
#eval (run sealA).map infoA
#eval (run readyA).map infoA
#eval (run bornA).map infoA

/-- C's tombstone is not receivable while X's mail sits on H. After H takes
it, the slot is free, and the following Go births generation 1. -/
theorem guards_child_respawn_enabled :
    (match run sealA with
      | none => false
      | some w =>
        mailInFlight w (P "C" 0) &&
          decide ((apply gImpl (.recvPrio (P "R" 0)) w).isNone) &&
          ((w.st (P "C" 1)).life == .absent)) = true ∧
      (match run readyA with
        | none => false
        | some w =>
          !(mailInFlight w (P "C" 0)) &&
            (slotRespawnBlocked gDesc w (P "R" 0) "C" 0 == false) &&
            ((w.st (P "C" 1)).life == .absent)) = true ∧
      (match run bornA with
        | none => false
        | some w => (w.st (P "C" 1)).life == .alive) = true := by
  decide

end Deadlock.Helen12g2
namespace Deadlock.Helen12g2
open Deadlock
#eval (List.range (preA.length + 1)).find? fun n => (run (preA.take n)).isNone
end Deadlock.Helen12g2
