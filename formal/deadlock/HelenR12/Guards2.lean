import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12g2
open Deadlock Deadlock.Outlive
/-! (a) per-peer child X under root R, and (b) pool W (subtree pw) under core M.
Both mail core H, die, and are re-spawned from a later state. -/
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
def st (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }
def ingA (t s l : String) : Edge := { go t s with label := l, occupancy := { a := 1, b := 0 } }
def ingB (t s l : String) : Edge := { go t s with label := l, occupancy := { a := 0, b := 1 } }
def tH : Template := let b := core "H"; { b with states := ["idle"], capacity := { a := 4, b := 4 } }
def tM : Template := let b := core "M"; { b with states := ["boot", "up", "wait"], initial := "boot", capacity := { a := 0, b := 4 }, priorityCapacity := { a := 0, b := 2 }, priorityBound := { a := 0, b := 2 } }
def pp (n : String) (sub : String) (sup : Option String) (sts : List String) (term : Bool) (slots : Nat) : Template :=
  let b := core n
  { b with multiplicity := .perPeer, slots := slots, supervisor := sup, tombstone := (match sup with | some _ => "dead/" ++ n | none => ""), subtree := sub, states := sts, initial := sts.headD "idle", capacity := { a := 3, b := 1 }, priorityCapacity := { a := 0, b := 2 }, priorityBound := { a := 0, b := 2 }, terminable := term }
def tW := pp "W" "pw" (some "M") ["idle", "up"] true 1
def tY := pp "Y" "pw" (some "W") ["idle", "sent"] false 0
def tRr := pp "R" "s" none ["boot", "up", "wait"] true 0
def tC := pp "C" "s" (some "R") ["idle", "up"] true 0
def tXc := pp "X" "s" (some "C") ["idle", "sent"] false 0
def two (t f l to : String) : List CompatStep := [st t f l to]
def gDesc : Description where
  name := "guards"
  freshNames := true
  templates := [tH, tM, tW, tY, tRr, tC, tXc]
  edges := [ingB "M" "boot" "Go", ingB "M" "up" "Go", ingB "M" "wait" "Go",
            ingA "R" "boot" "Go", ingA "R" "up" "Go", ingA "R" "wait" "Go",
            ingA "W" "idle" "Go", ingA "W" "up" "Go", ingA "C" "idle" "Go", ingA "C" "up" "Go",
            ingA "X" "idle" "Go", ingA "X" "sent" "Go", ingA "Y" "idle" "Go", ingA "Y" "sent" "Go",
            blk "Y" "sent" "H" "M" .coreInst { a := 1, b := 0 },
            blk "X" "sent" "H" "M" .coreInst { a := 1, b := 0 }]
  compatibility := .all
  steps := [st "M" "boot" "Go" "up", st "M" "up" "Go" "up", st "M" "wait" "Go" "up",
            st "M" "boot" "dead/W" "boot", st "M" "up" "dead/W" "wait", st "M" "wait" "dead/W" "wait",
            st "R" "boot" "Go" "up", st "R" "up" "Go" "up", st "R" "wait" "Go" "up",
            st "R" "boot" "dead/C" "boot", st "R" "up" "dead/C" "wait", st "R" "wait" "dead/C" "wait",
            st "W" "idle" "Go" "up", st "W" "up" "Go" "up", st "W" "idle" "dead/Y" "idle", st "W" "up" "dead/Y" "up",
            st "C" "idle" "Go" "up", st "C" "up" "Go" "up", st "C" "idle" "dead/X" "idle", st "C" "up" "dead/X" "up",
            st "X" "idle" "Go" "sent", st "X" "sent" "Go" "sent", st "Y" "idle" "Go" "sent", st "Y" "sent" "Go" "sent",
            st "H" "idle" "M" "idle"]
def gImpl : Impl where
  desc := gDesc
  transitions := [tr "M" "boot" "Go" "up" [.spawn "W"], tr "M" "up" "Go" "up" [], tr "M" "wait" "Go" "up" [.spawn "W"],
      tr "M" "boot" "dead/W" "boot" [], tr "M" "up" "dead/W" "wait" [], tr "M" "wait" "dead/W" "wait" [],
      tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "up" "Go" "up" [], tr "R" "wait" "Go" "up" [.spawn "C"],
      tr "R" "boot" "dead/C" "boot" [], tr "R" "up" "dead/C" "wait" [], tr "R" "wait" "dead/C" "wait" [],
      tr "W" "idle" "Go" "up" [.spawn "Y"], tr "W" "up" "Go" "up" [.terminate],
      tr "W" "idle" "dead/Y" "idle" [], tr "W" "up" "dead/Y" "up" [],
      tr "C" "idle" "Go" "up" [.spawn "X"], tr "C" "up" "Go" "up" [.terminate],
      tr "C" "idle" "dead/X" "idle" [], tr "C" "up" "dead/X" "up" [],
      tr "X" "idle" "Go" "sent" [.send "H" "M" 0], tr "X" "sent" "Go" "sent" [],
      tr "Y" "idle" "Go" "sent" [.send "H" "M" 0], tr "Y" "sent" "Go" "sent" [],
      tr "H" "idle" "M" "idle" []]
#eval (render gDesc, localIssues gImpl)

def run (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply gImpl a)) (some (initWorld gImpl 2))
def Hc : InstId := .core "H"
def Mc : InstId := .core "M"
def P (n : String) (g : Nat) : InstId := .peer n 0 g
-- (a) per-peer child C under root R: X (child of C) mails H, C terminates, R respawns C.
def preA : List Action :=
  [.spawn "R", .ingress (P "R" 0) "Go", .recvBulk (P "R" 0), .exec (P "R" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0),
   .ingress (P "X" 0) "Go", .recvBulk (P "X" 0), .exec (P "X" 0),
   .ingress (P "C" 0) "Go", .recvBulk (P "C" 0), .exec (P "C" 0), .exec (P "C" 0),
   .recvPrio (P "R" 0), .ingress (P "R" 0) "Go", .recvBulk (P "R" 0)]
def infoA (w : World) :=
  (lifeTag (w.st (P "C" 0)).life, lifeTag (w.st (P "X" 0)).life, lifeTag (w.st (P "C" 1)).life,
   (w.st Hc).box.map (·.label), slotRespawnBlocked gDesc w (P "R" 0) "C" 0, slotMailHeld gDesc w "C" 0, w.crashed)
#eval (run preA).map infoA
#eval (run (preA ++ [.exec (P "R" 0)])).map infoA            -- blocked: C@0.1 not born
#eval (run (preA ++ [.recvBulk Hc])).map infoA                -- H consumes X@0.0's M
#eval (run (preA ++ [.recvBulk Hc, .exec (P "R" 0)])).map infoA  -- unblocked: C@0.1 born
-- (b) pool W (slot 0) under core M: Y (child of W) mails H, W terminates, M respawns W.
def preB : List Action :=
  [.ingress Mc "Go", .recvBulk Mc, .exec Mc,
   .ingress (P "W" 0) "Go", .recvBulk (P "W" 0), .exec (P "W" 0),
   .ingress (P "Y" 0) "Go", .recvBulk (P "Y" 0), .exec (P "Y" 0),
   .ingress (P "W" 0) "Go", .recvBulk (P "W" 0), .exec (P "W" 0), .exec (P "W" 0),
   .recvPrio Mc, .ingress Mc "Go", .recvBulk Mc]
def infoB (w : World) :=
  (lifeTag (w.st (P "W" 0)).life, lifeTag (w.st (P "W" 1)).life, (w.st Hc).box.map (·.label),
   freeSlot gDesc w Mc "W" 1, slotMailHeld gDesc w "W" 0, w.crashed)
#eval (run preB).map infoB
#eval (run (preB ++ [.exec Mc])).map infoB
#eval (run (preB ++ [.recvBulk Hc, .exec Mc])).map infoB

/-- C stays unborn while X's mail sits on H, and is born once H consumes it. -/
theorem guards_child_reenabled :
    (match run (preA ++ [.exec (P "R" 0)]) with
      | none => false
      | some w => slotMailHeld gDesc w "C" 0 && ((w.st (P "C" 1)).life == .absent)) = true ∧
      (match run (preA ++ [.recvBulk Hc, .exec (P "R" 0)]) with
        | none => false
        | some w =>
          !(slotMailHeld gDesc w "C" 0) && ((w.st (P "C" 1)).life == .alive)) = true := by
  decide

/-- Pool slot W stays free of a new generation while Y's mail sits on H, and
is born once H consumes it. -/
theorem guards_pool_reenabled :
    (match run (preB ++ [.exec Mc]) with
      | none => false
      | some w =>
        decide (freeSlot gDesc w Mc "W" 1 = none) &&
          ((w.st (P "W" 1)).life == .absent)) = true ∧
      (match run (preB ++ [.recvBulk Hc, .exec Mc]) with
        | none => false
        | some w =>
          ((w.st (P "W" 1)).life == .alive) && !(slotMailHeld gDesc w "W" 0)) = true := by
  decide

end Deadlock.Helen12g2
namespace Deadlock.Helen12g2
open Deadlock
#eval (List.range (preA.length + 1)).find? fun n => (run (preA.take n)).isNone
#eval (List.range (preB.length + 1)).find? fun n => (run (preB.take n)).isNone
end Deadlock.Helen12g2
