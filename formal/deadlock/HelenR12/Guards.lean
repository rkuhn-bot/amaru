import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12g
open Deadlock Deadlock.Outlive
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
def info (w : World) :=
  (loneOutstanding outDesc w "R", (apply outImpl (.spawn "R") w).isSome,
   lifeTag (w.st (Rk 0)).life, lifeTag (w.st (Rk 1)).life,
   subtreeCoreMail outDesc w "c" 0, subtreeCoreMail outDesc w "c" 1,
   (w.st Hc).box.map (·.label), (w.st Kc).box.map (·.label))
-- (c) root population: blocked after prefix2; H and K drain; unblocked.
def drain : List Action :=
  [.recvBulk Hc, .exec Hc, .recvBulk Kc, .exec Kc,  -- the Pings (each sends P to the other)
   .recvBulk Hc, .recvBulk Hc, .recvBulk Kc, .recvBulk Kc]
#eval (List.range (drain.length + 1)).map fun n => (n, (runAt (prefix2 ++ drain.take n)).map info)
-- (d) shutting-down lone root with core mail: stop gen 1 before R@1's seal.
def gen1NoSeal : List Action := (gen 1).take 11
#eval (runAt ([.ingress Hc "Ping", .ingress Kc "Ping"] ++ gen 0 ++ gen1NoSeal)).map info
-- (d') shutting-down lone root with no core mail: R@0 terminates before X sends.
def noMail : List Action := [.spawn "R", .ingress (Rk 0) "Go", .recvBulk (Rk 0), .exec (Rk 0),
  .ingress (Rk 0) "Go", .recvBulk (Rk 0), .exec (Rk 0)]
#eval (runAt noMail).map info
#eval (runAt (noMail ++ [.spawn "R", .spawn "R"])).map info

/-- Population slots stay full while subtree mail sits on the cores, and a
spawn is enabled again once both cores have consumed it. A root that shuts
down before its child sends does not keep the slot. -/
theorem guards_reenabled :
    (match runAt prefix2 with
      | none => false
      | some w =>
        decide (loneOutstanding outDesc w "R" = 2) &&
          decide ((apply outImpl (.spawn "R") w).isNone) &&
          subtreeCoreMail outDesc w "c" 0 && subtreeCoreMail outDesc w "c" 1) = true ∧
      (match runAt (prefix2 ++ drain) with
        | none => false
        | some w =>
          decide (loneOutstanding outDesc w "R" = 0) &&
            decide ((apply outImpl (.spawn "R") w).isSome) &&
            !(subtreeCoreMail outDesc w "c" 0) && !(subtreeCoreMail outDesc w "c" 1)) = true ∧
      (match runAt noMail with
        | none => false
        | some w =>
          decide (loneOutstanding outDesc w "R" = 0) &&
            decide ((apply outImpl (.spawn "R") w).isSome)) = true := by
  decide

end Deadlock.Helen12g
