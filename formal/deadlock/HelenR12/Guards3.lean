import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12g3
open Deadlock Deadlock.Outlive
/-! `rootOutstanding`: Outlive with R supervised by a core S. -/
def tS : Template := let b := core "S"; { b with states := ["idle"], capacity := { a := 0, b := 1 }, priorityCapacity := { a := 2, b := 1 }, priorityBound := { a := 0, b := 0 } }
def tR2 : Template := { tR with supervisor := some "S", tombstone := "dead/R" }
def sStep : CompatStep := { template := "S", fromState := "idle", toState := "idle", label := "dead/R" }
def sDesc : Description := { outDesc with templates := [core "H", core "K", tR2, tX, tS], steps := outDesc.steps ++ [sStep] }
def sImpl : Impl := { desc := sDesc, transitions := outImpl.transitions ++ [tr "S" "idle" "dead/R" "idle" []] }
#eval (render sDesc, localIssues sImpl)
def run (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply sImpl a)) (some (initWorld sImpl 2))
def Sc : InstId := .core "S"
def info (w : World) :=
  (rootOutstanding sDesc w "S" "R", (apply sImpl (.spawn "R") w).isSome, (w.st Sc).prio.map (·.label),
   (w.st Hc).box.map (·.label), (w.st Kc).box.map (·.label))
#eval (run prefix2).map info
#eval (run (prefix2 ++ [.recvPrio Sc, .recvPrio Sc])).map info
def drain : List Action := [.recvBulk Hc, .exec Hc, .recvBulk Kc, .exec Kc, .recvBulk Hc, .recvBulk Hc, .recvBulk Kc, .recvBulk Kc]
#eval (List.range (drain.length + 1)).map fun n => (n, (run (prefix2 ++ [.recvPrio Sc, .recvPrio Sc] ++ drain.take n)).map info)

/-- After both tombstones are consumed, core mail still holds both population
slots. The spawn is enabled again once H and K have consumed that mail. -/
theorem guards_root_reenabled :
    (match run (prefix2 ++ [.recvPrio Sc, .recvPrio Sc]) with
      | none => false
      | some w =>
        decide (rootOutstanding sDesc w "S" "R" = 2) &&
          decide ((apply sImpl (.spawn "R") w).isNone)) = true ∧
      (match run (prefix2 ++ [.recvPrio Sc, .recvPrio Sc] ++ drain) with
        | none => false
        | some w =>
          decide (rootOutstanding sDesc w "S" "R" = 0) &&
            decide ((apply sImpl (.spawn "R") w).isSome)) = true := by
  decide

end Deadlock.Helen12g3
