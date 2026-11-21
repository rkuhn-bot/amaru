import Deadlock.Orphan
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen11w
open Deadlock Deadlock.Orphan
-- G self-terminates on Go; C re-spawns G on "Re" in state up (not the tombstone handler).
def tG2 : Template := { tG with states := ["idle"] }
def wDesc : Description where
  name := "win"
  freshNames := true
  templates := [tR, tC, tG2]
  edges := orphanDesc.edges ++ [{ ing "C" "up" with label := "Re" }, { ing "C" "idle" with label := "Re" }, { ing "C" "done" with label := "Re" }]
  compatibility := .all
  steps := orphanDesc.steps ++ [step "C" "up" "Re" "up", step "C" "idle" "Re" "idle", step "C" "done" "Re" "done"]
def wImpl : Impl where
  desc := wDesc
  transitions := (orphanImpl.transitions.filter fun t => !(t.template == "G")) ++
    [tr "G" "idle" "Go" "idle" [.terminate], tr "C" "up" "Re" "up" [.spawn "G"],
     tr "C" "idle" "Re" "idle" [], tr "C" "done" "Re" "done" []]
#eval (render wDesc, localIssues wImpl)
def acts : List Action :=
  birth ++ [.ingress G0 "Go", .recvBulk G0, .exec G0,   -- G@0.0 terminates: shutting down, not sealed
            .ingress C0 "Re", .recvBulk C0, .exec C0]  -- C@0.0 re-spawns G while G@0.0 is still shutting down
#eval (List.range (acts.length+1)).map fun n => (n, (runAt wImpl 2 (acts.take n)).map fun w =>
  (lifeTag (w.st G0).life, lifeTag (w.st G1).life, w.roster.contains G1, w.crashed))
end Deadlock.Helen11w
