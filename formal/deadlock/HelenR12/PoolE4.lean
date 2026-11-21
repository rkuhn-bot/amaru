import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12p
open Deadlock Deadlock.Outlive
/-! E4 with the two hosts as pool children (one slot each) of cores MH, MK. -/
def host (name sup : String) : Template :=
  { core name with multiplicity := .perPeer, slots := 1, supervisor := some sup, tombstone := "dead/" ++ name }
def mgr (name : String) : Template :=
  { core name with states := ["boot", "up"], initial := "boot", capacity := { a := 0, b := 2 } }
def goM (t st : String) : Edge := { go t st with occupancy := { a := 0, b := 1 } }
def pDesc : Description where
  name := "pool-outlive"
  freshNames := true
  templates := [mgr "MH", mgr "MK", host "H" "MH", host "K" "MK", tR, tX]
  edges := [ping "H" "idle", ping "H" "sent", ping "K" "idle", ping "K" "sent",
     go "R" "idle", go "R" "up", go "X" "idle", go "X" "sent",
     { blk "H" "sent" "K" "P" .intra { a := 1, b := 0 } with reliability := .superseding },
     { blk "K" "sent" "H" "P" .intra { a := 1, b := 0 } with reliability := .superseding },
     { blk "X" "sent" "K" "M" .intra { a := 1, b := 0 } with reliability := .superseding },
     { blk "X" "sent" "H" "M" .intra { a := 1, b := 0 } with reliability := .superseding },
     goM "MH" "boot", goM "MH" "up", goM "MK" "boot", goM "MK" "up"]
  compatibility := .all
  steps := outDesc.steps ++ ([("MH", "H"), ("MK", "K")].flatMap fun (m, h) =>
    [st m "boot" "Go" "up", st m "up" "Go" "up", st m "boot" ("dead/" ++ h) "boot", st m "up" ("dead/" ++ h) "up"])
where
  st (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }
def pImpl : Impl where
  desc := pDesc
  transitions := outImpl.transitions ++ ([("MH", "H"), ("MK", "K")].flatMap fun (m, h) =>
    [tr m "boot" "Go" "up" [.spawn h], tr m "up" "Go" "up" [],
     tr m "boot" ("dead/" ++ h) "boot" [], tr m "up" ("dead/" ++ h) "up" []])
#eval (render pDesc, localIssues pImpl, l1 pDesc "H", l1 pDesc "K")
end Deadlock.Helen12p
