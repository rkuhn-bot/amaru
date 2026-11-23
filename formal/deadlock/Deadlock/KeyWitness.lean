/-
What `spawnChild` does to a core-supervised subtree.

`coreChildDesc` passes the checker and has no unsupervised root. Spawning the
worker from the core admits nobody. Spawning it from a live peer of the
core's name admits the worker at that peer's key and does not move `nextKey`.
-/

import Deadlock.Examples
import Deadlock.Semantics

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Deadlock

def coreChildImpl : Impl where
  desc := coreChildDesc
  transitions := []

def hostActor : Actor where
  life := .alive
  typestate := "idle"
  phase := .idle
  box := []
  prio := []
  parked := []
  tokens := fun _ => 0

def hostPeer : InstId := InstId.peer "host" 0 0

def coreHostWorld : World where
  N := 1
  roster := [InstId.core "host"]
  nextIx := fun _ => 0
  nextKey := fun _ => 0
  st := fun id => if id = InstId.core "host" then hostActor else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- The core is alive and is the worker's supervisor. `spawnChild` admits
nobody from a core, so this world does not move `nextKey`. -/
theorem core_supervisor_spawns_nobody :
    spawnChild coreChildImpl coreHostWorld (InstId.core "host") "worker" = none := by
  rfl

def peerHostWorld : World where
  N := 1
  roster := [hostPeer]
  nextIx := fun n => if n = "host" then 1 else 0
  nextKey := fun _ => 0
  st := fun id => if id = hostPeer then hostActor else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- A live peer of the core's name is not a per-peer template. From that
peer, `spawnChild` admits `worker` at key 0. -/
theorem peer_host_admits :
    spawnChild coreChildImpl peerHostWorld hostPeer "worker" =
      some (admitBorn coreChildImpl peerHostWorld (InstId.peer "worker" 0 0)
        { bornActor coreChildDesc peerHostWorld "worker" 0 "idle" with parent := some hostPeer }) := by
  rfl

theorem readCells_key (D : Description) (w : World) (id : InstId) (s : String) :
    (readCells D w id).nextKey s = w.nextKey s := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ labs ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem peer_host_nextKey :
    ((admitBorn coreChildImpl peerHostWorld (InstId.peer "worker" 0 0)
        { bornActor coreChildDesc peerHostWorld "worker" 0 "idle" with parent := some hostPeer }).nextKey
      "sub") = 0 := by
  rw [admitBorn, readCells_key, setActor]
  rfl

/-- `host` is a multiplicity-one template. A live peer of that name is outside
`PeerRole`, which is what a birth step requires of every live peer. -/
theorem peer_host_multiplicity :
    match templateOf coreChildDesc "host" with
    | some t => t.multiplicity = Multiplicity.one
    | none => False := by
  rfl

theorem peer_host_roster :
    InstId.peer "worker" 0 0 ∈
      (admitBorn coreChildImpl peerHostWorld (InstId.peer "worker" 0 0)
        { bornActor coreChildDesc peerHostWorld "worker" 0 "idle" with parent := some hostPeer }).roster := by
  simp [admitBorn, cellsRoster, setActor]

end Deadlock
