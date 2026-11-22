/-
The respawn account after a termination seals in one step.

`C` has sent to its sibling `H` and sits in `High`, with `tokens H = 0` and
that message still in `H`'s box. `budget(C, H) = 1` and `landFloor(Idle) = 1`,
so a birth at `Idle` while the message is still queued would have
`tokens = 0`. `H` stays alive. The tombstone is queued in `C`'s seal and
`receivePrio` skips it until `H` consumes the message. The handler then
spawns `C'`, whose idle floor fits in its tokens.
-/

import Deadlock.Semantics
import Deadlock.Step

set_option autoImplicit false

namespace Deadlock

def fuseTpl (name : String) (sup : Option String) (tomb : String) (states : List String) : Template where
  name := name
  multiplicity := .perPeer
  capacity := .ofNat 2
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 4
  states := states
  initial := "Idle"
  terminable := true
  untimedPeer := false
  mustFit := true
  supervisor := sup
  tombstone := tomb

def fuseEdge : Edge where
  src := "C"
  srcState := "High"
  dst := "H"
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := "m"
  scope := .intra
  occupancy := { a := 1, b := 0 }
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := CellFlags.none

def fuseD : Description where
  name := "fuse"
  freshNames := true
  templates :=
    [fuseTpl "P" none "" ["Idle"],
     fuseTpl "C" (some "P") "died" ["Idle", "High"],
     fuseTpl "H" (some "P") "hdied" ["Idle"]]
  edges := [fuseEdge]
  compatibility := .all
  steps := []

def fuseTr (template src label dst : String) (program : List Eff) : Transition where
  template := template
  fromState := src
  label := label
  program := program
  toState := dst
  acceptsCall := false
  release := 1

def fuseI : Impl where
  desc := fuseD
  transitions :=
    [fuseTr "H" "Idle" "m" "Idle" [],
     fuseTr "P" "Idle" "died" "Idle" [.spawn "C"]]

def pId : InstId := .peer "P" 0 0
def cId : InstId := .peer "C" 0 0
def hId : InstId := .peer "H" 0 0
def cNext : InstId := .peer "C" 0 1

def fuseMail : Msg where
  label := "m"
  sender := cId
  callFrom := none

def fuseActor (life : Life) (ty : String) (box : List Msg) : Actor where
  life := life
  typestate := ty
  phase := .idle
  box := box
  prio := []
  parked := []
  tokens := fun _ => 0

def fuseSt (i : InstId) : Actor :=
  if i = pId then { fuseActor .alive "Idle" [] with }
  else if i = cId then { fuseActor .alive "High" [] with parent := some pId }
  else if i = hId then { fuseActor .alive "Idle" [fuseMail] with parent := some pId }
  else { fuseActor .absent "" [] with }

def held : World where
  N := 1
  roster := [pId, cId, hId]
  nextIx := fun _ => 0
  st := fuseSt
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- `C` seals. `H` is still alive and still holds `C`'s message. -/
def sealedC : World := shutdownActor fuseD held cId

theorem sealed_c_dead : (sealedC.st cId).life = .dead := rfl

theorem sibling_stays_alive : (sealedC.st hId).life = .alive := rfl

theorem sibling_still_holds : (sealedC.st hId).box = [fuseMail] := rfl

theorem queued_while_held : queuedFromKey sealedC "C" 0 "H" = 1 := rfl

theorem floor_idle : landFloor fuseD "C" "Idle" "H" = 1 := rfl

theorem floor_high : landFloor fuseD "C" "High" "H" = 0 := rfl

/-- A birth at this moment would be short one token. It is not a step. -/
theorem premature_tokens : (bornActor fuseD sealedC "C" 0 "Idle").tokens "H" = 0 := rfl

theorem premature_short :
    ¬ ((landFloor fuseD "C" "Idle" "H" : Int) ≤ (bornActor fuseD sealedC "C" 0 "Idle").tokens "H") := by
  decide

theorem tombstone_withheld : tombstoneWaits sealedC ((sealedC.st pId).prio.head!) = true := rfl

theorem held_receive_skips : receivePrio fuseI sealedC pId = none := rfl

theorem slot_blocked : slotRespawnBlocked fuseD sealedC pId "C" 0 = true := rfl

/-- `H` consumes the message. The refund finds no live generation of `C`. -/
def consumed : World :=
  match receiveBulk fuseI sealedC hId with
  | some w => w
  | none => sealedC

theorem consume_runs : receiveBulk fuseI sealedC hId = some consumed := rfl

theorem queued_after_consume : queuedFromKey consumed "C" 0 "H" = 0 := rfl

theorem mail_consumed : mailInFlight consumed cId = false := rfl

theorem credit_to_dead : (consumed.st cId).tokens "H" = 1 := rfl

theorem next_not_born : (consumed.st cNext).life = .absent := rfl

/-- The tombstone is now receivable, and the handler spawns `C'`. -/
def delivered : World :=
  match receivePrio fuseI consumed pId with
  | some w => w
  | none => consumed

theorem tombstone_delivered : receivePrio fuseI consumed pId = some delivered := rfl

def spawned : World :=
  match execHead fuseI delivered pId with
  | some w => w
  | none => delivered

theorem handler_spawns : execHead fuseI delivered pId = some spawned := rfl

theorem spawned_alive : (spawned.st cNext).life = .alive := rfl

theorem spawned_idle : (spawned.st cNext).phase = .idle ∧ (spawned.st cNext).typestate = "Idle" :=
  ⟨rfl, rfl⟩

theorem spawned_tokens : (spawned.st cNext).tokens "H" = 1 := rfl

theorem spawned_queued : queuedFromKey spawned "C" 0 "H" = 0 := rfl

theorem spawned_floor_fits :
    (landFloor fuseD "C" "Idle" "H" : Int) ≤ (spawned.st cNext).tokens "H" := by
  decide

theorem spawned_hold_fits :
    (tokenHold fuseD "C" "H" (spawned.st cNext) : Int) ≤ (spawned.st cNext).tokens "H" := by
  decide

theorem spawned_not_crashed : spawned.crashed = false := rfl

/-- The same sibling, sealed instead of consuming. The box is cleared in that
step, so the later birth is not charged for the message. -/
def siblingSealed : World := shutdownActor fuseD sealedC hId

theorem sibling_sealed_dead : (siblingSealed.st hId).life = .dead := rfl

theorem sibling_box_cleared : (siblingSealed.st hId).box = [] := rfl

theorem sibling_not_crashed : siblingSealed.crashed = false := rfl

theorem queued_after_sibling_seal : queuedFromKey siblingSealed "C" 0 "H" = 0 := rfl

theorem mail_gone_when_sibling_seals : mailInFlight siblingSealed cId = false := rfl

theorem sibling_seal_credits_dead : (siblingSealed.st cId).tokens "H" = 1 := rfl

def siblingDelivered : World :=
  match receivePrio fuseI siblingSealed pId with
  | some w => w
  | none => siblingSealed

theorem sibling_tombstone_delivered :
    receivePrio fuseI siblingSealed pId = some siblingDelivered := rfl

def siblingSpawned : World :=
  match execHead fuseI siblingDelivered pId with
  | some w => w
  | none => siblingDelivered

theorem sibling_handler_spawns : execHead fuseI siblingDelivered pId = some siblingSpawned := rfl

theorem sibling_spawn_tokens : (siblingSpawned.st cNext).tokens "H" = 1 := rfl

theorem sibling_spawn_fits :
    (landFloor fuseD "C" "Idle" "H" : Int) ≤ (siblingSpawned.st cNext).tokens "H" := by
  decide

/-- The same sealed world with the tombstone taken off the live parent's lane
by a state edit, not by `receivePrio`. Nothing in the occupancy account puts
that tombstone back, and the sibling still holds the message, so a spawn of
this edited state admits the next generation. That generation is short.
`cleared_spawn` records that the receive does not produce this state. -/
def cleared : World :=
  { sealedC with
    nextIx := fun _ => 1
    st := fun i =>
      if i = pId then { sealedC.st pId with prio := [] } else sealedC.st i }

theorem cleared_parent_alive : (cleared.st pId).life = .alive := rfl

theorem cleared_not_crashed : cleared.crashed = false := rfl

theorem cleared_budget : budget fuseD "C" "H" = 1 := rfl

theorem cleared_parent_floor : landFloor fuseD "P" "Idle" "H" = 0 := rfl

theorem cleared_host_floor : landFloor fuseD "H" "Idle" "H" = 0 := rfl

theorem cleared_child_empty : (cleared.st cId).box = [] ∧ (cleared.st cId).parked = [] := ⟨rfl, rfl⟩

theorem cleared_dead_gen : (cleared.st cId).life = .dead ∧ cId ∈ cleared.roster := by
  decide

theorem cleared_queued : queuedFromKey cleared "C" 0 "H" = 1 := rfl

theorem cleared_gen : maxGen cleared "C" 0 = 1 := rfl

theorem cleared_free : slotRespawnBlocked fuseD cleared pId "C" 0 = false := rfl

theorem cleared_born_tokens : (bornActor fuseD cleared "C" 0 "Idle").tokens "H" = 0 := rfl

theorem cleared_floor : landFloor fuseD "C" "Idle" "H" = 1 := rfl

/-- The admitted generation is idle in `Idle`, whose floor is the whole budget,
while `withKeyTokens` left it the budget minus the queued message. -/
theorem cleared_short :
    ¬ ((tokenHold fuseD "C" "H"
        { bornActor fuseD cleared "C" 0 "Idle" with parent := some pId } : Int) ≤
        (bornActor fuseD cleared "C" 0 "Idle").tokens "H") := by
  decide

theorem cleared_flight : mailInFlight cleared cId = true := rfl

theorem cleared_parent : (cleared.st cId).parent = some pId := rfl

theorem cleared_no_tomb : ¬ HoldsTomb cleared pId cId := by
  intro h
  rcases h with ⟨_, hm, _, _⟩
  simp [cleared] at hm

/-- The parent's lane no longer holds the dead child's tombstone, while the
child's mail is still at the live sibling. A real receive cannot take that
tombstone (`cleared_spawn`); this edit is outside the tombstone chain. -/
theorem cleared_not_chain : ¬ TombChain cleared := by
  intro h
  have hstep := h cId cleared_not_crashed cleared_dead_gen.1 cleared_flight
  rw [cleared_parent] at hstep
  simp at hstep
  rcases hstep with ⟨_, htomb⟩ | hdead
  · exact cleared_no_tomb htomb
  · exact hdead.1 cleared_parent_alive

theorem cleared_not_inv : ¬ Inv fuseI cleared :=
  fun h => cleared_not_chain h.seal.chain

theorem cleared_installed_tokens :
    ((admitBorn fuseI cleared cNext
        { bornActor fuseD cleared "C" 0 "Idle" with parent := some pId }).st cNext).tokens "H" = 0 ∧
      ((admitBorn fuseI cleared cNext
        { bornActor fuseD cleared "C" 0 "Idle" with parent := some pId }).st cNext).phase = .idle ∧
      ((admitBorn fuseI cleared cNext
        { bornActor fuseD cleared "C" 0 "Idle" with parent := some pId }).st cNext).life = .alive :=
  ⟨rfl, rfl, rfl⟩

/-- The same sealed world, with `C`'s message only on `H`'s parked lane. -/
def parkedHold : World :=
  { sealedC with
    st := fun i =>
      if i = hId then
        { sealedC.st hId with
          box := []
          parked := [{ sender := cId, msg := fuseMail, isCall := false }] }
      else sealedC.st i }

theorem parked_host_alive : (parkedHold.st hId).life = .alive := rfl

theorem parked_queued : queuedFromKey parkedHold "C" 0 "H" = 1 := rfl

theorem parked_box_empty : (parkedHold.st hId).box = [] := rfl

/-- The box still holds the message, so the parent cannot take the tombstone.
The slot stays blocked and `spawnChild` is the world it was given. -/
theorem cleared_spawn :
    receivePrio fuseI sealedC pId = none ∧
      spawnChild fuseI sealedC pId "C" = some sealedC :=
  ⟨rfl, rfl⟩

/-- `H` is alive and the parked entry's sender is dead. `releaseOutbound`
would have dropped that entry in the seal, so this world is not `ParkedFromLive`
and therefore not `Inv`. The receive does not refuse it: the exclusion is the
invariant, not a second scan of the parked lane. -/
theorem parked_not_live : ¬ ParkedFromLive parkedHold := by
  intro h
  have hmem : ({ sender := cId, msg := fuseMail, isCall := false } : Parked) ∈
      (parkedHold.st hId).parked := by
    simp [parkedHold]
  have hdead := h hId _ parked_host_alive hmem
  simp [parkedHold] at hdead
  have hne : ¬ cId = hId := by decide
  rw [ite_eq_right hne] at hdead
  exact hdead sealed_c_dead

theorem parked_receive :
    (receivePrio fuseI parkedHold pId).isSome = true := rfl

theorem parked_not_inv : ¬ Inv fuseI parkedHold :=
  not_inv_of_parked parked_not_live

/-- A dead host's own priority message does not keep the tombstone. The lane
checks sit under the liveness test. -/
def deadPrio : World :=
  { sealedC with
    st := fun i =>
      if i = hId then { sealedC.st hId with box := [] }
      else if i = cId then { sealedC.st cId with prio := [fuseMail] }
      else sealedC.st i }

theorem dead_prio_flight : mailInFlight deadPrio cId = false := rfl

end Deadlock
