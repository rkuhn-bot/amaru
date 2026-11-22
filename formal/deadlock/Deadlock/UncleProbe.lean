/-
`C` sends to `U`. `U` is a sibling of `C`'s parent `P`, so sealing `P`
does not seal `U` and does not clear `U`'s box. `P`'s own lane is cleared,
and with it `C`'s tombstone. `C`'s message is still sealed together with
`P`, so `P`'s tombstone on `R` waits and `R` cannot birth the next `P`.
-/

import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock

def uncleTpl (name : String) (sup : Option String) (tomb : String) (states : List String) : Template where
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

def uncleEdge : Edge where
  src := "C"
  srcState := "High"
  dst := "U"
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

def uncleD : Description where
  name := "uncle"
  freshNames := true
  templates :=
    [uncleTpl "R" none "" ["Idle"],
     uncleTpl "P" (some "R") "pdied" ["Idle"],
     uncleTpl "C" (some "P") "died" ["Idle", "High"],
     uncleTpl "U" (some "R") "udied" ["Idle"]]
  edges := [uncleEdge]
  compatibility := .all
  steps := []

def uncleTr (template src label dst : String) (program : List Eff) : Transition where
  template := template
  fromState := src
  label := label
  program := program
  toState := dst
  acceptsCall := false
  release := 1

def uncleI : Impl where
  desc := uncleD
  transitions :=
    [uncleTr "U" "Idle" "m" "Idle" [],
     uncleTr "R" "Idle" "pdied" "Idle" [.spawn "P"],
     uncleTr "P" "Idle" "died" "Idle" [.spawn "C"]]

def rId : InstId := .peer "R" 0 0
def pId : InstId := .peer "P" 0 0
def cId : InstId := .peer "C" 0 0
def uId : InstId := .peer "U" 0 0
def pNext : InstId := .peer "P" 0 1
def cNext : InstId := .peer "C" 0 1

def uncleMail : Msg where
  label := "m"
  sender := cId
  callFrom := none

def uncleActor (life : Life) (box : List Msg) : Actor where
  life := life
  typestate := "Idle"
  phase := .idle
  box := box
  prio := []
  parked := []
  tokens := fun _ => 0

/-- `C` has already sent. `U` holds the message. Everyone is alive. -/
def uncleLive : World where
  N := 1
  roster := [rId, pId, cId, uId]
  nextIx := fun _ => 0
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0
  st := fun i =>
    if i = rId then { uncleActor .alive [] with }
    else if i = pId then { uncleActor .alive [] with parent := some rId }
    else if i = cId then { uncleActor .alive [] with parent := some pId, typestate := "High" }
    else if i = uId then { uncleActor .alive [uncleMail] with parent := some rId }
    else { uncleActor .absent [] with }

def uncleSealedC : World := shutdownActor uncleD uncleLive cId

theorem child_sealed : (uncleSealedC.st cId).life = .dead := rfl

theorem uncle_holds_after_child : (uncleSealedC.st uId).box = [uncleMail] := rfl

theorem child_tombstone_on_parent : slotRespawnBlocked uncleD uncleSealedC pId "C" 0 = true := rfl

/-- Sealing `P` is the next step. `U` is not a descendant, so the message stays. -/
def parentSealed : World := shutdownActor uncleD uncleSealedC pId

theorem parent_dead : (parentSealed.st pId).life = .dead := rfl

theorem uncle_stays : (parentSealed.st uId).life = .alive := rfl

theorem uncle_keeps_mail : (parentSealed.st uId).box = [uncleMail] := rfl

theorem parent_lane_cleared : (parentSealed.st pId).prio = [] := rfl

theorem mail_still_in_flight : mailInFlight parentSealed cId = true := rfl

theorem queued_after_parent : queuedFromKey parentSealed "C" 0 "U" = 1 := rfl

theorem parent_not_crashed : parentSealed.crashed = false := rfl

/-- `C`'s mail is sealed together with `P`, so `P`'s tombstone waits on `R`. -/
theorem parent_tombstone_waits :
    tombstoneWaits parentSealed ((parentSealed.st rId).prio.head!) = true := rfl

theorem parent_receive_skips : receivePrio uncleI parentSealed rId = none := rfl

theorem parent_slot_blocked : slotRespawnBlocked uncleD parentSealed rId "P" 0 = true := rfl

end Deadlock
