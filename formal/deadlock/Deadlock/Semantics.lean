/-
Operational semantics of a finite network of actors with bounded mailboxes.

Internal timeouts are erased: a call reply is a oneshot that never uses the caller's
bulk mailbox, and the only way a call ends is a reply or an explicit lifecycle step
that the description has ruled out. Peer waits and internal effects complete
independently of every other actor. Self-schedule overflow crashes; it does not wait.
-/

import Deadlock.Graph

set_option autoImplicit false

namespace Deadlock

inductive InstId where
  | core (name : String)
  | peer (name : String) (index : Nat)
  deriving DecidableEq, Repr, Inhabited

def tname : InstId → String
  | .core n => n
  | .peer n _ => n

inductive Life where
  | absent
  | alive
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- A finite program of effects. `hint` selects a per-peer instance; it is ignored for a
core template. -/
inductive Eff where
  | send (dst : String) (hint : Nat)
  | trySend (dst : String) (hint : Nat)
  | call (dst : String) (hint : Nat)
  | reply
  | selfSchedule
  | cell (dst : String) (label : String)
  | internal
  | peer
  | terminate
  deriving DecidableEq, Repr, Inhabited

structure Cont where
  rest : List Eff
  toState : String
  replyTo : Option InstId
  deriving DecidableEq, Repr, Inhabited

inductive Phase where
  | idle
  | run (k : Cont)
  | parked (dst : InstId) (isCall : Bool) (k : Cont)
  | awaitReply (dst : InstId) (k : Cont)
  | awaitEffect (k : Cont)
  | awaitPeer (k : Cont)
  | crashed
  deriving DecidableEq, Repr, Inhabited

structure Msg where
  label : String
  sender : InstId
  callFrom : Option InstId
  deriving DecidableEq, Repr, Inhabited

/-- FIFO admission queue. The sender's phase is the source of truth for the continuation. -/
structure Parked where
  sender : InstId
  msg : Msg
  isCall : Bool
  deriving DecidableEq, Repr, Inhabited

structure Actor where
  life : Life
  typestate : String
  phase : Phase
  box : List Msg
  prio : List Msg
  parked : List Parked
  deriving DecidableEq, Repr, Inhabited

def absentActor : Actor where
  life := .absent
  typestate := ""
  phase := .idle
  box := []
  prio := []
  parked := []

structure Cell where
  value : Nat
  dirty : Bool
  deriving DecidableEq, Repr, Inhabited

def cleanCell : Cell := { value := 0, dirty := false }

structure World where
  N : Nat
  st : InstId → Actor
  cell : String → String → Cell

def setActor (w : World) (id : InstId) (a : Actor) : World :=
  { w with st := fun i => if i = id then a else w.st i }

def setCell (w : World) (dst label : String) (c : Cell) : World :=
  { w with cell := fun d l => if d = dst && l = label then c else w.cell d l }

theorem setActor_self (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).st id = a := by
  simp [setActor]

theorem setActor_other (w : World) (id i : InstId) (a : Actor) (h : i ≠ id) :
    (setActor w id a).st i = w.st i := by
  simp [setActor, h]

structure Transition where
  template : String
  fromState : String
  label : String
  program : List Eff
  toState : String
  acceptsCall : Bool
  deriving DecidableEq, Repr, Inhabited

structure Impl where
  desc : Description
  transitions : List Transition

def validId (D : Description) (N : Nat) : InstId → Bool
  | .core n =>
    match templateOf D n with
    | some t => decide (t.multiplicity = .one)
    | none => false
  | .peer n k =>
    decide (k < N) &&
      match templateOf D n with
      | some t => decide (t.multiplicity = .perPeer)
      | none => false

def capBulk (D : Description) (N : Nat) (id : InstId) : Nat :=
  match templateOf D (tname id) with
  | some t => t.capacity.eval N
  | none => 0

def capPrio (D : Description) (N : Nat) (id : InstId) : Nat :=
  match templateOf D (tname id) with
  | some t => t.priorityCapacity.eval N
  | none => 0

def boundPrio (D : Description) (N : Nat) (id : InstId) : Nat :=
  match templateOf D (tname id) with
  | some t => t.priorityBound.eval N
  | none => 0

def findTr (I : Impl) (template state label : String) : Option Transition :=
  I.transitions.findSome? fun tr =>
    if tr.template == template && tr.fromState == state && tr.label == label then some tr else none

def route (D : Description) (N : Nat) (dst : String) (hint : Nat) : Option InstId :=
  match templateOf D dst with
  | none => none
  | some t =>
    match t.multiplicity with
    | .one => some (.core dst)
    | .perPeer => if hint < N then some (.peer dst hint) else none

def proceed (a : Actor) (k : Cont) : Actor :=
  match k.rest with
  | [] => { a with phase := .idle, typestate := k.toState }
  | _ => { a with phase := .run k }

def afterHead (k : Cont) : Cont :=
  { k with rest := k.rest.tail }

def deliver (I : Impl) (receiver : InstId) (a : Actor) (m : Msg) : Actor :=
  if a.life ≠ .alive then a
  else
    match findTr I (tname receiver) a.typestate m.label with
    | none => { a with phase := .idle }
    | some tr =>
      let k : Cont := { rest := tr.program, toState := tr.toState, replyTo := m.callFrom }
      if tr.program.isEmpty then { a with phase := .idle, typestate := tr.toState }
      else { a with phase := .run k }

def resumeSender (a : Actor) (isCall : Bool) (dst : InstId) : Actor :=
  match a.phase with
  | .parked _ _ k =>
    if isCall then { a with phase := .awaitReply dst k } else proceed a k
  | _ => a

/-- Pop one bulk message, then admit the head parked sender if a slot is free.
A zero-capacity mailbox rendezvous-delivers the head parked message. -/
def receiveBulk (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive || a.phase ≠ .idle then none
  else
    match a.box, a.parked with
    | m :: ms, [] =>
      some (setActor w id (deliver I id { a with box := ms } m))
    | m :: ms, p :: ps =>
      -- The box message is ahead of every parked sender. Taking it frees a slot,
      -- which is given to the head of the park queue (FIFO).
      let delivered := deliver I id { a with box := ms } m
      let admitted := { delivered with box := delivered.box ++ [p.msg], parked := ps }
      some (setActor (setActor w id admitted) p.sender (resumeSender (w.st p.sender) p.isCall id))
    | [], p :: ps =>
      -- Empty mailbox with parked senders: deliver the head directly (zero-capacity
      -- rendezvous, or the slot that the invariant says is free).
      let delivered := deliver I id { a with parked := ps } p.msg
      some (setActor (setActor w id delivered) p.sender (resumeSender (w.st p.sender) p.isCall id))
    | [], [] => none

def receivePrio (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive || a.phase ≠ .idle || a.prio = [] then none
  else
    let m := a.prio.head!
    some (setActor w id (deliver I id { a with prio := a.prio.tail } m))

def enqueueOrPark (I : Impl) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : World :=
  let target := w.st dst
  let cap := capBulk I.desc w.N dst
  if target.life ≠ .alive then
    -- Send to a dead or absent actor drops. A call to one waits forever in ⟦·⟧^∞;
    -- refinement forbids that case for reachable worlds.
    if isCall then
      setActor w sender { w.st sender with phase := .awaitReply dst k }
    else
      setActor w sender (proceed (w.st sender) k)
  else if target.parked = [] && target.box.length < cap then
    let target := { target with box := target.box ++ [msg] }
    let w := setActor w dst target
    if isCall then
      setActor w sender { w.st sender with phase := .awaitReply dst k }
    else
      setActor w sender (proceed (w.st sender) k)
  else
    let target := { target with parked := target.parked ++ [{ sender, msg, isCall }] }
    let w := setActor w dst target
    setActor w sender { w.st sender with phase := .parked dst isCall k }

def performReply (w : World) (sender : InstId) (k : Cont) : World :=
  match k.replyTo with
  | none => setActor w sender (proceed (w.st sender) (afterHead k))
  | some caller =>
    match (w.st caller).phase with
    | .awaitReply _ ck =>
      let w := setActor w caller (proceed (w.st caller) ck)
      setActor w sender (proceed (w.st sender) (afterHead k))
    | _ =>
      setActor w sender (proceed (w.st sender) (afterHead k))

def tryWake (I : Impl) (w : World) (dstId : InstId) (label : String) : World :=
  let target := w.st dstId
  let cap := capBulk I.desc w.N dstId
  if target.life = .alive && target.parked = [] && target.box.length < cap then
    let msg : Msg := { label := label, sender := dstId, callFrom := none }
    setActor w dstId { target with box := target.box ++ [msg] }
  else
    -- Full, or someone is parked: keep the dirty bit, drop the wake. No parking.
    w

def execRun (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) : World :=
  match k.rest with
  | [] => setActor w id { a with phase := .idle, typestate := k.toState }
  | eff :: _ =>
    let k' := afterHead k
    match eff with
    | .send dst hint =>
      match route I.desc w.N dst hint with
      | none => setActor w id (proceed a k')
      | some dstId =>
        let msg : Msg := { label := "send", sender := id, callFrom := none }
        enqueueOrPark I w id dstId msg false k'
    | .trySend dst hint =>
      match route I.desc w.N dst hint with
      | none => setActor w id (proceed a k')
      | some dstId =>
        let target := w.st dstId
        let cap := capBulk I.desc w.N dstId
        if target.life = .alive && target.parked = [] && target.box.length < cap then
          let msg : Msg := { label := "try", sender := id, callFrom := none }
          let w := setActor w dstId { target with box := target.box ++ [msg] }
          setActor w id (proceed (w.st id) k')
        else
          setActor w id (proceed a k')
    | .call dst hint =>
      match route I.desc w.N dst hint with
      | none => setActor w id { a with phase := .awaitReply (.core dst) k' }
      | some dstId =>
        let msg : Msg := { label := "call", sender := id, callFrom := some id }
        enqueueOrPark I w id dstId msg true k'
    | .reply => performReply w id k
    | .selfSchedule =>
      let cap := capPrio I.desc w.N id
      if a.prio.length < cap then
        let msg : Msg := { label := "self", sender := id, callFrom := none }
        setActor w id (proceed { a with prio := a.prio ++ [msg] } k')
      else
        setActor w id { a with phase := .crashed }
    | .cell dst label =>
      let previous := w.cell dst label
      let w := setCell w dst label { value := previous.value + 1, dirty := true }
      let w := setActor w id (proceed (w.st id) k')
      if previous.dirty then w
      else
        match route I.desc w.N dst 0 with
        | none => w
        | some dstId => tryWake I w dstId label
    | .internal => setActor w id { a with phase := .awaitEffect k' }
    | .peer => setActor w id { a with phase := .awaitPeer k' }
    | .terminate =>
      let dead : Actor := { a with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
      -- Parked senders resume (the message is lost). Calls into a terminable template are
      -- rejected by the graph check, so a parked call is not left waiting here.
      let parked := (w.st id).parked
      let w := setActor w id dead
      parked.foldl (fun w p => setActor w p.sender (resumeSender (w.st p.sender) false id)) w

def execHead (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive then none
  else
    match a.phase with
    | .run k => some (execRun I w id a k)
    | _ => none

def finishWait (w : World) (id : InstId) : Option World :=
  match (w.st id).phase with
  | .awaitEffect k => some (setActor w id (proceed (w.st id) k))
  | .awaitPeer k => some (setActor w id (proceed (w.st id) k))
  | _ => none

def spawn (D : Description) (w : World) (id : InstId) : Option World :=
  if validId D w.N id && (w.st id).life = .absent then
    match templateOf D (tname id) with
    | none => none
    | some t =>
      some (setActor w id
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [] })
  else
    none

inductive Action where
  | recvBulk (s : InstId)
  | recvPrio (s : InstId)
  | exec (s : InstId)
  | finish (s : InstId)
  | spawn (s : InstId)
  deriving DecidableEq, Repr

def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait w s
  | .spawn s => spawn I.desc w s

def Enabled (I : Impl) (w : World) (a : Action) : Prop :=
  apply I a w ≠ none

def forced : Action → Bool
  | .spawn _ => false
  | _ => true

def initActor (D : Description) (N : Nat) (id : InstId) : Actor :=
  if validId D N id then
    match templateOf D (tname id) with
    | some t =>
      { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [] }
    | none => absentActor
  else
    absentActor

def initWorld (I : Impl) (N : Nat) : World where
  N := N
  st := initActor I.desc N
  cell := fun _ _ => cleanCell

inductive Reachable (I : Impl) (N : Nat) : World → Prop where
  | init : Reachable I N (initWorld I N)
  | step (w w' : World) (a : Action) : Reachable I N w → apply I a w = some w' → Reachable I N w'

/-- A run at instance count `N`, starting from the initial world. -/
structure Run (I : Impl) (N : Nat) where
  cfg : Nat → World
  act : Nat → Action
  startN : (cfg 0).N = N
  start : cfg 0 = initWorld I N
  valid : ∀ i, apply I (act i) (cfg i) = some (cfg (i + 1))

def alive (w : World) (id : InstId) : Prop :=
  (w.st id).life = .alive

def Idle (w : World) (id : InstId) : Prop :=
  alive w id ∧ (w.st id).phase = .idle

def CanReceive (w : World) (id : InstId) : Prop :=
  Idle w id ∧ ((w.st id).box ≠ [] ∨ (w.st id).parked ≠ [])

structure Fair {I : Impl} {N : Nat} (ρ : Run I N) : Prop where
  /-- F1. A forced action that stays enabled is taken. -/
  weak : ∀ (a : Action) (i : Nat), forced a = true →
    (∀ j, i ≤ j → Enabled I (ρ.cfg j) a) → ∃ j, i ≤ j ∧ ρ.act j = a
  /-- F3. Priority traffic does not starve bulk work, including a zero-capacity
  rendezvous with a nonempty park queue. F2 (FIFO admission) is `enqueueOrPark`. -/
  bulk : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ CanReceive (ρ.cfg j) s) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)

/-! Deadlock, including the partial form and the caller-mailbox pattern. -/

inductive WaitKind where
  | blockingSend (dst : InstId)
  | callReply (dst : InstId)
  | cell
  | effect
  | peer
  deriving DecidableEq, Repr

def waitKind (a : Actor) : Option WaitKind :=
  match a.phase with
  | .parked dst isCall _ => some (if isCall then .callReply dst else .blockingSend dst)
  | .awaitReply dst _ => some (.callReply dst)
  | .awaitEffect _ => some .effect
  | .awaitPeer _ => some .peer
  | _ => none

def SameWait (a b : Actor) : Prop :=
  waitKind a = waitKind b ∧ waitKind a ≠ none

def Stuck {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i : Nat) : Prop :=
  SameWait ((ρ.cfg i).st s) ((ρ.cfg i).st s) ∧
    ∀ j, i ≤ j → SameWait ((ρ.cfg i).st s) ((ρ.cfg j).st s)

/-- Internal deadlock: forever blocked on a send, a call reply, a cell, or an effect.
Peer waits are recorded separately; fairness discharges both. -/
def Deadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ s i, Stuck ρ s i ∧
    match waitKind ((ρ.cfg i).st s) with
    | some (.blockingSend _) => True
    | some (.callReply _) => True
    | some .cell => True
    | some .effect => True
    | _ => False

def PartialDeadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ s i, Stuck ρ s i ∧ ∃ t j, t ≠ s ∧ i ≤ j ∧
    match ρ.act j with
    | .recvBulk u => u = t
    | .recvPrio u => u = t
    | .exec u => u = t
    | .finish u => u = t
    | .spawn u => u = t

def GlobalDeadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ i, (∃ s, alive (ρ.cfg i) s) ∧ ∀ s, alive (ρ.cfg i) s → Stuck ρ s i

/-- A caller blocked on a reply while its own bulk mailbox is full. The reply path does
not use that mailbox; persistence of this pattern is still a call deadlock. -/
def CallerMailboxFull (D : Description) (w : World) (s : InstId) : Prop :=
  match (w.st s).phase with
  | .awaitReply _ _ => (w.st s).box.length = capBulk D w.N s
  | _ => False

/-- Cell writes do not have a waiting phase. `WaitKind.cell` is the classification a
phase would have if a cell read blocked; no phase is in that class. -/
theorem waitKind_ne_cell (a : Actor) : waitKind a ≠ some .cell := by
  intro hEq
  cases h : a.phase with
  | idle => simp [waitKind, h] at hEq
  | run _ => simp [waitKind, h] at hEq
  | parked _ isCall _ =>
    cases isCall with
    | false => simp [waitKind, h] at hEq
    | true => simp [waitKind, h] at hEq
  | awaitReply _ _ => simp [waitKind, h] at hEq
  | awaitEffect _ => simp [waitKind, h] at hEq
  | awaitPeer _ => simp [waitKind, h] at hEq
  | crashed => simp [waitKind, h] at hEq

def WaitingOnCell (a : Actor) : Prop := waitKind a = some .cell

end Deadlock
