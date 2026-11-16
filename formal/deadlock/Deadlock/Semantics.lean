/-
Operational semantics of actors with bounded mailboxes, oneshot call replies,
dirty-bit cells, and fresh-name restart.

`N` bounds how many instances of each per-peer template are alive at once.
Instance indices themselves are unbounded: a restart allocates a fresh index
and the dead id is never reused.
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

/-- Effects carry the real message label. `hint` is a per-peer index; cores ignore it. -/
inductive Eff where
  | send (dst label : String) (hint : Nat)
  | trySend (dst label : String) (hint : Nat)
  | call (dst label : String) (hint : Nat)
  | reply
  | selfSchedule (label : String)
  | cell (dst label : String) (value : Nat)
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
  /-- Identity issued by the actor that accepts the message. -/
  mid : Nat := 0
  /-- A try-drop send and a superseding cell wake are not delivery obligations. -/
  reliable : Bool := true
  deriving DecidableEq, Repr, Inhabited

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
  /-- Remaining send slots per destination template. `tokens dst + msgsTo dst = budget`. -/
  tokens : String → Nat
  /-- Next identity this actor stamps on a message it accepts. -/
  nextMid : Nat := 0
  deriving Inhabited

def absentActor : Actor where
  life := .absent
  typestate := ""
  phase := .idle
  box := []
  prio := []
  parked := []
  tokens := fun _ => 0

structure Cell where
  value : Nat
  dirty : Bool
  deriving DecidableEq, Repr, Inhabited

def cleanCell : Cell := { value := 0, dirty := false }

structure World where
  N : Nat
  roster : List InstId
  nextIx : String → Nat
  st : InstId → Actor
  cell : String → String → Cell
  observed : InstId → String → Nat

def setActor (w : World) (id : InstId) (a : Actor) : World :=
  { w with st := fun i => if i = id then a else w.st i }

def setCell (w : World) (dst label : String) (c : Cell) : World :=
  { w with cell := fun d l => if d = dst && l = label then c else w.cell d l }

def setObserved (w : World) (id : InstId) (label : String) (v : Nat) : World :=
  { w with observed := fun i l => if i = id && l = label then v else w.observed i l }

theorem setActor_self (w : World) (id : InstId) (a : Actor) : (setActor w id a).st id = a := by
  simp [setActor]

theorem setActor_other (w : World) (id i : InstId) (a : Actor) (h : i ≠ id) :
    (setActor w id a).st i = w.st i := by
  simp [setActor, h]

def bumpToken (a : Actor) (dst : String) (delta : Int) : Actor :=
  { a with tokens := fun d =>
      if d = dst then
        match delta with
        | .ofNat n => a.tokens d + n
        | .negSucc n => a.tokens d - (n + 1)
      else a.tokens d }

/-- One delivered message returns one slot to its sender. -/
def creditSender (w : World) (mailboxTemplate : String) (sender : InstId) : World :=
  setActor w sender (bumpToken (w.st sender) mailboxTemplate (.ofNat 1))

def chargeSender (a : Actor) (dstTemplate : String) : Actor :=
  bumpToken a dstTemplate (.negSucc 0)

structure Transition where
  template : String
  fromState : String
  label : String
  program : List Eff
  toState : String
  acceptsCall : Bool
  /-- Slots returned to the sender of the message that caused this transition.
  Bulk dequeue always returns one; this annotation is checked equal to 1. -/
  release : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Unused by the step relation. An internal effect always finishes. A timed
peer wait finishes as its timeout. An untimed peer finishes when a timed peer
in its cohort can end the chain; a pure untimed peer wait never does.
The fields remain so an environment value can still be attached to `Impl`. -/
structure Env where
  effectDone : World → InstId → Bool
  peerDone : World → InstId → Bool

/-- Default environment. `finishWait` does not read it. -/
def Env.always : Env where
  effectDone := fun _ _ => true
  peerDone := fun _ _ => true

structure Impl where
  desc : Description
  transitions : List Transition
  env : Env := Env.always

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

/-- Per-instance send budget read off an edge. Cores store it in `b` (`a = 0`);
per-peer templates store it in `a` (`b = 0`), so the total is `a * N`. -/
def perInstance (mult : Multiplicity) (occ : Affine) : Nat :=
  match mult with
  | .one => occ.b
  | .perPeer => occ.a

def debt (D : Description) (template state dst : String) : Nat :=
  match templateOf D template with
  | none => 0
  | some src =>
    D.edges.foldl (fun n e =>
      if e.src == template && e.srcState == state && e.dst == dst then n + perInstance src.multiplicity e.occupancy
      else n) 0

def budget (D : Description) (template dst : String) : Nat :=
  match templateOf D template with
  | none => 0
  | some t => t.states.foldl (fun m st => max m (debt D template st dst)) 0

def cellLabels (D : Description) (reader : String) : List String :=
  D.edges.filterMap fun e =>
    if e.effect == .cell && e.dst == reader then some e.label else none

def findTr (I : Impl) (template state label : String) : Option Transition :=
  I.transitions.findSome? fun tr =>
    if tr.template == template && tr.fromState == state && tr.label == label then some tr else none

def aliveCount (w : World) (template : String) : Nat :=
  w.roster.foldl (fun n id =>
    if tname id == template && (w.st id).life == .alive then n + 1 else n) 0

/-- A live target only. Absent and dead names are not routes. -/
def route (w : World) (D : Description) (dst : String) (hint : Nat) : Option InstId :=
  match templateOf D dst with
  | none => none
  | some t =>
    match t.multiplicity with
    | .one =>
      let id := InstId.core dst
      if (w.st id).life == .alive then some id else none
    | .perPeer =>
      let id := InstId.peer dst hint
      if (w.st id).life == .alive then some id else none

def proceed (a : Actor) (k : Cont) : Actor :=
  match k.rest with
  | [] => { a with phase := .idle, typestate := k.toState }
  | _ => { a with phase := .run k }

def afterHead (k : Cont) : Cont :=
  { k with rest := k.rest.tail }

def withTokens (D : Description) (template : String) (a : Actor) : Actor :=
  { a with tokens := fun dst => budget D template dst }

/-- Every transition the reader takes clears dirty and records the value. -/
def readCells (D : Description) (w : World) (reader : InstId) : World :=
  (cellLabels D (tname reader)).foldl (fun w label =>
    let c := w.cell (tname reader) label
    let w := setCell w (tname reader) label { c with dirty := false }
    setObserved w reader label c.value) w

/-- Deliver `m` to a live actor. A call with no `acceptsCall` transition is refused
(`none`) so the message is not dropped. A non-call with no transition is consumed. -/
def deliver (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) : Option (World × Actor) :=
  let w := readCells I.desc w id
  if a.life ≠ .alive then none
  else
    match findTr I (tname id) a.typestate m.label with
    | none =>
      if m.callFrom.isSome then none
      else some (w, { a with phase := .idle })
    | some tr =>
      if m.callFrom.isSome && !tr.acceptsCall then none
      else
        -- Typestate moves at the start of the transition, so messages this program
        -- sends are outstanding while the actor is already in `toState`.
        -- The sender of `m` is credited by the receive, not here: priority
        -- deliveries were never charged.
        let k : Cont := { rest := tr.program, toState := tr.toState, replyTo := m.callFrom }
        let a' := if tr.program.isEmpty then { a with phase := .idle, typestate := tr.toState }
          else { a with typestate := tr.toState, phase := .run k }
        some (w, a')

def resumeSender (a : Actor) (isCall : Bool) (dst : InstId) : Actor :=
  match a.phase with
  | .parked _ _ k => if isCall then { a with phase := .awaitReply dst k } else proceed a k
  | _ => a

def receiveBulk (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive || a.phase ≠ .idle then none
  else
    match a.box, a.parked with
    | m :: ms, [] =>
      match deliver I w id { a with box := ms } m with
      | none => none
      | some (w, a') =>
        -- Credit after installing `a'`, so a self-sent message is not overwritten.
        some (creditSender (setActor w id a') (tname id) m.sender)
    | m :: ms, p :: ps =>
      match deliver I w id { a with box := ms } m with
      | none => none
      | some (w, a') =>
        let admitted := { a' with box := a'.box ++ [p.msg], parked := ps }
        let w := creditSender (setActor w id admitted) (tname id) m.sender
        let resumed := resumeSender (w.st p.sender) p.isCall id
        some (setActor w p.sender resumed)
    | [], p :: ps =>
      match deliver I w id { a with parked := ps } p.msg with
      | none => none
      | some (w, a') =>
        let w := creditSender (setActor w id a') (tname id) p.msg.sender
        some (setActor w p.sender (resumeSender (w.st p.sender) p.isCall id))
    | [], [] => none

def receivePrio (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  match a.prio with
  | [] => none
  | m :: ms =>
    if a.life ≠ .alive || a.phase ≠ .idle then none
    else
      match deliver I w id { a with prio := ms } m with
      | none => none
      | some (w, a') => some (setActor w id a')

def enqueueOrPark (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : World :=
  let target := w.st dst
  let cap := capBulk D w.N dst
  if target.life ≠ .alive then
    -- Absent or dead: the message is not stored and the sender is not charged.
    -- A call is excluded here; it does not become a wait on a missing name.
    setActor w sender (proceed (w.st sender) k)
  else
    let senderA := chargeSender (w.st sender) (tname dst)
    let room := decide (target.parked = []) && decide (target.box.length < cap)
    let same := decide (sender = dst)
    -- The id belongs to the actor that stores the message. A self-send stores it
    -- on the sender after the charge, which does not move `nextMid`.
    let host := if same then senderA else target
    let issued : Msg := { msg with mid := host.nextMid }
    let entry : Parked := { sender := sender, msg := issued, isCall := isCall }
    if room then
      if same then
        let self : Actor :=
          { senderA with box := senderA.box ++ [issued], nextMid := host.nextMid + 1 }
        if isCall then setActor w sender { self with phase := .awaitReply dst k }
        else setActor w sender (proceed self k)
      else
        let stored : Actor :=
          { target with box := target.box ++ [issued], nextMid := host.nextMid + 1 }
        let w := setActor w dst stored
        if isCall then setActor w sender { senderA with phase := .awaitReply dst k }
        else setActor w sender (proceed senderA k)
    else if same then
      let self : Actor :=
        { senderA with parked := senderA.parked ++ [entry], nextMid := host.nextMid + 1 }
      setActor w sender { self with phase := .parked dst isCall k }
    else
      let stored : Actor :=
        { target with parked := target.parked ++ [entry], nextMid := host.nextMid + 1 }
      let w := setActor w dst stored
      setActor w sender { senderA with phase := .parked dst isCall k }

/-- Reply resumes the caller only when that caller is awaiting *this* sender. -/
def performReply (w : World) (sender : InstId) (k : Cont) : World :=
  let k' := afterHead k
  match k.replyTo with
  | none => setActor w sender (proceed (w.st sender) k')
  | some caller =>
    match (w.st caller).phase with
    | .awaitReply dst ck =>
      if dst = sender then
        let w := setActor w caller (proceed (w.st caller) ck)
        setActor w sender (proceed (w.st sender) k')
      else
        setActor w sender (proceed (w.st sender) k')
    | _ => setActor w sender (proceed (w.st sender) k')

/-- One wake per label on the priority lane. A full lane leaves the dirty bit set;
the next transition the reader does still read-and-clears. Wakes are not bulk
occupancy and are not charged. -/
def upsertPrio (prio : List Msg) (m : Msg) : List Msg :=
  if prio.any (fun p => p.label == m.label) then prio else prio ++ [m]

def tryWake (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId) : World :=
  let target := w.st dstId
  let cap := capPrio D w.N dstId
  -- A cell wake is a superseding write: it is not a reliable delivery.
  let wake : Msg :=
    { label := label, sender := writer, callFrom := none, reliable := false, mid := target.nextMid }
  if target.life == .alive && target.prio.length < cap && !(target.prio.any (fun p => p.label == label)) then
    setActor w dstId
      { target with prio := upsertPrio target.prio wake, nextMid := target.nextMid + 1 }
  else
    w

def readersOf (w : World) (dst : String) : List InstId :=
  w.roster.filter fun id => tname id == dst && (w.st id).life == .alive

def wakeReaders (D : Description) (w : World) (dst label : String) (writer : InstId) : World :=
  (readersOf w dst).foldl (fun w id => tryWake D w id label writer) w

def hasParkedCall (ps : List Parked) : Bool :=
  ps.any fun p => p.isCall

def refundMsgs (w : World) (dstName : String) (ms : List Msg) : World :=
  ms.foldl (fun w m => creditSender w dstName m.sender) w

def refundParked (w : World) (dstName : String) (ps : List Parked) : World :=
  ps.foldl (fun w p => creditSender w dstName p.msg.sender) w

def releaseParked (w : World) (id : InstId) (ps : List Parked) : World :=
  ps.foldl (fun w p =>
    if p.isCall || p.sender = id then w
    else setActor w p.sender (resumeSender (w.st p.sender) false id)) w

def execRun (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) : World :=
  match k.rest with
  | [] => setActor w id { a with phase := .idle, typestate := k.toState }
  | eff :: _ =>
    let k' := afterHead k
    match eff with
    | .send dst label hint =>
      match route w I.desc dst hint with
      | none => setActor w id (proceed a k')
      | some dstId =>
        let msg : Msg := { label := label, sender := id, callFrom := none }
        enqueueOrPark w I.desc id dstId msg false k'
    | .trySend dst label hint =>
      match route w I.desc dst hint with
      | none => setActor w id (proceed a k')
      | some dstId =>
        let target := w.st dstId
        let cap := capBulk I.desc w.N dstId
        if target.life == .alive && target.parked = [] && target.box.length < cap then
          -- Program `trySend` is the try-drop class: a full box discards it, and a
          -- copy that does land is not a reliable delivery obligation.
          let msg : Msg := { label := label, sender := id, callFrom := none, reliable := false }
          enqueueOrPark w I.desc id dstId msg false k'
        else
          setActor w id (proceed a k')
    | .call dst label hint =>
      match route w I.desc dst hint with
      | none =>
        -- No live target: the call is excluded, not turned into a wait on a dummy name.
        setActor w id (proceed a k')
      | some dstId =>
        let msg : Msg := { label := label, sender := id, callFrom := some id }
        enqueueOrPark w I.desc id dstId msg true k'
    | .reply => performReply w id k
    | .selfSchedule label =>
      let cap := capPrio I.desc w.N id
      let msg : Msg :=
        { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
      -- Re-arming a label already queued does not grow the lane, and does not
      -- accept a new message. A new label past the lane capacity is the overflow crash.
      if a.prio.any (fun p => p.label == label) then
        setActor w id (proceed a k')
      else if a.prio.length < cap then
        setActor w id (proceed { a with prio := upsertPrio a.prio msg, nextMid := a.nextMid + 1 } k')
      else
        setActor w id { a with phase := .crashed }
    | .cell dst label value =>
      let previous := w.cell dst label
      let written := max previous.value value
      let w := setCell w dst label { value := written, dirty := true }
      let w := setActor w id (proceed (w.st id) k')
      if previous.dirty then w
      else wakeReaders I.desc w dst label id
    | .internal => setActor w id { a with phase := .awaitEffect k' }
    | .peer => setActor w id { a with phase := .awaitPeer k' }
    | .terminate =>
      -- Terminable templates only. A parked call is not rewritten into a send:
      -- the step is refused when one is present (LocalOk makes that unreachable).
      match templateOf I.desc (tname id) with
      | some t =>
        if t.terminable && !hasParkedCall a.parked then
          -- Dropped mail is refunded so a dead id does not keep a send slot.
          -- Parked calls are refused above; graph/LocalOk also forbid them here.
          let w := readCells I.desc w id
          let w := refundMsgs w (tname id) a.box
          let w := refundParked w (tname id) a.parked
          let base := w.st id
          let dead : Actor :=
            { base with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
          releaseParked (setActor w id dead) id a.parked
        else w
      | none => w

def execHead (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive then none
  else
    match a.phase with
    | .run k => some (execRun I w id a k)
    | _ => none

/-- `true` when this actor's template declares its peer waits untimed. An untimed
peer may stay silent. A timed peer wait ends by timeout, which is the `finish`
step itself. -/
def peerUntimed (D : Description) (id : InstId) : Bool :=
  match templateOf D (tname id) with
  | some t => t.untimedPeer
  | none => false

/-- `finish` is enabled for this peer wait. A timed template always is. An
untimed template is when a timed peer in its cohort can end the chain. A pure
untimed wait (`templatePure`) is not: it is an external stall. -/
def peerFinishable (D : Description) (id : InstId) : Bool :=
  match templateOf D (tname id) with
  | none => true
  | some t => !t.untimedPeer || timedCohortEnds D (tname id)

/-- The actor is stopped on an untimed peer that no timed cohort peer can end. -/
def PurePeerEnd (D : Description) (w : World) (id : InstId) : Prop :=
  ∃ k, (w.st id).phase = .awaitPeer k ∧ peerFinishable D id = false

theorem peerFinishable_eq_not_pure (D : Description) (id : InstId) :
    peerFinishable D id = !templatePure D (tname id) := by
  cases ht : templateOf D (tname id) with
  | none => simp [peerFinishable, templatePure, ht]
  | some t => simp [peerFinishable, templatePure, ht]

theorem finishable_of_timed (D : Description) (id : InstId) (hu : peerUntimed D id = false) :
    peerFinishable D id = true := by
  cases ht : templateOf D (tname id) with
  | none => simp [peerFinishable, ht]
  | some t =>
    simp [peerUntimed, peerFinishable, ht] at hu ⊢
    simp [hu]

theorem untimed_of_silent (D : Description) (id : InstId) (hf : peerFinishable D id = false) :
    peerUntimed D id = true := by
  cases ht : templateOf D (tname id) with
  | none => simp [peerFinishable, ht] at hf
  | some t =>
    simp [peerUntimed, peerFinishable, ht] at hf ⊢
    cases hb : t.untimedPeer <;> simp_all

theorem pure_of_silent (D : Description) (id : InstId) (hf : peerFinishable D id = false) :
    templatePure D (tname id) = true := by
  have h := peerFinishable_eq_not_pure D id
  cases hp : templatePure D (tname id) with
  | true => rfl
  | false => simp [hp, hf] at h

/-- Internal effects complete as an ordinary step. A finishable peer wait
completes the same way: its own timeout, or a timed peer in the cohort. A pure
untimed peer wait does not. -/
def finishWait (I : Impl) (w : World) (id : InstId) : Option World :=
  match (w.st id).phase with
  | .awaitEffect k => some (setActor w id (proceed (w.st id) k))
  | .awaitPeer k =>
    if !peerFinishable I.desc id then none else some (setActor w id (proceed (w.st id) k))
  | _ => none

/-- A declared ingress edge: a non-blocking `trySend` the environment may deliver. -/
def hasIngress (D : Description) (dst label : String) : Bool :=
  D.edges.any fun e =>
    e.ingress && e.dst == dst && e.label == label && e.effect == .trySend

/-- Effects still to run from the current phase. -/
def contRest : Phase → List Eff
  | .run k => k.rest
  | .parked _ _ k => k.rest
  | .awaitReply _ k => k.rest
  | .awaitEffect k => k.rest
  | .awaitPeer k => k.rest
  | _ => []

def sendsTo (dst : String) : List Eff → Nat
  | [] => 0
  | .send d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | .trySend d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | .call d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | _ :: es => sendsTo dst es

/-- Bulk sends still in the continuation, counted toward the token floor. -/
def pending (a : Actor) (dst : String) : Nat := sendsTo dst (contRest a.phase)

/-- Idle, parked, or waiting. A running or crashed actor does not take ingress. -/
def ingressOpen : Phase → Bool
  | .idle => true
  | .parked _ _ _ => true
  | .awaitReply _ _ => true
  | .awaitEffect _ => true
  | .awaitPeer _ => true
  | .run _ => false
  | .crashed => false

/-- How many self-tokens an ingress may consume, from `ingressLegal` at this `N`. -/
def ingressAllowance (D : Description) (N : Nat) (dst label : String) : Nat :=
  match D.edges.find? fun e => e.ingress && e.dst == dst && e.label == label with
  | some e => match e.ingressLegal with
    | some a => a.eval N
    | none => 0
  | none => 0

/-- `true` when the named template is declared terminable. -/
def terminableB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.terminable
  | none => false

/-- Environment delivery into a live ingress stage. The actor may be idle, parked,
or waiting; a running or crashed actor is refused. It charges one self-slot and
appends a bulk message when the mailbox is under capacity and the target still
has a token above the typestate floor plus the sends still in its continuation.
A full mailbox, a dead target, a terminable target, or a spent budget makes the
action disabled, so the message is never dropped. The allowance is `ingressLegal`
evaluated at `w.N`. -/
def receiveIngress (I : Impl) (w : World) (dst : InstId) (label : String) : Option World :=
  let a := w.st dst
  let cap := capBulk I.desc w.N dst
  let floor := budget I.desc (tname dst) (tname dst) - debt I.desc (tname dst) a.typestate (tname dst)
  let need := floor + pending a (tname dst) + 1
  if a.life ≠ .alive || ingressOpen a.phase = false then none
  else if hasIngress I.desc (tname dst) label = false then none
  else if cap ≤ a.box.length then none
  else if terminableB I.desc (tname dst) then none
  else if a.tokens (tname dst) < need ||
      a.tokens (tname dst) < Nat.max (ingressAllowance I.desc w.N (tname dst) label) 1 then none
  else
    let msg : Msg :=
      { label := label, sender := dst, callFrom := none, reliable := true, mid := a.nextMid }
    let charged := chargeSender a (tname dst)
    some (setActor w dst { charged with box := a.box ++ [msg], nextMid := a.nextMid + 1 })

theorem ingress_phase (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (w'.st i).phase = (w.st i).phase ∧ (w'.st i).life = (w.st i).life ∧
      (w'.st i).prio = (w.st i).prio ∧ w'.cell = w.cell ∧ w'.roster = w.roster ∧
      w'.N = w.N ∧ w'.nextIx = w.nextIx ∧ w'.observed = w.observed := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · cases h
            refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
            all_goals
              by_cases hi : i = dst
              · simp [setActor, hi, chargeSender, bumpToken]
              · simp [setActor, hi]

/-- A successful `finish` is the continuation after an effect or peer wait. -/
theorem finish_proceed (I : Impl) (w w' : World) (id : InstId)
    (h : finishWait I w id = some w') :
    ∃ k, ((w.st id).phase = .awaitEffect k ∨ (w.st id).phase = .awaitPeer k) ∧
      w' = setActor w id (proceed (w.st id) k) := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    exact ⟨k, Or.inl rfl, rfl⟩
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    cases hw
    exact ⟨k, Or.inr rfl, rfl⟩
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

/-- Ingress appends one non-call to the target box and leaves every other box. -/
theorem ingress_box (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (i = dst ∧ (w'.st i).box = (w.st i).box ++
      [{ label := label, sender := dst, callFrom := none, reliable := true, mid := (w.st dst).nextMid }]) ∨
      (i ≠ dst ∧ (w'.st i).box = (w.st i).box) := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · cases h
            by_cases hi : i = dst
            · exact Or.inl ⟨hi, by simp [setActor, hi, chargeSender, bumpToken]⟩
            · exact Or.inr ⟨hi, by simp [setActor, hi]⟩

/-- Ingress does not change typestate. -/
theorem ingress_ty_eq (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (w'.st i).typestate = (w.st i).typestate := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · cases h
            by_cases hi : i = dst
            · simp [setActor, hi, chargeSender, bumpToken]
            · simp [setActor, hi]

/-- A successful ingress is the charged, appended world, and the guards that
make the charge safe have already held. The actor may be parked or waiting;
the token floor includes the sends still in that continuation. -/
theorem ingress_open (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    (w.st dst).life = .alive ∧ ingressOpen (w.st dst).phase = true ∧
      terminableB I.desc (tname dst) = false ∧
      budget I.desc (tname dst) (tname dst) -
        debt I.desc (tname dst) (w.st dst).typestate (tname dst) +
        pending (w.st dst) (tname dst) + 1 ≤ (w.st dst).tokens (tname dst) ∧
      w' = setActor w dst { chargeSender (w.st dst) (tname dst) with
        box := (w.st dst).box ++
          [{ label := label, sender := dst, callFrom := none, reliable := true, mid := (w.st dst).nextMid }],
        nextMid := (w.st dst).nextMid + 1 } := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · next hguard =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · next hterm =>
          split at h
          · simp at h
          · next htok =>
            cases h
            have hnot : ¬((w.st dst).life ≠ .alive ∨ ingressOpen (w.st dst).phase = false) := by
              simpa using hguard
            refine ⟨?_, ?_, ?_, ?_, rfl⟩
            · by_cases hl : (w.st dst).life = .alive
              · exact hl
              · exact False.elim (hnot (Or.inl hl))
            · by_cases hp : ingressOpen (w.st dst).phase = true
              · exact hp
              · have hf : ingressOpen (w.st dst).phase = false := by
                  cases hop : ingressOpen (w.st dst).phase <;> simp_all
                exact False.elim (hnot (Or.inr hf))
            · cases hb : terminableB I.desc (tname dst) with
              | true => simp [hb] at hterm
              | false => rfl
            · have hlt : ¬((w.st dst).tokens (tname dst) <
                  budget I.desc (tname dst) (tname dst) -
                    debt I.desc (tname dst) (w.st dst).typestate (tname dst) +
                    pending (w.st dst) (tname dst) + 1) := by
                intro hbad
                have hdec : decide ((w.st dst).tokens (tname dst) <
                    budget I.desc (tname dst) (tname dst) -
                      debt I.desc (tname dst) (w.st dst).typestate (tname dst) +
                      pending (w.st dst) (tname dst) + 1) = true :=
                  decide_eq_true_iff.mpr hbad
                simp [hdec] at htok
              simpa [Nat.not_lt] using hlt

/-- A delivered ingress names a live actor that is idle, parked, or waiting. -/
theorem ingress_ready (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    (w.st dst).life = .alive ∧ ingressOpen (w.st dst).phase = true := by
  obtain ⟨hl, hop, _, _, _⟩ := ingress_open I w w' dst label h
  exact ⟨hl, hop⟩

def spawn (I : Impl) (w : World) (template : String) : Option World :=
  match templateOf I.desc template with
  | none => none
  | some t =>
    if t.multiplicity == .perPeer && aliveCount w template < w.N then
      let id := InstId.peer template (w.nextIx template)
      let a := withTokens I.desc template
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 }
      let w := { w with roster := w.roster ++ [id], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n }
      let w := setActor w id a
      some (readCells I.desc w id)
    else none

inductive Action where
  | recvBulk (s : InstId)
  | recvPrio (s : InstId)
  | exec (s : InstId)
  | finish (s : InstId)
  | spawn (template : String)
  | ingress (dst : InstId) (label : String)
  /-- Scheduler idle. Enabled only when no roster actor can `recv`, `exec`, or `finish`.
  Ingress may still be enabled; taking it is the environment's choice. -/
  | stutter
  deriving DecidableEq, Repr

/-- A roster actor has a step the runtime is obliged to consider. -/
def runtimeBusy (I : Impl) (w : World) : Bool :=
  w.roster.any fun id =>
    (receiveBulk I w id).isSome || (receivePrio I w id).isSome ||
    (execHead I w id).isSome || (finishWait I w id).isSome

def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait I w s
  | .spawn template => spawn I w template
  | .ingress dst label => receiveIngress I w dst label
  | .stutter => if runtimeBusy I w then none else some w

theorem stutter_unchanged (I : Impl) (w w' : World) (h : apply I .stutter w = some w') : w' = w := by
  simp [apply, runtimeBusy] at h
  exact h.2.symm

def Enabled (I : Impl) (w : World) (a : Action) : Prop := apply I a w ≠ none

/-- Spawn and ingress are not scheduled by the runtime. A fair run does not
have to keep injecting when an ingress stays enabled. -/
def forced : Action → Bool
  | .spawn _ => false
  | .ingress _ _ => false
  | .stutter => false
  | _ => true

def coreRoster (D : Description) : List InstId :=
  D.templates.filterMap fun t => if t.multiplicity == .one then some (.core t.name) else none

def initActor (D : Description) (id : InstId) : Actor :=
  match templateOf D (tname id) with
  | some t => withTokens D (tname id)
      { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
        tokens := fun _ => 0 }
  | none => absentActor

def initWorld (I : Impl) (N : Nat) : World :=
  let roster := coreRoster I.desc
  let base : World :=
    { N := N, roster := roster, nextIx := fun _ => 0,
      st := fun id => if roster.contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }
  roster.foldl (fun w id => readCells I.desc w id) base

inductive Reachable (I : Impl) (N : Nat) : World → Prop where
  | init : Reachable I N (initWorld I N)
  | step (w w' : World) (a : Action) : Reachable I N w → apply I a w = some w' → Reachable I N w'

structure Run (I : Impl) (N : Nat) where
  cfg : Nat → World
  act : Nat → Action
  startN : (cfg 0).N = N
  start : cfg 0 = initWorld I N
  valid : ∀ i, apply I (act i) (cfg i) = some (cfg (i + 1))

def alive (w : World) (id : InstId) : Prop := (w.st id).life = .alive

def Idle (w : World) (id : InstId) : Prop := alive w id ∧ (w.st id).phase = .idle

def CanReceive (w : World) (id : InstId) : Prop :=
  Idle w id ∧ ((w.st id).box ≠ [] ∨ (w.st id).parked ≠ [])

structure Fair {I : Impl} {N : Nat} (ρ : Run I N) : Prop where
  weak : ∀ (a : Action) (i : Nat), forced a = true →
    (∀ j, i ≤ j → Enabled I (ρ.cfg j) a) → ∃ j, i ≤ j ∧ ρ.act j = a
  /-- Strong fairness of bulk receive, stated on `Enabled`. `CanReceive` is not
  enough: a call at the head can make the mailbox look ready while `deliver`
  refuses it. `uniqueKeys` plus `callTotal` are what turn readiness into
  `Enabled`. -/
  bulk : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk s)) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)
  /-- The runtime drains a priority lane that is enabled infinitely often.
  `recvBulk` stays enabled beside `recvPrio`; this is the policy that the
  priority wake is not left behind a bulk mailbox. -/
  prio : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ Enabled I (ρ.cfg j) (.recvPrio s)) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvPrio s)

inductive WaitKind where
  | blockingSend (dst : InstId)
  | callReply (dst : InstId)
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

def SameWait (a b : Actor) : Prop := waitKind a = waitKind b ∧ waitKind a ≠ none

def Stuck {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i : Nat) : Prop :=
  SameWait ((ρ.cfg i).st s) ((ρ.cfg i).st s) ∧
    ∀ j, i ≤ j → SameWait ((ρ.cfg i).st s) ((ρ.cfg j).st s)

/-- A run is deadlocked when some actor is stuck on a blocking send, a call
reply, an internal effect, or a timed peer wait. An untimed peer wait is not
a deadlock. `finish` is still enabled on it when a timed peer in the cohort
can end the chain (`peerFinishable`). A pure untimed wait leaves `finish`
disabled, and the actor may stay there. -/
def Deadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ s i, Stuck ρ s i ∧
    match waitKind ((ρ.cfg i).st s) with
    | some (.blockingSend _) => True
    | some (.callReply _) => True
    | some .effect => True
    | some .peer => peerUntimed I.desc s = false
    | _ => False

/-- Program length, used as the measure that makes a busy actor reach idle. -/
def phaseFuel : Phase → Nat
  | .idle | .crashed => 0
  | .run k => 2 * k.rest.length
  | .parked _ _ k => 2 * k.rest.length + 1
  | .awaitReply _ k => 2 * k.rest.length + 1
  | .awaitEffect k => 2 * k.rest.length + 1
  | .awaitPeer k => 2 * k.rest.length + 1

def replyCount : List Eff → Nat
  | [] => 0
  | .reply :: es => replyCount es + 1
  | _ :: es => replyCount es

def terminateBeforeReply : List Eff → Bool
  | [] => false
  | .terminate :: _ => true
  | .reply :: _ => false
  | _ :: es => terminateBeforeReply es

end Deadlock
