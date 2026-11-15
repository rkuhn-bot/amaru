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

structure Impl where
  desc : Description
  transitions : List Transition

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
    let entry : Parked := { sender := sender, msg := msg, isCall := isCall }
    if room then
      if same then
        let self : Actor := { senderA with box := senderA.box ++ [msg] }
        if isCall then setActor w sender { self with phase := .awaitReply dst k }
        else setActor w sender (proceed self k)
      else
        let stored : Actor := { target with box := target.box ++ [msg] }
        let w := setActor w dst stored
        if isCall then setActor w sender { senderA with phase := .awaitReply dst k }
        else setActor w sender (proceed senderA k)
    else if same then
      let self : Actor := { senderA with parked := senderA.parked ++ [entry] }
      setActor w sender { self with phase := .parked dst isCall k }
    else
      let stored : Actor := { target with parked := target.parked ++ [entry] }
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
  let wake : Msg := { label := label, sender := writer, callFrom := none }
  if target.life == .alive && target.prio.length < cap && !(target.prio.any (fun p => p.label == label)) then
    setActor w dstId { target with prio := upsertPrio target.prio wake }
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
          let msg : Msg := { label := label, sender := id, callFrom := none }
          let a' := chargeSender a (tname dstId)
          let w := setActor w id a'
          setActor w dstId { (w.st dstId) with box := (w.st dstId).box ++ [msg] }
            |> fun w => setActor w id (proceed (w.st id) k')
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
      let msg : Msg := { label := label, sender := id, callFrom := none }
      -- Re-arming a label already queued does not grow the lane. A new label
      -- past the lane capacity is the overflow crash.
      if a.prio.any (fun p => p.label == label) then
        setActor w id (proceed a k')
      else if a.prio.length < cap then
        setActor w id (proceed { a with prio := upsertPrio a.prio msg } k')
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

def finishWait (w : World) (id : InstId) : Option World :=
  match (w.st id).phase with
  | .awaitEffect k => some (setActor w id (proceed (w.st id) k))
  | .awaitPeer k => some (setActor w id (proceed (w.st id) k))
  | _ => none

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
  deriving DecidableEq, Repr

def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait w s
  | .spawn template => spawn I w template

def Enabled (I : Impl) (w : World) (a : Action) : Prop := apply I a w ≠ none

def forced : Action → Bool
  | .spawn _ => false
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
  bulk : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ CanReceive (ρ.cfg j) s) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)

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

def SameWait (a b : Actor) : Prop := waitKind a = waitKind b ∧ waitKind a ≠ none

def Stuck {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i : Nat) : Prop :=
  SameWait ((ρ.cfg i).st s) ((ρ.cfg i).st s) ∧
    ∀ j, i ≤ j → SameWait ((ρ.cfg i).st s) ((ρ.cfg j).st s)

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
    | .spawn _ => False

def GlobalDeadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ i, (∃ s, alive (ρ.cfg i) s) ∧ ∀ s, alive (ρ.cfg i) s → Stuck ρ s i

def CallerMailboxFull (D : Description) (w : World) (s : InstId) : Prop :=
  match (w.st s).phase with
  | .awaitReply _ _ => (w.st s).box.length = capBulk D w.N s
  | _ => False

theorem waitKind_ne_cell (a : Actor) : waitKind a ≠ some .cell := by
  intro hEq
  cases h : a.phase with
  | idle => simp [waitKind, h] at hEq
  | run _ => simp [waitKind, h] at hEq
  | parked _ isCall _ => cases isCall <;> simp [waitKind, h] at hEq
  | awaitReply _ _ => simp [waitKind, h] at hEq
  | awaitEffect _ => simp [waitKind, h] at hEq
  | awaitPeer _ => simp [waitKind, h] at hEq
  | crashed => simp [waitKind, h] at hEq

def WaitingOnCell (a : Actor) : Prop := waitKind a = some .cell

/-- Program length, used as the measure that makes a busy actor reach idle. -/
def phaseFuel : Phase → Nat
  | .idle | .crashed => 0
  | .run k => 2 * k.rest.length
  | .parked _ _ k => 2 * k.rest.length + 1
  | .awaitReply _ k => 2 * k.rest.length + 1
  | .awaitEffect k => 2 * k.rest.length + 1
  | .awaitPeer k => 2 * k.rest.length + 1

def sendsTo (dst : String) : List Eff → Nat
  | [] => 0
  | .send d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | .trySend d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | .call d _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | _ :: es => sendsTo dst es

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
