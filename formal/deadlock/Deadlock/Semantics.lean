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

/-- The per-peer index is the subtree key. A core has none. -/
def memberKey : InstId → Option Nat
  | .core _ => none
  | .peer _ k => some k

/-- `id` is a live-or-dead role of subtree `sub` at `key`. -/
def isMember (D : Description) (id : InstId) (sub : String) (key : Nat) : Bool :=
  match id with
  | .core _ => false
  | .peer role k => k == key && sub != "" && templateSubtree D role == sub

def timeoutKillsB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.timeoutKills
  | none => false

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
  /-- A route that named a per-peer role and did not resolve. Explicit, not a drop. -/
  failures : List (InstId × String) := []
  /-- The key of the last subtree kill, once the supervisor has been handed the tombstone. -/
  tombstone : Option Nat := none

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

/-- A live target only. A per-peer role is addressed by the sender's subtree key,
not by a literal hint. A dead or never-spawned key does not resolve. -/
def route (w : World) (D : Description) (sender : InstId) (dst : String) : Option InstId :=
  match templateOf D dst with
  | none => none
  | some t =>
    match t.multiplicity with
    | .one =>
      let id := InstId.core dst
      if (w.st id).life == .alive then some id else none
    | .perPeer =>
      match memberKey sender with
      | none => none
      | some k =>
        let id := InstId.peer dst k
        if (w.st id).life == .alive then some id else none

/-- Record a route that did not resolve. The sender then leaves the effect. -/
def noteStale (w : World) (sender : InstId) (dst : String) : World :=
  { w with failures := w.failures ++ [(sender, dst)] }

@[simp] theorem noteStale_st (w : World) (sender : InstId) (dst : String) (i : InstId) :
    (noteStale w sender dst).st i = w.st i := rfl

@[simp] theorem noteStale_roster (w : World) (sender : InstId) (dst : String) :
    (noteStale w sender dst).roster = w.roster := rfl

@[simp] theorem noteStale_cell (w : World) (sender : InstId) (dst : String) :
    (noteStale w sender dst).cell = w.cell := rfl

@[simp] theorem noteStale_nextIx (w : World) (sender : InstId) (dst : String) :
    (noteStale w sender dst).nextIx = w.nextIx := rfl

@[simp] theorem noteStale_observed (w : World) (sender : InstId) (dst : String) :
    (noteStale w sender dst).observed = w.observed := rfl

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
      match route w I.desc id dst with
      | none => setActor (noteStale w id dst) id (proceed a k')
      | some dstId =>
        let msg : Msg := { label := label, sender := id, callFrom := none }
        enqueueOrPark w I.desc id dstId msg false k'
    | .trySend dst label hint =>
      match route w I.desc id dst with
      | none => setActor (noteStale w id dst) id (proceed a k')
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
      match route w I.desc id dst with
      | none =>
        -- No live target: the call is failed explicitly, not turned into a wait on a dummy name.
        setActor (noteStale w id dst) id (proceed a k')
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
untimed template is when a timed peer in its subtree can kill that subtree.
A pure untimed wait (`templatePure`) is not: nothing kills it, so it is an
external stall. -/
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

/-- Drop parked entries whose sender is `dead`. -/
def forgetSender (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w id =>
    let a := w.st id
    let ps := a.parked.filter fun p => p.sender != dead
    if ps == a.parked then w else setActor w id { a with parked := ps }) w

/-- A live actor waiting on `dead` is failed: a call returns to idle, a blocking
send runs its continuation. -/
def failWaiter (w : World) (dead : InstId) (i : InstId) : World :=
  if (w.st i).life != .alive then w
  else
    match (w.st i).phase with
    | .parked d _ k =>
      if d == dead then setActor w i (proceed (w.st i) k) else w
    | .awaitReply d _ =>
      if d == dead then setActor w i { (w.st i) with phase := .idle } else w
    | _ => w

def failWaiters (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w i => failWaiter w dead i) w

/-- Kill one member: refund what its mailbox held, fail whoever was waiting on
it, cancel its own outbound parks, and leave it dead with an empty mailbox. -/
def killOne (w : World) (D : Description) (id : InstId) : World :=
  let a0 := w.st id
  let w := readCells D w id
  let w := refundMsgs w (tname id) a0.box
  let w := refundParked w (tname id) a0.parked
  let w := failWaiters w id
  let w := forgetSender w id
  let cur := w.st id
  setActor w id { cur with life := .dead, phase := .idle, box := [], prio := [], parked := [] }

def killMembers (w : World) (D : Description) (sub : String) (key : Nat) : World :=
  w.roster.foldl (fun w id =>
    if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w

/-- The supervisor named by any role of `sub`, if one is set. -/
def subtreeSupervisor (D : Description) (sub : String) : String :=
  (D.templates.findSome? fun t =>
    if t.subtree == sub && t.supervisor != "" then some t.supervisor else none).getD ""

/-- The supervisor's receipt for a subtree kill. It is the world field, not a bulk
message: a bulk message would spend a credit the supervisor may not hold, and a
credit that is not there cannot be a guaranteed delivery. A later respawn uses
a fresh key, so this receipt does not name the new subtree. `subtreeSupervisor`
is the role the receipt is for; an empty name still records the key. -/
def plantTombstone (w : World) (D : Description) (sub : String) (key : Nat) : World :=
  let _receiver := subtreeSupervisor D sub
  { w with tombstone := some key }

@[simp] theorem plant_st (w : World) (D : Description) (sub : String) (key : Nat) (i : InstId) :
    (plantTombstone w D sub key).st i = w.st i := rfl

@[simp] theorem plant_roster (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).roster = w.roster := rfl

@[simp] theorem plant_nextIx (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).nextIx = w.nextIx := rfl

@[simp] theorem plant_N (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).N = w.N := rfl

@[simp] theorem plant_cell (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).cell = w.cell := rfl

@[simp] theorem plant_observed (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).observed = w.observed := rfl

@[simp] theorem plant_failures (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).failures = w.failures := rfl

@[simp] theorem plant_tomb (w : World) (D : Description) (sub : String) (key : Nat) :
    (plantTombstone w D sub key).tombstone = some key := rfl

/-- Kill every live member of subtree `sub` at `key`, then hand the supervisor one tombstone. -/
def killSubtree (w : World) (D : Description) (sub : String) (key : Nat) : World :=
  plantTombstone (killMembers w D sub key) D sub key

/-- A timeout is armed when some live `timeoutKills` member of this key is in `awaitPeer`. -/
def killWait (w : World) (D : Description) (sub : String) (key : Nat) : Bool :=
  w.roster.any fun id =>
    isMember D id sub key && (w.st id).life == .alive && timeoutKillsB D (tname id) &&
      match (w.st id).phase with
      | .awaitPeer _ => true
      | _ => false

inductive Action where
  | recvBulk (s : InstId)
  | recvPrio (s : InstId)
  | exec (s : InstId)
  | finish (s : InstId)
  | spawn (template : String)
  | ingress (dst : InstId) (label : String)
  /-- Kill every live member of subtree `sub` at `key`. One step. -/
  | kill (sub : String) (key : Nat)
  /-- Scheduler idle. Enabled only when no roster actor can `recv`, `exec`, `finish`, or `kill`.
  Ingress may still be enabled; taking it is the environment's choice. -/
  | stutter
  deriving DecidableEq, Repr

/-- A subtree timeout is armed. The runtime must take the kill. -/
def killBusy (I : Impl) (w : World) : Bool :=
  w.roster.any fun id =>
    (w.st id).life == .alive && timeoutKillsB I.desc (tname id) &&
      match (w.st id).phase with
      | .awaitPeer _ => true
      | _ => false

/-- A roster actor has a step the runtime is obliged to consider. -/
def runtimeBusy (I : Impl) (w : World) : Bool :=
  w.roster.any (fun id =>
    (receiveBulk I w id).isSome || (receivePrio I w id).isSome ||
    (execHead I w id).isSome || (finishWait I w id).isSome) || killBusy I w

def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait I w s
  | .spawn template => spawn I w template
  | .ingress dst label => receiveIngress I w dst label
  | .kill sub key =>
    if killWait w I.desc sub key then some (killSubtree w I.desc sub key) else none
  | .stutter => if runtimeBusy I w then none else some w

/-- Data branch of `awaitPeer`: the segment arrived and the continuation runs.
This is `finish` when the wait is finishable. -/
def peerData (I : Impl) (w : World) (id : InstId) : Option World :=
  match (w.st id).phase with
  | .awaitPeer k =>
    if peerFinishable I.desc id then some (setActor w id (proceed (w.st id) k)) else none
  | _ => none

/-- Timeout branch of `awaitPeer`. A `timeoutKills` member kills the whole subtree. -/
def peerTimeout (I : Impl) (w : World) (id : InstId) : Option World :=
  match (w.st id).phase with
  | .awaitPeer _ =>
    match memberKey id with
    | some k =>
      let sub := templateSubtree I.desc (tname id)
      if timeoutKillsB I.desc (tname id) && killWait w I.desc sub k then
        some (killSubtree w I.desc sub k)
      else none
    | none => none
  | _ => none

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

theorem killWait_imp_busy (I : Impl) (w : World) (sub : String) (key : Nat)
    (h : killWait w I.desc sub key = true) : killBusy I w = true := by
  simp only [killWait, killBusy, List.any_eq_true] at h ⊢
  obtain ⟨id, hid, hmem⟩ := h
  refine ⟨id, hid, ?_⟩
  have h1 := (Bool.and_eq_true _ _).mp hmem
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  simp only [Bool.and_eq_true]
  exact ⟨⟨h3.2, h2.2⟩, h1.2⟩

theorem failWaiter_roster (w : World) (dead i : InstId) : (failWaiter w dead i).roster = w.roster := by
  unfold failWaiter
  split
  · rfl
  · cases hph : (w.st i).phase <;> simp [hph, setActor] <;> split <;> simp [setActor]

theorem failWaiter_nextIx (w : World) (dead i : InstId) : (failWaiter w dead i).nextIx = w.nextIx := by
  unfold failWaiter
  split
  · rfl
  · cases hph : (w.st i).phase <;> simp [hph, setActor] <;> split <;> simp [setActor]

theorem failWaiter_N (w : World) (dead i : InstId) : (failWaiter w dead i).N = w.N := by
  unfold failWaiter
  split
  · rfl
  · cases hph : (w.st i).phase <;> simp [hph, setActor] <;> split <;> simp [setActor]

theorem failWaiter_other (w : World) (dead i j : InstId) (h : j ≠ i) :
    (failWaiter w dead i).st j = w.st j := by
  unfold failWaiter
  split
  · rfl
  · cases hph : (w.st i).phase <;> simp [hph, setActor, h] <;> split <;> simp [setActor, h]

theorem failWaiter_life (w : World) (dead i j : InstId) :
    ((failWaiter w dead i).st j).life = (w.st j).life := by
  by_cases hj : j = i
  · rw [hj]
    unfold failWaiter
    split
    · rfl
    · cases hph : (w.st i).phase with
      | parked _ _ k =>
        simp [hph]
        split
        · cases hk : k.rest <;> simp [setActor, proceed, hk]
        · rfl
      | awaitReply _ _ =>
        simp [hph]
        split <;> simp [setActor]
      | idle => simp [hph]
      | run _ => simp [hph]
      | awaitEffect _ => simp [hph]
      | awaitPeer _ => simp [hph]
      | crashed => simp [hph]
  · rw [failWaiter_other w dead i j hj]

theorem failWaiters_roster (w : World) (dead : InstId) (ids : List InstId) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).roster) = w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih, failWaiter_roster]

theorem failWaiters_nextIx (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w i => failWaiter w dead i) w).nextIx = w.nextIx := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih, failWaiter_nextIx]

theorem failWaiters_N (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w i => failWaiter w dead i) w).N = w.N := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih, failWaiter_N]

theorem credit_roster (w : World) (dst : String) (s : InstId) :
    (creditSender w dst s).roster = w.roster := rfl

theorem credit_nextIx (w : World) (dst : String) (s : InstId) :
    (creditSender w dst s).nextIx = w.nextIx := rfl

theorem credit_N (w : World) (dst : String) (s : InstId) : (creditSender w dst s).N = w.N := rfl

theorem refundMsgs_roster (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).roster = w.roster := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_roster]

theorem refundMsgs_nextIx (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).nextIx = w.nextIx := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_nextIx]

theorem refundMsgs_N (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).N = w.N := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_N]

theorem refundParked_roster (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).roster = w.roster := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_roster]

theorem refundParked_nextIx (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).nextIx = w.nextIx := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_nextIx]

theorem refundParked_N (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).N = w.N := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_N]

theorem cellsN (D : Description) (w : World) (id : InstId) : (readCells D w id).N = w.N := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem cellsRoster (D : Description) (w : World) (id : InstId) : (readCells D w id).roster = w.roster := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem readCells_nextIx (D : Description) (w : World) (id : InstId) (name : String) :
    (readCells D w id).nextIx name = w.nextIx name := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem forgetFold_roster (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · exact ih w
    · rw [← show (setActor w id
        { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }).roster = w.roster from rfl]
      exact ih _

theorem forget_roster (w : World) (dead : InstId) : (forgetSender w dead).roster = w.roster := by
  simpa [forgetSender] using forgetFold_roster w dead w.roster

theorem forgetFold_nextIx (w : World) (dead : InstId) (ids : List InstId) (name : String) :
    (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w).nextIx name =
      w.nextIx name := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · exact ih w
    · rw [← show (setActor w id
        { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }).nextIx name =
        w.nextIx name from rfl]
      exact ih _

theorem forget_nextIx (w : World) (dead : InstId) (name : String) :
    (forgetSender w dead).nextIx name = w.nextIx name := by
  simpa [forgetSender] using forgetFold_nextIx w dead w.roster name

theorem forgetFold_N (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w).N = w.N := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · exact ih w
    · rw [← show (setActor w id
        { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }).N = w.N from rfl]
      exact ih _

theorem forget_N (w : World) (dead : InstId) : (forgetSender w dead).N = w.N := by
  simpa [forgetSender] using forgetFold_N w dead w.roster

theorem killOne_roster (w : World) (D : Description) (id : InstId) :
    (killOne w D id).roster = w.roster := by
  unfold killOne
  dsimp only [setActor]
  rw [forget_roster]
  simp only [failWaiters]
  rw [failWaiters_roster, refundParked_roster, refundMsgs_roster, cellsRoster]

theorem killOne_nextIx (w : World) (D : Description) (id : InstId) (name : String) :
    (killOne w D id).nextIx name = w.nextIx name := by
  unfold killOne
  dsimp only [setActor]
  rw [forget_nextIx]
  simp only [failWaiters]
  rw [failWaiters_nextIx, refundParked_nextIx, refundMsgs_nextIx, readCells_nextIx]

theorem killOne_N (w : World) (D : Description) (id : InstId) : (killOne w D id).N = w.N := by
  unfold killOne
  dsimp only [setActor]
  rw [forget_N]
  simp only [failWaiters]
  rw [failWaiters_N, refundParked_N, refundMsgs_N, cellsN]

theorem killFold_roster (w : World) (D : Description) (sub : String) (key : Nat) (ids : List InstId) :
    (ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).roster =
      w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · have hfold := ih (killOne w D id)
      simpa [killOne_roster] using hfold
    · exact ih w

theorem killMembers_roster (w : World) (D : Description) (sub : String) (key : Nat) :
    (killMembers w D sub key).roster = w.roster := by
  simpa [killMembers] using killFold_roster w D sub key w.roster

theorem killFold_nextIx (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (name : String) :
    (ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).nextIx name =
      w.nextIx name := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · have hfold := ih (killOne w D id)
      simpa [killOne_nextIx] using hfold
    · exact ih w

theorem killMembers_nextIx (w : World) (D : Description) (sub : String) (key : Nat) (name : String) :
    (killMembers w D sub key).nextIx name = w.nextIx name := by
  simpa [killMembers] using killFold_nextIx w D sub key w.roster name

theorem killFold_N (w : World) (D : Description) (sub : String) (key : Nat) (ids : List InstId) :
    (ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).N = w.N := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · have hfold := ih (killOne w D id)
      simpa [killOne_N] using hfold
    · exact ih w

theorem killMembers_N (w : World) (D : Description) (sub : String) (key : Nat) :
    (killMembers w D sub key).N = w.N := by
  simpa [killMembers] using killFold_N w D sub key w.roster

theorem killSubtree_roster (w : World) (D : Description) (sub : String) (key : Nat) :
    (killSubtree w D sub key).roster = w.roster := by
  simp [killSubtree, killMembers_roster]

theorem killSubtree_nextIx (w : World) (D : Description) (sub : String) (key : Nat) (name : String) :
    (killSubtree w D sub key).nextIx name = w.nextIx name := by
  simp [killSubtree, killMembers_nextIx]

theorem killSubtree_N (w : World) (D : Description) (sub : String) (key : Nat) :
    (killSubtree w D sub key).N = w.N := by
  simp [killSubtree, killMembers_N]

theorem kill_apply_world (I : Impl) (w w' : World) (sub : String) (key : Nat)
    (h : apply I (.kill sub key) w = some w') : w' = killSubtree w I.desc sub key := by
  simp only [apply] at h
  split at h
  · cases h
    rfl
  · simp at h

theorem cellsSt (D : Description) (w : World) (id i : InstId) : (readCells D w id).st i = w.st i := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldl_cons]
    let mid := setObserved
      (setCell w (tname id) l { (w.cell (tname id) l) with dirty := false }) id l (w.cell (tname id) l).value
    have hmid : mid.st i = w.st i := by simp [mid, setCell, setObserved]
    exact (ih mid).trans hmid

theorem credit_phase_life (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).phase = (w.st i).phase ∧
      ((creditSender w name sender).st i).life = (w.st i).life := by
  by_cases h : i = sender
  · subst h
    simp [creditSender, setActor, bumpToken]
  · simp [creditSender, setActor, h]

theorem refundMsgs_phase_life (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w name ms).st i).life = (w.st i).life := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    have hcred := credit_phase_life w name m.sender i
    have hih := ih (creditSender w name m.sender)
    exact ⟨hih.1.trans hcred.1, hih.2.trans hcred.2⟩

theorem refundParked_phase_life (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).phase = (w.st i).phase ∧
      ((refundParked w name ps).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    have hcred := credit_phase_life w name p.msg.sender i
    have hih := ih (creditSender w name p.msg.sender)
    exact ⟨hih.1.trans hcred.1, hih.2.trans hcred.2⟩

theorem failFold_off (w : World) (dead s : InstId) (ids : List InstId) (hs : s ∉ ids) :
    (ids.foldl (fun w i => failWaiter w dead i) w).st s = w.st s := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    have hne : s ≠ i := fun h => hs (by simpa [h] using List.Mem.head _)
    have hs' : s ∉ ids := fun h => hs (List.Mem.tail _ h)
    simp only [List.foldl_cons]
    rw [ih _ hs', failWaiter_other w dead i s hne]

theorem forgetFold_off (w : World) (dead s : InstId) (ids : List InstId) (hs : s ∉ ids) :
    (ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s = w.st s := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    have hne : s ≠ id := fun h => hs (by simpa [h] using List.Mem.head _)
    have hs' : s ∉ ids := fun h => hs (List.Mem.tail _ h)
    simp only [List.foldl_cons]
    split
    · exact ih _ hs'
    · have hih := ih (setActor w id
        { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }) hs'
      simpa [setActor, hne] using hih

theorem forget_off (w : World) (dead s : InstId) (hs : s ∉ w.roster) :
    (forgetSender w dead).st s = w.st s := by
  simpa [forgetSender] using forgetFold_off w dead s w.roster hs

/-- An off-roster id is not the member being removed, so a kill leaves its phase and life. -/
theorem killOne_off (w : World) (D : Description) (id s : InstId) (hs : s ∉ w.roster) (hne : s ≠ id) :
    ((killOne w D id).st s).phase = (w.st s).phase ∧ ((killOne w D id).st s).life = (w.st s).life := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  have hrs1 : w1.roster = w.roster := cellsRoster D w id
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have hst2 := refundMsgs_phase_life w1 (tname id) (w.st id).box s
  have hrs2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname id) (w.st id).box
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have hst3 := refundParked_phase_life w2 (tname id) (w.st id).parked s
  have hrs3 : w3.roster = w2.roster := refundParked_roster w2 (tname id) (w.st id).parked
  have hs3 : s ∉ w3.roster := by rw [hrs3, hrs2, hrs1]; exact hs
  let w4 := failWaiters w3 id
  have hst4 : w4.st s = w3.st s := by
    simpa [w4, failWaiters] using failFold_off w3 id s w3.roster hs3
  have hrs4 : w4.roster = w3.roster := by
    simpa [w4, failWaiters] using failWaiters_roster w3 id w3.roster
  let w5 := forgetSender w4 id
  have hst5 : w5.st s = w4.st s := forget_off w4 id s (by rw [hrs4]; exact hs3)
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5]
  rw [hbody, setActor_other _ _ _ _ hne, hst5, hst4]
  exact ⟨hst3.1.trans (hst2.1.trans (congrArg (·.phase) hst1)),
    hst3.2.trans (hst2.2.trans (congrArg (·.life) hst1))⟩

theorem killFold_off (w : World) (D : Description) (sub : String) (key : Nat) (ids : List InstId)
    (s : InstId) (hs : s ∉ w.roster) (hdead : (w.st s).life ≠ .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      (w.st s).phase ∧
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
      (w.st s).life := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D id sub key && ((w.st id).life == .alive)) = true
    · by_cases hsid : s = id
      · subst hsid
        have hlive : ((w.st s).life == .alive) = true := ((Bool.and_eq_true _ _).mp hcond).2
        exact absurd (by simpa [beq_iff_eq] using hlive) hdead
      · rw [if_pos hcond]
        have hpre := killOne_off w D id s hs hsid
        have hs' : s ∉ (killOne w D id).roster := by rw [killOne_roster]; exact hs
        have hdead' : ((killOne w D id).st s).life ≠ .alive := by rw [hpre.2]; exact hdead
        have hih := ih (killOne w D id) hs' hdead'
        exact ⟨hih.1.trans hpre.1, hih.2.trans hpre.2⟩
    · rw [if_neg hcond]
      exact ih w hs hdead

theorem killMembers_off (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hs : s ∉ w.roster) (hdead : (w.st s).life ≠ .alive) :
    ((killMembers w D sub key).st s).phase = (w.st s).phase ∧
      ((killMembers w D sub key).st s).life = (w.st s).life := by
  simpa [killMembers] using killFold_off w D sub key w.roster s hs hdead

theorem killSubtree_off (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hs : s ∉ w.roster) (hdead : (w.st s).life ≠ .alive) :
    ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
      ((killSubtree w D sub key).st s).life = (w.st s).life := by
  have hmem := killMembers_off w D sub key s hs hdead
  simp [killSubtree, plant_st, hmem.1, hmem.2]

/-- A phase a kill does not rewrite, except by killing the actor who is in it. -/
def holdsPhase (ph : Phase) : Bool :=
  match ph with
  | .parked _ _ _ => false
  | .awaitReply _ _ => false
  | _ => true

theorem bump_rest (a : Actor) (dst : String) (delta : Int) :
    (bumpToken a dst delta).phase = a.phase ∧ (bumpToken a dst delta).life = a.life ∧
      (bumpToken a dst delta).box = a.box ∧ (bumpToken a dst delta).prio = a.prio ∧
      (bumpToken a dst delta).parked = a.parked ∧
      (bumpToken a dst delta).typestate = a.typestate := by
  simp [bumpToken]

theorem credit_rest (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).phase = (w.st i).phase ∧
      ((creditSender w name sender).st i).life = (w.st i).life ∧
      ((creditSender w name sender).st i).box = (w.st i).box ∧
      ((creditSender w name sender).st i).prio = (w.st i).prio ∧
      ((creditSender w name sender).st i).parked = (w.st i).parked ∧
      ((creditSender w name sender).st i).typestate = (w.st i).typestate := by
  unfold creditSender
  by_cases h : i = sender
  · simp [setActor, h, bump_rest]
  · simp [setActor, h]

theorem refundMsgs_rest (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w name ms).st i).life = (w.st i).life ∧
      ((refundMsgs w name ms).st i).box = (w.st i).box ∧
      ((refundMsgs w name ms).st i).prio = (w.st i).prio ∧
      ((refundMsgs w name ms).st i).parked = (w.st i).parked ∧
      ((refundMsgs w name ms).st i).typestate = (w.st i).typestate := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    have h1 := credit_rest w name m.sender i
    have h2 := ih (creditSender w name m.sender)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
      h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem refundParked_rest (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).phase = (w.st i).phase ∧
      ((refundParked w name ps).st i).life = (w.st i).life ∧
      ((refundParked w name ps).st i).box = (w.st i).box ∧
      ((refundParked w name ps).st i).prio = (w.st i).prio ∧
      ((refundParked w name ps).st i).parked = (w.st i).parked ∧
      ((refundParked w name ps).st i).typestate = (w.st i).typestate := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    have h1 := credit_rest w name p.msg.sender i
    have h2 := ih (creditSender w name p.msg.sender)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
      h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem proceed_keeps_box (a : Actor) (k : Cont) : (proceed a k).box = a.box := by
  unfold proceed
  split <;> rfl

theorem proceed_keeps_prio (a : Actor) (k : Cont) : (proceed a k).prio = a.prio := by
  unfold proceed
  split <;> rfl

theorem proceed_keeps_parked (a : Actor) (k : Cont) : (proceed a k).parked = a.parked := by
  unfold proceed
  split <;> rfl

theorem failWaiter_mail (w : World) (dead i j : InstId) :
    ((failWaiter w dead i).st j).box = (w.st j).box ∧
      ((failWaiter w dead i).st j).prio = (w.st j).prio ∧
      ((failWaiter w dead i).st j).parked = (w.st j).parked := by
  unfold failWaiter
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases hph : (w.st i).phase with
    | parked d b k =>
      simp [hph]
      split
      · by_cases hj : j = i
        · simp [setActor, hj, proceed_keeps_box, proceed_keeps_prio, proceed_keeps_parked]
        · simp [setActor, hj]
      · exact ⟨rfl, rfl, rfl⟩
    | awaitReply d k =>
      simp [hph]
      split
      · by_cases hj : j = i <;> simp [setActor, hj]
      · exact ⟨rfl, rfl, rfl⟩
    | idle => simp [hph]
    | run _ => simp [hph]
    | awaitEffect _ => simp [hph]
    | awaitPeer _ => simp [hph]
    | crashed => simp [hph]

theorem failWaiter_holds (w : World) (dead i j : InstId) (hh : holdsPhase (w.st j).phase = true) :
    ((failWaiter w dead i).st j).phase = (w.st j).phase ∧
      ((failWaiter w dead i).st j).typestate = (w.st j).typestate := by
  by_cases hj : j = i
  · rw [hj] at hh ⊢
    unfold failWaiter
    split
    · exact ⟨rfl, rfl⟩
    · cases hph : (w.st i).phase with
      | parked _ _ _ => simp [holdsPhase, hph] at hh
      | awaitReply _ _ => simp [holdsPhase, hph] at hh
      | idle => simp [hph]
      | run _ => simp [hph]
      | awaitEffect _ => simp [hph]
      | awaitPeer _ => simp [hph]
      | crashed => simp [hph]
  · have h := failWaiter_other w dead i j hj
    exact ⟨congrArg (·.phase) h, congrArg (·.typestate) h⟩

theorem failFold_mail (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).box = (w.st s).box ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).prio = (w.st s).prio ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).parked = (w.st s).parked := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have h1 := failWaiter_mail w dead i s
    have h2 := ih (failWaiter w dead i)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem failFold_holds (w : World) (dead s : InstId) (ids : List InstId)
    (hh : holdsPhase (w.st s).phase = true) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = (w.st s).phase ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).typestate = (w.st s).typestate := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have h1 := failWaiter_holds w dead i s hh
    have hh' : holdsPhase ((failWaiter w dead i).st s).phase = true := by
      rw [h1.1, hh]
    have h2 := ih (failWaiter w dead i) hh'
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem forgetFold_mail (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).box =
      (w.st s).box ∧
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).prio =
      (w.st s).prio ∧
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).phase =
      (w.st s).phase ∧
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).life =
      (w.st s).life ∧
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).typestate =
      (w.st s).typestate := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _
    · have hset : ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).box = (w.st s).box ∧
        ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).prio = (w.st s).prio ∧
        ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).phase = (w.st s).phase ∧
        ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).life = (w.st s).life ∧
        ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).typestate =
          (w.st s).typestate := by
        by_cases hs : s = id
        · simp [setActor, hs]
        · simp [setActor, hs]
      have hih := ih (setActor w id { (w.st id) with
        parked := (w.st id).parked.filter fun p => p.sender != dead })
      exact ⟨hih.1.trans hset.1, hih.2.1.trans hset.2.1, hih.2.2.1.trans hset.2.2.1,
        hih.2.2.2.1.trans hset.2.2.2.1, hih.2.2.2.2.trans hset.2.2.2.2⟩

theorem filter_sublist {α : Type} (p : α → Bool) : ∀ xs : List α, (List.filter p xs).Sublist xs
  | [] => by simp
  | x :: xs => by
    simp only [List.filter]
    split
    · exact List.Sublist.cons_cons x (filter_sublist p xs)
    · exact List.Sublist.cons x (filter_sublist p xs)

theorem forgetFold_parked_sub (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).parked.Sublist
      (w.st s).parked := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · exact ih _
    · have hset : ((setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).parked.Sublist
          (w.st s).parked := by
        by_cases hs : s = id
        · simpa [setActor, hs] using filter_sublist (fun p => p.sender != dead) (w.st id).parked
        · simp [setActor, hs]
      exact List.Sublist.trans (ih _) hset

theorem filter_ne_sender (ps : List Parked) (dead : InstId)
    (h : ∀ p ∈ ps, p.sender ≠ dead) :
    ps.filter (fun p => p.sender != dead) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp : p.sender ≠ dead := h p (List.Mem.head _)
    have hb : (p.sender != dead) = true := by simpa [bne, beq_iff_eq] using hp
    simp [hb, ih (fun q hq => h q (List.Mem.tail _ hq))]

/-- Filtering out a sender who has nothing parked leaves that mailbox as it was. -/
theorem forgetFold_parked_keep (w : World) (dead s : InstId) (ids : List InstId)
    (h : ∀ p ∈ (w.st s).parked, p.sender ≠ dead) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).parked =
      (w.st s).parked := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    by_cases hkeep : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = true
    · simp only [hkeep, ite_true]
      exact ih w h
    · have hf : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = false := by
        cases hb : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) <;>
          simp_all
      simp only [hf, ite_false]
      by_cases hs : s = id
      · subst hs
        have htrue :
            ((w.st s).parked.filter (fun p => p.sender != dead) == (w.st s).parked) = true := by
          simpa [beq_iff_eq] using filter_ne_sender _ dead h
        simp [htrue] at hf
      · have hpark : ((setActor w id { (w.st id) with
            parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).parked =
            (w.st s).parked := by simp [setActor, hs]
        have hsend : ∀ p ∈ ((setActor w id { (w.st id) with
            parked := (w.st id).parked.filter fun p => p.sender != dead }).st s).parked,
            p.sender ≠ dead := by
          intro p hp
          exact h p (hpark ▸ hp)
        exact (ih _ hsend).trans hpark

/-- Forgetting one sender leaves a mailbox as it was, or as that mailbox with the sender removed. -/
theorem forgetFold_parked_fate (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).parked =
      (w.st s).parked ∨
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).parked =
      (w.st s).parked.filter fun p => p.sender != dead := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    by_cases hkeep : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = true
    · simp only [hkeep, ite_true]
      exact ih w
    · have hf : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = false := by
        cases hb : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) <;>
          simp_all
      simp only [hf]
      by_cases hs : s = id
      · subst hs
        let w' := setActor w s { (w.st s) with
          parked := (w.st s).parked.filter fun p => p.sender != dead }
        have hset : (w'.st s).parked =
            (w.st s).parked.filter fun p => p.sender != dead := by
          simp [w', setActor]
        have hih := ih w'
        rw [hset] at hih
        have hidem :
            ((w.st s).parked.filter fun p => p.sender != dead).filter (fun p => p.sender != dead) =
              (w.st s).parked.filter fun p => p.sender != dead := by
          have hfilt := List.filter_filter (p := fun p : Parked => p.sender != dead)
            (q := fun p : Parked => p.sender != dead) (l := (w.st s).parked)
          simpa [Bool.and_self] using hfilt
        rcases hih with hih | hih
        · exact Or.inr hih
        · exact Or.inr (hih.trans hidem)
      · let w' := setActor w id { (w.st id) with
          parked := (w.st id).parked.filter fun p => p.sender != dead }
        have hpark : (w'.st s).parked = (w.st s).parked := by simp [w', setActor, hs]
        have hih := ih w'
        rw [hpark] at hih
        exact hih

theorem killOne_parked_keep (w : World) (D : Description) (id i : InstId)
    (hne : i ≠ id) (h : ∀ p ∈ (w.st i).parked, p.sender ≠ id) :
    ((killOne w D id).st i).parked = (w.st i).parked := by
  let w1 := readCells D w id
  have hst1 : w1.st i = w.st i := cellsSt D w id i
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
  let w4 := failWaiters w3 id
  have h4 := failFold_mail w3 id i w3.roster
  let w5 := forgetSender w4 id
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have hpark : (w4.st i).parked = (w.st i).parked := by
    have h4p : (w4.st i).parked = (w3.st i).parked := by
      simpa [w4, failWaiters] using h4.2.2
    exact h4p.trans (h3.2.2.2.2.1.trans (h2.2.2.2.2.1.trans (congrArg (·.parked) hst1)))
  have hsend : ∀ p ∈ (w4.st i).parked, p.sender ≠ id := by
    intro p hp
    exact h p (hpark ▸ hp)
  exact (forgetFold_parked_keep w4 id i w4.roster hsend).trans hpark

/-- Killing someone else leaves this mailbox intact, or drops only that sender's parked entries. -/
theorem killOne_parked_fate (w : World) (D : Description) (id i : InstId) (hne : i ≠ id) :
    ((killOne w D id).st i).parked = (w.st i).parked ∨
      ((killOne w D id).st i).parked =
        (w.st i).parked.filter fun p => p.sender != id := by
  let w1 := readCells D w id
  have hst1 : w1.st i = w.st i := cellsSt D w id i
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
  let w4 := failWaiters w3 id
  have h4 := failFold_mail w3 id i w3.roster
  let w5 := forgetSender w4 id
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have hpark : (w4.st i).parked = (w.st i).parked := by
    have h4p : (w4.st i).parked = (w3.st i).parked := by
      simpa [w4, failWaiters] using h4.2.2
    exact h4p.trans (h3.2.2.2.2.1.trans (h2.2.2.2.2.1.trans (congrArg (·.parked) hst1)))
  have hfate := forgetFold_parked_fate w4 id i w4.roster
  simpa [w5, forgetSender, hpark] using hfate

/-- Killing `id` is the refund, the failure of whoever waited on it, and a dead idle actor. -/
theorem killOne_body (w : World) (D : Description) (id : InstId) :
    killOne w D id =
      let w1 := readCells D w id
      let w2 := refundMsgs w1 (tname id) (w.st id).box
      let w3 := refundParked w2 (tname id) (w.st id).parked
      let w4 := failWaiters w3 id
      let w5 := forgetSender w4 id
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := rfl

theorem killOne_self (w : World) (D : Description) (id : InstId) :
    ((killOne w D id).st id).life = .dead ∧ ((killOne w D id).st id).phase = .idle ∧
      ((killOne w D id).st id).box = [] ∧ ((killOne w D id).st id).prio = [] ∧
      ((killOne w D id).st id).parked = [] := by
  rw [killOne_body]
  simp [setActor]

theorem failFold_life (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).life = (w.st s).life := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact (ih (failWaiter w dead i)).trans (failWaiter_life w dead i s)

theorem killOne_other_rest (w : World) (D : Description) (id i : InstId) (hne : i ≠ id) :
    ((killOne w D id).st i).box = (w.st i).box ∧
      ((killOne w D id).st i).prio = (w.st i).prio ∧
      ((killOne w D id).st i).life = (w.st i).life := by
  let w1 := readCells D w id
  have hst1 : w1.st i = w.st i := cellsSt D w id i
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
  let w4 := failWaiters w3 id
  have hmail4 := failFold_mail w3 id i w3.roster
  have hlife4 := failFold_life w3 id i w3.roster
  let w5 := forgetSender w4 id
  have h5 := forgetFold_mail w4 id i w4.roster
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  refine ⟨?_, ?_, ?_⟩
  · exact h5.1.trans (hmail4.1.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst1))))
  · exact h5.2.1.trans (hmail4.2.1.trans (h3.2.2.2.1.trans (h2.2.2.2.1.trans (congrArg (·.prio) hst1))))
  · exact h5.2.2.2.1.trans (hlife4.trans (h3.2.1.trans (h2.2.1.trans (congrArg (·.life) hst1))))

theorem killOne_holds (w : World) (D : Description) (id i : InstId) (hne : i ≠ id)
    (hh : holdsPhase (w.st i).phase = true) :
    ((killOne w D id).st i).phase = (w.st i).phase ∧
      ((killOne w D id).st i).typestate = (w.st i).typestate := by
  let w1 := readCells D w id
  have hst1 : w1.st i = w.st i := cellsSt D w id i
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
  have hh3 : holdsPhase (w3.st i).phase = true := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hh]
  let w4 := failWaiters w3 id
  have h4 := failFold_holds w3 id i w3.roster hh3
  let w5 := forgetSender w4 id
  have h5 := forgetFold_mail w4 id i w4.roster
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact ⟨h5.2.2.1.trans (h4.1.trans (h3.1.trans (h2.1.trans (congrArg (·.phase) hst1)))),
    h5.2.2.2.2.trans (h4.2.trans (h3.2.2.2.2.2.trans (h2.2.2.2.2.2.trans
      (congrArg (·.typestate) hst1))))⟩

theorem nil_sublist {α : Type} : ∀ xs : List α, ([] : List α).Sublist xs
  | [] => List.Sublist.refl []
  | x :: xs => List.Sublist.cons x (nil_sublist xs)

theorem killOne_parked_sub (w : World) (D : Description) (id i : InstId) :
    ((killOne w D id).st i).parked.Sublist (w.st i).parked := by
  by_cases hne : i = id
  · rw [hne, (killOne_self w D id).2.2.2.2]
    exact nil_sublist _
  · let w1 := readCells D w id
    have hst1 : w1.st i = w.st i := cellsSt D w id i
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
    let w4 := failWaiters w3 id
    have h4 := failFold_mail w3 id i w3.roster
    let w5 := forgetSender w4 id
    have h5 := forgetFold_parked_sub w4 id i w4.roster
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hne]
    have hpark : (w4.st i).parked = (w.st i).parked := by
      have h4p : (w4.st i).parked = (w3.st i).parked := by
        simpa [w4, failWaiters] using h4.2.2
      exact h4p.trans (h3.2.2.2.2.1.trans (h2.2.2.2.2.1.trans (congrArg (·.parked) hst1)))
    exact List.Sublist.trans h5 (by rw [hpark]; exact List.Sublist.refl _)

/-- An actor that is already not alive stays that way: a kill never reuses its id. -/
theorem killFold_stays_dead (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hdead : (w.st s).life ≠ .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life ≠
      .alive := by
  induction ids generalizing w with
  | nil => simpa using hdead
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      by_cases hs : s = id
      · have hlive : (w.st id).life = .alive := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.2
        rw [← hs] at hlive
        exact absurd hlive hdead
      · exact ih (killOne w D id) ((killOne_other_rest w D id s hs).2.2.symm ▸ hdead)
    · exact ih w hdead

/-- A dead idle actor stays idle: a later kill does not put it back to work. -/
theorem killFold_keeps_idle (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (hdead : (w.st s).life = .dead) (hidle : (w.st s).phase = .idle) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .idle := by
  induction ids generalizing w with
  | nil => simpa using hidle
  | cons id ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D id sub key && (w.st id).life == .alive) = true
    · simp only [hcond, ite_true]
      by_cases hs : s = id
      · subst hs
        have hlive : (w.st s).life = .alive := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.2
        rw [hdead] at hlive
        cases hlive
      · have hh : holdsPhase (w.st s).phase = true := by rw [hidle]; rfl
        have hph := (killOne_holds w D id s hs hh).1
        have hlife := (killOne_other_rest w D id s hs).2.2
        exact ih (killOne w D id) (hlife.symm ▸ hdead) (hph.symm ▸ hidle)
    · simp only [hcond]
      exact ih w hdead hidle

theorem killMembers_stays_dead (w : World) (D : Description) (sub : String) (key : Nat)
    (s : InstId) (hdead : (w.st s).life ≠ .alive) :
    ((killMembers w D sub key).st s).life ≠ .alive := by
  simpa [killMembers] using killFold_stays_dead w D sub key w.roster s hdead

theorem killSubtree_stays_dead (w : World) (D : Description) (sub : String) (key : Nat)
    (s : InstId) (hdead : (w.st s).life ≠ .alive) :
    ((killSubtree w D sub key).st s).life ≠ .alive := by
  simpa [killSubtree, plant_st] using killMembers_stays_dead w D sub key s hdead

/-- A survivor's parked list is unchanged when no killed member has mail parked there. -/
theorem killFold_parked_keep (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (h : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ p ∈ (w.st s).parked, p.sender ≠ id)
    (hlive : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked =
      (w.st s).parked := by
  induction ids generalizing w with
  | nil => simp at hlive ⊢
  | cons j js ih =>
    simp only [List.foldl_cons] at hlive ⊢
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true] at hlive ⊢
      by_cases hs : s = j
      · subst hs
        have hdead : ((killOne w D s).st s).life ≠ .alive := by
          rw [(killOne_self w D s).1]
          decide
        exact absurd hlive (killFold_stays_dead (killOne w D s) D sub key js s hdead)
      · have hmem : isMember D j sub key = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.1
        have hjalive : (w.st j).life = .alive := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.2
        have heq := killOne_parked_keep w D j s hs (h j hmem hjalive)
        have h' : ∀ id, isMember D id sub key = true → ((killOne w D j).st id).life = .alive →
            ∀ p ∈ ((killOne w D j).st s).parked, p.sender ≠ id := by
          intro id hmem' halive' p hp
          have hp0 : p ∈ (w.st s).parked := by rw [heq] at hp; exact hp
          by_cases hid : id = j
          · subst hid
            have hdead : ((killOne w D id).st id).life = .dead := (killOne_self w D id).1
            rw [hdead] at halive'
            cases halive'
          · exact h id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') p hp0
        exact (ih (killOne w D j) h' hlive).trans heq
    · simp only [hcond] at hlive ⊢
      exact ih w h hlive

theorem killSubtree_parked_keep (w : World) (D : Description) (sub : String) (key : Nat)
    (s : InstId)
    (h : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ p ∈ (w.st s).parked, p.sender ≠ id)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) :
    ((killSubtree w D sub key).st s).parked = (w.st s).parked := by
  have hlive' : ((killMembers w D sub key).st s).life = .alive := by
    simpa [killSubtree, plant_st] using hlive
  have hmem := killFold_parked_keep w D sub key w.roster s h (by simpa [killMembers] using hlive')
  simpa [killSubtree, killMembers, plant_st] using hmem

/-- If `s` is still alive after the fold, no step killed it, so its bulk mail is unchanged
and a phase the kill does not rewrite is still that phase. -/
theorem killFold_if_alive (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (hlive : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .alive) :
    (w.st s).life = .alive ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
        (w.st s).box ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).prio =
        (w.st s).prio ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked.Sublist
        (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
          (w.st s).phase ∧
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).typestate =
          (w.st s).typestate) := by
  induction ids generalizing w with
  | nil =>
    dsimp [List.foldl] at hlive ⊢
    refine ⟨hlive, rfl, rfl, List.Sublist.refl _, ?_⟩
    intro _
    exact ⟨rfl, rfl⟩
  | cons id ids ih =>
    simp only [List.foldl_cons] at hlive ⊢
    split at hlive
    · next hcond =>
      simp only [hcond] at hlive ⊢
      have hih := ih (killOne w D id) hlive
      by_cases hs : s = id
      · rw [hs] at hih
        simp [(killOne_self w D id).1] at hih
      · have hrest := killOne_other_rest w D id s hs
        have hpark := killOne_parked_sub w D id s
        refine ⟨hrest.2.2.symm.trans hih.1, hih.2.1.trans hrest.1, hih.2.2.1.trans hrest.2.1,
          List.Sublist.trans hih.2.2.2.1 hpark, ?_⟩
        intro hh
        have hhold := killOne_holds w D id s hs hh
        have hh' : holdsPhase ((killOne w D id).st s).phase = true := by rw [hhold.1, hh]
        have hph := hih.2.2.2.2 hh'
        exact ⟨hph.1.trans hhold.1, hph.2.trans hhold.2⟩
    · next hcond =>
      simp only [hcond] at hlive ⊢
      exact ih w hlive

theorem killMembers_if_alive (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hlive : ((killMembers w D sub key).st s).life = .alive) :
    (w.st s).life = .alive ∧ ((killMembers w D sub key).st s).box = (w.st s).box ∧
      ((killMembers w D sub key).st s).prio = (w.st s).prio ∧
      ((killMembers w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killMembers w D sub key).st s).phase = (w.st s).phase ∧
          ((killMembers w D sub key).st s).typestate = (w.st s).typestate) := by
  simpa [killMembers] using killFold_if_alive w D sub key w.roster s hlive

theorem killSubtree_if_alive (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) :
    (w.st s).life = .alive ∧ ((killSubtree w D sub key).st s).box = (w.st s).box ∧
      ((killSubtree w D sub key).st s).prio = (w.st s).prio ∧
      ((killSubtree w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
          ((killSubtree w D sub key).st s).typestate = (w.st s).typestate) := by
  have hlive' : ((killMembers w D sub key).st s).life = .alive := by
    simpa [killSubtree, plant_st] using hlive
  have hmem := killMembers_if_alive w D sub key s hlive'
  simpa [killSubtree, plant_st] using hmem

/-- An actor that is already not alive is not killed, so its mail and a stable phase stay. -/
theorem killFold_if_dead (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hdead : (w.st s).life ≠ .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        (w.st s).life ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
        (w.st s).box ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).prio =
        (w.st s).prio ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked.Sublist
        (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
          (w.st s).phase ∧
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).typestate =
          (w.st s).typestate) := by
  induction ids generalizing w with
  | nil =>
    dsimp [List.foldl]
    exact ⟨rfl, rfl, rfl, List.Sublist.refl _, fun _ => ⟨rfl, rfl⟩⟩
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      by_cases hs : s = id
      · have hlive : (w.st id).life = .alive := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.2
        rw [← hs] at hlive
        exact absurd hlive hdead
      · have hrest := killOne_other_rest w D id s hs
        have hpark := killOne_parked_sub w D id s
        have hdead' : ((killOne w D id).st s).life ≠ .alive := by rw [hrest.2.2]; exact hdead
        have hih := ih (killOne w D id) hdead'
        refine ⟨hih.1.trans hrest.2.2, hih.2.1.trans hrest.1, hih.2.2.1.trans hrest.2.1,
          List.Sublist.trans hih.2.2.2.1 hpark, ?_⟩
        intro hh
        have hhold := killOne_holds w D id s hs hh
        have hh' : holdsPhase ((killOne w D id).st s).phase = true := by rw [hhold.1]; exact hh
        have hph := hih.2.2.2.2 hh'
        exact ⟨hph.1.trans hhold.1, hph.2.trans hhold.2⟩
    · exact ih w hdead

theorem killSubtree_if_dead (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hdead : (w.st s).life ≠ .alive) :
    ((killSubtree w D sub key).st s).life = (w.st s).life ∧
      ((killSubtree w D sub key).st s).box = (w.st s).box ∧
      ((killSubtree w D sub key).st s).prio = (w.st s).prio ∧
      ((killSubtree w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
          ((killSubtree w D sub key).st s).typestate = (w.st s).typestate) := by
  have hmem := killFold_if_dead w D sub key w.roster s hdead
  simpa [killSubtree, killMembers, plant_st] using hmem

theorem sublist_nil {α : Type} {xs : List α} (h : xs.Sublist ([] : List α)) : xs = [] := by
  cases h
  rfl

/-- An actor a kill actually removes ends dead, idle, and with an empty mailbox. -/
theorem killFold_died (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hl : (w.st s).life = .alive)
    (hd : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life ≠
        .alive) :
    isMember D s sub key = true ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .dead ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .idle ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
        [] ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).prio =
        [] ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked =
        [] := by
  induction ids generalizing w with
  | nil =>
    simp at hd
    exact absurd hl hd
  | cons j js ih =>
    simp only [List.foldl_cons] at hd ⊢
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true] at hd ⊢
      by_cases hs : s = j
      · subst hs
        have hself := killOne_self w D s
        have hdead : ((killOne w D s).st s).life ≠ .alive := by
          rw [hself.1]
          decide
        have hrest := killFold_if_dead (killOne w D s) D sub key js s hdead
        have hmem : isMember D s sub key = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          exact hcond.1
        refine ⟨hmem, hrest.1.trans hself.1, ?_, hrest.2.1.trans hself.2.2.1,
          hrest.2.2.1.trans hself.2.2.2.1, ?_⟩
        · have hh : holdsPhase ((killOne w D s).st s).phase = true := by
            simp [holdsPhase, hself.2.1]
          exact (hrest.2.2.2.2 hh).1.trans hself.2.1
        · exact sublist_nil (hself.2.2.2.2 ▸ hrest.2.2.2.1)
      · have hlife : ((killOne w D j).st s).life = .alive :=
          (killOne_other_rest w D j s hs).2.2.symm ▸ hl
        exact ih (killOne w D j) hlife hd
    · simp only [hcond] at hd ⊢
      exact ih w hl hd

theorem killSubtree_died (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hl : (w.st s).life = .alive)
    (hd : ((killSubtree w D sub key).st s).life ≠ .alive) :
    isMember D s sub key = true ∧ ((killSubtree w D sub key).st s).life = .dead ∧
      ((killSubtree w D sub key).st s).phase = .idle ∧
      ((killSubtree w D sub key).st s).box = [] ∧
      ((killSubtree w D sub key).st s).prio = [] ∧
      ((killSubtree w D sub key).st s).parked = [] := by
  have hd' : ((killMembers w D sub key).st s).life ≠ .alive := by
    simpa [killSubtree, plant_st] using hd
  have hmem := killFold_died w D sub key w.roster s hl (by simpa [killMembers] using hd')
  simpa [killSubtree, killMembers, plant_st] using hmem

theorem filterMap_none {α β : Type} (f : α → Option β) : ∀ xs : List α, xs.filterMap f = [] →
    ∀ a ∈ xs, f a = none
  | [], _, _, ha => by cases ha
  | x :: xs, h, a, ha => by
    simp only [List.filterMap] at h
    cases hf : f x with
    | none =>
      simp only [hf] at h
      cases ha with
      | head => exact hf
      | tail _ ha => exact filterMap_none f xs h a ha
    | some b => simp [hf] at h

theorem findSome_template (xs : List Template) (name : String) (t : Template)
    (h : xs.findSome? (fun u => if u.name == name then some u else none) = some t) :
    t ∈ xs ∧ t.name = name := by
  induction xs with
  | nil => simp at h
  | cons u us ih =>
    rw [List.findSome?_cons] at h
    by_cases hn : (u.name == name) = true
    · simp only [hn, ite_true] at h
      cases h
      exact ⟨List.Mem.head _, by simpa [beq_iff_eq] using hn⟩
    · have hf : (u.name == name) = false := by
        cases hbb : u.name == name <;> simp_all
      simp only [hf, ite_false] at h
      obtain ⟨hm, hname⟩ := ih h
      exact ⟨List.Mem.tail _ hm, hname⟩

theorem templateOf_mem (D : Description) (name : String) (t : Template)
    (h : templateOf D name = some t) : t ∈ D.templates ∧ t.name = name := by
  simpa [templateOf] using findSome_template D.templates name t h

/-- A passing subtree check makes every member terminable. A non-terminable role
is not part of a subtree, so a kill does not select it. -/
theorem member_terminable (D : Description) (hsub : subtreeFails D = []) (id : InstId)
    (sub : String) (key : Nat) (hm : isMember D id sub key = true) :
    terminableB D (tname id) = true := by
  cases id with
  | core _ => simp [isMember] at hm
  | peer role k =>
    have hm0 := hm
    simp only [isMember, Bool.and_eq_true] at hm0
    obtain ⟨⟨_, hsubb⟩, htreeb⟩ := hm0
    have htree : templateSubtree D role = sub := by simpa [beq_iff_eq] using htreeb
    have hsubne : sub ≠ "" := by
      have hfalse : (sub == "") = false := by simpa [bne] using hsubb
      simpa [beq_iff_eq] using hfalse
    obtain ⟨t, ht, htree'⟩ : ∃ t, templateOf D role = some t ∧ t.subtree = sub := by
      cases hto : templateOf D role with
      | none =>
        simp [templateSubtree, hto] at htree
        exact absurd htree hsubne
      | some t =>
        exact ⟨t, rfl, by simpa [templateSubtree, hto] using htree⟩
    have hmem := templateOf_mem D role t ht
    let classify : Template → Option String := fun u =>
        if u.subtree == "" then
          if u.timeoutKills then some s!"fail: {u.name} sets timeoutKills without a subtree"
          else if templatePure D u.name then some (pureKillMsg u.name)
          else none
        else if u.multiplicity != .perPeer then
          some s!"fail: subtree {u.subtree} member {u.name} is not per-peer"
        else if !u.terminable then
          some s!"fail: subtree {u.subtree} member {u.name} is not terminable"
        else if !(D.templates.any fun v => v.subtree == u.subtree && v.timeoutKills) then
          some s!"fail: subtree {u.subtree} has no timeoutKills role"
        else if u.supervisor != "" &&
            (match templateOf D u.supervisor with
              | some s => !(s.multiplicity == .one)
              | none => true) then
          some s!"fail: subtree {u.subtree} supervisor {u.supervisor} is not a permanent core"
        else if templatePure D u.name && !u.timeoutKills then
          some (pureKillMsg u.name)
        else none
    have hmap : D.templates.filterMap classify = [] := by
      simp only [subtreeFails, classify] at hsub
      exact hsub
    have hnone : classify t = none := filterMap_none classify D.templates hmap t hmem.1
    have hsubne' : sub ≠ "" := by simpa [bne, beq_iff_eq] using hsubne
    have hne : (t.subtree == "") = false := by simpa [beq_iff_eq, htree'] using hsubne'
    have hterm : t.terminable = true := by
      cases ht' : t.terminable with
      | true => rfl
      | false =>
        have hbad : classify t ≠ none := by
          simp only [classify]
          rw [hne, ht']
          cases hper : t.multiplicity == .perPeer
          · simp only [bne, hper, Bool.not_false, ite_true]
            intro h
            cases h
          · simp only [bne, hper, Bool.not_true, ite_false, ite_true]
            intro h
            cases h
        exact absurd hnone hbad
    simp [terminableB, tname, ht, hterm]

/-- `readCells` records the current value and clears dirty. It does not raise a value
or set a clean bit. -/
theorem readCells_quiet (D : Description) (w : World) (id : InstId) (d l : String) :
    ((readCells D w id).cell d l).value = (w.cell d l).value ∧
      ((w.cell d l).dirty = false → ((readCells D w id).cell d l).dirty = false) := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => exact ⟨rfl, fun h => h⟩
  | cons lab labs ih =>
    simp only [List.foldl_cons]
    let c := w.cell (tname id) lab
    let w1 := setCell w (tname id) lab { c with dirty := false }
    have hv1 : ∀ d l, (w1.cell d l).value = (w.cell d l).value := by
      intro d l
      simp only [w1, setCell, c]
      by_cases hhit : d = tname id ∧ l = lab
      · simp [hhit]
      · simp [hhit]
    have hd1 : ∀ d l, (w.cell d l).dirty = false → (w1.cell d l).dirty = false := by
      intro d l h
      simp only [w1, setCell, c]
      by_cases hhit : d = tname id ∧ l = lab
      · simp [hhit]
      · simp [hhit, h]
    have hih := ih (setObserved w1 id lab c.value)
    have hc : (setObserved w1 id lab c.value).cell = w1.cell := rfl
    refine ⟨?_, ?_⟩
    · rw [hih.1, hc]
      exact hv1 d l
    · intro h
      exact hih.2 (by rw [hc]; exact hd1 d l h)

theorem failWaiter_cell (w : World) (dead i : InstId) (d l : String) :
    (failWaiter w dead i).cell d l = w.cell d l := by
  unfold failWaiter
  split
  · rfl
  · cases hph : (w.st i).phase with
    | parked dst b k =>
      simp only [hph]
      split <;> simp [setActor]
    | awaitReply dst k =>
      simp only [hph]
      split <;> simp [setActor]
    | idle => simp [hph]
    | run k => simp [hph]
    | awaitEffect k => simp [hph]
    | awaitPeer k => simp [hph]
    | crashed => simp [hph]

theorem foldFail_cell (w : World) (dead : InstId) (ids : List InstId) (d l : String) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).cell d l) = w.cell d l := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih, failWaiter_cell]

theorem foldForget_cell (w : World) (dead : InstId) (ids : List InstId) (d l : String) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w).cell d l) =
      w.cell d l := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> simp [setActor]

theorem refundMsgs_cell (w : World) (name : String) (ms : List Msg) (d l : String) :
    ((refundMsgs w name ms).cell d l) = w.cell d l := by
  induction ms generalizing w with
  | nil => unfold refundMsgs; rfl
  | cons m ms ih =>
    unfold refundMsgs
    simp only [List.foldl_cons]
    rw [← refundMsgs, ih]
    simp [creditSender, setActor]

theorem refundParked_cell (w : World) (name : String) (ps : List Parked) (d l : String) :
    ((refundParked w name ps).cell d l) = w.cell d l := by
  induction ps generalizing w with
  | nil => unfold refundParked; rfl
  | cons p ps ih =>
    unfold refundParked
    simp only [List.foldl_cons]
    rw [← refundParked, ih]
    simp [creditSender, setActor]

theorem killOne_cell (w : World) (D : Description) (id : InstId) :
    (killOne w D id).cell = (readCells D w id).cell := by
  unfold killOne
  funext d l
  simp only [setActor]
  unfold forgetSender failWaiters
  rw [foldForget_cell, foldFail_cell, refundParked_cell, refundMsgs_cell]

theorem killOne_quiet (w : World) (D : Description) (id : InstId) (d l : String) :
    ((killOne w D id).cell d l).value = (w.cell d l).value ∧
      ((w.cell d l).dirty = false → ((killOne w D id).cell d l).dirty = false) := by
  rw [killOne_cell]
  exact readCells_quiet D w id d l

theorem killFold_quiet (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (d l : String) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).cell d l).value =
      (w.cell d l).value ∧
      ((w.cell d l).dirty = false →
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).cell d l).dirty =
          false) := by
  induction ids generalizing w with
  | nil => exact ⟨rfl, fun h => h⟩
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next _ =>
      obtain ⟨hv, hd⟩ := ih (killOne w D id)
      exact ⟨hv.trans (killOne_quiet w D id d l).1, fun h => hd ((killOne_quiet w D id d l).2 h)⟩
    · exact ih w

theorem killSubtree_quiet (w : World) (D : Description) (sub : String) (key : Nat) (d l : String) :
    ((killSubtree w D sub key).cell d l).value = (w.cell d l).value ∧
      ((w.cell d l).dirty = false → ((killSubtree w D sub key).cell d l).dirty = false) := by
  simpa [killSubtree, killMembers, plant_cell] using killFold_quiet w D sub key w.roster d l

/-- `failWaiter` writes `.idle` or a continuation. It never installs a parked phase. -/
theorem failWaiter_keeps_off (w : World) (dead i j dst : InstId) (c : Bool)
    (h : ∀ k, (w.st j).phase ≠ .parked dst c k) :
    ∀ k, ((failWaiter w dead i).st j).phase ≠ .parked dst c k := by
  intro k
  by_cases hj : j = i
  · rw [hj] at h ⊢
    unfold failWaiter
    split
    · exact h k
    · cases hph : (w.st i).phase with
      | parked d b k' =>
        simp only [hph]
        split
        · intro hbad
          cases hk : k'.rest <;> simp [setActor, proceed, hk] at hbad
        · exact h k
      | awaitReply d k' =>
        simp only [hph]
        split
        · intro hbad
          simp [setActor] at hbad
        · exact h k
      | idle => exact h k
      | run _ => exact h k
      | awaitEffect _ => exact h k
      | awaitPeer _ => exact h k
      | crashed => exact h k
  · rw [failWaiter_other w dead i j hj]
    exact h k

/-- A sender parked on someone other than `dead` keeps that phase through the failure fold. -/
theorem failFold_spares (w : World) (dead s dst : InstId) (ids : List InstId) (c : Bool) (k : Cont)
    (hdst : dst ≠ dead) (hph : (w.st s).phase = .parked dst c k) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = (w.st s).phase := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep : ((failWaiter w dead i).st s).phase = (w.st s).phase := by
      by_cases hsi : s = i
      · rw [hsi] at hph ⊢
        unfold failWaiter
        split
        · rfl
        · simp only [hph]
          have hne' : (dst == dead) = false := by simpa [beq_iff_eq] using hdst
          simp [hne']
          exact hph
      · exact congrArg (·.phase) (failWaiter_other w dead i s hsi)
    exact (ih (failWaiter w dead i) (by rw [hstep]; exact hph)).trans hstep

theorem failFold_keeps_off (w : World) (dead j dst : InstId) (ids : List InstId) (c : Bool)
    (h : ∀ k, (w.st j).phase ≠ .parked dst c k) :
    ∀ k, ((ids.foldl (fun w i => failWaiter w dead i) w).st j).phase ≠ .parked dst c k := by
  intro k
  induction ids generalizing w with
  | nil => simpa using h k
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (failWaiter_keeps_off w dead i j dst c h)

/-- A live waiter parked on `dead` is resumed, so that parked phase does not survive. -/
theorem failWaiter_clears (w : World) (dead s : InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive) :
    ∀ k', ((failWaiter w dead s).st s).phase ≠ .parked dead c k' := by
  intro k'
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, hph, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  intro hbad
  cases hk : k.rest <;> simp [setActor, proceed, hk] at hbad

theorem failFold_clears (w : World) (dead s : InstId) (ids : List InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive)
    (hs : s ∈ ids) :
    ∀ k', ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase ≠ .parked dead c k' := by
  intro k'
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    cases hs with
    | head =>
      exact failFold_keeps_off (failWaiter w dead s) dead s dead ids c
        (failWaiter_clears w dead s c k hph hl) k'
    | tail _ hmem =>
      by_cases heq : i = s
      · subst heq
        exact failFold_keeps_off (failWaiter w dead i) dead i dead ids c
          (failWaiter_clears w dead i c k hph hl) k'
      · have hst := failWaiter_other w dead i s (fun h => heq h.symm)
        exact ih (failWaiter w dead i) (by rw [hst]; exact hph) (by rw [hst]; exact hl) hmem

/-- Killing someone else leaves a sender parked on a third actor in that phase. -/
theorem killOne_spares (w : World) (D : Description) (j s dst : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ j) (hdst : dst ≠ j) (hph : (w.st s).phase = .parked dst c k) :
    ((killOne w D j).st s).phase = (w.st s).phase := by
  let w1 := readCells D w j
  have hst1 : w1.st s = w.st s := cellsSt D w j s
  let w2 := refundMsgs w1 (tname j) (w.st j).box
  have h2 := refundMsgs_rest w1 (tname j) (w.st j).box s
  let w3 := refundParked w2 (tname j) (w.st j).parked
  have h3 := refundParked_rest w2 (tname j) (w.st j).parked s
  have hph3 : (w3.st s).phase = .parked dst c k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  have h4 : ((failWaiters w3 j).st s).phase = (w3.st s).phase := by
    simpa [failWaiters] using failFold_spares w3 j s dst w3.roster c k hdst hph3
  let w4 := failWaiters w3 j
  let w5 := forgetSender w4 j
  have h5 := forgetFold_mail w4 j s w4.roster
  have hbody : killOne w D j =
      setActor w5 j { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have h4s : (w4.st s).phase = (w3.st s).phase := by simpa [w4] using h4
  exact h5.2.2.1.trans (h4s.trans (hph3.trans hph.symm))

/-- Killing `dst` resumes a live sender parked on it. -/
theorem killOne_drops_park (w : World) (D : Description) (dst s : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ dst) (hs : s ∈ w.roster) (hl : (w.st s).life = .alive)
    (hph : (w.st s).phase = .parked dst c k) :
    ∀ k', ((killOne w D dst).st s).phase ≠ .parked dst c k' := by
  let w1 := readCells D w dst
  have hst1 : w1.st s = w.st s := cellsSt D w dst s
  have hr1 : w1.roster = w.roster := cellsRoster D w dst
  let w2 := refundMsgs w1 (tname dst) (w.st dst).box
  have h2 := refundMsgs_rest w1 (tname dst) (w.st dst).box s
  have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname dst) (w.st dst).box
  let w3 := refundParked w2 (tname dst) (w.st dst).parked
  have h3 := refundParked_rest w2 (tname dst) (w.st dst).parked s
  have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname dst) (w.st dst).parked
  have hph3 : (w3.st s).phase = .parked dst c k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  have hl3 : (w3.st s).life = .alive := by
    rw [h3.2.1, h2.2.1, congrArg (·.life) hst1, hl]
  have hs3 : s ∈ w3.roster := by rw [hr3, hr2, hr1]; exact hs
  let w4 := failWaiters w3 dst
  have h4 := failFold_clears w3 dst s w3.roster c k hph3 hl3 hs3
  let w5 := forgetSender w4 dst
  have h5 := forgetFold_mail w4 dst s w4.roster
  have hbody : killOne w D dst =
      setActor w5 dst { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  intro k' hbad
  have : (w4.st s).phase = .parked dst c k' := by rw [← h5.2.2.1]; exact hbad
  exact h4 k' this

/-- A kill step does not install `.parked dst`. An actor already off that phase stays off it. -/
theorem killOne_keeps_off (w : World) (D : Description) (j s dst : InstId) (c : Bool)
    (h : ∀ k, (w.st s).phase ≠ .parked dst c k) :
    ∀ k, ((killOne w D j).st s).phase ≠ .parked dst c k := by
  intro k
  by_cases hne : s = j
  · subst hne
    intro hbad
    simp [(killOne_self w D s).2.1] at hbad
  · let w1 := readCells D w j
    have hst1 : w1.st s = w.st s := cellsSt D w j s
    let w2 := refundMsgs w1 (tname j) (w.st j).box
    have h2 := refundMsgs_rest w1 (tname j) (w.st j).box s
    let w3 := refundParked w2 (tname j) (w.st j).parked
    have h3 := refundParked_rest w2 (tname j) (w.st j).parked s
    have h3off : ∀ k, (w3.st s).phase ≠ .parked dst c k := by
      intro k'
      rw [h3.1, h2.1, congrArg (·.phase) hst1]
      exact h k'
    let w4 := failWaiters w3 j
    have h4 := failFold_keeps_off w3 j s dst w3.roster c h3off
    let w5 := forgetSender w4 j
    have h5 := forgetFold_mail w4 j s w4.roster
    have hbody : killOne w D j =
        setActor w5 j { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hne]
    intro hbad
    have hback : ((failWaiters w3 j).st s).phase = .parked dst c k := by
      have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
      rw [h5p] at hbad
      simpa [w4] using hbad
    exact h4 k hback

/-- While `dst` is a live member ahead in the fold, a sender parked on `dst` leaves that phase. -/
theorem killFold_unpark (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (h : ((w.st s).phase = .parked dst c k ∧ dst ∈ ids ∧ (w.st dst).life = .alive ∧
          isMember D dst sub key = true ∧ (w.st s).life = .alive) ∨
        (∀ k', (w.st s).phase ≠ .parked dst c k')) :
    ∀ k', ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase ≠
      .parked dst c k' := by
  induction ids generalizing w with
  | nil =>
    rcases h with ⟨_, hmem, _, _, _⟩ | hoff
    · cases hmem
    · exact hoff
  | cons j ids ih =>
    simp only [List.foldl_cons]
    rcases h with ⟨hph, hmem, hl, hm, hls⟩ | hoff
    · cases hmem with
      | head =>
        have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by
          simp [hm, hl]
        simp only [hcond, ite_true]
        by_cases hsd : s = dst
        · have hoff : ∀ k', ((killOne w D dst).st s).phase ≠ .parked dst c k' := by
            rw [hsd]
            intro k' hbad
            simp [(killOne_self w D dst).2.1] at hbad
          exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hoff)
        · have hdrop := killOne_drops_park w D dst s c k hsd hs hls hph
          exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hdrop)
      | tail _ hmem' =>
        by_cases hjd : j = dst
        · rw [hjd]
          have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by
            simp [hm, hl]
          simp only [hcond, ite_true]
          by_cases hsd : s = dst
          · have hoff : ∀ k', ((killOne w D dst).st s).phase ≠ .parked dst c k' := by
              rw [hsd]
              intro k' hbad
              simp [(killOne_self w D dst).2.1] at hbad
            exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hoff)
          · have hdrop := killOne_drops_park w D dst s c k hsd hs hls hph
            exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hdrop)
        · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
          · simp only [hcond, ite_true]
            by_cases hsj : s = j
            · have hoff : ∀ k', ((killOne w D j).st s).phase ≠ .parked dst c k' := by
                rw [hsj]
                intro k' hbad
                simp [(killOne_self w D j).2.1] at hbad
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs) (Or.inr hoff)
            · have hneDst : dst ≠ j := fun h => hjd h.symm
              have hsp := killOne_spares w D j s dst c k hsj hneDst hph
              have hl' : ((killOne w D j).st dst).life = .alive :=
                ((killOne_other_rest w D j dst hneDst).2.2).trans hl
              have hls' : ((killOne w D j).st s).life = .alive :=
                ((killOne_other_rest w D j s hsj).2.2).trans hls
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
                (Or.inl ⟨by rw [hsp]; exact hph, hmem', hl', hm, hls'⟩)
          · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
              cases hb : isMember D j sub key && (w.st j).life == .alive with
              | false => rfl
              | true => exact absurd hb hcond
            simp only [hf, ite_false]
            exact ih w hs (Or.inl ⟨hph, hmem', hl, hm, hls⟩)
    · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
      · simp only [hcond, ite_true]
        exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
          (Or.inr (killOne_keeps_off w D j s dst c hoff))
      · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
          cases hb : isMember D j sub key && (w.st j).life == .alive with
          | false => rfl
          | true => exact absurd hb hcond
        simp only [hf, ite_false]
        exact ih w hs (Or.inr hoff)

theorem killSubtree_unpark (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (hph : (w.st s).phase = .parked dst c k) (hls : (w.st s).life = .alive)
    (hl : (w.st dst).life = .alive) (hm : isMember D dst sub key = true)
    (hdst : dst ∈ w.roster) :
    ∀ k', ((killSubtree w D sub key).st s).phase ≠ .parked dst c k' := by
  simpa [killSubtree, killMembers, plant_st] using
    killFold_unpark w D sub key w.roster s dst c k hs
      (Or.inl ⟨hph, hdst, hl, hm, hls⟩)

/-- Resuming a waiter writes `.idle` or `.run`, and a later kill keeps one of those. -/
theorem failWaiter_shape (w : World) (dead s : InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive) :
    ((failWaiter w dead s).st s).phase = .idle ∨ ∃ k', ((failWaiter w dead s).st s).phase = .run k' := by
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, hph, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  cases hk : k.rest with
  | nil => exact Or.inl (by simp [setActor, proceed, hk])
  | cons _ _ => exact Or.inr ⟨k, by simp [setActor, proceed, hk]⟩

theorem failFold_shape (w : World) (dead s : InstId) (ids : List InstId)
    (h : ((w.st s).phase = .idle) ∨ ∃ k, (w.st s).phase = .run k) :
    (((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle) ∨
      ∃ k, ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .run k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep : ((failWaiter w dead i).st s).phase = .idle ∨
        ∃ k, ((failWaiter w dead i).st s).phase = .run k := by
      rcases h with hidle | ⟨k, hrun⟩
      · exact Or.inl ((failWaiter_holds w dead i s (by simp [holdsPhase, hidle])).1.trans hidle)
      · exact Or.inr ⟨k, (failWaiter_holds w dead i s (by simp [holdsPhase, hrun])).1.trans hrun⟩
    exact ih (failWaiter w dead i) hstep

theorem killOne_shape (w : World) (D : Description) (j s : InstId)
    (h : ((w.st s).phase = .idle) ∨ ∃ k, (w.st s).phase = .run k) :
    (((killOne w D j).st s).phase = .idle) ∨ ∃ k, ((killOne w D j).st s).phase = .run k := by
  by_cases hne : s = j
  · exact Or.inl (by rw [hne]; exact (killOne_self w D j).2.1)
  · rcases h with hidle | ⟨k, hrun⟩
    · exact Or.inl ((killOne_holds w D j s hne (by simp [holdsPhase, hidle])).1.trans hidle)
    · exact Or.inr ⟨k, (killOne_holds w D j s hne (by simp [holdsPhase, hrun])).1.trans hrun⟩

theorem failFold_resumes (w : World) (dead s : InstId) (ids : List InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive) (hs : s ∈ ids) :
    (((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle) ∨
      ∃ k', ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .run k' := by
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    cases hs with
    | head =>
      exact failFold_shape (failWaiter w dead s) dead s ids (failWaiter_shape w dead s c k hph hl)
    | tail _ hmem =>
      by_cases heq : i = s
      · subst heq
        exact failFold_shape (failWaiter w dead i) dead i ids (failWaiter_shape w dead i c k hph hl)
      · have hst := failWaiter_other w dead i s (fun h => heq h.symm)
        exact ih (failWaiter w dead i) (by rw [hst]; exact hph) (by rw [hst]; exact hl) hmem

theorem killOne_drops_shape (w : World) (D : Description) (dst s : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ dst) (hs : s ∈ w.roster) (hl : (w.st s).life = .alive)
    (hph : (w.st s).phase = .parked dst c k) :
    (((killOne w D dst).st s).phase = .idle) ∨ ∃ k', ((killOne w D dst).st s).phase = .run k' := by
  let w1 := readCells D w dst
  have hst1 : w1.st s = w.st s := cellsSt D w dst s
  have hr1 : w1.roster = w.roster := cellsRoster D w dst
  let w2 := refundMsgs w1 (tname dst) (w.st dst).box
  have h2 := refundMsgs_rest w1 (tname dst) (w.st dst).box s
  have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname dst) (w.st dst).box
  let w3 := refundParked w2 (tname dst) (w.st dst).parked
  have h3 := refundParked_rest w2 (tname dst) (w.st dst).parked s
  have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname dst) (w.st dst).parked
  have hph3 : (w3.st s).phase = .parked dst c k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  have hl3 : (w3.st s).life = .alive := by
    rw [h3.2.1, h2.2.1, congrArg (·.life) hst1, hl]
  have hs3 : s ∈ w3.roster := by rw [hr3, hr2, hr1]; exact hs
  have hfold : (((failWaiters w3 dst).st s).phase = .idle) ∨
      ∃ k', ((failWaiters w3 dst).st s).phase = .run k' := by
    simpa [failWaiters] using failFold_resumes w3 dst s w3.roster c k hph3 hl3 hs3
  let w4 := failWaiters w3 dst
  let w5 := forgetSender w4 dst
  have h5 := forgetFold_mail w4 dst s w4.roster
  have hbody : killOne w D dst =
      setActor w5 dst { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  rcases hfold with hidle | ⟨k', hrun⟩
  · have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
    exact Or.inl (by rw [h5p]; simpa [w4] using hidle)
  · have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
    exact Or.inr ⟨k', by rw [h5p]; simpa [w4] using hrun⟩

/-- A sender parked on a member that this fold kills is afterwards idle or running. -/
theorem killFold_resumed (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (h : ((w.st s).phase = .parked dst c k ∧ dst ∈ ids ∧ (w.st dst).life = .alive ∧
          isMember D dst sub key = true ∧ (w.st s).life = .alive) ∨
        (((w.st s).phase = .idle) ∨ ∃ k', (w.st s).phase = .run k')) :
    (((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .idle) ∨
      ∃ k', ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .run k' := by
  induction ids generalizing w with
  | nil =>
    rcases h with ⟨_, hmem, _, _, _⟩ | hshape
    · cases hmem
    · simpa using hshape
  | cons j ids ih =>
    simp only [List.foldl_cons]
    rcases h with ⟨hph, hmem, hl, hm, hls⟩ | hshape
    · cases hmem with
      | head =>
        have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by simp [hm, hl]
        simp only [hcond, ite_true]
        by_cases hsd : s = dst
        · have hshape : (((killOne w D dst).st s).phase = .idle) ∨
              ∃ k', ((killOne w D dst).st s).phase = .run k' := by
            rw [hsd]
            exact Or.inl (killOne_self w D dst).2.1
          exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hshape)
        · exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs)
            (Or.inr (killOne_drops_shape w D dst s c k hsd hs hls hph))
      | tail _ hmem' =>
        by_cases hjd : j = dst
        · rw [hjd]
          have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by simp [hm, hl]
          simp only [hcond, ite_true]
          by_cases hsd : s = dst
          · have hshape : (((killOne w D dst).st s).phase = .idle) ∨
                ∃ k', ((killOne w D dst).st s).phase = .run k' := by
              rw [hsd]
              exact Or.inl (killOne_self w D dst).2.1
            exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hshape)
          · exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs)
              (Or.inr (killOne_drops_shape w D dst s c k hsd hs hls hph))
        · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
          · simp only [hcond, ite_true]
            by_cases hsj : s = j
            · have hshape : (((killOne w D j).st s).phase = .idle) ∨
                  ∃ k', ((killOne w D j).st s).phase = .run k' := by
                rw [hsj]
                exact Or.inl (killOne_self w D j).2.1
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs) (Or.inr hshape)
            · have hneDst : dst ≠ j := fun h => hjd h.symm
              have hsp := killOne_spares w D j s dst c k hsj hneDst hph
              have hl' : ((killOne w D j).st dst).life = .alive :=
                ((killOne_other_rest w D j dst hneDst).2.2).trans hl
              have hls' : ((killOne w D j).st s).life = .alive :=
                ((killOne_other_rest w D j s hsj).2.2).trans hls
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
                (Or.inl ⟨by rw [hsp]; exact hph, hmem', hl', hm, hls'⟩)
          · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
              cases hb : isMember D j sub key && (w.st j).life == .alive with
              | false => rfl
              | true => exact absurd hb hcond
            simp only [hf, ite_false]
            exact ih w hs (Or.inl ⟨hph, hmem', hl, hm, hls⟩)
    · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
      · simp only [hcond, ite_true]
        exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
          (Or.inr (killOne_shape w D j s hshape))
      · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
          cases hb : isMember D j sub key && (w.st j).life == .alive with
          | false => rfl
          | true => exact absurd hb hcond
        simp only [hf, ite_false]
        exact ih w hs (Or.inr hshape)

theorem failWaiter_await_idle (w : World) (dead s : InstId) (k : Cont)
    (hph : (w.st s).phase = .awaitReply dead k) (hl : (w.st s).life = .alive) :
    ((failWaiter w dead s).st s).phase = .idle := by
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  simp [hlive, hph, setActor]

theorem failFold_await_idle (w : World) (dead s : InstId) (ids : List InstId)
    (h : (w.st s).phase = .idle) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i)
      ((failWaiter_holds w dead i s (by simp [holdsPhase, h])).1.trans h)

theorem failFold_drops_await (w : World) (dead s : InstId) (ids : List InstId) (k : Cont)
    (hph : (w.st s).phase = .awaitReply dead k) (hl : (w.st s).life = .alive) (hs : s ∈ ids) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle := by
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    cases hs with
    | head =>
      exact failFold_await_idle (failWaiter w dead s) dead s ids
        (failWaiter_await_idle w dead s k hph hl)
    | tail _ hmem =>
      by_cases heq : i = s
      · subst heq
        exact failFold_await_idle (failWaiter w dead i) dead i ids
          (failWaiter_await_idle w dead i k hph hl)
      · have hst := failWaiter_other w dead i s (fun h => heq h.symm)
        exact ih (failWaiter w dead i) (by rw [hst]; exact hph) (by rw [hst]; exact hl) hmem

theorem failFold_keeps_await (w : World) (dead s dst : InstId) (ids : List InstId) (k : Cont)
    (hdst : dst ≠ dead) (hph : (w.st s).phase = .awaitReply dst k) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = (w.st s).phase := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep : ((failWaiter w dead i).st s).phase = (w.st s).phase := by
      by_cases hsi : s = i
      · rw [hsi] at hph ⊢
        unfold failWaiter
        split
        · rfl
        · simp only [hph]
          have hne' : (dst == dead) = false := by simpa [beq_iff_eq] using hdst
          simp [hne']
          exact hph
      · exact congrArg (·.phase) (failWaiter_other w dead i s hsi)
    exact (ih (failWaiter w dead i) (by rw [hstep]; exact hph)).trans hstep

theorem killFold_await_idle (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (k : Cont) (hs : s ∈ w.roster)
    (h : ((w.st s).phase = .awaitReply dst k ∧ dst ∈ ids ∧ (w.st dst).life = .alive ∧
          isMember D dst sub key = true ∧ (w.st s).life = .alive) ∨
        (w.st s).phase = .idle) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .idle := by
  induction ids generalizing w with
  | nil =>
    rcases h with ⟨_, hmem, _, _, _⟩ | hidle
    · cases hmem
    · simpa using hidle
  | cons j ids ih =>
    simp only [List.foldl_cons]
    rcases h with ⟨hph, hmem, hl, hm, hls⟩ | hidle
    · cases hmem with
      | head =>
        have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by simp [hm, hl]
        simp only [hcond, ite_true]
        by_cases hsd : s = dst
        · have hidle : ((killOne w D dst).st s).phase = .idle := by
            rw [hsd]; exact (killOne_self w D dst).2.1
          exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hidle)
        · -- Killing `dst` fails the awaiter to idle. The chain is the await analogue of
          -- `killOne_drops_shape`.
          have hidle : ((killOne w D dst).st s).phase = .idle := by
            let w1 := readCells D w dst
            have hst1 : w1.st s = w.st s := cellsSt D w dst s
            have hr1 : w1.roster = w.roster := cellsRoster D w dst
            let w2 := refundMsgs w1 (tname dst) (w.st dst).box
            have h2 := refundMsgs_rest w1 (tname dst) (w.st dst).box s
            have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname dst) (w.st dst).box
            let w3 := refundParked w2 (tname dst) (w.st dst).parked
            have h3 := refundParked_rest w2 (tname dst) (w.st dst).parked s
            have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname dst) (w.st dst).parked
            have hph3 : (w3.st s).phase = .awaitReply dst k := by
              rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
            have hl3 : (w3.st s).life = .alive := by
              rw [h3.2.1, h2.2.1, congrArg (·.life) hst1, hls]
            have hs3 : s ∈ w3.roster := by rw [hr3, hr2, hr1]; exact hs
            have hfold := failFold_drops_await w3 dst s w3.roster k hph3 hl3 hs3
            let w4 := failWaiters w3 dst
            let w5 := forgetSender w4 dst
            have h5 := forgetFold_mail w4 dst s w4.roster
            have hbody : killOne w D dst =
                setActor w5 dst
                  { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
              simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
            rw [hbody, setActor_other _ _ _ _ hsd]
            have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
            rw [h5p]
            simpa [w4, failWaiters] using hfold
          exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hidle)
      | tail _ hmem' =>
        by_cases hjd : j = dst
        · rw [hjd]
          have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by simp [hm, hl]
          simp only [hcond, ite_true]
          by_cases hsd : s = dst
          · have hidle : ((killOne w D dst).st s).phase = .idle := by
              rw [hsd]; exact (killOne_self w D dst).2.1
            exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hidle)
          · have hidle : ((killOne w D dst).st s).phase = .idle := by
              let w1 := readCells D w dst
              have hst1 : w1.st s = w.st s := cellsSt D w dst s
              have hr1 : w1.roster = w.roster := cellsRoster D w dst
              let w2 := refundMsgs w1 (tname dst) (w.st dst).box
              have h2 := refundMsgs_rest w1 (tname dst) (w.st dst).box s
              have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname dst) (w.st dst).box
              let w3 := refundParked w2 (tname dst) (w.st dst).parked
              have h3 := refundParked_rest w2 (tname dst) (w.st dst).parked s
              have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname dst) (w.st dst).parked
              have hph3 : (w3.st s).phase = .awaitReply dst k := by
                rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
              have hl3 : (w3.st s).life = .alive := by
                rw [h3.2.1, h2.2.1, congrArg (·.life) hst1, hls]
              have hs3 : s ∈ w3.roster := by rw [hr3, hr2, hr1]; exact hs
              have hfold := failFold_drops_await w3 dst s w3.roster k hph3 hl3 hs3
              let w4 := failWaiters w3 dst
              let w5 := forgetSender w4 dst
              have h5 := forgetFold_mail w4 dst s w4.roster
              have hbody : killOne w D dst =
                  setActor w5 dst
                    { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
                simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
              rw [hbody, setActor_other _ _ _ _ hsd]
              have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
              rw [h5p]
              simpa [w4, failWaiters] using hfold
            exact ih (killOne w D dst) (by rw [killOne_roster]; exact hs) (Or.inr hidle)
        · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
          · simp only [hcond, ite_true]
            by_cases hsj : s = j
            · have hidle : ((killOne w D j).st s).phase = .idle := by
                rw [hsj]; exact (killOne_self w D j).2.1
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs) (Or.inr hidle)
            · have hneDst : dst ≠ j := fun h => hjd h.symm
              have hst : ((killOne w D j).st s).phase = (w.st s).phase := by
                -- `s` awaits `dst`, not `j`, so this kill does not rewrite `s`.
                let w1 := readCells D w j
                have hst1 : w1.st s = w.st s := cellsSt D w j s
                let w2 := refundMsgs w1 (tname j) (w.st j).box
                have h2 := refundMsgs_rest w1 (tname j) (w.st j).box s
                let w3 := refundParked w2 (tname j) (w.st j).parked
                have h3 := refundParked_rest w2 (tname j) (w.st j).parked s
                have hph3 : (w3.st s).phase = .awaitReply dst k := by
                  rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
                have h4 : ((failWaiters w3 j).st s).phase = (w3.st s).phase := by
                  simpa [failWaiters] using failFold_keeps_await w3 j s dst w3.roster k hneDst hph3
                let w4 := failWaiters w3 j
                let w5 := forgetSender w4 j
                have h5 := forgetFold_mail w4 j s w4.roster
                have hbody : killOne w D j =
                    setActor w5 j
                      { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
                  simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
                rw [hbody, setActor_other _ _ _ _ hsj]
                have h5p : (w5.st s).phase = (w4.st s).phase := by
                  simpa [w5, forgetSender] using h5.2.2.1
                have h4s : (w4.st s).phase = (w3.st s).phase := by simpa [w4] using h4
                exact h5p.trans (h4s.trans (hph3.trans hph.symm))
              have hl' : ((killOne w D j).st dst).life = .alive :=
                ((killOne_other_rest w D j dst hneDst).2.2).trans hl
              have hls' : ((killOne w D j).st s).life = .alive :=
                ((killOne_other_rest w D j s hsj).2.2).trans hls
              exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
                (Or.inl ⟨by rw [hst]; exact hph, hmem', hl', hm, hls'⟩)
          · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
              cases hb : isMember D j sub key && (w.st j).life == .alive with
              | false => rfl
              | true => exact absurd hb hcond
            simp only [hf, ite_false]
            exact ih w hs (Or.inl ⟨hph, hmem', hl, hm, hls⟩)
    · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
      · simp only [hcond, ite_true]
        by_cases hsj : s = j
        · have hidle' : ((killOne w D j).st s).phase = .idle := by
            rw [hsj]; exact (killOne_self w D j).2.1
          exact ih (killOne w D j) (by rw [killOne_roster]; exact hs) (Or.inr hidle')
        · exact ih (killOne w D j) (by rw [killOne_roster]; exact hs)
            (Or.inr ((killOne_holds w D j s hsj (by simp [holdsPhase, hidle])).1.trans hidle))
      · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
          cases hb : isMember D j sub key && (w.st j).life == .alive with
          | false => rfl
          | true => exact absurd hb hcond
        simp only [hf, ite_false]
        exact ih w hs (Or.inr hidle)

theorem killSubtree_await_idle (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (k : Cont) (hs : s ∈ w.roster)
    (hph : (w.st s).phase = .awaitReply dst k) (hls : (w.st s).life = .alive)
    (hl : (w.st dst).life = .alive) (hm : isMember D dst sub key = true) (hdst : dst ∈ w.roster) :
    ((killSubtree w D sub key).st s).phase = .idle := by
  simpa [killSubtree, killMembers, plant_st] using
    killFold_await_idle w D sub key w.roster s dst k hs (Or.inl ⟨hph, hdst, hl, hm, hls⟩)

theorem killSubtree_resumed (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (hph : (w.st s).phase = .parked dst c k) (hls : (w.st s).life = .alive)
    (hl : (w.st dst).life = .alive) (hm : isMember D dst sub key = true) (hdst : dst ∈ w.roster) :
    (((killSubtree w D sub key).st s).phase = .idle) ∨
      ∃ k', ((killSubtree w D sub key).st s).phase = .run k' := by
  simpa [killSubtree, killMembers, plant_st] using
    killFold_resumed w D sub key w.roster s dst c k hs (Or.inl ⟨hph, hdst, hl, hm, hls⟩)

/-- A live member on the roster is removed: dead, idle, and an empty mailbox. -/
theorem killFold_kills (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hm : isMember D s sub key = true)
    (hl : (w.st s).life = .alive) (hs : s ∈ ids) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .dead ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .idle ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
        [] ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).prio =
        [] ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked =
        [] := by
  induction ids generalizing w with
  | nil => cases hs
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hjs : j = s
    · rw [hjs]
      have hcond : (isMember D s sub key && (w.st s).life == .alive) = true := by simp [hm, hl]
      simp only [hcond, ite_true]
      have hself := killOne_self w D s
      have hdead : ((killOne w D s).st s).life ≠ .alive := by rw [hself.1]; decide
      have hrest := killFold_if_dead (killOne w D s) D sub key ids s hdead
      refine ⟨hrest.1.trans hself.1, ?_, hrest.2.1.trans hself.2.2.1,
        hrest.2.2.1.trans hself.2.2.2.1, sublist_nil (hself.2.2.2.2 ▸ hrest.2.2.2.1)⟩
      have hh : holdsPhase ((killOne w D s).st s).phase = true := by simp [holdsPhase, hself.2.1]
      exact (hrest.2.2.2.2 hh).1.trans hself.2.1
    · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
      · simp only [hcond, ite_true]
        have hne : s ≠ j := fun h => hjs h.symm
        have hl' : ((killOne w D j).st s).life = .alive :=
          ((killOne_other_rest w D j s hne).2.2).trans hl
        have hs' : s ∈ ids := by
          cases hs with
          | head => exact absurd rfl hjs
          | tail _ h => exact h
        exact ih (killOne w D j) hl' hs'
      · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
          cases hb : isMember D j sub key && (w.st j).life == .alive with
          | false => rfl
          | true => exact absurd hb hcond
        simp only [hf, ite_false]
        have hs' : s ∈ ids := by
          cases hs with
          | head => exact absurd rfl hjs
          | tail _ h => exact h
        exact ih w hl hs'

theorem killSubtree_kills (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hm : isMember D s sub key = true) (hl : (w.st s).life = .alive) (hs : s ∈ w.roster) :
    ((killSubtree w D sub key).st s).life = .dead ∧
      ((killSubtree w D sub key).st s).phase = .idle ∧
      ((killSubtree w D sub key).st s).box = [] ∧
      ((killSubtree w D sub key).st s).prio = [] ∧
      ((killSubtree w D sub key).st s).parked = [] := by
  simpa [killSubtree, killMembers, plant_st] using killFold_kills w D sub key w.roster s hm hl hs

/-- Parked or awaiting a reply. A kill rewrites these, and never installs them. -/
def isWait (ph : Phase) : Prop :=
  (∃ d c k, ph = .parked d c k) ∨ (∃ d k, ph = .awaitReply d k)

theorem failWaiter_keeps_wait (w : World) (dead i s : InstId) (h : isWait ((failWaiter w dead i).st s).phase) :
    (failWaiter w dead i).st s = w.st s := by
  unfold failWaiter at h ⊢
  by_cases hdead : ((w.st i).life != .alive) = true
  · simp [hdead]
  · simp only [hdead, ite_false] at h ⊢
    cases hph : (w.st i).phase with
    | parked d b k =>
      simp only [hph] at h ⊢
      by_cases hd : (d == dead) = true
      · simp only [hd, ite_true] at h ⊢
        by_cases hs : s = i
        · exfalso
          subst hs
          cases hk : k.rest with
          | nil => simp [setActor, proceed, hk, isWait] at h
          | cons _ _ => simp [setActor, proceed, hk, isWait] at h
        · simp [setActor, hs]
      · have hne : (d == dead) = false := by
          cases hb : (d == dead) with
          | false => rfl
          | true => exact absurd hb hd
        simp [hne]
    | awaitReply d k =>
      simp only [hph] at h ⊢
      by_cases hd : (d == dead) = true
      · simp only [hd, ite_true] at h ⊢
        by_cases hs : s = i
        · exfalso
          subst hs
          simp [setActor, isWait] at h
        · simp [setActor, hs]
      · have hne : (d == dead) = false := by
          cases hb : (d == dead) with
          | false => rfl
          | true => exact absurd hb hd
        simp [hne]
    | idle => simp [hph]
    | run _ => simp [hph]
    | awaitEffect _ => simp [hph]
    | awaitPeer _ => simp [hph]
    | crashed => simp [hph]

theorem failFold_keeps_wait (w : World) (dead s : InstId) (ids : List InstId)
    (h : isWait ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase) :
    (ids.foldl (fun w i => failWaiter w dead i) w).st s = w.st s := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.foldl_cons] at h ⊢
    have htail := ih (failWaiter w dead i) h
    rw [htail]
    exact failWaiter_keeps_wait w dead i s (by rw [← htail]; exact h)

theorem failWaiter_no_crash (w : World) (dead i s : InstId) (h : (w.st s).phase ≠ .crashed) :
    ((failWaiter w dead i).st s).phase ≠ .crashed := by
  by_cases hs : s = i
  · rw [hs] at h ⊢
    unfold failWaiter
    split
    · exact h
    · cases hph : (w.st i).phase with
      | parked _ _ k =>
        simp only [hph, beq_iff_eq]
        split
        · cases hk : k.rest <;> simp [setActor, proceed, hk]
        · exact h
      | awaitReply _ _ =>
        simp only [hph, beq_iff_eq]
        split
        · simp [setActor]
        · exact h
      | crashed => exact absurd hph h
      | idle => simp [hph]
      | run _ => simp [hph]
      | awaitEffect _ => simp [hph]
      | awaitPeer _ => simp [hph]
  · rw [failWaiter_other w dead i s hs]; exact h

theorem failFold_no_crash (w : World) (dead s : InstId) (ids : List InstId)
    (h : (w.st s).phase ≠ .crashed) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase ≠ .crashed := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (failWaiter_no_crash w dead i s h)

theorem killOne_no_crash (w : World) (D : Description) (id s : InstId) (h : (w.st s).phase ≠ .crashed) :
    ((killOne w D id).st s).phase ≠ .crashed := by
  by_cases hs : s = id
  · rw [hs, (killOne_self w D id).2.1]
    decide
  · let w1 := readCells D w id
    have hst1 : w1.st s = w.st s := cellsSt D w id s
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
    have hpre : (w3.st s).phase ≠ .crashed := by
      rw [h3.1, h2.1, congrArg (·.phase) hst1]; exact h
    let w4 := failWaiters w3 id
    have h4 := failFold_no_crash w3 id s w3.roster hpre
    let w5 := forgetSender w4 id
    have h5 := forgetFold_mail w4 id s w4.roster
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hs]
    have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
    rw [h5p]
    simpa [w4, failWaiters] using h4

theorem killFold_no_crash (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (h : (w.st s).phase ≠ .crashed) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase ≠
      .crashed := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (killOne_no_crash w D j s h)
    · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
        cases hb : isMember D j sub key && (w.st j).life == .alive with
        | false => rfl
        | true => exact absurd hb hcond
      simp only [hf, ite_false]
      exact ih w h

theorem killSubtree_no_crash (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : (w.st s).phase ≠ .crashed) :
    ((killSubtree w D sub key).st s).phase ≠ .crashed := by
  simpa [killSubtree, killMembers, plant_st] using killFold_no_crash w D sub key w.roster s h

/-- Every mailbox is a sublist of what it held: a kill refunds, filters, or empties. -/
theorem killSubtree_box_sub (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId) :
    ((killSubtree w D sub key).st s).box.Sublist (w.st s).box := by
  by_cases hl : (w.st s).life = .alive
  · by_cases hl' : ((killSubtree w D sub key).st s).life = .alive
    · rw [(killSubtree_if_alive w D sub key s hl').2.1]
      exact List.Sublist.refl _
    · rw [(killSubtree_died w D sub key s hl hl').2.2.2.1]
      exact nil_sublist _
  · rw [(killSubtree_if_dead w D sub key s hl).2.1]
    exact List.Sublist.refl _

theorem killSubtree_parked_sub (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId) :
    ((killSubtree w D sub key).st s).parked.Sublist (w.st s).parked := by
  by_cases hl : (w.st s).life = .alive
  · by_cases hl' : ((killSubtree w D sub key).st s).life = .alive
    · exact (killSubtree_if_alive w D sub key s hl').2.2.2.1
    · rw [(killSubtree_died w D sub key s hl hl').2.2.2.2.2]
      exact nil_sublist _
  · exact (killSubtree_if_dead w D sub key s hl).2.2.2.1

theorem killOne_keeps_wait (w : World) (D : Description) (id s : InstId)
    (h : isWait ((killOne w D id).st s).phase) :
    ((killOne w D id).st s).phase = (w.st s).phase ∧
      ((killOne w D id).st s).typestate = (w.st s).typestate := by
  by_cases hs : s = id
  · exfalso
    rw [hs, (killOne_self w D id).2.1, isWait] at h
    rcases h with ⟨_, _, _, hbad⟩ | ⟨_, _, hbad⟩ <;> cases hbad
  · let w1 := readCells D w id
    have hst1 : w1.st s = w.st s := cellsSt D w id s
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
    let w4 := failWaiters w3 id
    let w5 := forgetSender w4 id
    have h5 := forgetFold_mail w4 id s w4.roster
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    have hph : (w5.st s).phase = ((killOne w D id).st s).phase := by
      rw [hbody, setActor_other _ _ _ _ hs]
    have hty : (w5.st s).typestate = ((killOne w D id).st s).typestate := by
      rw [hbody, setActor_other _ _ _ _ hs]
    have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
    have h5t : (w5.st s).typestate = (w4.st s).typestate := by simpa [w5, forgetSender] using h5.2.2.2.2
    have hwait : isWait (w4.st s).phase := by rw [← h5p, hph]; exact h
    have h4 := failFold_keeps_wait w3 id s w3.roster (by simpa [w4, failWaiters] using hwait)
    have h4a : (w4.st s) = (w3.st s) := by simpa [w4, failWaiters] using h4
    refine ⟨?_, ?_⟩
    · rw [← hph, h5p, congrArg (·.phase) h4a, h3.1, h2.1, congrArg (·.phase) hst1]
    · rw [← hty, h5t, congrArg (·.typestate) h4a, h3.2.2.2.2.2, h2.2.2.2.2.2,
        congrArg (·.typestate) hst1]

theorem killFold_keeps_wait (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (h : isWait ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        (w.st s).phase ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).typestate =
        (w.st s).typestate := by
  induction ids generalizing w with
  | nil => exact ⟨rfl, rfl⟩
  | cons j ids ih =>
    simp only [List.foldl_cons] at h ⊢
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true] at h ⊢
      have hih := ih (killOne w D j) h
      have hstep := killOne_keeps_wait w D j s (by rw [← hih.1]; exact h)
      exact ⟨hih.1.trans hstep.1, hih.2.trans hstep.2⟩
    · have hf : (isMember D j sub key && (w.st j).life == .alive) = false := by
        cases hb : isMember D j sub key && (w.st j).life == .alive with
        | false => rfl
        | true => exact absurd hb hcond
      simp only [hf, ite_false] at h ⊢
      exact ih w h

theorem killSubtree_keeps_wait (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : isWait ((killSubtree w D sub key).st s).phase) :
    ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
      ((killSubtree w D sub key).st s).typestate = (w.st s).typestate := by
  simpa [killSubtree, killMembers, plant_st] using killFold_keeps_wait w D sub key w.roster s
    (by simpa [killSubtree, killMembers, plant_st] using h)

theorem killSubtree_prio_step (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId) :
    ((killSubtree w D sub key).st s).prio = (w.st s).prio ∨
      ((killSubtree w D sub key).st s).prio = [] := by
  by_cases hl : (w.st s).life = .alive
  · by_cases hl' : ((killSubtree w D sub key).st s).life = .alive
    · exact Or.inl (killSubtree_if_alive w D sub key s hl').2.2.1
    · exact Or.inr (killSubtree_died w D sub key s hl hl').2.2.2.2.1
  · exact Or.inl (killSubtree_if_dead w D sub key s hl).2.2.1

end Deadlock
