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

/-- A peer is a member of its own template's subtree, at the index it was spawned with. -/
theorem member_of_key (D : Description) (id : InstId) (t : Template) (key : Nat)
    (ht : templateOf D (tname id) = some t) (hsub : t.subtree ≠ "")
    (hkey : memberKey id = some key) : isMember D id t.subtree key = true := by
  cases id with
  | core _ => simp [memberKey] at hkey
  | peer role ix =>
    simp [memberKey] at hkey
    subst hkey
    have hbeq : (t.subtree == "") = false := by simpa [beq_iff_eq] using hsub
    have hne : (t.subtree != "") = true := by simp [bne, hbeq]
    have ht' : templateOf D role = some t := by simpa [tname] using ht
    simp [isMember, templateSubtree, ht', hne]

def timeoutKillsB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.timeoutKills
  | none => false

inductive Life where
  | absent
  | alive
  /-- Has begun to terminate. It accepts nothing. A later `exec` seals it to `dead`. -/
  | shuttingDown
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- How a life may change. Shutting down and death are permanent. An id is not reused. -/
def LifeStep (old new : Life) : Prop :=
  new = old ∨
    (old = .absent ∧ new = .alive) ∨
    (old = .alive ∧ new = .shuttingDown) ∨
    (old = .alive ∧ new = .dead) ∨
    (old = .shuttingDown ∧ new = .dead)

/-- The target will not handle mail: it has begun shutting down, or it has terminated. -/
def Halted (l : Life) : Prop := l = .shuttingDown ∨ l = .dead

/-- Effects carry the real message label. `hint` is a per-peer index; cores ignore it. -/
inductive Eff where
  | send (dst label : String) (hint : Nat)
  /-- `onFull` runs when the peer is alive but has no room. `onGone` runs when
  the peer is missing or not alive. The tail of the program is the admitted send. -/
  | trySend (dst label : String) (hint : Nat) (onFull onGone : List Eff)
  /-- `onNotAdmitted` runs when the request never enters the mailbox. `onTimedOut`
  runs when it was admitted and the deadline fires. The tail is the `Reply`. -/
  | call (dst label : String) (hint : Nat) (onNotAdmitted onTimedOut : List Eff)
  | reply
  | selfSchedule (label : String)
  | cell (dst label : String) (value : Nat)
  | internal
  /-- `onTimeout` runs when the external peer does not answer. The tail is the
  data result. -/
  | peer (onTimeout : List Eff)
  /-- A parent marks every child, terminable or not, and that child's descendants
  shutting down. Siblings are not children of each other. -/
  | abort
  | terminate
  /-- A per-peer stage spawns one child of `template` at its own subtree key.
  Cores do not run this effect: a supervision tree is built by its own members. -/
  | spawn (template : String)

mutual
private def decEff : DecidableEq Eff
  | .send d l n, .send d' l' n' =>
    if hd : d = d' then
      if hl : l = l' then
        if hn : n = n' then isTrue (by simp [hd, hl, hn])
        else isFalse (by intro h; cases h; exact hn rfl)
      else isFalse (by intro h; cases h; exact hl rfl)
    else isFalse (by intro h; cases h; exact hd rfl)
  | .send _ _ _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .send _ _ _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .send _ _ _, .reply => isFalse (by intro h; cases h)
  | .send _ _ _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .send _ _ _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .send _ _ _, .internal => isFalse (by intro h; cases h)
  | .send _ _ _, .peer _ => isFalse (by intro h; cases h)
  | .send _ _ _, .abort => isFalse (by intro h; cases h)
  | .send _ _ _, .terminate => isFalse (by intro h; cases h)
  | .send _ _ _, .spawn _ => isFalse (by intro h; cases h)
  | .trySend d l n f g, .trySend d' l' n' f' g' =>
    if hd : d = d' then
      if hl : l = l' then
        if hn : n = n' then
          match decEffs f f' with
          | isTrue hf =>
            match decEffs g g' with
            | isTrue hg => isTrue (by simp [hd, hl, hn, hf, hg])
            | isFalse hg => isFalse (by intro h; cases h; exact hg rfl)
          | isFalse hf => isFalse (by intro h; cases h; exact hf rfl)
        else isFalse (by intro h; cases h; exact hn rfl)
      else isFalse (by intro h; cases h; exact hl rfl)
    else isFalse (by intro h; cases h; exact hd rfl)
  | .trySend _ _ _ _ _, .send _ _ _ => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .reply => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .internal => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .peer _ => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .abort => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .terminate => isFalse (by intro h; cases h)
  | .trySend _ _ _ _ _, .spawn _ => isFalse (by intro h; cases h)
  | .call d l n na to, .call d' l' n' na' to' =>
    if hd : d = d' then
      if hl : l = l' then
        if hn : n = n' then
          match decEffs na na' with
          | isTrue hf =>
            match decEffs to to' with
            | isTrue hg => isTrue (by simp [hd, hl, hn, hf, hg])
            | isFalse hg => isFalse (by intro h; cases h; exact hg rfl)
          | isFalse hf => isFalse (by intro h; cases h; exact hf rfl)
        else isFalse (by intro h; cases h; exact hn rfl)
      else isFalse (by intro h; cases h; exact hl rfl)
    else isFalse (by intro h; cases h; exact hd rfl)
  | .call _ _ _ _ _, .send _ _ _ => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .reply => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .internal => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .peer _ => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .abort => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .terminate => isFalse (by intro h; cases h)
  | .call _ _ _ _ _, .spawn _ => isFalse (by intro h; cases h)
  | .reply, .reply => isTrue rfl
  | .reply, .send _ _ _ => isFalse (by intro h; cases h)
  | .reply, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .reply, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .reply, .selfSchedule _ => isFalse (by intro h; cases h)
  | .reply, .cell _ _ _ => isFalse (by intro h; cases h)
  | .reply, .internal => isFalse (by intro h; cases h)
  | .reply, .peer _ => isFalse (by intro h; cases h)
  | .reply, .abort => isFalse (by intro h; cases h)
  | .reply, .terminate => isFalse (by intro h; cases h)
  | .reply, .spawn _ => isFalse (by intro h; cases h)
  | .selfSchedule l, .selfSchedule l' =>
    if hl : l = l' then isTrue (by simp [hl]) else isFalse (by intro h; cases h; exact hl rfl)
  | .selfSchedule _, .send _ _ _ => isFalse (by intro h; cases h)
  | .selfSchedule _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .selfSchedule _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .selfSchedule _, .reply => isFalse (by intro h; cases h)
  | .selfSchedule _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .selfSchedule _, .internal => isFalse (by intro h; cases h)
  | .selfSchedule _, .peer _ => isFalse (by intro h; cases h)
  | .selfSchedule _, .abort => isFalse (by intro h; cases h)
  | .selfSchedule _, .terminate => isFalse (by intro h; cases h)
  | .selfSchedule _, .spawn _ => isFalse (by intro h; cases h)
  | .cell d l n, .cell d' l' n' =>
    if hd : d = d' then
      if hl : l = l' then
        if hn : n = n' then isTrue (by simp [hd, hl, hn])
        else isFalse (by intro h; cases h; exact hn rfl)
      else isFalse (by intro h; cases h; exact hl rfl)
    else isFalse (by intro h; cases h; exact hd rfl)
  | .cell _ _ _, .send _ _ _ => isFalse (by intro h; cases h)
  | .cell _ _ _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .cell _ _ _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .cell _ _ _, .reply => isFalse (by intro h; cases h)
  | .cell _ _ _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .cell _ _ _, .internal => isFalse (by intro h; cases h)
  | .cell _ _ _, .peer _ => isFalse (by intro h; cases h)
  | .cell _ _ _, .abort => isFalse (by intro h; cases h)
  | .cell _ _ _, .terminate => isFalse (by intro h; cases h)
  | .cell _ _ _, .spawn _ => isFalse (by intro h; cases h)
  | .internal, .internal => isTrue rfl
  | .internal, .send _ _ _ => isFalse (by intro h; cases h)
  | .internal, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .internal, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .internal, .reply => isFalse (by intro h; cases h)
  | .internal, .selfSchedule _ => isFalse (by intro h; cases h)
  | .internal, .cell _ _ _ => isFalse (by intro h; cases h)
  | .internal, .peer _ => isFalse (by intro h; cases h)
  | .internal, .abort => isFalse (by intro h; cases h)
  | .internal, .terminate => isFalse (by intro h; cases h)
  | .internal, .spawn _ => isFalse (by intro h; cases h)
  | .peer t, .peer t' =>
    match decEffs t t' with
    | isTrue h => isTrue (by simp [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .peer _, .send _ _ _ => isFalse (by intro h; cases h)
  | .peer _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .peer _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .peer _, .reply => isFalse (by intro h; cases h)
  | .peer _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .peer _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .peer _, .internal => isFalse (by intro h; cases h)
  | .peer _, .abort => isFalse (by intro h; cases h)
  | .peer _, .terminate => isFalse (by intro h; cases h)
  | .peer _, .spawn _ => isFalse (by intro h; cases h)
  | .abort, .abort => isTrue rfl
  | .abort, .send _ _ _ => isFalse (by intro h; cases h)
  | .abort, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .abort, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .abort, .reply => isFalse (by intro h; cases h)
  | .abort, .selfSchedule _ => isFalse (by intro h; cases h)
  | .abort, .cell _ _ _ => isFalse (by intro h; cases h)
  | .abort, .internal => isFalse (by intro h; cases h)
  | .abort, .peer _ => isFalse (by intro h; cases h)
  | .abort, .terminate => isFalse (by intro h; cases h)
  | .abort, .spawn _ => isFalse (by intro h; cases h)
  | .terminate, .terminate => isTrue rfl
  | .terminate, .send _ _ _ => isFalse (by intro h; cases h)
  | .terminate, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .terminate, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .terminate, .reply => isFalse (by intro h; cases h)
  | .terminate, .selfSchedule _ => isFalse (by intro h; cases h)
  | .terminate, .cell _ _ _ => isFalse (by intro h; cases h)
  | .terminate, .internal => isFalse (by intro h; cases h)
  | .terminate, .peer _ => isFalse (by intro h; cases h)
  | .terminate, .abort => isFalse (by intro h; cases h)
  | .terminate, .spawn _ => isFalse (by intro h; cases h)
  | .spawn l, .spawn l' =>
    if hl : l = l' then isTrue (by simp [hl]) else isFalse (by intro h; cases h; exact hl rfl)
  | .spawn _, .send _ _ _ => isFalse (by intro h; cases h)
  | .spawn _, .trySend _ _ _ _ _ => isFalse (by intro h; cases h)
  | .spawn _, .call _ _ _ _ _ => isFalse (by intro h; cases h)
  | .spawn _, .reply => isFalse (by intro h; cases h)
  | .spawn _, .selfSchedule _ => isFalse (by intro h; cases h)
  | .spawn _, .cell _ _ _ => isFalse (by intro h; cases h)
  | .spawn _, .internal => isFalse (by intro h; cases h)
  | .spawn _, .peer _ => isFalse (by intro h; cases h)
  | .spawn _, .abort => isFalse (by intro h; cases h)
  | .spawn _, .terminate => isFalse (by intro h; cases h)

private def decEffs : DecidableEq (List Eff)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs =>
    match decEff a b with
    | isTrue h =>
      match decEffs as bs with
      | isTrue hs => isTrue (by simp [h, hs])
      | isFalse hs => isFalse (by intro heq; cases heq; exact hs rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
end

instance : DecidableEq Eff := decEff

instance : Inhabited Eff := ⟨.send "" "" 0⟩

instance : Repr Eff where
  reprPrec _ _ := "eff"

/-- What the caller observes when a timed call ends.
`reply` is the callee's answer. `notAdmitted` means the deadline fired before
the request entered the mailbox. `timedOut` means it was admitted, then the
deadline fired: the request stays queued and a late reply is ignored. -/
inductive CallResult where
  | reply
  | notAdmitted
  | timedOut
  deriving DecidableEq, Repr, Inhabited

structure Cont where
  rest : List Eff
  toState : String
  replyTo : Option InstId
  /-- Run when a call ends as `NotAdmitted`. Empty leaves the actor idle. -/
  onNotAdmitted : List Eff := []
  /-- Run when an admitted call ends as `TimedOut`. Empty leaves the actor idle. -/
  onTimedOut : List Eff := []
  /-- Run when an `awaitPeer` times out. `rest` is the data result. -/
  onTimeout : List Eff := []
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
  /-- Identity the caller stamped on this call. A reply matches this id. -/
  callId : Option Nat := none
  /-- A supervision tombstone. It occupies a priority slot, the same as any other
  priority message. -/
  tombstone : Bool := false
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
  /-- Id of the call this actor is waiting on. Meaningful in `.parked _ true` and `.awaitReply`. -/
  waitId : Nat := 0
  /-- Next id this actor will stamp on a call it issues. Ids only grow. -/
  nextCall : Nat := 0
  /-- Id of the incoming call the current handler must answer, if there is one. -/
  oweId : Option Nat := none
  /-- Outcome of the last call this actor finished, with that call's id. -/
  lastCall : Option (Nat × CallResult) := none
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
  /-- Next key of a subtree. Every member of one instance is spawned under it. -/
  nextKey : String → Nat := fun _ => 0
  st : InstId → Actor
  cell : String → String → Cell
  observed : InstId → String → Nat
  /-- A route that named a per-peer role and did not resolve. Explicit, not a drop. -/
  failures : List (InstId × String) := []

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

/-- Population of `name` at root population `N`. A core is one instance. A
per-peer root — no supervisor, or a core supervisor — has `N` instances. A
per-peer child of a per-peer supervisor has that supervisor's population, one
child per parent, not a fresh `N`. `fuel` is the template count, so a cycle
stops. The chain is the product of those factors. -/
def population (D : Description) (name : String) (N fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    match templateOf D name with
    | none => 0
    | some t =>
      match t.multiplicity with
      | .one => 1
      | .perPeer =>
        if t.supervisor == "" then N
        else
          match templateOf D t.supervisor with
          | none => 0
          | some sup =>
            match sup.multiplicity with
            | .one => N
            | .perPeer => population D t.supervisor N fuel

/-- How many tombstones can sit on one instance of `parent` at once.
A per-peer parent has one instance of each child template. A core is the
supervisor of every instance, and that count is `population`: the product
along the supervision tree, not a flat `N` of labels. -/
def simultaneousTombstones (D : Description) (parent : String) (N : Nat) : Nat :=
  match templateOf D parent with
  | none => 0
  | some sup =>
    D.templates.foldl (fun n t =>
      if t.supervisor == parent && t.tombstone != "" then
        match sup.multiplicity with
        | .one => n + population D t.name N D.templates.length
        | .perPeer => n + 1
      else n) 0

/-- Slots a priority lane must have so it does not overflow: every child that
can tombstone at once, plus the other priority senders (self-schedules and
cell wakes). `otherSenders` is that second count. The checker will report a
template that fails this; it is not part of `LocalOk` yet. -/
def prioDemand (D : Description) (parent : String) (N otherSenders : Nat) : Nat :=
  simultaneousTombstones D parent N + otherSenders

def prioSized (D : Description) (parent : String) (N otherSenders : Nat) : Bool :=
  match templateOf D parent with
  | none => false
  | some t => decide (prioDemand D parent N otherSenders ≤ t.priorityCapacity.eval N)

/-- The instance a name denotes, whether or not it is alive. A missing template,
or a core addressing a per-peer role, does not resolve. -/
def resolveId (D : Description) (sender : InstId) (dst : String) : Option InstId :=
  match templateOf D dst with
  | none => none
  | some t =>
    match t.multiplicity with
    | .one => some (.core dst)
    | .perPeer =>
      match memberKey sender with
      | none => none
      | some k => some (.peer dst k)

/-- A live target only. A per-peer role is addressed by the sender's subtree key,
not by a literal hint. Shutting-down, dead, and never-spawned keys do not
resolve, so the send is dropped and stays dropped. -/
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

/-- The continuation of one call outcome. `Reply` is `rest`. The other two
outcomes do not share that program. -/
def selectCall (k : Cont) : CallResult → Cont
  | .reply => k
  | .notAdmitted => { k with rest := k.onNotAdmitted }
  | .timedOut => { k with rest := k.onTimedOut }

/-- Leave a call wait on the continuation of `r`. The id is retired, so a late
reply for it cannot match a later `awaitReply`. `waitId` becomes the next
unused id. -/
def finishCall (a : Actor) (k : Cont) (r : CallResult) : Actor :=
  let done := proceed a (selectCall k r)
  { done with lastCall := some (a.waitId, r), waitId := a.nextCall }

/-- Stamp the next call id onto `a` and remember it as the active wait. -/
def issueCall (a : Actor) : Actor :=
  let n := a.nextCall
  { a with waitId := n, nextCall := n + 1 }

theorem issueCall_keeps (a : Actor) :
    (issueCall a).typestate = a.typestate ∧ (issueCall a).life = a.life ∧
      (issueCall a).phase = a.phase := by
  simp [issueCall]

theorem condIssue_keeps (c : Bool) (a : Actor) :
    (if c then issueCall a else a).typestate = a.typestate ∧
      (if c then issueCall a else a).life = a.life ∧
        (if c then issueCall a else a).phase = a.phase := by
  cases c <;> simp [issueCall]

/-- The phase `proceed` reaches. It depends only on the continuation. -/
def resumed (k : Cont) : Phase :=
  match k.rest with
  | [] => .idle
  | _ => .run k

theorem proceed_resumed (a : Actor) (k : Cont) : (proceed a k).phase = resumed k := by
  cases hk : k.rest <;> simp [proceed, resumed, hk]

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
        -- A call records the id carried on the message, not the caller's later
        -- wait. A detached message has no `callFrom` and owes nothing.
        let owe : Option Nat :=
          match m.callFrom with
          | some _ => m.callId
          | none => none
        let a := { a with oweId := owe }
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
    -- Shutting-down, dead, and absent targets store nothing and are not charged.
    -- The drop is permanent: those lives do not return to alive, and a dead or
    -- shutting-down id is not spawned again. A call ends as `NotAdmitted`. A
    -- send proceeds. An absent id can still be spawned later, but this call
    -- does not sit on it.
    if isCall then
      setActor w sender (finishCall (issueCall (w.st sender)) k .notAdmitted)
    else
      setActor w sender (proceed (w.st sender) k)
  else
    let senderA := chargeSender (w.st sender) (tname dst)
    -- A call consumes one id. The sender remembers it for the reply match.
    let senderA := if isCall then issueCall senderA else senderA
    let room := decide (target.parked = []) && decide (target.box.length < cap)
    let same := decide (sender = dst)
    -- The id belongs to the actor that stores the message. A self-send stores it
    -- on the sender after the charge, which does not move `nextMid`. A call
    -- carries the id `issueCall` just stamped, and `performReply` matches it.
    let host := if same then senderA else target
    let issued : Msg :=
      { msg with mid := host.nextMid, callId := (if isCall then some senderA.waitId else msg.callId) }
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

/-- Reply resumes the caller only when that caller is awaiting *this* sender
and the callee's owed id is the caller's wait id. Delivery stored that id from
the message's `callId`. A late reply for a timed-out id does not match. -/
def performReply (w : World) (sender : InstId) (k : Cont) : World :=
  let k' := afterHead k
  match k.replyTo with
  | none => setActor w sender (proceed (w.st sender) k')
  | some caller =>
    match (w.st caller).phase with
    | .awaitReply dst ck =>
      if dst = sender && (w.st sender).oweId = some (w.st caller).waitId then
        let w := setActor w caller (finishCall (w.st caller) ck .reply)
        setActor w sender (proceed (w.st sender) k')
      else
        setActor w sender (proceed (w.st sender) k')
    | _ => setActor w sender (proceed (w.st sender) k')

/-- Every priority message, including a tombstone, consumes the lane budget. -/
def prioLoad (ms : List Msg) : Nat := ms.length

/-- One wake per label on the priority lane. The caller enqueues only when the
label is not already pending. Wakes are not bulk occupancy and are not charged. -/
def upsertPrio (prio : List Msg) (m : Msg) : List Msg :=
  if prio.any (fun p => p.label == m.label) then prio else prio ++ [m]

/-- A permanent core's `terminate`, and a priority lane with no room left. Every
live or shutting-down actor on the roster dies in this step, in the crashed
phase. Mail stays queued: the host is dead before anything dequeues it, and a
crashed world takes no further step. -/
def crashActor (a : Actor) : Actor :=
  if a.life == .alive || a.life == .shuttingDown then
    { a with life := .dead, phase := .crashed }
  else a

def crashWorld (w : World) : World :=
  { w with st := fun i => if decide (i ∈ w.roster) then crashActor (w.st i) else w.st i }

/-- Append one priority message. A full lane crashes the roster: the message is
not added, not dropped, and the sender does not block. -/
def offerPrio (D : Description) (w : World) (host : InstId) (msg : Msg) : World :=
  let a := w.st host
  if decide (prioLoad a.prio >= capPrio D w.N host) then crashWorld w
  else setActor w host { a with prio := a.prio ++ [msg], nextMid := a.nextMid + 1 }

def tryWake (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId) : World :=
  let target := w.st dstId
  -- A cell wake is a superseding write: it is not a reliable delivery.
  -- A label already pending is not a new enqueue. A new wake on a full lane crashes.
  let wake : Msg :=
    { label := label, sender := writer, callFrom := none, reliable := false, mid := target.nextMid }
  if target.life != .alive || target.prio.any (fun p => p.label == label) then w
  else offerPrio D w dstId wake

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

/-- Mailbox with `dead`'s messages removed. Tokens are unchanged. -/
def stripSender (dead : InstId) (a : Actor) : Actor :=
  { a with box := a.box.filter fun m => m.sender != dead
           parked := a.parked.filter fun p => p.sender != dead }

/-- Return `n` slots for mailbox template `name`. -/
def addTokens (a : Actor) (name : String) (n : Nat) : Actor :=
  { a with tokens := fun d => if d == name then a.tokens d + n else a.tokens d }

/-- How many of `dead`'s messages sit on this actor. -/
def outboundCount (dead : InstId) (a : Actor) : Nat :=
  (a.box.filter fun m => m.sender == dead).length +
    (a.parked.filter fun p => p.sender == dead).length

/-- Drop `dead`'s mail on `host` and return the slots to `dead`. `dead`'s own
mailbox is left alone: its inbound mail is refunded to the senders separately.
A host that holds nothing of `dead` is skipped, and the skip is silent. -/
def forgetHost (w : World) (dead host : InstId) : World :=
  if host == dead then w
  else if outboundCount dead (w.st host) == 0 then w
  else
    let cleared := setActor w host (stripSender dead (w.st host))
    setActor cleared dead (addTokens (cleared.st dead) (tname host) (outboundCount dead (w.st host)))

/-- Drop `dead`'s outbound mail on the roster and return those slots to `dead`.
Inbound mail on `dead` itself is not touched. -/
def forgetSender (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w host => forgetHost w dead host) w

/-- A live actor waiting on `dead` is failed only when the wait is a blocking
send. A parked call and an `awaitReply` stay: their deadline returns
`NotAdmitted` or `TimedOut`. -/
def failWaiter (w : World) (dead : InstId) (i : InstId) : World :=
  if (w.st i).life != .alive then w
  else
    match (w.st i).phase with
    | .parked d false k =>
      if d == dead then setActor w i (proceed (w.st i) k) else w
    | _ => w

def failWaiters (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w i => failWaiter w dead i) w

/-- Kill one member: refund what its mailbox held, fail whoever was waiting on
it, return the slots for its outbound mail, and leave it dead with an empty
mailbox. -/
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

/-- Kill every live member of subtree `sub` at `key`. Not a step. A stage's own
`terminate` does not call this: siblings die only when their parent terminates. -/
def killSubtree (w : World) (D : Description) (sub : String) (key : Nat) : World :=
  killMembers w D sub key

/-- The instance that supervises `child`. A multiplicity-one supervisor is the
core of that name. A per-peer supervisor is the same subtree at the child's key. -/
def supervisorInst (D : Description) (child : InstId) (supName : String) : Option InstId :=
  match templateOf D supName with
  | none => none
  | some sup =>
    match sup.multiplicity with
    | .one => some (.core supName)
    | .perPeer =>
      match child with
      | .core _ => none
      | .peer _ k =>
        match templateOf D (tname child) with
        | none => none
        | some t =>
          if t.subtree != "" && t.subtree == sup.subtree then some (.peer supName k) else none

/-- The supervisor `id`'s template names, if it names one. -/
def supervisorOf (D : Description) (id : InstId) : Option InstId :=
  match templateOf D (tname id) with
  | none => none
  | some t => if t.supervisor == "" then none else supervisorInst D id t.supervisor

/-- `child` is a direct descendant of `parent`. A per-peer member may supervise
other members of its own subtree. An actor is not its own child. -/
def isChild (D : Description) (parent child : InstId) : Bool :=
  match supervisorOf D child with
  | some p => p == parent && child != parent
  | none => false

/-- A per-peer stage supervises the per-peer child that names it, at the same
subtree key. The child is not required to be on the roster yet: the wiring is
what makes the parent the supervisor. -/
theorem isChild_peer (D : Description) (supName childName : String) (k : Nat)
    (sup child : Template) (hsup : templateOf D supName = some sup)
    (hchild : templateOf D childName = some child) (hm : sup.multiplicity = .perPeer)
    (hsub : child.subtree ≠ "") (hsame : child.subtree = sup.subtree)
    (hname : child.supervisor = supName) (hdiff : childName ≠ supName)
    (hnamed : supName ≠ "") :
    isChild D (.peer supName k) (.peer childName k) = true := by
  unfold isChild supervisorOf supervisorInst
  simp [tname, hchild, hsup, hm, hname, hsame, hsub, hdiff, hnamed, bne, beq_iff_eq]
  have hsupSub : sup.subtree ≠ "" := by simpa [hsame] using hsub
  by_cases hempty : sup.subtree = ""
  · exact absurd hempty hsupSub
  · rw [if_neg hempty]
    simp [hdiff, beq_iff_eq]

/-- Some live actor names `id` as its supervisor. -/
def hasChild (D : Description) (w : World) (id : InstId) : Bool :=
  w.roster.any fun c => isChild D id c && (w.st c).life == .alive

/-- The tombstone label the parent wired for this child template. -/
def tombstoneLabel (D : Description) (child : InstId) : String :=
  match templateOf D (tname child) with
  | some t => t.tombstone
  | none => ""

/-- One tombstone per child. The label is the child template's wired label, so
two templates do not share a message and two instances of one template do not
collapse into one wake. -/
def tombstoneMsg (D : Description) (parent : Actor) (child : InstId) : Msg :=
  { label := tombstoneLabel D child, sender := child, callFrom := none,
    reliable := true, mid := parent.nextMid, tombstone := true }

/-- Hand the parent the child's tombstone. A missing parent is not a delivery:
the template named no supervisor. A parent that is not alive, a child with no
wired label, or a priority lane with no room left crashes the roster. The
tombstone counts toward that lane's budget. -/
def enqueueTombstone (D : Description) (w : World) (child : InstId) : World :=
  match supervisorOf D child with
  | none => w
  | some parent =>
    let p := w.st parent
    let msg := tombstoneMsg D p child
    if p.life != .alive || msg.label == "" ||
        decide (prioLoad p.prio >= capPrio D w.N parent) then
      crashWorld w
    else
      setActor w parent
        { p with prio := p.prio ++ [msg], nextMid := p.nextMid + 1 }

/-- Drop parked entries whose sender is `dead` on every other host, and return
those slots to `dead`. The host's own mailbox is left alone. A host that holds
nothing of `dead` is skipped. -/
def releaseOutbound (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w host =>
    if host == dead then w
    else
      let dropped := (w.st host).parked.filter fun p => p.sender == dead
      if dropped.isEmpty then w
      else
        let w := setActor w host
          { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
        setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) w

/-- The world a lone terminable's seal leaves: refund the mailbox, refund every
parked entry on another host whose sender is this actor, install the dead actor,
and resume every non-call parked sender. A parked call stays for its deadline.
Nothing here clears a sibling's mailbox. -/
def releaseWorld (D : Description) (w : World) (id : InstId) (a : Actor) : World :=
  let w := readCells D w id
  let w := refundMsgs w (tname id) a.box
  let w := refundParked w (tname id) a.parked
  let w := releaseOutbound w id
  let base := w.st id
  let dead : Actor :=
    { base with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  releaseParked (setActor w id dead) id a.parked

/-- A blocked send from `dead` is moved into the target's box. The target stays
alive and still has to handle it. The dead sender is no longer parked there. -/
def admitHost (w : World) (dead host : InstId) : World :=
  if host == dead then w
  else if ((w.st host).parked.filter fun p => p.sender == dead).isEmpty then w
  else
    setActor w host
      { (w.st host) with
        box := (w.st host).box ++
          ((w.st host).parked.filter fun p => p.sender == dead).map (·.msg),
        parked := (w.st host).parked.filter fun p => p.sender != dead }

/-- Admit every blocked send `dead` still has on the roster. -/
def admitDead (w : World) (dead : InstId) : World :=
  w.roster.foldl (fun w host => admitHost w dead host) w

/-- `releaseWorld`, then resume blocking sends still waiting on `id`, then admit
`id`'s own blocked sends. Parked calls and `awaitReply` callers stay for their
deadline. -/
def abortActor (D : Description) (w : World) (id : InstId) (a : Actor) : World :=
  admitDead (failWaiters (releaseWorld D w id a) id) id

/-- A declared terminable template. Inlined here so the descendant fold can see it. -/
def childTerminable (D : Description) (child : InstId) : Bool :=
  match templateOf D (tname child) with
  | some t => t.terminable
  | none => false

/-- Abort the live terminable descendants of `parent`, children before grandchildren.
`fuel` is the roster length, so a chain cannot outrun the fold. A non-terminable
template is not a descendant the parent may abort: it can be a compat role. -/
def abortDesc (fuel : Nat) (D : Description) (w : World) (parent : InstId) : World :=
  match fuel with
  | 0 => w
  | fuel + 1 =>
    w.roster.foldl (fun w child =>
      if isChild D parent child && (w.st child).life == .alive &&
          childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w) w

/-- Enter shutting-down. Mail stays until `releaseWorld` seals the actor.
A life that is not alive is left alone. -/
def markShutdown (w : World) (id : InstId) : World :=
  if (w.st id).life == .alive then
    -- The phase stops here. Mail stays until the seal, and the actor accepts nothing.
    setActor w id { (w.st id) with life := .shuttingDown, phase := .idle }
  else w

/-- Mark `id` shutting down and hand its parent the tombstone. The parent
answers later, in its own step. -/
def shutdownActor (D : Description) (w : World) (id : InstId) : World :=
  enqueueTombstone D (markShutdown w id) id

/-- Mark the live terminable descendants of `parent` shutting down, children
before grandchildren. They stop accepting mail in this step. Each seals
itself on a later `exec`. -/
def shutdownDesc (fuel : Nat) (D : Description) (w : World) (parent : InstId) : World :=
  match fuel with
  | 0 => w
  | fuel + 1 =>
    w.roster.foldl (fun w child =>
      if isChild D parent child && (w.st child).life == .alive &&
          childTerminable D child then
        let w := shutdownDesc fuel D w child
        shutdownActor D w child
      else w) w

/-- A permanent core has crashed the roster. The world is terminal. Invariants
about live actors are not required of it. A priority-lane overflow, which
leaves the actor alive, is not this state. -/
def WorldCrashed (w : World) : Prop :=
  ∃ id, id ∈ w.roster ∧ (w.st id).life = .dead ∧ (w.st id).phase = .crashed

/-- Mark `id` and every descendant shutting down. Mail stays. Terminable and
permanent children are both marked: a parent abort is not the voluntary
`terminate` of a terminable actor. -/
def markTree (fuel : Nat) (D : Description) (w : World) (id : InstId) : World :=
  match fuel with
  | 0 => w
  | fuel + 1 =>
    let w := markShutdown w id
    w.roster.foldl (fun w child =>
      if isChild D id child then markTree fuel D w child else w) w

/-- A stage in the supervision tree terminates. Every descendant, terminable or
not, begins shutting down, and one tombstone is placed on the immediate
supervisor's priority lane. The supervisor may itself be per-peer. This step
does not terminate it: its own transition decides whether to terminate, which
is how the failure bubbles up. A sibling is not a descendant, and nothing here
clears a sibling's mail. -/
def terminateStage (D : Description) (w : World) (id : InstId) (a : Actor) : World :=
  let _committed := a
  let w := markTree w.roster.length D w id
  enqueueTombstone D w id

/-- The parent's abort. Every live child, terminable or not, and that child's
descendants begin shutting down. Each direct child leaves one tombstone on the
parent. A sibling is not a child, and this step does not touch a sibling's mail. -/
def abortChildren (D : Description) (w : World) (parent : InstId) : World :=
  w.roster.foldl (fun w child =>
    if isChild D parent child && (w.st child).life == .alive then
      let w := markTree w.roster.length D w child
      enqueueTombstone D w child
    else w) w

/-- A per-peer parent births one absent child at its own key. The child template
must name this parent, so `isChild` holds for the peer parent. A core has no
such effect. A dead id is not reused, and a second copy of a live child is not
created. There is no flat `N` cap: the child's population is the parent's. -/
def spawnChild (I : Impl) (w : World) (parent : InstId) (child : String) : Option World :=
  match parent with
  | .core _ => none
  | .peer _ k =>
    match templateOf I.desc child with
    | none => none
    | some t =>
      let id := InstId.peer child k
      if t.multiplicity == .perPeer && isChild I.desc parent id && (w.st id).life == .absent then
        let born := withTokens I.desc child
          { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
            tokens := fun _ => 0 }
        let w := { w with roster := w.roster ++ [id] }
        some (readCells I.desc (setActor w id born) id)
      else none

/-- Run one effect. An actor that is not alive does not run: while it is shutting
down the only enabled step is the seal in `execHead`. -/
def execRun (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) : World :=
  if a.life == .alive then
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
      | .trySend dst label hint onFull onGone =>
        let kFull := { k' with rest := onFull }
        let kGone := { k' with rest := onGone }
        match route w I.desc id dst with
        | none => setActor (noteStale w id dst) id (proceed a kGone)
        | some dstId =>
          let target := w.st dstId
          let cap := capBulk I.desc w.N dstId
          if target.life == .alive && target.parked = [] && target.box.length < cap then
            -- Admitted try-drop: a copy that lands is not a reliable delivery.
            let msg : Msg := { label := label, sender := id, callFrom := none, reliable := false }
            enqueueOrPark w I.desc id dstId msg false k'
          else if target.life == .alive then
            setActor w id (proceed a kFull)
          else
            setActor w id (proceed a kGone)
      | .call dst label hint onNotAdmitted onTimedOut =>
        let kWait := { k' with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
        match resolveId I.desc id dst with
        | none =>
          -- No such role: the call is not admitted, on its own continuation.
          setActor (noteStale w id dst) id (finishCall (issueCall a) kWait .notAdmitted)
        | some dstId =>
          let msg : Msg := { label := label, sender := id, callFrom := some id }
          enqueueOrPark w I.desc id dstId msg true kWait
      | .reply => performReply w id k
      | .selfSchedule label =>
        let cap := capPrio I.desc w.N id
        let msg : Msg :=
          { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
        -- Re-arming a label already queued does not grow the lane. A new label
        -- past the lane capacity crashes the roster. The lane does not grow,
        -- block, or drop the message.
        if a.prio.any (fun p => p.label == label) then
          setActor w id (proceed a k')
        else if prioLoad a.prio < cap then
          setActor w id (proceed { a with prio := upsertPrio a.prio msg, nextMid := a.nextMid + 1 } k')
        else
          crashWorld w
      | .cell dst label value =>
        let previous := w.cell dst label
        let written := max previous.value value
        let w := setCell w dst label { value := written, dirty := true }
        let w := setActor w id (proceed (w.st id) k')
        if previous.dirty then w
        else wakeReaders I.desc w dst label id
      | .internal => setActor w id { a with phase := .awaitEffect k' }
      | .peer onTimeout =>
        setActor w id { a with phase := .awaitPeer { k' with onTimeout := onTimeout } }
      | .abort => abortChildren I.desc w id
      | .spawn child =>
        match spawnChild I w id child with
        | some w' => setActor w' id (proceed (w'.st id) k')
        | none => crashWorld w
      | .terminate =>
        -- A permanent core crashes the whole roster. Any stage in a supervision
        -- tree may terminate, terminable or not: every descendant shuts down and
        -- the immediate supervisor receives one tombstone. A lone terminable with
        -- no child and no parked call shuts only itself down. Anything else,
        -- including a missing template, crashes the roster. Siblings are left alone.
        match templateOf I.desc (tname id) with
        | some t =>
          if t.multiplicity == .one && !t.terminable then
            crashWorld w
          else if t.multiplicity == .perPeer && t.subtree != "" then
            terminateStage I.desc w id a
          else if t.terminable && t.subtree == "" && !hasParkedCall a.parked &&
              !(hasChild I.desc w id) then
            shutdownActor I.desc w id
          else if t.terminable && t.subtree == "" && !hasParkedCall a.parked &&
              hasChild I.desc w id then
            terminateStage I.desc w id a
          else crashWorld w
        | none => crashWorld w
  else w

/-- What one `terminate` effect does when the actor is alive.
`fall` is every terminate that does not shut a terminable actor down: a missing
template, a permanent core, or a lone actor that still has a parked call. The
roster crashes. `lone` marks one childless actor shutting down. `cascade` marks
that actor's descendants shutting down and notifies its parent. -/
inductive TermStep (I : Impl) (w : World) (id : InstId) (a : Actor) : World → Prop where
  | fall : TermStep I w id a (crashWorld w)
  | crash (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.multiplicity = .one →
      t.terminable = false →
      TermStep I w id a (crashWorld w)
  | lone (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.subtree = "" →
      t.terminable = true →
      hasParkedCall a.parked = false →
      hasChild I.desc w id = false →
      TermStep I w id a (shutdownActor I.desc w id)
  | tree (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.multiplicity = .perPeer →
      t.subtree ≠ "" →
      TermStep I w id a (terminateStage I.desc w id a)
  | cascade (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.subtree = "" →
      t.terminable = true →
      hasParkedCall a.parked = false →
      hasChild I.desc w id = true →
      TermStep I w id a (terminateStage I.desc w id a)

/-- Classify `terminate`. A member commits even when a call is parked.
A permanent core, and every other fall-through, crashes the roster. -/
theorem exec_term_step (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hlive : a.life = .alive) (hk : ∃ tail, k.rest = .terminate :: tail) :
    TermStep I w id a (execRun I w id a k) := by
  have hgo : (a.life == .alive) = true := by simpa [beq_iff_eq] using hlive
  rcases hk with ⟨tail, hk⟩
  cases ht : templateOf I.desc (tname id) with
  | none =>
    simp [execRun, hgo, hk, ht]
    exact TermStep.fall
  | some t =>
    simp only [execRun, hgo, hk, ht, ite_true]
    by_cases hcrash : (t.multiplicity == .one && !t.terminable) = true
    · simp [hcrash]
      have hparts := (Bool.and_eq_true _ _).mp hcrash
      have hone : t.multiplicity = .one := by
        cases hm : t.multiplicity with
        | one => rfl
        | perPeer =>
          simp [hm, show (Multiplicity.perPeer == Multiplicity.one) = false from rfl] at hparts
      have hnt : t.terminable = false := by
        have hn : (!t.terminable) = true := hparts.2
        cases htm : t.terminable with
        | false => rfl
        | true => simp [htm] at hn
      exact TermStep.crash t ht hone hnt
    · rw [ite_eq_right hcrash]
      by_cases htree : (t.multiplicity == .perPeer && t.subtree != "") = true
      · simp only [htree, ite_true]
        have hparts := (Bool.and_eq_true _ _).mp htree
        have hper : t.multiplicity = .perPeer := by
          cases hm : t.multiplicity with
          | perPeer => rfl
          | one =>
            simp [hm, show (Multiplicity.one == Multiplicity.perPeer) = false from rfl] at hparts
        have hsub : t.subtree ≠ "" := by
          have hb : (t.subtree != "") = true := hparts.2
          simpa [bne, beq_iff_eq] using hb
        exact TermStep.tree t ht hper hsub
      · rw [ite_eq_right htree]
        by_cases hlone : (t.terminable && t.subtree == "" && !hasParkedCall a.parked &&
            !(hasChild I.desc w id)) = true
        · simp only [hlone, ite_true]
          simp [Bool.and_eq_true] at hlone
          rcases hlone with ⟨⟨⟨htm, hsubB⟩, hpkB⟩, hchB⟩
          have hsub : t.subtree = "" := by simpa [beq_iff_eq] using hsubB
          have hpk : hasParkedCall a.parked = false := by
            cases hp : hasParkedCall a.parked with
            | false => rfl
            | true => simp [hp] at hpkB
          have hch : hasChild I.desc w id = false := by
            cases hc : hasChild I.desc w id with
            | false => rfl
            | true => simp [hc] at hchB
          exact TermStep.lone t ht hsub htm hpk hch
        · rw [ite_eq_right hlone]
          by_cases hkids : (t.terminable && t.subtree == "" && !hasParkedCall a.parked &&
              hasChild I.desc w id) = true
          · simp only [hkids, ite_true]
            simp [Bool.and_eq_true] at hkids
            rcases hkids with ⟨⟨⟨htm, hsubB⟩, hpkB⟩, hch⟩
            have hsub : t.subtree = "" := by simpa [beq_iff_eq] using hsubB
            have hpk : hasParkedCall a.parked = false := by
              cases hp : hasParkedCall a.parked with
              | false => rfl
              | true => simp [hp] at hpkB
            exact TermStep.cascade t ht hsub htm hpk hch
          · rw [ite_eq_right hkids]
            exact TermStep.fall

/-- An alive `terminate` crashes the roster, shuts one childless actor down, or
aborts every descendant and notifies the immediate supervisor. A stage in a
supervision tree does not have to be marked terminable. -/
theorem execRun_terminate (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hlive : a.life = .alive) (hk : ∃ tail, k.rest = .terminate :: tail) :
    execRun I w id a k = crashWorld w ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.subtree = "" ∧ t.terminable = true ∧
        hasParkedCall a.parked = false ∧ hasChild I.desc w id = false ∧
        execRun I w id a k = shutdownActor I.desc w id) ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = .perPeer ∧ t.subtree ≠ "" ∧
        execRun I w id a k = terminateStage I.desc w id a) ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.subtree = "" ∧ t.terminable = true ∧
        hasParkedCall a.parked = false ∧ hasChild I.desc w id = true ∧
        execRun I w id a k = terminateStage I.desc w id a) := by
  have hstep := exec_term_step I w id a k hlive hk
  generalize hw : execRun I w id a k = wR at hstep
  cases hstep with
  | fall => exact Or.inl rfl
  | crash _ _ _ _ => exact Or.inl rfl
  | lone t ht hsub htm hpk hch =>
    exact Or.inr (Or.inl ⟨t, ht, hsub, htm, hpk, hch, rfl⟩)
  | tree t ht hm hsub =>
    exact Or.inr (Or.inr (Or.inl ⟨t, ht, hm, hsub, rfl⟩))
  | cascade t ht hsub htm hpk hch =>
    exact Or.inr (Or.inr (Or.inr ⟨t, ht, hsub, htm, hpk, hch, rfl⟩))

/-- An actor that is shutting down seals on `exec`: the mailbox is cleared and
the life becomes `dead`. A live actor runs. Anyone else has no `exec`. -/
def execHead (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life == .shuttingDown then some (releaseWorld I.desc w id a)
  else if a.life ≠ .alive then none
  else
    match a.phase with
    | .run k => some (execRun I w id a k)
    | _ => none

/-- The template flag. The step relation does not consult it: every external
wait ends by `finish`, which is a normal timeout. -/
def peerUntimed (D : Description) (id : InstId) : Bool :=
  match templateOf D (tname id) with
  | some t => t.untimedPeer
  | none => false

/-- Every peer wait can `finish`. The timeout is a normal result. -/
def peerFinishable (_D : Description) (_id : InstId) : Bool := true

/-- No peer wait is an external stall. `finish` is enabled on every `awaitPeer`. -/
def PurePeerEnd (_D : Description) (_w : World) (_id : InstId) : Prop := False

theorem peerFinishable_true (D : Description) (id : InstId) : peerFinishable D id = true := rfl

theorem finishable_of_timed (D : Description) (id : InstId) (_hu : peerUntimed D id = false) :
    peerFinishable D id = true := rfl

theorem untimed_of_silent (D : Description) (id : InstId) (hf : peerFinishable D id = false) :
    peerUntimed D id = true := by
  simp [peerFinishable] at hf

theorem pure_of_silent (D : Description) (id : InstId) (hf : peerFinishable D id = false) :
    templatePure D (tname id) = true := by
  simp [peerFinishable] at hf

/-- Drop `callFrom` on messages from `caller`. The bytes stay queued. -/
def detachMsg (caller : InstId) (m : Msg) : Msg :=
  if m.callFrom == some caller then { m with callFrom := none } else m

def detachBox (a : Actor) (caller : InstId) : Actor :=
  { a with box := a.box.map (detachMsg caller) }

/-- Forget a reply obligation for `caller`'s call `cid`. The effect list is unchanged. -/
def clearReplyCont (caller : InstId) (k : Cont) : Cont :=
  if k.replyTo == some caller then { k with replyTo := none } else k

def clearReplyPhase (caller : InstId) (ph : Phase) : Phase :=
  match ph with
  | .run k => .run (clearReplyCont caller k)
  | .parked d c k => .parked d c (clearReplyCont caller k)
  | .awaitReply d k => .awaitReply d (clearReplyCont caller k)
  | .awaitEffect k => .awaitEffect (clearReplyCont caller k)
  | .awaitPeer k => .awaitPeer (clearReplyCont caller k)
  | other => other

def detachReply (a : Actor) (caller : InstId) (cid : Nat) : Actor :=
  if a.oweId == some cid then { a with phase := clearReplyPhase caller a.phase } else a

theorem clearReplyCont_keeps (caller : InstId) (k : Cont) :
    (clearReplyCont caller k).rest = k.rest ∧ (clearReplyCont caller k).toState = k.toState := by
  unfold clearReplyCont
  split <;> simp

/-- Scrubbing a reply changes neither the queue nor the life of the callee. -/
theorem detachHost_rest (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).typestate = a.typestate ∧
      (detachReply (detachBox a caller) caller cid).life = a.life ∧
      (detachReply (detachBox a caller) caller cid).parked = a.parked := by
  unfold detachReply detachBox
  split <;> simp

/-- A parked phase stays parked on the same target. Only the reply obligation moves. -/
theorem detachHost_park (a : Actor) (caller : InstId) (cid : Nat) (dst : InstId) (c : Bool) :
    (∃ k, (detachReply (detachBox a caller) caller cid).phase = .parked dst c k) ↔
      (∃ k, a.phase = .parked dst c k) := by
  unfold detachReply
  split
  · cases hph : a.phase with
    | parked _ _ _ =>
      simp [detachBox, clearReplyPhase, hph]
    | idle => simp [detachBox, clearReplyPhase, hph]
    | run _ => simp [detachBox, clearReplyPhase, hph]
    | awaitReply _ _ => simp [detachBox, clearReplyPhase, hph]
    | awaitEffect _ => simp [detachBox, clearReplyPhase, hph]
    | awaitPeer _ => simp [detachBox, clearReplyPhase, hph]
    | crashed => simp [detachBox, clearReplyPhase, hph]
  · simp [detachBox]

/-- Remove `caller`'s parked calls on `dst` and return one token per removed entry.
An entry a dead callee already refunded is absent, so this credits nothing. -/
def refundParkedCall (w : World) (caller dst : InstId) : World :=
  let ps := (w.st dst).parked
  let drop := ps.filter fun p => p.sender == caller && p.isCall
  let keep := ps.filter fun p => !(p.sender == caller && p.isCall)
  if drop.isEmpty then w
  else
    let w := setActor w dst { (w.st dst) with parked := keep }
    drop.foldl (fun w _ => creditSender w (tname dst) caller) w

theorem filter_drop_empty {α : Type} (p : α → Bool) (l : List α)
    (h : (l.filter p).isEmpty = true) : l.filter (fun x => !p x) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a with
    | false =>
      have htail : (l.filter p).isEmpty = true := by
        simpa [List.filter, hpa] using h
      simpa [List.filter, hpa, ih htail]
    | true =>
      simp [List.filter, hpa] at h

/-- Refunding a parked call keeps every phase, life, and typestate. The target's
parked list loses that caller's call entries and every other queue stays. -/
theorem refundCall_fields (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).phase = (w.st i).phase ∧
      ((refundParkedCall w caller dst).st i).life = (w.st i).life ∧
      ((refundParkedCall w caller dst).st i).typestate = (w.st i).typestate ∧
      ((refundParkedCall w caller dst).st i).parked =
        (if i = dst then
          (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall)
        else (w.st i).parked) := by
  unfold refundParkedCall
  dsimp only
  let pred := fun p : Parked => p.sender == caller && p.isCall
  let keep := (w.st dst).parked.filter fun p => !pred p
  split
  · next hempty =>
    have hkeep := filter_drop_empty pred (w.st dst).parked hempty
    refine ⟨rfl, rfl, rfl, ?_⟩
    by_cases hi : i = dst
    · rw [hi, if_pos rfl]
      have hpred : (fun p : Parked => !(p.sender == caller && p.isCall)) = (fun p => !pred p) := by
        funext p
        simp [pred, Bool.not_and]
      rw [hpred, hkeep]
    · simp [hi]
  · next hgo =>
    let base := setActor w dst { (w.st dst) with parked := keep }
    have hbase : (base.st i).phase = (w.st i).phase ∧ (base.st i).life = (w.st i).life ∧
        (base.st i).typestate = (w.st i).typestate ∧
        (base.st i).parked = (if i = dst then keep else (w.st i).parked) := by
      by_cases hi : i = dst
      · simp [base, hi, setActor_self]
      · simp [base, setActor_other w dst i _ hi, hi]
    have hfold : ∀ (ps : List Parked) (w0 : World),
        (w0.st i).phase = (w.st i).phase → (w0.st i).life = (w.st i).life →
        (w0.st i).typestate = (w.st i).typestate →
        (w0.st i).parked = (if i = dst then keep else (w.st i).parked) →
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).phase = (w.st i).phase) ∧
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).life = (w.st i).life) ∧
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).typestate =
          (w.st i).typestate) ∧
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st i).parked =
          (if i = dst then keep else (w.st i).parked)) := by
      intro ps
      induction ps with
      | nil => intro w0 hp hl ht hk; simpa using ⟨hp, hl, ht, hk⟩
      | cons p ps ih =>
        intro w0 hp hl ht hk
        simp only [List.foldl_cons]
        have hcredit : ((creditSender w0 (tname dst) caller).st i).phase = (w0.st i).phase ∧
            ((creditSender w0 (tname dst) caller).st i).life = (w0.st i).life ∧
            ((creditSender w0 (tname dst) caller).st i).parked = (w0.st i).parked := by
          by_cases hwho : i = caller
          · simp [creditSender, hwho, setActor, bumpToken]
          · simp [creditSender, setActor, hwho]
        exact ih (creditSender w0 (tname dst) caller) (hcredit.1.trans hp) (hcredit.2.1.trans hl)
          (by
            by_cases hwho : i = caller
            · rw [hwho] at ht ⊢
              simp [creditSender, setActor, bumpToken]
              exact ht
            · rw [creditSender, setActor_other w0 caller i _ hwho]
              exact ht) (hcredit.2.2.trans hk)
    simpa [base, keep, pred] using hfold ((w.st dst).parked.filter pred) base hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2

/-- The deadline of a call. Always enabled from `.awaitReply` (`TimedOut`, the
request stays queued) and from a parked call (`NotAdmitted`, the parked entry
is removed and its token returned). -/
def callTimeout (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life != .alive then none
  else
    match a.phase with
    | .awaitReply dst k =>
      let cid := a.waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w := setActor w dst host
      some (setActor w id (finishCall (w.st id) k .timedOut))
    | .parked dst true k =>
      let w := refundParkedCall w id dst
      some (setActor w id (finishCall (w.st id) k .notAdmitted))
    | .awaitPeer k =>
      some (setActor w id (proceed (w.st id) { k with rest := k.onTimeout }))
    | _ => none

/-- Internal effects and the data result of a peer wait complete as an ordinary
step. The peer timeout is `callTimeout`, on `onTimeout`. A shutting-down or
dead actor does not finish; its next step is the seal, or nothing. -/
def finishWait (I : Impl) (w : World) (id : InstId) : Option World :=
  if (w.st id).life ≠ .alive then none
  else
    match (w.st id).phase with
    | .awaitEffect k => some (setActor w id (proceed (w.st id) k))
    | .awaitPeer k => some (setActor w id (proceed (w.st id) k))
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
  | .trySend d _ _ _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | .call d _ _ _ _ :: es => (if d == dst then 1 else 0) + sendsTo dst es
  | _ :: es => sendsTo dst es

/-- Bulk sends still in the continuation, counted toward the token floor. -/
def pending (a : Actor) (dst : String) : Nat := sendsTo dst (contRest a.phase)

/-- Idle, parked, waiting, or running. A message for a running actor waits in
the box until the continuation finishes. A crashed actor does not take ingress. -/
def ingressOpen : Phase → Bool
  | .idle => true
  | .parked _ _ _ => true
  | .awaitReply _ _ => true
  | .awaitEffect _ => true
  | .awaitPeer _ => true
  | .run _ => true
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

/-- A terminable role with an empty subtree. It has no siblings, so it stays mute. -/
def loneTerminableName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.terminable = true ∧ t.subtree = ""

/-- A terminable role that dies with the rest of a named subtree. -/
def subtreeMemberName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.terminable = true ∧ t.subtree ≠ ""

/-- `true` when `name` is terminable and belongs to no subtree. -/
def loneTerminableB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.terminable && t.subtree == ""
  | none => false

/-- A core that is not part of any subtree: one instance, and not terminable. -/
def permanentCore (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.multiplicity == .one && !t.terminable
  | none => false

/-- `true` when `name` is a per-peer role, so a kill of its key removes it. -/
def perPeerB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.multiplicity == .perPeer
  | none => false

/-- A per-peer member talks only to a per-peer role of its own subtree.
A permanent core is not per-peer, so a call to one is not enabled. A lone
terminable is not a subtree member and is not covered here: it stays mute. -/
abbrev subtreeTalk (D : Description) (src dst : String) : Bool :=
  sameSubtree D src dst && perPeerB D dst

mutual
/-- One effect of a subtree member. A send, try-send, or call stays inside
`subtreeTalk`. `selfSchedule` is the same actor. -/
def memberEffectOk (D : Description) (src : String) : Eff → Bool
  | .send dst _ _ => subtreeTalk D src dst
  | .trySend dst _ _ onFull onGone =>
    subtreeTalk D src dst && memberProgramOk D src onFull && memberProgramOk D src onGone
  | .call dst _ _ onNotAdmitted onTimedOut =>
    subtreeTalk D src dst && memberProgramOk D src onNotAdmitted &&
      memberProgramOk D src onTimedOut
  | .peer onTimeout => memberProgramOk D src onTimeout
  | .selfSchedule _ => true
  | .abort => true
  | .spawn child => sameSubtree D src child && perPeerB D src && perPeerB D child
  | _ => true

/-- Every effect of a subtree member's program, and every outcome continuation
of those effects, stays in scope. -/
def memberProgramOk (D : Description) (src : String) : List Eff → Bool
  | [] => true
  | e :: es => memberEffectOk D src e && memberProgramOk D src es
end

theorem memberProgram_tail (D : Description) (src : String) (e : Eff) (es : List Eff)
    (h : memberProgramOk D src (e :: es) = true) : memberProgramOk D src es = true := by
  simp [memberProgramOk, Bool.and_eq_true] at h
  exact h.2

theorem memberProgram_head (D : Description) (src : String) (e : Eff) (es : List Eff)
    (h : memberProgramOk D src (e :: es) = true) : memberEffectOk D src e = true := by
  simp [memberProgramOk, Bool.and_eq_true] at h
  exact h.1

/-- Where a subtree member's message may sit: a same-key actor of that subtree. -/
def memberHere (D : Description) (sender host : InstId) (_callFrom : Option InstId) : Prop :=
  subtreeMemberName D (tname sender) →
    sameSubtree D (tname sender) (tname host) = true ∧ memberKey sender = memberKey host

/-- Every queued message from a subtree member sits on a same-key member of it. -/
def MailHere (D : Description) (w : World) : Prop :=
  ∀ host,
    (∀ m ∈ (w.st host).box, memberHere D m.sender host m.callFrom) ∧
    (∀ p ∈ (w.st host).parked, memberHere D p.sender host p.msg.callFrom)

/-- Environment delivery into a live ingress stage. The actor may be idle, parked,
waiting, or running; a crashed actor is refused. It charges one self-slot and
appends a bulk message when the mailbox is under capacity and the target still
has a token above the typestate floor plus the sends still in its continuation.
A full mailbox, a dead target, a lone terminable, or a spent budget makes the
action disabled, so the message is never dropped. A subtree member may receive
ingress. The allowance is `ingressLegal` evaluated at `w.N`. -/
def receiveIngress (I : Impl) (w : World) (dst : InstId) (label : String) : Option World :=
  let a := w.st dst
  let cap := capBulk I.desc w.N dst
  let floor := budget I.desc (tname dst) (tname dst) - debt I.desc (tname dst) a.typestate (tname dst)
  let need := floor + pending a (tname dst) + 1
  if a.life ≠ .alive || ingressOpen a.phase = false then none
  else if hasIngress I.desc (tname dst) label = false then none
  else if cap ≤ a.box.length then none
  else if loneTerminableB I.desc (tname dst) then none
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
  unfold finishWait at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | awaitEffect k =>
      simp [hph] at h
      cases h
      exact ⟨k, Or.inl rfl, rfl⟩
    | awaitPeer k =>
      simp [hph] at h
      cases h
      exact ⟨k, Or.inr rfl, rfl⟩
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

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
make the charge safe have already held. The actor may be parked, waiting, or
running; the token floor includes the sends still in that continuation. -/
theorem ingress_open (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    (w.st dst).life = .alive ∧ ingressOpen (w.st dst).phase = true ∧
      loneTerminableB I.desc (tname dst) = false ∧
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
            · cases hb : loneTerminableB I.desc (tname dst) with
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

/-- Smallest key of subtree `sub` that already has a member and whose slot for
`template` has never been used. A dead id is not reused. -/
def openSubtreeKey (D : Description) (w : World) (sub template : String) : Option Nat :=
  let rec go (k fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | n + 1 =>
      if k >= w.nextKey sub then none
      else if (w.roster.any fun id => isMember D id sub k) &&
          (w.st (InstId.peer template k)).life == .absent then some k
      else go (k + 1) n
  go 0 (w.nextKey sub)

/-- A scheduler spawn opens a new subtree root. A child of a per-peer stage is
not a root: that stage births it with `Eff.spawn`, at its own key. -/
def rootOf (D : Description) (t : Template) : Bool :=
  if t.supervisor == "" then true
  else
    match templateOf D t.supervisor with
    | some sup => sup.multiplicity == .one
    | none => false

def maySpawnRoot (D : Description) (w : World) (template : String) (t : Template) : Bool :=
  t.multiplicity == .perPeer && rootOf D t && decide (aliveCount w template < w.N)

def spawn (I : Impl) (w : World) (template : String) : Option World :=
  match templateOf I.desc template with
  | none => none
  | some t =>
    if maySpawnRoot I.desc w template t then
      let a := withTokens I.desc template
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 }
      if t.subtree == "" then
        let id := InstId.peer template (w.nextIx template)
        let w := { w with roster := w.roster ++ [id], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n }
        some (readCells I.desc (setActor w id a) id)
      else
        match openSubtreeKey I.desc w t.subtree template with
        | some k =>
          let id := InstId.peer template k
          let w := { w with roster := w.roster ++ [id] }
          some (readCells I.desc (setActor w id a) id)
        | none =>
          let k := w.nextKey t.subtree
          let id := InstId.peer template k
          let w := { w with roster := w.roster ++ [id], nextKey := fun s => if s = t.subtree then k + 1 else w.nextKey s }
          some (readCells I.desc (setActor w id a) id)
    else none

inductive Action where
  | recvBulk (s : InstId)
  | recvPrio (s : InstId)
  | exec (s : InstId)
  | finish (s : InstId)
  | spawn (template : String)
  | ingress (dst : InstId) (label : String)
  /-- Deadline of a call. `TimedOut` from `.awaitReply`, `NotAdmitted` from a parked call. -/
  | callTimeout (s : InstId)
  /-- Scheduler idle. Enabled only when no roster actor can `recv`, `exec`, `finish`,
  or time out a call. Ingress may still be enabled; taking it is the environment's choice. -/
  | stutter
  deriving DecidableEq, Repr

/-- A roster actor has a step the runtime is obliged to consider. -/
def runtimeBusy (I : Impl) (w : World) : Bool :=
  w.roster.any (fun id =>
    (receiveBulk I w id).isSome || (receivePrio I w id).isSome ||
    (execHead I w id).isSome || (finishWait I w id).isSome ||
    (callTimeout w id).isSome)

def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait I w s
  | .spawn template => spawn I w template
  | .ingress dst label => receiveIngress I w dst label
  | .callTimeout s => callTimeout w s
  | .stutter => if runtimeBusy I w then none else some w

/-- Data branch of `awaitPeer`: the external result arrived and `rest` runs.
The timeout is a separate `callTimeout` step. A shutting-down actor does not
take either. -/
def peerData (I : Impl) (w : World) (id : InstId) : Option World :=
  if (w.st id).life != .alive then none
  else
    match (w.st id).phase with
    | .awaitPeer k => some (setActor w id (proceed (w.st id) k))
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
reply, an internal effect, or a peer wait. Every peer wait has a timeout, so
fairness taking `finish` is what says it does not stay stuck. -/
def Deadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ s i, Stuck ρ s i ∧
    match waitKind ((ρ.cfg i).st s) with
    | some (.blockingSend _) => True
    | some (.callReply _) => True
    | some .effect => True
    | some .peer => True
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

theorem failWaiter_roster (w : World) (dead i : InstId) : (failWaiter w dead i).roster = w.roster := by
  unfold failWaiter
  split
  · rfl
  · split
    · split <;> simp [setActor]
    · rfl

theorem failWaiter_nextIx (w : World) (dead i : InstId) : (failWaiter w dead i).nextIx = w.nextIx := by
  unfold failWaiter
  split
  · rfl
  · split
    · split <;> simp [setActor]
    · rfl

theorem failWaiter_N (w : World) (dead i : InstId) : (failWaiter w dead i).N = w.N := by
  unfold failWaiter
  split
  · rfl
  · split
    · split <;> simp [setActor]
    · rfl

theorem failWaiter_other (w : World) (dead i j : InstId) (h : j ≠ i) :
    (failWaiter w dead i).st j = w.st j := by
  unfold failWaiter
  split
  · rfl
  · split
    · split <;> simp [setActor, h]
    · rfl

theorem failWaiter_life (w : World) (dead i j : InstId) :
    ((failWaiter w dead i).st j).life = (w.st j).life := by
  unfold failWaiter
  split
  · rfl
  · split
    · split
      · by_cases hj : j = i
        · simp [setActor, hj]
          unfold proceed
          split <;> rfl
        · simp [setActor, hj]
      · rfl
    · rfl

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

theorem forgetHost_roster (w : World) (dead host : InstId) :
    (forgetHost w dead host).roster = w.roster := by
  unfold forgetHost
  split
  · rfl
  · split <;> simp [setActor]

theorem forgetFold_roster_new (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w host => forgetHost w dead host) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih (forgetHost w dead host)).trans (forgetHost_roster w dead host)

theorem forget_roster (w : World) (dead : InstId) : (forgetSender w dead).roster = w.roster := by
  simpa [forgetSender] using forgetFold_roster_new w dead w.roster

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

theorem forgetHost_nextIx (w : World) (dead host : InstId) (name : String) :
    (forgetHost w dead host).nextIx name = w.nextIx name := by
  unfold forgetHost
  split
  · rfl
  · split <;> simp [setActor]

theorem forgetFold_nextIx_new (w : World) (dead : InstId) (ids : List InstId) (name : String) :
    (ids.foldl (fun w host => forgetHost w dead host) w).nextIx name = w.nextIx name := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih (forgetHost w dead host)).trans (forgetHost_nextIx w dead host name)

theorem forget_nextIx (w : World) (dead : InstId) (name : String) :
    (forgetSender w dead).nextIx name = w.nextIx name := by
  simpa [forgetSender] using forgetFold_nextIx_new w dead w.roster name

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

theorem forgetHost_N (w : World) (dead host : InstId) : (forgetHost w dead host).N = w.N := by
  unfold forgetHost
  split
  · rfl
  · split <;> simp [setActor]

theorem forgetFold_N_new (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w host => forgetHost w dead host) w).N = w.N := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih (forgetHost w dead host)).trans (forgetHost_N w dead host)

theorem forget_N (w : World) (dead : InstId) : (forgetSender w dead).N = w.N := by
  simpa [forgetSender] using forgetFold_N_new w dead w.roster

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

/-- Crediting a sender touches only that sender's token account. -/
theorem credit_fields (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).phase = (w.st i).phase ∧
      ((creditSender w name sender).st i).life = (w.st i).life ∧
      ((creditSender w name sender).st i).box = (w.st i).box ∧
      ((creditSender w name sender).st i).parked = (w.st i).parked ∧
      ((creditSender w name sender).st i).prio = (w.st i).prio := by
  by_cases h : i = sender
  · subst h
    simp [creditSender, setActor, bumpToken]
  · simp [creditSender, setActor, h]

theorem refundMsgs_fields (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w name ms).st i).life = (w.st i).life ∧
      ((refundMsgs w name ms).st i).box = (w.st i).box ∧
      ((refundMsgs w name ms).st i).parked = (w.st i).parked ∧
      ((refundMsgs w name ms).st i).prio = (w.st i).prio := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    have h1 := credit_fields w name m.sender i
    have h2 := ih (creditSender w name m.sender)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem refundParked_fields (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).phase = (w.st i).phase ∧
      ((refundParked w name ps).st i).life = (w.st i).life ∧
      ((refundParked w name ps).st i).box = (w.st i).box ∧
      ((refundParked w name ps).st i).parked = (w.st i).parked ∧
      ((refundParked w name ps).st i).prio = (w.st i).prio := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    have h1 := credit_fields w name p.msg.sender i
    have h2 := ih (creditSender w name p.msg.sender)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

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

theorem host_ne_of_beq (host dead : InstId) (h : (host == dead) = false) : host ≠ dead := by
  simpa [beq_iff_eq] using h

theorem outbound_zero_box (dead : InstId) (ms : List Msg)
    (h : (ms.filter fun m => m.sender == dead).length = 0) :
    ms.filter (fun m => m.sender != dead) = ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    cases hb : m.sender == dead with
    | true =>
      simp [List.filter, hb] at h
    | false =>
      have hkeep : (m.sender != dead) = true := by simp [bne, hb]
      have hlen : (ms.filter fun m => m.sender == dead).length = 0 := by
        simpa [List.filter, hb] using h
      simpa [List.filter, hkeep] using congrArg (m :: ·) (ih hlen)

theorem outbound_zero_park (dead : InstId) (ps : List Parked)
    (h : (ps.filter fun p => p.sender == dead).length = 0) :
    ps.filter (fun p => p.sender != dead) = ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    cases hb : p.sender == dead with
    | true =>
      simp [List.filter, hb] at h
    | false =>
      have hkeep : (p.sender != dead) = true := by simp [bne, hb]
      have hlen : (ps.filter fun p => p.sender == dead).length = 0 := by
        simpa [List.filter, hb] using h
      simpa [List.filter, hkeep] using congrArg (p :: ·) (ih hlen)

theorem forgetHost_off (w : World) (dead host s : InstId) (hs : s ≠ host) (hd : s ≠ dead) :
    (forgetHost w dead host).st s = w.st s := by
  unfold forgetHost
  by_cases hself : host = dead
  · simp [hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      simp [hb, hn]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      simp [hb, hn, setActor, hs, hd]

theorem forgetHost_stable (w : World) (dead host i : InstId) :
    ((forgetHost w dead host).st i).phase = (w.st i).phase ∧
      ((forgetHost w dead host).st i).life = (w.st i).life ∧
      ((forgetHost w dead host).st i).typestate = (w.st i).typestate ∧
      ((forgetHost w dead host).st i).prio = (w.st i).prio := by
  unfold forgetHost
  by_cases hself : host = dead
  · simp [hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      simp [hb, hn]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      have hswap : dead ≠ host := fun h => hself h.symm
      by_cases hi : i = dead
      · simp [hb, hn, hi, setActor, stripSender, addTokens, hself, hswap]
      · by_cases hh : i = host
        · simp [hb, hn, hi, hh, setActor, stripSender, addTokens, hself, hswap]
        · simp [hb, hn, hi, hh, setActor, stripSender, addTokens, hself, hswap]

theorem forgetFold_off_new (w : World) (dead s : InstId) (ids : List InstId) (hs : s ∉ ids)
    (hd : s ≠ dead) :
    (ids.foldl (fun w host => forgetHost w dead host) w).st s = w.st s := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    have hne : s ≠ host := fun h => hs (by simpa [h] using List.Mem.head _)
    have hs' : s ∉ ids := fun h => hs (List.Mem.tail _ h)
    simp only [List.foldl_cons]
    exact (ih (forgetHost w dead host) hs').trans (forgetHost_off w dead host s hne hd)

theorem forget_off (w : World) (dead s : InstId) (hs : s ∉ w.roster) (hd : s ≠ dead) :
    (forgetSender w dead).st s = w.st s := by
  simpa [forgetSender] using forgetFold_off_new w dead s w.roster hs hd

/-- Phase, life, typestate, and the priority lane survive returning outbound slots. -/
theorem forgetFold_stable (w : World) (dead : InstId) (ids : List InstId) (s : InstId) :
    ((ids.foldl (fun w host => forgetHost w dead host) w).st s).phase = (w.st s).phase ∧
      ((ids.foldl (fun w host => forgetHost w dead host) w).st s).life = (w.st s).life ∧
      ((ids.foldl (fun w host => forgetHost w dead host) w).st s).typestate = (w.st s).typestate ∧
      ((ids.foldl (fun w host => forgetHost w dead host) w).st s).prio = (w.st s).prio := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have h1 := forgetHost_stable w dead host s
    have h2 := ih (forgetHost w dead host)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem forget_stable (w : World) (dead s : InstId) :
    ((forgetSender w dead).st s).phase = (w.st s).phase ∧
      ((forgetSender w dead).st s).life = (w.st s).life ∧
      ((forgetSender w dead).st s).typestate = (w.st s).typestate ∧
      ((forgetSender w dead).st s).prio = (w.st s).prio := by
  simpa [forgetSender] using forgetFold_stable w dead w.roster s

theorem filter_park_ne (dead : InstId) (ps : List Parked) (h : ∀ p ∈ ps, p.sender ≠ dead) :
    ps.filter (fun p => p.sender != dead) = ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : p.sender ≠ dead := h p (List.Mem.head _)
    have hb : (p.sender == dead) = false := by simpa [beq_iff_eq] using hp
    have hkeep : (p.sender != dead) = true := by simp [bne, hb]
    simp [List.filter, hkeep, ih fun q hq => h q (List.Mem.tail _ hq)]

theorem filter_box_ne (dead : InstId) (ms : List Msg) (h : ∀ m ∈ ms, m.sender ≠ dead) :
    ms.filter (fun m => m.sender != dead) = ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hm : m.sender ≠ dead := h m (List.Mem.head _)
    have hb : (m.sender == dead) = false := by simpa [beq_iff_eq] using hm
    have hkeep : (m.sender != dead) = true := by simp [bne, hb]
    simp [List.filter, hkeep, ih fun q hq => h q (List.Mem.tail _ hq)]

theorem forgetHost_box (w : World) (dead host s : InstId) :
    ((forgetHost w dead host).st s).box =
      if s = host ∧ host ≠ dead then (w.st s).box.filter fun m => m.sender != dead else (w.st s).box := by
  unfold forgetHost
  by_cases hself : host = dead
  · simp [hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      have hbox := outbound_zero_box dead (w.st host).box (by
        have hsum : ((w.st host).box.filter fun m => m.sender == dead).length +
            ((w.st host).parked.filter fun p => p.sender == dead).length = 0 := by
          simpa [outboundCount] using hz
        exact (Nat.eq_zero_of_add_eq_zero hsum).1)
      by_cases hs : s = host
      · simp [hb, hn, hs, hself, hbox]
      · simp [hb, hn, hs, hself]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      have hswap : dead ≠ host := fun h => hself h.symm
      by_cases hs : s = host
      · simp [hb, hn, hs, hself, hswap, setActor, stripSender]
      · by_cases hd : s = dead
        · simp [hb, hn, hs, hd, hself, hswap, setActor, stripSender, addTokens]
        · simp [hb, hn, hs, hd, hself, hswap, setActor]

theorem forgetHost_park (w : World) (dead host s : InstId) :
    ((forgetHost w dead host).st s).parked =
      if s = host ∧ host ≠ dead then (w.st s).parked.filter fun p => p.sender != dead
      else (w.st s).parked := by
  unfold forgetHost
  by_cases hself : host = dead
  · simp [hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      have hpark := outbound_zero_park dead (w.st host).parked (by
        have hsum : ((w.st host).box.filter fun m => m.sender == dead).length +
            ((w.st host).parked.filter fun p => p.sender == dead).length = 0 := by
          simpa [outboundCount] using hz
        exact (Nat.eq_zero_of_add_eq_zero hsum).2)
      by_cases hs : s = host
      · simp [hb, hn, hs, hself, hpark]
      · simp [hb, hn, hs, hself]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      have hswap : dead ≠ host := fun h => hself h.symm
      by_cases hs : s = host
      · simp [hb, hn, hs, hself, hswap, setActor, stripSender]
      · by_cases hd : s = dead
        · simp [hb, hn, hs, hd, hself, hswap, setActor, stripSender, addTokens]
        · simp [hb, hn, hs, hd, hself, hswap, setActor]

/-- A host that held no parked mail from `dead` still holds the same parked mail. -/
theorem forget_parked_keep (w : World) (dead s : InstId)
    (h : ∀ p ∈ (w.st s).parked, p.sender ≠ dead) :
    ((forgetSender w dead).st s).parked = (w.st s).parked := by
  have hfold : ∀ (ids : List InstId) (w' : World),
      (∀ p ∈ (w'.st s).parked, p.sender ≠ dead) →
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).parked = (w'.st s).parked := by
    intro ids
    induction ids with
    | nil =>
      intro w' _
      simp
    | cons host ids ih =>
      intro w' hnone
      simp only [List.foldl_cons]
      have hstep := forgetHost_park w' dead host s
      have heq : ((forgetHost w' dead host).st s).parked = (w'.st s).parked := by
        rw [hstep]
        by_cases hhit : s = host ∧ host ≠ dead
        · rcases hhit with ⟨hs, hne⟩
          rw [if_pos ⟨hs, hne⟩]
          exact filter_park_ne dead (w'.st s).parked hnone
        · rw [if_neg hhit]
      have hnone' : ∀ p ∈ ((forgetHost w' dead host).st s).parked, p.sender ≠ dead := by
        intro p hp
        exact hnone p (heq ▸ hp)
      exact (ih (forgetHost w' dead host) hnone').trans heq
  simpa [forgetSender] using hfold w.roster w h

/-- No queued message from `dead` means reclaiming outbound mail leaves the box. -/
theorem forget_box_keep (w : World) (dead s : InstId)
    (h : ∀ m ∈ (w.st s).box, m.sender ≠ dead) :
    ((forgetSender w dead).st s).box = (w.st s).box := by
  have hfold : ∀ (ids : List InstId) (w' : World),
      (∀ m ∈ (w'.st s).box, m.sender ≠ dead) →
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).box = (w'.st s).box := by
    intro ids
    induction ids with
    | nil =>
      intro w' _
      simp
    | cons host ids ih =>
      intro w' hnone
      simp only [List.foldl_cons]
      have hstep := forgetHost_box w' dead host s
      have heq : ((forgetHost w' dead host).st s).box = (w'.st s).box := by
        rw [hstep]
        by_cases hhit : s = host ∧ host ≠ dead
        · rcases hhit with ⟨hs, hne⟩
          rw [if_pos ⟨hs, hne⟩]
          exact filter_box_ne dead (w'.st s).box hnone
        · rw [if_neg hhit]
      have hnone' : ∀ m ∈ ((forgetHost w' dead host).st s).box, m.sender ≠ dead := by
        intro m hm
        exact hnone m (heq ▸ hm)
      exact (ih (forgetHost w' dead host) hnone').trans heq
  simpa [forgetSender] using hfold w.roster w h

/-- An actor that is not waiting on `dead` is left untouched by failing `dead`'s waiters. -/
theorem failWaiter_fields (w : World) (dead i s : InstId)
    (hpark : ∀ (b : Bool) (k : Cont), (w.st s).phase ≠ .parked dead b k)
    (hawait : ∀ k, (w.st s).phase ≠ .awaitReply dead k) :
    ((failWaiter w dead i).st s).phase = (w.st s).phase ∧
      ((failWaiter w dead i).st s).life = (w.st s).life ∧
      ((failWaiter w dead i).st s).box = (w.st s).box ∧
      ((failWaiter w dead i).st s).parked = (w.st s).parked ∧
      ((failWaiter w dead i).st s).prio = (w.st s).prio := by
  unfold failWaiter
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        simp only [hph]
        by_cases hd : (d == dead) = true
        · simp only [hd, ite_true]
          by_cases hs : s = i
          · subst hs
            have hdeq : d = dead := by simpa [beq_iff_eq] using hd
            exact absurd (hdeq ▸ hph) (hpark false k)
          · simp [setActor, hs, proceed]
        · simp [hd]
      | true => simp [hph]
    | awaitReply _ _ => simp [hph]
    | idle => simp [hph]
    | run _ => simp [hph]
    | awaitEffect _ => simp [hph]
    | awaitPeer _ => simp [hph]
    | crashed => simp [hph]

theorem failFold_fields (w : World) (dead : InstId) (ids : List InstId) (s : InstId)
    (hpark : ∀ (b : Bool) (k : Cont), (w.st s).phase ≠ .parked dead b k)
    (hawait : ∀ k, (w.st s).phase ≠ .awaitReply dead k) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = (w.st s).phase ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).life = (w.st s).life ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).box = (w.st s).box ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).parked = (w.st s).parked ∧
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).prio = (w.st s).prio := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have h1 := failWaiter_fields w dead i s hpark hawait
    have hpark' : ∀ (b : Bool) (k : Cont),
        ((failWaiter w dead i).st s).phase ≠ .parked dead b k := by
      intro b k hbad
      exact hpark b k (h1.1 ▸ hbad)
    have hawait' : ∀ k, ((failWaiter w dead i).st s).phase ≠ .awaitReply dead k := by
      intro k hbad
      exact hawait k (h1.1 ▸ hbad)
    have h2 := ih (failWaiter w dead i) hpark' hawait'
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- Killing one actor leaves another actor's phase and mail alone when that other
actor is not waiting on it and holds none of its mail. -/
theorem killOne_outsider (w : World) (D : Description) (id s : InstId) (hne : s ≠ id)
    (hpark : ∀ (b : Bool) (k : Cont), (w.st s).phase ≠ .parked id b k)
    (hawait : ∀ k, (w.st s).phase ≠ .awaitReply id k)
    (hbox : ∀ m ∈ (w.st s).box, m.sender ≠ id)
    (hparked : ∀ p ∈ (w.st s).parked, p.sender ≠ id) :
    ((killOne w D id).st s).phase = (w.st s).phase ∧
      ((killOne w D id).st s).life = (w.st s).life ∧
      ((killOne w D id).st s).box = (w.st s).box ∧
      ((killOne w D id).st s).parked = (w.st s).parked ∧
      ((killOne w D id).st s).prio = (w.st s).prio := by
  let w1 := readCells D w id
  have hst := cellsSt D w id s
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_fields w1 (tname id) (w.st id).box s
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_fields w2 (tname id) (w.st id).parked s
  let w4 := failWaiters w3 id
  have h4 := failFold_fields w3 id w3.roster s
    (by intro b k hbad
        have hph : (w3.st s).phase = (w.st s).phase :=
          h3.1.trans (h2.1.trans (congrArg (·.phase) hst))
        exact hpark b k (hph ▸ hbad))
    (by intro k hbad
        have hph : (w3.st s).phase = (w.st s).phase :=
          h3.1.trans (h2.1.trans (congrArg (·.phase) hst))
        exact hawait k (hph ▸ hbad))
  let w5 := forgetSender w4 id
  have hbox4 : ∀ m ∈ (w4.st s).box, m.sender ≠ id := by
    intro m hm
    have hbeq : (w4.st s).box = (w.st s).box :=
      h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst)))
    exact hbox m (hbeq ▸ hm)
  have hpark4 : ∀ p ∈ (w4.st s).parked, p.sender ≠ id := by
    intro p hp
    have hpeq : (w4.st s).parked = (w.st s).parked :=
      h4.2.2.2.1.trans (h3.2.2.2.1.trans (h2.2.2.2.1.trans (congrArg (·.parked) hst)))
    exact hparked p (hpeq ▸ hp)
  have h5box := forget_box_keep w4 id s hbox4
  have h5park := forget_parked_keep w4 id s hpark4
  have h5 := forget_stable w4 id s
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have hpre1 : (w4.st s).phase = (w.st s).phase :=
    h4.1.trans (h3.1.trans (h2.1.trans (congrArg (·.phase) hst)))
  have hpre2 : (w4.st s).life = (w.st s).life :=
    h4.2.1.trans (h3.2.1.trans (h2.2.1.trans (congrArg (·.life) hst)))
  have hpre3 : (w4.st s).box = (w.st s).box :=
    h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst)))
  have hpre4 : (w4.st s).parked = (w.st s).parked :=
    h4.2.2.2.1.trans (h3.2.2.2.1.trans (h2.2.2.2.1.trans (congrArg (·.parked) hst)))
  have hpre5 : (w4.st s).prio = (w.st s).prio :=
    h4.2.2.2.2.trans (h3.2.2.2.2.trans (h2.2.2.2.2.trans (congrArg (·.prio) hst)))
  exact ⟨h5.1.trans hpre1, h5.2.1.trans hpre2, h5box.trans hpre3, h5park.trans hpre4,
    h5.2.2.2.trans hpre5⟩

theorem filter_park_idem (dead : InstId) (ps : List Parked) :
    (ps.filter fun p => p.sender != dead).filter (fun p => p.sender != dead) =
      ps.filter fun p => p.sender != dead := by
  simpa [Bool.and_self] using
    List.filter_filter (p := fun p : Parked => p.sender != dead)
      (q := fun p : Parked => p.sender != dead) ps

theorem filter_box_idem (dead : InstId) (ms : List Msg) :
    (ms.filter fun m => m.sender != dead).filter (fun m => m.sender != dead) =
      ms.filter fun m => m.sender != dead := by
  simpa [Bool.and_self] using
    List.filter_filter (p := fun m : Msg => m.sender != dead)
      (q := fun m : Msg => m.sender != dead) ms

/-- On the roster, and not `dead` itself, queued mail is exactly the filtered list. -/
theorem forget_box_of_mem (w : World) (dead s : InstId) (hs : s ∈ w.roster) (hne : s ≠ dead) :
    ((forgetSender w dead).st s).box =
      (w.st s).box.filter fun m => m.sender != dead := by
  have hfold : ∀ (ids : List InstId) (w' : World), s ∈ ids →
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).box =
        (w'.st s).box.filter fun m => m.sender != dead := by
    intro ids
    induction ids with
    | nil =>
      intro _ hs
      cases hs
    | cons host ids ih =>
      intro w' hs
      simp only [List.foldl_cons]
      by_cases heq : s = host
      · subst heq
        have hstep := forgetHost_box w' dead s s
        have hnow : ((forgetHost w' dead s).st s).box =
            (w'.st s).box.filter fun m => m.sender != dead := by
          rw [hstep, if_pos ⟨rfl, hne⟩]
        by_cases htail : s ∈ ids
        · rw [ih (forgetHost w' dead s) htail, hnow, filter_box_idem]
        · have hskip := forgetFold_off_new (forgetHost w' dead s) dead s ids htail hne
          exact (congrArg (·.box) hskip).trans hnow
      · have htail : s ∈ ids := by
          cases List.mem_cons.mp hs with
          | inl h => exact absurd h heq
          | inr h => exact h
        have hstep := forgetHost_box w' dead host s
        have hsame : ((forgetHost w' dead host).st s).box = (w'.st s).box := by
          rw [hstep, if_neg (fun h => heq h.1)]
        exact (ih (forgetHost w' dead host) htail).trans
          (congrArg (List.filter fun m => m.sender != dead) hsame)
  simpa [forgetSender] using hfold w.roster w hs

/-- On the roster, and not `dead` itself, parked mail is exactly the filtered list. -/
theorem forget_parked_of_mem (w : World) (dead s : InstId) (hs : s ∈ w.roster) (hne : s ≠ dead) :
    ((forgetSender w dead).st s).parked =
      (w.st s).parked.filter fun p => p.sender != dead := by
  have hfold : ∀ (ids : List InstId) (w' : World), s ∈ ids →
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).parked =
        (w'.st s).parked.filter fun p => p.sender != dead := by
    intro ids
    induction ids with
    | nil =>
      intro _ hs
      cases hs
    | cons host ids ih =>
      intro w' hs
      simp only [List.foldl_cons]
      by_cases heq : s = host
      · subst heq
        have hstep := forgetHost_park w' dead s s
        have hnow : ((forgetHost w' dead s).st s).parked =
            (w'.st s).parked.filter fun p => p.sender != dead := by
          rw [hstep, if_pos ⟨rfl, hne⟩]
        by_cases htail : s ∈ ids
        · rw [ih (forgetHost w' dead s) htail, hnow, filter_park_idem]
        · have hskip := forgetFold_off_new (forgetHost w' dead s) dead s ids htail hne
          exact (congrArg (·.parked) hskip).trans hnow
      · have htail : s ∈ ids := by
          cases List.mem_cons.mp hs with
          | inl h => exact absurd h heq
          | inr h => exact h
        have hstep := forgetHost_park w' dead host s
        have hsame : ((forgetHost w' dead host).st s).parked = (w'.st s).parked := by
          rw [hstep, if_neg (fun h => heq h.1)]
        exact (ih (forgetHost w' dead host) htail).trans
          (congrArg (List.filter fun p => p.sender != dead) hsame)
  simpa [forgetSender] using hfold w.roster w hs

/-- Returning slots removes nothing, or exactly `dead`'s parked entries. -/
theorem forget_parked_fate (w : World) (dead s : InstId) :
    ((forgetSender w dead).st s).parked = (w.st s).parked ∨
      ((forgetSender w dead).st s).parked =
        (w.st s).parked.filter fun p => p.sender != dead := by
  have hfold : ∀ (ids : List InstId) (w' : World),
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).parked = (w'.st s).parked ∨
        ((ids.foldl (fun w host => forgetHost w dead host) w').st s).parked =
          (w'.st s).parked.filter fun p => p.sender != dead := by
    intro ids
    induction ids with
    | nil =>
      intro w'
      simp
    | cons host ids ih =>
      intro w'
      simp only [List.foldl_cons]
      have hstep := forgetHost_park w' dead host s
      have hnew : ((forgetHost w' dead host).st s).parked = (w'.st s).parked ∨
          ((forgetHost w' dead host).st s).parked =
            (w'.st s).parked.filter fun p => p.sender != dead := by
        rw [hstep]
        by_cases hhit : s = host ∧ host ≠ dead
        · exact Or.inr (by rw [if_pos hhit])
        · exact Or.inl (by rw [if_neg hhit])
      rcases ih (forgetHost w' dead host) with hsame | hfilt
      · rcases hnew with hnew | hnew
        · exact Or.inl (hsame.trans hnew)
        · exact Or.inr (hsame.trans hnew)
      · rcases hnew with hnew | hnew
        · exact Or.inr (hfilt.trans (congrArg (List.filter fun p => p.sender != dead) hnew))
        · exact Or.inr ((hfilt.trans (congrArg (List.filter fun p => p.sender != dead) hnew)).trans
            (filter_park_idem dead _))
  simpa [forgetSender] using hfold w.roster w

/-- Returning slots removes nothing, or exactly `dead`'s queued messages. -/
theorem forget_box_fate (w : World) (dead s : InstId) :
    ((forgetSender w dead).st s).box = (w.st s).box ∨
      ((forgetSender w dead).st s).box =
        (w.st s).box.filter fun m => m.sender != dead := by
  have hfold : ∀ (ids : List InstId) (w' : World),
      ((ids.foldl (fun w host => forgetHost w dead host) w').st s).box = (w'.st s).box ∨
        ((ids.foldl (fun w host => forgetHost w dead host) w').st s).box =
          (w'.st s).box.filter fun m => m.sender != dead := by
    intro ids
    induction ids with
    | nil =>
      intro w'
      simp
    | cons host ids ih =>
      intro w'
      simp only [List.foldl_cons]
      have hstep := forgetHost_box w' dead host s
      have hnew : ((forgetHost w' dead host).st s).box = (w'.st s).box ∨
          ((forgetHost w' dead host).st s).box =
            (w'.st s).box.filter fun m => m.sender != dead := by
        rw [hstep]
        by_cases hhit : s = host ∧ host ≠ dead
        · exact Or.inr (by rw [if_pos hhit])
        · exact Or.inl (by rw [if_neg hhit])
      rcases ih (forgetHost w' dead host) with hsame | hfilt
      · rcases hnew with hnew | hnew
        · exact Or.inl (hsame.trans hnew)
        · exact Or.inr (hsame.trans hnew)
      · rcases hnew with hnew | hnew
        · exact Or.inr (hfilt.trans (congrArg (List.filter fun m => m.sender != dead) hnew))
        · exact Or.inr ((hfilt.trans (congrArg (List.filter fun m => m.sender != dead) hnew)).trans
            (filter_box_idem dead _))
  simpa [forgetSender] using hfold w.roster w


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
  have hst5 : w5.st s = w4.st s := forget_off w4 id s (by rw [hrs4]; exact hs3) hne
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
  simp [killSubtree, hmem.1, hmem.2]

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
      cases b with
      | false =>
        simp [hph]
        split
        · by_cases hj : j = i
          · simp [setActor, hj, proceed_keeps_box, proceed_keeps_prio, proceed_keeps_parked]
          · simp [setActor, hj]
        · exact ⟨rfl, rfl, rfl⟩
      | true => simp [hph]
    | awaitReply _ _ => simp [hph]
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
  exact (forget_parked_keep w4 id i hsend).trans hpark

/-- Killing someone else leaves a box that holds none of their mail. -/
theorem killOne_box_keep (w : World) (D : Description) (id i : InstId)
    (hne : i ≠ id) (h : ∀ m ∈ (w.st i).box, m.sender ≠ id) :
    ((killOne w D id).st i).box = (w.st i).box := by
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
  have hbox : (w4.st i).box = (w.st i).box := by
    have h4b : (w4.st i).box = (w3.st i).box := by
      simpa [w4, failWaiters] using h4.1
    exact h4b.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst1)))
  have hsend : ∀ m ∈ (w4.st i).box, m.sender ≠ id := by
    intro m hm
    exact h m (hbox ▸ hm)
  exact (forget_box_keep w4 id i hsend).trans hbox

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
  have hfate := forget_parked_fate w4 id i
  simpa [w5, hpark] using hfate

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

theorem killOne_preserves_run (w : World) (D : Description) (id s : InstId) (k : Cont)
    (hs : s ≠ id) (hp : (w.st s).phase = .run k) :
    ((killOne w D id).st s).phase = .run k := by
  let w1 := readCells D w id
  have hp1 : (w1.st s).phase = .run k := by
    rw [cellsSt]
    exact hp
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have hp2 : (w2.st s).phase = .run k :=
    ((refundMsgs_rest w1 (tname id) (w.st id).box s).1).trans hp1
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have hp3 : (w3.st s).phase = .run k :=
    ((refundParked_rest w2 (tname id) (w.st id).parked s).1).trans hp2
  have hhold : holdsPhase (w3.st s).phase = true := by
    simp [hp3, holdsPhase]
  let w4 := failWaiters w3 id
  have hp4 : (w4.st s).phase = .run k := by
    have hfold := (failFold_holds w3 id s w3.roster hhold).1
    simpa [w4, failWaiters] using hfold.trans hp3
  let w5 := forgetSender w4 id
  have hp5 : (w5.st s).phase = .run k := (forget_stable w4 id s).1.trans hp4
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ id s _ hs]
  exact hp5

theorem failFold_life (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).life = (w.st s).life := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact (ih (failWaiter w dead i)).trans (failWaiter_life w dead i s)

theorem killOne_other_rest (w : World) (D : Description) (id i : InstId) (hne : i ≠ id) :
    (((killOne w D id).st i).box = (w.st i).box ∨
        ((killOne w D id).st i).box = (w.st i).box.filter fun m => m.sender != id) ∧
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
  have hstab := forget_stable w4 id i
  have hmailBox : (w4.st i).box = (w3.st i).box := by
    simpa [w4, failWaiters] using hmail4.1
  have hmailPrio : (w4.st i).prio = (w3.st i).prio := by
    simpa [w4, failWaiters] using hmail4.2.1
  have hbox4 : (w4.st i).box = (w.st i).box :=
    hmailBox.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst1)))
  have hprio4 : (w4.st i).prio = (w.st i).prio :=
    hmailPrio.trans (h3.2.2.2.1.trans (h2.2.2.2.1.trans (congrArg (·.prio) hst1)))
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  refine ⟨?_, ?_, ?_⟩
  · have hfate := forget_box_fate w4 id i
    simpa [w5, hbox4] using hfate
  · exact hstab.2.2.2.trans hprio4
  · exact hstab.2.1.trans (hlife4.trans (h3.2.1.trans (h2.2.1.trans (congrArg (·.life) hst1))))

theorem killOne_life_prev (w : World) (D : Description) (id s : InstId)
    (h : ((killOne w D id).st s).life = .alive) : (w.st s).life = .alive := by
  by_cases hs : s = id
  · rw [hs] at h
    rw [(killOne_self w D id).1] at h
    cases h
  · exact ((killOne_other_rest w D id s hs).2.2).symm.trans h

/-- One fold step leaves `i` as it was, or it is a member and the step ends it dead.
Later steps may only keep that death. -/
theorem killFold_life_or (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (i : InstId) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st i).life =
        (w.st i).life ∨
      (isMember D i sub key = true ∧
        ((ids.foldl (fun w id =>
          if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st i).life =
          .dead) := by
  induction ids generalizing w with
  | nil => simp
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      have hmemId : isMember D id sub key = true := ((Bool.and_eq_true _ _).mp hcond).1
      by_cases hme : i = id
      · have hdead : ((killOne w D id).st i).life = .dead := hme.symm ▸ (killOne_self w D id).1
        have hmemi : isMember D i sub key = true := hme.symm ▸ hmemId
        rcases ih (killOne w D id) with hsame | ⟨_, hfin⟩
        · exact Or.inr ⟨hmemi, hsame.trans hdead⟩
        · exact Or.inr ⟨hmemi, hfin⟩
      · have hlife := (killOne_other_rest w D id i hme).2.2
        rcases ih (killOne w D id) with hsame | ⟨hmem, hfin⟩
        · exact Or.inl (hsame.trans hlife)
        · exact Or.inr ⟨hmem, hfin⟩
    · exact ih w

/-- A subtree kill leaves a non-member's life alone. A member it selects ends dead. -/
theorem killSubtree_life_or (w : World) (D : Description) (sub : String) (key : Nat) (i : InstId) :
    ((killSubtree w D sub key).st i).life = (w.st i).life ∨
      (isMember D i sub key = true ∧ ((killSubtree w D sub key).st i).life = .dead) := by
  simpa [killSubtree, killMembers] using killFold_life_or w D sub key w.roster i

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
  have hstab := forget_stable w4 id i
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact ⟨hstab.1.trans (h4.1.trans (h3.1.trans (h2.1.trans (congrArg (·.phase) hst1)))),
    hstab.2.2.1.trans (h4.2.trans (h3.2.2.2.2.2.trans (h2.2.2.2.2.2.trans
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
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hne]
    have hpark : (w4.st i).parked = (w.st i).parked := by
      have h4p : (w4.st i).parked = (w3.st i).parked := by
        simpa [w4, failWaiters] using h4.2.2
      exact h4p.trans (h3.2.2.2.2.1.trans (h2.2.2.2.2.1.trans (congrArg (·.parked) hst1)))
    have hfate := forget_parked_fate w4 id i
    rw [hpark] at hfate
    rcases hfate with hfate | hfate
    · rw [hfate]
      exact List.Sublist.refl _
    · rw [hfate]
      exact List.filter_sublist

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
  simpa [killSubtree] using killMembers_stays_dead w D sub key s hdead

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
    simpa [killSubtree] using hlive
  have hmem := killFold_parked_keep w D sub key w.roster s h (by simpa [killMembers] using hlive')
  simpa [killSubtree, killMembers] using hmem

/-- A survivor's bulk box is unchanged when no killed member has mail queued there. -/
theorem killFold_box_keep (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (h : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ m ∈ (w.st s).box, m.sender ≠ id)
    (hlive : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
      (w.st s).box := by
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
        have heq := killOne_box_keep w D j s hs (h j hmem hjalive)
        have h' : ∀ id, isMember D id sub key = true → ((killOne w D j).st id).life = .alive →
            ∀ m ∈ ((killOne w D j).st s).box, m.sender ≠ id := by
          intro id hmem' halive' m hm
          have hm0 : m ∈ (w.st s).box := by rw [heq] at hm; exact hm
          by_cases hid : id = j
          · subst hid
            have hdead : ((killOne w D id).st id).life = .dead := (killOne_self w D id).1
            rw [hdead] at halive'
            cases halive'
          · exact h id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') m hm0
        exact (ih (killOne w D j) h' hlive).trans heq
    · simp only [hcond] at hlive ⊢
      exact ih w h hlive

theorem killSubtree_box_keep (w : World) (D : Description) (sub : String) (key : Nat)
    (s : InstId)
    (h : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ m ∈ (w.st s).box, m.sender ≠ id)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) :
    ((killSubtree w D sub key).st s).box = (w.st s).box := by
  have hlive' : ((killMembers w D sub key).st s).life = .alive := by
    simpa [killSubtree] using hlive
  have hmem := killFold_box_keep w D sub key w.roster s h (by simpa [killMembers] using hlive')
  simpa [killSubtree, killMembers] using hmem

/-- An actor outside the subtree keeps its phase and mail: it is not waiting on a member
and holds none of a member's mail, and the kill only rewrites those two things. -/
theorem killFold_outsider (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hnot : isMember D s sub key = false)
    (hpark : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ (b : Bool) (k : Cont), (w.st s).phase ≠ .parked id b k)
    (hawait : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ k, (w.st s).phase ≠ .awaitReply id k)
    (hbox : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ m ∈ (w.st s).box, m.sender ≠ id)
    (hparked : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ p ∈ (w.st s).parked, p.sender ≠ id) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        (w.st s).phase ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        (w.st s).life ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box =
        (w.st s).box ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).parked =
        (w.st s).parked ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).prio =
        (w.st s).prio := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      have hmem : isMember D j sub key = true := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        exact hcond.1
      have hlive : (w.st j).life = .alive := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        exact hcond.2
      have hsj : s ≠ j := by
        intro heq
        have hmems : isMember D s sub key = true := heq.symm ▸ hmem
        rw [hmems] at hnot
        cases hnot
      have hstep := killOne_outsider w D j s hsj (hpark j hmem hlive) (hawait j hmem hlive)
        (hbox j hmem hlive) (hparked j hmem hlive)
      have hpark' : ∀ id, isMember D id sub key = true →
          ((killOne w D j).st id).life = .alive →
          ∀ (b : Bool) (k : Cont), ((killOne w D j).st s).phase ≠ .parked id b k := by
        intro id hmem' halive' b k hbad
        have hbad0 : (w.st s).phase = .parked id b k := hstep.1 ▸ hbad
        by_cases hid : id = j
        · subst hid
          have hdead := (killOne_self w D id).1
          rw [hdead] at halive'
          cases halive'
        · exact hpark id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') b k hbad0
      have hawait' : ∀ id, isMember D id sub key = true →
          ((killOne w D j).st id).life = .alive →
          ∀ k, ((killOne w D j).st s).phase ≠ .awaitReply id k := by
        intro id hmem' halive' k hbad
        have hbad0 : (w.st s).phase = .awaitReply id k := hstep.1 ▸ hbad
        by_cases hid : id = j
        · subst hid
          have hdead := (killOne_self w D id).1
          rw [hdead] at halive'
          cases halive'
        · exact hawait id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') k hbad0
      have hbox' : ∀ id, isMember D id sub key = true →
          ((killOne w D j).st id).life = .alive →
          ∀ m ∈ ((killOne w D j).st s).box, m.sender ≠ id := by
        intro id hmem' halive' m hm
        have hm0 : m ∈ (w.st s).box := hstep.2.2.1 ▸ hm
        by_cases hid : id = j
        · subst hid
          have hdead := (killOne_self w D id).1
          rw [hdead] at halive'
          cases halive'
        · exact hbox id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') m hm0
      have hparked' : ∀ id, isMember D id sub key = true →
          ((killOne w D j).st id).life = .alive →
          ∀ p ∈ ((killOne w D j).st s).parked, p.sender ≠ id := by
        intro id hmem' halive' p hp
        have hp0 : p ∈ (w.st s).parked := hstep.2.2.2.1 ▸ hp
        by_cases hid : id = j
        · subst hid
          have hdead := (killOne_self w D id).1
          rw [hdead] at halive'
          cases halive'
        · exact hparked id hmem' ((killOne_other_rest w D j id hid).2.2 ▸ halive') p hp0
      have hih := ih (killOne w D j) hpark' hawait' hbox' hparked'
      exact ⟨hih.1.trans hstep.1, hih.2.1.trans hstep.2.1, hih.2.2.1.trans hstep.2.2.1,
        hih.2.2.2.1.trans hstep.2.2.2.1, hih.2.2.2.2.trans hstep.2.2.2.2⟩
    · simp only [hcond, ite_false]
      exact ih w hpark hawait hbox hparked

theorem killSubtree_outsider (w : World) (D : Description) (sub : String) (key : Nat)
    (s : InstId) (hnot : isMember D s sub key = false)
    (hpark : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ (b : Bool) (k : Cont), (w.st s).phase ≠ .parked id b k)
    (hawait : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ k, (w.st s).phase ≠ .awaitReply id k)
    (hbox : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ m ∈ (w.st s).box, m.sender ≠ id)
    (hparked : ∀ id, isMember D id sub key = true → (w.st id).life = .alive →
      ∀ p ∈ (w.st s).parked, p.sender ≠ id) :
    ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
      ((killSubtree w D sub key).st s).life = (w.st s).life ∧
      ((killSubtree w D sub key).st s).box = (w.st s).box ∧
      ((killSubtree w D sub key).st s).parked = (w.st s).parked ∧
      ((killSubtree w D sub key).st s).prio = (w.st s).prio := by
  have hmem := killFold_outsider w D sub key w.roster s hnot hpark hawait hbox hparked
  simpa [killSubtree, killMembers] using hmem

/-- If `s` is still alive after the fold, no step killed it, so its bulk mail is unchanged
and a phase the kill does not rewrite is still that phase. -/
theorem killFold_if_alive (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (hlive : ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        .alive) :
    (w.st s).life = .alive ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box.Sublist
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
    refine ⟨hlive, List.Sublist.refl _, rfl, List.Sublist.refl _, ?_⟩
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
        have hbox : ((killOne w D id).st s).box.Sublist (w.st s).box := by
          rcases hrest.1 with h | h
          · rw [h]
            exact List.Sublist.refl _
          · rw [h]
            exact List.filter_sublist
        refine ⟨hrest.2.2.symm.trans hih.1, List.Sublist.trans hih.2.1 hbox, hih.2.2.1.trans hrest.2.1,
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
    (w.st s).life = .alive ∧ ((killMembers w D sub key).st s).box.Sublist (w.st s).box ∧
      ((killMembers w D sub key).st s).prio = (w.st s).prio ∧
      ((killMembers w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killMembers w D sub key).st s).phase = (w.st s).phase ∧
          ((killMembers w D sub key).st s).typestate = (w.st s).typestate) := by
  simpa [killMembers] using killFold_if_alive w D sub key w.roster s hlive

theorem killSubtree_if_alive (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) :
    (w.st s).life = .alive ∧ ((killSubtree w D sub key).st s).box.Sublist (w.st s).box ∧
      ((killSubtree w D sub key).st s).prio = (w.st s).prio ∧
      ((killSubtree w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
          ((killSubtree w D sub key).st s).typestate = (w.st s).typestate) := by
  have hlive' : ((killMembers w D sub key).st s).life = .alive := by
    simpa [killSubtree] using hlive
  have hmem := killMembers_if_alive w D sub key s hlive'
  simpa [killSubtree] using hmem

/-- An actor that is already not alive is not killed, so its mail and a stable phase stay. -/
theorem killFold_if_dead (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (hdead : (w.st s).life ≠ .alive) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).life =
        (w.st s).life ∧
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).box.Sublist
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
    exact ⟨rfl, List.Sublist.refl _, rfl, List.Sublist.refl _, fun _ => ⟨rfl, rfl⟩⟩
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
        have hbox : ((killOne w D id).st s).box.Sublist (w.st s).box := by
          rcases hrest.1 with h | h
          · rw [h]
            exact List.Sublist.refl _
          · rw [h]
            exact List.filter_sublist
        refine ⟨hih.1.trans hrest.2.2, List.Sublist.trans hih.2.1 hbox, hih.2.2.1.trans hrest.2.1,
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
      ((killSubtree w D sub key).st s).box.Sublist (w.st s).box ∧
      ((killSubtree w D sub key).st s).prio = (w.st s).prio ∧
      ((killSubtree w D sub key).st s).parked.Sublist (w.st s).parked ∧
      (holdsPhase (w.st s).phase = true →
        ((killSubtree w D sub key).st s).phase = (w.st s).phase ∧
          ((killSubtree w D sub key).st s).typestate = (w.st s).typestate) := by
  have hmem := killFold_if_dead w D sub key w.roster s hdead
  simpa [killSubtree, killMembers] using hmem

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
        refine ⟨hmem, hrest.1.trans hself.1, ?_,
          sublist_nil (hself.2.2.1 ▸ hrest.2.1),
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
    simpa [killSubtree] using hd
  have hmem := killFold_died w D sub key w.roster s hl (by simpa [killMembers] using hd')
  simpa [killSubtree, killMembers] using hmem

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
          if u.supervisor != "" then some s!"fail: {u.name} names a supervisor without a subtree"
          else if u.timeoutKills then some s!"fail: {u.name} sets timeoutKills without a subtree"
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
      cases b with
      | false =>
        simp only [hph]
        split <;> simp [setActor]
      | true => simp [hph]
    | awaitReply _ _ => simp [hph]
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

theorem forgetHost_cell (w : World) (dead host : InstId) (d l : String) :
    (forgetHost w dead host).cell d l = w.cell d l := by
  unfold forgetHost
  by_cases hself : host = dead
  · simp [hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      simp [hb, hn]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      simp [hb, hn, setActor]

theorem foldForget_cell (w : World) (dead : InstId) (ids : List InstId) (d l : String) :
    ((ids.foldl (fun w host => forgetHost w dead host) w).cell d l) = w.cell d l := by
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih (forgetHost w dead host)).trans (forgetHost_cell w dead host d l)

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
  simpa [killSubtree, killMembers] using killFold_quiet w D sub key w.roster d l

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
        cases b with
        | false =>
          simp only [hph]
          split
          · intro hbad
            cases hk : k'.rest <;> simp [setActor, proceed, hk] at hbad
          · exact h k
        | true => exact h k
      | awaitReply _ _ => exact h k
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
        · cases c with
          | true => simp [hph]
          | false =>
            simp only [hph]
            have hne' : (dst == dead) = false := by simpa [beq_iff_eq] using hdst
            simp [hne']
            exact hph
      · exact congrArg (·.phase) (failWaiter_other w dead i s hsi)
    exact (ih (failWaiter w dead i) (by rw [hstep]; exact hph)).trans hstep

/-- A parked call is not a waiter `failWaiter` resumes, whichever target it names. -/
theorem failFold_keeps_call (w : World) (dead s dst : InstId) (ids : List InstId) (k : Cont)
    (hph : (w.st s).phase = .parked dst true k) :
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
        · simp [hph]
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

/-- A live plain sender parked on `dead` is resumed, so that parked phase does not survive.
A parked call stays until its own deadline. -/
theorem failWaiter_clears (w : World) (dead s : InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive)
    (hc : c = false) :
    ∀ k', ((failWaiter w dead s).st s).phase ≠ .parked dead c k' := by
  intro k'
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  subst hc
  simp only [hlive, hph, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  intro hbad
  cases hk : k.rest <;> simp [setActor, proceed, hk] at hbad

theorem failFold_clears (w : World) (dead s : InstId) (ids : List InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive)
    (hs : s ∈ ids) (hc : c = false) :
    ∀ k', ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase ≠ .parked dead c k' := by
  intro k'
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    cases hs with
    | head =>
      exact failFold_keeps_off (failWaiter w dead s) dead s dead ids c
        (failWaiter_clears w dead s c k hph hl hc) k'
    | tail _ hmem =>
      by_cases heq : i = s
      · subst heq
        exact failFold_keeps_off (failWaiter w dead i) dead i dead ids c
          (failWaiter_clears w dead i c k hph hl hc) k'
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
  have h5 := forget_stable w4 j s
  have hbody : killOne w D j =
      setActor w5 j { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have h4s : (w4.st s).phase = (w3.st s).phase := by simpa [w4] using h4
  exact h5.1.trans (h4s.trans (hph3.trans hph.symm))

/-- Killing `dst` resumes a live sender parked on it. -/
theorem killOne_drops_park (w : World) (D : Description) (dst s : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ dst) (hs : s ∈ w.roster) (hl : (w.st s).life = .alive)
    (hph : (w.st s).phase = .parked dst c k) (hc : c = false) :
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
  have h4 := failFold_clears w3 dst s w3.roster c k hph3 hl3 hs3 hc
  let w5 := forgetSender w4 dst
  have h5 := forget_stable w4 dst s
  have hbody : killOne w D dst =
      setActor w5 dst { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  intro k' hbad
  have : (w4.st s).phase = .parked dst c k' := by rw [← h5.1]; exact hbad
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
    have h5 := forget_stable w4 j s
    have hbody : killOne w D j =
        setActor w5 j { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hne]
    intro hbad
    have hback : ((failWaiters w3 j).st s).phase = .parked dst c k := by
      have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
      rw [h5p] at hbad
      simpa [w4] using hbad
    exact h4 k hback

/-- While `dst` is a live member ahead in the fold, a sender parked on `dst` leaves that phase. -/
theorem killFold_unpark (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (hc : c = false)
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
        · have hdrop := killOne_drops_park w D dst s c k hsd hs hls hph hc
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
          · have hdrop := killOne_drops_park w D dst s c k hsd hs hls hph hc
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
    (hdst : dst ∈ w.roster) (hc : c = false) :
    ∀ k', ((killSubtree w D sub key).st s).phase ≠ .parked dst c k' := by
  simpa [killSubtree, killMembers] using
    killFold_unpark w D sub key w.roster s dst c k hs hc
      (Or.inl ⟨hph, hdst, hl, hm, hls⟩)

/-- Resuming a plain parked sender writes `.idle` or `.run`. A parked call is not resumed. -/
theorem failWaiter_shape (w : World) (dead s : InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive)
    (hc : c = false) :
    ((failWaiter w dead s).st s).phase = .idle ∨ ∃ k', ((failWaiter w dead s).st s).phase = .run k' := by
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  subst hc
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

/-- A parked sender is resumed only when the actor it waits on is the one that fails.
Otherwise the park stays. -/
theorem failWaiter_park (w : World) (dead i s dst : InstId) (c : Bool) (k : Cont)
    (hpark : (w.st s).phase = .parked dst c k) :
    ((failWaiter w dead i).st s).phase = .parked dst c k ∨
      ((failWaiter w dead i).st s).phase = resumed k := by
  by_cases hs : s = i
  · rw [hs] at hpark ⊢
    unfold failWaiter
    split
    · exact Or.inl hpark
    · cases hph : (w.st i).phase with
      | parked d b ck =>
        cases b with
        | false =>
          rw [hpark] at hph
          cases hph
          simp
          split
          · simp [setActor_self]
            exact Or.inr (proceed_resumed (w.st i) k)
          · exact Or.inl hpark
        | true =>
          rw [hpark] at hph
          cases hph
          exact Or.inl hpark
      | idle => simp [hpark] at hph
      | run _ => simp [hpark] at hph
      | awaitReply _ _ => simp [hpark] at hph
      | awaitEffect _ => simp [hpark] at hph
      | awaitPeer _ => simp [hpark] at hph
      | crashed => simp [hpark] at hph
  · rw [failWaiter_other w dead i s hs]
    exact Or.inl hpark

theorem failFold_park (w : World) (dead s dst : InstId) (c : Bool) (k : Cont) (ids : List InstId)
    (hph : (w.st s).phase = .parked dst c k) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .parked dst c k ∨
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = resumed k := by
  induction ids generalizing w with
  | nil => exact Or.inl hph
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rcases failWaiter_park w dead i s dst c k hph with hstay | hgo
    · exact ih (failWaiter w dead i) hstay
    · have hh : holdsPhase (((failWaiter w dead i).st s).phase) = true := by
        rw [hgo]
        cases hk : k.rest <;> simp [resumed, holdsPhase, hk]
      exact Or.inr ((failFold_holds (failWaiter w dead i) dead s ids hh).1.trans hgo)

theorem killOne_from_park (w : World) (D : Description) (id s dst : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ id) (hph : (w.st s).phase = .parked dst c k) :
    ((killOne w D id).st s).phase = .parked dst c k ∨
      ((killOne w D id).st s).phase = resumed k := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  have hph1 : (w1.st s).phase = .parked dst c k := by simpa [hst1] using hph
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
  have hph2 : (w2.st s).phase = .parked dst c k := by
    have hphase : (w2.st s).phase = (w1.st s).phase := by simpa [w2] using h2.1
    exact hphase.trans hph1
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
  have hph3 : (w3.st s).phase = .parked dst c k := by
    have hphase : (w3.st s).phase = (w2.st s).phase := by simpa [w3] using h3.1
    exact hphase.trans hph2
  let w4 := failWaiters w3 id
  have h4 : (w4.st s).phase = .parked dst c k ∨ (w4.st s).phase = resumed k := by
    simpa [w4, failWaiters] using failFold_park w3 id s dst c k w3.roster hph3
  let w5 := forgetSender w4 id
  have h5 := forget_stable w4 id s
  have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  rcases h4 with hstay | hgo
  · exact Or.inl (h5p.trans hstay)
  · exact Or.inr (h5p.trans hgo)

theorem killOne_keeps_done (w : World) (D : Description) (j s : InstId) (k : Cont) (hne : s ≠ j)
    (h : (w.st s).phase = resumed k ∨ (w.st s).phase = .idle) :
    ((killOne w D j).st s).phase = (w.st s).phase := by
  have hh : holdsPhase (w.st s).phase = true := by
    rcases h with h | h
    · rw [h]
      cases hk : k.rest <;> simp [resumed, holdsPhase, hk]
    · simp [holdsPhase, h]
  exact (killOne_holds w D j s hne hh).1

/-- Killing one actor leaves a parked sender parked, resumed, or idle. -/
theorem killOne_block_inv (w : World) (D : Description) (j s dst : InstId) (c : Bool) (k : Cont)
    (h : (w.st s).phase = .parked dst c k ∨ (w.st s).phase = resumed k ∨ (w.st s).phase = .idle) :
    ((killOne w D j).st s).phase = .parked dst c k ∨
      ((killOne w D j).st s).phase = resumed k ∨
      ((killOne w D j).st s).phase = .idle := by
  by_cases hs : s = j
  · exact Or.inr (Or.inr (by rw [hs]; exact (killOne_self w D j).2.1))
  · rcases h with hpark | hres | hidle
    · rcases killOne_from_park w D j s dst c k hs hpark with hstay | hgo
      · exact Or.inl hstay
      · exact Or.inr (Or.inl hgo)
    · exact Or.inr (Or.inl ((killOne_keeps_done w D j s k hs (Or.inl hres)).trans hres))
    · exact Or.inr (Or.inr ((killOne_keeps_done w D j s k hs (Or.inr hidle)).trans hidle))

theorem killFold_block (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont)
    (h : (w.st s).phase = .parked dst c k ∨ (w.st s).phase = resumed k ∨ (w.st s).phase = .idle) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .parked dst c k ∨
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
          resumed k ∨
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
          .idle := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (killOne_block_inv w D j s dst c k h)
    · simp only [hcond]
      exact ih w h

theorem killSubtree_block (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (c : Bool) (k : Cont) (hph : (w.st s).phase = .parked dst c k) :
    ((killSubtree w D sub key).st s).phase = .parked dst c k ∨
      ((killSubtree w D sub key).st s).phase = resumed k ∨
      ((killSubtree w D sub key).st s).phase = .idle := by
  simpa [killSubtree, killMembers] using
    killFold_block w D sub key w.roster s dst c k (Or.inl hph)

/-- An `awaitReply` stays, or the callee's failure returns the caller to idle. -/
theorem failWaiter_await (w : World) (dead s dst : InstId) (k : Cont)
    (hawait : (w.st s).phase = .awaitReply dst k) :
    ((failWaiter w dead s).st s).phase = .awaitReply dst k ∨
      ((failWaiter w dead s).st s).phase = .idle := by
  unfold failWaiter
  split
  · exact Or.inl hawait
  · simp only [hawait]
    exact Or.inl trivial

theorem failWaiter_await_inv (w : World) (dead i s dst : InstId) (k : Cont)
    (h : (w.st s).phase = .awaitReply dst k ∨ (w.st s).phase = .idle) :
    ((failWaiter w dead i).st s).phase = .awaitReply dst k ∨
      ((failWaiter w dead i).st s).phase = .idle := by
  rcases h with hawait | hidle
  · by_cases hs : s = i
    · rw [hs] at hawait ⊢
      exact failWaiter_await w dead i dst k hawait
    · rw [failWaiter_other w dead i s hs]
      exact Or.inl hawait
  · by_cases hs : s = i
    · rw [hs] at hidle ⊢
      exact Or.inr ((failWaiter_holds w dead i i (by simp [holdsPhase, hidle])).1.trans hidle)
    · rw [failWaiter_other w dead i s hs]
      exact Or.inr hidle

theorem failFold_await (w : World) (dead s dst : InstId) (k : Cont) (ids : List InstId)
    (h : (w.st s).phase = .awaitReply dst k ∨ (w.st s).phase = .idle) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .awaitReply dst k ∨
      ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (failWaiter_await_inv w dead i s dst k h)

theorem killOne_await_inv (w : World) (D : Description) (j s dst : InstId) (k : Cont)
    (h : (w.st s).phase = .awaitReply dst k ∨ (w.st s).phase = .idle) :
    ((killOne w D j).st s).phase = .awaitReply dst k ∨
      ((killOne w D j).st s).phase = .idle := by
  by_cases hs : s = j
  · exact Or.inr (by rw [hs]; exact (killOne_self w D j).2.1)
  · rcases h with hawait | hidle
    · let w1 := readCells D w j
      have hst1 : w1.st s = w.st s := cellsSt D w j s
      have hph1 : (w1.st s).phase = .awaitReply dst k := by simpa [hst1] using hawait
      let w2 := refundMsgs w1 (tname j) (w.st j).box
      have h2 := refundMsgs_rest w1 (tname j) (w.st j).box s
      have hph2 : (w2.st s).phase = .awaitReply dst k := by
        have hphase : (w2.st s).phase = (w1.st s).phase := by simpa [w2] using h2.1
        exact hphase.trans hph1
      let w3 := refundParked w2 (tname j) (w.st j).parked
      have h3 := refundParked_rest w2 (tname j) (w.st j).parked s
      have hph3 : (w3.st s).phase = .awaitReply dst k := by
        have hphase : (w3.st s).phase = (w2.st s).phase := by simpa [w3] using h3.1
        exact hphase.trans hph2
      let w4 := failWaiters w3 j
      have h4 : (w4.st s).phase = .awaitReply dst k ∨ (w4.st s).phase = .idle := by
        simpa [w4, failWaiters] using failFold_await w3 j s dst k w3.roster (Or.inl hph3)
      let w5 := forgetSender w4 j
      have h5 := forget_stable w4 j s
      have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
      have hbody : killOne w D j =
          setActor w5 j { w5.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
        simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
      rw [hbody, setActor_other _ _ _ _ hs]
      rcases h4 with hstay | hgo
      · exact Or.inl (h5p.trans hstay)
      · exact Or.inr (h5p.trans hgo)
    · exact Or.inr ((killOne_holds w D j s hs (by simp [holdsPhase, hidle])).1.trans hidle)

theorem killFold_await (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (k : Cont)
    (h : (w.st s).phase = .awaitReply dst k ∨ (w.st s).phase = .idle) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .awaitReply dst k ∨
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
          .idle := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (killOne_await_inv w D j s dst k h)
    · simp only [hcond]
      exact ih w h

theorem killSubtree_await (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (k : Cont) (hph : (w.st s).phase = .awaitReply dst k) :
    ((killSubtree w D sub key).st s).phase = .awaitReply dst k ∨
      ((killSubtree w D sub key).st s).phase = .idle := by
  simpa [killSubtree, killMembers] using
    killFold_await w D sub key w.roster s dst k (Or.inl hph)

theorem failFold_resumes (w : World) (dead s : InstId) (ids : List InstId) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked dead c k) (hl : (w.st s).life = .alive) (hs : s ∈ ids)
    (hc : c = false) :
    (((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .idle) ∨
      ∃ k', ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .run k' := by
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    cases hs with
    | head =>
      exact failFold_shape (failWaiter w dead s) dead s ids (failWaiter_shape w dead s c k hph hl hc)
    | tail _ hmem =>
      by_cases heq : i = s
      · subst heq
        exact failFold_shape (failWaiter w dead i) dead i ids (failWaiter_shape w dead i c k hph hl hc)
      · have hst := failWaiter_other w dead i s (fun h => heq h.symm)
        exact ih (failWaiter w dead i) (by rw [hst]; exact hph) (by rw [hst]; exact hl) hmem

theorem killOne_drops_shape (w : World) (D : Description) (dst s : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ dst) (hs : s ∈ w.roster) (hl : (w.st s).life = .alive)
    (hph : (w.st s).phase = .parked dst c k) (hc : c = false) :
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
    simpa [failWaiters] using failFold_resumes w3 dst s w3.roster c k hph3 hl3 hs3 hc
  let w4 := failWaiters w3 dst
  let w5 := forgetSender w4 dst
  have h5 := forget_stable w4 dst s
  have hbody : killOne w D dst =
      setActor w5 dst { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  rcases hfold with hidle | ⟨k', hrun⟩
  · have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
    exact Or.inl (by rw [h5p]; simpa [w4] using hidle)
  · have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
    exact Or.inr ⟨k', by rw [h5p]; simpa [w4] using hrun⟩

/-- A sender parked on a member that this fold kills is afterwards idle or running. -/
theorem killFold_resumed (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (hc : c = false)
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
            (Or.inr (killOne_drops_shape w D dst s c k hsd hs hls hph hc))
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
              (Or.inr (killOne_drops_shape w D dst s c k hsd hs hls hph hc))
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

/-- A caller's `awaitReply` survives the callee's death. The deadline, not the
kill, ends the wait. -/
theorem failWaiter_await_idle (w : World) (dead s : InstId) (k : Cont)
    (hph : (w.st s).phase = .awaitReply dead k) (hl : (w.st s).life = .alive) :
    ((failWaiter w dead s).st s).phase = .awaitReply dead k := by
  unfold failWaiter
  have hlive : ((w.st s).life != .alive) = false := by simp [hl, bne]
  simp [hlive, hph]

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
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .awaitReply dead k := by
  have _mem := hs
  have hfold : ∀ (ids' : List InstId) (w' : World),
      (w'.st s).phase = .awaitReply dead k → (w'.st s).life = .alive →
        ((ids'.foldl (fun w i => failWaiter w dead i) w').st s).phase = .awaitReply dead k := by
    intro ids'
    induction ids' with
    | nil =>
      intro w' hph' _
      simpa using hph'
    | cons i rest ih =>
      intro w' hph' hl'
      simp only [List.foldl_cons]
      refine ih _ ?_ ?_
      · by_cases hsi : s = i
        · subst hsi
          exact failWaiter_await_idle w' dead s k hph' hl'
        · exact (congrArg (·.phase) (failWaiter_other w' dead i s hsi)).trans hph'
      · rw [failWaiter_life]; exact hl'
  exact hfold ids w hph hl

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
        · simp [hph]
      · exact congrArg (·.phase) (failWaiter_other w dead i s hsi)
    exact (ih (failWaiter w dead i) (by rw [hstep]; exact hph)).trans hstep

theorem killFold_await_idle (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (k : Cont) (hs : s ∈ w.roster)
    (h : ((w.st s).phase = .awaitReply dst k ∧ dst ∈ ids ∧ (w.st dst).life = .alive ∧
          isMember D dst sub key = true ∧ (w.st s).life = .alive) ∨
        (w.st s).phase = .idle) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .awaitReply dst k ∨
      ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
        .idle := by
  have _rostered := hs
  refine killFold_await w D sub key ids s dst k ?_
  rcases h with ⟨hph, _, _, _, _⟩ | hidle
  · exact Or.inl hph
  · exact Or.inr hidle

/-- Killing the callee does not idle an outside caller. The caller stays in
`awaitReply` until its deadline, unless the caller itself is the actor killed. -/
theorem killSubtree_await_idle (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (k : Cont) (hs : s ∈ w.roster)
    (hph : (w.st s).phase = .awaitReply dst k) (hls : (w.st s).life = .alive)
    (hl : (w.st dst).life = .alive) (hm : isMember D dst sub key = true) (hdst : dst ∈ w.roster) :
    ((killSubtree w D sub key).st s).phase = .awaitReply dst k ∨
      ((killSubtree w D sub key).st s).phase = .idle := by
  simpa [killSubtree, killMembers] using
    killFold_await_idle w D sub key w.roster s dst k hs (Or.inl ⟨hph, hdst, hl, hm, hls⟩)


theorem killSubtree_resumed (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (c : Bool) (k : Cont) (hs : s ∈ w.roster)
    (hph : (w.st s).phase = .parked dst c k) (hls : (w.st s).life = .alive)
    (hl : (w.st dst).life = .alive) (hm : isMember D dst sub key = true) (hdst : dst ∈ w.roster)
    (hc : c = false) :
    (((killSubtree w D sub key).st s).phase = .idle) ∨
      ∃ k', ((killSubtree w D sub key).st s).phase = .run k' := by
  simpa [killSubtree, killMembers] using
    killFold_resumed w D sub key w.roster s dst c k hs hc (Or.inl ⟨hph, hdst, hl, hm, hls⟩)

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
      refine ⟨hrest.1.trans hself.1, ?_, sublist_nil (hself.2.2.1 ▸ hrest.2.1),
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
  simpa [killSubtree, killMembers] using killFold_kills w D sub key w.roster s hm hl hs

/-- An actor still alive after the subtree kill was not one of its members. -/
theorem survivor_not_member (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (hlive : ((killSubtree w D sub key).st s).life = .alive) (hs : s ∈ w.roster) :
    isMember D s sub key = false := by
  by_cases hm : isMember D s sub key = true
  · have hpre := (killSubtree_if_alive w D sub key s hlive).1
    have hdead := (killSubtree_kills w D sub key s hm hpre hs).1
    rw [hdead] at hlive
    cases hlive
  · cases hb : isMember D s sub key with
    | false => rfl
    | true => exact False.elim (hm hb)

/-- A core is not a subtree member, so a subtree kill leaves its life alone. -/
theorem killFold_core_life (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (name : String) :
    ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st
        (InstId.core name)).life = (w.st (InstId.core name)).life := by
  induction ids generalizing w with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      have hne : InstId.core name ≠ id := by
        intro h
        subst h
        simp [isMember] at hcond
      have hlife := (killOne_other_rest w D id (InstId.core name) hne).2.2
      exact (ih _).trans hlife
    · exact ih _

theorem killSubtree_core_life (w : World) (D : Description) (sub : String) (key : Nat) (name : String) :
    ((killSubtree w D sub key).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  simpa [killSubtree, killMembers] using killFold_core_life w D sub key w.roster name

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
      cases b with
      | false =>
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
      | true => simp [hph] at h ⊢
    | awaitReply _ _ => simp [hph] at h ⊢
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
      | parked _ b k =>
        cases b with
        | false =>
          simp only [hph, beq_iff_eq]
          split
          · cases hk : k.rest <;> simp [setActor, proceed, hk]
          · exact h
        | true => simp [hph]
      | awaitReply _ _ => simp [hph]
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
    have h5 := forget_stable w4 id s
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hs]
    have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
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
  simpa [killSubtree, killMembers] using killFold_no_crash w D sub key w.roster s h

/-- Every mailbox is a sublist of what it held: a kill refunds, filters, or empties. -/
theorem killSubtree_box_sub (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId) :
    ((killSubtree w D sub key).st s).box.Sublist (w.st s).box := by
  by_cases hl : (w.st s).life = .alive
  · by_cases hl' : ((killSubtree w D sub key).st s).life = .alive
    · exact (killSubtree_if_alive w D sub key s hl').2.1
    · rw [(killSubtree_died w D sub key s hl hl').2.2.2.1]
      exact nil_sublist _
  · exact (killSubtree_if_dead w D sub key s hl).2.1

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
    have h5 := forget_stable w4 id s
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    have hph : (w5.st s).phase = ((killOne w D id).st s).phase := by
      rw [hbody, setActor_other _ _ _ _ hs]
    have hty : (w5.st s).typestate = ((killOne w D id).st s).typestate := by
      rw [hbody, setActor_other _ _ _ _ hs]
    have h5p : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using h5.1
    have h5t : (w5.st s).typestate = (w4.st s).typestate := by simpa [w5] using h5.2.2.1
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
  simpa [killSubtree, killMembers] using killFold_keeps_wait w D sub key w.roster s
    (by simpa [killSubtree, killMembers] using h)

/-- `proceed` lands on a phase a later kill does not touch. -/
theorem resumed_holds (k : Cont) : holdsPhase (resumed k) = true := by
  cases hk : k.rest <;> simp [resumed, holdsPhase, hk]

/-- A plain park on the actor being killed becomes exactly the resumed continuation. -/
theorem failWaiter_resumes (w : World) (dead i : InstId) (k : Cont)
    (hl : (w.st i).life = .alive) (hph : (w.st i).phase = .parked dead false k) :
    ((failWaiter w dead i).st i).phase = resumed k := by
  unfold failWaiter
  have hlive : ((w.st i).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, hph, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  cases hk : k.rest <;> simp [setActor, proceed, resumed, hk]

/-- A park or reply aimed at someone else is not this kill. -/
theorem failWaiter_keeps_park (w : World) (dead i dst : InstId) (c : Bool) (k : Cont)
    (hdst : dst ≠ dead) (hph : (w.st i).phase = .parked dst c k) :
    ((failWaiter w dead i).st i).phase = .parked dst c k := by
  unfold failWaiter
  by_cases hl : ((w.st i).life != .alive) = true
  · simp [hl, hph]
  · have hlive : ((w.st i).life != .alive) = false := by
      simpa [Bool.not_eq_true] using hl
    cases c with
    | true => simp [hlive, hph]
    | false =>
      simp only [hlive, hph]
      have hne : (dst == dead) = false := by simpa [beq_iff_eq] using hdst
      simp [hne, hph]

theorem failFold_keeps_park (w : World) (dead s dst : InstId) (c : Bool) (k : Cont)
    (ids : List InstId) (hdst : dst ≠ dead) (hph : (w.st s).phase = .parked dst c k) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .parked dst c k := by
  induction ids generalizing w with
  | nil => simpa using hph
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep : ((failWaiter w dead i).st s).phase = .parked dst c k := by
      by_cases hs : i = s
      · rw [hs]
        exact failWaiter_keeps_park w dead s dst c k hdst hph
      · have hother := failWaiter_other w dead i s (Ne.symm hs)
        exact (congrArg (·.phase) hother).trans hph
    exact ih (failWaiter w dead i) hstep

/-- The fold resumes `s` when it reaches that actor, and the resumed phase stays. -/
theorem failFold_resumes_at (w : World) (dead s : InstId) (k : Cont) (ids : List InstId)
    (hl : (w.st s).life = .alive) (hph : (w.st s).phase = .parked dead false k)
    (hs : s ∈ ids) :
    ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = resumed k := by
  induction ids generalizing w with
  | nil => cases hs
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep : ((failWaiter w dead i).st s).life = (w.st s).life ∧
        ((failWaiter w dead i).st s).phase = (w.st s).phase ∨ i = s := by
      by_cases hi : i = s
      · exact Or.inr hi
      · exact Or.inl ⟨congrArg (·.life) (failWaiter_other w dead i s (Ne.symm hi)),
          congrArg (·.phase) (failWaiter_other w dead i s (Ne.symm hi))⟩
    cases hs with
    | head =>
      have h1 := failWaiter_resumes w dead s k hl hph
      have hh : holdsPhase ((failWaiter w dead s).st s).phase = true := by
        rw [h1]
        exact resumed_holds k
      exact ((failFold_holds (failWaiter w dead s) dead s ids hh).1).trans h1
    | tail _ hmem =>
      rcases hstep with ⟨hlife, hphase⟩ | hi
      · exact ih (failWaiter w dead i) (hlife.trans hl) (hphase.trans hph) hmem
      · rw [hi]
        have h1 := failWaiter_resumes w dead s k hl hph
        have hh : holdsPhase ((failWaiter w dead s).st s).phase = true := by
          rw [h1]
          exact resumed_holds k
        exact ((failFold_holds (failWaiter w dead s) dead s ids hh).1).trans h1

/-- Killing one member resumes a different actor's plain park on that member. -/
theorem killOne_resumes_plain (w : World) (D : Description) (dst s : InstId) (k : Cont)
    (hne : s ≠ dst) (hs : s ∈ w.roster) (hl : (w.st s).life = .alive)
    (hph : (w.st s).phase = .parked dst false k) :
    ((killOne w D dst).st s).phase = resumed k := by
  let w1 := readCells D w dst
  have hst1 : w1.st s = w.st s := cellsSt D w dst s
  have hr1 : w1.roster = w.roster := cellsRoster D w dst
  let w2 := refundMsgs w1 (tname dst) (w.st dst).box
  have h2 := refundMsgs_rest w1 (tname dst) (w.st dst).box s
  have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname dst) (w.st dst).box
  let w3 := refundParked w2 (tname dst) (w.st dst).parked
  have h3 := refundParked_rest w2 (tname dst) (w.st dst).parked s
  have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname dst) (w.st dst).parked
  have hph3 : (w3.st s).phase = .parked dst false k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  have hl3 : (w3.st s).life = .alive := by
    rw [h3.2.1, h2.2.1, congrArg (·.life) hst1, hl]
  have hs3 : s ∈ w3.roster := by rw [hr3, hr2, hr1]; exact hs
  let w4 := failWaiters w3 dst
  have h4 : (w4.st s).phase = resumed k := by
    simpa [w4, failWaiters] using failFold_resumes_at w3 dst s k w3.roster hl3 hph3 hs3
  let w5 := forgetSender w4 dst
  have hstab := forget_stable w4 dst s
  have hbody : killOne w D dst =
      setActor w5 dst { w5.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact hstab.1.trans h4

/-- Killing a different actor leaves a park on someone else in place. -/
theorem killOne_keeps_park (w : World) (D : Description) (id s dst : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ id) (hdst : dst ≠ id) (hph : (w.st s).phase = .parked dst c k) :
    ((killOne w D id).st s).phase = .parked dst c k := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
  have hph3 : (w3.st s).phase = .parked dst c k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  let w4 := failWaiters w3 id
  have h4 : (w4.st s).phase = .parked dst c k := by
    simpa [w4, failWaiters] using failFold_keeps_park w3 id s dst c k w3.roster hdst hph3
  let w5 := forgetSender w4 id
  have hstab := forget_stable w4 id s
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact hstab.1.trans h4

/-- A non-member plain-parked on a subtree member ends on that continuation. -/
theorem killFold_plain_phase (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (k : Cont)
    (hnot : isMember D s sub key = false) (hs : s ∈ w.roster) (hls : (w.st s).life = .alive)
    (h : ((w.st s).phase = .parked dst false k ∧ isMember D dst sub key = true ∧
        (w.st dst).life = .alive ∧ dst ∈ ids) ∨ (w.st s).phase = resumed k) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      resumed k := by
  induction ids generalizing w with
  | nil =>
    rcases h with ⟨_, _, _, hmem⟩ | hdone
    · cases hmem
    · simpa using hdone
  | cons j ids ih =>
    simp only [List.foldl_cons]
    rcases h with ⟨hph, hm, hl, hmem⟩ | hdone
    · cases hmem with
      | head =>
        have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by
          simp [hm, hl, beq_iff_eq]
        simp only [hcond, ite_true]
        have hne : s ≠ dst := by
          intro heq
          simpa [heq, hm] using hnot
        have hres := killOne_resumes_plain w D dst s k hne hs hls hph
        have hlife : ((killOne w D dst).st s).life = .alive := by
          rw [(killOne_other_rest w D dst s hne).2.2, hls]
        have hroster : s ∈ (killOne w D dst).roster := by rw [killOne_roster]; exact hs
        exact ih (killOne w D dst) hroster hlife (Or.inr hres)
      | tail _ hmem' =>
        by_cases hjd : j = dst
        · rw [hjd]
          have hcond : (isMember D dst sub key && (w.st dst).life == .alive) = true := by
            simp [hm, hl, beq_iff_eq]
          simp only [hcond, ite_true]
          have hne : s ≠ dst := by
            intro heq
            simpa [heq, hm] using hnot
          have hres := killOne_resumes_plain w D dst s k hne hs hls hph
          have hlife : ((killOne w D dst).st s).life = .alive := by
            rw [(killOne_other_rest w D dst s hne).2.2, hls]
          have hroster : s ∈ (killOne w D dst).roster := by rw [killOne_roster]; exact hs
          exact ih (killOne w D dst) hroster hlife (Or.inr hres)
        · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
          · simp only [hcond, ite_true]
            have hne : s ≠ j := by
              intro heq
              have hparts := (Bool.and_eq_true _ _).mp hcond
              simpa [heq, hparts.1] using hnot
            have hkeep := killOne_keeps_park w D j s dst false k hne (Ne.symm hjd) hph
            have hlife : ((killOne w D j).st s).life = .alive := by
              rw [(killOne_other_rest w D j s hne).2.2, hls]
            have hdstL : ((killOne w D j).st dst).life = .alive := by
              have hnd : dst ≠ j := Ne.symm hjd
              rw [(killOne_other_rest w D j dst hnd).2.2, hl]
            have hroster : s ∈ (killOne w D j).roster := by rw [killOne_roster]; exact hs
            exact ih (killOne w D j) hroster hlife (Or.inl ⟨hkeep, hm, hdstL, hmem'⟩)
          · simp only [hcond, ite_false]
            exact ih w hs hls (Or.inl ⟨hph, hm, hl, hmem'⟩)
    · by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
      · simp only [hcond, ite_true]
        have hne : s ≠ j := by
          intro heq
          have hparts := (Bool.and_eq_true _ _).mp hcond
          simpa [heq, hparts.1] using hnot
        have hh : holdsPhase (w.st s).phase = true := by rw [hdone]; exact resumed_holds k
        have hhold := (killOne_holds w D j s hne hh).1
        have hlife : ((killOne w D j).st s).life = .alive := by
          rw [(killOne_other_rest w D j s hne).2.2, hls]
        have hroster : s ∈ (killOne w D j).roster := by rw [killOne_roster]; exact hs
        exact ih (killOne w D j) hroster hlife (Or.inr (hhold.trans hdone))
      · simp only [hcond, ite_false]
        exact ih w hs hls (Or.inr hdone)

/-- A message from someone else survives killing `id`. -/
theorem killOne_keeps_msg (w : World) (D : Description) (id host : InstId) (m : Msg)
    (hhost : host ≠ id) (hsend : m.sender ≠ id) (hm : m ∈ (w.st host).box) :
    m ∈ ((killOne w D id).st host).box := by
  rcases (killOne_other_rest w D id host hhost).1 with heq | hfilt
  · simpa [heq] using hm
  · rw [hfilt]
    refine List.mem_filter.mpr ⟨hm, ?_⟩
    simp [bne, beq_iff_eq, hsend]

/-- Killing `id` removes `id`'s own bulk messages from every rostered mailbox. -/
theorem killOne_drops_sender (w : World) (D : Description) (id host : InstId) (m : Msg)
    (hsend : m.sender = id) (hs : host ∈ w.roster) :
    m ∉ ((killOne w D id).st host).box := by
  intro hmem
  by_cases hh : host = id
  · rw [hh, (killOne_self w D id).2.2.1] at hmem
    exact (List.not_mem_nil hmem).elim
  · let w1 := readCells D w id
    have hst1 : w1.st host = w.st host := cellsSt D w id host
    have hr1 : w1.roster = w.roster := cellsRoster D w id
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box host
    have hr2 : w2.roster = w1.roster := refundMsgs_roster w1 (tname id) (w.st id).box
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked host
    have hr3 : w3.roster = w2.roster := refundParked_roster w2 (tname id) (w.st id).parked
    let w4 := failWaiters w3 id
    have h4 := failFold_mail w3 id host w3.roster
    have hr4 : w4.roster = w3.roster := by simpa [w4, failWaiters] using failWaiters_roster w3 id w3.roster
    have hbox : (w4.st host).box = (w.st host).box := by
      have h4b : (w4.st host).box = (w3.st host).box := by
        simpa [w4, failWaiters] using h4.1
      exact h4b.trans (h3.2.2.1.trans (h2.2.2.1.trans (congrArg (·.box) hst1)))
    let w5 := forgetSender w4 id
    have hmem4 : host ∈ w4.roster := by rw [hr4, hr3, hr2, hr1]; exact hs
    have hfilt : (w5.st host).box = (w4.st host).box.filter fun m => m.sender != id :=
      forget_box_of_mem w4 id host hmem4 hh
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hh] at hmem
    rw [hfilt, hbox] at hmem
    have hpred := (List.mem_filter.mp hmem).2
    simp [bne, beq_iff_eq, hsend] at hpred

/-- Killing a different actor leaves an await on someone else in place. -/
theorem killOne_keeps_await (w : World) (D : Description) (id s dst : InstId) (k : Cont)
    (hne : s ≠ id) (hdst : dst ≠ id) (hph : (w.st s).phase = .awaitReply dst k) :
    ((killOne w D id).st s).phase = .awaitReply dst k := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
  have hph3 : (w3.st s).phase = .awaitReply dst k := by
    rw [h3.1, h2.1, congrArg (·.phase) hst1, hph]
  let w4 := failWaiters w3 id
  have h4 : (w4.st s).phase = .awaitReply dst k := by
    have hfold : ((failWaiters w3 id).st s).phase = (w3.st s).phase := by
      simpa [failWaiters] using failFold_keeps_await w3 id s dst w3.roster k hdst hph3
    exact hfold.trans hph3
  let w5 := forgetSender w4 id
  have hstab := forget_stable w4 id s
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  exact hstab.1.trans h4

/-- A non-member plain-parked on a live subtree member is resumed by the subtree kill. -/
theorem killSubtree_plain_phase (w : World) (D : Description) (sub : String) (key : Nat)
    (s dst : InstId) (k : Cont) (hnot : isMember D s sub key = false) (hs : s ∈ w.roster)
    (hls : (w.st s).life = .alive) (hph : (w.st s).phase = .parked dst false k)
    (hm : isMember D dst sub key = true) (hl : (w.st dst).life = .alive) (hdst : dst ∈ w.roster) :
    ((killSubtree w D sub key).st s).phase = resumed k := by
  simpa [killSubtree, killMembers] using
    killFold_plain_phase w D sub key w.roster s dst k hnot hs hls (Or.inl ⟨hph, hm, hl, hdst⟩)

/-- A non-member's park on a non-member is not cleared by killing this subtree. -/
theorem killFold_foreign_park (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (c : Bool) (k : Cont)
    (hnot : isMember D s sub key = false)
    (hdst : isMember D dst sub key = false ∨ (w.st dst).life ≠ .alive)
    (hph : (w.st s).phase = .parked dst c k) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .parked dst c k := by
  induction ids generalizing w with
  | nil => simpa using hph
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have hsj : s ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hnot
      have hdj : dst ≠ j := by
        intro hd
        rcases hdst with hnotD | hdead
        · simpa [hd, hparts.1] using hnotD
        · rw [hd] at hdead
          exact hdead (by simpa [beq_iff_eq] using hparts.2)
      have hkeep := killOne_keeps_park w D j s dst c k hsj hdj hph
      have hdst' : isMember D dst sub key = false ∨ ((killOne w D j).st dst).life ≠ .alive := by
        rcases hdst with hnotD | hdead
        · exact Or.inl hnotD
        · exact Or.inr (by rw [(killOne_other_rest w D j dst hdj).2.2]; exact hdead)
      exact ih (killOne w D j) hdst' hkeep
    · simp only [hcond, ite_false]
      exact ih w hdst hph

/-- A non-member's await on a non-member is not cleared by killing this subtree. -/
theorem killFold_foreign_await (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s dst : InstId) (k : Cont)
    (hnot : isMember D s sub key = false)
    (hdst : isMember D dst sub key = false ∨ (w.st dst).life ≠ .alive)
    (hph : (w.st s).phase = .awaitReply dst k) :
    ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase =
      .awaitReply dst k := by
  induction ids generalizing w with
  | nil => simpa using hph
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have hsj : s ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hnot
      have hdj : dst ≠ j := by
        intro hd
        rcases hdst with hnotD | hdead
        · simpa [hd, hparts.1] using hnotD
        · rw [hd] at hdead
          exact hdead (by simpa [beq_iff_eq] using hparts.2)
      have hkeep := killOne_keeps_await w D j s dst k hsj hdj hph
      have hdst' : isMember D dst sub key = false ∨ ((killOne w D j).st dst).life ≠ .alive := by
        rcases hdst with hnotD | hdead
        · exact Or.inl hnotD
        · exact Or.inr (by rw [(killOne_other_rest w D j dst hdj).2.2]; exact hdead)
      exact ih (killOne w D j) hdst' hkeep
    · simp only [hcond, ite_false]
      exact ih w hdst hph

/-- A message whose sender is outside the subtree stays in an outsider's box. -/
theorem killFold_keeps_msg (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (host : InstId) (m : Msg)
    (hhost : isMember D host sub key = false) (hsend : isMember D m.sender sub key = false)
    (hm : m ∈ (w.st host).box) :
    m ∈ ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st host).box := by
  induction ids generalizing w with
  | nil => simpa using hm
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have hh : host ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hhost
      have hs : m.sender ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hsend
      exact ih (killOne w D j) (killOne_keeps_msg w D j host m hh hs hm)
    · simp only [hcond, ite_false]
      exact ih w hm

theorem killSubtree_prio_step (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId) :
    ((killSubtree w D sub key).st s).prio = (w.st s).prio ∨
      ((killSubtree w D sub key).st s).prio = [] := by
  by_cases hl : (w.st s).life = .alive
  · by_cases hl' : ((killSubtree w D sub key).st s).life = .alive
    · exact Or.inl (killSubtree_if_alive w D sub key s hl').2.2.1
    · exact Or.inr (killSubtree_died w D sub key s hl hl').2.2.2.2.1
  · exact Or.inl (killSubtree_if_dead w D sub key s hl).2.2.1

/-- A mailbox the fold never visits keeps its parked list. -/
theorem forgetFold_skip (w : World) (dead s : InstId) (ids : List InstId) (hs : s ∉ ids) :
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
    have htail : s ∉ ids := fun h => hs (List.Mem.tail _ h)
    have hne : s ≠ id := fun h => hs (by simpa [h] using List.Mem.head _)
    by_cases hkeep : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = true
    · simp only [hkeep, ite_true]
      exact ih w htail
    · have hf : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = false := by
        cases hb : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) <;>
          simp_all
      simp only [hf, ite_false]
      let w' := setActor w id { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }
      have hpark : (w'.st s).parked = (w.st s).parked := by simp [w', setActor, hne]
      have hih := ih w' htail
      simpa [w', hpark] using hih

/-- Visiting `s` drops parked entries whose sender is `dead`. -/
theorem forgetFold_parked_eq (w : World) (dead s : InstId) (ids : List InstId) (hs : s ∈ ids) :
    ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w
      else setActor w id { a with parked := ps }) w).st s).parked =
      (w.st s).parked.filter fun p => p.sender != dead := by
  induction ids generalizing w with
  | nil => cases hs
  | cons id ids ih =>
    simp only [List.foldl_cons]
    by_cases hhead : s = id
    · subst hhead
      by_cases hkeep : ((w.st s).parked.filter (fun p => p.sender != dead) == (w.st s).parked) = true
      · simp only [hkeep, ite_true]
        have heq : (w.st s).parked.filter (fun p => p.sender != dead) = (w.st s).parked := by
          simpa [beq_iff_eq] using hkeep
        by_cases htail : s ∈ ids
        · exact (ih w htail).trans (by
            have hidem := List.filter_filter (p := fun p : Parked => p.sender != dead)
              (q := fun p : Parked => p.sender != dead) (l := (w.st s).parked)
            simpa [Bool.and_self, heq] using hidem.symm)
        · have hskip := forgetFold_skip w dead s ids htail
          simpa [heq] using hskip
      · have hf : ((w.st s).parked.filter (fun p => p.sender != dead) == (w.st s).parked) = false := by
          cases hb : ((w.st s).parked.filter (fun p => p.sender != dead) == (w.st s).parked) <;>
            simp_all
        simp only [hf, ite_false]
        let w' := setActor w s { (w.st s) with parked := (w.st s).parked.filter fun p => p.sender != dead }
        have hset : (w'.st s).parked = (w.st s).parked.filter fun p => p.sender != dead := by
          simp [w', setActor]
        have hidem :
            ((w.st s).parked.filter fun p => p.sender != dead).filter (fun p => p.sender != dead) =
              (w.st s).parked.filter fun p => p.sender != dead := by
          have hfilt := List.filter_filter (p := fun p : Parked => p.sender != dead)
            (q := fun p : Parked => p.sender != dead) (l := (w.st s).parked)
          simpa [Bool.and_self] using hfilt
        by_cases htail : s ∈ ids
        · have hih := ih w' htail
          rw [hset] at hih
          exact hih.trans hidem
        · have hskip := forgetFold_skip w' dead s ids htail
          rw [hset] at hskip
          exact hskip
    · have htail : s ∈ ids := by
        rcases List.mem_cons.mp hs with h | h
        · exact absurd h hhead
        · exact h
      by_cases hkeep : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = true
      · simp only [hkeep, ite_true]
        exact ih w htail
      · have hf : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) = false := by
          cases hb : ((w.st id).parked.filter (fun p => p.sender != dead) == (w.st id).parked) <;>
            simp_all
        simp only [hf, ite_false]
        let w' := setActor w id { (w.st id) with parked := (w.st id).parked.filter fun p => p.sender != dead }
        have hpark : (w'.st s).parked = (w.st s).parked := by simp [w', setActor, hhead]
        have hih := ih w' htail
        simpa [w', hpark] using hih

theorem killOne_parked_eq (w : World) (D : Description) (id i : InstId) (hne : i ≠ id)
    (hi : i ∈ w.roster) :
    ((killOne w D id).st i).parked = (w.st i).parked.filter fun p => p.sender != id := by
  let w1 := readCells D w id
  have hst1 : w1.st i = w.st i := cellsSt D w id i
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box i
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked i
  let w4 := failWaiters w3 id
  have h4 := failFold_mail w3 id i w3.roster
  let w5 := forgetSender w4 id
  have hmem : i ∈ w4.roster := by
    have hr : w4.roster = w.roster := by
      simp [w4, w3, w2, w1, failWaiters, failWaiters_roster, refundParked_roster, refundMsgs_roster,
        cellsRoster]
    simpa [hr] using hi
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne]
  have hpark : (w4.st i).parked = (w.st i).parked := by
    have h4p : (w4.st i).parked = (w3.st i).parked := by
      simpa [w4, failWaiters] using h4.2.2
    exact h4p.trans (h3.2.2.2.2.1.trans (h2.2.2.2.2.1.trans (congrArg (·.parked) hst1)))
  have hfilter := forget_parked_of_mem w4 id i hmem hne
  simpa [w5, hpark] using hfilter

/-- A parked entry from someone else survives killing `id`. -/
theorem killOne_keeps_parked (w : World) (D : Description) (id host : InstId) (p : Parked)
    (hhost : host ≠ id) (hs : host ∈ w.roster) (hsend : p.sender ≠ id)
    (hp : p ∈ (w.st host).parked) :
    p ∈ ((killOne w D id).st host).parked := by
  rw [killOne_parked_eq w D id host hhost hs]
  refine List.mem_filter.mpr ⟨hp, ?_⟩
  simp [bne, beq_iff_eq, hsend]

/-- A parked entry whose sender is outside the subtree stays. -/
theorem killFold_keeps_parked (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (host : InstId) (p : Parked)
    (hhost : isMember D host sub key = false) (hsend : isMember D p.sender sub key = false)
    (hs : host ∈ w.roster) (hp : p ∈ (w.st host).parked) :
    p ∈ ((ids.foldl (fun w id =>
        if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st host).parked := by
  induction ids generalizing w with
  | nil => simpa using hp
  | cons j ids ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have hh : host ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hhost
      have hsendj : p.sender ≠ j := by
        intro heq
        simpa [heq, hparts.1] using hsend
      have hmem := killOne_keeps_parked w D j host p hh hs hsendj hp
      have hroster : host ∈ (killOne w D j).roster := by rw [killOne_roster]; exact hs
      exact ih (killOne w D j) hroster hmem
    · simp only [hcond, ite_false]
      exact ih w hs hp

theorem proceed_keeps_life (a : Actor) (k : Cont) : (proceed a k).life = a.life := by
  unfold proceed
  split <;> rfl

theorem resume_keeps_life (a : Actor) (b : Bool) (dst : InstId) : (resumeSender a b dst).life = a.life := by
  unfold resumeSender
  split
  · split
    · rfl
    · exact proceed_keeps_life _ _
  · rfl

/-- Resuming the actor installed at `id` keeps that actor's life. -/
theorem set_resume_life (w : World) (id : InstId) (a : Actor) (b : Bool) (dst : InstId) :
    ((setActor w id (resumeSender a b dst)).st id).life = a.life := by
  simp [setActor, resume_keeps_life]

/-- Resuming one actor leaves every other life untouched. -/
theorem set_resume_life_other (w : World) (id i : InstId) (a : Actor) (b : Bool) (dst : InstId)
    (hi : i ≠ id) : ((setActor w id (resumeSender a b dst)).st i).life = (w.st i).life := by
  simp [setActor, hi]

theorem bump_keeps_life (a : Actor) (dst : String) (delta : Int) : (bumpToken a dst delta).life = a.life := by
  unfold bumpToken
  rfl

/-- Installing an actor of the same life leaves every core's life where it was. -/
theorem set_core_life (w : World) (id : InstId) (a : Actor) (name : String)
    (hl : a.life = (w.st id).life) :
    ((setActor w id a).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  by_cases h : InstId.core name = id
  · simp [setActor, h, hl]
  · simp [setActor, h]

/-- Installing anywhere but this core leaves the core's life alone. -/
theorem set_other_life (w : World) (id : InstId) (a : Actor) (name : String)
    (hne : InstId.core name ≠ id) :
    ((setActor w id a).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  simp [setActor, hne]

theorem credit_core_life (w : World) (tmpl : String) (sender : InstId) (name : String) :
    ((creditSender w tmpl sender).st (InstId.core name)).life =
      (w.st (InstId.core name)).life := by
  simpa [creditSender, bump_keeps_life] using
    set_core_life w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) name (bump_keeps_life _ _ _)

theorem refundMsgs_core_life (w : World) (dstName : String) (ms : List Msg) (name : String) :
    ((refundMsgs w dstName ms).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  induction ms generalizing w with
  | nil => rfl
  | cons m ms ih =>
    rw [refundMsgs, List.foldl_cons]
    exact (ih _).trans (credit_core_life _ _ _ _)

theorem refundParked_core_life (w : World) (dstName : String) (ps : List Parked) (name : String) :
    ((refundParked w dstName ps).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [refundParked, List.foldl_cons]
    exact (ih _).trans (credit_core_life _ _ _ _)

/-- Resuming parked senders does not change a core's life. -/
theorem release_core_life (w : World) (id : InstId) (ps : List Parked) (name : String) :
    ((releaseParked w id ps).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split
    · exact ih _
    · exact (ih _).trans
        (set_core_life w p.sender (resumeSender (w.st p.sender) false id) name (resume_keeps_life _ _ _))

/-- A core that is already dead stays dead while its parked senders resume. -/
theorem release_self_dead (w : World) (id : InstId) (ps : List Parked)
    (h : (w.st id).life = .dead) : ((releaseParked w id ps).st id).life = .dead := by
  induction ps generalizing w with
  | nil => exact h
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split
    · next _ => exact ih _ h
    · next hskip =>
      by_cases hs : id = p.sender
      · simp [hs] at hskip
      · exact ih _ (by simp [setActor, hs, h])

/-- Resuming parked senders does not change anyone's life. -/
theorem releaseParked_life (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    split
    · exact ih _
    · exact (ih _).trans (by
        by_cases hi : i = p.sender
        · simp [hi, setActor, resume_keeps_life]
        · simp [setActor, hi])

/-- A send or call stores mail without changing any core's life. -/
theorem enqueue_core_life (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (name : String) :
    ((enqueueOrPark w D sender dst msg isCall k).st (InstId.core name)).life =
      (w.st (InstId.core name)).life := by
  generalize i : InstId.core name = id
  cases isCall <;>
    (unfold enqueueOrPark
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive]
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor]
           by_cases hi : id = sender <;> simp [hi, chargeSender, bumpToken, issueCall, proceed_keeps_life]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : id = sender
           · simp [hi, chargeSender, bumpToken, issueCall, proceed_keeps_life]
           · by_cases hid : id = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor]
           by_cases hi : id = sender <;> simp [hi, chargeSender, bumpToken, issueCall]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : id = sender
           · simp [hi, chargeSender, bumpToken, issueCall]
           · by_cases hid : id = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
     · rw [if_pos hlive]
       by_cases hi : id = sender
       · simp [hi, setActor, issueCall, finishCall, selectCall, proceed_keeps_life]
       · simp [setActor, hi])

theorem reply_core_life (w : World) (sender : InstId) (k : Cont) (name : String) :
    ((performReply w sender k).st (InstId.core name)).life =
      (w.st (InstId.core name)).life := by
  generalize i : InstId.core name = id
  unfold performReply
  cases hr : k.replyTo with
  | none =>
    by_cases hi : id = sender
    · rw [hi]; simp [setActor, proceed_keeps_life]
    · simp [setActor, hi]
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · by_cases hm : (w.st sender).oweId = some (w.st caller).waitId
        · by_cases hi : id = sender
          · rw [hi]
            by_cases hsc : sender = caller
            · subst hsc
              simp [setActor, hph, hd, hm, finishCall, proceed]
              split <;> split <;> rfl
            · simp [setActor, hph, hd, hm, hsc, proceed]
              split <;> rfl
          · by_cases hc : id = caller
            · rw [hc]
              have hflip : ¬caller = sender := fun h => hi (hc.trans h)
              simp [setActor, hph, hd, hm, hflip, finishCall, proceed]
              split <;> rfl
            · simp [setActor, hi, hc, hph, hd, hm]
        · by_cases hi : id = sender
          · rw [hi]; simp [setActor, proceed_keeps_life, hph, hd, hm]
          · simp [setActor, hi, hph, hd, hm]
      · by_cases hi : id = sender
        · rw [hi]; simp [setActor, proceed_keeps_life, hph, hd]
        · simp [setActor, hi, hph, hd]
    | idle =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | run _ =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | parked _ _ _ =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | awaitEffect _ =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | awaitPeer _ =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | crashed =>
      by_cases hi : id = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]

theorem deliver_life (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    a1.life = a.life ∧ ∀ i, (w1.st i).life = (w.st i).life := by
  unfold deliver at h
  have hcells : ∀ i, ((readCells I.desc w id).st i).life = (w.st i).life :=
    fun i => congrArg Actor.life (cellsSt I.desc w id i)
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, hcells⟩
    · split at h
      · cases h
      · cases h
        split <;> exact ⟨rfl, hcells⟩

/-- `receiveBulk` does not change anyone's life. -/
theorem receiveBulk_keeps_life (I : Impl) (w w' : World) (id i : InstId)
    (h : receiveBulk I w id = some w') : (w'.st i).life = (w.st i).life := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hkeep := deliver_life I w id _ p.msg w1 a1 hdel
          have hset : ((setActor w1 id a1).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]; simpa [setActor] using hkeep.1
            · simpa [setActor, hi] using hkeep.2 i
          have hcred := (credit_phase_life (setActor w1 id a1) (tname id) p.msg.sender i).2
          by_cases hs : i = p.sender
          · rw [hs] at hcred hset ⊢
            simp only [setActor, ite_true, resume_keeps_life]
            exact hcred.trans hset
          · simp only [setActor, hs]
            exact hcred.trans hset
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hkeep := deliver_life I w id _ m w1 a1 hdel
          have hset : ((setActor w1 id a1).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]; simpa [setActor] using hkeep.1
            · simpa [setActor, hi] using hkeep.2 i
          exact ((credit_phase_life (setActor w1 id a1) (tname id) m.sender i).2).trans hset
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hkeep := deliver_life I w id _ m w1 a1 hdel
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hset : ((setActor w1 id admitted).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]; simpa [setActor, admitted] using hkeep.1
            · simpa [setActor, hi] using hkeep.2 i
          have hcred := (credit_phase_life (setActor w1 id admitted) (tname id) m.sender i).2
          by_cases hs : i = p.sender
          · rw [hs] at hcred hset ⊢
            simp only [setActor, ite_true, resume_keeps_life]
            exact hcred.trans hset
          · simp only [setActor, hs]
            exact hcred.trans hset

theorem receivePrio_keeps_life (I : Impl) (w w' : World) (id i : InstId)
    (h : receivePrio I w id = some w') : (w'.st i).life = (w.st i).life := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
    · simp [hp, hready] at h
    · simp [hp, hready] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hkeep := deliver_life I w id _ m w1 a1 hdel
        by_cases hi : i = id
        · rw [hi]; simpa [setActor] using hkeep.1
        · simpa [setActor, hi] using hkeep.2 i

/-- Spawning a peer does not change a core's life. -/
theorem spawn_core_life (I : Impl) (w : World) (template : String) (w' : World) (name : String)
    (h : spawn I w template = some w') :
    (w'.st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo : maySpawnRoot I.desc w template t = true
    · simp only [hgo, ite_true] at h
      by_cases hsub : (t.subtree == "") = true
      · simp only [hsub, ite_true] at h
        cases h
        have hpeer : InstId.core name ≠ InstId.peer template (w.nextIx template) := by
          intro h; cases h
        simp [setActor, cellsSt, hpeer]
      · have hsubF : (t.subtree == "") = false := by simpa [Bool.not_eq_true] using hsub
        simp only [hsubF, ite_false] at h
        cases hk : openSubtreeKey I.desc w t.subtree template with
        | some k =>
          simp [hk] at h
          cases h
          have hpeer : InstId.core name ≠ InstId.peer template k := by
            intro h; cases h
          simp [setActor, cellsSt, hpeer]
        | none =>
          simp [hk] at h
          cases h
          have hpeer : InstId.core name ≠ InstId.peer template (w.nextKey t.subtree) := by
            intro h; cases h
          simp [setActor, cellsSt, hpeer]
    · simp [hgo] at h

theorem releaseOutbound_life (w : World) (dead s : InstId) :
    ((releaseOutbound w dead).st s).life = (w.st s).life := by
  unfold releaseOutbound
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w host =>
        if host == dead then w
        else
          let dropped := (w.st host).parked.filter fun p => p.sender == dead
          if dropped.isEmpty then w
          else
            let w := setActor w host
              { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
            setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) w0).st s).life =
        (w0.st s).life from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro _; rfl
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    split
    · exact ih _
    · rename_i hnot
      split
      · exact ih _
      · refine (ih _).trans ?_
        have hne : host ≠ dead := by
          intro heq
          apply hnot
          simpa [beq_iff_eq] using heq
        by_cases hs : s = dead
        · simp only [setActor, addTokens, hs, ite_true]
          rw [if_neg (Ne.symm hne)]
        · by_cases hh : s = host
          · simp only [setActor, addTokens, hh, ite_true]
            rw [if_neg hne]
          · simp [setActor, hs, hh, addTokens]

/-- A lone release leaves its subject dead. -/
theorem releaseWorld_self_dead (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).life = .dead := by
  simp only [releaseWorld]
  exact release_self_dead _ id a.parked (by simp [setActor])

/-- A lone release of someone else leaves this core's life alone. -/
theorem releaseWorld_core_life (D : Description) (w : World) (id : InstId) (a : Actor) (name : String)
    (hne : InstId.core name ≠ id) :
    ((releaseWorld D w id a).st (InstId.core name)).life =
      (w.st (InstId.core name)).life := by
  simp only [releaseWorld]
  exact (release_core_life _ id a.parked name).trans
    ((set_other_life _ id _ name hne).trans
      ((releaseOutbound_life _ id _).trans
        ((refundParked_core_life _ _ _ name).trans
          ((refundMsgs_core_life _ _ _ name).trans
            (congrArg (fun a => a.life) (cellsSt D w id _))))))

theorem failWaiters_life (w : World) (dead s : InstId) :
    ((failWaiters w dead).st s).life = (w.st s).life := by
  simpa [failWaiters] using failFold_life w dead s w.roster

theorem admitHost_phase (w : World) (dead host s : InstId) :
    ((admitHost w dead host).st s).phase = (w.st s).phase ∧
      ((admitHost w dead host).st s).life = (w.st s).life := by
  unfold admitHost
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · by_cases hs : s = host
      · simp [setActor, hs]
      · simp [setActor, hs]

theorem admitFold_phase (w : World) (dead s : InstId) (ids : List InstId) :
    ((ids.foldl (fun w host => admitHost w dead host) w).st s).phase = (w.st s).phase ∧
      ((ids.foldl (fun w host => admitHost w dead host) w).st s).life = (w.st s).life := by
  induction ids generalizing w with
  | nil => exact ⟨rfl, rfl⟩
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have h1 := admitHost_phase w dead host s
    have h2 := ih (admitHost w dead host)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem admitDead_phase (w : World) (dead s : InstId) :
    ((admitDead w dead).st s).phase = (w.st s).phase ∧
      ((admitDead w dead).st s).life = (w.st s).life := by
  simpa [admitDead] using admitFold_phase w dead s w.roster

theorem admitHost_skip (w : World) (dead host : InstId)
    (h : ∀ p ∈ (w.st host).parked, p.sender ≠ dead) : admitHost w dead host = w := by
  unfold admitHost
  by_cases hhost : (host == dead) = true
  · simp [hhost]
  · have hempty : ((w.st host).parked.filter fun p => p.sender == dead) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp heq
      exact h p hp (beq_iff_eq.mp heq)
    simp [hhost, hempty, List.isEmpty_nil]

theorem admitFold_skip (w : World) (dead : InstId) (ids : List InstId)
    (h : ∀ host p, p ∈ (w.st host).parked → p.sender ≠ dead) :
    ids.foldl (fun w host => admitHost w dead host) w = w := by
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have hstep : admitHost w dead host = w := admitHost_skip w dead host (h host)
    have hpark : ∀ host' p, p ∈ ((admitHost w dead host).st host').parked → p.sender ≠ dead := by
      intro host' p hp
      rw [hstep] at hp
      exact h host' p hp
    rw [hstep]
    exact ih w h

theorem admitDead_skip (w : World) (dead : InstId)
    (h : ∀ host p, p ∈ (w.st host).parked → p.sender ≠ dead) : admitDead w dead = w := by
  simpa [admitDead] using admitFold_skip w dead w.roster h

theorem abortActor_other_life (D : Description) (w : World) (id s : InstId) (a : Actor) (hs : s ≠ id) :
    ((abortActor D w id a).st s).life = (w.st s).life := by
  have hrel : ((releaseWorld D w id a).st s).life = (w.st s).life := by
    simp only [releaseWorld]
    rw [releaseParked_life]
    rw [setActor_other _ id s _ hs]
    rw [releaseOutbound_life]
    rw [(refundParked_rest _ (tname id) a.parked s).2.1]
    rw [(refundMsgs_rest _ (tname id) a.box s).2.1]
    exact congrArg (·.life) (cellsSt D w id s)
  have hfail := failWaiters_life (releaseWorld D w id a) id s
  simpa [abortActor] using
    (admitDead_phase (failWaiters (releaseWorld D w id a) id) id s).2.trans (hfail.trans hrel)

theorem abortActor_core_prev (D : Description) (w : World) (id : InstId) (a : Actor) (name : String)
    (h : ((abortActor D w id a).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  have hfw : ((abortActor D w id a).st (InstId.core name)).life =
      ((releaseWorld D w id a).st (InstId.core name)).life := by
    have hfail := failWaiters_life (releaseWorld D w id a) id (InstId.core name)
    have hadmit := (admitDead_phase (failWaiters (releaseWorld D w id a) id) id
      (InstId.core name)).2
    simpa [abortActor] using hadmit.trans hfail
  rw [hfw] at h
  by_cases hid : InstId.core name = id
  · rw [hid] at h
    have hdead := releaseWorld_self_dead D w id a
    rw [hdead] at h
    cases h
  · exact (releaseWorld_core_life D w id a name hid).symm.trans h

/-- A tombstone that leaves a core alive did not create that life. Crashing the
roster kills every alive core, so the equality of lives does not hold. -/
theorem tombstone_core_life (D : Description) (w : World) (child : InstId) (name : String)
    (h : ((enqueueTombstone D w child).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  unfold enqueueTombstone at h
  cases hsup : supervisorOf D child with
  | none => simpa [hsup] using h
  | some parent =>
    simp only [hsup] at h
    by_cases hbad : ((w.st parent).life != .alive ||
        (tombstoneMsg D (w.st parent) child).label == "" ||
        decide (prioLoad (w.st parent).prio >= capPrio D w.N parent)) = true
    · simp only [hbad, ite_true, crashWorld] at h
      by_cases hmem : decide (InstId.core name ∈ w.roster) = true
      · simp only [hmem, ite_true, crashActor] at h
        by_cases hgo : ((w.st (InstId.core name)).life == .alive ||
            (w.st (InstId.core name)).life == .shuttingDown) = true
        · simp [hgo] at h
        · simpa [hgo] using h
      · simpa [hmem] using h
    · have hok : ((w.st parent).life != .alive ||
          (tombstoneMsg D (w.st parent) child).label == "" ||
          decide (prioLoad (w.st parent).prio >= capPrio D w.N parent)) = false := by
        simpa [Bool.not_eq_true] using hbad
      simp only [hok, ite_false] at h
      by_cases hi : InstId.core name = parent
      · rw [hi] at h ⊢
        simp [setActor] at h
        exact h
      · simpa [setActor, hi] using h

theorem abortDesc_core_prev (fuel : Nat) (D : Description) (w : World) (parent : InstId)
    (name : String) (h : ((abortDesc fuel D w parent).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  induction fuel generalizing w parent with
  | zero => simpa [abortDesc] using h
  | succ fuel ih =>
    simp only [abortDesc] at h
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st (InstId.core name)).life = .alive →
          (w0.st (InstId.core name)).life = .alive := by
      intro ids
      induction ids with
      | nil => intro _ h0; exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = true
        · simp only [hcond, ite_true] at h0
          let wDesc := abortDesc fuel D w0 child
          let wAct := abortActor D wDesc child (wDesc.st child)
          have hActAlive : (wAct.st (InstId.core name)).life = .alive := ihids wAct h0
          have hDescAlive :=
            abortActor_core_prev D wDesc child (wDesc.st child) name hActAlive
          exact ih w0 child hDescAlive
        · have hf : (isChild D parent child && (w0.st child).life == .alive && childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive && childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf, ite_false] at h0
          exact ihids w0 h0
    exact hfold w.roster w h

/-- A tombstone step that leaves `i` alive did not create that life. A crash,
a missing label, or a full lane does not leave an alive actor that was absent. -/
theorem enqueueTombstone_life (D : Description) (w : World) (child i : InstId)
    (h : ((enqueueTombstone D w child).st i).life = .alive) : (w.st i).life = .alive := by
  unfold enqueueTombstone at h
  cases hsup : supervisorOf D child with
  | none => simpa [hsup] using h
  | some parent =>
    simp only [hsup] at h
    by_cases hbad : ((w.st parent).life != .alive ||
        (tombstoneMsg D (w.st parent) child).label == "" ||
        decide (prioLoad (w.st parent).prio >= capPrio D w.N parent)) = true
    · simp only [hbad, ite_true, crashWorld] at h
      by_cases hmem : decide (i ∈ w.roster) = true
      · simp only [hmem, ite_true, crashActor] at h
        by_cases hgo : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
        · simp [hgo] at h
        · simpa [hgo] using h
      · simpa [hmem] using h
    · have hok : ((w.st parent).life != .alive ||
          (tombstoneMsg D (w.st parent) child).label == "" ||
          decide (prioLoad (w.st parent).prio >= capPrio D w.N parent)) = false := by
        simpa [Bool.not_eq_true] using hbad
      simp only [hok, ite_false] at h
      by_cases hi : i = parent
      · rw [hi] at h ⊢
        simp [setActor] at h
        exact h
      · simpa [setActor, hi] using h

theorem markShutdown_prev (w : World) (id i : InstId)
    (h : ((markShutdown w id).st i).life = .alive) : (w.st i).life = .alive := by
  unfold markShutdown at h
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true, setActor] at h
    by_cases hi : i = id
    · simp [hi] at h
    · simpa [hi] using h
  · simpa [hlive] using h

theorem shutdownActor_prev (D : Description) (w : World) (id i : InstId)
    (h : ((shutdownActor D w id).st i).life = .alive) : (w.st i).life = .alive := by
  have hmark : ((markShutdown w id).st i).life = .alive :=
    enqueueTombstone_life D (markShutdown w id) id i (by simpa [shutdownActor] using h)
  exact markShutdown_prev w id i hmark

theorem shutdownDesc_core_prev (fuel : Nat) (D : Description) (w : World) (parent : InstId)
    (name : String) (h : ((shutdownDesc fuel D w parent).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  induction fuel generalizing w parent with
  | zero => simpa [shutdownDesc] using h
  | succ fuel ih =>
    simp only [shutdownDesc] at h
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := shutdownDesc fuel D w child
        shutdownActor D w child
      else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st (InstId.core name)).life = .alive →
          (w0.st (InstId.core name)).life = .alive := by
      intro ids
      induction ids with
      | nil => intro _ h0; exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive &&
            childTerminable D child) = true
        · simp only [hcond, ite_true] at h0
          let wDesc := shutdownDesc fuel D w0 child
          have hActAlive : ((shutdownActor D wDesc child).st (InstId.core name)).life = .alive :=
            ihids _ h0
          have hDescAlive := shutdownActor_prev D wDesc child (InstId.core name) hActAlive
          exact ih w0 child hDescAlive
        · have hf : (isChild D parent child && (w0.st child).life == .alive &&
              childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive &&
                childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf, ite_false] at h0
          exact ihids w0 h0
    exact hfold w.roster w h

theorem crashWorld_prev (w : World) (i : InstId)
    (h : ((crashWorld w).st i).life = .alive) : (w.st i).life = .alive := by
  simp only [crashWorld] at h
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp only [hmem, ite_true, crashActor] at h
    by_cases hgo : ((w.st i).life == .alive || (w.st i).life == .shuttingDown) = true
    · simp [hgo] at h
    · simpa [hgo] using h
  · simpa [hmem] using h

/-- A cell wake that leaves a core alive did not create that life. A full lane
crashes the roster instead of dropping the wake. -/
theorem tryWake_core_life (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (name : String)
    (h : ((tryWake D w dstId label writer).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  unfold tryWake offerPrio at h
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip] at h
    exact h
  · have hgo : ((w.st dstId).life != .alive ||
        (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      simpa [Bool.not_eq_true] using hskip
    simp only [hgo, ite_false] at h
    by_cases hfull : decide (prioLoad (w.st dstId).prio >= capPrio D w.N dstId) = true
    · simp only [hfull, ite_true] at h
      exact crashWorld_prev w (InstId.core name) h
    · have hroom : decide (prioLoad (w.st dstId).prio >= capPrio D w.N dstId) = false := by
        simpa [Bool.not_eq_true] using hfull
      simp only [hroom, ite_false] at h
      by_cases hi : InstId.core name = dstId
      · rw [hi] at h ⊢
        simp [setActor] at h
        exact h
      · simpa [setActor, hi] using h

theorem wake_core_life (D : Description) (w : World) (dst label : String) (writer : InstId)
    (name : String)
    (h : ((wakeReaders D w dst label writer).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  unfold wakeReaders at h
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w id => tryWake D w id label writer) w0).st (InstId.core name)).life = .alive →
      (w0.st (InstId.core name)).life = .alive from
    this (readersOf w dst) w h
  intro ids
  induction ids with
  | nil =>
    intro _ h0
    exact h0
  | cons j js ih =>
    intro w0 h0
    rw [List.foldl_cons] at h0
    exact tryWake_core_life D w0 j label writer name (ih _ h0)

/-- If `exec` leaves a core alive, it was already alive. A core's own lone
`terminate` is the only life change, and that one ends dead. -/
theorem markTree_prev (fuel : Nat) (D : Description) (w : World) (id i : InstId)
    (h : ((markTree fuel D w id).st i).life = .alive) : (w.st i).life = .alive := by
  induction fuel generalizing w id with
  | zero => simpa [markTree] using h
  | succ fuel ih =>
    simp only [markTree] at h
    let step (w : World) (child : InstId) : World :=
      if isChild D id child then markTree fuel D w child else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st i).life = .alive → (w0.st i).life = .alive := by
      intro ids
      induction ids with
      | nil => intro _ h0; exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hc : isChild D id child = true
        · simp only [hc, ite_true] at h0
          exact ih w0 child (ihids _ h0)
        · have hf : isChild D id child = false := by
            cases hb : isChild D id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf, ite_false] at h0
          exact ihids w0 h0
    exact markShutdown_prev w id i (hfold (markShutdown w id).roster (markShutdown w id) h)

/-- Beginning to shut down does not bring a core to life. -/
theorem terminateStage_core_prev (D : Description) (w : World) (id : InstId) (a : Actor)
    (name : String) (h : ((terminateStage D w id a).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  have hmark : ((markTree w.roster.length D w id).st (InstId.core name)).life = .alive :=
    enqueueTombstone_life D (markTree w.roster.length D w id) id (InstId.core name)
      (by simpa [terminateStage] using h)
  exact markTree_prev _ D w id (InstId.core name) hmark

theorem abortChildren_prev (D : Description) (w : World) (parent i : InstId)
    (h : ((abortChildren D w parent).st i).life = .alive) : (w.st i).life = .alive := by
  unfold abortChildren at h
  let step (w0 : World) (child : InstId) : World :=
    if isChild D parent child && (w0.st child).life == .alive then
      let w0 := markTree w0.roster.length D w0 child
      enqueueTombstone D w0 child
    else w0
  have hfold : ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl step w0).st i).life = .alive → (w0.st i).life = .alive := by
    intro ids
    induction ids with
    | nil => intro _ h0; exact h0
    | cons child ids ihids =>
      intro w0 h0
      simp only [List.foldl_cons, step] at h0
      by_cases hc : (isChild D parent child && (w0.st child).life == .alive) = true
      · simp only [hc, ite_true] at h0
        have hts := enqueueTombstone_life D (markTree w0.roster.length D w0 child) child i
          (ihids _ h0)
        exact markTree_prev _ D w0 child i hts
      · have hf : (isChild D parent child && (w0.st child).life == .alive) = false := by
          cases hb : isChild D parent child && (w0.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf, ite_false] at h0
        exact ihids w0 h0
  exact hfold w.roster w h

theorem spawnChild_core_life (I : Impl) (w w' : World) (parent : InstId) (child name : String)
    (h : spawnChild I w parent child = some w') :
    (w'.st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  unfold spawnChild at h
  cases parent with
  | core _ => simp at h
  | peer parentName k =>
    cases ht : templateOf I.desc child with
    | none => simp [ht] at h
    | some t =>
      simp only [ht] at h
      by_cases hgo : (t.multiplicity == .perPeer &&
          isChild I.desc (InstId.peer parentName k) (InstId.peer child k) &&
          (w.st (InstId.peer child k)).life == .absent) = true
      · simp only [hgo, ite_true] at h
        cases h
        have hpeer : InstId.core name ≠ InstId.peer child k := by
          intro h; cases h
        simp [setActor, cellsSt, hpeer]
      · simp [hgo] at h

theorem exec_core_alive_prev (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (name : String) (ha : a.life = (w.st id).life)
    (hl : ((execRun I w id a k).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  classical
  by_cases hliveB : (a.life == .alive) = true
  · cases hk : k.rest with
  | nil =>
    simp [execRun, hliveB, hk] at hl
    have hset := set_core_life w id { a with phase := .idle, typestate := k.toState } name (by simp [ha])
    exact hset.symm.trans hl
  | cons e es =>
    cases e with
    | send dst label hint =>
      simp [execRun, hliveB, hk] at hl
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr, noteStale] at hl
        have hset := set_core_life w id (proceed a (afterHead k)) name (by simp [proceed_keeps_life, ha])
        exact hset.symm.trans hl
      | some dstId =>
        simp [hr] at hl
        exact (enqueue_core_life w I.desc id dstId _ false (afterHead k) name).symm.trans hl
    | trySend dst label hint onFull onGone =>
      simp [execRun, hliveB, hk] at hl
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr, noteStale] at hl
        have hset := set_core_life w id (proceed a { afterHead k with rest := onGone }) name
          (by simp [proceed_keeps_life, ha])
        exact hset.symm.trans hl
      | some dstId =>
        simp [hr] at hl
        split at hl
        · exact (enqueue_core_life w I.desc id dstId _ false (afterHead k) name).symm.trans hl
        · split at hl
          · have hset := set_core_life w id (proceed a { afterHead k with rest := onFull }) name
              (by simp [proceed_keeps_life, ha])
            exact hset.symm.trans hl
          · have hset := set_core_life w id (proceed a { afterHead k with rest := onGone }) name
              (by simp [proceed_keeps_life, ha])
            exact hset.symm.trans hl
    | call dst label hint onNotAdmitted onTimedOut =>
      simp [execRun, hliveB, hk] at hl
      cases hr : resolveId I.desc id dst with
      | none =>
        simp [hr, noteStale] at hl
        have hset := set_core_life (noteStale w id dst) id
            (finishCall (issueCall a)
              { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
              .notAdmitted) name
            (by simp [finishCall, selectCall, proceed_keeps_life, issueCall, ha, noteStale_st])
        simpa [noteStale_st] using hset.symm.trans hl
      | some dstId =>
        simp [hr] at hl
        exact (enqueue_core_life w I.desc id dstId _ true
            { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
            name).symm.trans hl
    | reply =>
      simp [execRun, hliveB, hk] at hl
      exact (reply_core_life w id k name).symm.trans hl
    | selfSchedule label =>
      simp [execRun, hliveB, hk] at hl
      split at hl
      · have hset := set_core_life w id (proceed a (afterHead k)) name (by simp [proceed_keeps_life, ha])
        exact hset.symm.trans hl
      · split at hl
        · let msg : Msg :=
            { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
          have hset := set_core_life w id
            (proceed { a with prio := upsertPrio a.prio msg, nextMid := a.nextMid + 1 } (afterHead k)) name
            (by simp [proceed_keeps_life, ha, msg])
          exact hset.symm.trans hl
        · exact crashWorld_prev w (InstId.core name) hl
    | cell dst label value =>
      simp [execRun, hliveB, hk] at hl
      let c : Cell := { value := max (w.cell dst label).value value, dirty := true }
      split at hl
      · have hset := set_core_life (setCell w dst label c) id (proceed (w.st id) (afterHead k)) name
          (by simp [setCell, c, proceed_keeps_life])
        simpa [setCell, c] using hset.symm.trans hl
      · have hstep := wake_core_life I.desc
          (setActor (setCell w dst label c) id (proceed (w.st id) (afterHead k))) dst label id name hl
        have hset := set_core_life (setCell w dst label c) id (proceed (w.st id) (afterHead k)) name
          (by simp [setCell, c, proceed_keeps_life])
        simpa [setCell, c] using hset.symm.trans hstep
    | internal =>
      simp [execRun, hliveB, hk] at hl
      exact (set_core_life w id { a with phase := .awaitEffect (afterHead k) } name (by simp [ha])).symm.trans hl
    | peer _ =>
      simp [execRun, hliveB, hk] at hl
      exact (set_core_life w id { a with phase := .awaitPeer _ } name (by simp [ha])).symm.trans hl
    | abort =>
      simp [execRun, hliveB, hk] at hl
      exact abortChildren_prev I.desc w id (InstId.core name) hl
    | spawn child =>
      simp [execRun, hliveB, hk] at hl
      cases hs : spawnChild I w id child with
      | none =>
        simp [hs] at hl
        exact crashWorld_prev w (InstId.core name) hl
      | some w' =>
        simp [hs] at hl
        have hborn := spawnChild_core_life I w w' id child name hs
        have hset := set_core_life w' id (proceed (w'.st id) (afterHead k)) name
          (by simp [proceed_keeps_life])
        exact hborn.symm.trans (hset.symm.trans hl)
    | terminate =>
      have hprop : a.life = .alive := by simpa [beq_iff_eq] using hliveB
      have hstep := exec_term_step I w id a k hprop ⟨es, hk⟩
      generalize hw : execRun I w id a k = wR at hstep hl
      have H : (wR.st (InstId.core name)).life = .alive → (w.st (InstId.core name)).life = .alive := by
        cases hstep with
        | fall =>
          intro h
          exact crashWorld_prev w (InstId.core name) h
        | crash _ _ _ _ =>
          intro h
          exact crashWorld_prev w (InstId.core name) h
        | lone _ _ _ _ _ _ =>
          intro h
          exact shutdownActor_prev I.desc w id (InstId.core name) h
        | tree _ _ _ _ =>
          intro h
          exact terminateStage_core_prev I.desc w id a name h
        | cascade _ _ _ _ _ _ =>
          intro h
          exact terminateStage_core_prev I.desc w id a name h
      exact H hl
  · simp [execRun, hliveB] at hl
    exact hl

theorem finishCall_life (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).life = a.life := by
  cases r <;> simp [finishCall, selectCall, proceed_keeps_life]

theorem detachBox_life (a : Actor) (c : InstId) : (detachBox a c).life = a.life := by
  simp [detachBox]

theorem detachReply_life (a : Actor) (c : InstId) (n : Nat) :
    (detachReply a c n).life = a.life := by
  unfold detachReply
  split <;> rfl

theorem setActor_keeps_life (w : World) (id i : InstId) (a : Actor)
    (h : a.life = (w.st id).life) : ((setActor w id a).st i).life = (w.st i).life := by
  by_cases hi : i = id
  · simp [setActor, hi, h]
  · simp [setActor, hi]

theorem creditFold_life (w : World) (name : String) (s : InstId) (ps : List Parked) (i : InstId) :
    ((ps.foldl (fun w _ => creditSender w name s) w).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons _ ps ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (credit_phase_life w name s i).2

theorem refundCall_life (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).life = (w.st i).life := by
  unfold refundParkedCall
  dsimp only
  split
  · rfl
  · rename_i hne
    have hset := setActor_keeps_life w dst i
      { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
      (by simp)
    exact (creditFold_life _ (tname dst) caller _ i).trans hset

/-- A call deadline does not change anyone's life. -/
theorem callTimeout_life (w w' : World) (id i : InstId) (h : callTimeout w id = some w') :
    (w'.st i).life = (w.st i).life := by
  unfold callTimeout at h
  dsimp only at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hgo : ((w.st id).life != .alive) = false := by simpa [Bool.not_eq_true] using hlive
    simp only [hgo, ite_false] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      cases h
      have hhost : (detachReply (detachBox (w.st dst) id) id (w.st id).waitId).life = (w.st dst).life := by
        rw [detachReply_life, detachBox_life]
      have h1 := setActor_keeps_life w dst i _ hhost
      have hfin : (finishCall ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id)
          k .timedOut).life =
          ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id).life :=
        finishCall_life _ _ _
      exact (setActor_keeps_life _ id i _ hfin).trans h1
    | parked dst isCall k =>
      cases isCall with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        cases h
        have h1 := refundCall_life w id dst i
        have hfin := finishCall_life ((refundParkedCall w id dst).st id) k .notAdmitted
        exact (setActor_keeps_life _ id i _ hfin).trans h1
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer k =>
      simp only [hph] at h
      cases h
      exact setActor_keeps_life w id i _
        (proceed_keeps_life (w.st id) { k with rest := k.onTimeout })
    | crashed => simp [hph] at h

/-- A core that is alive after a step was alive before it. No step creates a core. -/
theorem apply_core_prev (I : Impl) (w w' : World) (a : Action) (name : String)
    (h : apply I a w = some w') (hl : (w'.st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  cases a with
  | callTimeout id =>
    exact (callTimeout_life w w' id (InstId.core name) (by simpa [apply] using h)).symm.trans hl
  | stutter =>
    simp [apply] at h
    cases h.2
    exact hl
  | ingress dst label =>
    have hlife := (ingress_phase I w w' dst label (InstId.core name) (by simpa [apply] using h)).2.1
    exact hlife.symm.trans hl
  | finish id =>
    obtain ⟨k, _, hw⟩ := finish_proceed I w w' id (by simpa [apply] using h)
    rw [hw] at hl
    exact (set_core_life w id (proceed (w.st id) k) name (proceed_keeps_life _ _)).symm.trans hl
  | spawn template =>
    exact (spawn_core_life I w template w' name (by simpa [apply] using h)).symm.trans hl
  | recvBulk id =>
    exact (receiveBulk_keeps_life I w w' id (InstId.core name) (by simpa [apply] using h)).symm.trans hl
  | recvPrio id =>
    exact (receivePrio_keeps_life I w w' id (InstId.core name) (by simpa [apply] using h)).symm.trans hl
  | exec id =>
    have hhead : execHead I w id = some w' := by simpa [apply] using h
    unfold execHead at hhead
    by_cases hshut : ((w.st id).life == .shuttingDown) = true
    · simp only [hshut, ite_true] at hhead
      cases hhead
      by_cases hid : id = InstId.core name
      · rw [hid] at hl
        rw [releaseWorld_self_dead I.desc w (InstId.core name) (w.st (InstId.core name))] at hl
        cases hl
      · have hne : InstId.core name ≠ id := fun h => hid h.symm
        exact (releaseWorld_core_life I.desc w id (w.st id) name hne).symm.trans hl
    · have hnot : ((w.st id).life == .shuttingDown) = false := by
        simpa [Bool.not_eq_true] using hshut
      simp only [hnot, ite_false] at hhead
      by_cases hlive : (w.st id).life = .alive
      · simp [hlive] at hhead
        cases hph : (w.st id).phase with
        | run k =>
          simp [hph] at hhead
          cases hhead
          exact exec_core_alive_prev I w id (w.st id) k name rfl hl
        | idle => simp [hph] at hhead
        | parked _ _ _ => simp [hph] at hhead
        | awaitReply _ _ => simp [hph] at hhead
        | awaitEffect _ => simp [hph] at hhead
        | awaitPeer _ => simp [hph] at hhead
        | crashed => simp [hph] at hhead
      · simp [hlive, bne] at hhead

/-- Reading cells does not change actor state. -/
theorem reads_keep_st (D : Description) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun w id => readCells D w id) w).st i) = w.st i := by
  induction ids generalizing w with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons]
    exact (ih _).trans (cellsSt D w j i)

/-- An alive core of the initial world is one of the multiplicity-one roles. -/
theorem init_core_mem (I : Impl) (N : Nat) (name : String)
    (hl : ((initWorld I N).st (InstId.core name)).life = .alive) :
    InstId.core name ∈ coreRoster I.desc := by
  have hst : ((initWorld I N).st (InstId.core name)) =
      if (coreRoster I.desc).contains (InstId.core name) then initActor I.desc (InstId.core name)
      else absentActor := by
    simp only [initWorld]
    simpa using reads_keep_st I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }
      (InstId.core name)
  by_cases hc : (coreRoster I.desc).contains (InstId.core name) = true
  · rw [List.contains] at hc
    exact List.elem_iff.mp hc
  · rw [hst] at hl
    rw [ite_eq_right hc] at hl
    simp [absentActor] at hl

/-- Five children, one core parent, a priority lane of capacity 4. -/
def overflowTpl (name : String) (mult : Multiplicity) (sup tomb : String) : Template where
  name := name
  multiplicity := mult
  capacity := .ofNat 1
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 4
  states := ["idle"]
  initial := "idle"
  terminable := false
  untimedPeer := false
  mustFit := true
  subtree := "net"
  supervisor := sup
  tombstone := tomb

def overflowDesc : Description where
  name := "overflow"
  freshNames := true
  templates := overflowTpl "parent" .one "" "" ::
    (List.range 5).map fun n => overflowTpl s!"c{n}" .perPeer "parent" s!"t{n}"
  edges := []
  compatibility := .all
  steps := []

def overflowIds : List InstId :=
  .core "parent" :: (List.range 5).map fun n => .peer s!"c{n}" 0

def overflowActor : Actor where
  life := .alive
  typestate := "idle"
  phase := .idle
  box := []
  prio := []
  parked := []
  tokens := fun _ => 0

def overflowWorld : World where
  N := 1
  roster := overflowIds
  nextIx := fun _ => 0
  st := fun i => if decide (i ∈ overflowIds) then overflowActor else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- Enqueue one tombstone from each of the five children. The fifth finds a
lane of capacity 4 already full. -/
def overflowRun : World :=
  (List.range 5).foldl (fun w n => enqueueTombstone overflowDesc w (.peer s!"c{n}" 0)) overflowWorld

def worldCrashedB (w : World) : Bool :=
  w.roster.any fun id => (w.st id).life == .dead && (w.st id).phase == .crashed

theorem worldCrashed_of_b (w : World) (h : worldCrashedB w = true) : WorldCrashed w := by
  unfold worldCrashedB at h
  simp [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨id, hmem, hlife, hph⟩ := h
  exact ⟨id, hmem, hlife, hph⟩

/-- Five tombstones on a lane of capacity 4 end in `crashed`. -/
theorem tombstones_exceed_capPrio : WorldCrashed overflowRun :=
  worldCrashed_of_b overflowRun (by decide)

/-- Each call outcome runs one continuation. `Reply` keeps `rest`.
`NotAdmitted` runs `onNotAdmitted`. `TimedOut` runs `onTimedOut`. -/
theorem finishCall_cont (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).lastCall = some (a.waitId, r) ∧
      (finishCall a k r).phase = (proceed a (selectCall k r)).phase ∧
      (selectCall k r).rest =
        match r with
        | .reply => k.rest
        | .notAdmitted => k.onNotAdmitted
        | .timedOut => k.onTimedOut := by
  cases r <;> simp [finishCall, selectCall]

theorem proceed_not_await (a : Actor) (k k' : Cont) (d : InstId) :
    (proceed a k).phase ≠ .awaitReply d k' := by
  cases hr : k.rest <;> intro h <;> simp [proceed, hr] at h

theorem detachBox_id (a : Actor) (caller : InstId) :
    (detachBox a caller).waitId = a.waitId ∧ (detachBox a caller).life = a.life := by
  simp [detachBox]

theorem detachReply_id (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply a caller cid).waitId = a.waitId ∧ (detachReply a caller cid).life = a.life := by
  unfold detachReply
  split <;> simp

theorem detachReply_box (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply a caller cid).box = a.box := by
  unfold detachReply
  split <;> rfl

theorem proceed_phase_actor (a b : Actor) (k : Cont) :
    (proceed a k).phase = (proceed b k).phase := by
  cases hr : k.rest <;> simp [proceed, hr]

/-- `TimedOut` ends an `awaitReply` on `onTimedOut`. The callee stays at the
same life: the deadline does not dequeue the request. -/
theorem await_timeout_end (w w' : World) (c d : InstId) (k : Cont)
    (hl : (w.st c).life = .alive) (hph : (w.st c).phase = .awaitReply d k)
    (h : callTimeout w c = some w') :
    (w'.st c).lastCall = some ((w.st c).waitId, CallResult.timedOut) ∧
      (w'.st c).phase = (proceed (w.st c) (selectCall k CallResult.timedOut)).phase ∧
      (w'.st d).life = (w.st d).life := by
  unfold callTimeout at h
  have hlive : ((w.st c).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, ite_false, hph] at h
  let host := detachReply (detachBox (w.st d) c) c (w.st c).waitId
  let w1 := setActor w d host
  have hw' : w' = setActor w1 c (finishCall (w1.st c) k CallResult.timedOut) := by
    simpa [host, w1] using h.symm
  have hwait : (w1.st c).waitId = (w.st c).waitId := by
    by_cases hcd : c = d
    · subst hcd
      simp [w1, setActor_self, host, detachReply_id, detachBox_id]
    · simp [w1, setActor_other w d c host hcd]
  have hlifeC : (w1.st c).life = (w.st c).life := by
    by_cases hcd : c = d
    · subst hcd
      simp [w1, setActor_self, host, detachReply_id, detachBox_id]
    · simp [w1, setActor_other w d c host hcd]
  have hself : (w'.st c) = finishCall (w1.st c) k CallResult.timedOut := by
    rw [hw', setActor_self]
  refine ⟨?_, ?_, ?_⟩
  · simp [hself, finishCall, hwait]
  · have hphP := proceed_phase_actor (w1.st c) (w.st c) (selectCall k CallResult.timedOut)
    simpa [hself, finishCall, selectCall] using hphP
  · by_cases hcd : c = d
    · subst hcd
      rw [hw', setActor_self, finishCall_life, hlifeC]
    · have hdc : d ≠ c := fun h => hcd h.symm
      rw [hw', setActor_other w1 c d _ hdc]
      simp [w1, setActor_self, host, detachReply_id, detachBox_id]

/-- The deadline leaves the callee's mailbox mapped by `detachMsg`. It does not
dequeue the request. -/
theorem await_timeout_box (w w' : World) (c d : InstId) (k : Cont)
    (hl : (w.st c).life = .alive) (hph : (w.st c).phase = .awaitReply d k)
    (h : callTimeout w c = some w') (hcd : c ≠ d) :
    (w'.st d).box = (detachBox (w.st d) c).box := by
  unfold callTimeout at h
  have hlive : ((w.st c).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, ite_false, hph] at h
  let host := detachReply (detachBox (w.st d) c) c (w.st c).waitId
  let w1 := setActor w d host
  have hw' : w' = setActor w1 c (finishCall (w1.st c) k CallResult.timedOut) := by
    simpa [host, w1] using h.symm
  have hdc : d ≠ c := fun h => hcd h.symm
  rw [hw', setActor_other w1 c d _ hdc]
  simp [w1, setActor_self, host, detachReply_box]

/-- A matching reply ends that `awaitReply` on `rest`. The effect's `replyTo`
names the caller, the caller is waiting on this sender, and the owed id is
the caller's wait id. -/
theorem await_reply_end (w : World) (sender c d : InstId) (k ck : Cont)
    (hreply : k.replyTo = some c)
    (hph : (w.st c).phase = .awaitReply d ck)
    (hd : d = sender) (howe : (w.st sender).oweId = some (w.st c).waitId)
    (hns : c ≠ sender) :
    ((performReply w sender k).st c).lastCall = some ((w.st c).waitId, CallResult.reply) ∧
      ((performReply w sender k).st c).phase =
        (proceed (w.st c) (selectCall ck CallResult.reply)).phase := by
  unfold performReply
  rw [hreply]
  cases hphase : (w.st c).phase with
  | awaitReply dst ck' =>
    have heq : Phase.awaitReply d ck = Phase.awaitReply dst ck' := hph.symm.trans hphase
    injection heq with hdst hck
    subst hck
    have hds : dst = sender := hdst.symm.trans hd
    simp [setActor, hphase, hds, howe, hns, finishCall, selectCall]
  | idle | run _ | parked _ _ _ | awaitEffect _ | awaitPeer _ | crashed =>
    cases hph.symm.trans hphase

/-- Refunding a parked call does not change the caller's wait id or life. -/
theorem refundCall_wait (w : World) (caller dst : InstId) :
    ((refundParkedCall w caller dst).st caller).waitId = (w.st caller).waitId ∧
      ((refundParkedCall w caller dst).st caller).life = (w.st caller).life := by
  unfold refundParkedCall
  dsimp only
  let pred := fun p : Parked => p.sender == caller && p.isCall
  let keep := (w.st dst).parked.filter fun p => !pred p
  split
  · exact ⟨rfl, rfl⟩
  · let base := setActor w dst { (w.st dst) with parked := keep }
    have hbase : (base.st caller).waitId = (w.st caller).waitId ∧
        (base.st caller).life = (w.st caller).life := by
      by_cases hi : caller = dst
      · simp [base, hi, setActor_self]
      · simp [base, setActor_other w dst caller _ hi]
    have hfold : ∀ (ps : List Parked) (w0 : World),
        (w0.st caller).waitId = (w.st caller).waitId →
        (w0.st caller).life = (w.st caller).life →
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st caller).waitId =
          (w.st caller).waitId) ∧
        (((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st caller).life =
          (w.st caller).life) := by
      intro ps
      induction ps with
      | nil =>
        intro w0 hw hl
        exact ⟨hw, hl⟩
      | cons p ps ih =>
        intro w0 hw hl
        simp only [List.foldl_cons]
        have hcredit :
            ((creditSender w0 (tname dst) caller).st caller).waitId = (w0.st caller).waitId ∧
              ((creditSender w0 (tname dst) caller).st caller).life = (w0.st caller).life := by
          simp [creditSender, setActor_self, bumpToken]
        exact ih (creditSender w0 (tname dst) caller) (hcredit.1.trans hw) (hcredit.2.trans hl)
    have hstep := hfold ((w.st dst).parked.filter pred) base hbase.1 hbase.2
    simpa [base, keep, pred, Bool.not_and] using hstep

/-- `NotAdmitted` ends a parked call on `onNotAdmitted`. It is not how an
`awaitReply` ends. -/
theorem parked_not_admitted (w w' : World) (c d : InstId) (k : Cont)
    (hl : (w.st c).life = .alive) (hph : (w.st c).phase = .parked d true k)
    (h : callTimeout w c = some w') :
    (w'.st c).lastCall = some ((w.st c).waitId, CallResult.notAdmitted) ∧
      (w'.st c).phase =
        (proceed (w.st c) (selectCall k CallResult.notAdmitted)).phase := by
  unfold callTimeout at h
  have hlive : ((w.st c).life != .alive) = false := by simp [hl, bne]
  simp only [hlive, ite_false, hph] at h
  have hw' : w' = setActor (refundParkedCall w c d) c
      (finishCall ((refundParkedCall w c d).st c) k CallResult.notAdmitted) := by
    simpa using h.symm
  have hkeep := refundCall_wait w c d
  have hself : (w'.st c) =
      finishCall ((refundParkedCall w c d).st c) k CallResult.notAdmitted := by
    rw [hw', setActor_self]
  refine ⟨?_, ?_⟩
  · simp [hself, finishCall, hkeep.1]
  · simpa [hself, finishCall, selectCall] using
      proceed_phase_actor ((refundParkedCall w c d).st c) (w.st c)
        (selectCall k CallResult.notAdmitted)

theorem await_still_enabled (I : Impl) (w : World) (c d : InstId) (k : Cont)
    (hl : (w.st c).life = .alive) (hph : (w.st c).phase = .awaitReply d k) :
    Enabled I w (.callTimeout c) := by
  unfold Enabled apply callTimeout
  have hlive : ((w.st c).life != .alive) = false := by simp [hl, bne]
  simp [hlive, hph]

/-- An `awaitReply` does not last for the rest of a fair run while the caller
stays alive. The deadline stays enabled, and fairness takes it. -/
theorem await_not_forever (I : Impl) {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (c d : InstId) (i : Nat)
    (hph : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st c).phase = .awaitReply d k)
    (hlive : ∀ t, i ≤ t → ((ρ.cfg t).st c).life = .alive) : False := by
  have hen : ∀ t, i ≤ t → Enabled I (ρ.cfg t) (.callTimeout c) := by
    intro t ht
    obtain ⟨k, hk⟩ := hph t ht
    exact await_still_enabled I (ρ.cfg t) c d k (hlive t ht) hk
  obtain ⟨j, hj, hact⟩ := hF.weak (.callTimeout c) i rfl hen
  have happ := ρ.valid j
  rw [hact] at happ
  simp only [apply] at happ
  obtain ⟨k, hk⟩ := hph j hj
  have hend := await_timeout_end (ρ.cfg j) (ρ.cfg (j + 1)) c d k (hlive j hj) hk happ
  obtain ⟨k', hk'⟩ := hph (j + 1) (Nat.le_trans hj (Nat.le_succ j))
  exact proceed_not_await ((ρ.cfg j).st c) (selectCall k CallResult.timedOut) k' d
    (hend.2.1.symm.trans hk')

/-- Caller-side totality for the deadline step. A live `awaitReply` that takes
`callTimeout` records `TimedOut` and runs `onTimedOut`.

The three caller outcomes, each on its own continuation (`finishCall_cont`):
`Reply` is a matching reply (`await_reply_end`), `TimedOut` is this step, and
`NotAdmitted` is a parked call whose deadline fires before the request enters
the mailbox (`parked_not_admitted`). `NotAdmitted` is not an exit of
`awaitReply`. A live `awaitReply` does not last for the rest of a fair run
(`await_not_forever`). -/
theorem await_total (I : Impl) {N : Nat} (ρ : Run I N) (_hF : Fair ρ)
    (c d : InstId) (k : Cont) (i j : Nat)
    (hph : ((ρ.cfg j).st c).phase = .awaitReply d k)
    (hl : ((ρ.cfg j).st c).life = .alive)
    (_hle : i ≤ j) (hact : ρ.act j = .callTimeout c) :
    ((ρ.cfg (j + 1)).st c).lastCall = some (((ρ.cfg j).st c).waitId, CallResult.timedOut) ∧
      ((ρ.cfg (j + 1)).st c).phase =
        (proceed ((ρ.cfg j).st c) (selectCall k CallResult.timedOut)).phase ∧
      (selectCall k CallResult.timedOut).rest = k.onTimedOut := by
  have happ := ρ.valid j
  rw [hact] at happ
  simp only [apply] at happ
  have hend := await_timeout_end (ρ.cfg j) (ρ.cfg (j + 1)) c d k hl hph happ
  have hrest : (selectCall k CallResult.timedOut).rest = k.onTimedOut := by
    simp [selectCall]
  exact ⟨hend.1, hend.2.1, hrest⟩

/-- The world in which the callee is alive and the caller is already in
`awaitReply`, with the request still queued. -/
def raceDesc : Description where
  name := "race"
  freshNames := true
  templates := []
  edges := []
  compatibility := .all
  steps := []

def raceImpl : Impl where
  desc := raceDesc
  transitions := []

def replyFalseK : Cont where
  rest := [.reply]
  toState := "idle"
  replyTo := none
  onNotAdmitted := []
  onTimedOut := []

def replyFalseMsg : Msg where
  label := "Req"
  sender := .core "caller"
  callFrom := some (.core "caller")
  mid := 3
  callId := some 7

def replyFalseActor (ph : Phase) : Actor where
  life := .alive
  typestate := "idle"
  phase := ph
  box := []
  prio := []
  parked := []
  tokens := fun _ => 0
  waitId := 7
  nextCall := 8

def replyFalseWorld : World where
  N := 1
  roster := [.core "caller", .core "callee"]
  nextIx := fun _ => 0
  st := fun i =>
    if i = .core "caller" then replyFalseActor (.awaitReply (.core "callee") replyFalseK)
    else if i = .core "callee" then
      { replyFalseActor .idle with box := [replyFalseMsg] }
    else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- The `Reply` conjunct is false. The caller is in `awaitReply`, the callee is
alive, and the deadline is enabled. Taking it records `TimedOut` for that call
id and leaves the callee alive, with message `3` still queued. A later reply
cannot turn that result into `Reply`: `finishCall` retires the id. -/
theorem call_answered_reply_false :
    let c := InstId.core "caller"
    let d := InstId.core "callee"
    (replyFalseWorld.st d).life = .alive ∧
      (replyFalseWorld.st c).phase = .awaitReply d replyFalseK ∧
      Enabled raceImpl replyFalseWorld (.callTimeout c) ∧
      ∃ w, callTimeout replyFalseWorld c = some w ∧
        (w.st d).life = .alive ∧
        (w.st c).lastCall = some (7, CallResult.timedOut) ∧
        (w.st c).lastCall ≠ some (7, CallResult.reply) ∧
        ∃ m, m ∈ (w.st d).box ∧ m.mid = 3 ∧ m.callId = some 7 := by
  intro c d
  have hl : (replyFalseWorld.st c).life = .alive := rfl
  have hph : (replyFalseWorld.st c).phase = .awaitReply d replyFalseK := rfl
  have hen := await_still_enabled raceImpl replyFalseWorld c d replyFalseK hl hph
  cases hopt : callTimeout replyFalseWorld c with
  | none => simp [Enabled, apply, hopt] at hen
  | some w =>
    have hend := await_timeout_end replyFalseWorld w c d replyFalseK hl hph hopt
    have hwid : (replyFalseWorld.st c).waitId = 7 := rfl
    have hne : c ≠ d := by decide
    have hbox := await_timeout_box replyFalseWorld w c d replyFalseK hl hph hopt hne
    have hcal : (replyFalseWorld.st d).life = .alive := rfl
    have hst : (replyFalseWorld.st d).box = [replyFalseMsg] := by
      have hnc : d ≠ InstId.core "caller" := by decide
      simp [replyFalseWorld, replyFalseActor, d, hnc]
    refine ⟨rfl, hph, hen, ⟨w, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rfl
    · simpa [hcal] using hend.2.2
    · simpa [hend.1, hwid]
    · intro hbad
      simp [hend.1, hwid] at hbad
    · rw [hbox, detachBox, hst]
      refine ⟨detachMsg c replyFalseMsg, List.Mem.head _, ?_, ?_⟩
      · simp [detachMsg, replyFalseMsg, c]
      · simp [detachMsg, replyFalseMsg, c]

end Deadlock
