/-
Operational semantics of actors with bounded mailboxes, oneshot call replies,
dirty-bit cells, and fresh-name restart.

`N` bounds how many root subtrees of a per-peer template occupy a population
slot at once. A root holds its slot while it is alive. A core-supervised root
also holds it while its tombstone is queued, and that tombstone is not
receivable while the dead stage's mail is in a live queue. An unsupervised
root holds it while a member of its subtree still has mail on a surviving
receiver. Instance indices stay fresh: a restart allocates a new key, and the
dead id is never reused. There is no shutting-down phase: a stage that
terminates goes from alive to dead in that step.
-/

import Deadlock.Graph

set_option autoImplicit false

namespace Deadlock

inductive InstId where
  | core (name : String)
  /-- `key` is the subtree slot. `gen` is the incarnation. A restart uses a
  fresh `gen` at the same `key`, so siblings still route and the dead id stays. -/
  | peer (name : String) (key : Nat) (gen : Nat)
  deriving DecidableEq, Repr, Inhabited

def tname : InstId → String
  | .core n => n
  | .peer n _ _ => n

/-- The subtree key. The generation is not part of it. A core has none. -/
def memberKey : InstId → Option Nat
  | .core _ => none
  | .peer _ k _ => some k

/-- `id` is a live-or-dead role of subtree `sub` at `key`. -/
def isMember (D : Description) (id : InstId) (sub : String) (key : Nat) : Bool :=
  match id with
  | .core _ => false
  | .peer role k _ => k == key && sub != "" && templateSubtree D role == sub

/-- A peer is a member of its own template's subtree, at the index it was spawned with. -/
theorem member_of_key (D : Description) (id : InstId) (t : Template) (key : Nat)
    (ht : templateOf D (tname id) = some t) (hsub : t.subtree ≠ "")
    (hkey : memberKey id = some key) : isMember D id t.subtree key = true := by
  cases id with
  | core _ => simp [memberKey] at hkey
  | peer role ix _ =>
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
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- How a life may change. Death is permanent. An id is not reused.
There is no shutting-down life: a termination goes from alive to dead in one step. -/
def LifeStep (old new : Life) : Prop :=
  new = old ∨
    (old = .absent ∧ new = .alive) ∨
    (old = .alive ∧ new = .dead)

/-- The target will not handle mail: it has terminated. -/
def Halted (l : Life) : Prop := l = .dead

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
  /-- A parent seals every child, terminable or not, and that child's descendants,
  in this step. Siblings are not children of each other. -/
  | abort
  | terminate
  /-- A per-peer stage spawns one child of `template` at its own key.
  A slot whose tombstone is still queued is not free, and the spawn is a no-op.
  A core spawns nothing. -/
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
  /-- Typestate of `NotAdmitted`. Empty means `toState`. -/
  toNotAdmitted : String := ""
  /-- Typestate of `TimedOut`. Empty means `toState`. -/
  toTimedOut : String := ""
  /-- Typestate of a peer timeout. Empty means `toState`. -/
  toTimeout : String := ""
  /-- Typestate of a `trySend` that found a full live mailbox. Empty means `toState`. -/
  toFull : String := ""
  /-- Typestate of a `trySend` whose target was gone. Empty means `toState`. -/
  toGone : String := ""
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
  /-- Template tombstone the parent handler is written on. The queued `label`
  also carries the generation, so two incarnations do not compare equal. -/
  baseLabel : String := ""
  deriving DecidableEq, Repr, Inhabited

structure Parked where
  sender : InstId
  msg : Msg
  isCall : Bool
  deriving DecidableEq, Repr, Inhabited

structure Actor where
  life : Life
  /-- A non-idle actor's typestate is the pending landing state; pure-stage has none until `finish`. -/
  typestate : String
  phase : Phase
  box : List Msg
  prio : List Msg
  parked : List Parked
  /-- Remaining send slots toward template `dst`, as an exact integer.
  For the live generation of a key, `tokens dst + msgsTo dst = budget`:
  mail still queued from an older generation is subtracted here, and a refund
  of that mail is added back. The balance may be negative while more mail is
  queued than the budget. -/
  tokens : String → Int
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
  /-- Unused by the step. `shutdownActor` queues the tombstone itself in the
  same step that seals the actor, so nothing arms this flag. It stays on the
  record because earlier proofs still name the field. -/
  pendingTombstone : Bool := false
  /-- The incarnation that wired this actor. `none` is a scheduler root.
  The tombstone is delivered to this id, and dropped when that id is not alive. -/
  parent : Option InstId := none
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
  /-- Set by `crashWorld`. Every action is disabled while this is true. -/
  crashed : Bool := false

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
  /-- Typestate after `NotAdmitted`. Empty means `toState`. -/
  toNotAdmitted : String := ""
  /-- Typestate after `TimedOut`. Empty means `toState`. -/
  toTimedOut : String := ""
  /-- Typestate after a peer timeout. Empty means `toState`. -/
  toTimeout : String := ""
  /-- Typestate after `trySend` `Full`. Empty means `toState`. -/
  toFull : String := ""
  /-- Typestate after `trySend` `Gone`. Empty means `toState`. -/
  toGone : String := ""
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

/-- `findTr` on the message label. A current tombstone also matches `baseLabel`,
so a handler written for the template's `tombstone` accepts the newest
generation's label. A stale generation is dropped by `deliver` before this
lookup, and does not run that handler. -/
def findDeliver (I : Impl) (template state : String) (m : Msg) : Option Transition :=
  match findTr I template state m.label with
  | some tr => some tr
  | none =>
    if m.tombstone && m.baseLabel != "" && m.baseLabel != m.label then
      findTr I template state m.baseLabel
    else none

def aliveCount (w : World) (template : String) : Nat :=
  w.roster.foldl (fun n id =>
    if tname id == template && (w.st id).life == .alive then n + 1 else n) 0

/-- Population of `name` at root population `N`. A core is one instance. A
per-peer root — no supervisor, or a core supervisor — has `N` instances. A
per-peer child has its per-peer supervisor's population, one child per
parent, not a fresh `N`. `fuel` is the template count, so a cycle stops.
The chain is the product of those factors. -/
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
        match t.supervisor with
        | none => N
        | some name =>
          match templateOf D name with
          | none => 0
          | some sup =>
            match sup.multiplicity with
            | .one => N
            | .perPeer => population D name N fuel

/-- Tombstones one instance of `parent` can hold at once, as `a * N + b`.
A per-peer parent's lane sees each direct child once. A core's lane sees one
slot per root population. A restart does not add a second term: the spawn
rule keeps one tombstone per child template at a key. -/
def tombstoneAffine (D : Description) (parent : String) : Affine :=
  match templateOf D parent with
  | none => .zero
  | some sup =>
    D.templates.foldl (fun acc t =>
      if supNamed t.supervisor parent && t.tombstone != "" then
        match sup.multiplicity with
        | .perPeer => { a := acc.a, b := acc.b + 1 }
        | .one => { a := acc.a + 1, b := acc.b }
      else acc) .zero

/-- How many tombstones can sit on one instance of `parent` at population `N`.
This is `tombstoneAffine` evaluated, so a core's root children scale with `N`
and a per-peer parent contributes one per child template. -/
def simultaneousTombstones (D : Description) (parent : String) (N : Nat) : Nat :=
  (tombstoneAffine D parent).eval N

/-- The static priority demand: one tombstone per child slot, plus the other
priority senders. `otherSenders` is the self-schedule and cell-wake count.
There is no leftover-restart term. The lane still crashes if an enqueue does
not fit; `prioSized` is the check under which a tombstone enqueue has room. -/
def prioDemandAffine (D : Description) (parent : String) (otherSenders : Nat) : Affine :=
  { a := (tombstoneAffine D parent).a, b := (tombstoneAffine D parent).b + otherSenders }

def prioDemand (D : Description) (parent : String) (N otherSenders : Nat) : Nat :=
  (prioDemandAffine D parent otherSenders).eval N

def prioSized (D : Description) (parent : String) (otherSenders : Nat) : Bool :=
  match templateOf D parent with
  | none => false
  | some t => Affine.leB (prioDemandAffine D parent otherSenders) t.priorityCapacity

/-- One more tombstone fits a `prioSized` lane when the tombstones already
queued are strictly under the slot bound and the other priority messages are
within the static sender count. The restart rule is what keeps a slot's
queued count at zero at the moment that slot dies again. -/
theorem tombstone_enqueue_room
    (D : Description) (parent : String) (other tombs rest N : Nat) (t : Template)
    (ht : templateOf D parent = some t)
    (hs : prioSized D parent other = true)
    (hrest : rest ≤ other)
    (htombs : tombs + 1 ≤ (tombstoneAffine D parent).eval N) :
    tombs + rest < t.priorityCapacity.eval N := by
  simp only [prioSized, ht] at hs
  have hcap := Affine.eval_le_of_leB (prioDemandAffine D parent other) t.priorityCapacity hs N
  have hdem :
      (prioDemandAffine D parent other).eval N = (tombstoneAffine D parent).eval N + other := by
    unfold prioDemandAffine Affine.eval
    exact (Nat.add_assoc ((tombstoneAffine D parent).a * N) (tombstoneAffine D parent).b other).symm
  have hbound : (tombstoneAffine D parent).eval N + other ≤ t.priorityCapacity.eval N := by
    simpa [hdem] using hcap
  have hstep : tombs + rest + 1 ≤ (tombstoneAffine D parent).eval N + other := by
    have hsum : tombs + 1 + rest ≤ (tombstoneAffine D parent).eval N + other :=
      Nat.add_le_add htombs hrest
    have hcomm : tombs + rest + 1 = tombs + 1 + rest := by
      calc tombs + rest + 1
        _ = tombs + (rest + 1) := by rw [Nat.add_assoc]
        _ = tombs + (1 + rest) := by rw [Nat.add_comm rest 1]
        _ = tombs + 1 + rest := by rw [← Nat.add_assoc]
    simpa [hcomm] using hsum
  exact Nat.lt_of_succ_le (Nat.le_trans hstep hbound)

/-- One more ordinary priority message fits a `prioSized` lane when the
tombstones already queued are within the slot bound and the ordinary messages
are strictly under the static sender count. A label already queued is not a
new message: the caller checks that before it asks for room. -/
theorem ordinary_enqueue_room
    (D : Description) (parent : String) (other tombs rest N : Nat) (t : Template)
    (ht : templateOf D parent = some t)
    (hs : prioSized D parent other = true)
    (hrest : rest + 1 ≤ other)
    (htombs : tombs ≤ (tombstoneAffine D parent).eval N) :
    tombs + rest < t.priorityCapacity.eval N := by
  simp only [prioSized, ht] at hs
  have hcap := Affine.eval_le_of_leB (prioDemandAffine D parent other) t.priorityCapacity hs N
  have hdem :
      (prioDemandAffine D parent other).eval N = (tombstoneAffine D parent).eval N + other := by
    unfold prioDemandAffine Affine.eval
    exact (Nat.add_assoc ((tombstoneAffine D parent).a * N) (tombstoneAffine D parent).b other).symm
  have hbound : (tombstoneAffine D parent).eval N + other ≤ t.priorityCapacity.eval N := by
    simpa [hdem] using hcap
  have hstep : tombs + rest + 1 ≤ (tombstoneAffine D parent).eval N + other := by
    have hsum : tombs + (rest + 1) ≤ (tombstoneAffine D parent).eval N + other :=
      Nat.add_le_add htombs hrest
    have hcomm : tombs + rest + 1 = tombs + (rest + 1) := Nat.add_assoc tombs rest 1
    simpa [hcomm] using hsum
  exact Nat.lt_of_succ_le (Nat.le_trans hstep hbound)

/-- Tombstones still queued on `id`. A dead child's message stays until the
parent's `recvPrio`, and a replacement has to count it. -/
def queuedTombstones (w : World) (id : InstId) : Nat :=
  ((w.st id).prio.filter (·.tombstone)).length

/-- The live incarnation of `name` at `key`, if one is on the roster. -/
def findLive (w : World) (name : String) (key : Nat) : Option InstId :=
  w.roster.find? fun id =>
    match id with
    | .peer n k _ => n == name && k == key && (w.st id).life == .alive
    | .core _ => false

/-- One past every incarnation of `name` at `key` already on the roster.
The first occupant gets generation 0. A dead id is not reused. -/
def genStep (name : String) (key : Nat) (acc : Nat) (id : InstId) : Nat :=
  match id with
  | .peer n k gen => if n == name && k == key then max acc (gen + 1) else acc
  | .core _ => acc

def maxGen (w : World) (name : String) (key : Nat) : Nat :=
  w.roster.foldl (genStep name key) 0

theorem genStep_ge (name : String) (key acc : Nat) (ids : List InstId) :
    acc ≤ ids.foldl (genStep name key) acc := by
  induction ids generalizing acc with
  | nil => exact Nat.le_refl _
  | cons id ids ih =>
    rw [List.foldl_cons]
    cases id with
    | core _ => exact ih _
    | peer n k gen =>
      by_cases h : (n == name && k == key) = true
      · simp only [genStep, h, ite_true]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      · simp only [genStep, h, ite_false]
        exact ih _

theorem genStep_mono (name : String) (key : Nat) (ids : List InstId) {a b : Nat} (h : a ≤ b) :
    ids.foldl (genStep name key) a ≤ ids.foldl (genStep name key) b := by
  induction ids generalizing a b with
  | nil => exact h
  | cons id ids ih =>
    rw [List.foldl_cons, List.foldl_cons]
    cases id with
    | core _ => exact ih h
    | peer n k gen =>
      by_cases hs : (n == name && k == key) = true
      · simp only [genStep, hs, ite_true]
        exact ih (by
          apply Nat.max_le.mpr
          exact ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
      · simp only [genStep, hs, ite_false]
        exact ih h

/-- Every incarnation of this slot already on the roster has a smaller generation. -/
theorem maxGen_gt (ids : List InstId) (name : String) (key g : Nat)
    (h : InstId.peer name key g ∈ ids) : g < ids.foldl (genStep name key) 0 := by
  induction ids with
  | nil => cases h
  | cons id ids ih =>
    rw [List.foldl_cons]
    cases List.mem_cons.mp h with
    | inl heq =>
      cases heq
      simp only [genStep, beq_self_eq_true, Bool.and_self, ite_true]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self g)
        (Nat.le_trans (Nat.le_max_right _ _) (genStep_ge name key _ ids))
    | inr hmem =>
      exact Nat.lt_of_lt_of_le (ih hmem) (genStep_mono name key ids (Nat.zero_le _))

theorem maxGen_notin (w : World) (name : String) (key : Nat) :
    InstId.peer name key (maxGen w name key) ∉ w.roster := by
  intro hmem
  exact Nat.lt_irrefl _ (maxGen_gt w.roster name key _ hmem)

def aliveAt (w : World) (name : String) (key : Nat) : Bool :=
  (findLive w name key).isSome

/-- The generation that holds this key's send budget. A live incarnation
receives credits and refunds. A core, and a key with nobody alive, keep the
id that was charged. -/
abbrev budgetHolder (w : World) (sender : InstId) : InstId :=
  match sender with
  | .core _ => sender
  | .peer name key _ =>
    match findLive w name key with
    | some id => id
    | none => sender

/-- One returned slot goes to the key's live generation when one exists. -/
abbrev creditLive (w : World) (mailboxTemplate : String) (sender : InstId) : World :=
  creditSender w mailboxTemplate (budgetHolder w sender)

/-- A tombstone from a generation older than some incarnation already on the
roster. Delivery drops it, so it never runs the live generation's handler. -/
def newerGeneration (w : World) (m : Msg) : Bool :=
  match m.sender with
  | .peer name key gen =>
    m.tombstone &&
      w.roster.any fun id =>
        match id with
        | .peer n k g =>
          n == name && k == key && decide (g > gen) &&
            decide ((w.st id).parent = (w.st m.sender).parent)
        | .core _ => false
  | .core _ => false

/-- The instance a name denotes, whether or not it is alive. A per-peer role
uses the sender's subtree key. A missing template does not resolve. -/
def resolveId (D : Description) (w : World) (sender : InstId) (dst : String) : Option InstId :=
  match templateOf D dst with
  | none => none
  | some t =>
    match t.multiplicity with
    | .one => some (.core dst)
    | .perPeer =>
      match memberKey sender with
      | none => none
      | some k =>
        match findLive w dst k with
        | some id => some id
        | none => some (.peer dst k 0)

/-- A live target only. A per-peer role is the live occupant of the sender's
subtree key. Dead and never-spawned targets do not resolve. -/
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
      | some k => findLive w dst k

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

/-- Enter `k` in `k.toState`. The landing state is written when the arm is chosen,
including a nonempty arm. An empty arm is idle in that state. -/
def proceed (a : Actor) (k : Cont) : Actor :=
  match k.rest with
  | [] => { a with phase := .idle, typestate := k.toState }
  | _ => { a with phase := .run k, typestate := k.toState }

/-- `specific` when the outcome names its own typestate, otherwise `fallback`. -/
def pickState (fallback specific : String) : String :=
  if specific == "" then fallback else specific

/-- The continuation of one call outcome. `Reply` is `rest` and `toState`.
`NotAdmitted` and `TimedOut` each run their own program into their own typestate. -/
def selectCall (k : Cont) : CallResult → Cont
  | .reply => k
  | .notAdmitted =>
    { k with rest := k.onNotAdmitted, toState := pickState k.toState k.toNotAdmitted }
  | .timedOut =>
    { k with rest := k.onTimedOut, toState := pickState k.toState k.toTimedOut }

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
  { a with tokens := fun dst => (budget D template dst : Int) }

/-- Messages still queued from any generation of `name` at `key`, on hosts of
template `dst`. A new generation is charged for them: the key's budget is one
account, not a fresh account per incarnation. -/
def queuedFromKey (w : World) (name : String) (key : Nat) (dst : String) : Nat :=
  let fromKey : Msg → Bool := fun m =>
    match m.sender with
    | .peer s k _ => s == name && k == key
    | .core _ => false
  w.roster.foldl (fun n host =>
    if tname host != dst then n
    else
      n + ((w.st host).box.filter fromKey).length +
        ((w.st host).parked.filter fun p => fromKey p.msg).length) 0

/-- `budget` minus mail from every generation of this key. The subtraction is
in `Int`, so a queue longer than the budget stays visible as a negative
balance instead of being truncated. The first generation is charged nothing.
A later refund of that mail is credited to the live generation, which brings
the sum back to `budget`. -/
def withKeyTokens (D : Description) (w : World) (template : String) (key : Nat) (a : Actor) : Actor :=
  { a with tokens := fun dst =>
      (budget D template dst : Int) - (queuedFromKey w template key dst : Int) }

def bornActor (D : Description) (w : World) (template : String) (key : Nat) (initial : String) : Actor :=
  withKeyTokens D w template key
    { life := .alive, typestate := initial, phase := .idle, box := [], prio := [],
      parked := [], tokens := fun _ => 0 }

/-- Every transition the reader takes clears dirty and records the value. -/
def readCells (D : Description) (w : World) (reader : InstId) : World :=
  (cellLabels D (tname reader)).foldl (fun w label =>
    let c := w.cell (tname reader) label
    let w := setCell w (tname reader) label { c with dirty := false }
    setObserved w reader label c.value) w

def admitBorn (I : Impl) (w : World) (id : InstId) (a : Actor) : World :=
  let w := { w with roster := w.roster ++ [id] }
  readCells I.desc (setActor w id a) id

/-- Deliver `m` to a live actor. A call with no `acceptsCall` transition is refused
(`none`) so the message is not dropped. A tombstone with no transition stays
queued. Another non-call with no transition is consumed. -/
def deliver (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) : Option (World × Actor) :=
  let w := readCells I.desc w id
  if a.life ≠ .alive then none
  else if m.tombstone && newerGeneration w m then
    -- An older generation's tombstone does not run the live handler.
    some (w, { a with phase := .idle })
  else
    match findDeliver I (tname id) a.typestate m with
    | none =>
      -- A call, and a current tombstone, stay queued when this state has no transition.
      -- A non-call that is not a tombstone is consumed.
      if m.callFrom.isSome || m.tombstone then none
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
        let k : Cont :=
          { rest := tr.program, toState := tr.toState, replyTo := m.callFrom,
            toNotAdmitted := tr.toNotAdmitted, toTimedOut := tr.toTimedOut,
            toTimeout := tr.toTimeout, toFull := tr.toFull, toGone := tr.toGone }
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
        some (creditLive (setActor w id a') (tname id) m.sender)
    | m :: ms, p :: ps =>
      match deliver I w id { a with box := ms } m with
      | none => none
      | some (w, a') =>
        let admitted := { a' with box := a'.box ++ [p.msg], parked := ps }
        let w := creditLive (setActor w id admitted) (tname id) m.sender
        let resumed := resumeSender (w.st p.sender) p.isCall id
        some (setActor w p.sender resumed)
    | [], p :: ps =>
      match deliver I w id { a with parked := ps } p.msg with
      | none => none
      | some (w, a') =>
        let w := creditLive (setActor w id a') (tname id) p.msg.sender
        some (setActor w p.sender (resumeSender (w.st p.sender) p.isCall id))
    | [], [] => none

/-- `desc` sits under `anc` on the recorded parent chain. `fuel` is the
roster length, so a cycle stops. The node itself is not a descendant. -/
def descends (fuel : Nat) (w : World) (anc desc : InstId) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if desc == anc then false
    else
      match (w.st desc).parent with
      | none => false
      | some p =>
        if p == anc then true
        else if p == desc then false
        else descends fuel w anc p

/-- `host` is dropped in the same seal as `sender`. `terminateStage` seals
the sender's descendants in that step (`dropDescendants`, then `sealBranch`
and `releaseWorld`) and seals the sender in the same step. `releaseWorld`
empties that actor's mailbox. It does not clear a sibling, a parent, or a
core: those hosts are not in this seal. -/
def sealedTogether (w : World) (sender host : InstId) : Bool :=
  sender == host || descends w.roster.length w sender host

/-- Program mail from `origin` or a recorded descendant, still sitting in a
live receiver's bulk or priority queue. A tombstone is not program mail.
A dead receiver's mailbox was cleared when it was sealed. Mail left by
`crashWorld` is never consumed, because a crashed world takes no step. A
parked send is not here: the kill drops it, so it is never enqueued. -/
def mailInFlight (w : World) (origin : InstId) : Bool :=
  w.roster.any fun host =>
    (w.st host).life == .alive &&
      let hit (m : Msg) : Bool := !m.tombstone && sealedTogether w origin m.sender
      (w.st host).box.any hit || (w.st host).prio.any hit

/-- A queued tombstone whose sender, or one of that sender's sealed
descendants, still has program mail in a live queue. It stays in the lane,
so it keeps its priority slot, and a receive skips it. -/
def tombstoneWaits (w : World) (m : Msg) : Bool :=
  m.tombstone && mailInFlight w m.sender

theorem tombstone_clear_of_take (w : World) (m : Msg)
    (h : tombstoneWaits w m = false) (ht : m.tombstone = true) :
    mailInFlight w m.sender = false := by
  simp only [tombstoneWaits, ht, Bool.true_and] at h
  exact h

/-- Take the first priority message that is not a waiting tombstone. Messages
skipped are waiting tombstones; they stay in the lane, ahead of whatever
follows them in the remainder. A waiting tombstone is not a head that stalls
a later ready message. -/
def receivePrioFrom (I : Impl) (w : World) (id : InstId) (skipped : List Msg) :
    List Msg → Option World
  | [] => none
  | m :: ms =>
    if tombstoneWaits w m then receivePrioFrom I w id (skipped ++ [m]) ms
    else
      match deliver I w id { (w.st id) with prio := skipped ++ ms } m with
      | none => none
      | some (w', a') => some (setActor w' id a')

def receivePrio (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive || a.phase ≠ .idle then none
  else receivePrioFrom I w id [] a.prio

theorem receivePrioFrom_spec (I : Impl) (w : World) (id : InstId) (skipped ms : List Msg)
    (w' : World) (h : receivePrioFrom I w id skipped ms = some w') :
    ∃ m pre suf w1 a1,
      skipped ++ ms = pre ++ m :: suf ∧
      tombstoneWaits w m = false ∧
      deliver I w id { (w.st id) with prio := pre ++ suf } m = some (w1, a1) ∧
      w' = setActor w1 id a1 := by
  induction ms generalizing skipped with
  | nil => simp [receivePrioFrom] at h
  | cons m ms ih =>
    unfold receivePrioFrom at h
    split at h
    · rename_i hwait
      obtain ⟨m', pre, suf, w1, a1, happ, hclear, hdel, hw'⟩ := ih (skipped ++ [m]) h
      refine ⟨m', pre, suf, w1, a1, ?_, hclear, hdel, hw'⟩
      have hstep : skipped ++ (m :: ms) = (skipped ++ [m]) ++ ms := by
        simp [List.append_assoc]
      exact hstep.trans happ
    · rename_i hclear
      have hwf : tombstoneWaits w m = false := by
        cases hb : tombstoneWaits w m with
        | false => rfl
        | true => exact absurd hb hclear
      split at h
      · cases h
      · rename_i w1 a1 hdel
        cases h
        refine ⟨m, skipped, ms, w1, a1, ?_, hwf, hdel, rfl⟩
        simp

/-- A successful priority receive takes one message that is not a waiting
tombstone, and leaves every skipped waiting tombstone in the lane. -/
theorem receivePrio_spec (I : Impl) (w w' : World) (id : InstId)
    (h : receivePrio I w id = some w') :
    ∃ m pre suf w1 a1,
      (w.st id).life = .alive ∧ (w.st id).phase = .idle ∧
      (w.st id).prio = pre ++ m :: suf ∧
      tombstoneWaits w m = false ∧
      deliver I w id { (w.st id) with prio := pre ++ suf } m = some (w1, a1) ∧
      w' = setActor w1 id a1 := by
  unfold receivePrio at h
  dsimp at h
  split at h
  · cases h
  · rename_i hready
    have hboth : decide ((w.st id).life ≠ .alive) = false ∧
        decide ((w.st id).phase ≠ .idle) = false := by
      simpa [Bool.or_eq_false_iff] using hready
    have hlife : (w.st id).life = .alive := by
      have hnot := decide_eq_false_iff_not.mp hboth.1
      simpa [ne_eq] using hnot
    have hidle : (w.st id).phase = .idle := by
      have hnot := decide_eq_false_iff_not.mp hboth.2
      simpa [ne_eq] using hnot
    obtain ⟨m, pre, suf, w1, a1, happ, hwait, hdel, hw'⟩ :=
      receivePrioFrom_spec I w id [] (w.st id).prio w' h
    exact ⟨m, pre, suf, w1, a1, hlife, hidle, by simpa using happ, hwait, hdel, hw'⟩

/-- Skipped messages are waiting tombstones. `receivePrio_spec` records the
split; this one also records why the prefix stayed in the lane. -/
theorem receivePrioFrom_waits (I : Impl) (w : World) (id : InstId) (skipped ms : List Msg)
    (w' : World) (hskip : ∀ t ∈ skipped, tombstoneWaits w t = true)
    (h : receivePrioFrom I w id skipped ms = some w') :
    ∃ m pre suf w1 a1,
      skipped ++ ms = pre ++ m :: suf ∧
      (∀ t ∈ pre, tombstoneWaits w t = true) ∧
      tombstoneWaits w m = false ∧
      deliver I w id { (w.st id) with prio := pre ++ suf } m = some (w1, a1) ∧
      w' = setActor w1 id a1 := by
  induction ms generalizing skipped with
  | nil => simp [receivePrioFrom] at h
  | cons m ms ih =>
    unfold receivePrioFrom at h
    split at h
    · rename_i hwait
      have hskip' : ∀ t ∈ skipped ++ [m], tombstoneWaits w t = true := by
        intro t ht
        simp [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hskip t ht
        · exact hwait
      obtain ⟨m', pre, suf, w1, a1, happ, hpre, hclear, hdel, hw'⟩ := ih (skipped ++ [m]) hskip' h
      refine ⟨m', pre, suf, w1, a1, ?_, hpre, hclear, hdel, hw'⟩
      have hstep : skipped ++ (m :: ms) = (skipped ++ [m]) ++ ms := by simp [List.append_assoc]
      exact hstep.trans happ
    · rename_i hclear
      have hwf : tombstoneWaits w m = false := by
        cases hb : tombstoneWaits w m with
        | false => rfl
        | true => exact absurd hb hclear
      split at h
      · cases h
      · rename_i w1 a1 hdel
        cases h
        refine ⟨m, skipped, ms, w1, a1, ?_, hskip, hwf, hdel, rfl⟩
        simp

theorem receivePrio_waits (I : Impl) (w w' : World) (id : InstId)
    (h : receivePrio I w id = some w') :
    ∃ m pre suf w1 a1,
      (w.st id).life = .alive ∧ (w.st id).phase = .idle ∧
      (w.st id).prio = pre ++ m :: suf ∧
      (∀ t ∈ pre, tombstoneWaits w t = true) ∧
      tombstoneWaits w m = false ∧
      deliver I w id { (w.st id) with prio := pre ++ suf } m = some (w1, a1) ∧
      w' = setActor w1 id a1 := by
  unfold receivePrio at h
  dsimp at h
  split at h
  · cases h
  · rename_i hready
    have hboth : decide ((w.st id).life ≠ .alive) = false ∧
        decide ((w.st id).phase ≠ .idle) = false := by
      simpa [Bool.or_eq_false_iff] using hready
    have hlife : (w.st id).life = .alive := by
      have hnot := decide_eq_false_iff_not.mp hboth.1
      simpa [ne_eq] using hnot
    have hidle : (w.st id).phase = .idle := by
      have hnot := decide_eq_false_iff_not.mp hboth.2
      simpa [ne_eq] using hnot
    obtain ⟨m, pre, suf, w1, a1, happ, hpre, hwait, hdel, hw'⟩ :=
      receivePrioFrom_waits I w id [] (w.st id).prio w' (by intro _ ht; cases ht) h
    exact ⟨m, pre, suf, w1, a1, hlife, hidle, by simpa using happ, hpre, hwait, hdel, hw'⟩

/-- The message `receivePrio` removes is the one `receivePrio_spec` delivers.
The world after the receive is that delivery, so the witness is not some
other message that merely fails to be a waiting tombstone. A tombstone in
that position has no program mail left in a live queue. -/
theorem receivePrio_tombstone_drained (I : Impl) (w w' : World) (id : InstId)
    (h : receivePrio I w id = some w') :
    ∃ m pre suf w1 a1,
      (w.st id).life = .alive ∧ (w.st id).phase = .idle ∧
      (w.st id).prio = pre ++ m :: suf ∧
      tombstoneWaits w m = false ∧
      deliver I w id { (w.st id) with prio := pre ++ suf } m = some (w1, a1) ∧
      w' = setActor w1 id a1 ∧
      (m.tombstone = true → mailInFlight w m.sender = false) := by
  obtain ⟨m, pre, suf, w1, a1, hlife, hidle, happ, hwait, hdel, hw'⟩ :=
    receivePrio_spec I w w' id h
  exact ⟨m, pre, suf, w1, a1, hlife, hidle, happ, hwait, hdel, hw',
    fun ht => tombstone_clear_of_take w m hwait ht⟩

def enqueueOrPark (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : World :=
  let target := w.st dst
  let cap := capBulk D w.N dst
  if target.life ≠ .alive then
    -- Dead and absent targets store nothing and are not charged.
    -- The drop is permanent: death does not return to alive, and a dead id
    -- is not spawned again. A call ends as `NotAdmitted`. A send proceeds.
    -- An absent id can still be spawned later, but this call does not sit on it.
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

/-- A core's `terminate`, and a priority lane with no room left. Every alive
actor on the roster dies in this step, in the crashed phase.
Mail stays queued: the host is dead before anything dequeues it, and a crashed
world takes no further step. -/
def crashActor (a : Actor) : Actor :=
  if a.life == .alive then
    { a with life := .dead, phase := .crashed }
  else a

def crashWorld (w : World) : World :=
  let killed (i : InstId) : Actor :=
    if decide (i ∈ w.roster) then crashActor (w.st i) else w.st i
  { w with crashed := true, st := killed }

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
  ms.foldl (fun w m => creditLive w dstName m.sender) w

def refundParked (w : World) (dstName : String) (ps : List Parked) : World :=
  ps.foldl (fun w p => creditLive w dstName p.msg.sender) w

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
      | .peer _ k _ =>
        match templateOf D (tname child) with
        | none => none
        | some t =>
          if t.subtree != "" && t.subtree == sup.subtree then some (.peer supName k 0) else none

/-- The supervisor `id`'s template names, if it names one. -/
def supervisorOf (D : Description) (id : InstId) : Option InstId :=
  match templateOf D (tname id) with
  | none => none
  | some t =>
    match t.supervisor with
    | none => none
    | some name => supervisorInst D id name

/-- Same role and subtree key. Generations are incarnations, not different slots. -/
def sameSlot (a b : InstId) : Bool :=
  match a, b with
  | .core x, .core y => x == y
  | .peer n k _, .peer n' k' _ => n == n' && k == k'
  | _, _ => false

/-- `child` recorded `parent` as the incarnation that wired it. The match is
the id, including generation. An actor is not its own child. -/
def isChild (w : World) (parent child : InstId) : Bool :=
  match (w.st child).parent with
  | some p => p == parent && decide (child ≠ parent)
  | none => false

/-- The recorded parent is the child link. -/
theorem isChild_recorded (w : World) (parent child : InstId)
    (h : (w.st child).parent = some parent) (hne : child ≠ parent) :
    isChild w parent child = true := by
  simp [isChild, h, hne]

/-- A child link stores the recorded parent. -/
theorem isChild_parent (w : World) (parent child : InstId)
    (h : isChild w parent child = true) : (w.st child).parent = some parent := by
  simp only [isChild] at h
  split at h
  · rename_i p hp
    have hpair := (Bool.and_eq_true _ _).mp h
    have heq : p = parent := (beq_iff_eq).mp hpair.1
    simpa [hp, heq]
  · simp at h

/-- `parent` is the recorded parent of `child`. A self-loop is not an edge. -/
def ParentEdge (w : World) (child parent : InstId) : Prop :=
  (w.st child).parent = some parent ∧ child ≠ parent

/-- `anc` is a strict ancestor of `desc` along recorded parent links. -/
inductive StrictAncestor (w : World) : InstId → InstId → Prop where
  | edge {desc anc : InstId} : ParentEdge w desc anc → StrictAncestor w desc anc
  | tail {desc mid anc : InstId} : ParentEdge w desc mid →
      StrictAncestor w mid anc → StrictAncestor w desc anc

/-- Ancestry is well-founded: following a parent link terminates, so no actor
is its own strict ancestor. The relation steps from a parent to its child. -/
def ParentAcyclic (w : World) : Prop :=
  WellFounded (fun anc desc => ParentEdge w desc anc)

/-- A parent link, an actor off the roster with no parent, and every recorded
parent on the roster. Spawn is the only step that adds a link, and it adds
one from a fresh id to a roster actor. -/
structure ParentForest (w : World) : Prop where
  wf : ParentAcyclic w
  off : ∀ id, id ∉ w.roster → (w.st id).parent = none
  hosted : ∀ id p, (w.st id).parent = some p → p ∈ w.roster

/-- A roster actor was wired by the supervisor its template names.
An unsupervised actor has no parent. A per-peer supervisor is the
incarnation at that actor's own key. A core supervisor carries no key. -/
def Parented (D : Description) (w : World) : Prop :=
  ∀ id t, id ∈ w.roster → templateOf D (tname id) = some t →
    match t.supervisor with
    | none => (w.st id).parent = none
    | some name => ∃ p, (w.st id).parent = some p ∧ tname p = name ∧
        match p with
        | .peer _ k _ => memberKey id = some k
        | .core _ => True

/-- A roster actor was born alive and is later dead. Nothing writes `.absent`
onto the roster. -/
def Present (w : World) : Prop :=
  ∀ id, id ∈ w.roster → (w.st id).life ≠ .absent

/-- Bulk mail is program mail. A tombstone is offered on the priority lane. -/
def PlainBox (w : World) : Prop :=
  ∀ host m, m ∈ (w.st host).box → m.tombstone = false

/-- A live host does not hold a parked entry whose sender is already dead.
`releaseOutbound` drops those entries and returns their slots to the sender
before `releaseWorld` marks that sender dead, so a later step never sees them. -/
def ParkedFromLive (w : World) : Prop :=
  ∀ host p, (w.st host).life = .alive → p ∈ (w.st host).parked →
    (w.st p.sender).life ≠ .dead

/-- An actor that is not alive has an empty mailbox, unless the roster has
crashed and no further step will read it. -/
def DeadQuiet (w : World) : Prop :=
  w.crashed = true ∨ ∀ id, (w.st id).life ≠ .alive →
    (w.st id).box = [] ∧ (w.st id).parked = []

/-- An actor that is not alive has no live child. A step seals descendants
before the parent, or it seals a childless actor. -/
def DeadChildless (w : World) : Prop :=
  w.crashed = true ∨ ∀ id c, (w.st id).life ≠ .alive →
    (w.st c).parent = some id → (w.st c).life ≠ .alive

/-- `parent`'s priority lane still holds `id`'s tombstone. -/
def HoldsTomb (w : World) (parent id : InstId) : Prop :=
  ∃ m, m ∈ (w.st parent).prio ∧ m.tombstone = true ∧ m.sender = id

/-- While a dead actor's mail sits in a live queue, either its parent is alive
and still holds its tombstone, or the parent is not alive and that parent's own
mail is in flight. The second case is the ancestor: a descendant's message is
sealed together with the parent, so the parent's tombstone is what stays queued.
`occ_set` may change `prio` and `parent`, so this stays out of `OccInv`. -/
def TombChain (w : World) : Prop :=
  ∀ id, w.crashed = false → (w.st id).life = .dead → mailInFlight w id = true →
    match (w.st id).parent with
    | none => True
    | some p =>
        ((w.st p).life = .alive ∧ HoldsTomb w p id) ∨
        ((w.st p).life ≠ .alive ∧ mailInFlight w p = true)

/-- Tombstone chain for every dead id outside `gap`. `releaseWorld` puts the
actor it seals into `gap`: that actor is dead and its tombstone is not queued
yet. An id leaves `gap` when its parent dies, because its mail then keeps the
parent's tombstone waiting, or when its own tombstone is queued. -/
def TombGap (w : World) (gap : InstId → Prop) : Prop :=
  ∀ id, w.crashed = false → (w.st id).life = .dead → mailInFlight w id = true →
    ¬ gap id →
    match (w.st id).parent with
    | none => True
    | some p =>
        ((w.st p).life = .alive ∧ HoldsTomb w p id) ∨
        ((w.st p).life ≠ .alive ∧ mailInFlight w p = true)

theorem gap_of_chain {w : World} (h : TombChain w) : TombGap w (fun _ => False) :=
  fun id hc hd hf _ => h id hc hd hf

theorem chain_of_gap {w : World} (h : TombGap w (fun _ => False)) : TombChain w :=
  fun id hc hd hf => h id hc hd hf (fun hf => hf)

/-- Seal facts carried by `Inv` beside the parent forest. `OccInv` does not
hold them: a state edit may change `prio` and `parent` while life, the box,
and the parked lane stay put. -/
structure SealInv (w : World) : Prop where
  liveParked : ParkedFromLive w
  quiet : DeadQuiet w
  childless : DeadChildless w
  chain : TombChain w
  /-- The parked entry and the message it carries name the same sender. -/
  parkedFrom : ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender
  /-- Bulk and priority mail was sent by someone on the roster. An id that has
  not been born has no queued mail, so a later birth does not adopt it. -/
  hostedMail : ∀ host m,
    (m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) → m.sender ∈ w.roster

theorem isChild_edge (w : World) (parent child : InstId)
    (h : isChild w parent child = true) : ParentEdge w child parent := by
  have hp := isChild_parent w parent child h
  refine ⟨hp, ?_⟩
  intro heq
  rw [heq] at hp h
  simp [isChild, hp] at h

theorem StrictAncestor.trans {w : World} {desc mid anc : InstId}
    (h1 : StrictAncestor w desc mid) (h2 : StrictAncestor w mid anc) : StrictAncestor w desc anc := by
  induction h1 with
  | edge h => exact StrictAncestor.tail h h2
  | tail h _ ih => exact StrictAncestor.tail h (ih h2)

theorem ParentEdge.parents {w w' : World} (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    {c p : InstId} (h : ParentEdge w c p) : ParentEdge w' c p := by
  exact ⟨by rw [hp, h.1], h.2⟩

theorem StrictAncestor.parents {w w' : World} (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    {desc anc : InstId} (h : StrictAncestor w desc anc) : StrictAncestor w' desc anc := by
  induction h with
  | edge he => exact StrictAncestor.edge (ParentEdge.parents hp he)
  | tail he _ ih => exact StrictAncestor.tail (ParentEdge.parents hp he) ih

theorem parentAcyclic_parents {w w' : World} (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hw : ParentAcyclic w) : ParentAcyclic w' := by
  refine ⟨fun id => ?_⟩
  have hacc : ∀ id, Acc (fun anc desc => ParentEdge w desc anc) id →
      Acc (fun anc desc => ParentEdge w' desc anc) id := by
    intro id ha
    induction ha with
    | intro id _ ih =>
      refine Acc.intro id fun anc hanc => ih anc ?_
      exact ⟨by rw [← hp, hanc.1], hanc.2⟩
  exact hacc id (hw.apply id)

theorem ParentAcyclic.no_self {w : World} (hw : ParentAcyclic w) (id : InstId) :
    ¬ StrictAncestor w id id := by
  have hacc : ∀ id, Acc (fun anc desc => ParentEdge w desc anc) id → ¬ StrictAncestor w id id := by
    intro id ha
    induction ha with
    | intro id _ ih =>
      intro hself
      cases hself with
      | edge he => exact he.2 rfl
      | tail he hrest =>
        exact ih _ ⟨he.1, he.2⟩ (StrictAncestor.trans hrest (StrictAncestor.edge he))
  exact hacc id (hw.apply id)

/-- Replace `born`'s parent. `born` was unwired, and nothing already points at it,
so the new link does not close a cycle. -/
theorem parentAcyclic_link (w : World) (born : InstId) (a : Actor) (hw : ParentAcyclic w)
    (hold : (w.st born).parent = none) (hfree : ∀ i, (w.st i).parent ≠ some born)
    (hne : ∀ p, a.parent = some p → p ≠ born) : ParentAcyclic (setActor w born a) := by
  by_cases hpar : a.parent = none
  · apply parentAcyclic_parents (w' := setActor w born a) _ hw
    intro i
    by_cases hi : i = born
    · simp [hi, setActor_self, hpar, hold]
    · simp [setActor_other w born i a hi]
  · cases hpa : a.parent with
    | none => exact absurd hpa hpar
    | some p =>
      have hpne : p ≠ born := hne p hpa
      let w' := setActor w born a
      have lift : ∀ id, Acc (fun anc desc => ParentEdge w desc anc) id → id ≠ born →
          Acc (fun anc desc => ParentEdge w' desc anc) id := by
        intro id ha
        induction ha with
        | intro id _ ih =>
          intro hid
          refine Acc.intro id fun anc hanc => ?_
          have hancw : ParentEdge w id anc := by
            have hst : (w'.st id).parent = (w.st id).parent := by
              simpa [w', setActor_other w born id a hid]
            exact ⟨by rw [← hst, hanc.1], hanc.2⟩
          have hancne : anc ≠ born := by
            intro heq
            exact hfree id (by simpa [heq] using hancw.1)
          exact ih anc hancw hancne
      refine ⟨fun id => ?_⟩
      by_cases hidB : id = born
      · rw [hidB]
        refine Acc.intro born fun anc hanc => ?_
        have hancp : anc = p := by
          have h1 := hanc.1
          simp [w', setActor_self, hpa] at h1
          exact h1.symm
        exact lift anc (hw.apply anc) (by rw [hancp]; exact hpne)
      · exact lift id (hw.apply id) hidB

theorem ParentForest.parents {w w' : World} (h : ParentForest w)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent) (hr : w'.roster = w.roster) : ParentForest w' where
  wf := parentAcyclic_parents hp h.wf
  off := fun id hid => by
    have hid' : id ∉ w.roster := by rw [hr] at hid; exact hid
    rw [hp]
    exact h.off id hid'
  hosted := fun id p hsome => by
    rw [hp id] at hsome
    rw [hr]
    exact h.hosted id p hsome

theorem ParentForest.setActor {w : World} {id : InstId} {a : Actor} (h : ParentForest w)
    (hp : a.parent = (w.st id).parent) : ParentForest (setActor w id a) := by
  refine h.parents ?_ rfl
  intro i
  by_cases hi : i = id
  · simp [hi, setActor_self, hp]
  · simp [setActor_other w id i a hi]

/-- Appending an id does not add a parent edge. An id that was already off the
roster stays unwired. -/
theorem ParentForest.grow {w : World} (h : ParentForest w) (id : InstId) :
    ParentForest { w with roster := w.roster ++ [id] } where
  wf := parentAcyclic_parents (fun _ => rfl) h.wf
  off := fun i hi => h.off i (fun hm => hi (List.mem_append_left _ hm))
  hosted := fun i p hp => List.mem_append_left _ (h.hosted i p hp)

/-- Some live actor recorded `id` as its parent. -/
def hasChild (D : Description) (w : World) (id : InstId) : Bool :=
  let _desc := D
  w.roster.any fun c => isChild w id c && (w.st c).life == .alive

/-- The tombstone label the parent wired for this child template.
A peer's label carries its generation, so a stale tombstone is not the
live incarnation's. The parent's transition is on the base label; delivery
accepts either spelling. -/
def tombstoneLabel (D : Description) (child : InstId) : String :=
  let base :=
    match templateOf D (tname child) with
    | some t => t.tombstone
    | none => ""
  if base == "" then ""
  else
    match child with
    | .peer _ _ g => base ++ "#" ++ toString g
    | .core _ => base

/-- One tombstone per child. The label is the child template's wired label, so
two templates do not share a message and two instances of one template do not
collapse into one wake. -/
def tombstoneMsg (D : Description) (parent : Actor) (child : InstId) : Msg :=
  let base :=
    match templateOf D (tname child) with
    | some t => t.tombstone
    | none => ""
  { label := tombstoneLabel D child, sender := child, callFrom := none,
    reliable := true, mid := parent.nextMid, tombstone := true, baseLabel := base }

/-- The recorded parent, when that incarnation is still alive. A dead parent
is not a delivery target: pure-stage has already removed its queue. -/
def liveSupervisor (D : Description) (w : World) (child : InstId) : Option InstId :=
  let _desc := D
  match (w.st child).parent with
  | none => none
  | some p => if (w.st p).life == .alive then some p else none

/-- Hand the recorded parent the child's tombstone. No recorded parent is not a
delivery. A parent that is dead has no queue left, so the
tombstone is dropped. A live parent with no wired label crashes: a live
supervisor must have a handler. A tombstone that does not fit is `offerPrio`'s
crash. The tombstone counts toward that lane's budget. -/
def enqueueTombstone (D : Description) (w : World) (child : InstId) : World :=
  match (w.st child).parent with
  | none => w
  | some parent =>
    let p := w.st parent
    let msg := tombstoneMsg D p child
    if p.life != .alive then w
    else if msg.label == "" then crashWorld w
    else offerPrio D w parent msg

/-- A tombstone enqueue does not crash when the recorded parent is alive, the
label is non-empty, and the lane has room. A full lane and an empty label on
a live parent still crash. A parent that is not alive drops the tombstone. -/
theorem enqueueTombstone_fits
    (D : Description) (w : World) (child parent : InstId)
    (hsup : liveSupervisor D w child = some parent)
    (hlife : (w.st parent).life = .alive)
    (hlabel : (tombstoneMsg D (w.st parent) child).label ≠ "")
    (hroom : prioLoad (w.st parent).prio < capPrio D w.N parent)
    (hcrash : w.crashed = false) :
    (enqueueTombstone D w child).crashed = false := by
  have hpar : (w.st child).parent = some parent := by
    unfold liveSupervisor at hsup
    cases hparent : (w.st child).parent with
    | none => simp [hparent] at hsup
    | some p =>
      simp only [hparent] at hsup
      by_cases haliveP : (w.st p).life = .alive
      · have hbit : ((w.st p).life == .alive) = true := by simpa [beq_iff_eq] using haliveP
        simp only [hbit, ite_true] at hsup
        cases hsup
        rfl
      · have hbit : ((w.st p).life == .alive) = false := by
          simpa [beq_iff_eq] using haliveP
        simp only [hbit, ite_false] at hsup
        cases hsup
  unfold enqueueTombstone offerPrio
  simp only [hpar]
  have hif : ((w.st parent).life != .alive) = false := by simp [hlife]
  have hlab : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
    simpa [beq_iff_eq] using hlabel
  have hdec : decide (prioLoad (w.st parent).prio ≥ capPrio D w.N parent) = false :=
    decide_eq_false (Nat.not_le.mpr hroom)
  simp [hif, hlab, hdec, setActor, hcrash]

/-- Under `prioSized`, a tombstone fits when the queued tombstones are strictly
under the slot bound and the other priority messages are within the static
sender count. That split is the hypothesis here. It is not yet shown for
every world `GraphOk` and `LocalOk` can reach. -/
theorem tombstone_offer_room
    (D : Description) (w : World) (child parent : InstId) (parentName : String)
    (other tombs rest : Nat) (t : Template)
    (ht : templateOf D parentName = some t)
    (hs : prioSized D parentName other = true)
    (hrest : rest ≤ other)
    (htombs : tombs + 1 ≤ (tombstoneAffine D parentName).eval w.N)
    (hload : prioLoad (w.st parent).prio = tombs + rest)
    (hsup : liveSupervisor D w child = some parent)
    (hlife : (w.st parent).life = .alive)
    (hlabel : (tombstoneMsg D (w.st parent) child).label ≠ "")
    (hname : tname parent = parentName)
    (hcrash : w.crashed = false) :
    (enqueueTombstone D w child).crashed = false := by
  have hlt : tombs + rest < t.priorityCapacity.eval w.N :=
    tombstone_enqueue_room D parentName other tombs rest w.N t ht hs hrest htombs
  have hcap : capPrio D w.N parent = t.priorityCapacity.eval w.N := by
    unfold capPrio
    rw [hname, ht]
  exact enqueueTombstone_fits D w child parent hsup hlife hlabel (by simpa [hload, hcap] using hlt) hcrash

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

/-- Finish `id` and queue its tombstone on the supervisor. `releaseWorld` refunds
the mailbox, drops parked sends, and installs the actor dead and empty. The
tombstone is queued in that same step. A receive skips it while program mail
from this stage is still in a live queue. `pendingTombstone` is not consulted. -/
def sealActor (D : Description) (w : World) (id : InstId) (a : Actor) : World :=
  enqueueTombstone D (releaseWorld D w id a) id

/-- Seal `id` when it is alive: alive becomes dead, and the tombstone is queued
on the supervisor, in this step. A life that is not alive is left alone.
A stage that terminates inside its own transition is sealed here. -/
def shutdownActor (D : Description) (w : World) (id : InstId) : World :=
  if (w.st id).life == .alive then sealActor D w id (w.st id) else w

/-- A core's `terminate`, or a priority-lane overflow, has crashed the roster.
`crashWorld` sets `w.crashed` and every later action is disabled, so the world
is absorbing. The liveness claim is deadlock-free or crashed: a fair run of a
checked implementation is not stuck, or a step has already crashed the roster.
A core terminate is one of those crashes, and it is acceptable.
`tombstone_offer_room` is the numeric half: under `prioSized`, one more
tombstone fits when the ones already queued are strictly under the slot bound
and the other priority messages are within the static sender count. A
self-schedule or a cell wake that does not fit still crashes. -/
def WorldCrashed (w : World) : Prop :=
  ∃ id, id ∈ w.roster ∧ (w.st id).life = .dead ∧ (w.st id).phase = .crashed

/-- Seal `id` and every recorded descendant in this step. A descendant's
tombstone is discarded: pure-stage terminates each child, ignores the
tombstone that child would return, and removes the stage before the parent
is told. An actor that is already dead or absent is left as it is. `fuel`
bounds the depth. -/
def sealBranch (fuel : Nat) (D : Description) (w : World) (id : InstId) : World :=
  match fuel with
  | 0 => w
  | fuel + 1 =>
    let sealed := w.roster.foldl (fun acc child =>
      if isChild acc id child then sealBranch fuel D acc child else acc) w
    if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id)
    else sealed

/-- Proper descendants of `id`, sealed now. `id` itself stays for its own
tombstone. -/
def dropDescendants (D : Description) (w : World) (id : InstId) : World :=
  w.roster.foldl (fun acc child =>
    if isChild acc id child then sealBranch w.roster.length D acc child else acc) w

/-- A stage in the supervision tree terminates. Descendants are sealed in this
step, and their tombstones are not delivered. The stage itself is sealed in
the same step: alive becomes dead, and its tombstone is queued on the
immediate supervisor. A sibling is not a descendant. -/
def terminateStage (D : Description) (w : World) (id : InstId) (a : Actor) : World :=
  let _committed := a
  shutdownActor D (dropDescendants D w id) id

/-- The parent's abort. Every live child is sealed in this step, so the parent
receives that child's tombstone now. The child's own descendants are sealed
in the same step and do not leave a grandchild occupying the slot. -/
def abortChildren (D : Description) (w : World) (parent : InstId) : World :=
  w.roster.foldl (fun w child =>
    if isChild w parent child && (w.st child).life == .alive then
      shutdownActor D (dropDescendants D w child) child
    else w) w

/-- A tombstone for `child` at slot `k` is still on `parent`'s priority lane. -/
def slotTombstoneQueued (w : World) (parent : InstId) (child : String) (k : Nat) : Bool :=
  (w.st parent).prio.any fun m =>
    m.tombstone &&
      match m.sender with
      | .peer n key _ => n == child && key == k
      | .core _ => false

/-- `name` at `key` is alive. The seal installs `dead` and queues the tombstone
in the same step, so a dead slot is held by `slotTombstoneQueued`, not here. -/
def slotOccupied (w : World) (name : String) (k : Nat) : Bool :=
  w.roster.any fun id =>
    match id with
    | .peer n key _ =>
      n == name && key == k && (w.st id).life == .alive
    | .core _ => false

/-- `id` is an occupant of per-peer slot `(name, key)`. A per-peer parent's
one child uses the parent's key. Generation distinguishes occupants of the
same key. A scheduler root takes a fresh key, so it is a new slot. -/
def fromSlot (name : String) (key : Nat) (id : InstId) : Bool :=
  match id with
  | .peer n k _ => n == name && k == key
  | .core _ => false

/-- `host` still has to consume mail from `sender`. It is alive, and it is not
sealed together with the sender. A dead or absent host does not count: a host
sealed with the sender is already dead, and its mailbox was cleared in that
seal. -/
def survivesSender (w : World) (sender host : InstId) : Bool :=
  (w.st host).life == .alive && !(sealedTogether w sender host)

/-- Mail from slot `(name, key)` that `host` has not consumed: a bulk
message, a priority message, or a parked send still sitting here, and only
when `host` survives that sender. -/
def actorHoldsSlotMail (w : World) (host : InstId) (name : String) (key : Nat) (a : Actor) : Bool :=
  let held (sender : InstId) : Bool := fromSlot name key sender && survivesSender w sender host
  a.box.any (fun m => held m.sender) ||
    a.prio.any (fun m => held m.sender) ||
    a.parked.any (fun p => held p.sender || held p.msg.sender)

/-- A surviving receiver still holds mail from any occupant of slot
`(name, key)`. -/
def slotCoreMail (w : World) (name : String) (key : Nat) : Bool :=
  w.roster.any fun host => actorHoldsSlotMail w host name key (w.st host)

/-- `id` is any generation of any template in subtree `sub` at `key`. -/
def fromSubtree (D : Description) (sub : String) (key : Nat) (id : InstId) : Bool :=
  isMember D id sub key

/-- Mail from subtree `sub` at `key` that `host` has not consumed, when
`host` survives that sender. -/
def actorHoldsSubtreeMail (D : Description) (w : World) (host : InstId) (sub : String) (key : Nat)
    (a : Actor) : Bool :=
  let held (sender : InstId) : Bool := fromSubtree D sub key sender && survivesSender w sender host
  a.box.any (fun m => held m.sender) ||
    a.prio.any (fun m => held m.sender) ||
    a.parked.any (fun p => held p.sender || held p.msg.sender)

/-- A surviving receiver still holds mail from subtree `sub` at `key`. An
empty subtree has no members, so this is false. -/
def subtreeCoreMail (D : Description) (w : World) (sub : String) (key : Nat) : Bool :=
  w.roster.any fun host => actorHoldsSubtreeMail D w host sub key (w.st host)

/-- Mail that holds slot `(name, key)`. A nonempty subtree holds for every
member at that key, any generation. A template with no subtree holds for its
own senders. The receiver is any host that survives the sender. This is not
emptiness of a mailbox, and the drained signal is not a state of this model. -/
def slotMailHeld (D : Description) (w : World) (name : String) (key : Nat) : Bool :=
  let sub := templateSubtree D name
  if sub == "" then slotCoreMail w name key else subtreeCoreMail D w sub key

/-- No new incarnation of this slot. It is alive, or its tombstone is still on
the supervisor's lane. The tombstone is queued in the seal and is not
receivable while program mail from that stage is in a live queue, so the
handler that would respawn runs only after that mail has left every live
queue. Mail at a dead receiver counts as consumed. Mail is not a second
guard here. -/
def slotRespawnBlocked (_D : Description) (w : World) (parent : InstId) (name : String) (key : Nat) : Bool :=
  slotOccupied w name key || slotTombstoneQueued w parent name key

theorem slotRespawnBlocked_clear (D : Description) (w : World) (parent : InstId) (name : String) (key : Nat)
    (h : slotRespawnBlocked D w parent name key = false) :
    slotOccupied w name key = false ∧ slotTombstoneQueued w parent name key = false := by
  unfold slotRespawnBlocked at h
  exact Bool.or_eq_false_iff.mp h

/-- A per-peer parent births one child at its own key. The spawn is a no-op
while `slotRespawnBlocked` holds: the slot is alive, or its tombstone is
still on the supervisor's lane. The tombstone is queued in the same step
as the seal and is not receivable while program mail from that stage, or
from a descendant sealed with it, sits in a live queue. The handler that
consumes the tombstone therefore runs with that mail already gone, and the
spawn in the handler is not refused for mail.
A core births nobody. A parent that is not alive admits nobody. A spawn the
template does not allow is `none`, and the effect then crashes. -/
def spawnChild (I : Impl) (w : World) (parent : InstId) (child : String) : Option World :=
  match templateOf I.desc child with
  | none => none
  | some t =>
    if t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) && (w.st parent).life == .alive then
      match parent with
      | .core _ => none
      | .peer _ k _ =>
        if slotRespawnBlocked I.desc w parent child k then some w
        else
          let id := InstId.peer child k (maxGen w child k)
          let born := { bornActor I.desc w child k t.initial with parent := some parent }
          some (admitBorn I w id born)
    else if t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) then
      some w
    else none

/-- Install the effect's continuation, unless the effect crashed the roster.
A tombstone enqueue with an empty label or a full lane is `crashWorld`
inside the effect. `proceed` must not overwrite that crashed phase. The
same guard covers every such enqueue: the continuation is one step after
the effect world, not a special case of abort or of the lane. -/
def commitCont (w : World) (id : InstId) (next : Actor) : World :=
  if w.crashed then w else setActor w id next

/-- Run one effect. An actor that is not alive does not run. A `terminate`
inside this transition seals the actor in the same step. A continuation is
`commitCont`: a crash inside the effect is the result, and the parent does
not advance. -/
def execRun (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) : World :=
  if a.life == .alive then
    match k.rest with
    | [] => setActor w id { a with phase := .idle, typestate := k.toState }
    | eff :: _ =>
      let k' := afterHead k
      match eff with
      | .send dst label _hint =>
        match route w I.desc id dst with
        | none => setActor (noteStale w id dst) id (proceed a k')
        | some dstId =>
          let msg : Msg := { label := label, sender := id, callFrom := none }
          enqueueOrPark w I.desc id dstId msg false k'
      | .trySend dst label _hint onFull onGone =>
        let kFull := { k' with rest := onFull, toState := pickState k'.toState k'.toFull }
        let kGone := { k' with rest := onGone, toState := pickState k'.toState k'.toGone }
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
      | .call dst label _hint onNotAdmitted onTimedOut =>
        let kWait := { k' with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
        match resolveId I.desc w id dst with
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
      | .abort =>
        -- The children are sealed, and their tombstones are queued, in this step.
        -- The parent takes the continuation only when that enqueue did not crash.
        -- `offerPrio` writes the lane onto `w'.st id`, so `proceed` starts there.
        let w' := abortChildren I.desc w id
        commitCont w' id (proceed (w'.st id) k')
      | .spawn child =>
        match spawnChild I w id child with
        | some w' => commitCont w' id (proceed (w'.st id) k')
        | none => crashWorld w
      | .terminate =>
        -- Every core crashes the node. pure-stage stops the simulation when a
        -- top-level stage terminates. A per-peer stage in a subtree shuts its
        -- descendants down and the immediate supervisor receives one tombstone.
        -- A lone terminable per-peer with no child and no parked call shuts only
        -- itself down. Anything else, including a missing template, crashes the
        -- roster. Siblings are left alone. There is no per-core shutdown.
        match templateOf I.desc (tname id) with
        | some t =>
          if t.multiplicity == .one then
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
`fall` is every terminate that does not crash a core and does not shut a
per-peer down: a missing template, or a lone per-peer that still has a parked
call. The roster crashes. `crash` is every core. `lone` seals one childless
per-peer. `cascade` seals that per-peer's descendants and queues the parent's
tombstone in the same step. -/
inductive TermStep (I : Impl) (w : World) (id : InstId) (a : Actor) : World → Prop where
  | fall : TermStep I w id a (crashWorld w)
  | crash (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.multiplicity = .one →
      TermStep I w id a (crashWorld w)
  | lone (t : Template) :
      templateOf I.desc (tname id) = some t →
      t.multiplicity = .perPeer →
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
      t.multiplicity = .perPeer →
      t.subtree = "" →
      t.terminable = true →
      hasParkedCall a.parked = false →
      hasChild I.desc w id = true →
      TermStep I w id a (terminateStage I.desc w id a)

/-- Classify `terminate`. Every core crashes the roster. A per-peer in a
subtree shuts its descendants down. A lone terminable per-peer shuts itself
down when it has no parked call. Every other fall-through crashes. -/
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
    by_cases hcore : (t.multiplicity == .one) = true
    · simp [hcore]
      have hone : t.multiplicity = .one := by
        cases hm : t.multiplicity with
        | one => rfl
        | perPeer =>
          simp [hm, show (Multiplicity.perPeer == Multiplicity.one) = false from rfl] at hcore
      exact TermStep.crash t ht hone
    · rw [ite_eq_right hcore]
      have hper : t.multiplicity = .perPeer := by
        cases hm : t.multiplicity with
        | perPeer => rfl
        | one =>
          simp [hm, show (Multiplicity.one == Multiplicity.one) = true from rfl] at hcore
      by_cases htree : (t.multiplicity == .perPeer && t.subtree != "") = true
      · simp only [htree, ite_true]
        have hparts := (Bool.and_eq_true _ _).mp htree
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
          exact TermStep.lone t ht hper hsub htm hpk hch
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
            exact TermStep.cascade t ht hper hsub htm hpk hch
          · rw [ite_eq_right hkids]
            exact TermStep.fall

/-- An alive `terminate` crashes the roster, shuts one childless per-peer down,
or aborts every descendant and notifies the immediate supervisor. A core always
crashes. A stage in a supervision tree does not have to be marked terminable. -/
theorem execRun_terminate (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hlive : a.life = .alive) (hk : ∃ tail, k.rest = .terminate :: tail) :
    execRun I w id a k = crashWorld w ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = .perPeer ∧
        t.subtree = "" ∧ t.terminable = true ∧
        hasParkedCall a.parked = false ∧ hasChild I.desc w id = false ∧
        execRun I w id a k = shutdownActor I.desc w id) ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = .perPeer ∧ t.subtree ≠ "" ∧
        execRun I w id a k = terminateStage I.desc w id a) ∨
      (∃ t, templateOf I.desc (tname id) = some t ∧ t.multiplicity = .perPeer ∧
        t.subtree = "" ∧ t.terminable = true ∧
        hasParkedCall a.parked = false ∧ hasChild I.desc w id = true ∧
        execRun I w id a k = terminateStage I.desc w id a) := by
  have hstep := exec_term_step I w id a k hlive hk
  generalize hw : execRun I w id a k = wR at hstep
  cases hstep with
  | fall => exact Or.inl rfl
  | crash _ _ _ => exact Or.inl rfl
  | lone t ht hper hsub htm hpk hch =>
    exact Or.inr (Or.inl ⟨t, ht, hper, hsub, htm, hpk, hch, rfl⟩)
  | tree t ht hm hsub =>
    exact Or.inr (Or.inr (Or.inl ⟨t, ht, hm, hsub, rfl⟩))
  | cascade t ht hper hsub htm hpk hch =>
    exact Or.inr (Or.inr (Or.inr ⟨t, ht, hper, hsub, htm, hpk, hch, rfl⟩))

/-- A live actor in `.run` performs the head effect. A `terminate` in that
effect seals the actor before this step returns. Anyone who is not alive
has no `exec`: the seal already ran in the step that killed them. -/
def execHead (I : Impl) (w : World) (id : InstId) : Option World :=
  let a := w.st id
  if a.life ≠ .alive then none
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
      some (setActor w id (proceed (w.st id)
        { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }))
    | _ => none

/-- Internal effects and the data result of a peer wait complete as an ordinary
step. The peer timeout is `callTimeout`, on `onTimeout`. A dead actor does
not finish. -/
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

mutual
/-- Bulk sends a program can still perform toward `dst`. One outcome of a
`trySend`, `call`, or `peer` runs, so the count is the maximum of those
alternatives. A replacing branch does not also run the tail. `tailN` is the
count of that tail. -/
def sendsTo (dst : String) : List Eff → Nat
  | [] => 0
  | e :: es => effSends dst e (sendsTo dst es)

def effSends (dst : String) (e : Eff) (tailN : Nat) : Nat :=
  match e with
  | .send d _ _ => (if d == dst then 1 else 0) + tailN
  | .trySend d _ _ onFull onGone =>
    let own := if d == dst then 1 else 0
    max (own + tailN) (max (sendsTo dst onFull) (sendsTo dst onGone))
  | .call d _ _ onNotAdmitted onTimedOut =>
    let own := if d == dst then 1 else 0
    max (own + tailN) (max (own + sendsTo dst onTimedOut) (sendsTo dst onNotAdmitted))
  | .peer onTimeout => max tailN (sendsTo dst onTimeout)
  | _ => tailN
end

/-- Bulk sends still stored on a continuation, counting every outcome branch.
The call's own message is not in these lists: it was already issued. -/
def contSends (dst : String) (k : Cont) : Nat :=
  max (sendsTo dst k.rest)
    (max (sendsTo dst k.onNotAdmitted)
      (max (sendsTo dst k.onTimedOut) (sendsTo dst k.onTimeout)))

/-- Typestate each outcome lands in. `here` is the reply, admitted, and data path. -/
structure BranchAt where
  here : String
  notAdmitted : String := ""
  timedOut : String := ""
  timeout : String := ""
  full : String := ""
  gone : String := ""

/-- The typestate a replacing branch is checked in. Empty keeps `here`. -/
def focus (a : BranchAt) (s : String) : BranchAt :=
  { a with here := if s == "" then a.here else s }

def branchAt (tr : Transition) : BranchAt where
  here := tr.toState
  notAdmitted := tr.toNotAdmitted
  timedOut := tr.toTimedOut
  timeout := tr.toTimeout
  full := tr.toFull
  gone := tr.toGone

def contAt (k : Cont) : BranchAt where
  here := k.toState
  notAdmitted := k.toNotAdmitted
  timedOut := k.toTimedOut
  timeout := k.toTimeout
  full := k.toFull
  gone := k.toGone

/-- Tokens a state must still hold toward `dst`: the budget minus what that
state itself may have in flight. -/
def landFloor (D : Description) (template state dst : String) : Nat :=
  budget D template dst - debt D template state dst

mutual
/-- Maximum of `sends + floor(landing)` over every path. A replacing branch
does not also run the tail, and it lands in its own typestate. -/
def pathReserve (D : Description) (template dst : String) (at_ : BranchAt) : List Eff → Nat
  | [] => landFloor D template at_.here dst
  | e :: es => effReserve D template dst at_ e (pathReserve D template dst at_ es)

def effReserve (D : Description) (template dst : String) (at_ : BranchAt) (e : Eff) (tail : Nat) : Nat :=
  match e with
  | .send d _ _ => (if d == dst then 1 else 0) + tail
  | .trySend d _ _ onFull onGone =>
    let own := if d == dst then 1 else 0
    max (own + tail)
      (max (pathReserve D template dst (focus at_ at_.full) onFull)
        (pathReserve D template dst (focus at_ at_.gone) onGone))
  | .call d _ _ onNotAdmitted onTimedOut =>
    let own := if d == dst then 1 else 0
    max (own + tail)
      (max (pathReserve D template dst (focus at_ at_.notAdmitted) onNotAdmitted)
        (own + pathReserve D template dst (focus at_ at_.timedOut) onTimedOut))
  | .peer onTimeout =>
    max tail (pathReserve D template dst (focus at_ at_.timeout) onTimeout)
  | _ => tail
end

/-- Bulk sends still in the continuation. A parked call uses `contSends`, and
the `TimedOut` alternative also counts the call's own message: that message
stays queued when the deadline fires after admission. -/
def pending (a : Actor) (dst : String) : Nat :=
  match a.phase with
  | .run k | .awaitEffect k => sendsTo dst k.rest
  | .parked _ false k => sendsTo dst k.rest
  | .parked target true k =>
    let own := if tname target == dst then 1 else 0
    max (sendsTo dst k.rest)
      (max (sendsTo dst k.onNotAdmitted)
        (max (own + sendsTo dst k.onTimedOut) (sendsTo dst k.onTimeout)))
  | .awaitReply _ k => max (sendsTo dst k.rest) (sendsTo dst k.onTimedOut)
  | .awaitPeer k => max (sendsTo dst k.rest) (sendsTo dst k.onTimeout)
  | .idle | .crashed => 0

/-- What an actor must still be able to spend: `sends + floor(landing)` over
the paths still open in this phase. A parked call has already been charged
for its own message, `NotAdmitted` is refunded before it runs, and a stale
peer timeout is not one of its branches. Idle reserves the current
typestate's floor. The ingress gate checks `gateHold`. -/
def tokenHold (D : Description) (template dst : String) (a : Actor) : Nat :=
  match a.phase with
  | .idle | .crashed => landFloor D template a.typestate dst
  | .run k | .awaitEffect k => pathReserve D template dst (contAt k) k.rest
  | .awaitPeer k =>
    max (pathReserve D template dst (contAt k) k.rest)
      (pathReserve D template dst (focus (contAt k) k.toTimeout) k.onTimeout)
  | .awaitReply _ k =>
    max (pathReserve D template dst (contAt k) k.rest)
      (pathReserve D template dst (focus (contAt k) k.toTimedOut) k.onTimedOut)
  | .parked _ false k => pathReserve D template dst (contAt k) k.rest
  | .parked target true k =>
    let at_ := contAt k
    let own := if tname target == dst then 1 else 0
    max (pathReserve D template dst at_ k.rest)
      (max (pathReserve D template dst (focus at_ at_.notAdmitted) k.onNotAdmitted - own)
        (pathReserve D template dst (focus at_ at_.timedOut) k.onTimedOut))

/-- The reserve `receiveIngress` checks. It is `tokenHold` on every phase but
a parked call. There it also counts a stale peer timeout and the full
not-admitted path: the count the gate has always used. A successful ingress
still leaves `tokenHold` under the tokens, because that count is smaller. -/
def gateHold (D : Description) (template dst : String) (a : Actor) : Nat :=
  match a.phase with
  | .parked _ true k =>
    let at_ := contAt k
    max (pathReserve D template dst at_ k.rest)
      (max (pathReserve D template dst (focus at_ at_.notAdmitted) k.onNotAdmitted)
        (max (pathReserve D template dst (focus at_ at_.timedOut) k.onTimedOut)
          (pathReserve D template dst (focus at_ at_.timeout) k.onTimeout)))
  | _ => tokenHold D template dst a

theorem tokenHold_le_gate (D : Description) (template dst : String) (a : Actor) :
    tokenHold D template dst a ≤ gateHold D template dst a := by
  cases h : a.phase with
  | parked target c k =>
    cases c with
    | false => simp [tokenHold, gateHold, h]
    | true =>
      unfold tokenHold gateHold
      simp only [h]
      by_cases ho : (tname target == dst) = true
      · simp [ho]
        omega
      · have hf : (tname target == dst) = false := by
          cases hbb : tname target == dst with
          | false => rfl
          | true => exact absurd hbb ho
        simp [hf]
        omega
  | idle => simp [tokenHold, gateHold, h]
  | crashed => simp [tokenHold, gateHold, h]
  | run _ => simp [tokenHold, gateHold, h]
  | awaitEffect _ => simp [tokenHold, gateHold, h]
  | awaitPeer _ => simp [tokenHold, gateHold, h]
  | awaitReply _ _ => simp [tokenHold, gateHold, h]

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

/-- A terminable per-peer with an empty subtree. It has no siblings, so it stays
mute. A core is not in this class: its `terminate` crashes the node. -/
def loneTerminableName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.multiplicity = .perPeer ∧ t.terminable = true ∧ t.subtree = ""

/-- A terminable role that dies with the rest of a named subtree. -/
def subtreeMemberName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.terminable = true ∧ t.subtree ≠ ""

/-- `true` when `name` is a terminable per-peer and belongs to no subtree. -/
def loneTerminableB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.multiplicity == .perPeer && t.terminable && t.subtree == ""
  | none => false

/-- A multiplicity-one template. Its `terminate` crashes the node. The
`terminable` flag is not meaningful on a core. -/
def permanentCore (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.multiplicity == .one
  | none => false

/-- `true` when `name` is a per-peer role, so a kill of its key removes it. -/
def perPeerB (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | some t => t.multiplicity == .perPeer
  | none => false

/-- A per-peer member talks only to a per-peer role of its own subtree.
A core is not per-peer, so a call to one is not enabled. A lone terminable
per-peer is not a subtree member and is not covered here: it stays mute. -/
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
  | .spawn child =>
    match templateOf D child with
    | some ct => supNamed ct.supervisor src && perPeerB D src && perPeerB D child
    | none => false
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
  let need := gateHold I.desc (tname dst) (tname dst) a + 1
  if a.life ≠ .alive || ingressOpen a.phase = false then none
  else if hasIngress I.desc (tname dst) label = false then none
  else if cap ≤ a.box.length then none
  else if loneTerminableB I.desc (tname dst) then none
  else if a.tokens (tname dst) < (need : Int) ||
      a.tokens (tname dst) < (Nat.max (ingressAllowance I.desc w.N (tname dst) label) 1 : Int) then none
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
running; the reservation is `gateHold`. -/
theorem ingress_open (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    (w.st dst).life = .alive ∧ ingressOpen (w.st dst).phase = true ∧
      loneTerminableB I.desc (tname dst) = false ∧
      (gateHold I.desc (tname dst) (tname dst) (w.st dst) : Int) + 1 ≤ (w.st dst).tokens (tname dst) ∧
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
            · exact Int.not_lt.mp (by
                intro hbad
                apply htok
                have hdec : decide ((w.st dst).tokens (tname dst) <
                    (gateHold I.desc (tname dst) (tname dst) (w.st dst) : Int) + 1) = true :=
                  decide_eq_true_iff.mpr hbad
                simp [hdec])

/-- A delivered ingress names a live actor that is idle, parked, or waiting. -/
theorem ingress_ready (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    (w.st dst).life = .alive ∧ ingressOpen (w.st dst).phase = true := by
  obtain ⟨hl, hop, _, _, _⟩ := ingress_open I w w' dst label h
  exact ⟨hl, hop⟩

/-- A scheduler spawn opens a new subtree root. A child of a per-peer stage is
not a root: that stage births it with `Eff.spawn`, at its own key. -/
def rootOf (D : Description) (t : Template) : Bool :=
  match t.supervisor with
  | none => true
  | some name =>
    match templateOf D name with
    | some sup => sup.multiplicity == .one
    | none => false

/-- A scheduler root occupies one key for its whole life. A per-peer child
is born again at its parent's key, so this does not constrain it. -/
def SingleGen (D : Description) (w : World) : Prop :=
  ∀ name k g1 g2 t, templateOf D name = some t → rootOf D t = true →
    InstId.peer name k g1 ∈ w.roster → InstId.peer name k g2 ∈ w.roster →
    g1 = g2

/-- A recorded parent is a different actor. Birth wires a fresh id to the
spawner, and no step points an actor at itself. -/
def NoSelfParent (w : World) : Prop :=
  ∀ id, (w.st id).parent ≠ some id

/-- An alive generation shares its key with no queued tombstone. The next
generation is born only after that tombstone is taken, and nothing queues
it again. -/
def NoTombWhileLive (w : World) : Prop :=
  ∀ name k g host m,
    (w.st (InstId.peer name k g)).life = .alive →
    (w.st host).life = .alive →
    m ∈ (w.st host).prio →
    m.tombstone = true →
    match m.sender with
    | .peer n key _ => n = name → key = k → False
    | .core _ => True

/-- A live child of `parent` keeps that parent's lane free of its tombstone. -/
def TombFresh (D : Description) (w : World) : Prop :=
  ∀ parent n k g,
    let c := InstId.peer n k g
    c ∈ w.roster →
    isChild w parent c = true →
    (w.st c).life = .alive →
    (match templateOf D n with
      | some t => t.tombstone != ""
      | none => false) = true →
    slotTombstoneQueued w parent n k = false

/-- A core supervisor that is not alive admits no new root. -/
def supervisorLive (D : Description) (w : World) (t : Template) : Bool :=
  match t.supervisor with
  | none => true
  | some name =>
    match templateOf D name with
    | none => false
    | some sup =>
      match sup.multiplicity with
      | .one => (w.st (.core name)).life == .alive
      | .perPeer => false

/-- One past every key any member of subtree `sub` has ever used, and at least
`nextKey sub`. A key is not reused. An empty subtree has no shared key space. -/
def freshKey (D : Description) (w : World) (sub : String) : Nat :=
  w.roster.foldl (fun m id =>
    match id with
    | .peer n k _ =>
      if sub != "" && templateSubtree D n == sub then max m (k + 1) else m
    | .core _ => m) (w.nextKey sub)

/-- Roots of `name` under this core that still occupy a population slot.
One slot per such root, up to `N`: alive, or tombstone still queued. The
tombstone is queued in the seal and stays queued until the core receives it,
and the core cannot receive it while that root's mail remains in a live
queue, so the slot is held through the drain without a separate mail count. -/
def rootOutstanding (_D : Description) (w : World) (supervisor name : String) : Nat :=
  w.roster.foldl (fun n id =>
    match id with
    | .peer child k _ =>
      if child == name &&
          ((w.st id).life == .alive ||
            slotTombstoneQueued w (.core supervisor) name k) then n + 1
      else n
    | .core _ => n) 0

/-- Unsupervised roots of `name` that occupy a population slot. Alive counts.
There is no supervisor and no tombstone, so a root that has left `alive`
still counts while any member of its subtree key has mail on a surviving
receiver. The seal clears that root's own mailbox in the same step, so mail
on the root itself does not count. At most `N` of these roots.
`survivesSender` counts an alive host. A supervised slot does not:
`mailInFlight` requires the receiver to be `alive`. This count is the
conservative one, and it is transient. -/
def loneOutstanding (D : Description) (w : World) (name : String) : Nat :=
  w.roster.foldl (fun n id =>
    match id with
    | .peer child k _ =>
      if child == name &&
          ((w.st id).life == .alive || slotMailHeld D w name k) then n + 1
      else n
    | .core _ => n) 0

/-- A root under no supervisor is bounded by `loneOutstanding`: alive roots,
plus roots whose subtree mail is still on a surviving receiver. A root under
a core is bounded by `rootOutstanding`: alive, or tombstone still queued.
The key itself is always fresh. -/
def maySpawnRoot (D : Description) (w : World) (template : String) (t : Template) : Bool :=
  t.multiplicity == .perPeer && rootOf D t && supervisorLive D w t &&
    match t.supervisor with
    | some name => decide (rootOutstanding D w name template < w.N)
    | none => decide (loneOutstanding D w template < w.N)

/-- Install one peer. `next` records the fresh key. The parent is the
incarnation that wired it, or `none` for a scheduler root. -/
def placePeer (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World) : World :=
  let id := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  let w := next { w with roster := w.roster ++ [id] }
  readCells I.desc (setActor w id born) id

/-- Scheduler birth of a per-peer subtree root. The key is fresh (`freshKey`
or `nextIx`). The birth is not enabled while `N` roots of this template
already occupy a population slot. A core-supervised root keeps the slot
while its tombstone is queued. An unsupervised root keeps it while subtree
mail remains on a surviving receiver. A later incarnation of a per-peer
parent's one child is `spawnChild`, which is a no-op while
`slotRespawnBlocked` holds. -/
def spawn (I : Impl) (w : World) (template : String) : Option World :=
  match templateOf I.desc template with
  | none => none
  | some t =>
    if maySpawnRoot I.desc w template t then
      match t.supervisor with
      | some name =>
        let k := freshKey I.desc w t.subtree
        some (placePeer I w template k t.initial (some (.core name))
          (fun w => { w with nextKey := fun s => if s = t.subtree then k + 1 else w.nextKey s }))
      | none =>
        if t.subtree == "" then
          let k := w.nextIx template
          some (placePeer I w template k t.initial none
            (fun w => { w with nextIx := fun n => if n = template then k + 1 else w.nextIx n }))
        else
          let k := freshKey I.desc w t.subtree
          some (placePeer I w template k t.initial none
            (fun w => { w with nextKey := fun s => if s = t.subtree then k + 1 else w.nextKey s }))
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

def stepWorld (I : Impl) (a : Action) (w : World) : Option World :=
  match a with
  | .recvBulk s => receiveBulk I w s
  | .recvPrio s => receivePrio I w s
  | .exec s => execHead I w s
  | .finish s => finishWait I w s
  | .spawn template => spawn I w template
  | .ingress dst label => receiveIngress I w dst label
  | .callTimeout s => callTimeout w s
  | .stutter => if runtimeBusy I w then none else some w

/-- A crashed world is absorbing: spawn, ingress, stutter, and every runtime
action are disabled. A `Run` cannot continue past it. -/
def apply (I : Impl) (a : Action) (w : World) : Option World :=
  match w.crashed with
  | true => none
  | false => stepWorld I a w

theorem apply_step (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w') :
    w.crashed = false ∧ stepWorld I a w = some w' := by
  cases hc : w.crashed with
  | true => simp [apply, hc] at h
  | false =>
    simp [apply, hc] at h
    exact ⟨rfl, h⟩

/-- Data branch of `awaitPeer`: the external result arrived and `rest` runs.
The timeout is a separate `callTimeout` step. A dead actor takes neither. -/
def peerData (I : Impl) (w : World) (id : InstId) : Option World :=
  if (w.st id).life != .alive then none
  else
    match (w.st id).phase with
    | .awaitPeer k => some (setActor w id (proceed (w.st id) k))
    | _ => none

theorem stutter_unchanged (I : Impl) (w w' : World) (h : apply I .stutter w = some w') : w' = w := by
  have ⟨_, hstep⟩ := apply_step I .stutter w w' h
  simp [stepWorld, runtimeBusy] at hstep
  exact hstep.2.symm

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

/-- Every world of a `Run` stepped, so none of them is the absorbing crash.
A crashed world takes no further action, so it cannot sit at an index of a run. -/
theorem run_not_crashed {I : Impl} {N : Nat} (ρ : Run I N) (i : Nat) :
    (ρ.cfg i).crashed = false :=
  (apply_step I (ρ.act i) (ρ.cfg i) (ρ.cfg (i + 1)) (ρ.valid i)).1

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

mutual
/-- Nested program size. Outcome lists count inside the effect that can run them,
so taking `onTimeout`, `onNotAdmitted`, `onFull` or `onGone` is a smaller program. -/
def progFuel : List Eff → Nat
  | [] => 0
  | e :: es => effFuel e + progFuel es

def effFuel : Eff → Nat
  | .trySend _ _ _ onFull onGone => 1 + progFuel onFull + progFuel onGone
  | .call _ _ _ onNotAdmitted onTimedOut => 1 + progFuel onNotAdmitted + progFuel onTimedOut
  | .peer onTimeout => 1 + progFuel onTimeout
  | _ => 1
end

theorem effFuel_pos (e : Eff) : 0 < effFuel e := by
  cases e <;> simp [effFuel] <;> omega

theorem progFuel_tail_lt (e : Eff) (es : List Eff) : progFuel es < progFuel (e :: es) := by
  have h := effFuel_pos e
  simp [progFuel]
  omega

/-- Reply continuation, `onNotAdmitted` and `onTimedOut`: the three ways a call wait ends. -/
def callFuel (k : Cont) : Nat :=
  max (progFuel k.rest) (max (progFuel k.onNotAdmitted) (progFuel k.onTimedOut))

/-- Data continuation and `onTimeout`: the two ways a peer wait ends. -/
def peerFuel (k : Cont) : Nat :=
  max (progFuel k.rest) (progFuel k.onTimeout)

/-- Remaining program. A run counts `rest`, nested arms included. A call wait
(`awaitReply`, or a parked call) is one more than the largest of its reply
continuation, `onNotAdmitted` and `onTimedOut`. A peer wait is one more than
the largest of its data continuation and `onTimeout`. An effect wait is one
more than `rest`. The extra one makes every exit, including a timeout into a
longer arm, strictly smaller.
(DECISIONS.md 2026-11-19, "Every external wait carries a timeout";
2026-11-22, "A call waits on its own outcomes".) -/
def phaseFuel : Phase → Nat
  | .idle | .crashed => 0
  | .run k => 2 * progFuel k.rest
  | .parked _ false k => 2 * progFuel k.rest + 1
  | .parked _ true k => 2 * callFuel k + 1
  | .awaitReply _ k => 2 * callFuel k + 1
  | .awaitEffect k => 2 * progFuel k.rest + 1
  | .awaitPeer k => 2 * peerFuel k + 1

theorem phaseFuel_proceed_le (a : Actor) (k : Cont) :
    phaseFuel (proceed a k).phase ≤ 2 * progFuel k.rest := by
  cases hk : k.rest <;> simp [proceed, phaseFuel, progFuel, hk]

theorem peer_enter_fuel (tail o : List Eff) :
    2 * max (progFuel tail) (progFuel o) + 1 < 2 * progFuel (.peer o :: tail) := by
  simp [progFuel, effFuel]
  have hmax : max (progFuel tail) (progFuel o) ≤ progFuel tail + progFuel o := by
    rw [Nat.max_le]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  omega

theorem call_enter_fuel (dst label : String) (hint : Nat) (tail na to : List Eff) :
    2 * max (progFuel tail) (max (progFuel na) (progFuel to)) + 1 <
      2 * progFuel (.call dst label hint na to :: tail) := by
  simp [progFuel, effFuel]
  have hmax : max (progFuel tail) (max (progFuel na) (progFuel to)) ≤
      progFuel tail + progFuel na + progFuel to := by
    rw [Nat.max_le, Nat.max_le]
    omega
  omega

theorem arm_enter_fuel (dst label : String) (hint : Nat) (arm other tail : List Eff) :
    2 * progFuel arm < 2 * progFuel (.trySend dst label hint arm other :: tail) := by
  simp [progFuel, effFuel]
  omega

theorem effect_enter_fuel (tail : List Eff) :
    2 * progFuel tail + 1 < 2 * progFuel (.internal :: tail) := by
  simp [progFuel, effFuel]
  omega

theorem finish_peer_drops (a : Actor) (k : Cont) :
    phaseFuel (proceed a k).phase < phaseFuel (.awaitPeer k) := by
  have hle := phaseFuel_proceed_le a k
  have hrest : progFuel k.rest ≤ peerFuel k := by
    unfold peerFuel
    exact Nat.le_max_left _ _
  have hgoal : phaseFuel (.awaitPeer k) = 2 * peerFuel k + 1 := by
    simp [phaseFuel]
  rw [hgoal]
  omega

theorem timeout_peer_drops (a : Actor) (k : Cont) :
    phaseFuel (proceed a { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }).phase <
      phaseFuel (.awaitPeer k) := by
  have hle := phaseFuel_proceed_le a
    { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }
  have hrest : ({ k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout } : Cont).rest =
      k.onTimeout := rfl
  rw [hrest] at hle
  have hto : progFuel k.onTimeout ≤ peerFuel k := by
    unfold peerFuel
    exact Nat.le_max_right _ _
  have hgoal : phaseFuel (.awaitPeer k) = 2 * peerFuel k + 1 := by
    simp [phaseFuel]
  rw [hgoal]
  omega

theorem finish_effect_drops (a : Actor) (k : Cont) :
    phaseFuel (proceed a k).phase < phaseFuel (.awaitEffect k) := by
  have hle := phaseFuel_proceed_le a k
  have hgoal : phaseFuel (.awaitEffect k) = 2 * progFuel k.rest + 1 := by
    simp [phaseFuel]
  rw [hgoal]
  omega

theorem finish_reply_drops (a : Actor) (dst : InstId) (k : Cont) :
    phaseFuel (proceed a k).phase < phaseFuel (.awaitReply dst k) := by
  have hle := phaseFuel_proceed_le a k
  have hrest : progFuel k.rest ≤ callFuel k := by
    unfold callFuel
    exact Nat.le_max_left _ _
  have hgoal : phaseFuel (.awaitReply dst k) = 2 * callFuel k + 1 := by
    simp [phaseFuel]
  rw [hgoal]
  omega

theorem finish_park_drops (a : Actor) (dst : InstId) (c : Bool) (k : Cont) :
    phaseFuel (proceed a k).phase < phaseFuel (.parked dst c k) := by
  have hle := phaseFuel_proceed_le a k
  cases c with
  | false =>
    have hgoal : phaseFuel (.parked dst false k) = 2 * progFuel k.rest + 1 := by
      simp [phaseFuel]
    rw [hgoal]
    omega
  | true =>
    have hrest : progFuel k.rest ≤ callFuel k := by
      unfold callFuel
      exact Nat.le_max_left _ _
    have hgoal : phaseFuel (.parked dst true k) = 2 * callFuel k + 1 := by
      simp [phaseFuel]
    rw [hgoal]
    omega

mutual
def replyCount : List Eff → Nat
  | [] => 0
  | e :: es => effReplies e + replyCount es

def effReplies : Eff → Nat
  | .reply => 1
  | .trySend _ _ _ onFull onGone => replyCount onFull + replyCount onGone
  | .call _ _ _ onNotAdmitted onTimedOut => replyCount onNotAdmitted + replyCount onTimedOut
  | .peer onTimeout => replyCount onTimeout
  | _ => 0
end

mutual
/-- One count per path. A branch replaces the tail, so the tail's counts are
only the admitted or data path. -/
def pathReplies : List Eff → List Nat
  | [] => [0]
  | e :: es => effReplyPaths e (pathReplies es)

def effReplyPaths (e : Eff) (tails : List Nat) : List Nat :=
  match e with
  | .reply => tails.map (· + 1)
  | .trySend _ _ _ onFull onGone => tails ++ pathReplies onFull ++ pathReplies onGone
  | .call _ _ _ onNotAdmitted onTimedOut =>
    tails ++ pathReplies onNotAdmitted ++ pathReplies onTimedOut
  | .peer onTimeout => tails ++ pathReplies onTimeout
  | _ => tails
end

/-- Every path replies exactly `n` times. A sum across alternatives is not enough. -/
def repliesMatch (n : Nat) (es : List Eff) : Bool :=
  (pathReplies es).all (· == n)

mutual
/-- `terminate` occurs on some path before the first `reply`. A reply ends the
scan of that path. Branches that sit before the reply are scanned too. -/
def terminateBeforeReply : List Eff → Bool
  | [] => false
  | e :: es => termBefore e || (termContinues e && terminateBeforeReply es)

def termBefore : Eff → Bool
  | .terminate => true
  | .trySend _ _ _ onFull onGone => terminateBeforeReply onFull || terminateBeforeReply onGone
  | .call _ _ _ onNotAdmitted onTimedOut =>
    terminateBeforeReply onNotAdmitted || terminateBeforeReply onTimedOut
  | .peer onTimeout => terminateBeforeReply onTimeout
  | _ => false

/-- A `terminate` or a `reply` ends the path. Later effects are not a reply's prefix. -/
def termContinues : Eff → Bool
  | .terminate => false
  | .reply => false
  | _ => true
end

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

theorem creditLive_roster (w : World) (dst : String) (s : InstId) :
    (creditLive w dst s).roster = w.roster :=
  credit_roster w dst (budgetHolder w s)

theorem creditLive_nextIx (w : World) (dst : String) (s : InstId) :
    (creditLive w dst s).nextIx = w.nextIx :=
  credit_nextIx w dst (budgetHolder w s)

theorem creditLive_N (w : World) (dst : String) (s : InstId) :
    (creditLive w dst s).N = w.N :=
  credit_N w dst (budgetHolder w s)

theorem refundMsgs_roster (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).roster = w.roster := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, creditLive_roster]

theorem refundMsgs_nextIx (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).nextIx = w.nextIx := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, creditLive_nextIx]

theorem refundMsgs_N (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).N = w.N := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, creditLive_N]

theorem refundParked_roster (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).roster = w.roster := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, creditLive_roster]

theorem refundParked_nextIx (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).nextIx = w.nextIx := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, creditLive_nextIx]

theorem refundParked_N (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).N = w.N := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) =
        refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, creditLive_N]

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
    have h1 := credit_fields w name (budgetHolder w m.sender) i
    have h2 := ih (creditLive w name m.sender)
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
    have h1 := credit_fields w name (budgetHolder w p.msg.sender) i
    have h2 := ih (creditLive w name p.msg.sender)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
      h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem refundMsgs_phase_life (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w name ms).st i).life = (w.st i).life := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    have hcred := credit_phase_life w name (budgetHolder w m.sender) i
    have hih := ih (creditLive w name m.sender)
    exact ⟨hih.1.trans hcred.1, hih.2.trans hcred.2⟩

theorem refundParked_phase_life (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).phase = (w.st i).phase ∧
      ((refundParked w name ps).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    have hcred := credit_phase_life w name (budgetHolder w p.msg.sender) i
    have hih := ih (creditLive w name p.msg.sender)
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
    have h1 := credit_rest w name (budgetHolder w m.sender) i
    have h2 := ih (creditLive w name m.sender)
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
    have h1 := credit_rest w name (budgetHolder w p.msg.sender) i
    have h2 := ih (creditLive w name p.msg.sender)
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
    simp [creditLive, creditSender, setActor]

theorem refundParked_cell (w : World) (name : String) (ps : List Parked) (d l : String) :
    ((refundParked w name ps).cell d l) = w.cell d l := by
  induction ps generalizing w with
  | nil => unfold refundParked; rfl
  | cons p ps ih =>
    unfold refundParked
    simp only [List.foldl_cons]
    rw [← refundParked, ih]
    simp [creditLive, creditSender, setActor]

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

theorem setActor_life_ne (w : World) (id : InstId) (a : Actor) (i : InstId) (hne : i ≠ id) :
    ((setActor w id a).st i).life = (w.st i).life := by
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
    exact (ih _).trans (credit_core_life _ _ (budgetHolder _ m.sender) _)

theorem refundParked_core_life (w : World) (dstName : String) (ps : List Parked) (name : String) :
    ((refundParked w dstName ps).st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [refundParked, List.foldl_cons]
    exact (ih _).trans (credit_core_life _ _ (budgetHolder _ p.msg.sender) _)

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

/-- Resuming other senders does not touch the actor being released. A parked
entry whose sender is that actor is skipped, and every other resume writes a
different id. `Inv2.releaseParked_self` is the same fact for the whole actor. -/
theorem releaseParked_spares (w : World) (id : InstId) (ps : List Parked) :
    ((releaseParked w id ps).st id).phase = (w.st id).phase ∧
      ((releaseParked w id ps).st id).life = (w.st id).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    split
    · next => exact ih _
    · next hskip =>
      have hne : p.sender ≠ id := by
        intro hs
        exact hskip (by simp [hs])
      have hst : (setActor w p.sender (resumeSender (w.st p.sender) false id)).st id = w.st id := by
        simp [setActor, Ne.symm hne]
      have hih := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      rw [hst] at hih
      exact hih

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
  simp only [deliver] at h
  have hcells : ∀ i, ((readCells I.desc w id).st i).life = (w.st i).life :=
    fun i => congrArg Actor.life (cellsSt I.desc w id i)
  revert h
  split
  · intro h; cases h
  · intro h
    split at h
    · cases h
      exact ⟨rfl, hcells⟩
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
          have hcred := (credit_phase_life (setActor w1 id a1) (tname id) (budgetHolder (setActor w1 id a1) p.msg.sender) i).2
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
          exact ((credit_phase_life (setActor w1 id a1) (tname id) (budgetHolder (setActor w1 id a1) m.sender) i).2).trans hset
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
          have hcred := (credit_phase_life (setActor w1 id admitted) (tname id) (budgetHolder (setActor w1 id admitted) m.sender) i).2
          by_cases hs : i = p.sender
          · rw [hs] at hcred hset ⊢
            simp only [setActor, ite_true, resume_keeps_life]
            exact hcred.trans hset
          · simp only [setActor, hs]
            exact hcred.trans hset

theorem receivePrio_keeps_life (I : Impl) (w w' : World) (id i : InstId)
    (h : receivePrio I w id = some w') : (w'.st i).life = (w.st i).life := by
  obtain ⟨m, pre, suf, w1, a1, _, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  have hkeep := deliver_life I w id { (w.st id) with prio := pre ++ suf } m w1 a1 hdel
  rw [hw']
  by_cases hi : i = id
  · rw [hi]
    simpa [setActor] using hkeep.1
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
      cases hsup : t.supervisor with
      | some supName =>
        simp only [hsup] at h
        cases h
        unfold placePeer
        have hpeer : InstId.core name ≠
            InstId.peer template (freshKey I.desc w t.subtree) (maxGen w template (freshKey I.desc w t.subtree)) := by
          intro h; cases h
        simp [setActor, cellsSt, hpeer]
      | none =>
        simp only [hsup] at h
        by_cases hsub : (t.subtree == "") = true
        · simp only [hsub, ite_true] at h
          cases h
          unfold placePeer
          have hpeer : InstId.core name ≠ InstId.peer template (w.nextIx template) (maxGen w template (w.nextIx template)) := by
            intro h; cases h
          simp [setActor, cellsSt, hpeer]
        · have hsubF : (t.subtree == "") = false := by simpa [Bool.not_eq_true] using hsub
          simp only [hsubF, ite_false] at h
          cases h
          unfold placePeer
          have hpeer : InstId.core name ≠
              InstId.peer template (freshKey I.desc w t.subtree) (maxGen w template (freshKey I.desc w t.subtree)) := by
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

/-- Releasing one actor leaves everyone else's life alone. -/
theorem releaseWorld_other_life (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (hne : i ≠ id) : ((releaseWorld D w id a).st i).life = (w.st i).life := by
  simp only [releaseWorld]
  exact (releaseParked_life _ id a.parked i).trans
    ((setActor_life_ne _ id _ i hne).trans
      ((releaseOutbound_life _ id i).trans
        ((refundParked_phase_life _ _ _ i).2.trans
          ((refundMsgs_phase_life _ _ _ i).2.trans
            (congrArg Actor.life (cellsSt D w id i))))))

/-- A release does not bring anyone back to life. -/
theorem releaseWorld_prev (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (h : ((releaseWorld D w id a).st i).life = .alive) : (w.st i).life = .alive := by
  by_cases hne : i = id
  · rw [hne] at h
    simp [releaseWorld_self_dead D w id a] at h
  · exact (releaseWorld_other_life D w id a i hne).symm ▸ h

theorem failWaiters_life (w : World) (dead s : InstId) :
    ((failWaiters w dead).st s).life = (w.st s).life := by
  simpa [failWaiters] using failFold_life w dead s w.roster

theorem crashWorld_prev (w : World) (i : InstId)
    (h : ((crashWorld w).st i).life = .alive) : (w.st i).life = .alive := by
  simp only [crashWorld] at h
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp only [hmem, ite_true, crashActor] at h
    by_cases hgo : ((w.st i).life == .alive) = true
    · simp [hgo] at h
    · simpa [hgo] using h
  · simpa [hmem] using h

theorem crashWorld_keeps_dead (w : World) (i : InstId) (h : (w.st i).life = .dead) :
    ((crashWorld w).st i).life = .dead := by
  simp only [crashWorld]
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp only [hmem, ite_true, crashActor]
    have hgo : ((w.st i).life == .alive) = false := by
      simp [h]
    simp [hgo, h]
  · simpa [hmem] using h

/-- `crashActor` rewrites only an alive actor. A stage already installed dead
and idle stays dead and idle when a later tombstone crashes the roster. -/
theorem crashWorld_keeps_idle (w : World) (i : InstId)
    (hdead : (w.st i).life = .dead) (hidle : (w.st i).phase = .idle) :
    ((crashWorld w).st i).life = .dead ∧ ((crashWorld w).st i).phase = .idle := by
  simp only [crashWorld]
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp only [hmem, ite_true, crashActor]
    have hgo : ((w.st i).life == .alive) = false := by
      simp [hdead]
    simp [hgo, hdead, hidle]
  · simpa [hmem] using ⟨hdead, hidle⟩

/-- A tombstone step that leaves `i` alive did not create that life. A crash,
a missing label, or a full lane does not leave an alive actor that was absent. -/
theorem enqueueTombstone_life (D : Description) (w : World) (child i : InstId)
    (h : ((enqueueTombstone D w child).st i).life = .alive) : (w.st i).life = .alive := by
  unfold enqueueTombstone at h
  cases hpar : (w.st child).parent with
  | none => simpa [hpar] using h
  | some parent =>
    simp only [hpar] at h
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp only [hlive, ite_true] at h
      exact h
    · have hliveF : ((w.st parent).life != .alive) = false := by
        simpa [Bool.not_eq_true] using hlive
      simp only [hliveF, ite_false] at h
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true] at h
        exact crashWorld_prev w i h
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          simpa [Bool.not_eq_true] using hlab
        simp only [hlabF, ite_false] at h
        unfold offerPrio at h
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp only [hfull, ite_true] at h
          exact crashWorld_prev w i h
        · have hroom : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            simpa [Bool.not_eq_true] using hfull
          simp only [hroom, ite_false] at h
          by_cases hi : i = parent
          · rw [hi] at h ⊢
            simp [setActor] at h
            exact h
          · simpa [setActor, hi] using h

theorem enqueueTombstone_keeps_dead (D : Description) (w : World) (child i : InstId)
    (h : (w.st i).life = .dead) : ((enqueueTombstone D w child).st i).life = .dead := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simpa [hpar] using h
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp only [hlive, ite_true]
      exact h
    · have hliveF : ((w.st parent).life != .alive) = false := by
        simpa [Bool.not_eq_true] using hlive
      simp only [hliveF, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        exact crashWorld_keeps_dead w i h
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          simpa [Bool.not_eq_true] using hlab
        simp only [hlabF, ite_false]
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp only [hfull, ite_true, offerPrio]
          exact crashWorld_keeps_dead w i h
        · have hroom : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            simpa [Bool.not_eq_true] using hfull
          simp only [hroom, ite_false, offerPrio]
          by_cases hi : i = parent
          · rw [hi] at h ⊢
            simp [setActor, h]
          · simpa [setActor, hi] using h

/-- Queueing a tombstone, or crashing because it does not fit, leaves a dead
idle actor dead and idle. The crash rewrites alive actors only, and a
successful offer changes the supervisor's priority lane, not this phase. -/
theorem enqueueTombstone_keeps_idle (D : Description) (w : World) (child i : InstId)
    (hdead : (w.st i).life = .dead) (hidle : (w.st i).phase = .idle) :
    ((enqueueTombstone D w child).st i).life = .dead ∧
      ((enqueueTombstone D w child).st i).phase = .idle := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simpa [hpar] using ⟨hdead, hidle⟩
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp only [hlive, ite_true]
      exact ⟨hdead, hidle⟩
    · have hliveF : ((w.st parent).life != .alive) = false := by
        simpa [Bool.not_eq_true] using hlive
      simp only [hliveF, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        exact crashWorld_keeps_idle w i hdead hidle
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          simpa [Bool.not_eq_true] using hlab
        simp only [hlabF, ite_false]
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp only [hfull, ite_true, offerPrio]
          exact crashWorld_keeps_idle w i hdead hidle
        · have hroom : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            simpa [Bool.not_eq_true] using hfull
          simp only [hroom, ite_false, offerPrio]
          by_cases hi : i = parent
          · rw [hi] at hdead hidle ⊢
            simp [setActor, hdead, hidle]
          · simpa [setActor, hi] using ⟨hdead, hidle⟩

/-- A tombstone that leaves a core alive did not create that life. Crashing the
roster kills every alive core, so the equality of lives does not hold. -/
theorem tombstone_core_life (D : Description) (w : World) (child : InstId) (name : String)
    (h : ((enqueueTombstone D w child).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive :=
  enqueueTombstone_life D w child (InstId.core name) h

theorem sealActor_self_dead (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((sealActor D w id a).st id).life = .dead := by
  unfold sealActor
  exact enqueueTombstone_keeps_dead D (releaseWorld D w id a) id id (releaseWorld_self_dead D w id a)

/-- Releasing `id` installs it dead and idle, then resumes other senders.
Those resumes never write `id`. -/
theorem releaseWorld_self_idle (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).life = .dead ∧
      ((releaseWorld D w id a).st id).phase = .idle := by
  let w1 := releaseOutbound (refundParked (refundMsgs (readCells D w id) (tname id) a.box)
    (tname id) a.parked) id
  let dead : Actor :=
    { w1.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hworld : releaseWorld D w id a = releaseParked (setActor w1 id dead) id a.parked := by
    simp [releaseWorld, w1, dead]
  have hv := releaseParked_spares (setActor w1 id dead) id a.parked
  have hset : ((setActor w1 id dead).st id).life = .dead ∧
      ((setActor w1 id dead).st id).phase = .idle := by
    simp [setActor, dead]
  rw [hworld]
  exact ⟨hv.2.trans hset.1, hv.1.trans hset.2⟩

/-- Sealing a live actor leaves it dead and idle, including when the tombstone
does not fit and the roster crashes. `releaseWorld` installs the dead idle
actor before the offer, and `crashActor` does not rewrite an actor that is
already dead. -/
theorem shutdownActor_alive_idle (D : Description) (w : World) (id : InstId)
    (hl : (w.st id).life = .alive) :
    ((shutdownActor D w id).st id).life = .dead ∧
      ((shutdownActor D w id).st id).phase = .idle := by
  unfold shutdownActor
  have hbit : ((w.st id).life == .alive) = true := by simp [hl]
  simp only [hbit, ite_true, sealActor]
  have hrel := releaseWorld_self_idle D w id (w.st id)
  exact enqueueTombstone_keeps_idle D (releaseWorld D w id (w.st id)) id id hrel.1 hrel.2

theorem shutdownActor_prev (D : Description) (w : World) (id i : InstId)
    (h : ((shutdownActor D w id).st i).life = .alive) : (w.st i).life = .alive := by
  unfold shutdownActor at h
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true] at h
    unfold sealActor at h
    exact releaseWorld_prev D w id (w.st id) i
      (enqueueTombstone_life D (releaseWorld D w id (w.st id)) id i h)
  · simpa [hlive] using h

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

/-- Sealing a branch does not bring anyone back to life. -/
theorem sealBranch_prev (fuel : Nat) (D : Description) (i : InstId) :
    ∀ (id : InstId) (w : World),
      ((sealBranch fuel D w id).st i).life = .alive → (w.st i).life = .alive := by
  induction fuel with
  | zero =>
    intro id w h
    simpa [sealBranch] using h
  | succ fuel ih =>
    intro id w h
    simp only [sealBranch] at h
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel D w0 child else w0
    have hfold : ∀ (ids : List InstId) (w0 : World),
        ((ids.foldl step w0).st i).life = .alive → (w0.st i).life = .alive := by
      intro ids
      induction ids with
      | nil => intro _ h0; exact h0
      | cons child ids ihids =>
        intro w0 h0
        simp only [List.foldl_cons, step] at h0
        by_cases hc : isChild w0 id child = true
        · simp only [hc, ite_true] at h0
          exact ih child w0 (ihids _ h0)
        · have hf : isChild w0 id child = false := by
            cases hb : isChild w0 id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf] at h0
          exact ihids w0 h0
    let sealed := w.roster.foldl step w
    change ((if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id) else sealed).st i).life = .alive at h
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · simp only [hgo, ite_true] at h
      exact hfold w.roster w (releaseWorld_prev D sealed id (sealed.st id) i h)
    · have hf : ((sealed.st id).life == .alive) = false := by
        cases hb : (sealed.st id).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf] at h
      exact hfold w.roster w h

/-- Dropping descendants does not bring anyone back to life. -/
theorem dropDescendants_prev (D : Description) (w : World) (id i : InstId)
    (h : ((dropDescendants D w id).st i).life = .alive) : (w.st i).life = .alive := by
  unfold dropDescendants at h
  have hfold : ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch w.roster.length D acc child else acc) w0).st i).life =
        .alive → (w0.st i).life = .alive := by
    intro ids
    induction ids with
    | nil => intro _ h0; exact h0
    | cons child ids ihids =>
      intro w0 h0
      simp only [List.foldl_cons] at h0
      by_cases hc : isChild w0 id child = true
      · simp only [hc, ite_true] at h0
        exact sealBranch_prev _ D i child w0 (ihids _ h0)
      · have hf : isChild w0 id child = false := by
          cases hb : isChild w0 id child with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf, ite_false] at h0
        exact ihids w0 h0
  exact hfold w.roster w h

/-- Sealing a stage does not bring a core to life. -/
theorem terminateStage_core_prev (D : Description) (w : World) (id : InstId) (a : Actor)
    (name : String) (h : ((terminateStage D w id a).st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  unfold terminateStage at h
  exact dropDescendants_prev D w id (InstId.core name)
    (shutdownActor_prev D (dropDescendants D w id) id (InstId.core name) h)

theorem abortChildren_prev (D : Description) (w : World) (parent i : InstId)
    (h : ((abortChildren D w parent).st i).life = .alive) : (w.st i).life = .alive := by
  unfold abortChildren at h
  have hfold : ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w0).st i).life = .alive → (w0.st i).life = .alive := by
    intro ids
    induction ids with
    | nil => intro _ h0; exact h0
    | cons child ids ihids =>
      intro w0 h0
      simp only [List.foldl_cons] at h0
      by_cases hc : (isChild w0 parent child && (w0.st child).life == .alive) = true
      · simp only [hc, ite_true] at h0
        exact dropDescendants_prev D w0 child i
          (shutdownActor_prev D (dropDescendants D w0 child) child i (ihids _ h0))
      · have hf : (isChild w0 parent child && (w0.st child).life == .alive) = false := by
          cases hb : isChild w0 parent child && (w0.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf, ite_false] at h0
        exact ihids w0 h0
  exact hfold w.roster w h

theorem setActor_parent_keep (w : World) (id : InstId) (a : Actor) (i : InstId)
    (hp : a.parent = (w.st id).parent) : ((setActor w id a).st i).parent = (w.st i).parent := by
  by_cases hi : i = id
  · simp [hi, setActor_self, hp]
  · simp [setActor_other w id i a hi]

theorem setActor_crashed (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).crashed = w.crashed := rfl

theorem bumpToken_parent (a : Actor) (dst : String) (d : Int) :
    (bumpToken a dst d).parent = a.parent := rfl

theorem addTokens_parent (a : Actor) (name : String) (n : Nat) :
    (addTokens a name n).parent = a.parent := rfl

theorem proceed_parent (a : Actor) (k : Cont) : (proceed a k).parent = a.parent := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem chargeSender_parent (a : Actor) (dst : String) : (chargeSender a dst).parent = a.parent := rfl

theorem issueCall_parent (a : Actor) : (issueCall a).parent = a.parent := rfl

theorem finishCall_parent (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).parent = a.parent := by
  simp [finishCall, proceed_parent]

theorem detachHost_parent (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).parent = a.parent := by
  unfold detachReply detachBox
  split <;> rfl

theorem resumeSender_parent (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).parent = a.parent := by
  unfold resumeSender
  split
  · split
    · rfl
    · exact proceed_parent _ _
  · rfl

theorem creditSender_parent (w : World) (tmpl : String) (s i : InstId) :
    ((creditSender w tmpl s).st i).parent = (w.st i).parent := by
  unfold creditSender
  exact setActor_parent_keep w s _ i (bumpToken_parent _ _ _)

theorem creditSender_crashed (w : World) (tmpl : String) (s : InstId) :
    (creditSender w tmpl s).crashed = w.crashed := rfl

theorem creditFold_parent (w : World) (name : String) (sender : InstId) (ps : List Parked)
    (i : InstId) :
    ((ps.foldl (fun w _ => creditSender w name sender) w).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil => rfl
  | cons _ ps ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (creditSender_parent w name sender i)

theorem refundCall_parent (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).parent = (w.st i).parent := by
  unfold refundParkedCall
  dsimp only
  split
  · rfl
  · exact (creditFold_parent _ (tname dst) caller _ i).trans (setActor_parent_keep _ _ _ _ rfl)

theorem creditLive_parent (w : World) (tmpl : String) (s i : InstId) :
    ((creditLive w tmpl s).st i).parent = (w.st i).parent :=
  creditSender_parent w tmpl _ i

theorem creditLive_crashed (w : World) (tmpl : String) (s : InstId) :
    (creditLive w tmpl s).crashed = w.crashed := rfl

theorem refundMsgs_parent (w : World) (name : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w name ms).st i).parent = (w.st i).parent := by
  induction ms generalizing w with
  | nil => rfl
  | cons m ms ih =>
    rw [show refundMsgs w name (m :: ms) = refundMsgs (creditLive w name m.sender) name ms from rfl]
    rw [ih, creditLive_parent]

theorem refundMsgs_crashed (w : World) (name : String) (ms : List Msg) :
    (refundMsgs w name ms).crashed = w.crashed := by
  induction ms generalizing w with
  | nil => rfl
  | cons m ms ih =>
    rw [show refundMsgs w name (m :: ms) = refundMsgs (creditLive w name m.sender) name ms from rfl]
    rw [ih, creditLive_crashed]

theorem refundParked_parent (w : World) (name : String) (ps : List Parked) (i : InstId) :
    ((refundParked w name ps).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [show refundParked w name (p :: ps) = refundParked (creditLive w name p.msg.sender) name ps from rfl]
    rw [ih, creditLive_parent]

theorem refundParked_crashed (w : World) (name : String) (ps : List Parked) :
    (refundParked w name ps).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [show refundParked w name (p :: ps) = refundParked (creditLive w name p.msg.sender) name ps from rfl]
    rw [ih, creditLive_crashed]

theorem readCells_parent (D : Description) (w : World) (id i : InstId) :
    ((readCells D w id).st i).parent = (w.st i).parent :=
  congrArg (fun a : Actor => a.parent) (cellsSt D w id i)

private theorem readCells_crashed (D : Description) (w : World) (id : InstId) :
    (readCells D w id).crashed = w.crashed := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact ih _

theorem admitBorn_crashed (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).crashed = w.crashed := by
  simp [admitBorn, setActor_crashed, readCells_crashed]

private theorem releaseOutbound_step_parent (w : World) (dead host i : InstId) :
    ((if host == dead then w
      else
        let dropped := (w.st host).parked.filter fun p => p.sender == dead
        if dropped.isEmpty then w
        else
          let w := setActor w host
            { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
          setActor w dead (addTokens (w.st dead) (tname host) dropped.length)).st i).parent =
      (w.st i).parent := by
  by_cases hd : (host == dead) = true
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd]
    by_cases he : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · rw [ite_eq_left he]
    · rw [ite_eq_right he]
      rw [setActor_parent_keep _ dead _ i (addTokens_parent _ _ _)]
      exact setActor_parent_keep _ host _ i rfl

private theorem releaseOutbound_step_crashed (w : World) (dead host : InstId) :
    (if host == dead then w
      else
        let dropped := (w.st host).parked.filter fun p => p.sender == dead
        if dropped.isEmpty then w
        else
          let w := setActor w host
            { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
          setActor w dead (addTokens (w.st dead) (tname host) dropped.length)).crashed =
      w.crashed := by
  by_cases hd : (host == dead) = true
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd]
    by_cases he : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · rw [ite_eq_left he]
    · rw [ite_eq_right he]
      rw [setActor_crashed, setActor_crashed]

theorem releaseOutbound_parent (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).parent = (w.st i).parent := by
  unfold releaseOutbound
  generalize w.roster = ids
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (releaseOutbound_step_parent w dead host i)

theorem releaseOutbound_crashed (w : World) (dead : InstId) :
    (releaseOutbound w dead).crashed = w.crashed := by
  unfold releaseOutbound
  generalize w.roster = ids
  induction ids generalizing w with
  | nil => rfl
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (releaseOutbound_step_crashed w dead host)

theorem releaseParked_parent (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    unfold releaseParked
    simp only [List.foldl_cons]
    split
    · exact ih _
    · exact (ih _).trans (setActor_parent_keep _ p.sender _ i (resumeSender_parent _ _ _))

theorem releaseParked_crashed (w : World) (id : InstId) (ps : List Parked) :
    (releaseParked w id ps).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => rfl
  | cons p ps ih =>
    unfold releaseParked
    simp only [List.foldl_cons]
    split
    · exact ih _
    · exact (ih _).trans (setActor_crashed _ _ _)

theorem releaseWorld_parent (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((releaseWorld D w id a).st i).parent = (w.st i).parent := by
  simp only [releaseWorld]
  rw [releaseParked_parent, setActor_parent_keep]
  · rw [releaseOutbound_parent, refundParked_parent, refundMsgs_parent, readCells_parent]
  · rfl

theorem releaseWorld_crashed (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).crashed = w.crashed := by
  simp only [releaseWorld]
  rw [releaseParked_crashed, setActor_crashed, releaseOutbound_crashed, refundParked_crashed,
    refundMsgs_crashed, readCells_crashed]

theorem crashWorld_parent (w : World) (i : InstId) :
    ((crashWorld w).st i).parent = (w.st i).parent := by
  simp only [crashWorld]
  by_cases hm : decide (i ∈ w.roster) = true
  · simp only [hm, ite_true, crashActor]
    by_cases ha : ((w.st i).life == .alive) = true
    · simp [ha]
    · simp [ha]
  · simp [hm]

theorem crashWorld_is_crashed (w : World) : (crashWorld w).crashed = true := rfl

theorem offerPrio_parent (D : Description) (w : World) (host : InstId) (msg : Msg) (i : InstId) :
    ((offerPrio D w host msg).st i).parent = (w.st i).parent := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = true
  · simp only [hfull, ite_true]
    exact crashWorld_parent w i
  · have hf : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = false := by
      simpa [Bool.not_eq_true] using hfull
    simp only [hf, ite_false]
    exact setActor_parent_keep _ host _ i rfl

theorem enqueueTombstone_parent (D : Description) (w : World) (child i : InstId) :
    ((enqueueTombstone D w child).st i).parent = (w.st i).parent := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simp [hpar]
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp [hlive]
    · have hf : ((w.st parent).life != .alive) = false := by
        simpa [Bool.not_eq_true] using hlive
      simp only [hf, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        exact crashWorld_parent w i
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          simpa [Bool.not_eq_true] using hlab
        simp only [hlabF, ite_false]
        exact offerPrio_parent D w parent _ i

/-- A tombstone that does not crash leaves every life where it was. -/
theorem enqueueTombstone_life_stable (D : Description) (w : World) (child i : InstId)
    (hcr : (enqueueTombstone D w child).crashed = false) :
    ((enqueueTombstone D w child).st i).life = (w.st i).life := by
  unfold enqueueTombstone at hcr ⊢
  cases hpar : (w.st child).parent with
  | none => simp [hpar]
  | some parent =>
    simp only [hpar] at hcr ⊢
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp [hlive]
    · have hf : ((w.st parent).life != .alive) = false := by
        simpa [Bool.not_eq_true] using hlive
      simp only [hf, ite_false] at hcr ⊢
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true] at hcr
        simp [crashWorld_is_crashed] at hcr
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          simpa [Bool.not_eq_true] using hlab
        simp only [hlabF, ite_false] at hcr ⊢
        unfold offerPrio at hcr ⊢
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · simp only [hfull, ite_true] at hcr
          simp [crashWorld_is_crashed] at hcr
        · have hroom : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = false := by
            simpa [Bool.not_eq_true] using hfull
          simp only [hroom, ite_false]
          by_cases hi : i = parent
          · simp [hi, setActor]
          · simp [setActor, hi]

theorem sealActor_parent (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((sealActor D w id a).st i).parent = (w.st i).parent := by
  unfold sealActor
  rw [enqueueTombstone_parent, releaseWorld_parent]

theorem shutdownActor_parent (D : Description) (w : World) (id i : InstId) :
    ((shutdownActor D w id).st i).parent = (w.st i).parent := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true]
    exact sealActor_parent D w id (w.st id) i
  · simp [hlive]

/-- Shutting one actor down leaves everyone else at the same life, unless the
tombstone crashes the roster. -/
theorem shutdownActor_other_life (D : Description) (w : World) (id i : InstId) (hne : i ≠ id)
    (hcr : (shutdownActor D w id).crashed = false) :
    ((shutdownActor D w id).st i).life = (w.st i).life := by
  unfold shutdownActor at hcr ⊢
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true] at hcr ⊢
    unfold sealActor at hcr ⊢
    have hrel : ((releaseWorld D w id (w.st id)).st i).life = (w.st i).life :=
      releaseWorld_other_life D w id (w.st id) i hne
    rw [enqueueTombstone_life_stable D (releaseWorld D w id (w.st id)) id i hcr, hrel]
  · simp [hlive]

theorem enqueueTombstone_crashed_back (D : Description) (w : World) (child : InstId)
    (hcr : (enqueueTombstone D w child).crashed = false) : w.crashed = false := by
  unfold enqueueTombstone at hcr
  cases hpar : (w.st child).parent with
  | none =>
    simp only [hpar] at hcr
    exact hcr
  | some parent =>
    simp only [hpar] at hcr
    by_cases hlive : ((w.st parent).life != .alive) = true
    · rw [ite_eq_left hlive] at hcr
      exact hcr
    · rw [ite_eq_right hlive] at hcr
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · rw [ite_eq_left hlab] at hcr
        simp [crashWorld_is_crashed] at hcr
      · rw [ite_eq_right hlab] at hcr
        unfold offerPrio at hcr
        by_cases hfull : decide (prioLoad (w.st parent).prio >= capPrio D w.N parent) = true
        · rw [ite_eq_left hfull] at hcr
          simp [crashWorld_is_crashed] at hcr
        · rw [ite_eq_right hfull] at hcr
          rw [setActor_crashed] at hcr
          exact hcr

theorem shutdownActor_crashed_back (D : Description) (w : World) (id : InstId)
    (hcr : (shutdownActor D w id).crashed = false) : w.crashed = false := by
  unfold shutdownActor at hcr
  by_cases hlive : ((w.st id).life == .alive) = true
  · rw [ite_eq_left hlive] at hcr
    unfold sealActor at hcr
    exact (releaseWorld_crashed D w id (w.st id)).symm.trans
      (enqueueTombstone_crashed_back D (releaseWorld D w id (w.st id)) id hcr)
  · rw [ite_eq_right hlive] at hcr
    exact hcr

theorem isChild_parents {w w' : World} (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (parent child : InstId) : isChild w' parent child = isChild w parent child := by
  simp [isChild, hp]

/-- Sealing a branch keeps parent links and the crash flag, and it changes a
life only for the sealed actor or one of its strict descendants. -/
theorem sealBranch_stable (fuel : Nat) (D : Description) :
    ∀ (root : InstId) (w : World),
      (∀ i, ((sealBranch fuel D w root).st i).parent = (w.st i).parent) ∧
      (sealBranch fuel D w root).crashed = w.crashed ∧
      ∀ id, ((sealBranch fuel D w root).st id).life = (w.st id).life ∨
        id = root ∨ StrictAncestor w id root := by
  induction fuel with
  | zero =>
    intro root w
    refine ⟨fun _ => rfl, rfl, fun _ => Or.inl rfl⟩
  | succ fuel ih =>
    intro root w
    simp only [sealBranch]
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 root child then sealBranch fuel D w0 child else w0
    have hfold : ∀ (ids : List InstId) (w0 : World),
        (∀ i, (w0.st i).parent = (w.st i).parent) →
        w0.crashed = w.crashed →
        (∀ id, (w0.st id).life = (w.st id).life ∨ id = root ∨ StrictAncestor w id root) →
        (∀ i, ((ids.foldl step w0).st i).parent = (w.st i).parent) ∧
        (ids.foldl step w0).crashed = w.crashed ∧
        ∀ id, ((ids.foldl step w0).st id).life = (w.st id).life ∨
          id = root ∨ StrictAncestor w id root := by
      intro ids
      induction ids with
      | nil =>
        intro w0 hp hc hl
        exact ⟨hp, hc, hl⟩
      | cons child ids ihids =>
        intro w0 hp hc hl
        simp only [List.foldl_cons, step]
        by_cases hch : isChild w0 root child = true
        · simp only [hch, ite_true]
          have hch0 : isChild w root child = true := by
            rw [← isChild_parents hp, hch]
          have ihc := ih child w0
          have hp1 : ∀ i, ((sealBranch fuel D w0 child).st i).parent = (w.st i).parent := by
            intro i
            rw [ihc.1 i, hp i]
          have hc1 : (sealBranch fuel D w0 child).crashed = w.crashed := by
            rw [ihc.2.1, hc]
          have hl1 : ∀ id, ((sealBranch fuel D w0 child).st id).life = (w.st id).life ∨
              id = root ∨ StrictAncestor w id root := by
            intro id
            rcases ihc.2.2 id with heq | hid | hanc
            · rcases hl id with h0 | hroot | hanc0
              · exact Or.inl (heq.trans h0)
              · exact Or.inr (Or.inl hroot)
              · exact Or.inr (Or.inr hanc0)
            · exact Or.inr (Or.inr (by
                rw [hid]
                exact StrictAncestor.edge (isChild_edge w root child hch0)))
            · exact Or.inr (Or.inr
                (StrictAncestor.trans (StrictAncestor.parents (fun i => (hp i).symm) hanc)
                  (StrictAncestor.edge (isChild_edge w root child hch0))))
          exact ihids _ hp1 hc1 hl1
        · have hf : isChild w0 root child = false := by
            cases hb : isChild w0 root child with
            | false => rfl
            | true => exact absurd hb hch
          simp only [hf, ite_false]
          exact ihids w0 hp hc hl
    have hsealed := hfold w.roster w (fun _ => rfl) rfl (fun _ => Or.inl rfl)
    let sealed := w.roster.foldl step w
    have hsealed_id : sealed = w.roster.foldl step w := rfl
    split
    · next hgo =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        rw [releaseWorld_parent, hsealed.1 i]
      · rw [releaseWorld_crashed, hsealed.2.1]
      · intro id
        by_cases hid : id = root
        · exact Or.inr (Or.inl hid)
        · have hlife := releaseWorld_other_life D sealed root (sealed.st root) id hid
          rcases hsealed.2.2 id with heq | hroot | hanc
          · exact Or.inl (hlife.trans heq)
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr hanc)
    · next hgo =>
      exact hsealed

theorem dropDescendants_stable (D : Description) (w : World) (root : InstId) :
    (∀ i, ((dropDescendants D w root).st i).parent = (w.st i).parent) ∧
    (dropDescendants D w root).crashed = w.crashed ∧
    ∀ id, ((dropDescendants D w root).st id).life = (w.st id).life ∨
      StrictAncestor w id root := by
  unfold dropDescendants
  have hfold : ∀ (ids : List InstId) (w0 : World),
      (∀ i, (w0.st i).parent = (w.st i).parent) →
      w0.crashed = w.crashed →
      (∀ id, (w0.st id).life = (w.st id).life ∨ StrictAncestor w id root) →
      (∀ i, ((ids.foldl (fun acc child =>
        if isChild acc root child then sealBranch w.roster.length D acc child else acc) w0).st i).parent =
          (w.st i).parent) ∧
      (ids.foldl (fun acc child =>
        if isChild acc root child then sealBranch w.roster.length D acc child else acc) w0).crashed =
        w.crashed ∧
      ∀ id, ((ids.foldl (fun acc child =>
        if isChild acc root child then sealBranch w.roster.length D acc child else acc) w0).st id).life =
          (w.st id).life ∨ StrictAncestor w id root := by
    intro ids
    induction ids with
    | nil =>
      intro w0 hp hc hl
      exact ⟨hp, hc, hl⟩
    | cons child ids ih =>
      intro w0 hp hc hl
      simp only [List.foldl_cons]
      by_cases hch : isChild w0 root child = true
      · simp only [hch, ite_true]
        have hch0 : isChild w root child = true := by rw [← isChild_parents hp, hch]
        have ihc := sealBranch_stable w.roster.length D child w0
        have hp1 : ∀ i, ((sealBranch w.roster.length D w0 child).st i).parent = (w.st i).parent :=
          fun i => (ihc.1 i).trans (hp i)
        have hc1 : (sealBranch w.roster.length D w0 child).crashed = w.crashed :=
          (ihc.2.1).trans hc
        have hl1 : ∀ id, ((sealBranch w.roster.length D w0 child).st id).life = (w.st id).life ∨
            StrictAncestor w id root := by
          intro id
          rcases ihc.2.2 id with heq | hid | hanc
          · rcases hl id with h0 | hanc0
            · exact Or.inl (heq.trans h0)
            · exact Or.inr hanc0
          · exact Or.inr (by
              rw [hid]
              exact StrictAncestor.edge (isChild_edge w root child hch0))
          · exact Or.inr (StrictAncestor.trans
              (StrictAncestor.parents (fun i => (hp i).symm) hanc)
              (StrictAncestor.edge (isChild_edge w root child hch0)))
        exact ih _ hp1 hc1 hl1
      · have hf : isChild w0 root child = false := by
          cases hb : isChild w0 root child with
          | false => rfl
          | true => exact absurd hb hch
        simp only [hf, ite_false]
        exact ih w0 hp hc hl
  exact hfold w.roster w (fun _ => rfl) rfl (fun _ => Or.inl rfl)

/-- Sealing descendants does not change the root's life. The only other
disjunct of `dropDescendants_stable` is that the root is its own strict
ancestor, which a forest forbids. -/
theorem drop_root_life (D : Description) (w : World) (root : InstId) (hacy : ParentAcyclic w) :
    ((dropDescendants D w root).st root).life = (w.st root).life := by
  rcases (dropDescendants_stable D w root).2.2 root with heq | hanc
  · exact heq
  · exact absurd hanc (ParentAcyclic.no_self hacy root)

/-- A live stage that terminates is dead and idle afterwards. Descendants are
sealed first and cannot kill the stage, because a stage is not its own
ancestor. The stage's own tombstone may still crash the roster; that crash
does not rewrite the stage, which `releaseWorld` has already installed dead. -/
theorem terminate_alive_idle (D : Description) (w : World) (id : InstId)
    (hacy : ParentAcyclic w) (hl : (w.st id).life = .alive) :
    ((terminateStage D w id (w.st id)).st id).life = .dead ∧
      ((terminateStage D w id (w.st id)).st id).phase = .idle := by
  simp only [terminateStage]
  have hstay : ((dropDescendants D w id).st id).life = .alive := by
    rw [drop_root_life D w id hacy, hl]
  exact shutdownActor_alive_idle D (dropDescendants D w id) id hstay

theorem abortChildren_parent (D : Description) (w : World) (parent i : InstId) :
    ((abortChildren D w parent).st i).parent = (w.st i).parent := by
  unfold abortChildren
  have hfold : ∀ (ids : List InstId) (w0 : World),
      (∀ j, (w0.st j).parent = (w.st j).parent) →
      ∀ j, ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w0).st j).parent = (w.st j).parent := by
    intro ids
    induction ids with
    | nil => intro w0 hp j; exact hp j
    | cons child ids ih =>
      intro w0 hp j
      simp only [List.foldl_cons]
      by_cases hc : (isChild w0 parent child && (w0.st child).life == .alive) = true
      · simp only [hc, ite_true]
        have hdrop := dropDescendants_stable D w0 child
        exact ih _ (fun k => (shutdownActor_parent D _ child k).trans ((hdrop.1 k).trans (hp k))) j
      · have hf : (isChild w0 parent child && (w0.st child).life == .alive) = false := by
          cases hb : isChild w0 parent child && (w0.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf, ite_false]
        exact ih w0 hp j
  exact hfold w.roster w (fun _ => rfl) i

/-- Aborting under a forest leaves the parent alive unless the enqueue crashes
the roster. A child cannot seal the parent: that would make the parent its own
ancestor. -/
theorem abort_parent_alive (D : Description) (w : World) (parent : InstId)
    (hacy : ParentAcyclic w) (hlive : (w.st parent).life = .alive)
    (hcr : (abortChildren D w parent).crashed = false) :
    ((abortChildren D w parent).st parent).life = .alive := by
  unfold abortChildren at hcr ⊢
  have hfold : ∀ (ids : List InstId) (w0 : World),
      ParentAcyclic w0 → (w0.st parent).life = .alive →
      ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w0).crashed = false) →
      ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w0).st parent).life = .alive := by
    intro ids
    induction ids with
    | nil =>
      intro w0 _ hlive0 _
      exact hlive0
    | cons child ids ih =>
      intro w0 hacy0 hlive0 hcr0
      simp only [List.foldl_cons] at hcr0 ⊢
      by_cases hc : (isChild w0 parent child && (w0.st child).life == .alive) = true
      · simp only [hc, ite_true] at hcr0 ⊢
        have hparts := (Bool.and_eq_true _ _).mp hc
        have hchild : isChild w0 parent child = true := hparts.1
        have hne : child ≠ parent := (isChild_edge w0 parent child hchild).2
        have hdrop := dropDescendants_stable D w0 child
        let w1 := dropDescendants D w0 child
        have hsh : (shutdownActor D w1 child).crashed = false := by
          -- The tail fold does not clear a crash, so a clear result started clear.
          revert hcr0
          generalize hW : shutdownActor D w1 child = wS
          intro hcr0
          have hback : ∀ (ids : List InstId) (acc : World),
              ((ids.foldl (fun w c =>
                if isChild w parent c && (w.st c).life == .alive then
                  shutdownActor D (dropDescendants D w c) c else w) acc).crashed = false) →
              acc.crashed = false := by
            intro ids
            induction ids with
            | nil => intro acc h; exact h
            | cons c cs ihc =>
              intro acc h
              simp only [List.foldl_cons] at h
              by_cases hcc : (isChild acc parent c && (acc.st c).life == .alive) = true
              · simp only [hcc, ite_true] at h
                have hshut : (shutdownActor D (dropDescendants D acc c) c).crashed = false := ihc _ h
                have hd := dropDescendants_stable D acc c
                have hdropCr := shutdownActor_crashed_back D (dropDescendants D acc c) c hshut
                rw [hd.2.1] at hdropCr
                exact hdropCr
              · have hf : (isChild acc parent c && (acc.st c).life == .alive) = false := by
                  cases hb : isChild acc parent c && (acc.st c).life == .alive with
                  | false => rfl
                  | true => exact absurd hb hcc
                simp only [hf, ite_false] at h
                exact ihc acc h
          exact hback ids wS (by simpa [hW] using hcr0)
        have hlife1 : (w1.st parent).life = .alive := by
          rcases hdrop.2.2 parent with heq | hanc
          · rw [heq]; exact hlive0
          · exact absurd (StrictAncestor.trans hanc (StrictAncestor.edge (isChild_edge w0 parent child hchild)))
              (ParentAcyclic.no_self hacy0 parent)
        have hlife2 : ((shutdownActor D w1 child).st parent).life = .alive := by
          rw [shutdownActor_other_life D w1 child parent (Ne.symm hne) hsh]
          exact hlife1
        have hacy2 : ParentAcyclic (shutdownActor D w1 child) := by
          apply parentAcyclic_parents (w' := shutdownActor D w1 child) _ hacy0
          intro j
          rw [shutdownActor_parent, hdrop.1 j]
        exact ih _ hacy2 hlife2 hcr0
      · have hf : (isChild w0 parent child && (w0.st child).life == .alive) = false := by
          cases hb : isChild w0 parent child && (w0.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf, ite_false] at hcr0 ⊢
        exact ih w0 hacy0 hlive0 hcr0
  exact hfold w.roster w hacy hlive hcr

theorem spawnChild_core_life (I : Impl) (w w' : World) (parent : InstId) (child name : String)
    (h : spawnChild I w parent child = some w') :
    (w'.st (InstId.core name)).life = (w.st (InstId.core name)).life := by
  unfold spawnChild at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · next _ k _ =>
        split at h
        · cases h
          rfl
        · cases h
          have hpeer : InstId.core name ≠ InstId.peer child k (maxGen w child k) := by
            intro h; cases h
          simp [admitBorn, setActor, cellsSt, hpeer]
    · split at h
      · cases h
        rfl
      · simp at h

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
        let goneK := { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone }
        have hset := set_core_life w id (proceed a goneK) name (by simp [proceed_keeps_life, ha])
        exact hset.symm.trans hl
      | some dstId =>
        simp [hr] at hl
        split at hl
        · exact (enqueue_core_life w I.desc id dstId _ false (afterHead k) name).symm.trans hl
        · split at hl
          · let fullK := { afterHead k with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull }
            have hset := set_core_life w id (proceed a fullK) name (by simp [proceed_keeps_life, ha])
            exact hset.symm.trans hl
          · let goneK := { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone }
            have hset := set_core_life w id (proceed a goneK) name (by simp [proceed_keeps_life, ha])
            exact hset.symm.trans hl
    | call dst label hint onNotAdmitted onTimedOut =>
      simp [execRun, hliveB, hk] at hl
      cases hr : resolveId I.desc w id dst with
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
      simp only [execRun, hliveB, hk, ite_true, commitCont] at hl
      by_cases hcr : (abortChildren I.desc w id).crashed = true
      · rw [ite_eq_left hcr] at hl
        exact abortChildren_prev I.desc w id (InstId.core name) hl
      · rw [ite_eq_right hcr] at hl
        have hset := set_core_life (abortChildren I.desc w id) id
          (proceed ((abortChildren I.desc w id).st id) (afterHead k)) name
          (by simp [proceed_keeps_life])
        exact abortChildren_prev I.desc w id (InstId.core name) (hset.symm.trans hl)
    | spawn child =>
      simp only [execRun, hliveB, hk, ite_true, commitCont] at hl
      cases hs : spawnChild I w id child with
      | none =>
        simp [hs] at hl
        exact crashWorld_prev w (InstId.core name) hl
      | some w' =>
        simp only [hs] at hl
        by_cases hcr : w'.crashed = true
        · rw [ite_eq_left hcr] at hl
          exact (spawnChild_core_life I w w' id child name hs).symm.trans hl
        · rw [ite_eq_right hcr] at hl
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
        | crash _ _ _ =>
          intro h
          exact crashWorld_prev w (InstId.core name) h
        | lone _ _ _ _ _ _ _ =>
          intro h
          exact shutdownActor_prev I.desc w id (InstId.core name) h
        | tree _ _ _ _ =>
          intro h
          exact terminateStage_core_prev I.desc w id a name h
        | cascade _ _ _ _ _ _ _ =>
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
        (proceed_keeps_life (w.st id)
          { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout })
    | crashed => simp [hph] at h

/-- A core that is alive after a step was alive before it. No step creates a core. -/
theorem apply_core_prev (I : Impl) (w w' : World) (a : Action) (name : String)
    (h : apply I a w = some w') (hl : (w'.st (InstId.core name)).life = .alive) :
    (w.st (InstId.core name)).life = .alive := by
  cases a with
  | callTimeout id =>
    exact (callTimeout_life w w' id (InstId.core name)
      (by simpa [stepWorld] using (apply_step I (.callTimeout id) w w' h).2)).symm.trans hl
  | stutter =>
    have hstep := (apply_step I .stutter w w' h).2
    simp [stepWorld] at hstep
    cases hstep.2
    exact hl
  | ingress dst label =>
    have hlife := (ingress_phase I w w' dst label (InstId.core name)
      (by simpa [stepWorld] using (apply_step I (.ingress dst label) w w' h).2)).2.1
    exact hlife.symm.trans hl
  | finish id =>
    obtain ⟨k, _, hw⟩ := finish_proceed I w w' id
      (by simpa [stepWorld] using (apply_step I (.finish id) w w' h).2)
    rw [hw] at hl
    exact (set_core_life w id (proceed (w.st id) k) name (proceed_keeps_life _ _)).symm.trans hl
  | spawn template =>
    exact (spawn_core_life I w template w' name
      (by simpa [stepWorld] using (apply_step I (.spawn template) w w' h).2)).symm.trans hl
  | recvBulk id =>
    exact (receiveBulk_keeps_life I w w' id (InstId.core name)
      (by simpa [stepWorld] using (apply_step I (.recvBulk id) w w' h).2)).symm.trans hl
  | recvPrio id =>
    exact (receivePrio_keeps_life I w w' id (InstId.core name)
      (by simpa [stepWorld] using (apply_step I (.recvPrio id) w w' h).2)).symm.trans hl
  | exec id =>
    have hhead : execHead I w id = some w' := by
      simpa [stepWorld] using (apply_step I (.exec id) w w' h).2
    unfold execHead at hhead
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
  supervisor := if sup == "" then none else some sup
  tombstone := tomb

def laneOverflowDesc : Description where
  name := "overflow"
  freshNames := true
  templates := overflowTpl "parent" .one "" "" ::
    (List.range 5).map fun n => overflowTpl s!"c{n}" .perPeer "parent" s!"t{n}"
  edges := []
  compatibility := .all
  steps := []

def overflowIds : List InstId :=
  .core "parent" :: (List.range 5).map fun n => .peer s!"c{n}" 0 0

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
  st := fun i =>
    if decide (i ∈ overflowIds) then
      match i with
      | .peer _ _ _ => { overflowActor with parent := some (.core "parent") }
      | .core _ => overflowActor
    else absentActor
  cell := fun _ _ => cleanCell
  observed := fun _ _ => 0

/-- Enqueue one tombstone from each of the five children. The fifth finds a
lane of capacity 4 already full. -/
def overflowRun : World :=
  (List.range 5).foldl (fun w n => enqueueTombstone laneOverflowDesc w (.peer s!"c{n}" 0 0)) overflowWorld

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
    (hl : (w.st c).life = .alive) (hph : (w.st c).phase = .awaitReply d k)
    (hc : w.crashed = false) :
    Enabled I w (.callTimeout c) := by
  unfold Enabled apply stepWorld callTimeout
  have hlive : ((w.st c).life != .alive) = false := by simp [hl, bne]
  simp [hc, hlive, hph]

/-- An `awaitReply` does not last for the rest of a fair run while the caller
stays alive. The deadline stays enabled, and fairness takes it. -/
theorem await_not_forever (I : Impl) {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (c d : InstId) (i : Nat)
    (hph : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st c).phase = .awaitReply d k)
    (hlive : ∀ t, i ≤ t → ((ρ.cfg t).st c).life = .alive) : False := by
  have hen : ∀ t, i ≤ t → Enabled I (ρ.cfg t) (.callTimeout c) := by
    intro t ht
    obtain ⟨k, hk⟩ := hph t ht
    exact await_still_enabled I (ρ.cfg t) c d k (hlive t ht) hk (apply_step _ _ _ _ (ρ.valid t)).1
  obtain ⟨j, hj, hact⟩ := hF.weak (.callTimeout c) i rfl hen
  have happ := (apply_step _ _ _ _ (ρ.valid j)).2
  rw [hact] at happ
  simp only [stepWorld] at happ
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
  have happ := (apply_step _ _ _ _ (ρ.valid j)).2
  rw [hact] at happ
  simp only [stepWorld] at happ
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
  have hc : replyFalseWorld.crashed = false := rfl
  have hen := await_still_enabled raceImpl replyFalseWorld c d replyFalseK hl hph hc
  cases hopt : callTimeout replyFalseWorld c with
  | none => simp [Enabled, apply, stepWorld, hc, hopt] at hen
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
