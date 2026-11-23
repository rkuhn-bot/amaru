# Semantics

What `Deadlock/Semantics.lean` does now. Names below are the definitions.
There is no shutting-down phase: `Life` is `absent`, `alive`, or `dead`, and
a kill removes its members in the same step. Update this page in the same
commit as any change to that step relation.

## World

`World` holds `N`, `roster`, `nextIx`, `st`, `cell`, `observed`, `failures`,
and `tombstone`.

`InstId` is `core name` or `peer name key generation`. A per-peer child
uses its parent's key and a generation. A dead id is not reused.
`memberKey` is the key; a core has none.
`isMember` is a peer whose key is the subtree key and whose template's
subtree is `sub`.

An `Actor` has `life`, `typestate`, `phase`, `box`, `prio`, `parked`,
`tokens`, and `nextMid`.

`Phase` is `idle`, `run`, `parked dst isCall`, `awaitReply dst`,
`awaitEffect`, `awaitPeer`, or `crashed`. `proceed` goes to `idle` when the
continuation is empty, otherwise back to `run`.

`box` is the bulk mailbox, `prio` the priority lane, `parked` the messages
that did not fit. Each `Msg` carries `label`, `sender`, `callFrom`, `mid`,
and `reliable`. `mid` is the id the accepting actor stamps from its
`nextMid`. `callFrom` is the caller, or `none`. A try-drop send and a cell
wake are `reliable = false`.

`tokens dst` is the remaining send credit toward template `dst`, an exact
integer. For the live generation of a key, `tokens dst + msgsTo dst = budget`.
`enqueueOrPark` spends one with `chargeSender`. A receive and a shutdown
refund give it back with `creditLive`, to the live generation of the
sender's key when one exists, and otherwise to the id that was charged.
While idle, the ingress gate reserves the current typestate's floor. While
a continuation is open, it reserves the maximum of `sends + floor(landing)`
over the paths still open. A parked call's own message is already charged,
so the reserve does not count it again. A new generation's tokens are that
budget minus mail still queued from any generation of the same key, and the
subtraction does not truncate. `capBulk` and `capPrio` bound the queues. A
priority wake is not charged.

`cell dst label` is a monotonic dirty bit. `observed id label` is the value
a reader has recorded. `readCells` clears the bits it copies.

`failures` records a `route` that did not resolve (`noteStale`). That is a
miss, not a stored message. `tombstone : Option Nat` is the key of the last
`plantTombstone`. Nothing reads it, including `route`. A later kill
overwrites it. It is not a supervision message. That message is under Later.

`initWorld` puts every multiplicity-one template on `coreRoster`, alive and
idle. Everyone else is `absentActor`.

## Actions

`Enabled` means `apply` returns `some`. `forced` is false for `spawn`,
`ingress`, and `stutter`.

| Action | Enabled when | Effect |
| --- | --- | --- |
| `recvBulk id` | alive, `idle`, and `box` or `parked` nonempty, and `deliver` accepts the head | Consume the `box` head, or the parked head if `box` is empty. If both are nonempty, also move the parked head onto `box` and `resumeSender`. Credit the consumed sender. |
| `recvPrio id` | alive, `idle`, and some `prio` message is not a waiting tombstone, and `deliver` accepts it | Consume the first such message. A waiting tombstone stays in the lane, in its place. No credit. |
| `exec id` | alive and `run` | `execRun` performs the head `Eff` and leaves `afterHead`. An empty continuation becomes `idle`. |
| `finish id` | `awaitEffect`, or `awaitPeer` with `peerFinishable` | `finishWait` runs `proceed`. |
| `spawn template` | per-peer root, a fresh key, and fewer than `N` roots occupying a population slot | Fresh generation at a fresh key, idle, on the roster. A root occupies a slot while it is alive. A core-supervised root also occupies it while its tombstone is queued, and that tombstone is not receivable while the dead stage's mail is in a live queue. An unsupervised root occupies it while a member of that subtree key still has mail on a surviving receiver. A per-peer parent births one child at its own key with `Eff.spawn`. That spawn is a no-op while the child is alive or its tombstone is still queued. The tombstone is queued in the seal and stays queued until the stage's in-flight mail has left every live queue. A core's `Eff.spawn` is not a birth. A dead id is not reused. |
| `ingress dst label` | alive, `ingressOpen`, a declared ingress edge, room in `box`, not a lone terminable, and `tokens` cover the path reserve plus one | Append one reliable self-message and charge. |
| `stutter` | not `runtimeBusy` | Same world. A crashed world does not stutter. |

`runtimeBusy` is a roster actor who can `recvBulk`, `recvPrio`, `exec`,
`finish`, or `callTimeout`.

One `exec` step, by the head effect:

- `send` and `call` use `route` (a call first uses `resolveId`). A miss is
  `noteStale` and the sender proceeds. A hit is `enqueueOrPark`: into `box`
  when the target is alive, its `parked` list is empty, and `box` has room;
  otherwise onto `parked`. A dead or absent target stores
  nothing. A send then proceeds. A call ends as `NotAdmitted` on
  `onNotAdmitted`, and does not enter `awaitReply`. An admitted call waits
  in `awaitReply` (room) or `parked` with `isCall` (no room). `Reply`,
  `NotAdmitted`, and `TimedOut` each run their own continuation into their
  own typestate.
- `trySend` stores only when the target is alive, unparked, and not full.
  The copy is `reliable = false`. `Full` runs `onFull` and `Gone` runs
  `onGone`, each into its own typestate. The admitted path keeps `toState`.
- `reply` is `performReply`: the caller runs only when it is in
  `awaitReply` of this sender.
- `selfSchedule` enqueues its label on `prio`, or crashes when the lane is
  full and the label is new.
- `cell` writes `max` of the old value and sets `dirty`. The first write
  wakes readers with `wakeReaders` (`tryWake`, one unreliable `prio` message
  per label).
- `internal` becomes `awaitEffect`. `peer` becomes `awaitPeer`. The data
  path is `finish`. The timeout is `callTimeout`, which runs `onTimeout`
  into its own typestate.
- `terminate` is the shutdown below. Every core crashes the roster.
  A per-peer stage in a supervision tree seals itself and its descendants
  in that step. A lone terminable per-peer with no child and no parked call
  seals only itself.

`route` resolves a multiplicity-one name to its live core. A per-peer
name is the live occupant of the sender's subtree key.

`deliver` refuses a dead actor, a call with no transition, and a call whose
transition does not `acceptsCall`. The receive is then not enabled. A
tombstone with no transition in the parent's current state is also refused,
so it stays queued. The queued label is the template's tombstone, `#`, and
the generation. A handler written on the base label still accepts the newest
generation. A tombstone from an older generation is consumed and leaves the
receiver idle, and does not run that handler. Another non-call with no transition is accepted and
leaves the receiver `idle`. A program becomes `run`, or `idle` when the
program is empty. `replyTo` is `callFrom`. Each outcome's typestate is
copied onto the continuation.

## Runtime rules

A stage that has come back to `idle` with mail does not choose its next
message. `recvBulk` or `recvPrio` is enabled, and `deliver` cannot refuse a
message the checker accepted. The receive consumes the head. Returning to
receiving and taking that head are two steps. `Fair.bulk` and `Fair.prio`
are what take the receive.

An `internal` effect is one step into `awaitEffect`. `finishWait` on
`awaitEffect` is `some` and does not read `Env.effectDone`. The effect
completes as `finish`. A program effect does not contain a further
computation: `apply` is one step.

`Fair.weak` takes an action that stays forced and enabled. `Fair.bulk` and
`Fair.prio` take a receive that is enabled infinitely often. Fairness does
not force `ingress`, `spawn`, or `stutter`.

An untimed peer (`peerUntimed`) is not a `Deadlock`. Its data result is
`finish` and its timeout is `callTimeout`. `peerFinishable` is true, so
`PurePeerEnd` is empty. There is no subtree kill that ends the wait.

## Shutdown and drop

`terminate` of a stage in a supervision tree is `terminateStage`:
`dropDescendants` seals every recorded descendant in this step, and those
tombstones are not delivered. The stage itself is `shutdownActor` in the
same step. `shutdownActor` calls `sealActor`. `releaseWorld` refunds the
mailbox, drops parked sends, and installs the actor `dead` and empty, and
`enqueueTombstone` queues the tombstone on the immediate supervisor's
priority lane. There is no later seal. A stage that terminates inside its
own transition is sealed before that `exec` returns.
pure-stage `terminate_stage` removes the stage and its mailbox and pushes
the tombstone in that step. The receive skips that message while program
mail from the child, or from a descendant sealed with it, sits in a live
queue. Mail at a dead receiver counts as consumed. A parked send of the
killed stage is dropped at the kill, and the seal returns those slots in
the same step, so a reachable world does not put that send back. The
supervisor may be a per-peer stage
of the same subtree. The parent answers the tombstone in its own later
step, which runs only after that mail is gone. A re-spawn of that slot is a
no-op while the slot is alive, or while its tombstone is queued. The mail
is not a second guard. A per-peer parent uses that rule. A core does
not birth a child with `Eff.spawn`.
A scheduler root under a core keeps one of the `N` population slots while
that tombstone is queued. An unsupervised root has no tombstone, and that
key keeps its population slot while the subtree's mail remains on a
surviving receiver. The seal clears the root's own mailbox in the same
step. A sibling is not a descendant, and nothing here clears a sibling's
mailbox. A lone terminable per-peer with no child and no parked call is
`shutdownActor` of itself. Every core's `terminate`, and a priority enqueue
onto a full lane, are `crashWorld`. There is no per-core shutdown.
`terminable` is rejected on a multiplicity-one template.

`commitCont` installs the continuation of an effect only when that effect
did not crash the roster. `abort` seals the children and queues their
tombstones, then continues the parent from the actor that holds those
tombstones. An empty tombstone label, or a tombstone that does not fit on
the lane, is `crashWorld` inside that enqueue. The parent stays in the
crashed phase and does not take the continuation. The same guard is the
continuation of `spawn`. A crash that is itself the effect, with no later
continuation, is unchanged.

A reachable world's parent links are a forest. No actor is its own strict
ancestor, an actor off the roster records no parent, and every recorded
parent is on the roster. The initial world has no parent links. `spawn` is
the only step that adds one, from a fresh id to a parent already on the
roster. A parent pointer cycle is not a reachable world. `abort` on a
forest does not seal the actor that is running it, unless the tombstone
enqueue crashes the roster.

`releaseWorld` is `readCells`, `refundMsgs` (`creditLive`), `refundParked`,
`releaseOutbound`, the dead empty actor, and `releaseParked` for non-call
parked senders. `markShutdown` is not a step. A crashed world has
`crashed = true`. Every action, including spawn, ingress, and stutter, is
disabled, so the run stops. The liveness claim is deadlock-free or crashed.

A drop that is not a crash: `trySend` discards when the target is missing or
the box is not free; `noteStale` records a route miss and stores nothing;
`enqueueOrPark` toward a target that is not alive stores nothing and does
not charge. A stored reliable message is not dropped by a later send. Mail
inside a member sealed in this step is refunded by `releaseWorld`, not left
for a later receive.

## Later

Not the step relation above. Cells are not a pure-stage primitive, so `cell`
and `tryWake` deviate from current pure-stage. The planned runtime encoding
is an effect whose resource holds a map keyed by reader stage name, one cell
per reader. Each cell holds a `(counter, value)` pair, ordered by the
counter, which removes the max-only limit, plus a wake-pending flag. A write
atomically stores the value and, if no wake is pending, sets the flag and
enqueues one regular wake message. The reader's handler atomically reads and
clears the flag. That atomicity is the runtime's.

The model change that goes with it: replace the uncharged `prio` wake with a
regular message that uses one reserved mailbox slot per cell label and
reader. Count that slot in the occupancy bound. The wake enqueue stays
non-blocking because the slot is reserved.

Supervision is not this step relation either. Termination there is the
pure-stage mechanisms plus one. A stage terminates on its own `terminate`.
An `awaitPeer` timeout is only a typestate choice that may do so:
`peerTimeout`'s built-in atomic `killSubtree` is removed. The tombstone is
the message the parent supplies when it creates the child. The parent
receives it on `prio` once the child has terminated, then answers in its own
typestate transition and may itself terminate. The slot is reserved per
child, so the enqueue does not block and spends no bulk credit, and it
counts in `capPrio`. When a stage terminates, its descendants terminate in
that same step, as pure-stage `terminate_stage` does
(`crates/amaru-pure-stage/src/simulation/running/mod.rs`): parked non-call
senders resume, and parked calls finish via their deadline. `crashed` stays
a fourth outcome that kills every actor at once. It is a terminal state the
theorems need not say more about, where the proofs already treat it that
way. It gets no extra proof burden. If keeping it costs significant proof
work, stop and report. The environment `.kill sub key` action goes away with `killWait`,
and so do `World.tombstone` and `plantTombstone`. Peer selection stays in
the application typegraph. A send that has been dropped stays dropped
because death is permanent and an id is not reused. On that step relation,
`route` reads life.

Mailbox sizing is a separate decision, not a change to this step relation.
Slots are sized for a duplex connection, and the model may include every
peer direction. Occupancy for nested supervision is a product along the
supervision tree. The record is `DECISIONS.md` (2026-11-19).

Every external wait carries a timeout. That is also recorded in
`DECISIONS.md` (2026-11-19), and it is not this step relation. The
implication, flagged for step D (R4-1): untimed external waits leave the
model. `untimedPeer`, `PurePeerEnd`, `timedCohortEnds`, and the untimed side
of `peerFinishable` go away. R4-1 then reduces to removing them.

A permanent pure stage, a multiplicity-one core, may also execute
`terminate`. That is recorded in `DECISIONS.md` (2026-11-19), and it is not
this step relation. A core's `terminate` will map to the existing
whole-system `crashed` outcome. That outcome is terminal and adds no proof
burden, as already ruled. If keeping that mapping free of proof burden is
not possible, report it at step C.
