# Semantics

What `Deadlock/Semantics.lean` does now. Names below are the definitions.
There is no shutting-down phase: `Life` is `absent`, `alive`, or `dead`, and
a kill removes its members in the same step. Update this page in the same
commit as any change to that step relation.

## World

`World` holds `N`, `roster`, `nextIx`, `st`, `cell`, `observed`, `failures`,
and `tombstone`.

`InstId` is `core name` or `peer name index`. `nextIx` only grows. `spawn`
allocates `InstId.peer template (nextIx template)` and a dead index is never
reused. `memberKey` is that index; a core has none. `isMember` is a peer
whose index is the key and whose template's subtree is `sub`.

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

`tokens dst` is the remaining send credit toward template `dst`.
`enqueueOrPark` spends one with `chargeSender`. A receive gives it back
with `creditSender`. `capBulk` and `capPrio` bound the queues. A priority
wake is not charged.

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
| `recvPrio id` | alive, `idle`, `prio` nonempty, `deliver` accepts | Consume the `prio` head. No credit. |
| `exec id` | alive and `run` | `execRun` performs the head `Eff` and leaves `afterHead`. An empty continuation becomes `idle`. |
| `finish id` | `awaitEffect`, or `awaitPeer` with `peerFinishable` | `finishWait` runs `proceed`. |
| `spawn template` | per-peer template and `aliveCount < N` | Fresh peer, idle, on the roster. |
| `ingress dst label` | alive, `ingressOpen`, a declared ingress edge, room in `box`, not `terminableB`, and enough `tokens` | Append one reliable self-message and charge. |
| `kill sub key` | `killWait`: a live `timeoutKills` member of that key is in `awaitPeer` | `killSubtree`. |
| `stutter` | not `runtimeBusy` | Same world. |

`runtimeBusy` is a roster actor who can `recvBulk`, `recvPrio`, `exec`, or
`finish`, or `killBusy`.

One `exec` step, by the head effect:

- `send` and `call` use `route`. A miss is `noteStale` and the sender
  proceeds. A hit is `enqueueOrPark`: into `box` when the target is alive,
  its `parked` list is empty, and `box` has room; otherwise onto `parked`.
  A dead or absent target stores nothing. A call then waits in `awaitReply`
  or `parked` with `isCall`.
- `trySend` stores only when the target is alive, unparked, and not full.
  The copy is `reliable = false`. Otherwise it is discarded and the sender
  proceeds.
- `reply` is `performReply`: the caller runs only when it is in
  `awaitReply` of this sender.
- `selfSchedule` enqueues its label on `prio`, or crashes when the lane is
  full and the label is new.
- `cell` writes `max` of the old value and sets `dirty`. The first write
  wakes readers with `wakeReaders` (`tryWake`, one unreliable `prio` message
  per label).
- `internal` becomes `awaitEffect`. `peer` becomes `awaitPeer`.
- `terminate` runs only when the template is `terminable` and `parked` holds
  no call. It `readCells`, `refundMsgs`, `refundParked`, installs `dead` with
  an empty mailbox, and `releaseParked` (a non-call parked sender resumes; a
  call is left). Otherwise the world is unchanged.

`route` resolves a multiplicity-one name to its live core, and a per-peer
name to `InstId.peer dst (memberKey sender)` when that peer is alive. A core
cannot address a per-peer role. The `hint` is not the address.

`deliver` refuses a dead actor, a call with no transition, and a call whose
transition does not `acceptsCall`. The receive is then not enabled. A
non-call with no transition is accepted and leaves the receiver `idle`. A
program becomes `run`, or `idle` when the program is empty. `replyTo` is
`callFrom`.

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

An untimed peer (`peerUntimed`) is not a `Deadlock`. `finish` is enabled on
it only when `peerFinishable` (`timedCohortEnds`: a timed peer in the subtree
can kill it). `PurePeerEnd` is the wait where `peerFinishable` is false. That
wait is the external peer. Nothing in the model ends it.

## Kill and drop

`killSubtree` is `killMembers` then `plantTombstone`. Each live member is
`killOne`: refund what its `box` and `parked` held, `failWaiters` (a sender
parked on the member proceeds; a caller in `awaitReply` becomes `idle`),
`forgetSender` (delete that member's entries from other actors' `parked`
lists), then `dead`, `idle`, and an empty mailbox. `plantTombstone` stores
the key. Peer selection belongs to the application typegraph.
The parent's reaction is not a step of `kill`.

A drop that is not a kill: `trySend` discards when the target is missing or
the box is not free; `noteStale` records a route miss and stores nothing;
`enqueueOrPark` toward a target that is not alive stores nothing and does
not charge. A stored reliable message is not dropped by a later send. Mail
inside a member is refunded or deleted by `killOne`, not left for a later
receive.

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
because death is permanent, shutting-down is monotone, and an id is not
reused. On that step relation, `route` reads life and shutting-down.

Mailbox sizing is a separate decision, not a change to this step relation.
Slots are sized for a duplex connection, and the model may include every
peer direction. Occupancy for nested supervision is a product along the
supervision tree. The record is `DECISIONS.md` (2026-11-19).
