# Decisions

Design decisions for the deadlock model. Each one is recorded when it is
made. Nothing here is a change to the step relation by itself.

## 2026-11-19 — Pessimistic full-duplex sizing

Mailbox sizing is pessimistic. Each slot, outbound or inbound, may end up
carrying a duplex connection, so mailboxes are sized for the worst case. The
Lean model therefore treats every peer as full duplex, which is the worst
case for wait edges. The model already allows any number of templates; what
is fixed is the instance structure. So setting up every peer direction in
the model is acceptable. That is more than runs in practice, but given the
pessimistic sizing the extra edges are not an over-approximation: they match
what production already commits to. Full-duplex support is needed anyway, so
this adds no scope. Nested depth is unbounded. Occupancy is the chain
`population` walks: a root per-peer template has population `N`, and a
per-peer child has the population of its per-peer supervisor. That is the
parameterized product along the supervision tree, not a flat `N` per template.
A child is spawned by its per-peer parent, one instance per parent, so the
child's count is the parent's count and is not capped by a second `N`.

## 2026-11-19 — Every external wait carries a timeout

Every external wait carries a timeout. "External" means anything untrusted
outside the modelled system, including what is now `awaitPeer`. A timeout is
not a failure. It is a normal result that tells the waiting actor the
external peer has not responded, or the external effect has not completed.
The actor's typestate handles that result like any other, and may choose to
terminate. This matches the earlier ruling that a timeout is the actor's own
typestate choice, not an environment kill action.

## 2026-11-19 — A permanent core may terminate the system

The `terminate` effect is currently allowed only for terminable templates. A
permanent pure stage, which is a multiplicity-one core, may also execute
`terminate`, and its effect is the same as `crashed`: the whole system
terminates. The 2026-11-21 decision replaces that split for cores.

## 2026-11-20 — A full priority lane crashes

A priority enqueue onto a full lane crashes the roster. Tombstones,
self-schedules, and cell wakes all count toward `capPrio`. A label that is
already pending is not a new enqueue: cell wakes and self-schedules keep that
dedup, and a wake that does enqueue counts like any other entry. The lane
never grows past its capacity, never blocks, and never drops the message.

`crashed` is a terminal state. It has no proof burden. It is reachable: five
tombstones on a lane of capacity 4 end there.

A lane does not overflow when `prioSized` holds. That asks `capPrio` to be at
least the children that can tombstone at once plus the other priority senders.
Under full-duplex sizing the child count is `population`, the product along
the supervision tree. `prioSizeFails` is that check. It is not wired into
`LocalOk` yet; the checker will report it later.

## 2026-11-20 — call_answered does not promise Reply

`call_answered` is the callee's handling guarantee. An admitted call is a
request queued at the callee under `mid`. If the callee stays alive, it
handles that request by `recvBulk` of `mid`. The caller's outcome is not
part of that claim.

The caller's totality is one continuation per outcome (`finishCall_cont`).
An `awaitReply` ends as `Reply` (`await_reply_end`) or `TimedOut`
(`await_total`). `NotAdmitted` (`parked_not_admitted`) is the outcome when
the request never enters the mailbox. A live `awaitReply` does not last for
the rest of a fair run (`await_not_forever`).

The old `Reply` conjunct is false. The deadline can fire while the callee is
still alive (`call_answered_reply_false`). There will never be a `Reply`
guarantee: Amaru is not a real-time system. The callee-side handling
guarantee plus the caller-side outcome totality is the final form of
`call_answered`.

## 2026-11-20 — Deadlock-free or crashed

`deadlock_freedom` is deadlock-free or crashed. A fair run of a `GraphOk`
and `LocalOk` implementation is not stuck on a parked send, or a step has
crashed the roster. `crashWorld` sets `World.crashed`. Spawn, ingress,
stutter, and every runtime action are then disabled, so the run stops.
Crash is a reachable outcome: a core's `terminate`, and a priority enqueue
onto a full lane. It is not a silent escape from a stuck parked send. Every
core may terminate; see 2026-11-21.

A parent restarts a dead child at a fresh generation of the same key. The
dead id is not reused. A supervisor that is not alive admits no new child.
The shutting-down half of the earlier wording is superseded by the
2026-11-21 20:20 fusion. A core births a pool of `slots` children, indexed by slot and
generation, and that `slots` multiplies the population and the tombstone
count. The restart bound is the later decision on this page.

## 2026-11-20 — What deadlock freedom is about

`deadlock_freedom` is about parked sends. A run is deadlocked when a send sits
parked and nothing that actor can do makes the send progress. `Fair` on its
own already excludes being stuck on an effect wait, a peer wait, or a call
wait: each of those has a step the runtime is obliged to take, and fairness
says that step is eventually taken. The theorem's content, past fairness, is
the parked send.

## 2026-11-19 — Priority versus bulk

Priority versus bulk: keep the model as it is. The hypothesis is `Fair`:
weak fairness for forced actions, plus strong fairness per actor and per
lane for both `recvBulk` and `recvPrio`. The proofs hold for every
interleaving, including a strictly prio-first runtime. Proving the larger
model is stronger than narrowing it with a runtime assumption. So do not
add a prio-first runtime assumption to `SEMANTICS.md`, and do not change
`Fair`. The known gap is accepted for now: a prio-first runtime satisfies
`Fair.bulk` only if the priority lane eventually drains, and nothing in the
model guarantees that.

## 2026-11-20 — A slot has one outstanding tombstone

Tombstones count toward `capPrio`. An enqueue that does not fit is
`crashWorld`. A parent, core pool or per-peer, may spawn slot `s` when that
slot has never been born, or when its tombstone has already been consumed, or
in the transition that consumes that tombstone. Until then the spawn is not
enabled: `Eff.spawn` is a no-op, the same as a full pool, and a root spawn by
a core into that slot returns no world. A slot is occupied while it is
alive, or while its tombstone is queued. The 2026-11-21 20:20 fusion
supersedes the shutting-down occupation: the seal queues the tombstone in
that same step.

The tombstone is queued when the child seals, after it is dead. Pure-stage's
`terminate_stage` finishes the child before the parent is notified, and the
model follows that. A consumed tombstone therefore means the predecessor has
sealed. Refunds still go to the live generation of the sender's key.
`GraphOk` rejects a supervised template whose tombstone is empty. A reachable
world records a parent only when the child's template names that supervisor,
so the seal's label is nonempty. An empty label is not in the affine count
because that template does not pass the checker.

`LocalOk` rejects a program that spawns the child from a state which can run
while the tombstone is still queued, so a checked design cannot rely on the
no-op. Each slot then has at most one tombstone outstanding. Per parent,
`prioSized` says `capPrio` covers the sum over child templates of that
parent's slots — one per pool slot, one per key of a root the core spawns,
one for a per-peer parent's child — plus that parent's self-schedule and
cell-wake senders. A path contributes the sends on one outcome; the two
branches are not added. The lane also keeps a label from a later transition,
and it keeps each label once, so the sender term is the larger of the
single-path count and the number of distinct labels. `prioSizeFails` is part
of `LocalOk`. That bound is the lane's static account.
`no_tombstone_overflow` is that account for a reachable seal: under
`GraphOk` and `LocalOk`, sealing a child does not fill a
live parent's lane. `LocalOk` supplies `prioSized`. A reachable self-schedule
or cell wake fits the same lane, so it does not crash there. An undeclared
label is outside that claim. pure-stage still panics when a lane has no room.

Pure-stage will be changed to match this bound. Its tombstone queue is an
unbounded `VecDeque` (`supervisor.tombstones.push_back` in
`crates/amaru-pure-stage/src/simulation/running/mod.rs:1323` at `34a45300`).
That is an implementation change to make, not a defect in the model.

## 2026-11-20 — A reused key was a fidelity bug

The overflow in `Deadlock/Counterexample.lean` reused a subtree key and
delivered the second child's tombstone to the older generation. pure-stage
at `34a45300` does not do that. `stage_name` gives every birth a fresh name,
and `supervised_by` is that exact parent. `terminate_stage` discards a
child's tombstone when the parent is removed.

The semantics follow that rule. A scheduler root takes a fresh subtree key.
A per-peer child is born at its parent's key, and a restart under that same
live parent is a new generation. The child records the parent incarnation.
The seal delivers the tombstone to that incarnation, and drops it when the
incarnation is dead. An empty tombstone on a live parent is
not a reachable seal under `GraphOk`. A root under no supervisor is bounded by how many are
alive. A root under a core is bounded by how many are alive or still have a
tombstone queued. The 2026-11-21 20:20 fusion supersedes the shutting-down
disjunct. `supervisor` is an `Option`: `none` does
not match a template, including one whose name is empty.

`no_tombstone_overflow` is that seal for a reachable world. `hold_reach` is
`Hold` at every world a run reaches under `GraphOk`. `Side` carries the key
counters, a duplicate-free roster, and the empty off-roster lane from the
initial world through every enabled step. `tmb_seal_room` is the numeric
fact those worlds instantiate. Refunds still go to the live generation, and
the tombstone is still queued at the seal.

## 2026-11-21 — A core terminate crashes the node

Roland, 2026-11-21: "all cores may terminate and any such termination crashes
the node i.e. ends the run. Such a crash is operationally undesirable but in
this work we should count it as acceptable behaviour."

This resolves N39. It replaces the split in the 2026-11-19 note, where only a
non-terminable core crashed and a terminable core shut itself down.

Every multiplicity-one template is a core. Its `terminate` is `crashWorld`,
the same end pure-stage takes when a top-level stage terminates
(`Effect::Terminate` with supervisor `BLACKHOLE` stops the simulation). There
is no per-core shutdown. `terminable` is not a property of a core:
`coreFlagFails` rejects a multiplicity-one template that sets it. The flag
stays meaningful for a per-peer template. A lone terminable per-peer still
shuts only itself down, and a per-peer stage in a subtree still seals its
descendants and arms one tombstone.

`LocalOk` allows `terminate` on a core. A per-peer program may `terminate`
only when the template is terminable. That is the old gate, kept for peers.
A core program is not muted by the flag. The mute rule is what keeps a lone
terminable per-peer from leaving reliable mail in a run that continues.

`permanentTarget` accepts any multiplicity-one target, the same subtree, or a
pool child of the calling core. The old `terminable = false` conjunct excluded
a core that could shut down and leave the sender running. A core no longer
does that. Dropping the conjunct does not admit a new `GraphOk` target,
because a core that sets the flag is already rejected. A reliable send or
call to a terminable per-peer outside its subtree is still rejected.
`callTermFails` uses the same cut. `pureTermFails` still requires a pure
untimed per-peer to be terminable. A core is not that peer: a pure core is
rejected by `subtreeEntry` (`pureKillMsg`), and demanding `terminable` there
would contradict the flag check.

The slot-mail note below is the decision on N32. Helen's E4
(`Outlive.lean`) is mail from a non-terminable per-peer child left in two
cores after the per-peer root terminates. That root is per-peer, so its
`terminate` is still the subtree seal, not a core crash. The cores in that
run do not terminate. This decision does not move that mail.

`FairRun.lossTpl` is a terminable core. Its `terminate` used to clear a
mailbox (`loss_not_delivered`). That step is now `crashWorld`. `FairRun` does
not build, and this change does not repair it. `TermStep.crash` no longer
carries `terminable = false`, and `lone` and `cascade` require
`multiplicity = .perPeer`. Modules that still split the old constructors are
left as they are.

## 2026-11-21 — A slot respawns after its core mail is consumed

Roland, from the 2026-11-21 08:04 CET call: mail in a tokio channel cannot
be removed or diverted, so processing-before-respawn must be a precondition
of spawn, not an operational hope. A per-peer slot may be respawned only
once every message that any previous occupant of that slot sent to a core
has been consumed by that core.

The slot is `(template, key)`. A pool slot is that key in `0 ..< slots`
under its core. A per-peer parent's one child uses the parent's key, and
the next generation is the next occupant. A scheduler root takes a fresh
key from `freshKey` — a new slot, with no previous occupant.
`slotCoreMail` is a bulk message, a priority message, or a parked send still
sitting on a core, whose sender is any generation of that slot.
`slotRespawnBlocked` was that mail, or the slot still alive or shutting
down, or its tombstone still queued. The 11:46 entry drops the mail term
for a supervised slot, and the 2026-11-21 20:20 fusion drops the
shutting-down term. `spawnChild` is then a no-op, the
same as a full pool. `freeSlot` skips such a pool index. `spawn` of a root
is unchanged: the key is fresh.

The tombstone rule and this rule are separate — the tombstone is one
priority message on the supervisor. Core mail is what occupants already
placed on cores. Neither implies the other. A per-peer supervisor's
tombstone is not on a core, so the parent can consume it while a core still
holds the slot's bulk mail, and a core can consume that mail while the
tombstone is still queued. A core supervisor's tombstone is itself core
mail from the slot, so consuming it clears that one priority message and
the queued-tombstone bit together. Other messages on that core, and mail
on any other core, stay until those cores consume them. A respawn needs
both guards clear. They can be discharged in either order.

A respawn can stay disabled for the rest of the run. Liveness of respawn
is not claimed. The slot stays blocked while any of that mail remains.
The shutdown mark drops the dying sender's parked entries on other hosts
without delivering them (`releaseOutbound`), so those particular parked
sends do not outlive the occupant. Mail already admitted to a core's box
or priority lane does, and it is not drained. If the core never receives
it, the next incarnation is not born.

`GraphOk` is unchanged: it does not read mailboxes. `LocalOk`'s restart
check is unchanged. It refuses a spawn that can run while the tombstone
may still be queued, which is a fact about typestate. Core mail is not.
The step no-op is the guard.

pure-stage and Amaru have to enforce the same precondition before a
restart. This model does not change the Rust node. A restart that births
the next incarnation while a core still holds the slot's earlier mail
would not be this semantics.

Helen's E4 is not this same-key guard. Each birth of `R` and `X` is
generation 0 of a fresh subtree key. The 08:44 entry is the decision on
that case.

The 09:30 entry generalises the receiver. The 11:46 entry changes the
interaction. A supervised tombstone is not delivered while that stage's
in-flight mail remains, and the spawn is not given a second mail guard.

## 2026-11-21 — Implementation work not covered by the Lean model

Roland, from the 2026-11-21 08:06 CET call, revised 2026-11-21 11:46 CET.
pure-stage cannot yet delay a tombstone the way this model does.

pure-stage delays delivery of a terminated stage's tombstone until that
stage's in-flight mail has been consumed. Each message is tagged with the
sender's slot and generation. A live receiver reports consumption of those
tagged messages. The tombstone is delivered when every such message from
the terminated stage, and from the descendants sealed with it, has been
consumed or dropped. Mail at a dead receiver counts as consumed: the seal
cleared that mailbox in the same step, and there is no shutting-down
receiver. A parked send of a stage that is killed is dropped at the kill
and is not in the set. The supervisor does not wait. The tombstone is
already on its priority lane, and a receive skips it until the set is
empty. The signal is not a mailbox becoming empty. Unrelated mail may keep
arriving. Mail on a host sealed together with the sender is not in the set:
that host drops its mailbox in the same seal. This is net-new functionality
in pure-stage.

An unsupervised root has no tombstone, so there is nothing to delay. The
scheduler holds that population slot until every surviving receiver has
consumed the subtree's mail. That is the set `loneOutstanding` counts. A
core-supervised root is held by the queued tombstone, and the tombstone is
what pure-stage withholds until the same consumption reports arrive.

The Lean model checks the finite set directly. `mailInFlight` is program
mail from the dead stage or a recorded descendant, sitting in a live
receiver's bulk or priority queue. It does not ask whether a mailbox is
empty. The drained signal itself is not a state of this model.

Three pure-stage changes sit under that gap (N55).

A receive skips a waiting tombstone in place and goes on to the next
priority message, then the bulk mailbox. The simulation pops the tombstone
queue first (`crates/amaru-pure-stage/src/simulation/running/resume.rs:65`)
and the tokio runtime takes a tombstone before a due timeout, a priority
message, or bulk (`crates/amaru-pure-stage/src/tokio.rs:452-454`). Neither
leaves a waiting tombstone queued while it delivers a later message.

The in-flight count is not one mailbox. It is that dead stage's program
mail in every live mailbox, every live priority queue, and every tokio
channel that still holds it. A dead receiver is not in the count. The
20:20 entry is that seal: the receiver is dead in the step that terminates
it, and its mailbox is already empty.

The tombstone queue has to fall through to the priority lane and then to
bulk, instead of stalling the receive on a tombstone that is not yet ready.

## 2026-11-21 — A dead root keeps its population slot

Roland, 2026-11-21 08:44 CET, his own answer: a dead root occupies its
population slot until its core mail is consumed.

The counting unit is the slot. A same-key respawn was already refused while
that key's mail sat on a core. E4 never reuses a key. Each scheduler birth
takes a fresh key, and five dead subtrees' mail filled both cores. The root
population is the account that stops that. `N` is how many roots may occupy
a slot at once. A root keeps the slot while any member of its subtree at
that key, any generation, still has mail on a core — bulk box, priority
lane, or a parked send. That is the same holding as a queued tombstone.
`rootOutstanding` is the core-supervised count, and it includes a root that
is alive or waiting on its tombstone. `loneOutstanding` is the unsupervised
count: alive, or still holding subtree mail. An unsupervised root has no
tombstone. The seal clears that root's own mailbox in the same step, so a
dead root holds the slot only through mail a surviving receiver still has.
The 2026-11-21 20:20 fusion supersedes the shutting-down clauses of this
entry. Fresh keys are unchanged.

A core-supervised pool is the same unit on a different account. Its
population is `slots`, not `N`, so it does not go through `rootOutstanding`.
`freeSlot` already skips an index while `slotRespawnBlocked` holds. The
11:46 entry takes the mail term off that supervised guard. A per-peer
parent's one child is the same guard at the parent's key.

`may_root_parts` and `may_free_parts` are the bound: a spawn is enabled only
when the count is strictly below `N`. Dead subtrees with core mail are
inside that count, so there are fewer than `N` of them whenever another root
of that template may be born. `outlive_refused` is E4 under this rule. Two
roots fill `N = 2` while their mail sits on `H` and `K`, and the third spawn
is not enabled. `outlive_stuck` is that the old five-birth run is refused.

The 09:30 entry is the same generalisation for this population slot:
the receiver is any host that is not sealed with the sender.

## 2026-11-21 — Mail on any surviving receiver holds the slot

Roland, 2026-11-21 09:30 CET, his own answer: hold the slot while its mail
sits at any live host that is not sealed together with it. The drained
signal comes from every receiver. The 11:46 entry supersedes this for a
supervised respawn and for `rootOutstanding`. `slotMailHeld` remains the
unsupervised population count.

This generalises the receiver of the 08:04 respawn rule and the 08:44
population rule. The sender set is unchanged. A nonempty subtree holds for
every member at that key, any generation. A template with no subtree holds
for its own senders. The message may be bulk, priority, or a parked send
still on the host.

A host counts while its life is alive, unless it is sealed together with the
sender. Sealed together means the host is the sender, or it sits under the
sender on the recorded parent chain. `terminateStage` seals those
descendants and the sender in the same step (`dropDescendants`,
`sealBranch`, `releaseWorld`, then `shutdownActor`). The 2026-11-21 20:20
fusion supersedes the shutting-down host and the later seal.
`releaseWorld` empties that actor's mailbox and does not clear a sibling, a
parent, or a core. Mail on a host that dies in that seal does not hold the
slot. At a later spawn check those hosts are already dead, so the life
filter excludes them as well. A sibling is not in that seal. Its copy stays
until that sibling consumes it or seals on its own.

`slotMailHeld` is that test. At 09:30, `slotRespawnBlocked`, `freeSlot`,
`rootOutstanding`, and `loneOutstanding` all used it. A same-key respawn was
a no-op while the mail remained. A fresh-key root still occupies a
population slot while it remains, and that half is what `loneOutstanding`
keeps. Mail on the root itself is sealed with the sender and does not count.
The 2026-11-21 20:20 fusion supersedes the shutting-down root: the seal
clears that mailbox in the terminate step.

`child_sub_refused` and `pool_sub_refused` were the one-script witnesses
that a supervised respawn did not birth the next generation. They do not
survive the 11:46 rule, and they must not be cited as closing that class.
`outlive_refused` still holds, because that mail sits on cores, the roots
are unsupervised, and a core is not sealed with the sender.

`GraphOk` is unchanged. `LocalOk` still does not read mailboxes. The step
no-op is the guard. The drained signal is how pure-stage learns the same
fact. It is not a state of this model.

## 2026-11-21 — Duplicate tombstone labels across root keys

Noted as N45. `tombstoneLabel` is the template's base label, then `#`, then
the generation. Two roots of one template at generation 0 and different keys
therefore share the string `dead/R#0`. The guard counts the sender id, not
the label, so the slot is held for the right occupant. A handler cannot tell
the keys apart by the label alone. The spelling is unchanged.

## 2026-11-21 — A tombstone waits until the dead stage's mail is consumed

Roland, 2026-11-21 11:46–11:50 CET, his own words and his approval. A dead
stage's tombstone, the `ChildDied` offered to its supervisor, is not
delivered while mail sent by the terminated stage, and by the descendants
sealed with it, is still in flight. In flight means sitting in a live
receiver's bulk or priority queue, not yet dequeued. Mail at a dead
receiver counts as consumed. There is no shutting-down receiver: the 20:20
entry seals the stage in the step that terminates it, and that seal clears
the mailbox. Parked sends need nothing: aborting the sender means that
message is never enqueued, and the kill drops it. This holds for every
supervisor. There is no per-supervisor flag.

The tombstone is still queued at the seal, on the supervisor's priority
lane, so it keeps its place in the lane census and `no_tombstone_overflow`
is unchanged. A priority receive skips a waiting tombstone and takes the
first message that is not waiting. The skipped tombstone stays in the lane.
It is not a head that stalls a later ready message. `slotTombstoneQueued`
stays true until the message is taken, so the population slot and the
respawn stay held, and that hold is counted.

`slotRespawnBlocked` is only the slot still occupied, or that tombstone
still queued. It does not consult `slotMailHeld`. The handler that consumes
the tombstone therefore runs when the in-flight set is already empty, and
the spawn in that handler is not refused for mail. The sender set is the
dead stage and its recorded descendants, which is who was sealed in that
termination. A sibling's tombstone, and mail from a live sibling, do not
hold this slot. `child_sub_respawn_enabled` is that birth for a per-peer
child. `guards_child_respawn_enabled` is the same when the mail sits on a
core and the spawn is the supervisor's later step, once the tombstone has
been received. The pool witnesses `pool_sub_respawn_enabled` and
`guards_pool_respawn_enabled` described a core pool and were removed with
pools. The one-script refusals
`child_sub_refused` and `pool_sub_refused` do not survive. They showed a
permanent drop under the old no-op, and they must not be cited as closing
that class (N49).

An unsupervised root has no tombstone. `loneOutstanding` still counts it
while it is alive, or while `slotMailHeld` says a surviving receiver holds
subtree mail. That is the population rule for E4, and `outlive_refused` is
unchanged. The seal clears the root's own mailbox in the same step, so a
dead root holds the slot only through mail a surviving receiver still has
(N50). The count is transient.

`survivesSender` counts a host that is alive, and `slotMailHeld` uses that
(N56). A supervised slot does not. `mailInFlight` requires the receiver's
life to be `alive`, so mail at a dead host is already consumed there. The
unsupervised count is the conservative one, and it is transient: that host
is sealed and its mailbox cleared in the step that terminates it.

`rootOutstanding`, the core-supervised count, is alive, or tombstone still
queued. The mail term is gone. The tombstone is queued in the seal and
cannot be received while that root's in-flight mail remains, so the slot
stays occupied through the drain. `guards_root_held_until_drain` is two
such roots. The tombstones stay queued, both labelled `dead/R#0`, until
`H` and `K` have taken the mail, and the spawn is enabled once both
tombstones are received.

Roland, 2026-11-21 11:49 CET: a pending tombstone adds no runtime wait
edge. The only blocking waits are parked sends, and this guard does not
wait on those. Dequeuing the dead child's mail is ordinary receive work,
covered by fairness. A standoff where receiver `B` waits on a protocol
message that only the supervisor's reaction to the death would send is a
higher-level protocol liveness question, the same shape as each side
sending only after the other has sent. It is out of scope. Both parties
stay responsive to other messages.

Deadlock freedom does not need the drain. A waiting tombstone is skipped,
so it blocks nobody. `fair_delivered` does need it: a tombstone is a
reliable priority message (N53). The obligation that its delivery
eventually becomes enabled follows from fair receive. It is argued here
and is not proved in `FairRun`.
`mailInFlight` is a finite set of messages already sitting in live actors'
bulk or priority queues. Each is program mail, not a tombstone, and its
sender is the dead stage or a recorded descendant. Those senders are dead.
The seal cleared their mailboxes, and the kill dropped their parked sends,
so they have no enabled send and the set cannot grow. A live receiver with
a nonempty queue is busy, and fair receive dequeues it. If that receiver
leaves `alive` first, what it still holds no longer counts. The set shrinks
to empty. `tombstoneWaits` is then false, and `receivePrio` is enabled for
the supervisor on the same condition as any other priority message: the
supervisor is alive and idle, and the lane has a message that is not
waiting. A waiting tombstone is skipped, so it does not stand at the head
and block a sibling's ready message.

`GraphOk` is unchanged. `LocalOk`'s restart check is unchanged. The one
spawn it allows is the transition that consumes the tombstone, or a state
reached only by consuming it. That attempt now happens when the in-flight
set is empty. The checker still does not read mailboxes.

## 2026-11-21 — A termination seals the stage in that step

Roland, 2026-11-21 20:20 CET. This supersedes the shutting-down phase.
`markShutdown` and the later seal are one step. `Life` is `absent`,
`alive`, or `dead`.

`terminateStage`, `abortChildren`, and `shutdownActor` take an alive actor
to dead in the step that terminates it. `releaseWorld` runs then:
`readCells`, `refundMsgs` through `creditLive`, `refundParked`,
`releaseOutbound`, an empty box, priority lane, and parked list, and
`releaseParked` for a non-call parked sender. The tombstone is queued on
the supervisor in that same step. `armTombstone` is not a step, and
`pendingTombstone` is not consulted. A stage that terminates inside its own
transition is sealed before that step returns. `dropDescendants` seals
descendants in the step, and their tombstones are not delivered. A sibling
is not in that seal.

The delayed tombstone is unchanged in one respect and restated for this
step. The message is queued at the seal, which is now the terminate step,
and `receivePrio` still skips it while program mail from the dead stage, or
from a descendant sealed with it, sits in a live receiver's bulk or
priority queue. Mail at a dead receiver counts as consumed — the seal
cleared that mailbox, and mail `crashWorld` leaves behind is never
dequeued. A parked send is dropped at the kill. The handler that consumes
the tombstone therefore still runs only after that live mail is gone, and
the spawn in the handler is not refused for mail. An alive sibling that
still holds the message withholds `ChildDied`; the refund is `creditLive`
when that sibling consumes it, which is before the handler can spawn the
next generation.

## 2026-11-21 — Abort advances the parent's continuation

Helen, round 16, at `05e42f884`. `Eff.abort` sealed the live children and
left the parent in `.run` with `.abort` still at the head. The tombstones
sat on the parent's lane, and the parent never reached a step that could
receive them.

The effect seals the children and then continues the parent. `proceed` is
applied to the actor `abortChildren` returned, so the lane that just
received the tombstones is the lane the continuation keeps.
`Deadlock/AbortCont.lean` is a checked parent: `Stop` is `.abort` followed
by `.internal`, the abort step leaves the parent running that `.internal`
with the child dead and the tombstone queued, and `finish` then `recvPrio`
takes the tombstone.

## 2026-11-21 — Abort after a tombstone crash leaves the parent running

The continuation above is unconditional. `enqueueTombstone` still crashes
the roster when the label is empty or the lane is full, and that crash is
inside `abortChildren`, before `proceed`. `crashWorld` has already set the
parent `dead` and `.crashed`. `proceed` keeps the dead life and, when the
tail is nonempty, writes `.run`.

`Deadlock/AbortCrash.lean` was that step before the guard below. The child
template's tombstone is `""`. The pre-state is a `SemInv` and a `MailInv`,
every non-absent actor is on the roster, and the parent stands on the
landing of its only transition. `proceed` then left the parent dead and in
`.run`. This entry records the bug. The 2026-11-22 06:37 guard is the rule.

## 2026-11-22 — A crashed effect does not continue

Roland, 2026-11-22 06:37 CET. `commitCont` is the continuation of an
effect. When the effect world has `crashed = true`, that world is the
result and the parent does not advance. `abort` still seals the live
children and queues their tombstones, and it still continues when the
enqueue fits. An empty label and a full lane are the same crash: both are
`crashWorld` inside the enqueue, and both stop before `proceed`. `spawn`
uses the same guard. `Deadlock/AbortCrash.lean` is the empty-label abort:
the parent is dead, `.crashed`, and not in `.run`.

## 2026-11-22 — A parent cycle still continues

Superseded by the 2026-11-22 07:01 entry. Kept as the record of the step
`Deadlock/ParentCycle.lean` reduces. The guard above stops only when the
effect world is crashed. A parent
pointer cycle is not a crash. `R` parents `C` and `C` parents `R`, both
alive, and `R` runs `.abort`. `abortChildren` seals `C`, and sealing `C`
seals `R` as its descendant, through `releaseWorld`, so `R` is dead and
`.idle` and the world is not crashed. `commitCont` then installs the
continuation. `Deadlock/ParentCycle.lean` is that step: the pre-state is a
`SemInv` and a `MailInv`, every non-absent actor is on the roster, and the
parent stands on the landing of its only transition. The post-state is not
crashed, the parent is dead, and its phase is `.run` of `.internal`.
`idleOff` rejects that phase, so the post-state is not a `SemInv`.
`exec_run_inv` is false for this world. No further change to the step
relation was made.

## 2026-11-22 — A reachable parent link is a forest

Roland, 2026-11-22 07:01 CET. Parent acyclicity is a reachable invariant,
not a change to the step. `ParentForest` is a conjunct of `Inv`: the parent
relation is well-founded, an actor off the roster has no parent, and every
recorded parent is on the roster. No actor is its own strict ancestor.
`spawn` is the only step that adds a link, and it adds one from a fresh id
to a parent already on the roster. The initial world has no parent links.

`Deadlock/ParentCycle.lean` is the cycle the step still reduces. Its
pre-state is a `SemInv` and a `MailInv`, and it is not `ParentAcyclic`, so
it is not a reachable `Inv`. On a forest, the actor running `abort` is not
a descendant of its own child, so it stays alive through `abortChildren`
unless the enqueue crashes, where `commitCont` returns that crashed world.

## 2026-11-22 — A lone terminable may address a core

The occupancy invariant, not the step. `noBulkSend` mutes a plain `send` and a
`selfSchedule`. It does not mute a `trySend` or a `call` whose outcome lists
are themselves mute. A checked lone terminable per-peer can place that
message in a core. The core's mailbox keeps it after the sender is sealed:
`releaseWorld` refunds the sender's own lanes and its parked outbound, and
the message already delivered stays where it was queued.

`OccInv.coreFrom` used to say mail in a core comes from a core or from a role
that does not terminate. That excludes this sender. `coreSender` is the
placement the account uses: a core, a role that does not terminate, or a
lone terminable per-peer. A subtree member is still excluded. Its program
only addresses a per-peer of its own subtree, and sealing that subtree takes
the mail with it.

`OccInv.still` used to say a lone terminable owes nothing. The same message
is queued mail. `still` is now the slot bound: that actor's `owed` is at
most its template budget. The charge is the live generation's tokens plus
`queuedFromKey`, the same equation as every other per-peer slot. The message
is not a second account, and it is not forbidden.

Two generations of one template share a key, so a sum of `budget` over roster
ids of that key counts the template twice. That sum is not the edge fold.
The account that replaces it is one budget per live slot, with every
generation's mail in `queuedFromKey`.

## 2026-11-22 — A pool mailbox may park under Lemma 1

The capacity check is not a promise that the parked lane stays empty.
`l1` compares edge occupancy with capacity for every population `N`. A
per-peer edge stores its budget in the `a` coefficient, so at `N = 1` that
edge pays for one key. A core-supervised pool's population is `slots`, not
`N`. An earlier key can leave its message in the core, the core can seal
that child and birth the next slot, and the new child can send while the
old message is still queued.

`Deadlock/PoolPark.lean` is that run. The core's capacity is `1*N+1`, Lemma
1 holds, and `N = 1`. After two sealed children have each delivered one
message, the third child's send finds the box full and parks. The world is
not crashed. The box holds 2 and the parked lane holds 1, against
`capBulk = 2`. Alive children of that template never exceed `N`.

`OccInv` does not claim `parked = []` on a Lemma-1 host. The account that
remains is per key: `queuedFromKey` is at most that template's budget, and
the live generation's tokens are the rest of the same equation. The sum
over a pool's keys is not bounded by `capBulk`. `enqueueOrPark` parks when
the box is full; that branch is reachable, and the occupancy proof has to
follow it.

## 2026-11-22 — A delivery reserves the checked path

`sendsOk` does not compare `sendsTo` of the main tail plus `floor(toState)`
with `floor(fromState)`. It checks `pathReserve` of the transition, the
maximum of `sends + floor(landing)` over the reply and every outcome branch,
against the floor of `fromState`. Delivering a priority message leaves the
receiver idle at `toState`, or running that program. In both cases the new
`tokenHold` is that `pathReserve`, and the tokens do not move. The slack
bound is the inequality the checker already proved. A name with no template
has floor 0, and a checked program has no edge there, so its reserve is 0
as well.

## 2026-11-22 — A returned token goes to the live generation

The step already does this. `creditLive` gives the slot to `budgetHolder`:
the sender, when the sender is a core or no generation of that key is alive,
and the live generation otherwise. Charging a new incarnation for mail left
by an earlier one only stays an equality if the refund of that mail returns
to the incarnation that holds the budget. Crediting the raw sender, after
that sender is dead, would leave the token on an actor the account does not
add, and the live equation would drop by one. The occupancy proof follows
`creditLive`. It does not change the step.

## 2026-11-22 — A crash keeps the queued mail inside the budget

`crashWorld` kills every alive roster actor and leaves every mailbox as it
was. The world is then crashed, so `quiet` and `deadEmpty` are not claimed.
A key that had a live generation loses that equation. The mail stays in
`queuedFromKey`, and it is still at most the budget: the live holder had
nonnegative tokens, because its `tokenHold` was a natural number bounded by
those tokens. A key that already had no live generation keeps the inequality
it had.

## 2026-11-22 — A call resume does not raise the reserve

`resumeSender` on a call park moves to `awaitReply`. On a plain park it
`proceed`s. `tokenHold` of `awaitReply` includes the timed-out program, so
resuming a non-call park as a call can raise the reserve. While the sender
is alive, `MailInv.fwd` says the parked flag is the phase's flag, so that
resume does not occur. A resume that is not a call never raises `tokenHold`.
The occupancy step takes that side condition. It does not change
`resumeSender`.

## 2026-11-22 — A spent token is bounded by the reserve

`tokenHold` is the reserve the ingress gate checked. `pending` is a send
count, and a parked call counts its own message there again. Spending one
token keeps `tokenHold` plus that token under the reserve the actor already
held. The occupancy step uses that inequality. It does not change the charge.

## 2026-11-22 — A call waits on its own outcomes

`execRun` of a call stores that call's `onNotAdmitted` and `onTimedOut` on
`afterHead`. Waiting on the outer continuation would reserve the outer
timeout, which the call's reserve does not cover. The occupancy step follows
the continuation the step stores. A send still proceeds on `afterHead`, and
the spent token plus that tail stays under the head effect's reserve. Neither
fact changes the step.

## 2026-11-22 — A non-call park keeps the tail

A full mailbox parks the message. For a send the phase is the tail, and the
spent token is the one the head effect already reserved. The parked message
is the charge, so the phase does not count it again. A parked call's reserve
also includes `onTimeout`, which the running phase did not hold, so that case
is separate. The step is unchanged.

## 2026-11-22 — A missed call runs its own refusal

A call aimed at a name that is not alive finishes as `NotAdmitted` on that
call's own `onNotAdmitted`. That list is the not-admitted branch of the call's
reserve, so the finish does not raise `tokenHold`. A send to a dead name still
proceeds on the tail. The step is unchanged.

## 2026-11-22 — A full self-schedule crashes the world

A self-schedule that does not fit the priority lane crashes the world. The
occupancy proof follows `crashWorld`. Killing only the sender was a stale
account of the same step. The step is unchanged.

## 2026-11-22 — An empty-subtree root takes a fresh key

A root with an empty subtree is born at `nextIx`. Occupancy records that every
such key already on the roster is below that counter, so the birth does not
share a slot with a live generation. Keys of every other template are
allocated elsewhere and are not part of this bound. The step is unchanged.

## 2026-11-22 — A scheduler root is born on a fresh key

`spawn` installs one peer at `nextIx` or at `freshKey`. The key has no
generation on the roster yet, so the newborn is the only live holder and its
tokens are the whole budget. A checked description does not put a supervisor
on an empty subtree, which is why that birth uses the subtree counter. The
step is unchanged.

## 2026-11-22 — A refund counts the live holder

Refunding a mailbox, or the messages parked behind it, credits the live
generation of each message's key, the same holder a delivery credits. The
count is that holder, not the generation that sent the message. Draining the
box or the parked lane one message at a time is the same world. The step is
unchanged.

## 2026-11-22 — A parked call reserves the tight count

The occupancy reserve of a parked call is the tail, the not-admitted path
without its own token, and the timed-out path. The ingress gate keeps the
older, larger count, including a stale timeout, under the name `gateHold`.
Refusing an ingress that would pass the tight count and fail the gate is not
a fairness obligation. The step is unchanged.

## 2026-11-22 — A lone terminable is charged on its own slot

A lone terminable may `trySend` or `call` when its branches are mute. The
charge stays on its own slot, and `still` is the bound. It does not follow
that such an actor has no parked mail. The step is unchanged.

## 2026-11-22 — Marking the live holder dead weakens the slot equation

While a generation is alive, its tokens plus the key's queued mail equal the
budget. Marking that holder dead drops the equation to the inequality: the
queue is at most the budget, because the holder's tokens were nonnegative.
The step is unchanged.

## 2026-11-22 — Sealing refunds before the actor is marked dead

`releaseWorld` and `forgetHost` credit the actor itself, not whichever
generation happens to be live. That credit is the live holder's only while
the actor is still alive, which is when both steps run. A descendant seal
and a shutdown both check the life first. `admitHost`, `abortActor`, and
`abortDesc` are not steps. A stage terminates by sealing its descendants and
then itself. The step is unchanged.

## 2026-11-22 — Draining then releasing outbound is the seal

`releaseOutbound` never reads the actor it is crediting, so draining that
actor's mailbox and then releasing outbound is the same world as refunding
and then releasing outbound. The final dead record overwrites the mailbox
either way. The step is unchanged.

## 2026-11-22 — Killing one member does not crash the roster

`killOne` refunds the mailbox, fails plain waits, returns outbound slots, and
leaves the member dead and idle. It does not set the crashed flag. The same
flag on the drain-then-forget account is the original flag, so the two
worlds agree. The step is unchanged.

## 2026-11-22 — A killed member's plain waits are resumed

A non-call parked on the member runs its continuation before the mailbox is
cleared, so the entry and the park disappear together. A parked call stays
parked, and a call parked on a target that is now dead needs no entry. The
roster does not change, and the member's life becomes dead rather than
absent. Semantic compatibility, mail, and the open-slot roster all hold of
the result. The step is unchanged.

## 2026-11-22 — Abort uses the parent forest

The occupancy account of one effect takes the parent forest. Aborting the
children can crash the roster, and otherwise the parent is still alive and
still running the same continuation, so the effect advances. Acyclicity is
what keeps a child from sealing that parent. The step is unchanged.

## 2026-11-22 — A free-slot respawn can be short of its idle floor

`withKeyTokens` gives the new generation `budget − queuedFromKey`. That is the
live-slot equation, and it is not the idle reserve. `C` at key 0 generation 0
is dead and still on the roster, its message to `H` is still queued
(`queuedFromKey = 1`, `budget(C, H) = 1`), and the parent's tombstone has left
the lane, so `slotRespawnBlocked` is false. `spawnChild` admits generation
`maxGen = 1`. The newborn is idle in `Idle`, whose floor is 1, and its token
for `H` is 0. The birth does not satisfy the occupancy reserve. The parents
and the host, both alive and idle, have floor 0, so the shortage is the
newborn's. The step is unchanged.

## 2026-11-22 — The parked lane was the tombstone hole

`tombstoneWaits` is `mailInFlight` of the tombstone's sender. The scan walks
every roster host, keeps a host whose life is `alive`, and looks for a
non-tombstone message `sealedTogether` with that sender. The sender itself
is sealed together with itself, so a live sibling is counted, and the
generation is that sender id. In the sealed fuse world the message is in
`H`'s box, `H` is alive, `queuedFromKey` is 1, and `receivePrio` is already
`none`. Key indexing, the liveness test, and a missing sibling are not what
lets the parent take the tombstone.

The lane the scan did not look at is `parked`. `queuedFromKey` counts
`p.msg` there. `enqueueOrPark` appends the entry to the live target when the
bulk lane is not free. The same sealed world with the message only on
`H.parked` had `tombstoneWaits = false`, and `receivePrio` returned a world,
while `queuedFromKey` stayed 1 and `H` stayed alive. A dead host's own
priority message does not count: the lane checks sit under the liveness
test. `releaseOutbound` drops `p.sender == dead` at the seal, so a tombstone
queued by `shutdownActor` is not born next to that parked mail. The receive
still accepted a world that still had it. `cleared` is not that receive. It
deletes the tombstone by a state edit while the box still holds the message.

## 2026-11-22 — A tombstone waits on the live queues

2026-11-22 20:05, Roland approved option (a). A tombstone for a generation is
not consumable while any mail sent by that generation, or by a descendant
sealed with it, is queued at a live host. The lanes `mailInFlight` counts
are the bulk queue and the priority queue. Mail at a dead host still counts
as consumed. The spawn guard is unchanged: the slot stays blocked because
the tombstone stays queued, not because spawn reads the mail.

The wait ends when that mail is consumed or the host dies. `fair_box`
empties a finishable peer's bulk queue. `Fair.prio` takes a priority
message once the actor is idle and the receive stays enabled. Sealing the
host refunds its box and clears its parked list. A separate theorem that
every held message meets one of those ends is not proved here. The two
drain lemmas keep their statements.

## 2026-11-22 — A parked send is credited in the seal

2026-11-22 21:01, Roland. A parked send is credited in the sender's
termination step. Nothing is enqueued in the mailbox. `releaseOutbound`
drops `p.sender == dead` and `addTokens` returns that count to the sender
while the sender is still alive. `releaseWorld` then installs the dead
actor and keeps those tokens. Inbound parked mail on the dying actor is
`refundParked`, which is `creditLive`. `livePark` counts that inbound side.

A live host therefore does not hold a parked entry whose sender is already
dead. That is `ParkedFromLive`, a field of `SealInv`, and `Inv` carries it
beside `ParentForest`. `occ_set` may still change `prio` and `parent`, so
the fact stays out of `OccInv`. The parked-lane scan of `mailInFlight` is
reverted: it was justified only by a state edit that puts a dead sender's
entry back after the seal. `parkedHold` is outside `Inv`. The box case of
`cleared` is the same kind of edit: deleting the tombstone while the
message sits in a live box is not a step. It lies outside the tombstone
chain, and the receive still refuses that box.

## 2026-11-22 — A sealed child is waived while its parent lives

Sealing a child does not enqueue that child's tombstone. While the parent
is still alive, the child is a gap in the tombstone chain. Releasing the
parent repairs those children, because their mail is then the parent's
mail, and the gap that remains is only the parent. Queueing the parent's
tombstone closes it. If the parent is already dead, the child's mail is an
ancestor obligation and the gap closes at once.

A birth does not adopt queued mail. The fresh id is off the roster, so no
queued message names it, and one extra roster slot does not reveal a new
descent among the ids that were already present. A child is born under a
live parent, or under none.

## 2026-11-22 — A pool's live count is not `N`

`N` is the root population. A per-peer root with `slots = 0` has `N`
instances. A core-supervised pool has `slots` instances. `OccInv.livePeer`
asks every per-peer template for `aliveCount ≤ N`, and the live-debt sum
uses that to stay under `occupancy.eval N`.

`Deadlock/SpawnCount.lean` passes `checkBool` and `localOkB`. At `N = 1`,
`W` has two slots and the core spawns it twice with no abort. Both children
are alive. Each idle child has debt 1 toward `W`, so the live sum is 2.
`(totalOcc "W").eval 1` is 1, and Lemma 1 holds. Each child's tokens are 1
and its `tokenHold` is 0, so the per-key reserve fits. The template-wide
live sum does not. The checker still multiplies a per-peer edge by `N`.

The population rule already says a pool counts as `slots`. The step relation
is left as it is. Closing the sum is a checker change: a pool edge pays for
its slot count, and the live bound follows `population`. Refusing the birth
past `N` would be a step change, and a pool could not reach `slots` when
`slots > N`. A static ban that holds for every `N` is that same accounting,
or it forbids pools.

## 2026-11-23 — Pools removed

2026-11-23, Roland, by voice. Pools are removed. They are not repriced.

The connector's `connect-worker-{n}` stages are created lazily up to
`DEFAULT_PARALLEL_CONNECTION = 10`, reused from the idle list, never
terminated, never restarted, and unsupervised. Nothing dynamic remains, so
they are ten fixed stages. No description in `examples/*.json`,
`Deadlock/Examples.lean`, or an exporter names `slots > 0`, and none names
those workers, so the model does not invent ten core templates for them.
Each listener's accept stage is a static core. It does not terminate. The
accept call is a detached effect, and its result comes back to that core as
an ingress message: `Accepted`, or `AcceptError` for `AcceptError::Other`.
Both edges are non-blocking, so the completion adds no wait and the stage
never waits on its own result. The core has one bulk slot. That is the
outstanding bound: one completion may sit in the box, and a second is
refused until the first is received. The slot is Lemma 1 for the mailbox
and `prioSized` for one priority sender. There is no `Listen(addr)`
tombstone and no respawn. `examples/accept.json` is that listener, and
`Deadlock/Accept.lean` records the bound. Production still terminates on
`AcceptError::Other` and still respawns through `Listen(addr)`. Those
changes stay pending in `RUST-CHANGES.md` and are not made here. A connection stage is
already one scheduler root per key. A per-peer parent births one child of
each template at its own key. A done-trap is the exception: the connection
spawns one on every expected stop, and those traps stay alive together under
that connection. A done-trap sends nothing. Its only effect is terminate,
which tears the connection down, so it does not matter for deadlock.

`Template` no longer has `slots`. `spawnChild` on a core is `none`, and
`spawnScope` rejects a core's `Eff.spawn`. A per-peer parent still births
one child at its own key. Generations, `slotRespawnBlocked`, and tombstone
delivery are unchanged. Population of every per-peer template is `N` at a
root and the parent's population under a per-peer supervisor.

This supersedes the pool adoption of 2026-11-21 20:20 and the pool entries
of 2026-11-22, including the live-count note above. `SpawnCount.lean` and
`PoolPark.lean` recorded pool behaviour and are deleted.

## 2026-11-23 — Accept error occupancy and the re-issue gap

The `AcceptError` edge is occupancy 0 and legal 0. Both numbers are
`Affine.ofNat`, so each is a pure `b` count with `a = 0`. The three
neighbouring pairs fail `checkBool`:

- occupancy 1 and legal 1, and occupancy 1 and legal 0, put two units of
  occupancy into a capacity-1 mailbox, so Lemma 1 fails
  (`accept_err_one_one`, `accept_err_one_zero`);
- occupancy 0 and legal 1 keeps the occupancy sum at 1, and the ingress
  check adds that legal count to the `Accepted` edge's occupancy. The sum
  is 2, above capacity (`accept_err_zero_one`).

The `(0, 0)` pair is what lets the error share the mailbox with `Accepted`.

Nothing in the model issues the accept. The completion is environment
ingress. Nothing bounds a detached call beyond the one mailbox slot, and
nothing checks that a new accept is issued only after the result has been
handled. `accept_fits_prio` sizes the priority lane. Completions arrive on
the bulk lane; the mailbox bound is `accept_fits_occ`, `l1` and
`accept_cap`. The re-issue rule is a production obligation in
`RUST-CHANGES.md`.

## 2026-11-23 — A state of maximum debt cannot send

`sendsOk` requires `pathReserve(program) ≤ floorState(fromState)`.
`floorState` is `budget - debt`. A straight send reserves
`1 + landFloor(landing)`, and `landFloor` is that same floor, so an
admitted send needs `debt(landing) ≥ debt(from) + 1` when both debts sit
under the budget. Debt is at most the budget, so the state whose debt
equals the budget has floor 0 and cannot be the source of a send.

A one-state loop fails at once. `Deadlock/ForwardLimit.lean` is that
loop: one core, state `idle`, one blocking self-edge of occupancy 1, and
a transition that sends that label back to `idle`. `sendsOk` is false
and `localOkB` is false. A two-state machine can send only toward the
strictly higher debt, and cannot return. `localOk`, the checker, and the
step semantics are unchanged. Whether a forwarding core should be
admitted is open.

## 2026-11-23 — A parked call's hold does not cover NotAdmitted

`tokenHold` of `.parked target true` subtracts the call's own slot from
the `NotAdmitted` reserve. `finishCall` of `.notAdmitted` spends that
reserve in full. The two are not ordered.

`Deadlock/TimeoutGap.lean` is the smallest description. One core, states
`idle` (debt 2 toward `box`) and `busy` (debt 0). Budget is 2, so the
floors are 0 and 2. The actor is parked on `.core "box"` with
`onNotAdmitted` empty and landing state `busy`. `tokenHold` is 1.
`finishCall` of `.notAdmitted` has `tokenHold` 2. `gap_old`, `gap_new`
and `gap_grows` are closed by `decide`.

`callTimeout` refunds one token per parked call entry of that caller and
then runs `NotAdmitted`. The refund covers the extra unit when the entry
is still queued. `OccInv.parkedCall` is the other case: the
`NotAdmitted` hold is already within the tokens. `refundParkedCall`,
`tokenHold` and `callTimeout` are unchanged.

## 2026-11-23 — Sealing the callee drops a parked call

A caller whose phase is `.parked dst true` does not always have an entry
in `(st dst).parked`. `Deadlock/ParkDrop.lean` is one `exec` step.

`box` is a per-peer template with subtree `tree`. `callee` is the peer
`box` at key 0, alive, running `terminate`, with one parked call from
`caller` (a core). `caller` is alive and its phase is `.parked callee true`.
`before_entry` is that filter, length 1. `apply` of `.exec callee` is
`some`. `terminateStage` seals `callee` because the subtree is nonempty,
and that branch does not consult `hasParkedCall`. `releaseWorld` credits
the caller (`refundParked` / `creditLive`), clears `callee`'s parked list,
and `releaseParked` resumes only a non-call. `seal_drops_parked_call`:
the caller is still `.parked callee true`, `callee` is dead, and its
parked list is empty.

The same step is what a later `callTimeout` of the caller would see: the
phase is still parked and the filter `refundParkedCall` uses is empty.
The step semantics are unchanged.

The ledger still balances. `seal_shifts_one` is one more token on `box`
and one less queued entry. `shift_keeps_budget` is the sum. `led_budget`
is 2, the parked hold is 1 and `NotAdmitted` spends 2
(`led_hold_parked`, `led_hold_done`). `timeout_keeps_tokens` is the
deadline after the seal: the filter is empty, so nothing is credited
again. `credit_covers_notAdmitted` is the one extra token against a hold
that grows by one. pure-stage does the same with the caller:
`terminate_stage` leaves a sender that is waiting on a call until the
deadline, and does not resume it as a failed send.

## 2026-11-23 — A parked call is queued or already covered

`OccInv.parkedCall` is the missing entry. While the caller is alive, a
phase `.parked dst true` means the call is still in `(st dst).parked`,
or `tokenHold` of `finishCall` with `.notAdmitted` is already at most
the caller's tokens. A dead parked actor is exempt: the clause is only
required while `life = .alive`.

The target's death is not a conjunct. `refundParkedCall` credits an
alive target and is not itself a step. `callTimeout` then runs
`finishCall` and leaves the parked phase in that same step. A seal takes
the credited branch only after the target is dead. Storing the death in
the clause would leave that in-step refund with no `OccInv`.

An admit moves a parked call into the mailbox and resumes the sender in
the same step. `receiveBulk`, when both the box and the parked list are
nonempty, credits the box head's sender rather than the parked caller.
The intermediate still has that caller in `.parked _ true` with the
entry gone, and `hold_na_bound` says a timeout from there is one token
short. `MailInv` already treats the mailbox update and the sender's
phase update as one step. `OccInv` is proved on the post-resume world.

`occ_timeout` cases on the clause. An entry refunds at least one token,
and `hold_na_bound` bounds the `NotAdmitted` hold by the parked hold plus
the call's own slot. A caller already covered stays covered because the
refund is nonnegative. `tokenHold` is still the phase's reserve. The
clause is what makes the extra unit available. `tokenHold`, `gateHold`,
`receiveIngress` and `callTimeout` are unchanged.

Workarounds recorded with the proof: the clause applies only while the
caller is alive; the target's death is not a conjunct; the admit
intermediate is the post-resume world; a parked timeout uses `occ_set`
because both the tokens and the hold rise by the refunded slot; a
consumed entry is credited to `budgetHolder`.

## 2026-11-24 — Checker completeness: an arm call is a call site

`callSites` is the only change. `callPairs` and `callPairEff` mirror
`effectsOk` and `effectOk`: structural mutual recursion on the program
and on each effect, with no fuel cutoff. A cutoff would drop a deep
call and bring the `msgOk` failure back. The arms are `onFull`,
`onGone`, `onNotAdmitted`, `onTimedOut`, and `onTimeout`.

No new call edge is added. `effectOk` already requires the edge for an
arm call, and `effReserve` already takes the max over those arms. A
second edge would be counted twice in `totalOcc`. `labelHandled` and
`GraphOk` still read the edges the description already has. `msgOk`
is unchanged. It is `callFrom = none` or `callSite`. There is no
timeout disjunct.

`callTotal` now demands `acceptsCall` in every state of the callee,
including an arm that can never fire. That is stricter than
`targetStates`, and it is not unsound. Restricting `callTotal` to
`targetStates` is deferred. `inProg_call_mem` states all seven
`InProg` cases, and `callSites_pairs` is the recursive walk.

Helen found no counterexample of `call_answered` under partial
compatibility. That question is closed. The Rust checker is not
recorded here.
