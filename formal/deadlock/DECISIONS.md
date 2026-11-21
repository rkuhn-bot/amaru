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
dead id is not reused. A supervisor that is dead or shutting down admits no
new child. A core births a pool of `slots` children, indexed by slot and
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
a core into that slot returns no world. A slot that is still shutting down
is occupied: the tombstone is not queued until the seal.

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
`GraphOk` and `LocalOk`, a pending seal of a shutting child does not fill a
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
incarnation is shutting down or dead. An empty tombstone on a live parent is
not a reachable seal under `GraphOk`. A root under no supervisor is bounded by how many are
alive. A root under a core is bounded by how many are alive, shutting down,
or still have a tombstone queued. `supervisor` is an `Option`: `none` does
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
`slotRespawnBlocked` is that mail, or the slot still alive or shutting
down, or its tombstone still queued. `spawnChild` is then a no-op, the
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
consumed or dropped. Mail at a dead or shutting-down receiver counts as
consumed. A parked send of a stage that is killed is dropped at the kill
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
`rootOutstanding` is the core-supervised count, and it still includes a root
that is alive, shutting down, or waiting on its tombstone. `loneOutstanding`
is the unsupervised count: alive, or still holding subtree mail. An
unsupervised root has no tombstone. Shutting down alone does not hold its
slot. A shutting-down root that still holds a descendant's mail does, until
its own seal clears that mailbox. Fresh keys are unchanged.

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

A host counts while its life is alive or shutting down, unless it is sealed
together with the sender. Sealed together means the host is the sender, or
it sits under the sender on the recorded parent chain. `terminateStage`
seals those descendants in the same step (`dropDescendants`, `sealBranch`,
`releaseWorld`) and seals the sender itself at its later seal.
`releaseWorld` empties that actor's mailbox and does not clear a sibling, a
parent, or a core. Mail on a host that dies in that seal does not hold the
slot. At a later spawn check those hosts are already dead, so the life
filter excludes them as well. A sibling is not in that seal. Its copy stays
until that sibling consumes it or seals on its own.

`slotMailHeld` is that test. At 09:30, `slotRespawnBlocked`, `freeSlot`,
`rootOutstanding`, and `loneOutstanding` all used it. A same-key respawn was
a no-op while the mail remained. A fresh-key root still occupies a
population slot while it remains, and that half is what `loneOutstanding`
keeps. Shutting down alone does not hold an unsupervised root. Mail on the
root itself is sealed with the sender and does not count. A shutting-down
root that still holds a descendant's mail does count, until its own seal
clears that mailbox.

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
receiver's bulk or priority queue, not yet dequeued. Mail at a dead or
shutting-down receiver counts as consumed. Parked sends need nothing:
aborting the sender means that message is never enqueued, and the kill
drops it. This holds for every supervisor. There is no per-supervisor flag.

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
hold this slot. `child_sub_respawn_enabled` and `pool_sub_respawn_enabled`
are that birth, for a per-peer child and for a pool child.
`guards_child_respawn_enabled` and `guards_pool_respawn_enabled` are the
same when the mail sits on a core and the spawn is the supervisor's later
step, once the tombstone has been received. The one-script refusals
`child_sub_refused` and `pool_sub_refused` do not survive. They showed a
permanent drop under the old no-op, and they must not be cited as closing
that class (N49).

An unsupervised root has no tombstone. `loneOutstanding` still counts it
while it is alive, or while `slotMailHeld` says a surviving receiver holds
subtree mail. That is the population rule for E4, and `outlive_refused` is
unchanged. Shutting down alone does not hold that slot. A shutting-down
root that still holds a descendant's mail does, until its own seal clears
that mailbox (N50). The count is transient.

`rootOutstanding`, the core-supervised count, is alive, shutting down, or
tombstone still queued. The mail term is gone. The tombstone cannot be
received while that root's in-flight mail remains, so the slot stays
occupied through the drain. `guards_root_held_until_drain` is two such
roots. The tombstones stay queued, both labelled `dead/R#0`, until `H` and
`K` have taken the mail, and the spawn is enabled once both tombstones are
received.

Roland, 2026-11-21 11:49 CET: a pending tombstone adds no runtime wait
edge. The only blocking waits are parked sends, and this guard does not
wait on those. Dequeuing the dead child's mail is ordinary receive work,
covered by fairness. A standoff where receiver `B` waits on a protocol
message that only the supervisor's reaction to the death would send is a
higher-level protocol liveness question, the same shape as each side
sending only after the other has sent. It is out of scope. Both parties
stay responsive to other messages.

The obligation that delivery of the tombstone eventually becomes enabled
follows from fair receive. It is argued here and is not proved in `FairRun`.
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
