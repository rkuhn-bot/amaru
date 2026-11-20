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
terminates.

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
Crash is a reachable outcome: a permanent core's `terminate`, and a priority
enqueue onto a full lane. It is not a silent escape from a stuck parked send.

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
sealed. Refunds still go to the live generation of the sender's key. A peer
whose template tombstone is empty keeps an empty label, so the enqueue
crashes before `offerPrio` and that slot is not in the affine count.

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
of `LocalOk`. That bound does not keep a tombstone inside the lane. A
self-schedule or a cell wake that does not fit still crashes. That is
pure-stage's panic.

Pure-stage will be changed to match this bound. Its tombstone queue is an
unbounded `VecDeque` (`supervisor.tombstones.push_back` in
`crates/amaru-pure-stage/src/simulation/running/mod.rs:1323` at `34a45300`).
That is an implementation change to make, not a defect in the model.

## 2026-11-20 — Two live generations overflow one lane

`no_tombstone_overflow` is false, and the semantics are left as they are.
`Deadlock/Counterexample.lean` is a `GraphOk`, `LocalOk` design whose
`prioSized` check passes. It runs at population 8.

An empty-named root at key 5 spawns `R` generation 0. Later scheduler births
of `R` fill keys 0–4 and then take key 5 again, because `openSubtreeKey`
only searches below `nextKey`. Generation 1 is born while generation 0 is
still alive. `findLive` returns generation 0.

Generation 0 spawns `C`. The seal queues `dead/C#0` on generation 0, whose
priority capacity is 1, so the lane is full. Generation 1 is still in
`boot`. `restartOk` treats the spawn from `boot` as a first birth, and the
spawn looks at generation 1's own empty lane, so the second `C` is born.
Its seal offers another tombstone to generation 0, and `offerPrio` crashes.
The same actions do not crash when that capacity is 2.

`restartOk` and `prioSized` both account for one parent instance. They do
not count a second live generation of that instance. Refunds still go to
the live generation, and the tombstone is still queued at the seal.
