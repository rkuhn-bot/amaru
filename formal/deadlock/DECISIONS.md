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

`prioSized` counts the children that can tombstone at once, the other
priority senders, and the tombstones still queued from dead predecessors.
`maySpawnRoot` passes that last count and refuses the spawn when the lane
cannot hold another. A parent restarts a dead child at a fresh generation
of the same subtree key. The dead id is not reused. A supervisor that is
dead or shutting down admits no new child.

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
