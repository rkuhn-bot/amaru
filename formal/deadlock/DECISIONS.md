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
this adds no scope. For the later multi-template and nested-supervisor work,
occupancy bounds become a parameterized product along the supervision tree,
not a flat N per template.

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
