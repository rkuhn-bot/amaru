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
