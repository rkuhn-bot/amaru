# Per-peer subtrees

A nonempty subtree is one connection. Amaru starts one connection stage for each `conn_id` (`start_connection_stage` in `crates/amaru-protocols/src/manager/mod.rs`) and that stage supervises the mux and the mini-protocols. Those stages are descendants of the one connection root. Two scheduler roots never form one connection.

## One unsupervised root

`GraphOk` rejects a nonempty subtree with two or more templates whose `supervisor` is `none`. A scheduler root takes a fresh subtree key, shared by the templates of that birth and not by the next root. A send resolves the sender's own key, so a send from one root does not reach the other root's child. A per-peer child is born at its parent's key and records that parent.

A subtree may have no unsupervised template. Every member then names a supervisor that is a multiplicity-one core or a per-peer stage of the same subtree. A core-supervised member is still a scheduler root of its own key; the population bound on that birth is separate from this check.

## What else the checker records

- A subtree member is per-peer.
- A named supervisor is a multiplicity-one core or a per-peer stage of the same subtree, and not the member itself.
- A pool (`slots` > 0) names a multiplicity-one supervisor. Slots under a per-peer parent are rejected.
- A supervised child names a nonempty tombstone. `GraphOk` rejects an empty one, so a reachable seal does not enqueue an empty label.
- An untimed peer wait is allowed when a timed `timeoutKills` peer shares the subtree. A pure untimed wait is not an interior dependency and is not a permanent mailbox.

`muxDesc` is that shape. `timer` is the one unsupervised root and the killing timeout. `reader` is its child, and the untimed header wait sits in the same subtree.
