# Per-peer subtrees

Design note only. The checker and the step relation in this tree do not implement it.

## What the node does

A connection is a tree, not a single actor. The mux is terminable and is also a call target (`miniprotocol`, blockfetch). The connection, the mux, and the blockfetch initiator both terminate and bulk-send or call. When the connection's parent terminates, the children are aborted with no tombstone: nothing is enqueued to tell the rest of the node.

`Eff.send` and `Eff.call` carry the peer index as a literal `Nat`. `route` resolves `InstId.peer dst hint` and returns `none` when that id is not alive; the sender then `proceed`s and the message is gone. `spawn` allocates `nextIx`, so a respawned child is a new id. A hint captured earlier does not name it, `route` is `none`, and the message is dropped.

## What the model should say

- An owner kills a per-peer subtree in one step. Every member changes to dead together. There is no window where the parent is dead and a child is still alive, and no window the other way.
- A call or a blocking send whose target is in the same subtree is allowed even when that target is terminable. The subtree dies as a unit, so the caller does not outlive the callee.
- A call that leaves the subtree may target only a non-terminable core. `permanentTarget` is the special case of that rule for today's flat roster.
- Outstanding messages of a dead member stay in the occupancy count (`owed` does not drop to zero just because `life` did) until a real receive or an explicit supersede consumes them. That is the dead-instance lift. It is not in the proofs here.
- Abort delivers one guaranteed message to the supervisor. That message is the tombstone. It is not a best-effort `trySend`, and it is not silence.
- Routing does not use a literal hint stored in the effect. The continuation or the actor carries a `peerKey`, or the message carries a reference that `route` dereferences. `spawn` allocates one fresh key for the whole subtree, and every member is named by that key plus a role. Respawn allocates a new key; old messages do not resolve.

## What stays true

Superseding cell writes may still be dropped. A reliable send, call, or `trySend` may not. `reliable_try_fails` is the flat-roster case of that rule.
