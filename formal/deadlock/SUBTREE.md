# Per-peer subtrees

A connection is one subtree. The mux reader waits, untimed, on the leading edge of a segment header. A mini-protocol timeout in the same subtree is a timed peer, and its `awaitPeer` kills every live member of that key in one step. The checker allows the untimed wait because that kill is what ends it.

## Kill

`Action.kill sub key` is enabled when some live `timeoutKills` member of that key is in `awaitPeer`. The step is `killSubtree`: each live member whose role names `sub` and whose index is `key` is killed, then `tombstone` becomes `some key`.

The tombstone is a world field, not a bulk message — a bulk message would spend a credit the supervisor may not hold. For each member the step refunds what the mailbox held, fails whoever was waiting on that member, drops parked entries that name the dead sender, and leaves the member dead and idle with an empty mailbox. A dead actor is idle. A live actor is on the roster. An actor off the roster has an empty parked list.

A terminable member has no outstanding send and is not in a call, so the refund is the whole occupancy account and no call tag moves. `kill` preserves the step invariant, occupancy, and call tags. `deadlock_freedom` is proved with no `sorry`.

## What the checker allows

- A call or a reliable send may name a terminable role when both ends share a nonempty subtree. The subtree dies as a unit, so the caller does not outlive the callee.
- A call that leaves the subtree may target only a non-terminable template. `mux_cross_fails` is that rejection.
- An untimed peer wait is allowed when a timed `timeoutKills` peer shares the subtree — the mux reader's wait on a header. A pure untimed wait, with no such peer, is not an interior dependency and is not a permanent mailbox.
- `finish` proceeds a finishable peer wait. An untimed wait is finishable only when that killing peer exists. The teardown of the subtree is the kill step.

## Routing

`route` addresses a per-peer role by the sender's own index, not by the `Nat` hint on the effect. A core has no index, so it does not resolve a per-peer target. `isMember` is that index together with the role's subtree name. `spawn` allocates the next index of one role. The first instance of every role is index 0, which is the key `mux_kill` kills.

## Witness

`muxDesc` passes `checkBool`. From the initial world the run spawns the opener, the timer, and the reader, arms the timer, and takes `.kill "conn" 0`. The timer and the reader are dead, the opener is still alive, and the tombstone is `0`.
