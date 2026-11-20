# Statement and definition changes

Running notes for the delivery statement. A headline theorem is
`deadlock_freedom`, `blocked_unblocks`, `blocked_chain`, `blocked_progress`,
`fair_delivered`, `cell_fresh`, and the other results printed from
`Deadlock.lean`.

The Lean definition of `Delivered` is unchanged. These are the constraints on
the edit, not the edit.

## What `Delivered` will say

A reliable message is either handled by its target, or the target began
shutting down or terminated before handling it. Mail that was enqueued and
not yet handled may be lost in that second case. The sender does not block
in either case. There is no failure return from the send.

This replaces the disjunct `∃ sub key, act = .kill sub key ∧ isMember host`.
The loss case stays. Deleting it is not allowed. Reliable delivery is not
promised for every target that was not shutting down at enqueue: the target
may terminate, or be killed, after the message is queued, and the queued mail
is then lost. That loss is per message. It is not "some member of the subtree
was killed", and it is not "the sender was killed".

A try-drop send and a superseding cell wake stay outside the obligation, as
they are now.

## The handled half

Delivery to a target that does not terminate is a property of the runtime,
once every stage step terminates. It is not a separate proof obligation and
not an axiom.

Once a stage has returned its next state, the runtime gives it the next
message, and the stage cannot refuse. The small lemma is that runtime rule,
already the shape of `receiveBulk`, `receivePrio`, and `deliver`: a step that
leaves the actor alive and idle with a non-empty mailbox enables the receive,
and `deliver` returns `some` for mail `LocalOk` accepted (`enabled_of_can`,
`deliver_msg`, `noncall_deliver`). That receive consumes the head.

Handled therefore reduces to the target eventually returning to receiving,
which `deadlock_freedom` gives through `idle_when_free`, plus step
termination. `Fair.bulk` and `Fair.prio` take the enabled receive. That is
the structure `box_mid_taken` already uses. No new definition, no new field
of `Assumptions`, no new axiom.

## Step termination

Named here so it is not reinvented as an axiom.

A stage step terminates. A non-terminating computation inside a stage is
excluded: it cannot be proved of the Rust, and the model already assumes
that steps and internal effects complete.

- One `apply` is one step. A program effect does not contain a diverging
  computation.
- `Eff.internal` reaches `awaitEffect` in that step.
- `finishWait` on `awaitEffect` is `some`. It does not consult
  `Env.effectDone`, which is unused (`effect_finish_enabled`).
- Fairness takes that `finish` (`not_stuck_effect`, `effect_resumes`).

`Assumptions` stays the single field `rust_refines`. Step termination is this
behaviour of the step relation, not a hypothesis to be added.

## Calls

`call_answered` promises `Reply` only when the callee stays live and not
shutting down until it replies. A callee that terminates or begins shutting
down after admission does not owe `Reply`. The same reduction applies: the
callee returns to the handler, and the runtime delivers. The three call
outcomes are unchanged. No proof may assume which one is taken.

## Supervision

This replaces the plan that a connection manager emits peer loss, and it
replaces `World.tombstone`. It is step C. The step relation above it is
unchanged until that step lands.

Termination is the pure-stage mechanisms, plus one.

- Voluntary. The stage's own `terminate`. The `awaitPeer` timeout is a
  typestate choice: the member's transition may terminate. Remove
  `peerTimeout`'s built-in atomic `killSubtree`.
- Supervision, upward and asynchronous. The tombstone is the message the
  parent supplies when it creates the child. When that child terminates, the
  parent receives it on `prio` and reacts in its own typestate transition,
  possibly terminating itself, so failure climbs. The slot is reserved on the
  parent's priority lane. The enqueue does not block and spends no bulk
  credit. The slot counts in `capPrio`. One message per child is the whole
  obligation.
- Aborted, downward and atomic. When a stage terminates, every descendant
  terminates in that same step, as pure-stage `terminate_stage` does
  (`crates/amaru-pure-stage/src/simulation/running/mod.rs`). Parked non-call
  senders are resumed. Parked calls finish via their deadline.
- `crashed` stays a fourth outcome. A crash instantly kills every actor. It
  is a terminal state the theorems need not say more about, where the proofs
  already treat it that way. Do not add proof burden for it. If keeping it
  costs significant proof work, stop and report.
- Remove the environment `.kill sub key` action, and `killWait` if nothing
  else uses it.
- Peer selection stays in the application typegraph and uses the same check.
- A dropped send stays dropped because death is permanent, shutting-down is
  monotone, and an id is not reused. `route` reads life and shutting-down.
  The drop rule does not add a second tombstone.
- `World.tombstone` and `plantTombstone` are removed. The field is not the
  per-child message.

## Work plan

The round, in order. This note does not change the step relation. `Delivered`
stays as it is until the kill step changes.

A. Members of one subtree may send and call each other. A call to a permanent
core stays disabled: `Delivered` loses a message when its target shuts down
or terminates, and a permanent core does not, so a dropped call to it would
not be a delivery. A lone terminable still may not send or call. Ingress
into a member is allowed. Disjointness of that mail is a proof obligation.
The mux, handler, and connection witness passes, and so does the round's
send and call pair.

B. A call carries a duration. `awaitReply` resumes with a reply, not
admitted, or timed out. The caller's continuation is checked on every
branch, and no proof assumes which branch runs. The timeout stays enabled
from `awaitReply`, including a call that is still parked. A call id stops a
late reply from resuming a newer wait. `call_answered` promises a reply only
while the callee stays live and not shutting down.

C. Termination follows Supervision, and not before. Voluntary `terminate`
replaces `peerTimeout`'s built-in `killSubtree`. The upward message is the
per-child tombstone the parent supplied at spawn, delivered on `prio`, and
answered in the parent's own transition. The downward abort ends descendants
in that same step. `crashed` stays a whole-system terminal state; add no
proof burden, and stop if keeping it costs a significant proof. The
environment `.kill sub key` action and `killWait` go away. `World.tombstone`
and `plantTombstone` are removed here. `route` reads life and shutting-down.
No theorem is weakened. A statement change is justified in the commit body
and in this note. A weakening is a blocker and is not committed.

D. An untimed peer wait needs a live, armed timeout killer at its key. A
static role test is not enough. `finish` on the success path does not resume
an untimed wait.

## `CallTagInv.awaiting`

A caller in `awaitReply` is in one of four states. The first three are the
live callee: the call is in its mailbox, the handler owes the reply, or the
reply is the next effect. The fourth is the callee already dead, the caller
still alive, and nobody owing or holding that call id. There is no
shutting-down life yet; when that phase exists it joins this disjunct.

This is the pure-stage timeout. A caller waiting on a dead callee is not a
stuck call: the deadline stays enabled and fairness ends it as `TimedOut`,
or as `NotAdmitted` when the call was never admitted. `call_answered` is
unchanged. It is `Reply` while the callee stays alive and is not shutting
down, and `NotAdmitted` or `TimedOut` otherwise. The fourth disjunct is how
the dead case is proved: the timeout is enabled, and fairness fires it.
`abort_await_not_tag` stays as a regression against the old three-disjunct
formula, which does not hold after the abort. Deadlock freedom, `Delivered`,
and `call_answered` are not weakened. The invariant covers one more
reachable state that the approved semantics already produces.

## `replyTo` scrub

A deadline of an admitted call clears `replyTo` on the callee when that
callee still owes the call. The effect list and the typestate target stay.
A late reply is ignored. `step_keeps_run` and `step_keeps_quiet` record that
scrub and nothing else. The same fact is what `run_prefix`, `run_holds`,
`quiet_prefix`, `effect_resumes`, and `peer_resumes` carry: the continuation
afterwards has the same effects and the same typestate target. While the
caller named by `replyTo` stays in `awaitReply`, the scrub does not happen,
so a reply that is still owed runs as that reply (`run_holds_owed`).

## Not a weakening

`fair_delivered` keeps a loss disjunct. The companion fact that a target
which stays alive and not shutting down eventually handles the message is
the handled half above. It is not stated by allowing loss in every case, and
it is not a second theorem with its own machinery.

## Later

Not this round. Cells are not a pure-stage primitive today, so the model
deviates from current pure-stage. The planned runtime encoding:

- A cell write is an effect whose resource holds a map keyed by reader stage
  name, one cell per reader. Each cell holds a `(counter, value)` pair,
  ordered by the counter, which removes the max-only limit, plus a
  wake-pending flag.
- A write atomically stores the value and, if no wake is pending, sets the
  flag and enqueues one regular wake message.
- The reader's handler atomically reads and clears the flag. Atomicity is
  guaranteed by the runtime.

The model change to make then: replace the uncharged priority wake with a
regular message that uses one reserved mailbox slot per cell label and
reader. Count that slot in the occupancy bound, and keep the wake enqueue
non-blocking because the slot is reserved. `cell`, `tryWake`, and `CellFresh`
stay as they are until that change.
