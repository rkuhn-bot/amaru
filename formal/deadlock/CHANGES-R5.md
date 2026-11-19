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
replaces `World.tombstone`.

A tombstone is the pure-stage supervision message. It is not an Ouroboros
peer event.

- A parent declares the message when it spawns a supervised child.
- The parent receives it on `prio` once the child has terminated, by `kill`
  or by the child's own `terminate`.
- One message per child is the whole obligation.
- The slot is reserved on the parent's priority lane. The enqueue does not
  block and spends no bulk credit. The slot counts in `capPrio`.
- The kill climbs because each parent answers that message with its own
  typestate transition. A parent may itself terminate.
- Peer selection stays in the application typegraph and uses the same check.
- A dropped send stays dropped because death is permanent, shutting-down is
  monotone, and an id is not reused. `route` reads life and shutting-down.
  The drop rule does not add a second tombstone.
- `World.tombstone` and `plantTombstone` are removed. The field is not this
  message.

## Work plan

The round, in order. This note does not change the step relation. `Delivered`
stays as it is until the kill step changes.

A. Members of one subtree may send and call each other, and may call a
permanent core. A lone terminable still may not. Ingress into a member is
allowed. Disjointness of that mail is a proof obligation. The mux, handler,
and connection witness passes, and so does the round's send and call pair.

B. A call carries a duration. `awaitReply` resumes with a reply, not
admitted, or timed out. The caller's continuation is checked on every
branch, and no proof assumes which branch runs. The timeout stays enabled
from `awaitReply`, including a call that is still parked. A call id stops a
late reply from resuming a newer wait. `call_answered` promises a reply only
while the callee stays live and not shutting down.

C. The kill is no longer one step. Follow Supervision: one declared priority
tombstone per child, parents climb by their own transition, and peer
selection stays out of the model. `World.tombstone` and `plantTombstone` are
removed here. `route` reads life and shutting-down.

D. An untimed peer wait needs a live, armed timeout killer at its key. A
static role test is not enough. `finish` on the success path does not resume
an untimed wait.

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
