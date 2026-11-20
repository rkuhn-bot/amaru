# Deadlock freedom, delivery, and a quiet fair run

This note is the statement a reviewer can check against the Lean development.
Nothing in the development uses `sorry` or `admit`.

## What is proved

Three statements lead.

`blocked_unblocks` is a finite execution along the blocked actor's own wait
chain, when that actor is not a pure untimed peer end. It ends with that
actor not `Blocked`.

`fair_delivered` is liveness for a `Fair` run of a `GraphOk` and `LocalOk`
implementation that has not crashed. The headline is deadlock-free or
crashed: a fair run is not stuck, or a step has already crashed the roster
and no further action is enabled.

## Deadlock-free or crashed

A fair run is exactly a non-crashing infinite run. Once `crashWorld` sets
`World.crashed`, every action is disabled, including stutter, ingress, and
spawn, and the run stops. The claim is deadlock-free or crashed. `LocalOk`
does not remove the crash. Under `GraphOk` and `LocalOk` the steps that
still crash the roster are:

- `terminate` of a permanent core
- a self-schedule that does not fit the priority lane
- a cell wake that does not fit the priority lane
- `enqueueTombstone` when the parent is not alive, or when the tombstone
  label is empty
- the `terminate` fall-through, a stage the shutdown cases do not classify
- a missing template at a step that looks the template up and crashes

The last three are obligations, not a proved absence. Under `GraphOk` and
`LocalOk` a tombstone is enqueued only for a child whose supervisor is
alive and whose label is the template's non-empty tombstone; a `LocalOk`
program's `terminate` meets one of the classified shutdown cases; and a
step looks up a template the description declares. This note does not
prove those sites unreachable. A design that reaches one of them crashes.

`prioSized` is part of `LocalOk`. Per parent it is one tombstone per child
slot — a pool's `slots`, one key per root population for a root a core
spawns, one child for a per-peer parent — plus that parent's self-schedule
and cell-wake senders. The sender term is the larger of the maximum along
one program path and the number of distinct labels: a branch's outcomes are
not added, and the lane holds each label once across later transitions.
`LocalOk` also rejects a re-spawn that can run while that slot's tombstone
is still queued. The semantics makes the same spawn a no-op, for a core pool
and for a per-peer parent, and a root spawn into such a slot is not enabled.
A slot that is still shutting down is occupied too. The tombstone is queued
at the seal, so the predecessor is dead before the parent is notified.
`no_tombstone_overflow` says that under `GraphOk`, `LocalOk`, and
`prioSized`, `offerPrio` does not take its crash branch for that tombstone.
Tombstone overflow is not a crash source under the checks. A self-schedule
or a cell wake that does not fit still crashes, matching pure-stage's panic.
`LocalOk`'s spawn scope does rule out the crash from `Eff.spawn` of a
template its parent is not allowed to birth. `Delivered` says every reliable message in
the bulk box, the parked list, or the priority lane is later the head
consumed by `recvBulk` or `recvPrio`, matched by the id the storing actor
assigned when it accepted the message, or the target had begun shutting down
or had terminated while the message was still queued. A try-drop send and a
superseding cell wake are not obligations. An admitted call leaves
`awaitReply`.
`Assumptions` is only `rust_refines`.

The parked-call reserve is the ingress gate, not `LocalOk`. `tokenHold`
counts the call's own message once, through the charge taken when the call
was parked, and counts the `TimedOut` continuation's future sends on top.
`receiveIngress` refuses a message that would leave `tokens` short of that
reserve. A Rust ingress adapter that checked only mailbox room would accept
a self-park the gate refuses. Keeping that gate is an obligation on the
exporter and the runtime, beside `rust_refines`.

The handled half is not a separate obligation. Once a stage has returned its
next state, the runtime gives it the next message and the stage cannot refuse.
A world in which the actor is alive and idle with a non-empty mailbox enables
`recvBulk` or `recvPrio`, and `deliver` returns `some` for mail the checker
accepted (`enabled_of_can`, `deliver_msg`, `noncall_deliver`). That receive
consumes the head. So a reliable message whose target stays alive is delivered
once deadlock freedom has brought the target back to receiving
(`idle_when_free`) and the stage's own step has terminated. `Fair.bulk` and
`Fair.prio` are what take the enabled receive. Nothing here is an axiom.
The loss half stays: mail still queued when the target shuts down or
terminates may be dropped, and the sender still does not block. The loss is
that the target had begun shutting down or had terminated while the message
was still queued. It is not a subtree kill. It does not delete the loss
case, and it does not promise delivery for every target that was not
shutting down at the moment of enqueue. The proof text in `Deliver.lean`
is not yet restated against this wording.

`loss_fair` and `loss_not_delivered` are the run without that check. A
terminable actor accepts a reliable message and then executes `terminate`,
which clears the mailbox. The schedule ends in stutter and is `Fair`, and the
message is never received.

`demo_fair` is one quiet run of a checked description. It parks a producer on
a full sink, admits a call and waits for the reply, wakes a reader from a cell,
and then stutters. The trace is kernel-checked with `decide`. Fairness does not
ask the environment to keep injecting: `forced` is false for `ingress`,
`spawn`, and `stutter`, and `stutter` is enabled only when no roster actor can
`recv`, `exec`, or `finish`.

```lean
theorem blocked_unblocks (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I)
    (hA : Assumptions I) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (hB : Blocked w id) (hnotP : ¬ PurePeerEnd I.desc w id) :
    ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
      Reachable I N w' ∧ ¬ Blocked w' id

theorem fair_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc)
    (hA : Assumptions I) {N : Nat} (ρ : Run I N) (hF : Fair ρ) : Delivered ρ

theorem loss_fair : Fair lossRun
theorem loss_not_delivered : ¬ Delivered lossRun

theorem demo_fair : Fair demoRun
theorem demo_parked : demoCode 4 prodId = 1
theorem demo_awaiting : demoCode 9 callerId = 2
theorem demo_answered : demoCode 11 callerId = 3
theorem demo_woken :
    ((replayCfg demoImpl demoActs 15).st readerId).prio = [] ∧
      ((replayCfg demoImpl demoActs 14).st readerId).prio ≠ []
```

`park_graph_ok`, `park_local_ok`, `park_reachable`, and `park_unblocks` are the
same park/resume world, checked with `decide`. `demo_graph_ok` and
`demo_local_ok` are the quiet run's checks.

```lean
def OnChain (w : World) (root : InstId) (act : Action) : Prop

theorem blocked_chain ... :
    ∃ acts w', ChainRun I id w acts ∧ runFrom I (some w) acts = some w' ∧
      Reachable I N w' ∧
      (¬ Blocked w' id ∨ ∃ s k, InChain w' id s ∧
        (w'.st s).phase = .awaitPeer k ∧ peerUntimed I.desc s = true ∧
        peerFinishable I.desc s = false)
```

`OnChain` holds only for `recvBulk`, `recvPrio`, `exec`, and `finish` whose
subject is `id` or is reached by following `.parked` / `.awaitReply` targets.
Ingress and spawn are never on the chain. `ChainRun` is a list of such steps,
each on the chain in the world where it is taken. `InChain` is that wait relation.

`Blocked` is a live actor in `.parked` (a blocking send or a parked call),
`.awaitReply`, `.awaitEffect`, or `.awaitPeer`. The proof is strong induction
on residual height, and inside one height on a debt of parked index or call
position plus the partner's remaining program (`work`). An `awaitEffect` is
one `finish` on the chain. A finishable `awaitPeer` is the same step: its own
timeout, or a timed peer in the cohort. A send or call waits on a live
partner of strictly smaller height (`park_below`, `call_below`, `reply_below`).
The partner is drained by `recvBulk`, `exec`, and `finish` on the chain, or the
induction hypothesis unblocks the partner first.

An untimed external peer wait is a legitimate end of a wait chain.
`PurePeerEnd` is an `awaitPeer` whose `peerFinishable` is false: the template
is `untimedPeer` and `timedCohortEnds` is false, so `finishWait` returns
`none`. `blocked_chain` then takes the empty run and the second disjunct, at
`InChain.refl`, with `peerUntimed = true` and `peerFinishable = false`.
`blocked_unblocks` is the other case. It assumes `¬ PurePeerEnd` and ends
with `¬ Blocked`.

That end must not sit inside a chain another actor depends on for liveness,
unless some timed wait in the chain can end it. `peerFails` is that check,
and `GraphOk.peers` is `peerFails D = []`:

- `pureTermFails`: a pure untimed template (`templatePure`) is terminable. A
  permanent mailbox would stall with the peer. `permanent_finishable` is why
  `finish` stays enabled on a non-terminable actor.
- `cellPureFails`: a pure untimed template is not a cell reader. A wake would
  sit on the priority lane while `finish` is disabled.
- `interiorFails`: a blocking send or a call onto an untimed template is
  rejected unless `timedCohortEnds`. The cohort is every template when
  compatibility is `all`, the templates named together in an explicit allowed
  pair, or the roles of a shared compat group. `hasTimedPeer` is a template
  that is not `untimedPeer` and has a `peer` edge; `finish` is that timeout.
  A mini-protocol timeout that can end the chain is this cut. When it is
  present, `peerFinishable` is true, so `finish` is enabled on the untimed
  waiter and the chain continues. `target_finishable` is that fact for a
  reachable park or `awaitReply`.

`blocked_progress` is the one-step form: an enabled action is `OnChain`, or
the actor is a `PurePeerEnd`. `fin_exec_no_blocked` is the total-stall
corollary. A stopped finite execution's only live blocked actor is a pure
untimed peer end, because any other blocked actor would have an enabled chain
step. It does not by itself rule out a partial deadlock in a world where some
unrelated actor can still step; `blocked_unblocks` does, for an actor that is
not a pure untimed end.

`park_reachable` and `park_unblocks` are one `GraphOk` and `LocalOk` world in
which the producer is parked and the next `recvBulk` leaves it idle.
`Counter.lean` shows an ingress into an independent clock is enabled in that
world and is not `OnChain`, and that a mutual A↔B park is rejected by `checkBool`.

A live reader with a label still on its priority lane likewise has an enabled
step. If the reader is idle, that step is `recvPrio`, and delivery runs
`readCells`. `fin_exec_no_wake` says a stopped execution is not still holding
that wake.

```lean
theorem cell_wake_enabled ... (hlive) (hhas : hasLabel prio label) :
    ∃ act, Enabled I w act ∧ ((w.st r).phase = .idle → act = .recvPrio r)

theorem fin_exec_no_wake ... (hlive) (hhas) : False
```

The infinite-run theorems stay as corollaries of fairness:

```lean
theorem deadlock_freedom (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc)
    (hA : Assumptions I) {N : Nat} (ρ : Run I N) (hF : Fair ρ) : ¬ Deadlock ρ

theorem cell_fresh (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc)
    (hA : Assumptions I) {N : Nat} (ρ : Run I N) (hF : Fair ρ) : CellFresh ρ
```

A fair reachable run has no actor blocked forever on a blocking send, a call
reply, an internal effect, or a timed peer wait. The proof is strong
induction on residual height (`below_idle`), then `never_stuck`. `below_idle`
settles a low actor at `Idle`, or at a pure untimed peer (`Settled`). An
effect or a finishable peer wait is ended by `finish`, which the step
relation enables without reading `Env`. A pure untimed peer may stay; it is
not a `Deadlock`. An untimed template whose cohort has a timed peer is
finishable, so fairness ends that wait as well. `Deadlock` still does not
count it, because the peer clause asks `peerUntimed = false`. `Assumptions`
is only `rust_refines`. A blocking send
or a parked call waits on a strictly lower actor. An `awaitReply` cannot last:
while the caller stays there it cannot mint a new `callFrom`, so `CallTagInv`
keeps the callee in `handlerOwes` or `replyPending`, and that phase is not
`idle`. `forced` is false for `spawn`, `ingress`, and `stutter`, so fairness does not
require the environment to keep injecting. A run that takes a finite schedule
and then stutters is fair once no roster actor can `recv`, `exec`, or
`finish`, because an off-roster actor stays idle and not alive
(`off_idle_reachable`). `cell_fresh`
is the liveness form of the same cell fact: along a fair infinite run the
queued wake is eventually observed. `fin_exec_no_wake` is the safety form.

`cell_fresh` is the cell half of the target conjunction, for the `CellFresh`
below. After a declared cell label strictly rises, every reader instance of
that template which is already alive and stays alive eventually has `observed`
at least the post-write value. The rise is an `exec` of `.cell`. If the bit
was clean, that step wakes every live reader; if it was already dirty, the
label has been on the lane since the last clean-to-dirty write, because a
later read or a killing `terminate` would have cleared the bit. `Fair.prio`
then takes `recvPrio`, and that delivery's `readCells` records the current
value. Cell values only rise, so the recorded value is at least the written
one.

`deadlock_freedom` does not use `Fair.prio`. `recvBulk` stays enabled when
`recvPrio` is enabled; the step relation is unchanged.

## Why `CellFresh` is stated this way

An earlier statement quantified over every reader name and every label a
program might write, and asked for a later `recvBulk`, `recvPrio`, or `exec`.
Two fair runs fail that statement. Both are closed by the statement and the
checker, not by a change to the step relation.

**No live reader.** Let `R` be `perPeer`, or a `one` template that has already
taken a killing `terminate`. Let `W` be a non-terminable `one` whose program
contains `.cell R L 1`. `W` runs that effect. The cell goes from 0 to 1 and
`dirty` becomes true. `readersOf` is empty, so `wakeReaders` enqueues nothing.
No instance of `R` is ever alive to take `recvPrio`. `Fair.prio` holds because
`recvPrio` of a reader that does not exist is never enabled. A dead or
never-spawned reader has nothing to be fresh about, so `CellFresh` quantifies
only over instances that are alive at the write and stay alive.

**Undeclared label.** `readCells` stores `observed` only for `cellLabels`, the
labels of edges with `effect = cell` and `dst` equal to the reader's template.
A program could write some other label, and a later `recvPrio` of a live
reader would leave that `observed` entry at 0. `effectsOk` now rejects a
`.cell R L _` effect unless it is a non-blocking cell edge into `R` with label
`L`. `GraphOk.struct` includes `cellEffectFails`: a listed `cellEffects` entry
with no such edge is not `GraphOk`. `examples/undeclared-cell.json` fails with

```
fail: cell effect writer/idle -[Ghost]-> reader is not a declared cell edge
```

`CellFresh` assumes `label ∈ cellLabels`, which is what that check forces of
every program `LocalOk` accepts.

## Definitions the statement uses

### `Run`

```lean
structure Run (I : Impl) (N : Nat) where
  cfg : Nat → World
  act : Nat → Action
  startN : (cfg 0).N = N
  start : cfg 0 = initWorld I N
  valid : ∀ i, apply I (act i) (cfg i) = some (cfg (i + 1))
```

### `Fair`

```lean
structure Fair {I : Impl} {N : Nat} (ρ : Run I N) : Prop where
  weak : ∀ (a : Action) (i : Nat), forced a = true →
    (∀ j, i ≤ j → Enabled I (ρ.cfg j) a) → ∃ j, i ≤ j ∧ ρ.act j = a
  bulk : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ Enabled I (ρ.cfg j) (.recvBulk s)) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)
  prio : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ Enabled I (ρ.cfg j) (.recvPrio s)) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvPrio s)
```

`forced` is false for `.spawn`, `.ingress`, and `.stutter`, and true for
`recvBulk`, `recvPrio`, `exec`, and `finish`. `stutter` applies only when
`runtimeBusy` is false: no roster actor has `recv`, `exec`, or `finish`.
Ingress may still be enabled; taking it is the environment's choice, and a
fair run does not have to. `Enabled` is
`apply ≠ none`. `bulk` is stated on `Enabled`, not on `CanReceive`: a call at
the head can make the mailbox look ready while `deliver` refuses it.
`uniqueKeys` and `callTotal` are what turn readiness into `Enabled`. `prio`
is strong fairness: enabled infinitely often implies taken infinitely often.
It is the runtime draining a priority wake rather than leaving it behind the
bulk mailbox. `recvBulk` is not disabled by a nonempty priority lane.

### `Deadlock`

```lean
def Stuck {I : Impl} {N : Nat} (ρ : Run I N) (s : InstId) (i : Nat) : Prop :=
  SameWait ((ρ.cfg i).st s) ((ρ.cfg i).st s) ∧
    ∀ j, i ≤ j → SameWait ((ρ.cfg i).st s) ((ρ.cfg j).st s)

def Deadlock {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∃ s i, Stuck ρ s i ∧
    match waitKind ((ρ.cfg i).st s) with
    | some (.blockingSend _) => True
    | some (.callReply _) => True
    | some .effect => True
    | some .peer => peerUntimed I.desc s = false
    | _ => False
```

An effect or a timed peer wait is ended by `finish`, which the step relation
enables without reading `Env`. An untimed peer wait is not a deadlock. When
`timedCohortEnds` holds, `peerFinishable` is true and `finish` is enabled on
that waiter too. A pure untimed wait (`peerFinishable = false`) leaves
`finish` disabled, and the peer may stay silent. That is a chain end, and
`peerFails` is what keeps it from being interior to another actor's chain.

### `CellFresh`

```lean
def CellFresh {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∀ i dst label,
    label ∈ cellLabels I.desc dst →
    ((ρ.cfg i).cell dst label).value < ((ρ.cfg (i + 1)).cell dst label).value →
    ∀ r, tname r = dst →
      (∀ t, i ≤ t → ((ρ.cfg t).st r).life = .alive) →
      ∃ j, i < j ∧
        ((ρ.cfg (i + 1)).cell dst label).value ≤ ((ρ.cfg j).observed r label)
```

`cellLabels` is the labels of edges with `effect = cell` and `dst` equal to
the reader template. A cell write sets `value := max(old, payload)` and
`dirty := true`. If `dirty` was clear it upserts one priority wake per live
reader (`wakeReaders`). `readCells` clears `dirty` and stores the value in
`observed`. It runs from `deliver` (hence `recvBulk` and `recvPrio`), from
spawn, and from a killing `terminate`. The witness index is a world after the
reading step, so `observed` there already holds the value. An `exec` that is
not `terminate` does not call `readCells`.

### `GraphOk`

```lean
structure GraphOk (D : Description) : Prop where
  struct : structLines D = []
  fresh : freshFails D = []
  priority : priorityFails D = []
  replies : replyFails D = []
  lifecycle : callTermFails D = []
  peers : peerFails D = []
  acyclic : Acyclic (edgeBool (residualEdges D))
  ranked : ∃ hs : List (Node × Nat), heightsOkB (residualEdges D) hs = true
  credit : overflowFails D = []
```

`checkBool D = true` implies `GraphOk D` (`checkBool_sound`).

### `LocalOk`

```lean
def LocalOk (I : Impl) : Prop := localOkB I = true
```

`localOkB` is the conjunction of: every transition passes `transitionOk`,
`callTotal`, `targetsAll`, `occShape`, `dstClosed`, `prioOk`,
`compatFails I.desc = []`, and `stepsCoverB`. A terminable template's
programs contain no bulk `send`, `trySend`, or `call` (`noBulkSend` inside
`transitionOk`). `prioOk` bounds the declared priority labels by
`priorityBound`. Inside `transitionOk`, `effectsOk` requires every
`.cell R L _` effect to be a non-blocking cell edge from the transition's
template and target state into `R` with label `L`. The same shape is
`cellEffectFails` on a description's `cellEffects` list, and that list is part
of `structLines`, so `GraphOk.struct` rejects an undeclared cell write.

### `Assumptions`

```lean
structure Assumptions (I : Impl) : Prop where
  rust_refines :
    ∀ tr ∈ I.transitions, ∃ tr' ∈ I.transitions,
      tr'.template = tr.template ∧ tr'.fromState = tr.fromState ∧
      tr'.label = tr.label ∧ tr'.program = tr.program ∧
      tr'.toState = tr.toState ∧ tr'.acceptsCall = tr.acceptsCall
```

This is not a theorem about Rust. `rust_refines` is the exporter obligation.
In this development the transition list is the model, so the field is the
identity on that list. An internal effect and a timed peer wait complete as
`finish` steps. An untimed peer wait completes the same way when
`timedCohortEnds` holds. A pure untimed peer wait does not.

**Step termination.** A stage step terminates. A computation inside a stage
that does not return is excluded, because it cannot be proved of the Rust
program, and the model already treats every effect as one completing step.
`Eff.internal` moves the actor to `awaitEffect` in that step. `finishWait` on
`awaitEffect` is `some` and does not read `Env.effectDone`
(`effect_finish_enabled`). `Env.effectDone` is unused. Fairness then takes
`finish` (`not_stuck_effect`, `effect_resumes`), and the continuation runs.
`deadlock_freedom` is what says the actor is not stuck there, so it returns
to receiving. This is not a field of `Assumptions` and not an axiom. Delivery
to a target that does not terminate is the runtime's, from this assumption
plus that return to receiving. The small lemma is the runtime rule above:
returning to receiving with mail handles the head next, and the stage cannot
refuse it.

## Restrictions that are still in force

**BulkFree for a terminable template.** `BulkFree` says a terminable actor's
carried continuation satisfies `noBulkSend`. `LocalOk` checks the same thing
on every listed program of a terminable template. A terminable actor may
terminate while a shared stage still holds its earlier sends; it may not
bulk-send as part of the program it is running. This is narrower than a rule
that would forbid every send by a terminable template.

**callTermFails.** `GraphOk.lifecycle` is `callTermFails D = []`: no call edge
targets a terminable template. A killing `terminate` is refused while a parked
call is present. The two together are why a callee that is owed a reply cannot
be the actor that exits.

**Compatibility is sufficient, not necessary.** The group list is untrusted.
`compatFails = []` checks that each group is well-formed, contains the initial
tuple, and is closed under the listed typestate steps. Failure means "not
provable with this relation", not "the system deadlocks". `compatibility: all`
is the universal relation. `compatibility: explicit` is rejected; a pairwise
list is not an invariance check. Roles in a group are multiplicity `one` and
not terminable. In-place restart is not a step of this semantics.

The dead-instance lift (a dead actor may still be owed a message) is not in
this development.

## Still open

- **N4/N5.** A per-peer subtree is killed in one step, and that step preserves
  the step, occupancy, and call-tag invariants. A call may name a terminable
  role inside the subtree and is rejected outside it. `route` uses the sender's
  index. `mux_kill` is a run from the initial world; `mux_cross_fails` is the
  rejected call. The tombstone is a world field. `spawn` still allocates one
  role at a time, so a shared key is the index those roles hold, not one
  allocation of the whole tree.
- **F7.** Peer waits are not given their own timeout. A timed peer ends by the
  `finish` step; there is no clock beside that step.
- **F10.** Under `LocalOk` and `GraphOk`, `fair_delivered` shows each reliable
  message, identified by the id of the actor that stored it, is consumed by
  `recvBulk` or `recvPrio`. `reliable_free_reachable` keeps a terminable mailbox
  free of reliable mail, so a killing `terminate` cannot discard one.
  `loss_not_delivered` is that discard on a description the checker does not
  accept: the run is `Fair` and the message is never received.
- **F11.** `CellFlags` is not checked against the set of writers. A cell edge
  is accepted when the flag word passes `cellFails`, not when the program
  effects are shown to be the only writers.

## Axioms

From `lake build Deadlock` (`#print axioms`):

```
'Deadlock.below_idle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.deadlock_freedom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.cell_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.fair_delivered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.loss_fair' depends on axioms: [propext, Quot.sound]
'Deadlock.loss_not_delivered' depends on axioms: [propext, Quot.sound]
'Deadlock.demo_fair' depends on axioms: [propext, Quot.sound]
'Deadlock.park_reachable' depends on axioms: [propext]
'Deadlock.park_unblocks' depends on axioms: [propext]
```

`park_graph_ok`, `park_local_ok`, `park_reachable`, `park_unblocks`, and the
`demo_*` Bool facts (`demo_graph`, `demo_parked`, `demo_awaiting`,
`demo_answered`, `demo_woken`, `demo_quiet`) are `decide`. They do not use
`native_decide` (`Lean.ofReduceBool`).

`propext`, `Classical.choice`, and `Quot.sound` are the standard Lean kernel
axioms used by `Classical.em` and by `simp` of definitions. There is no
domain axiom.
