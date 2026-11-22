# Deadlock freedom, delivery, and a quiet fair run

This note is the statement a reviewer can check against the Lean development.
Nothing in the development uses `sorry` or `admit`.

## What is proved

`Deadlock.Step` builds. `Inv` is `SemInv`, `MailInv`, `OpenSlots`,
`OutcomeInv`, and `ParentForest`: the parent relation of a reachable world
is well-founded, an actor off the roster has no parent, and every recorded
parent is on the roster. The modules past `Step` (`Projects`, `CallTag`,
`Occ`, `Inv2`, `Rank`, `Progress`, `Chain`, `Deliver`, `FairRun`,
`Theorem`) are not claimed by this paragraph. `no_tombstone_overflow` is
not part of that chain. It is a theorem of
`Deadlock.Tomb`: a reachable world under `GraphOk` and `LocalOk` does not
overflow a live parent's lane. `GraphOk` rejects a supervised template whose
tombstone is empty, and a recorded parent on a reachable world is the
supervisor that template names, so the label is nonempty.
`self_schedule_fits` and `cell_wake_fits` are the same lane for a reachable
self-schedule and for a cell wake of one of its readers: the label is already
queued, or the lane is below `capPrio`. `hold_reach` is
`Hold` for every reachable world under `GraphOk`. `Side` carries the key counters, roster
uniqueness, and the empty off-roster lane from the initial world through
every enabled step. `LocalOk` supplies `prioSized`.

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
still crash a world a run can reach are:

- `terminate` of a core, every multiplicity-one template
- the `terminate` fall-through, a per-peer the shutdown cases do not classify
- a missing template at a step that looks the template up and crashes

Those three are obligations, not a proved absence. A `LocalOk` program on a
per-peer `terminate`s only when that template is terminable, and that step is
one of the classified shutdowns. A core may `terminate`, and that step is the
crash above. It is an acceptable end of the run. A step is expected to look
up a template the description declares. This note does not prove the
fall-through or the missing template unreachable. A design that reaches one
of them crashes.

A seal whose recorded parent is dead drops the tombstone:
pure-stage has already discarded that queue in `terminate_stage`. An empty
label on a live parent is not a reachable seal under `GraphOk`. A reachable
self-schedule and a reachable cell wake fit the lane, so neither overflows
it.

`prioSized` is part of `LocalOk`. Per parent it is one tombstone per child
slot — a pool's `slots`, one key per root population for a root a core
spawns, one child for a per-peer parent — plus that parent's self-schedule
and cell-wake senders. The sender term is the larger of the maximum along
one program path and the number of distinct labels: a branch's outcomes are
not added, and the lane holds each label once across later transitions.
`LocalOk` also rejects a re-spawn that can run while that slot's tombstone
is still queued. The semantics makes the same spawn a no-op, for a core pool
and for a per-peer parent, while the slot is occupied or that tombstone is
still queued. The tombstone is queued at the seal and is not receivable
while program mail from the dead stage, or from a descendant sealed with it,
sits in a live receiver's bulk or priority queue. `receivePrio` skips that
tombstone and takes the first priority message that is not waiting, so a
waiting tombstone is not a head that stalls the lane. It stays in the lane,
and `no_tombstone_overflow` still counts it. The handler that consumes it
therefore runs with that mail already gone, and the spawn is not refused
for mail. `slotRespawnBlocked` does not consult `slotMailHeld`.
`receivePrio_tombstone_drained` is that fact for the message `receivePrio`
removes. The world after the receive is the delivery of that message, and a
tombstone in that position was not waiting. `child_sub_respawn_enabled` and `pool_sub_respawn_enabled` are
the birth after the receivers have taken the mail. `child_sub_refused` and
`pool_sub_refused` do not survive, and they are not a closure of that class.
A scheduler root takes a fresh key. A core-supervised root occupies one of
the `N` population slots while it is alive, or its tombstone
is still queued. `rootOutstanding` is that count. The tombstone cannot be
received while the root's in-flight mail remains, so the slot stays occupied
through the drain without a separate mail term. An unsupervised root has no
tombstone. `loneOutstanding` counts it while it is alive, or while
`slotMailHeld` says a surviving receiver still holds subtree mail — bulk
box, priority lane, or a parked send, from any member at that key, on a host
that is alive and is not sealed with the sender. The seal clears the root's
own mailbox in the same step, so a dead root holds the slot only through mail
a surviving receiver still has.
`may_root_parts` and `may_free_parts` say an enabled spawn has that count
strictly below `N`. The restart check in `LocalOk` is still only the
tombstone, because the mail is not a typestate fact. The one attempt it
allows now runs when the in-flight set is empty. `GraphOk` does not read
mailboxes. Deadlock freedom does not need that drain. A waiting tombstone
is skipped, so it blocks nobody. `fair_delivered` does. A tombstone is a
reliable priority message, and the obligation is that every such message is
later taken or its receiver has halted while the message is still queued.
The drain that makes the tombstone receivable is the same fair receive: the
in-flight set is finite, the dead senders cannot add to it, and a fair run
dequeues each message or the receiver leaves `alive`. Mail already at a
host that is not alive is the second case, and it is not in `mailInFlight`.
That argument is not yet a theorem of `FairRun`.
pure-stage delays the tombstone until receivers report that consumption.
The scheduler, for an unsupervised root, holds the population slot until
every surviving receiver has drained that subtree. `outlive_refused` is E4:
two unsupervised roots fill `N = 2` while their mail sits on the cores, and
the third spawn is not enabled. `outlive_stuck` is that the old run is
refused.

A slot is occupied while its actor is alive. The tombstone is queued in the
same step as the seal, so the predecessor is dead before the parent is notified.
`no_tombstone_overflow` is that account for a reachable world. Under
`GraphOk` and `LocalOk`, sealing a child does not fill a
live parent's lane. The offer stays
strictly below `capPrio`. `LocalOk` supplies `prioSized`, through
`tmb_prio_sized`, and `hold_reach` supplies `Hold`. The run that overflowed
one lane reused a subtree key and delivered both tombstones to the older
generation. A birth now takes a fresh key, the child records the parent
incarnation, and a seal drops the tombstone when that incarnation is not
alive. `Deadlock/Counterexample.lean` runs the schedule that matches that
rule: two roots, two keys, one tombstone on each live lane. A reachable
self-schedule or cell wake fits the same lane: the label is already queued,
or there is room under `capPrio`. An undeclared label is outside that claim.
`LocalOk`'s spawn scope does rule out the crash from `Eff.spawn` of a
template its parent is not allowed to birth. `Delivered` says every reliable message in
the bulk box, the parked list, or the priority lane is later the head
consumed by `recvBulk` or `recvPrio`, matched by the id the storing actor
assigned when it accepted the message, or the target had terminated while
the message was still queued. A try-drop send and a
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
The loss half stays: mail still queued when the target terminates may be
dropped, and the sender still does not block. The loss is that the target
had terminated while the message was still queued. It is not a subtree kill.
It does not delete the loss case, and it does not promise delivery for every
target that was alive at the moment of enqueue. The proof text in `Deliver.lean`
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

- `pureTermFails`: a pure untimed per-peer (`templatePure`) is terminable. A
  permanent mailbox would stall with the peer. A core is not that peer.
  `subtreeEntry` rejects a pure core, and a core may not set `terminable`.
  `permanent_finishable` is why `finish` stays enabled on a non-terminable actor.
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

**No live reader.** Let `R` be `perPeer` and already terminated, or never
spawned. Let `W` be a core whose program contains `.cell R L 1`. `W` runs
that effect. The cell goes from 0 to 1 and `dirty` becomes true. `readersOf`
is empty, so `wakeReaders` enqueues nothing. No instance of `R` is alive to
take `recvPrio`. `Fair.prio` holds because `recvPrio` of a reader that does
not exist is never enabled. A core reader that `terminate`s crashes the node,
so there is no later write in that run. A dead or never-spawned reader has
nothing to be fresh about, so `CellFresh` quantifies only over instances that
are alive at the write and stay alive.

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
    | some .peer => True
    | _ => False
```

An effect or a peer wait is ended by `finish`. The step relation enables it
on every `awaitPeer` and does not read `Env`. `peerFinishable` is true for
every actor, including one whose template sets `untimedPeer`, so a peer wait
that stays stuck is a deadlock. Fairness taking `finish` is what rules that
out. `peerUntimed` is only the template flag. `peerFails` still rejects a
pure untimed per-peer that is not terminable, a cell wake of a pure untimed
template, and a blocking send or call onto an untimed template that no
subtree kill can end. `timedCohortEnds` is that graph cut. It does not
disable `finish`.

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
`compatFails I.desc = []`, and `stepsCoverB`. A terminable per-peer's programs
contain no bulk `send`, `trySend`, or `call` (`noBulkSend` inside
`transitionOk`). A core is not muted, and its program may `terminate`.
`prioOk` bounds the declared priority labels by `priorityBound`. Inside
`transitionOk`, `effectsOk` requires every `.cell R L _` effect to be a
non-blocking cell edge from the transition's template and target state into
`R` with label `L`. The same shape is `cellEffectFails` on a description's
`cellEffects` list, and that list is part of `structLines`, so `GraphOk.struct`
rejects an undeclared cell write.

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

**BulkFree for a terminable per-peer.** `BulkFree` says a terminable per-peer's
carried continuation satisfies `noBulkSend`. `LocalOk` checks the same thing
on every listed program of a terminable per-peer. A core is not in that class.
A terminable per-peer may terminate while a shared stage still holds its
earlier sends; it may not bulk-send as part of the program it is running.
This is narrower than a rule that would forbid every send by a terminable
per-peer.

**callTermFails.** `GraphOk.lifecycle` is `callTermFails D = []`: no call edge
targets a terminable per-peer outside that peer's subtree, except a pool child
of the calling core. A core is not a terminable target. `coreFlagFails` rejects
the flag, and a call to a core is allowed because the core's `terminate`
crashes the node rather than leaving the caller waiting. A killing `terminate`
is refused while a parked call is present. The two together are why a per-peer
callee that is owed a reply cannot be the actor that exits.

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
- **F10.** The intended statement, once `fair_delivered` builds again, is that
  under `LocalOk` and `GraphOk` each reliable message, identified by the id of
  the actor that stored it, is consumed by `recvBulk` or `recvPrio`.
  `reliable_free_reachable` would keep a terminable mailbox free of reliable
  mail, so a killing `terminate` cannot discard one. `loss_not_delivered` is
  that discard on a description the checker does not accept: the run is `Fair`
  and the message is never received. None of these three elaborate today.
- **F11.** `CellFlags` is not checked against the set of writers. A cell edge
  is accepted when the flag word passes `cellFails`, not when the program
  effects are shown to be the only writers.

## Axioms

`lake build Deadlock` does not succeed: the default target elaborates
`Deadlock.Json`, and the headline modules above do not build. The list is
what an earlier successful build printed. It is not a `#print axioms` of
this tree.

The modules that do build are `Basic`, `Compat`, `Counterexample`,
`Examples`, `Failures`, `Graph`, `Local`, `Occupy`, `Safety`, `Semantics`,
`Tomb`, `Orphan`, and `Outlive`. An axiom audit of those modules, and of
the R6a, R6b, R6c, R7a, R7b, R7c, R7d, R8b, R8c, Orphan, and Outlive
probes, found only `propext`, `Classical.choice`, and `Quot.sound`. The
probes' printed axioms are `propext` and `Quot.sound`. There is no `sorry`
and no `native_decide`.

From that earlier `lake build Deadlock`:

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
