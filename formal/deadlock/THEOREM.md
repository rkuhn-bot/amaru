# Deadlock freedom and cell observation

This note is the statement a reviewer can check against the Lean development.
Nothing in the development uses `sorry` or `admit`.

## What is proved

The headline is safety on reachable worlds, not an infinite run.

```lean
theorem blocked_progress (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I)
    (hA : Assumptions I) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (hB : Blocked w id) : ∃ act, Enabled I w act

theorem fin_exec_no_blocked (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I)
    (hA : Assumptions I) {N : Nat} (e : FinExec I N) (id : InstId) :
    ¬ Blocked (e.cfg e.len) id
```

`Blocked` is a live actor in `.parked` (a blocking send or a parked call),
`.awaitReply`, `.awaitEffect`, or `.awaitPeer`. `blocked_progress` is strong
induction on residual height. An effect or peer wait has `finish` enabled by
`Assumptions`. A send or call waits on a live partner of strictly smaller
height (`park_below`, `call_below`, `reply_below`): an idle partner can
`recvBulk`, a running partner can `exec`, and a partner that is itself blocked
is the induction hypothesis. `fin_exec_no_blocked` is the corollary: a finite
execution that has stopped (`FinExec.maximal`) has no live blocked actor.
`fin_exec_reachable` puts that last world in `Reachable`.

`park_reachable` and `park_unblocks` are one `GraphOk` and `LocalOk` world in
which the producer is parked and the next `recvBulk` leaves it idle, so the
hypothesis of `blocked_progress` is inhabited.

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

A fair reachable run has no actor blocked forever. The proof is strong
induction on residual height (`below_idle`), then `never_stuck`. Effect and
peer waits are discharged by `Assumptions.internal_complete` and
`Assumptions.peer_complete`. A blocking send or a parked call waits on a
strictly lower actor. An `awaitReply` cannot last: while the caller stays
there it cannot mint a new `callFrom`, so `CallTagInv` keeps the callee in
`handlerOwes` or `replyPending`, and that phase is not `idle`. `cell_fresh`
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

`forced (.spawn _) = false` and `forced _ = true` otherwise. `Enabled` is
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
    | some .cell => True
    | some .effect => True
    | _ => False
```

`waitKind` of a real phase is never `some .cell` (`waitKind_ne_cell`). The
`cell` arm of `Deadlock` is unreachable. `effect` and `peer` are discharged
by `Assumptions`, not by the height induction.

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
  internal_complete :
    ∀ (w : World) (id : InstId) (k : Cont),
      (w.st id).phase = .awaitEffect k → Enabled I w (.finish id)
  peer_complete :
    ∀ (w : World) (id : InstId) (k : Cont),
      (w.st id).phase = .awaitPeer k → Enabled I w (.finish id)
```

These are not theorems about Rust. `rust_refines` is the exporter obligation.
In this development the transition list is the model, so the field is the
identity on that list. `internal_complete` and `peer_complete` are the
assumptions that an internal effect returns and a peer wait completes or
times out.

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

- **F4/F5.** Per-peer subtree kill, calls inside a subtree, and routing by a
  subtree key. Design only, in `SUBTREE.md`. Not implemented.
- **F7.** Peer waits are not given their own timeout. `Assumptions.peer_complete`
  is an oracle flag, not a clock.
- **F10.** No liveness theorem that a message accepted into a mailbox is
  eventually delivered. `cell_fresh` is the cell special case, and it still
  assumes a `Fair` infinite run.
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
```

`propext`, `Classical.choice`, and `Quot.sound` are the standard Lean kernel
axioms used by `Classical.em` and by `simp` of definitions. There is no
domain axiom.
