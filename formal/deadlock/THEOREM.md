# Deadlock freedom and cell observation

This note is the statement a reviewer can check against the Lean development.
Nothing in the development uses `sorry` or `admit`.

## What is proved

```lean
theorem deadlock_freedom (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc)
    (hA : Assumptions I) {N : Nat} (ρ : Run I N) (hF : Fair ρ) : ¬ Deadlock ρ
```

A fair reachable run has no actor blocked forever. The proof is strong
induction on residual height (`below_idle`), then `never_stuck`. Effect and
peer waits are discharged by `Assumptions.internal_complete` and
`Assumptions.peer_complete`. A blocking send or a parked call waits on a
strictly lower actor. An `awaitReply` cannot last: while the caller stays
there it cannot mint a new `callFrom`, so `CallTagInv` keeps the callee in
`handlerOwes` or `replyPending`, and that phase is not `idle`.

`Fair.prio` is not used. Adding it does not change `deadlock_freedom`.
`recvBulk` stays enabled when `recvPrio` is enabled; the step relation is
unchanged.

## What was asked, and what is false

The target written in `README.md` is

```lean
theorem deadlock_freedom (I) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I) :
  ∀ N, ∀ ρ : Run I N, Fair ρ → ¬ Deadlock ρ ∧ CellFresh ρ
```

The first conjunct is the theorem above. The second conjunct is **not true**
of this semantics, even after `Fair.prio`.

`CellFresh` says: if `cell dst label` strictly increases at step `i`, then
some later step `j > i` is `recvBulk r`, `recvPrio r`, or `exec r` for a live
`r` with `tname r = dst`, and `observed r label` at `j + 1` is at least the
post-write value.

Two fair runs fail it.

**No live reader.** Let `R` be `perPeer`, or a `one` template that has already
taken a killing `terminate`. Let `W` be a non-terminable `one` whose program
contains `.cell R L 1`. `W` runs that effect. The cell goes from 0 to 1 and
`dirty` becomes true. `readersOf` is empty, so `wakeReaders` enqueues nothing.
No instance of `R` ever takes `recvBulk`, `recvPrio`, or `exec`. `Fair.prio`
holds because `recvPrio` of a reader that does not exist is never enabled.
`Fair.weak` and `Fair.bulk` hold. `LocalOk` does not reject the program:
`effectsOk` does not require a cell effect to be an edge.

**Undeclared label.** `readCells` stores `observed` only for
`cellLabels`, the labels of edges with `effect = cell` and `dst` equal to the
reader's template. A program can still write some other label. A later
`recvPrio` of a live reader records the edge labels and leaves that
`observed` entry at its initial 0, which is below the written value.

`Fair.prio` is the right hypothesis for the scheduler gap (a run that always
prefers `recvBulk` while a priority wake is enabled only at idle instants).
It does not create a reader, and it does not make `readCells` record a label
that is not an edge.

What the priority rule does give, and what is in the development as lemmas
rather than as `CellFresh`: a non-terminable multiplicity-`one` template's
core stays alive (`core_alive`); a declared cell label is a priority label
(`edge_in_prio`); an idle live actor with that label on its lane has
`recvPrio` enabled (`recv_prio_enabled`), because a priority message has
`callFrom = none` (`CallTagInv.prioPlain`) and such a delivery returns
`some`. The drain itself is `Fair.prio`.

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
    (∀ i, ∃ j, i ≤ j ∧ CanReceive (ρ.cfg j) s) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)
  prio : ∀ (s : InstId),
    (∀ i, ∃ j, i ≤ j ∧ Enabled I (ρ.cfg j) (.recvPrio s)) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvPrio s)
```

`forced (.spawn _) = false` and `forced _ = true` otherwise. `Enabled` is
`apply ≠ none`. `CanReceive` is idle, alive, and a nonempty bulk box or parked
list. `prio` is strong fairness: enabled infinitely often implies taken
infinitely often. It is the runtime draining a priority wake rather than
leaving it behind the bulk mailbox. `recvBulk` is not disabled by a nonempty
priority lane.

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
    ((ρ.cfg i).cell dst label).value < ((ρ.cfg (i + 1)).cell dst label).value →
    ∃ j r, i < j ∧ tname r = dst ∧ ((ρ.cfg j).st r).life = .alive ∧
      (ρ.act j = .recvBulk r ∨ ρ.act j = .recvPrio r ∨ ρ.act j = .exec r) ∧
      ((ρ.cfg (i + 1)).cell dst label).value ≤ ((ρ.cfg (j + 1)).observed r label)
```

A cell write sets `value := max(old, payload)` and `dirty := true`. If `dirty`
was clear it upserts one priority wake per live reader (`wakeReaders`).
`readCells` clears `dirty` and stores the value in `observed`, and it runs
from `deliver` (hence `recvBulk` and `recvPrio`), from spawn, and from a
killing `terminate` (`exec`). Spawn is not one of the three witness actions.
An `exec` that is not `terminate` does not call `readCells`.

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
`priorityBound`.

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

## Axioms

From `lake build Deadlock` (`#print axioms`):

```
'Deadlock.below_idle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.never_stuck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Deadlock.deadlock_freedom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice`, and `Quot.sound` are the standard Lean kernel
axioms used by `Classical.em` and by `simp` of definitions. There is no
domain axiom.
