# Deadlock freedom for bounded-mailbox actors

A Lean 4 development, abstracted from the Amaru pure-stage notes in
`docs/deadlock-research/`. It does not import Amaru types. Haskell and
cardano-node are not used.

Pinned toolchain: `lean-toolchain` (`leanprover/lean4:v4.35.0`).
`lake-manifest.json` locks an empty package set: the proof depends only on
Lean's prelude, not Mathlib, so `lake build` does not download anything else.

```sh
cd formal/deadlock
lake build
lake exe check examples/safe.json
```

Exit status is 0 on `pass`, 1 when the checks fail, 2 on usage or parse errors.

## What is proved

`GraphOk` is the decidable side of the theory (Lemmas 1–4 and H1–H7, minus
timing). `checkBool` / `lake exe check` implement it. `checkBool_sound` says a
passing check yields `GraphOk`. A reported cycle is a real cycle
(`issue_cycle_real`).

`deadlock_freedom` is the theorem a later Rust test should cite. Its statement:

```lean
theorem deadlock_freedom (I : Impl) (hG : GraphOk I.desc) (hR : Refines I) :
    ∀ N, ∀ ρ : Run I N, Fair ρ →
      (∀ i s, ¬ WaitPath (ρ.cfg i) s s) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) = some .effect → ¬ Stuck ρ s i) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) = some .peer → ¬ Stuck ρ s i) ∧
      (∀ s i, waitKind ((ρ.cfg i).st s) ≠ some .cell) ∧
      (∀ s i dst, l1 I.desc (tname dst) = true →
        waitKind ((ρ.cfg i).st s) ≠ some (.blockingSend dst))
```

In prose, for every instance count `N` and every fair run of an implementation
that refines a passing description:

1. **Safety.** No configuration on the run contains a wait-for cycle. A wait is
   a blocking send or an admitted call waiting for its reply. Any such cycle
   would project to a cycle in the state-indexed residual graph, which the
   checker has rejected. Projection is on `(template, typestate)`, so one proof
   covers every `N` and every intermediate set of live instances.
2. **Effects.** No actor is stuck forever in an internal effect. Completion is
   always enabled and does not depend on any other actor (A-int). Fairness
   therefore takes it.
3. **Peers.** No actor is stuck forever in a peer wait. Every peer wait in the
   semantics is timed: completion is always enabled (A-peer, timeouts kept;
   Theorem B's numeric bounds are not). Descriptions that set `untimedPeer`
   are rejected.
4. **Cells.** No phase waits on a cell. A cell write stores the value and, when
   the dirty bit was clear, `try_send`s one wake. A full mailbox drops the wake
   and leaves the bit set. The writer is not parked. `WaitKind.cell` is the
   class a blocking cell read would have; `waitKind_ne_cell` says no phase is
   in it.
5. **Lemma 1.** On a mailbox whose summed occupancy bound fits its capacity for
   every `N` (`a*N+b` compared coefficient-wise), refinement says there is no
   blocking-send wait. The checker deletes those send edges from the residual
   graph. Call **reply** edges are not deleted by credit: admission may be
   free while the caller still waits for the answer.

Partial deadlock (some actor stuck forever while others still step) and global
deadlock are both impossible for the waits in (2)–(5), because those waits
cannot stick. A wait-cycle, partial or global, is impossible for every blocking
send and call by (1), with or without fairness.

`performReply_caller_box` is the oneshot reply fact: the reply step does not
read the caller's bulk occupancy. A caller whose own mailbox is full is not
blocked by that fullness. The definition `CallerMailboxFull` records the
configuration the informal notes worry about.

### Axioms

From `#print axioms` (Lean 4.35.0):

| theorem | axioms |
|---|---|
| `deadlock_freedom` | `propext` |
| `no_wait_cycle` | `propext` |
| `not_stuck_effect` | `propext` |
| `checkBool_sound` | `propext`, `Quot.sound` |

No `sorry`, no `Classical.choice`, no axioms beyond Lean's standard ones.

## Assumptions (the trust boundary)

`GraphOk` is checked. `Refines I` is not. A Rust exporter that dumps typestate
graphs and wiring as JSON, then runs `lake exe check`, discharges `GraphOk`
for that description. For `deadlock_freedom` to apply to production code the
exporter (or a later proof) must also establish `Refines`:

- **`projects`.** In every reachable configuration, a blocking send or a
  call-reply wait from actor `s` to actor `dst` is a residual edge
  `(template s, typestate s) → (template dst, typestate dst)`. The `allowed`
  list is an **over-approximation** of pairs that can co-occur: every reachable
  pair must be listed. An omitted reachable pair makes `projects` false and the
  checker can miss a cycle. Extra pairs can only cause a false failure.
  When `compatibility` is `"all"`, every target state is allowed.
- **`call_replies`.** If a transition is started by dequeuing a call
  (`acceptsCall`), its program contains `reply` before it finishes. The checker
  only sees the boolean `repliesInDequeue` on the edge; this field says the
  boolean is honest.
- **`credit_clear`.** Occupancy bounds are real invariants. For a mailbox with
  Lemma 1 (`mustFit` or, more precisely, `l1`: sum of edge occupancies `≤`
  capacity for every `N`), no reachable state has a blocking sender parked on
  it. The exporter's numbers must count every producer, including per-peer
  copies, injectors, and wakes. An edge's `occupancy` is that producer's
  contribution, already written as `a*N+b` (the checker does not multiply by
  `N` again).
- **`no_crash`.** Priority-lane occupancy, including an in-flight self-schedule,
  stays `≤ priorityBound ≤ priorityCapacity`. Overflow is a crash in the
  semantics, not a wait; refinement says the crash state is unreachable.
- **Edge honesty.** A superseding edge must be a non-blocking cell write with
  flags (i)–(v) plus the dirty bit, or the check fails. An ingress edge must be
  a non-blocking `try_send` whose `ingressLegal + other producers ≤ capacity`,
  or the check fails. The exporter must not mark a real blocking send as either
  of those.
- **Effects.** Anything classified as `internal` must actually complete without
  waiting on an actor mailbox. A callback that blocks on a stage is not an
  internal effect; it has to be a pseudo-stage edge. Peer waits in the model
  all complete (timeout or environment). `untimedPeer: true` is rejected.
- **Names.** `freshNames` must be true. The semantics never revives a `dead`
  id. Sends to a dead actor drop. A call to a missing or terminable actor is
  rejected by the check (`no call targets a terminable template`).
- **Fairness.** Runs are fair in the sense of `Fair`: a forced action that
  stays enabled is taken (F1), admission is FIFO in `enqueueOrPark` /
  `receiveBulk` (F2), and if an actor is idle with bulk work infinitely often
  then it takes a bulk receive infinitely often (F3, priority does not starve
  the mailbox). Spawn is not forced.

`Impl` is the description plus a finite list of transitions
`(template, fromState, label, program, toState, acceptsCall)`. Programs are
finite lists of `send`, `trySend`, `call`, `reply`, `selfSchedule`, `cell`,
`internal`, `peer`, `terminate`. Per-peer targets use the effect's `hint`
index, which must be `< N`.

Affine comparison is exact for every `N ≥ 0`: `a₁*N+b₁ ≤ a₂*N+b₂` for all `N`
if and only if `a₁ ≤ a₂` and `b₁ ≤ b₂` (`Affine.leB_iff_forall_eval`).

## What is not covered

- **Theorem B / timing.** No Δ, no per-hop budget, no per-peer fairness bound,
  no O4/O5. Deadlock freedom is not timeliness. A fair run may still be
  arbitrarily slow.
- **General residual-queue liveness.** `no_wait_cycle` forbids a cycle of
  blocking sends and call replies, at every `N`. It does not by itself show
  that a sender parked *behind* other parked senders, or waiting while its
  target is busy in a lower program, eventually runs. The pieces for that
  argument are in the development (`run_enabled`, `can_receive_enabled`,
  `fair_recv`, `recv_resumes_head_of_box`, rank from `GraphOk.ranked`) but the
  phase-stability lemma under other actors' steps is not finished, so it is
  not part of `deadlock_freedom`. Lemma 1 mailboxes do not need it: refinement
  says they never park.
- **Protocol deadlock of an idle actor** waiting for a message nobody will
  send, while its mailbox still drains. That is out of scope except where it
  is a call that never replies (`call_replies` is the hypothesis, not a
  theorem that every program replies).
- **Livelock** of `try_send` retry loops (obligation O1').
- **That Amaru refines this model.** Nothing here reads the Rust. Until an
  exporter produces the JSON and a proof or audit of `Refines`, the theorem
  does not apply to the node.

## Checker rules

`lake exe check` fails unless all of the following hold.

- Templates and edge endpoints exist; states contain `initial`; names are unique.
- `send` and `call` are blocking. `trySend`, `reply`, `selfSchedule`, `cell`,
  `internal`, `peer` are non-blocking.
- `scope` matches multiplicity (`cross` is per-peer to per-peer, `coreInst`
  mixes `one` and `perPeer`, `intra` is unrestricted).
- `freshNames` is true. No template has `untimedPeer`. Priority bound `≤`
  priority capacity. Every `call` has `repliesInDequeue` and its target is not
  `terminable`.
- A `superseding` edge is a non-blocking `cell` whose flags are all true:
  `singleWriter` and `orderMonotone` (i), `noPerMessageObligation` (ii),
  `visibility` (iii), `readPoints` (iv), `idempotent` (v), `dirtyBit`.
  Otherwise the offending flag is printed.
- An `ingress` edge is a non-blocking `trySend` with `ingressLegal` such that
  `legal + occupancy of every other edge into that mailbox ≤ capacity`.
- **Residual graph.** An edge contributes state-indexed waits unless it is
  non-blocking, or it is a blocking `send` into a mailbox with Lemma 1.
  Calls stay (the reply wait). Each remaining edge is drawn only to target
  states the compatibility relation allows. That graph must be acyclic. A
  cycle is printed as `(template, state) -> ... -> (template, state)`.
- **`mustFit`.** Default true. The mailbox's summed occupancy must be `≤` its
  capacity. Set false only when the mailbox is deliberately not credited and
  its blocking sends are ordered by compatibility (the token example). A
  violation is printed as `fail: overflowing mailbox`.

`a*N+b` may be a bare number (`b`, with `a = 0`) or `{"a": …, "b": …}`.

### Schema `amaru-deadlock-graph/v1`

```json
{
  "schema": "amaru-deadlock-graph/v1",
  "name": "example",
  "freshNames": true,
  "compatibility": "all",
  "templates": [{
    "name": "sink",
    "multiplicity": "one",
    "capacity": {"a": 0, "b": 10},
    "priorityCapacity": 4,
    "priorityBound": 1,
    "states": ["idle"],
    "initial": "idle",
    "terminable": false,
    "untimedPeer": false,
    "mustFit": true
  }],
  "edges": [{
    "src": "source",
    "srcState": "idle",
    "dst": "sink",
    "kind": "blocking",
    "reliability": "reliable",
    "effect": "send",
    "label": "Ping",
    "scope": "intra",
    "occupancy": 1,
    "repliesInDequeue": false,
    "ingress": false,
    "ingressLegal": null,
    "cell": {
      "singleWriter": false,
      "orderMonotone": false,
      "noPerMessageObligation": false,
      "visibility": false,
      "readPoints": false,
      "idempotent": false,
      "dirtyBit": false
    }
  }]
}
```

`compatibility` is `"all"` or `"explicit"`. The latter requires `allowed`:
`[{ "src", "srcState", "dst", "dstState" }]`. Omitted booleans default as in
the decoder (`terminable` / `untimedPeer` / `repliesInDequeue` / `ingress`
false, `mustFit` true, missing `cell` all false).

## Examples

| file | expected |
|---|---|
| `examples/safe.json` | `pass` — one blocking send, occupancy 1, capacity 10 |
| `examples/credit.json` | `pass` — request and response, each of occupancy 1 into a capacity-1 mailbox (Lemma 1 both ways) |
| `examples/token-pair.json` | `pass` — `select_chain`/`fetch_blocks` token cycle, occupancy 11 > capacity 10, broken by compatibility |
| `examples/token-pair-ungated.json` | `fail: residual cycle` — same edges, compatibility `"all"` |
| `examples/manager-peer.json` | `fail: residual cycle` — blocking `manager ↔ peer_selection`, occupancy 11 > 10 |
| `examples/overflow.json` | `fail: overflowing mailbox` — one send, 11 > 10, `mustFit` |

The same verdicts are `native_decide`d in `Deadlock/Examples.lean`.

## Layout

- `Deadlock/Basic.lean` — descriptions, affine forms
- `Deadlock/Graph.lean` — residual graph, checker, `checkBool_sound`
- `Deadlock/Semantics.lean` — configurations, step, fairness, deadlock notions
- `Deadlock/Proof.lean` — effect, peer, and cell progress; oneshot reply; head-of-queue resume
- `Deadlock/Theorem.lean` — `Refines`, `no_wait_cycle`, `deadlock_freedom`
- `Deadlock/Json.lean`, `Main.lean` — `lake exe check`
