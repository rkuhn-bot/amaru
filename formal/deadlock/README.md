# Deadlock freedom for bounded-mailbox actors

A Lean 4 development, abstracted from the Amaru pure-stage notes in
`docs/deadlock-research/`. It does not import Amaru types. Haskell and
cardano-node are not used.

Pinned toolchain: `lean-toolchain` (`leanprover/lean4:v4.35.0`).
`lake-manifest.json` locks an empty package set: the proof depends only on
Lean's prelude, not Mathlib.

```sh
cd formal/deadlock
lake build
lake exe check examples/safe.json
```

Exit status is 0 on `pass`, 1 when the checks fail, 2 on usage or parse errors.

## Compatibility relation

The relation is untrusted input. A group names two or more template roles and
lists the tuples of `(role, state)` that may co-occur. Pairs are groups of size
2; a 3-stage fetch token is a group of size 3. The same JSON is what a later
exporter can fill with a product fixpoint, or with the projection of a global
protocol. This version does not compute either of those.

`compatFails` checks, locally and decidably:

- the initial tuple (every role in its `initial` state) is allowed
- every transition in `transitions` sends an allowed tuple to an allowed tuple
- a per-peer role is rejected: the check does not certify every instance count
- a terminable role is rejected: a dead actor is not a state of the tuple, and
  is not treated as the initial state
- restart-in-place is not a step of the semantics, so it is not a closure
  obligation. Fresh spawn allocates a new per-peer index; those roles are the
  ones the check rejects
- every blocking edge has both ends in some group, so the list cannot quietly
  drop an interaction

Failure names the step and the pre/post tuple, for example:

```text
fail: compatibility broken by transition fetch_blocks idle -> busy [OnTip]
  pre: (select_chain: holding, fetch_blocks: idle, header_store: idle)
  post: (select_chain: holding, fetch_blocks: busy, header_store: idle)
```

or, when the relation is closed but too coarse, the residual cycle it still
leaves. A failure means **not provable with this relation**. The check is
sufficient, not necessary: a list can be rejected even though some finer
argument would have worked. A wrong or hand-written list cannot make a passing
check unsound. It can only fail.

Residual edges are drawn only to partner states that co-occur with the source
state in every group containing both roles (`groupTargets`).
`groupTargets_cooccur` is that filter. `compat_group_closed` says a passing
check leaves each group well-formed and with an empty closure list.

Roles in a group must have multiplicity `one` in this version. The tuple format
does not depend on that; per-peer products are left to the later fixpoint.

`compatibility: "all"` is the universal relation: every declared pair co-occurs,
so it cannot hide a cycle. `compatibility: "explicit"` is rejected. A pairwise
list is not an invariance check and must not pass. `token-pair.json` now fails
with that message; the checked token relation is `token-relation.json`.

## Target theorem

```lean
theorem deadlock_freedom (I) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I) :
  ∀ N, ∀ ρ : Run I N, Fair ρ → ¬ Deadlock ρ ∧ CellFresh ρ
```

`Deadlock` is the one in `Semantics.lean`: some actor is stuck forever on a
blocking send, a call reply, a cell wait, or an internal effect. `CellFresh`
says that after a cell write strictly raises the stored value, some later step
of a live reader of that template is a receive or an exec that read-and-clears,
and the value it records is at least the written one.

**This statement is not yet a theorem.** The height induction that would
discharge a blocking send or a call reply — destination at strictly lower
rank, finite program, FIFO index in `parked` then `box`, one reply before
terminate — is not closed. What is closed is recorded below. Nothing in the
development uses `sorry`.

## Assumptions

`Assumptions` is only the trust boundary. Effect completion and peer timeout
are assumptions about the binary, not results.

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

`rust_refines` is the exporter obligation: the node's programs are
`I.transitions`. In the Lean model the list is the model, so the field is the
identity on that list; applying the development to Rust is assuming the
exporter told the truth. `internal_complete` and `peer_complete` are A-int and
A-peer. Fair scheduling is the separate `Fair` hypothesis (F1 on forced
actions, F3 so priority does not starve the bulk mailbox). Spawn is not forced.

`not_stuck_effect_assumed` and `not_stuck_peer_assumed` use those two fields.
They are not derived from `GraphOk`.

## What `LocalOk` checks

`LocalOk I` is `localOkB I = true`, a decidable predicate on the transition
list. It is the part that used to be assumed as `Refines.projects`,
`credit_clear`, and `no_crash`, and is now a check:

- Every transition's states are declared, `release = 1`, and
  `sends(program) + floor(toState) ≤ floor(fromState)` for every destination
  template. `floor` is `budget - debt`, and `debt` is the per-instance sum of
  edge occupancies out of that state (`b` for multiplicity `one`, `a` for
  `perPeer`).
- A program's `send` / `trySend` / `call` effects are edges from the
  **target** state (typestate moves when the transition starts).
- An `acceptsCall` program has exactly one `reply`, and no `terminate` before
  it. Any other program has no `reply`. `terminate` occurs only on a
  `terminable` template, and a terminable template's programs do no bulk send.
- Every call label is accepted, with `acceptsCall`, in every declared state of
  the callee.
- For `compatibility: "all"`, every declared partner state is a residual
  target. For `groups`, residual targets are the states that co-occur in the
  relation (`groupTargets_cooccur`). `stepsCoverB` requires every transition
  the semantics can fire to be one of the steps that relation was closed under.
- Occupancy shape: multiplicity `one` edges have `a = 0`, `perPeer` edges have
  `b = 0`, so the affine total matches the per-instance sum.
- Priority labels (self-schedules, cell-edge labels, and `cell` writes in
  programs) number at most `priorityBound.b`, and that bound has `a = 0`.
  `GraphOk` already requires the bound to fit `priorityCapacity`, so the
  declared set fits the lane for every `N`. Re-arming a label does not grow
  the lane; a new label past the lane is the overflow crash.

`projects` holds for every reachable world (`GraphOk` and `LocalOk`). A parked
phase or an `awaitReply` is a blocking edge of the description, and if the
partner is alive its typestate is a member of `targetStates`. In group mode
that list is the states that co-occur with the source state in every group
containing both roles; the live tuple is one of the allowed ones, both roles
are multiplicity-one cores (a busy peer of such a template cannot exist), and
`uncoveredEdges` rejects a blocking edge that no group covers. `"all"` uses
the declared state list: an alive actor's typestate is declared, because it
starts at `initial` and only moves to a transition's `toState`. `"explicit"`
does not pass `LocalOk`. The mailbox bound `box.length + |parked| ≤ cap` and
`no_crash` are **not** proved yet. The accounting lemmas (`owed`,
`owed_append_msg`, `debt_le_budget`, `targetsAll_edge`) are in `Occupy.lean`.
Lemma 1's decidable side is the affine comparison `totalOcc ≤ capacity`
(`l1`), which is a bound for every `N`. The semantic inequality along a run
is not proved, so a blocking send that Lemma 1 deletes from the residual
graph is not yet known to be unparked.

## Operational model

- Message labels are real. `send` / `trySend` / `call` / `selfSchedule` carry
  the label the transition fires on. `cell` carries the value.
- A call with no `acceptsCall` transition is not dequeued. A call to a name
  that is not alive is discarded and does not become `awaitReply`.
  `performReply` resumes the caller only when that caller is in
  `awaitReply` **this** sender. `terminate` runs only for `terminable`
  templates and is refused while a parked entry is a call; parked calls are
  not resumed as sends. Dropped mail on terminate is credited back to its
  senders.
- Cells live at `(template, label)`. A write sets `value := max(old, payload)`
  and `dirty := true`, and if the bit was clear it upserts one priority wake
  per live reader. Every `deliver`, `init`, spawn, and successful `terminate`
  read-and-clears `dirty` and stores the value in `observed`. Wakes are not
  bulk occupancy and are not charged.
- Instance ids are unbounded (`peer name index`). `World.N` bounds how many
  instances of each per-peer template are alive at once. Spawn takes the next
  index; a `dead` id is not reused.
- Bulk send/park charges the sender one token for the destination template.
  A bulk receive credits that sender after the receiver is installed, so a
  self-send is not overwritten. Priority delivery is not credited.

`execRun_preserves_other_run` says an actor in `.run` keeps that phase across
another actor's `exec`. `enqueue_keeps_other_run` is the corresponding fact
for a send the actor did not itself perform.

## What is not covered

- **The height induction itself**, and therefore `¬ Deadlock` for
  `blockingSend` and `callReply`, and `CellFresh`. Cycle-freedom
  (`heightsOkB_acyclic`) is proved and is only the well-foundedness of that
  induction.
- **Reachable worlds satisfy `Inv`, and `projects` is proved from that.** The
  items below are closed. The one state this bullet does not claim is the
  intermediate after a queue is cleared and before its senders resume.
  `semInv_init` holds at `initWorld`. `sem_set` / `credit_sem` / `cells_sem` /
  `finish_sem` / `spawn_sem` keep it when typestate and life of group roles do
  not change.   `sem_move` keeps it when one core follows a step the relation
  was closed under (`step_on_observed`). `enqueue_sem` keeps it for a blocking
  send or call and stores that edge in `waitEdge`. `exec_basic_sem` covers an
  `internal`, `peer`, `send`, or `call` head, and `exec_done_sem` covers an
  empty continuation. `exec_try_sem`, `exec_sched_sem`, `exec_reply_sem`, and
  `exec_cell_sem` also keep `MailInv`. `MailInv` says each parked entry's
  sender is `.parked` on that mailbox with the same call bit, each such phase
  has one entry there, and a sender occurs once. `exec_term_skip_sem` is
  terminate that the template refuses. `exec_term_die_sem` is a killing
  terminate: the mailbox is refunded, the actor is dead with an empty queue,
  and every parked sender is resumed, and both invariants hold of that
  combined state. `deliver_inv` moves a core along `sem_move` when delivery
  finds a transition, and a peer only when no group role changes.
  `receive_prio_inv` and `receive_bulk_inv` keep both invariants, including a
  bulk receive that admits a parked sender and resumes that sender together.
  `exec_basic_inv` keeps `MailInv` for `internal`, `peer`, `send`, and `call`,
  including the branch that parks. `exec_head_inv` covers every running head.
  `spawn_inv` keeps both invariants when the peer index being overwritten is
  idle with an empty queue. `Inv` is `SemInv`, `MailInv`, and `OpenSlots`
  together. It holds at `initWorld` and is preserved by one successful `apply`,
  so every reachable world satisfies `inv_reachable`. A parked phase or an
  `awaitReply` is a blocking edge of the description, and a live partner's
  typestate lies in `targetStates` (`projects`, from `projects_park` and
  `projects_reply`).
- **Occupancy as a run invariant.** Per-producer outstanding is already the
  token account: `owed` counts that sender's messages in bulk boxes and parked
  lists, and `tokens` is what has not been spent. `l1_fit` and
  `l1_park_unreachable` show that, when `OccInv` and `TyOk` hold, a Lemma-1
  mailbox holds at most `capBulk` messages and the park branch of
  `enqueueOrPark` is unreachable. `occ_init` holds at `initWorld` when template
  names are unique. `occ_set` keeps it when one actor is replaced without changing
  its life, queues, or tokens, provided the new typestate still fits in those
  tokens. `occ_finish`, `occ_prio`, and `occ_bulk` cover `finish` and both
  receives, including a parked sender being resumed. `occ_enqueue` covers a
  blocking send or call, including a self-send and the park branch.
  `occ_schedule` covers self-schedule, including the overflow crash, and
  `occ_cell` covers a cell write followed by reader wakes. `occ_reply` covers
  `performReply`.   `occ_spawn` covers allocating a fresh per-peer instance. `occ_try` covers
  `trySend`: a fitting target is charged, and a miss or a full mailbox is not.
  `drain_eq_refund` shows that refunding a box and then clearing it is the
  same world as dropping each message and crediting its sender, including a
  message the mailbox owner sent to itself; `occ_drain_box` keeps `OccInv`
  along that second order. `occ_die` marks that actor dead once both lanes are empty and
  it owes nothing, and `occ_release` resumes the parked senders.
  `occ_exec` covers every head of a running actor, including a killing
  `terminate`. `Inv2` packages the step invariant, occupancy, typestate, and
  the terminable-continuation restriction. It holds at `initWorld`, and
  `inv2_reachable` keeps it at every reachable world: a suffix of a program
  with no bulk send still has none, delivery of a terminable actor installs
  such a program, and `bulk_apply` covers every action. `occ_apply` keeps
  occupancy for every action. Charging a send requires the sender's template not
  to be terminable, and `OccInv.still` keeps a terminable actor's owed count
  at zero. That is narrower than Amaru: a per-peer stage, such as a chainsync
  initiator, terminates when its peer disconnects and does send to shared
  stages. Deadlock freedom is proved first under this restriction. The lift
  lets a dead instance keep the messages it already sent charged until they
  are consumed, and counts every instance with `life = dead` and `owed > 0`
  toward the per-peer occupancy bound (or bounds those leftovers by an
  explicit annotation). If that preservation needs a check the current
  description does not have, the check is defined with the lift. The present
  check is not known to be unsound for the restricted model: a terminable
  template cannot bulk-send, so a dead instance does not keep credit a
  replacement would count again. `deadlock_kind` reduces a deadlock to a
  blocking send or a call reply that stays waiting; an effect wait is taken
  by fairness, and no phase is a cell wait. A live partner of either wait
  sits at a strictly lower residual rank (`park_below`, `reply_below`), so a
  least-rank actor is not blocked on a live partner. A call edge cannot
  target a terminable template. Killing `terminate` resumes a parked send
  (`release_resumes_send`) and skips a parked call; an admitted call sits in
  the box, so that same step would leave its caller in `awaitReply` on the
  now-dead callee. `GraphOk` rules that description out, because the callee
  of a call is not terminable and the killing step is the only assignment of
  `life = dead`. `call_program_replies` is the handler fact: one `reply`, and
  no `terminate` before it, so the program has a single path to the reply.
  `step_keeps_run` says any step other than that actor's own `exec` leaves a
  running continuation in place, which is the measure's stability.
  `programOk` does not see `terminate` (`effectsOk` skips it). `TermOk` is
  the missing record: a carried list that still contains `terminate` came
  from a checked transition, so the template is terminable
  (`term_program`, `deliver_carries`). It holds at `initWorld` and across
  `finish` and a priority receive. `terminable_no_parked_call` is the
  `callTermFails` half: no parked call can name that template.
  `terminate_commits` then says the refused branch does not run, the actor
  dies idle, whenever `TermOk` holds. `TermOk` is preserved by bulk receive,
  `exec`, and spawn as well, so `inv3_reachable` carries it at every reachable
  world and `terminate_commits` applies there. `exec_shortens` says every head
  that is still `.run` is a strictly shorter tail, and `not_forever_run` says a
  fair run cannot keep a live actor in `.run` forever. `effect_resumes` and
  `peer_resumes` say fairness takes the `finish` of an effect or peer wait and
  the actor continues on the tail, still alive. `exec_drops` says one step of a
  nonempty program strictly lowers the phase measure, including a crash or a
  killing `terminate`. `reaches_block` puts those together: a live actor later
  becomes idle, dies, crashes, or blocks on a send or a call. `lane_has_room`
  says a fresh label from that declared set still fits, so the crash branch
  does not run once a reachable world keeps the lane duplicate-free and inside
  the set. `prog_src_reachable` says a carried list is a suffix of a listed
  transition, so its `selfSchedule` and `cell` labels are declared.
  `lane_reachable` says every reachable world keeps that lane: receive, finish,
  spawn, and every exec head, including a cell wake into a reader's lane.
  `reachable_not_crashed` follows: the only write of `.crashed` is the overflow
  branch, and it is not taken.   `bulk_resumes_send` says a bulk receive whose
  parked list is nonempty resumes a blocking send at the head, and
  `bulk_admits_call` says the same receive puts a parked call into
  `awaitReply`. While the mailbox owner stays alive, `alive_queue` says every
  step leaves the parked list alone, appends behind it, or drops its head
  (`enqueue_queue`, `bulk_drops_head`, `bulk_queue`). `parkIndex` is the
  waiter's position: an append does not move it (`parkIndex_append`), and
  `recv_closer` says dropping a head in front of it moves it one place closer.
  `queue_place` puts the three queue steps together. `step_index` and
  `index_mono` carry the index across any finite run in which the send stays
  parked and the receiver stays alive. `queued_forever_false` is the inner
  induction: if that receiver is idle with mail infinitely often, `Fair.bulk`
  delivers often enough to walk a finite index down to the head and clear the
  send. `only_terminate_kills` and `receiver_stays` say the receiver of a send
  that stays parked cannot die: a life leaves `alive` only on that actor's
  killing `terminate`, and that step resumes the sender (`alive_while_send`).
  `blocking_next` says one step either leaves the sender on the same parked
  continuation or runs it, and `blocking_fuel` says the run is strictly
  shorter. `blocking_stays` and `send_drops_at` keep that continuation until
  the kind changes, so the drop is at the first differing step. `await_stays`
  and `await_drops_at` do the same for `awaitReply`. `parked_forever_false`
  is the same queue walk for either parked bit: a call cannot stay parked
  once its callee is idle with mail infinitely often.   `mailbox_alive` says a reachable parked list belongs to a live owner.
  `parked_typestate_stays` says an actor that stays parked or in `awaitReply`
  keeps its typestate. `send_height_below` puts those together for a blocking
  send. `call_stays` keeps a call on the same continuation, including when
  admission rewrites `.parked dst true k` into `.awaitReply dst k`.
  `call_drops_at` is the fuel drop at the first step that leaves that kind,
  and `call_height_below` places the callee strictly below the caller through
  both the parked call and the later `awaitReply`. `idle_when_free` says an
  actor that stays alive, and whose wait kind keeps changing, later reaches
  idle: each change drops `phaseFuel`, and a call uses the frozen continuation
  so the drop is against the fuel at the start of the wait.   `send_stuck_false`
  and `call_parked_stuck_false` are the two queue contradictions under that
  hypothesis: a receiver that stays strictly below the waiter, alive, and idle
  with mail infinitely often cannot leave the waiter parked.   `call_admitted`
  uses the second one: a stuck call reaches `awaitReply` on the same
  continuation and stays there. `CallTagInv` names the three places that reply
  can sit while the caller is in `awaitReply`: `d`'s mailbox (`callFrom`),
  `d`'s handler with the reply still ahead, or that reply as the next effect.
  A parked call owns the mailbox entry before admission, which is why a
  `callFrom` is not stray there either. It holds in the initial world, and
  `finish` and `spawn` preserve it. Preservation for receive and `exec`, the
  delivery of the tagged message, the handler reply, `never_stuck`,
  `deadlock_freedom`, `CellFresh`, and the dead-instance lift are not proved.
- **Theorem B / timing.** No Δ, no per-hop budget. Deadlock freedom is not
  timeliness.
- **Receive-side and obligation liveness.** Token leaks, "this request
  eventually gets that response", and the selective token gate
  (`holding` excludes `busy` even though both states are reachable) are out of
  scope. `LocalOk` over-approximates by requiring every declared partner state
  on a blocking edge.
- **That Amaru refines this model.** Nothing here reads the Rust.

## Checker rules

`lake exe check` fails unless all of the following hold. These are unchanged
by the semantic rework, and the old examples keep their verdicts.

- Templates and edge endpoints exist; states contain `initial`; names are unique.
- `send` and `call` are blocking. `trySend`, `reply`, `selfSchedule`, `cell`,
  `internal`, `peer` are non-blocking.
- `scope` matches multiplicity.
- `freshNames` is true. No template has `untimedPeer`. Priority bound `≤`
  priority capacity. Every `call` has `repliesInDequeue`. A call with
  `repliesInDequeue: false` is `lost-reply.json`.
- **No call targets a terminable template** (`callTermFails`, part of
  `GraphOk.lifecycle`). An admitted call sits in the callee's box and the
  caller is in `awaitReply`; it is not a parked entry. Killing `terminate`
  refunds that box with a credit only, and `releaseParked` skips `isCall`
  entries and does not read the box, so the caller would stay in `awaitReply`
  on a dead callee. `performReply` never runs for a callee that is not alive.
  The check rejects the edge, and `call_edge_unterminable` is that fact for a
  description that passes. A parked send is different: `release_resumes_send`
  runs `proceed` on the sender.
- A `superseding` edge is a non-blocking `cell` whose flags are all true,
  including `dirtyBit` and `readPoints`. A missing flag is `lost-wake.json`.
- An `ingress` edge is a non-blocking `trySend` with `ingressLegal` such that
  `legal + occupancy of every other edge into that mailbox ≤ capacity`.
- **Residual graph.** Non-blocking edges are dropped. A blocking `send` into a
  Lemma 1 mailbox is dropped. Calls stay. Each remaining edge is drawn only to
  compatibility targets. The graph must be acyclic.
- **`mustFit`.** Default true. Summed occupancy must be `≤` capacity.

`a*N+b` may be a bare number or `{"a": …, "b": …}`.

## Examples

| file | expected |
|---|---|
| `examples/safe.json` | `pass` |
| `examples/credit.json` | `pass` |
| `examples/token-pair.json` | `fail: compatibility mode explicit is not an invariance check; use groups` |
| `examples/token-pair-ungated.json` | `fail: residual cycle` |
| `examples/manager-peer.json` | `fail: residual cycle` |
| `examples/overflow.json` | `fail: overflowing mailbox` |
| `examples/lost-reply.json` | `fail: call source -[Ping]-> sink is not answered in the dequeue transition` |
| `examples/lost-wake.json` | `fail: superseding edge Wake misses cell conditions readPoints, dirtyBit` |
| `examples/token-relation.json` | `pass` — 3-role fetch token, closed under its transitions and under restart |
| `examples/token-relation-gap.json` | `fail: compatibility broken by transition fetch_blocks idle -> busy [OnTip]` with the pre/post tuple |
| `examples/token-relation-coarse.json` | `fail: residual cycle` — the extra `(holding, busy)` tuple is closed, and it restores the cycle |

The same strings are `native_decide`d in `Deadlock/Examples.lean`.

## Layout

- `Deadlock/Basic.lean` — descriptions, affine forms
- `Deadlock/Graph.lean` — residual graph, checker, `checkBool_sound`
- `Deadlock/Semantics.lean` — configurations, step, fairness, `Deadlock`, cells, churn
- `Deadlock/Local.lean` — `LocalOk`, `Assumptions`, `CellFresh`
- `Deadlock/Occupy.lean` — in-flight message accounting
- `Deadlock/Proof.lean` — effect/peer progress, phase stability of a running actor
- `Deadlock/Projects.lean` — `projects` for reachable worlds
- `Deadlock/Occ.lean` — `OccInv`, and the Lemma-1 bound assuming it
- `Deadlock/Compat.lean` — `compat_group_closed`
- `Deadlock/Theorem.lean` — effect and peer non-stuckness **from `Assumptions`**
- `Deadlock/Json.lean`, `Main.lean` — `lake exe check`

## Axioms

From `#print axioms` (Lean 4.35.0), no `sorryAx`:

| theorem | axioms |
|---|---|
| `not_stuck_effect_assumed`, `not_stuck_peer_assumed`, `compat_group_closed` | `propext` |
| `checkBool_sound`, `groupTargets_cooccur`, `execRun_preserves_other_run` | `propext`, `Quot.sound` |
| `projects`, `ty_reachable`, `inv_reachable`, `step_inv`, `findTr_mem` | `propext`, `Classical.choice`, `Quot.sound` |
| `live_le_occ`, `l1_fit`, `l1_park_unreachable`, `occ_init` | `propext`, `Classical.choice`, `Quot.sound` |
| `occ_set` | `propext`, `Quot.sound` |
| `occ_finish` | `propext`, `Quot.sound` |
| `occ_prio`, `occ_bulk` | `propext`, `Classical.choice`, `Quot.sound` |
