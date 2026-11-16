# Adversarial review: `formal/deadlock` at rkuhn-bot/amaru@79e5ae3d6 (experiment/lean-deadlock)

Reviewer: Helen. This review only read code: nothing was pushed, no GitHub comments were made, and no one was contacted.

**Fetch.** `git fetch origin experiment/lean-deadlock` succeeded first time, moving the branch from 908593cb6 to 79e5ae3d6. No workaround was needed. I extracted the tree with `git archive 79e5ae3d6 formal/deadlock` into /workspace/lean-review-79e5ae/.

**My Lean files.** These are not in the repo. They live in `formal/deadlock/Helen/` and are checked with `lake env lean`:
- `Axioms.lean`: `#print axioms` for every headline theorem.
- `Counter.lean`: the counterexamples and witnesses below. It compiles with no errors and no `sorry`.
- `Dbg.lean`: step-by-step traces.

## Build and axioms

- `lake build Deadlock` succeeded (25 jobs, ~30 s, linter warnings only). Log: /workspace/lean-review-79e5ae/build.log.
- `Deadlock.lean` imports `Progress`, `Witness` and `Failures`, so all three are built.
- The sources contain no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `extern`. The build log has 0 "declaration uses 'sorry'" messages.
- `native_decide` is **not** on the safety or liveness theorem path. It is used only in Examples, Failures and **Witness**.
- `#print axioms` (Helen/Axioms.lean):

| theorem | axioms |
|---|---|
| `blocked_progress`, `blocked_go`, `fin_exec_no_blocked`, `cell_wake_enabled`, `fin_exec_no_wake`, `deadlock_freedom`, `cell_fresh`, `below_idle`, `never_stuck` | propext, Classical.choice, Quot.sound |
| `park_reachable` | propext, `parks_on_second_send._native.native_decide.ax_1_1` |
| `park_unblocks` | + `resumes_after_receive._native…` |
| `park_graph_ok` / `park_local_ok` | + `park_checked._native…` / `park_local._native…` |

The non-vacuity witness is therefore trusted through the compiler (`native_decide`), not checked by the kernel.

## Verdict

- **The vacuity is gone. The headline safety theorem is now true but too weak to mean what we want.**
  - `Action.ingress` gives the model real behaviour. I show a GraphOk ∧ LocalOk reachable world with a genuine blocking-send wait (`Helen.not_vacuous`).
  - The new `blocked_progress` concludes only `∃ act, Enabled I w act`. An unrelated actor's ingress satisfies that.
  - I mechanised a reachable world with a genuine permanent A↔B deadlock where the conclusion still holds via an independent ingress into C (`Helen.deadlocked_world_reachable`, `still_parked`). The same off-chain witness exists in a variant that **passes** GraphOk ∧ LocalOk (`pc_graph`, `pc_local`, `pc_producer_parked`, `pc_clock_enabled`).
  - `fin_exec_no_blocked` is the same content restricted to worlds where nothing at all is enabled. It is a correct result about **total** stalls, and it is silent about partial deadlock.
- **The proof is stronger than the statement.** `blocked_go` (Progress.lean:391–470) does walk the wait chain. It picks `recvBulk dst`, `exec dst` or `finish dst` of the partner, or recurses on a partner of strictly lower height. The statement then discards which action it found.
- **Partial deadlock is covered only by `deadlock_freedom` under `Fair`.** No fair `Run` has been shown to exist.
- **F6 is not fixed.** The env oracle is pinned to `true` by `Assumptions` (mechanised).
- **F4 got worse.** `permanentTarget` forbids every reliable send or call into a per-peer or terminable template. Amaru's mux, handlers and connection are now unrepresentable, not just restricted.

## Findings, ranked

### N1 (high): `blocked_progress` concludes `∃ act, Enabled`, so any unrelated step satisfies it

Lean (Progress.lean:475–477):
```lean
theorem blocked_progress … (hR : Reachable I N w) (id : InstId) (hB : Blocked w id) :
    ∃ act, Enabled I w act
```

**Why it is too weak.** The conclusion does not mention `id`. In any world where some other actor can take an ingress, `exec` or `recvBulk`, the statement holds whether or not `id` can ever make progress. So it cannot tell "A waits on a chain that drains" apart from "A is in a permanent cycle while C keeps ticking".

**Does ingress make `Enabled` trivially true?** Not in every world. `receiveIngress` (Semantics.lean:499–513) needs the target to be live, idle, non-terminable, with `parked = []`, box room, and a token above the floor. But one idle ingress core with an empty box is enough, and in that situation the token is refunded on every `recvBulk`. So in any system with an always-ready ingress core, `∃ act, Enabled` holds in every world where that core is idle.

**Mechanised counterexample** (Helen/Counter.lean, `cycImpl`):
- Cores A and B each have capacity 1 and a self ingress `Go`. On `Go`, each sends `M` twice to the other. Core C has a self ingress `Tick` with an empty program.
- Trace `[ingress A Go, ingress B Go, recvBulk A, recvBulk B, exec A, exec B, exec A, exec B]`. Afterwards A is `parked(B)` and B is `parked(A)`, each with a full box and one parked entry (`mutual_park`, trace in Dbg.lean).
- `chain_disabled`: `recvBulk A`, `recvBulk B`, `exec A` and `exec B` all return `none`.
- `still_parked`: three rounds of `ingress C Tick` and `recvBulk C` leave A and B parked.
- `deadlocked_world_reachable`: the world is `Reachable`, `Blocked w A` holds, and `∃ act, Enabled` holds with `ingress C "Tick"` as the witness.
- `cyc_rejected`: `checkBool cycDesc = false`. GraphOk forbids this config (residual cycle B→A→B and ingress overflow), so it does not refute the theorem. It shows the statement's conclusion is satisfied by a deadlocked system.

**Variant that passes the checks** (`parkClockImpl` = the authors' `parkImpl` plus an independent `clock` core with a self ingress):
- `pc_graph : checkBool = true` and `pc_local : localOkB = true`.
- After `parkActs`, the producer is parked (`pc_producer_parked`), and `ingress clock Tick` is enabled (`pc_clock_enabled`).
- So `blocked_progress`'s conclusion at that world is witnessed off the producer's chain.
- In this instance the producer does in fact unblock, by `recvBulk sink`. The point is that the theorem does not say so.

**Fix.** Export what `blocked_go` already proves, then strengthen it to a finite unblocking execution:
```lean
-- chain relation: the wait target of id, transitively, through parked / awaitReply
def OnChain (w) (id) : Action → Prop := …   -- act's subject is id's wait target*, act ∈ {recvBulk, exec, finish}
theorem blocked_progress' … : ∃ act, OnChain w id act ∧ Enabled I w act
theorem blocked_unblocks … : ∃ acts w', (∀ a ∈ acts, OnChainOrEnvFinish w id a) ∧
    runFrom I (some w) acts = some w' ∧ (¬ Blocked w' id ∨ chain ends in awaitPeer)
```
The second theorem is a lexicographic descent on (residual height, `parkIndex`, `phaseFuel`). The proof already has all three measures.

### N2 (high): `fin_exec_no_blocked` speaks only about total stalls

Lean (Rank.lean:11751–11757, Progress.lean:482–487):
```lean
structure FinExec … maximal : ∀ a, apply I a (cfg len) = none
theorem fin_exec_no_blocked … (e : FinExec I N) (id) : ¬ Blocked (e.cfg e.len) id
```

**Why.**
- Yes, it is maximal: nothing is enabled in the last world. It is exactly "no reachable world is a global stall that contains a blocked actor". That is equivalent to N1's statement and inherits its weakness.
- With an always-ready ingress core (C or `clock` above), **no** maximal finite execution exists at the A↔B world. The corollary is then silent about the partial deadlock.
- It is not empty in general. Drop C from `cycImpl` and the A↔B world has nothing enabled: A and B are parked, and ingress needs an idle target. That is a maximal `FinExec` ending in a blocked actor, and `GraphOk` correctly rejects the configuration. I argued this case by hand; it is not mechanised, because proving `∀ a, apply = none` needs quantification over label strings.

So F2's "total deadlock is excluded by definition" is fixed. Partial deadlock still rests on `deadlock_freedom` with `Fair`.

**Fix.** Use N1's chain form. The corollary then becomes: in a maximal execution, no blocked actor exists. In any execution, each blocked actor has a finite chain-only continuation that unblocks it.

### N3 (high): F6 is not fixed; the env oracle is pinned to `true` by `Assumptions`

Lean (Semantics.lean:152–165, 475–481; Local.lean `Assumptions`):
```lean
structure Impl where … env : Env := Env.always
def finishWait (I) (w) (id) := match … | .awaitEffect k => if I.env.effectDone w id then some … else none …
internal_complete : ∀ (w : World) (id) (k), (w.st id).phase = .awaitEffect k → Enabled I w (.finish id)
peer_complete     : ∀ (w : World) (id) (k), (w.st id).phase = .awaitPeer k   → Enabled I w (.finish id)
```

Mechanised (Helen/Counter.lean):
```lean
theorem assumptions_default (D trs) : Assumptions { desc := D, transitions := trs }      -- [propext]
theorem assumptions_force_peer (I) (hA : Assumptions I) … (hk : phase = .awaitPeer k) :
    I.env.peerDone w id = true                                                         -- [propext]
```
(The effect version is `assumptions_force_effect`.)

**Why.**
- `Assumptions` is free for the default env.
- For any env, it forces `effectDone` and `peerDone` to be true at **every** world, reachable or not, where a wait exists.
- So "a peer can stall forever" is still impossible in the model. A-peer is "every peer is always instantly ready".
- `blocked_progress` relies on this directly (Progress.lean:410–412, 432–434, 462–464).
- `rust_refines` is still the identity statement.

**Fix.**
- Remove the per-world enabledness fields.
- Make the progress theorem end its chain at an `awaitPeer`. A peer stall is an external stall attributed to the peer.
- State A-int as a liveness or fairness premise on reachable runs: an `awaitEffect` on a fair run eventually finishes.
- State A-peer only for timed peer edges.

### N4 (high): F4 is worse; `permanentTarget` makes per-peer and terminable templates unreachable by any reliable send or call

Lean (Local.lean:158, new):
```lean
def permanentTarget (I : Impl) : Bool :=
  I.desc.edges.all fun e =>
    if (e.effect == .send || e.effect == .call) && e.reliability == .reliable then
      match templateOf I.desc e.dst with
      | none => false
      | some t => t.multiplicity == .one && t.terminable == false
    else true
```
Further constraints:
- `superseding` must be a cell (`cellFails`).
- A reliable non-ingress `trySend` fails (`reliableTryFails`).
- `receiveIngress` refuses terminable targets.
- The authors' own `per_peer_target_fails` and `terminable_target_fails` confirm the restriction.

**Why.** A per-peer template can now receive only ingress and cell wakes, and a terminable one only cell wakes. Amaru's per-connection traffic between per-peer stages is exactly the core of the node:
- mux → handler `FromNetwork`: mux.rs:846, :858.
- connection → chainsync `NewTip` and → blockfetch `RequestRange`: connection.rs:252, :258.
- the mini-protocol call into mux: miniprotocol.rs:232, :278.

These were restricted before. Now they cannot be written down at all. SUBTREE.md is a design note only.

**Fix.** Implement SUBTREE.md: atomic subtree kill, intra-subtree reliable sends and calls to terminable members, `peerKey` routing, the dead-instance lift, and guaranteed tombstones. Until then, state explicitly in THEOREM.md that the theorem covers only networks whose per-peer parts are leaf sources.

### N5 (medium): ingress only into an idle actor under-approximates Amaru

Lean (Semantics.lean:503):
```lean
if a.life ≠ .alive || a.phase ≠ .idle then none
```

**Why.**
- In pure-stage, the mailbox accepts messages while the stage runs, parks or awaits a reply. The mux reader keeps pushing `FromNetwork` into a busy handler.
- The model never explores "ingress fills X's box while X is parked or awaiting". It therefore proves a property of a strict sub-behaviour, and Rust ⊑ model fails.
- Token accounting (`totalOcc` includes the ingress edge's occupancy) makes it plausible that `OccInv` and the height argument extend. That is unproved: the `ingress` case of `step_inv`, `OccInv` and `CallTagInv` assumes `phase = .idle` (`ingress_open`).

**Counterexample sketch to test.** X calls Y. Y's handler sends to X, and X's box has 1 slot left. Ingress arrives at X while X is in `awaitReply`, and Y then parks on X. This is excluded by `l1` if the ingress occupancy is counted, so: prove it.

**Fix.** Drop the `phase = .idle` guard and re-prove the ingress preservation cases.

### N6 (medium): no fair `Run` is shown to exist, so `deadlock_freedom` and `cell_fresh` may still be vacuous

- The witness gives a reachable world, not a `Run` with `Fair`.
- Fair runs are plausible, for example the lasso `parkActs ++ [recvBulk sink, recvBulk sink] ++ (ingress producer Go, recvBulk producer)^ω` in `parkImpl`. None is constructed.
- New wrinkle: `forced (.ingress _ _) = true` (Semantics.lean:695–697), so `Fair.weak` obliges the environment to inject whenever ingress stays enabled. Runs with a quiet peer are not fair, and the liveness theorems exclude them.

**Fix.**
- Construct the lasso in Lean.
- Set `forced (.ingress _ _) = false`; the environment is not scheduled by us.

### N7 (medium): the witness is a toy

- `parkDesc` (Witness.lean:11–29) has two `one` cores, `N = 0`, one residual edge (producer/busy → sink, `mustFit = false`), and residual height 1.
- It does involve a real park on a full box: the sink has capacity 1 and the second `send` parks.
- It has **no** call, **no** cell, **no** per-peer instance, **no** termination and **no** chain of length ≥ 2. The `ih` branch of `blocked_go` is never exercised.
- It relies on `native_decide`.

**Fix.** Add a witness with a height-≥2 chain, using either a call or a park on a parked partner. Also add a cell wake reaching `recvPrio`, and an ingress into a per-peer instance. Prefer `decide`, or a small kernel-checked evaluator.

### N8 (low–medium): the ingress flag is a drop loophole, and `ingressLegal` is unused by the semantics

- `reliableTryFails` exempts any edge with `ingress = true` (Graph.lean:405–409).
- `effectsOk` lets a program emit `.trySend d l` along such an edge (Local.lean:40).
- `hasIngress` ignores `e.src`.

So an exporter can mark a program-to-program `trySend` as "ingress" and drop reliable messages on a full box (Semantics.lean:396–403).

- `receiveIngress` budgets from self-edge occupancy (`budget/debt (tname dst) (tname dst)`), not from `ingressLegal`. `ingressLegal` only feeds the static `ingressFails`.

**Fix.**
- Require ingress edges to have `src = dst` (or an `env` pseudo-template).
- Forbid programs from emitting `trySend` on ingress edges.
- Budget ingress from `ingressLegal`.

### N9 (low): `Deadlock` still has a dead `cell` arm

`Deadlock` (Semantics.lean:779–786) keeps `| some .cell => True`. The new docstring correctly explains why `.peer` is excluded. The unused `PartialDeadlock`, `GlobalDeadlock` and `CallerMailboxFull` were removed.

## (c) Vacuity

- `Review/Vacuity.lean` is now a comment-only "negative record" in the repo. The old `step_quiet` case split fails because `Action.ingress` is not covered.
- That failure is substantive. Reachable GraphOk ∧ LocalOk worlds now contain real waits (`Helen.not_vacuous`: `GraphOk parkDesc ∧ LocalOk parkImpl ∧ ∃ w, Reachable parkImpl 0 w ∧ ∃ d, waitKind (w.st producerId) = some (.blockingSend d)`).
- What remains near-vacuous is the *shape* of the safety conclusion (N1, N2). For the Run theorems, what is missing is a witness that a fair run exists (N6).

## (e) Status F1–F11

| # | Status at 79e5ae3d6 |
|---|---|
| F1 no stimulus | **Fixed.** `Action.ingress` exists and a reachable park is witnessed. Ingress is restricted to idle targets (N5), and the witness is a toy (N7). |
| F2 infinite runs only, total deadlock excluded | **Partly fixed.** `FinExec.maximal` and the safety form cover total stalls. Partial deadlock is covered only under `Fair` (N2, N6). |
| F3 Fair on CanReceive, duplicate keys | **Fixed.** `uniqueKeys` is in `localTail`, and `Fair.bulk` is stated on `Enabled`. The safety theorems do not use `Fair` at all; only `deadlock_freedom` and `cell_fresh` do. |
| F4 Amaru breaks the restrictions | **Worse** (N4). `permanentTarget` bans reliable traffic into per-peer and terminable stages. Design only, in SUBTREE.md. |
| F5 constant routing hint | **Open** (design only). |
| F6 Assumptions decorative / A-int, A-peer baked in | **Not fixed** (N3). The oracle is forced to `true` at every waiting world. Mechanised. |
| F7 internal timeouts not expressible | **Open.** |
| F8 reliable drops | **Mostly fixed.** Reliable non-ingress `trySend` fails, `labelHandled` is checked, and `permanentTarget` removes dead-target drops. The ingress flag is a remaining loophole (N8). |
| F9 dead definitions / cell arm | **Mostly fixed.** Unused definitions removed and the `.peer` exclusion documented. The `cell` arm remains (N9). |
| F10 receive-side / obligation liveness | **Open.** |
| F11 CellFlags unverified | **Open.** |

## Target statement (restated)

For every N:
```
GraphOk I.desc ∧ LocalOk I ∧ Env I   -- Env: A-int as fairness on awaitEffect along reachable runs;
                                     --      A-peer only for timed peer edges; Rust ⊑ Impl separately
→ (Progress, safety form)
    ∀ w, Reachable I N w → ∀ a, Blocked w a →
      ∃ acts w', runFrom I (some w) acts = some w' ∧
        (∀ x ∈ acts, x acts on a's wait chain in w, or is the finish of an effect wait on it) ∧
        (¬ SameWait (w.st a) (w'.st a)  ∨  a's chain ends in an awaitPeer)
  ∧ (Liveness, under scheduler fairness with the environment NOT forced)
    ∀ ρ : Run I N, Fair ρ → ¬ Deadlock ρ ∧ CellFresh ρ ∧ Delivered ρ
    -- Delivered: every message accepted into a live actor's box is dequeued later,
    --            and every admitted call is answered
  ∧ (Non-vacuity) ∃ ρ, Fair ρ ∧ ρ reaches a park on a full box, an awaitReply, and a cell wake
```
This statement should also hold for the subtree semantics of SUBTREE.md (F4, F5), with ingress allowed into busy actors (N5).
