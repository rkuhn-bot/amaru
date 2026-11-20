# Review (Helen), Round 7: snapshot/lean-r5-wip @ e5f48c977

Written Fri 20 Nov 2026, about 15:00 CET. This review is read-only: nothing was pushed, posted or sent, pragma-org was not touched, and the Cursor GitHub App was not used.

- **Setup.** `git`/`gh` ran as `rkuhn-bot` (`gh api user`). I fetched into `/workspace/amaru-research/repo` and created a detached worktree at `/workspace/lean-review-e5f48c`.
- **pure-stage and Amaru references** are read from fork main 34a453005 in that clone.
- **My probes** are `formal/deadlock/Helen/R7a.lean`, `R7b.lean`, `R7c.lean` and `R7d.lean`. The axiom dump is `Helen/AxAll7.lean`. All of these are local, uncommitted files.

## 1. Build and axioms

- **Build.** `lake build Deadlock.Semantics Deadlock.Local Deadlock.Graph Deadlock.Examples` exits 0 in 12.7 s; the log is `build.log`. The only warnings are linter warnings in Graph and Semantics.
  - Examples now builds alongside Semantics: `overflowDesc` is defined only in Examples.lean:91, so N7 is fixed.
- **Axioms of the green files.** `Helen/AxAll7.lean` is generated from every `theorem` in Basic, Graph, Semantics, Local, Examples and Occupy: 411 theorems in all.
  - Every one depends only on a subset of {propext, Classical.choice, Quot.sound}. 66 of them use Classical.choice, all inherited library lemmas in Semantics/Occupy.
  - No theorem depends on `sorryAx` or `Lean.ofReduceBool`.
  - None of those files contains `sorry`, `native_decide`, `implemented_by`, `extern` or `unsafe`.
- **Branch probes.** Andrew's R6a, R6b and R6c on the branch are green. Their axioms are [propext] or [propext, Quot.sound], so the claim "propext and Quot.sound only" holds.
- **My R7 probes** are all green, with [propext] or [propext, Quot.sound] and no sorry or native_decide.
- **Rank.lean is unchanged and still red**, so the headline `deadlock_freedom` (Rank.lean:18783) is not checked. I refute its exact hypothesis shape instead (§4).

### Workarounds and deviations

1. **Two Fair-run refutations take one hypothesis, `OffIdle`.** They are `R7b/R7d.deadlock_freedom_false`. `OffIdle` is `off_idle_reachable` (Progress.lean, red) specialised to the final world, as in R6.
2. **`GraphOk` comes from `checkBool_sound`** (Graph.lean:828), because `GraphOk` is a structure and not a Bool.
3. **One fact is shown with `#eval`, not a theorem.** `localIssues noEdge = []` (R7b) is built from strings and the kernel cannot reduce it. Only `localOkB noEdge = false` is a theorem.
4. **R7a/R7c copy the branch's R6a/R6c definitions** and then add statements. The Helen files are not a lake library, so they cannot be imported.
5. **"Original statements, API-adapted"** means only that `.peer n k` became `.peer n key gen`, with the generation index set to the instance the old run named. Andrew changed `deadImpl` (he added Q `gone` handlers, which the new `tombstoneHandled` requires); I used his version.

## 2. Probe-flip audit

| Probe | Branch statement | Honest? |
|---|---|---|
| R6a outcome_blind → outcome_own_state | **Changed design**: a `miss` state and `toTimedOut := "miss"` | Yes, as an F9 fix (per-outcome typestate exists). On the *original* design, `outcome_blind` still holds (`R7a.orig_outcome_blind_holds_by_choice`). That is now a design choice, not a model limit. |
| R6a branch_label_uncounted → branch_labels_counted | the true negation | Yes. `R7a.orig_branch_label_uncounted_refuted` |
| R6a wk_* / fairR | adds `hc : crashed = false` | Legitimate: `apply` is `none` on a crashed world |
| R6b deadlock_freedom_false → bypass_rejected | `localOkB bypassImpl = false`, `sendsTo … = 4` | Yes. The design leaves the hypotheses. But see **N11/N12**: the same theorem fails again on other designs |
| R6c sub_local | now `= false` | Same design; the **checker** changed (`tombstoneHandled` in every state). So `respawn_overflow` and `tombstone_later_state` now speak about a design *outside* LocalOk. I redid the overflow on a LocalOk version (`R7c.sub2_ok`, `sub2_root_refused`): the root refusal holds there too |
| respawn_overflow | `… ++ cycle 4 = none` | True, but it does not say *which* step fails. `R7c.orig_respawn_overflow_refuted` pins it: the prefix is `some`, and `[.spawn "A"]` is `none` |
| tombstone_later_state | `runAt tombActs = none` | True; the prefix is `some` (`orig_tombstone_later_refuted`), so the final `recvPrio` is the refused step |
| respawn_key_split | routes resolve | Yes (`orig_key_split_refuted`) |
| crash_not_absorbing → crash_absorbing | a new `crashImpl` | Yes. The original overflow trace is now `none` (`orig_crash_not_absorbing_refuted`) |
| tree_graph_rejected → tree_graph_ok | | Yes |
| respawn_child_crashes → respawn_child_live, _fresh | | Yes |
| dead_sender_refunded | snapshot changed: refunded at the mark | Yes (N9) |
| dead_supervisor_crash → dead_supervisor_refused | `= none ∧ crashedB (…) = false` | The first conjunct is honest. **The second is vacuous**: `crashedB none = false` by definition, so it follows from the first. Low; drop it or state it on the prefix |

I found no added hypothesis that makes a statement trivial. Every original counterexample is refuted by `decide` (R7a, R7c `orig_*`). For R6b, Andrew's `bypass_rejected` refutes it.

## 3. N1–N10 and the residues

| # | Verdict | Evidence |
|---|---|---|
| N1 branch counts | **Partial (two new high holes, N11/N12)** | `sendsTo`/`effSends` take the maximum over alternatives, and a branch replaces the tail (Semantics.lean:1688-1708). `contSends` :1711. `pending` :1718-1725. `selfLabels`/`effSelf`, `cellWakeLabels`, `hasTerminate`, `noBulkSend` and `noSelfSchedule` all recurse (Local.lean:22-48, 90-117, 296-305). Branch effects are checked at their own typestate (`BranchAt`/`focus`/`effectOk`, Local.lean:55-88). `stateNamed` is checked (:144, used at :175). Nested branches are counted correctly (`R7c.nested_counted`). `deadlock_freedom_false` is gone from R6b. But (a) the parked-call `pending` omits `onTimedOut` (:1722, N12), and (b) `sendsOk` checks every path against `toState`'s floor, not the typestate the path lands in (Local.lean:50, N11). `replyCount` (Semantics.lean:2249-2258) *sums* across alternatives instead of counting per path (N14). |
| N2 GraphOk | **Fixed** | `supervisorInSubtree` and `subtreeFails` (Graph.lean:655-680). The terminable and `timeoutKills` requirements are dropped. `spawnScope` (Local.lean:149-167): the child must name `src` as its supervisor, and both must be per-peer. `tree_graph_ok` |
| N3 crashed | **Fixed (semantics)** | `World.crashed` :397. `crashWorld` sets it (:868-871). `apply` is `none` for every action, including stutter, ingress and spawn (:2115-2118), with `apply_step` :2120. The headline exists only in prose (DECISIONS, THEOREM.md, :1176-1181); Rank.lean is unchanged and red. Not vacuous: R7b/R7d reach non-crashed quiescent worlds with Fair runs. But see N13 |
| N4 prioSized / refusal | **Partial** | `prioDemand`/`prioSized` with `queued` (:562-568), `queuedTombstones` :572, `tombstoneRoom` and `maySpawnRoot` (:2042-2055). Holds for core-supervised roots (`sub2_root_refused`). **Not** for children: `spawnChild` (:1222-1241) has no room check, so a per-peer parent that restarts its child overflows and crashes in a design that passes GraphOk, LocalOk and `prioSizeFails = []` (`R7c.rtree_ok`, `child_restart_overflow`). Faithfulness: §5 |
| N5 restart | **Fixed (one live child per key)** | `InstId.peer name key gen` :12. `findLive`, `maxGen`, `aliveAt` (:576-591). `spawnChild` gives a no-op on a live child and generation+1 on a dead one (:1231-1239). `openSubtreeKey` reuses the key (:2010-2018). The routing split is fixed (`respawn_key_split`). Expressiveness: §5 |
| N6 dead supervisor | **Fixed** | `supervisorLive` (:2030-2040) and `maySpawnRoot` (:2052-2055). `dead_supervisor_refused` (vacuous second conjunct, see §2) |
| N7 overflowDesc clash | **Fixed** | Only Examples.lean:91 defines it; everything builds together |
| N8 stale docs | **Mostly fixed** | THEOREM.md and CHANGES-R5.md are updated. THEOREM.md itself says "the proof text in Deliver.lean is not yet restated" |
| N9 seal lag | **Fixed** | `markShutdown` calls `releaseOutbound` (:1149-1155). `dead_sender_refunded` take 12 = (…, 0, 1) |
| N10 decidable | **Fixed** | `instance Decidable (LocalOk I)` (Local.lean:340) via `inferInstanceAs`, with no Classical. `unfold LocalOk; decide` works in every probe, with [propext] only and each probe under 3 s. Side gap: the reporter `localIssues` misses the branch-focus failure (`R7b.reporter_gap`: `localOkB = false` but `localIssues = []`), low |
| F4 residue | **Fixed** | `deliver` keeps a tombstone that has no handler (:716-719). `tombstoneHandled` requires a handler in every declared parent state (Local.lean:317-331), and branch landing states must be declared (`stateNamed`) |
| F5 residue | **Fixed** | Same key, new generation; sibling routes resolve |
| F8 residue | **Fixed** | Crash is absorbing (N3). Seal and mark as in R6 |
| F9 residue | **Fixed** | `toNotAdmitted`/`toTimedOut`/`toTimeout`/`toFull`/`toGone` on Transition and Cont (Cont :306-314, Transition :441-449), `pickState` :650, `selectCall` :655-660, `callTimeout` :1658-1660, trySend :1259-1260. But N11 is a consequence of this fix |

## 4. New findings

**N11 (high): an outcome branch that lands in a typestate with a higher floor breaks the token invariant, and `deadlock_freedom` is false again.**

- **Cause.** `sendsOk` (Local.lean:50) checks `sendsTo prog + floor(toState) ≤ floor(fromState)` only. An outcome that lands in `toTimeout` (or `toTimedOut`, `toFull`, `toGone`, `toNotAdmitted`) with a *higher* floor is never checked against that floor. The ingress gate (Semantics.lean:1841-1848) uses the current typestate's floor, so it lets ingress consume the tokens that the landing state needs.
- **Counterexample: `Helen/R7b.lean`.** One core A with capacity 4 and states idle/w/miss.
  - Edges: ingress `Go` in idle and w, A w→A M with occupancy 2, A miss→A M with occupancy 0. Floors are idle 2, w 0, miss 3 (`land_unchecked`).
  - Transitions: idle -Go→ w runs `[peer [send A M]]` with `toTimeout := "miss"`; miss -Go→ w sends M three times.
  - `land_graph` (checkBool) and `land_local` (LocalOk by `decide`) hold.
  - The run: ingress, receive, peer, two ingresses while in w, timeout (landing in miss with 0 tokens), receive Go, three sends. A ends parked on itself with box 4 and parked 1 (`land_overrun`), the world is not crashed (`WT_open`) and it is quiescent (`WT_quiet`).
  - `fairL`, `land_deadlock` and `deadlock_freedom_false (OffIdle)` refute the exact shape of Rank.lean:18783. Axioms [propext, Quot.sound].
- **Fix.** Check every path against its own landing floor: `sends_p + floor(land_p) ≤ floor(fromState)`. Make the token gate the maximum over paths of `sends_p + floor(land_p)`, using that `need` both in `receiveIngress` and as the proof invariant. Equivalently, require `floor(toX) ≤ floor(toState)` for every outcome state, which is weaker in expressiveness but simple.

**N12 (high): a parked call's `pending` omits `onTimedOut`.**

- **Cause.** `pending (.parked _ true k) = max rest onNotAdmitted` (Semantics.lean:1722). Once the call is admitted it becomes `awaitReply`, where `onTimedOut` can still run.
- **Counterexample: `Helen/R7d.lean`.** A is a core with capacity 4. It calls B (capacity 0, a rendezvous), and `onTimedOut` sends M to itself twice; the occupancy is 2 and floors are idle 2, w 0.
  - `pc_graph` and `pc_local` hold.
  - While the call is parked, `pending = 0` and three ingresses take A's tokens to 0. When B admits the call, `pending` jumps to 2 with 0 tokens (`pc_pending_gap`).
  - The timeout branch then overfills A: box 4 plus 1 parked on itself (`pc_overrun`).
  - `fairP`, `pc_deadlock` and `deadlock_freedom_false (OffIdle)` follow. Axioms [propext, Quot.sound].
- **Fix.** `pending (.parked _ true k) = max (sendsTo rest) (max (sendsTo onNotAdmitted) (own + sendsTo onTimedOut))`. More robustly, define `pending` as `contSends`, which already takes the maximum of all four (:1711) but is not used, and re-derive the token-floor lemma from that.

**N13 (med): tombstone overflow is model-only and still reachable, through child restarts.**

- **Evidence.** `tombstoneRoom` guards only *root* spawns. `R7c.rtree_ok` (GraphOk, LocalOk, `prioSizeFails = []`) and `child_restart_overflow`:
  1. Conn (per-peer, capacity 4) restarts Hand four times without draining.
  2. The fifth Hand's `terminate` crashes the world, because `enqueueTombstone` finds a full lane (:1070-1072).
- **pure-stage never crashes here.** Tombstones go to an unbounded `VecDeque` (`supervisor.tombstones.push_back`, mod.rs:1323, field initialised at :1356). Only self-schedules are bounded and panic (mod.rs:1238-1243, :1882-1883).
- **Consequences.** A crash in the model ends the run (N3), so every real execution past that point is outside the theorem.
- **Fix.** Model tombstones as pure-stage does: a separate unbounded queue, taken before the priority lane. tokio.rs:452 has the order "tombstones, then a parked timeout, then …". Then remove the tombstone term from `prioSized` and remove `tombstoneRoom`. If the bound is kept, it cannot be static under restarts (the number of restarts between drains is unbounded), so the crash would remain model-only.

**N14 (low/med): `replyCount` sums over alternatives instead of counting per path.**

- **Examples:**
  - `[.call X q 0 [] [], .reply]` passes `replyCount == 1`, but the NotAdmitted and TimedOut paths replace the tail and never reply.
  - `[.trySend X l 0 [.reply] []]` passes with zero replies on the admitted path.
  - `[.call X q 0 [.reply] [.reply], .reply]`, which has exactly one reply on every path, is rejected.
- **Impact.** No deadlock, because the caller's `callTimeout` is always enabled and there is no Reply guarantee. But the "exactly one reply" discipline is not what is checked.
- **Fix.** Count per path: a list of path counts, or min = max = 1, with branches replacing the tail.

**N15 (low): stale tombstones are indistinguishable across generations.**

- **Evidence.** The label has no generation, so a gen-0 tombstone can be handled while gen 1 is alive (`R7c.stale_tombstone`: prio `["dead/Hand"]` from `.peer "Hand" 0 0` while `Hand 0 1` is alive). Amaru's tombstones carry the instance, e.g. `ManagerMessage::ConnectionDied(peer, conn_id, role)` (manager/mod.rs:429).
- **Impact.** No hang: `Eff.spawn` is not a wait, routing and calls resolve to the live incarnation (`findLive`), and a second spawn is a no-op. But a parent state that means "child is dead" can be wrong.
- **Fix.** Either let transitions match the sender, or document that a typestate never encodes child liveness.

**N16 (low): a shutting-down generation's queued box mail is not counted against the host's per-key budget.** The new generation gets a fresh budget (`withTokens` in `spawnChild`), and `releaseOutbound` drops only parked entries. A host can hold mail from two generations of one key. I found no deadlock from this (members only talk within their subtree, and the excess parks). The token-floor proof needs an invariant that bounds this per key, or the excess must be charged to the key.

**N17 (low): the reporter disagrees with the checker.** `localIssues` misses the branch-focus `effectOk` failures (`R7b.reporter_gap`). Add focus-aware `programGap`.

**N18 (low): `dead_supervisor_refused`'s second conjunct is vacuous** (§2).

**N19 (low/observation): "deadlock-free or crashed" is implicit.** A `Run` is infinite and a crashed world has no successor, so Fair runs are exactly the runs that never crash. Any prefix in which fairness forces a crashing step (for example, a full lane) cannot be extended. A deadlock elsewhere in that prefix is therefore outside the theorem's scope. That is consistent with Roland's ruling (overflow means crashed). But it means every model-only crash (N13) silently shrinks the theorem.
- Suggestion: let `stutter` be enabled on a crashed world, and state `Fair ρ → ¬ Deadlock ρ ∨ ∃ i, (ρ.cfg i).crashed` explicitly.
- No valid design crashes trivially: with LocalOk, `spawnScope` rules out the `spawnChild` crash paths, and roots under a dead supervisor are refused. The remaining crash sources are a permanent core's `terminate` (visible in the design) and overflow: self-schedules and cell wakes (matching pure-stage) and tombstones (model-only, N13).

## 5. The N4 and N5 questions

**N4: does pure-stage ever refuse a spawn?** No.
- `Effect::AddStage` takes a fresh `stage_name(&mut self.stage_count, …)` and calls `resume_add_stage_internal(…).expect("add stage effect is always runnable")` (mod.rs:1331-1335).
- `Effect::WireStage` inserts `StageData` unconditionally (mod.rs:1336-1368).
- The only skip is `skip_if_terminated` when the *parent itself* has terminated.
- Tombstones are unbounded (mod.rs:1323).

So the refusal in `maySpawnRoot` (Semantics.lean:2052-2055) is model-only behaviour:
- **What it returns.** In the model, a root spawn is an *environment* `Action.spawn` with no spawning actor. Refusal is `apply = none`: the action is simply not enabled. Nothing is returned to anyone, no actor waits on it, and `spawn` is not `forced`, so Fair never demands it. There is no retry loop; the environment may try again on any later step.
- **Hence** the refusal cannot deadlock anything. But in Amaru the spawner is a stage: the manager calls `eff.stage(format!("{conn_id}-{peer}"), connection::stage)` (manager/mod.rs:424-430). In the real system that spawn always succeeds and the tombstone queue simply grows. The refusal therefore hides real executions (more simultaneous tombstones than `capPrio`).
- Child spawns are not refused at all, and they crash instead (N13).

**Recommendation:** match pure-stage. Use an unbounded separate tombstone queue, drop the refusal and the tombstone term in `prioSized`, and keep crash-on-overflow only for self-schedules and cell wakes, which pure-stage also panics on. A static bound that made refusal impossible cannot exist under unbounded restarts.

**N5: does Amaru spawn several concurrent children of one template under one parent?**
- **Per-peer code: no.** Every per-peer parent spawns at most one child per template:
  - connection: mux and handshake (connection.rs:378-402);
  - chainsync initiator and responder (chainsync/mod.rs:64-90);
  - blockfetch initiator and responder (blockfetch/initiator.rs:453-459, responder.rs:287-289);
  - keepalive (keepalive/mod.rs:77-88);
  - peer_sharing (peer_sharing/mod.rs:93-95, responder.rs:64);
  - mux: done-trap (mux.rs:272-274), and the writer plus reader per connection (mux.rs:387-391, two templates sharing the tombstone `MuxMessage::Terminate`).
  - So "one live child per key" is expressive enough for per-peer parents.
- **Concurrent same-template children exist only under singleton parents:**
  - the connector's worker pool: up to `DEFAULT_PARALLEL_CONNECTION = 10` `connect-worker-{n}` stages, unsupervised (manager/connector.rs:32, :60-70);
  - one `accept` stage per listen address (manager/mod.rs:392-395);
  - one connection stage per `(conn_id, peer)`, including several inbound connections to the same peer before duplicate detection (manager/mod.rs:403-430).
- **What Lean can express.** Lean models the manager→connection case as environment-spawned roots with population N. It cannot express a core spawning a bounded pool: `spawnScope` (Local.lean:149-167) needs a per-peer parent, and `spawnChild (.core _) = none` (:1224) would crash.
- **Proposal.** Allow `Eff.spawn` from a core with a declared multiplicity bound n per child template. Index children by `(slot < n, gen)`, make `population` multiply by n, and size `simultaneousTombstones` accordingly. A connection pool's population is then n, independent of N.
- **Silent no-op re-spawn.** It cannot leave the parent waiting: `Eff.spawn` is not a wait, sends and calls resolve to the live incarnation, and calls have deadlines. It does diverge from pure-stage, where a second `stage` call creates a second stage (low).

## 6. Verdict

**No go** for the one-shot proof repair. There are two high findings:
- **N11:** an outcome typestate's floor is not checked.
- **N12:** a parked call's `pending` omits `onTimedOut`.

Each one refutes `deadlock_freedom` with a design that passes GraphOk, LocalOk and Assumptions (modulo `off_idle_reachable`). Both fixes are local to `sendsOk`, `pending` and the ingress gate, and they should be in place before the proof is repaired. N13 (tombstone faithfulness) should be decided at the same time, because it changes `prioSized` and `maySpawnRoot`.
