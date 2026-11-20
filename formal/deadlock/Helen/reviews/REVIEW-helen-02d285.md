# Review (Helen), Round 6: snapshot/lean-r5-wip @ 02d285b76

Written Fri 20 Nov 2026, about 14:00 CET. This review is read-only: nothing was pushed, posted or sent to anyone, and pragma-org was not touched.

- **Repository:** rkuhn-bot/amaru.
- **GitHub access:** `gh api user` is `rkuhn-bot`. I fetched into `/workspace/amaru-research/repo` and made a detached worktree at `/workspace/lean-review-02d285`.
- **pure-stage reference:** `origin/main` 34a453005 (`crates/amaru-pure-stage`).

## Build and axioms

- **Build.** `lake build Deadlock.Semantics Deadlock.Local Deadlock.Examples` on Lean v4.35.0 exits 0 in about 14 s; the log is `build.log`. The only warnings are unused-simp linter warnings in Graph. There is no `sorry` in Basic, Graph, Semantics, Occupy, Local or Examples.
- **Repo axioms.** `formal/deadlock/Helen/AxAll.lean` runs `#print axioms` on every `theorem` in Semantics, Local, Graph and Occupy: 401 theorems in all. Each one depends only on a subset of {propext, Classical.choice, Quot.sound}, with no `sorryAx` and no `Lean.ofReduceBool`. Examples.lean has no top-level theorems.
  - Key theorems: `tombstones_exceed_capPrio` [propext, Quot.sound]; `finishCall_cont`, `await_reply_end`, `await_total`, `await_not_forever`, `parked_not_admitted` and `call_answered_reply_false` [propext]; `isChild_peer` [propext, Classical.choice, Quot.sound]; `exec_term_step` [propext].
  - `deadlock_freedom` (Rank.lean:18783), `call_answered` (Deliver.lean:2602) and `fair_delivered` are in red files and were not checked.
- **Probes.** `Helen/R6a.lean`, `Helen/R6b.lean` and `Helen/R6c.lean` are all green with `lake env lean`. They contain no `sorry` and no `native_decide`.
  - Probe axioms are [propext], [propext, Quot.sound] or [propext, Classical.choice, Quot.sound]. Classical.choice comes only from the `simp` proofs of `LocalOk`.

### Workarounds and deviations

1. **Examples cannot be imported next to Semantics.** Both files declare `Deadlock.overflowDesc` (Semantics.lean:7186 and Examples.lean:91). I copied `tpl` and `sendEdge` verbatim from Examples.lean:8-33 into each probe. The probes import only `Deadlock.Semantics` and `Deadlock.Local`.
2. **`localOkB` is no longer kernel-decidable.** `effectsOk`, `callOutcomesOk` and `memberProgramOk` are now well-founded and therefore `@[irreducible]`, so `decide` and `decide +kernel` both fail. I proved `LocalOk` with `simp (config := {decide := true}) [localOkB, …]`. That is where Classical.choice enters.
3. **The two Fair-run refutations take one hypothesis, `OffIdle`.** They are `call_answered_reply_false` in R6a and `deadlock_freedom_false` in R6b.
   - `OffIdle` says that every actor off the roster in the final world is idle and `absent`. This is Andrew's `off_idle_reachable` (Progress.lean, red), specialised to that world.
   - The per-peer half is proved by `rfl` (`off_peer`). The half for cores needs a string disequality that the kernel cannot reduce on a free name.
   - Everything else in both refutations is kernel-checked: the Run, Fair, GraphOk, LocalOk and Assumptions.
4. **Probe location.** The R5 probes were at `/workspace/lean-review-3c0665/formal/deadlock/Helen/`, not `…/3c0665/Helen/` as the brief said. I ported them from there.

## F1–F13

| # | Verdict | Evidence |
|---|---|---|
| F1 call_answered / no Reply | **Fixed** | `call_answered` (Deliver.lean:2602) is now the callee-side claim: an admitted `mid`, with a callee that stays alive, is handled by `recvBulk`. Caller totality is `finishCall_cont` (Semantics.lean:7235), `await_reply_end` :7325, `await_total` :7444, `parked_not_admitted` :7386 and `await_not_forever` :7417. `call_answered_reply_false` is kept at :7516 (and R6a's Fair-run version is still green). DECISIONS.md:57-75 says there is no Reply guarantee. Nothing in the .md or .lean files still promises Reply (grep). Stale docs: SEMANTICS.md:71 ("A dead or absent target stores nothing. A call then waits in `awaitReply`"; it is now NotAdmitted) and SEMANTICS.md:120-126 (`killSubtree`/`plantTombstone`) (N8) |
| F2 dead sender | **Fixed** | `releaseOutbound` :995 runs inside `releaseWorld` :1010-1020 and matches mod.rs:1460-1463. R6c `dead_sender_refunded`: X's entry leaves H, X gets its token back, and `recvBulk H` is disabled. The residue is a seal lag: between the mark and the seal, a host can still admit a parked entry from a shutting-down sender (low, N9) |
| F3 subtree abort, peer supervision | **Partial** | The semantics are fixed. `supervisorInst` :912 and `isChild` :935 allow per-peer parents (`isChild_peer` :944). `markTree` :1098 marks every descendant, terminable or not. `terminateStage` :1112 sends one tombstone to the immediate supervisor. `Eff.abort` (`abortChildren` :1120) exists. R6c `terminate_marks_grandchild` and `tree_sealed`: Conn→Hand→Work all shut down and seal, and Mgr gets `dead/Conn`. **But GraphOk still rejects every per-peer supervisor** (Graph.lean:671-674 is unchanged), so the fix is outside the theorems' hypotheses (**N2**) |
| F4 tombstones | **Partial** | Fixed parts: a per-template label (`Template.tombstone`, Basic.lean; `tombstoneLabel` :963); `prioLoad` = length :790; the full-lane crash in `offerPrio` :811, `enqueueTombstone` :979 and `selfSchedule` :1190-1201; and `tombstoneHandled` in LocalOk (Local.lean:236). Remaining: (a) `tombstoneHandled` asks for *one* parent transition on the label, so a tombstone that arrives in another state is still consumed silently (R6c `tombstone_later_state`). (b) The `prioSized` bound is unsound under root respawn (**N4**, R6c `respawn_overflow`). (c) `prioSizeFails` is not in LocalOk, and `prioLabels` misses branch self-schedules (**N1**). (d) Andrew's `tombstones_exceed_capPrio` is a hand-built world, not reachable from `initWorld`; its members are non-terminable, so GraphOk would reject them |
| F5 keys | **Partial** | `spawnChild` :1131 creates the child at the parent's key (a positive result in R6c). Root members still use `openSubtreeKey` (:1880), which never reuses a dead slot. After A#0 dies, A#1 lands at a fresh key while B#0 stays alive at key 0 (R6c `respawn_key_split`). `spawnChild` also crashes on a second spawn of the same child template at that key, whether the earlier child is alive or dead (**N5**) |
| F6 DECISIONS | **Fixed** | DECISIONS.md:77-84: deadlock freedom is about parked sends. R6a `no_stuck_effect_peer` and `no_stuck_call` still hold. They now need the actor alive, because `finishWait` has a life guard (:1569) |
| F7 Delivered | **Fixed** | Deliver.lean:559-571: loss counts only while the message is still in the box, parked list or prio lane. `callTimeout` detaches without dequeuing (:1549-1558; `await_timeout_box` :7307). There is no capacity leak (the slot comes back at the callee's `recvBulk` or the refund at the seal) and no double handling (a detached request runs once, owes nothing, and `performReply` with `replyTo = none` just proceeds). Remaining: a non-call or tombstone with no transition still counts as "taken" (`deliver` :660-662) |
| F8 sealing vs terminate_stage | **Mostly fixed** | Every child is marked (`markTree`), sealing is lazy, `finishWait` and `peerData` are guarded by life (:1569, :1963), and `markShutdown` resets the phase to idle (:1064-1069). Remaining divergences: a dead supervisor makes a later child termination crash (**N6**), and a crashed world is not terminal (**N3**) |
| F9 one continuation per outcome | **Partial** | `Cont.onNotAdmitted`, `onTimedOut` and `onTimeout` (:293-303), `selectCall` :601, `finishCall_cont` :7235, and the peer timeout on `onTimeout` (`callTimeout` :1560). R6a `outcome_branches`: TimedOut arms `late`, Reply does not. But every outcome ends in the same `toState` (R6a `outcome_blind` still holds), so the typestate itself cannot record the outcome. The branches are also invisible to several LocalOk checks (**N1**) |
| F10 Msg.callId | **Fixed** | `Msg.callId` :324 is stamped in `enqueueOrPark` :748 and copied into `oweId` by `deliver` (:672-675). `performReply` :775 matches it |
| F11 onFull/onGone | **Fixed** | `Eff.trySend … onFull onGone` :79, `execRun` :1162-1176. This matches pure-stage's Queued/Full/Gone |
| F12 fall-through | **Fixed** | `TermStep.fall` gives `crashWorld` (:1243-1250), and `execRun` ends in `else crashWorld w` (:1230) |
| F13 off-roster invariant | **Harmless to defer** | It only matters for proofs (`runtimeBusy` scans the roster). `markShutdown`, `crashWorld` and `releaseWorld` touch only roster ids, and `spawn`/`spawnChild` add to the roster first. My refutations need exactly this lemma (workaround 3). It should come back in the `life = absent` form |

## Probe results (old → new)

| Probe | R5 | R6 |
|---|---|---|
| call_answered_reply_false (Fair run) | biting | still holds, kept as a regression (`R6a.call_answered_reply_false`) |
| race_point / race_timedout / race_reply | holds | holds |
| outcome_blind | biting | still holds for `toState`. Positive counterpart: `outcome_branches` |
| peerData_is_finish | biting | dead. Positive: `peer_timeout_branch`, `peer_finish_live` |
| no_stuck_effect_peer / no_stuck_call | holds | holds, with a life hypothesis (consistent with DECISIONS) |
| tombstones_exceed_capPrio | biting (unbounded) | fixed: `respawn_overflow` puts a 5th tombstone on capPrio=4 and the world crashes, in a GraphOk ∧ LocalOk ∧ prioSized design (see N4) |
| dead_sender_admitted | biting | dead. Positive: `dead_sender_refunded` (GraphOk ∧ LocalOk design) |
| member_terminate_alone / peer_supervises_nobody | biting | dead in the semantics. Positive: `terminate_marks_grandchild`, `tree_sealed`. But `tree_graph_rejected` (N2) |
| tombstone_unmatched | biting | per-template label fixed. Still biting for another parent state (`tombstone_later_state`) |
| respawn_key_split | biting | still biting for roots (`respawn_key_split`). Children are fine (`terminate_marks_grandchild`) |
| new | — | `deadlock_freedom_false` (N1), `crash_not_absorbing` (N3), `respawn_child_crashes` (N5), `dead_supervisor_crash` (N6), `branch_label_uncounted` (N1) |

## New findings

**N1 (high): sends in outcome branches bypass `sendsOk`, and `deadlock_freedom` is false.**

- **Cause.** The R6 branch lists (`onFull`, `onGone`, `onNotAdmitted`, `onTimedOut`, `onTimeout`) are checked by `effectsOk` and `callOutcomesOk`, but not by the counting checks. `sendsTo` (Semantics.lean:1591) and `pending` (:1599) count only the top level, and `pending` reads only `k.rest`. `sendsOk` (Local.lean:33) therefore does not bound branch sends.
- **Other blind checks.** `selfLabels` (Local.lean:22), and with it `prioLabels`, `prioOk` and `prioSizeFails`, does not look into branches. Neither do `replyCount`, `terminateBeforeReply`, `hasTerminate` or `noSelfSchedule` (R6a `branch_label_uncounted`).
- **Counterexample: `Helen/R6b.lean`.**
  - Setup: one permanent core A with capacity 3, ingress `Go`, and transition `Go → [peer [send A M ×4]]`. The self edge has occupancy 1. `checkBool` is `pass` and `LocalOk` and `Assumptions` hold (`bypass_graph`, `bypass_local`).
  - Run: the peer timeout fires and the branch sends four times. Three messages queue, and the fourth parks A on itself. A's mail on A is 4 against a budget of 2 (`bypass_overrun`), and the world goes quiet.
  - Result: `fairB` shows the run is Fair; `stuck_A` and `bypass_deadlock` show A is `Stuck` on `blockingSend` forever. `deadlock_freedom_false (OffIdle)` refutes the universal statement of `deadlock_freedom`.
- **Fix.** Make every counting function recurse into branches, and count the *maximum* over the outcomes of a call/trySend/peer (only one runs), plus the tail. Concretely: `sendsTo` (and so `sendsOk` and `pending`, where `pending` must also read the branches stored in the `Cont`), `selfLabels`/`cellWakeLabels`, `replyCount`, `terminateBeforeReply`, `hasTerminate` and `noSelfSchedule`.

**N2 (high): GraphOk rejects every per-peer supervisor, so the F3/F5 fixes are unreachable under the theorems' hypotheses.**

- **Evidence.** `subtreeFails` (Graph.lean:671-674, unchanged in this round) still fails "supervisor … is not a permanent core". R6c `tree_graph_rejected`: the Conn→Hand→Work tree fails `checkBool`.
- **Consequences under GraphOk ∧ LocalOk:**
  - `isChild` for a peer parent never holds, so `spawnChild` never succeeds.
  - Every `Eff.spawn` crashes the world. LocalOk allows `Eff.spawn` in member programs (Semantics.lean:1671), and in core and lone-terminable programs too, because `bulkScopeOf` does not restrict it (Local.lean:74).
  - The nested-supervisor model exists only in the semantics.
- **Stale requirements.** `subtreeFails` also still requires every member to be terminable and every subtree to have a `timeoutKills` role. The step relation no longer uses either.
- **Fix.** In `subtreeFails`, accept a per-peer supervisor of the same subtree. Drop the terminable and `timeoutKills` requirements, or justify them. Restrict `Eff.spawn` in LocalOk to `src` being the child's supervisor, which makes `spawnChild` total under LocalOk.

**N3 (med): a crashed world is not absorbing.**

- **Evidence.** `crashWorld` (:806) kills only the roster and leaves mail queued (:797-800, "a crashed world takes no further step"). But `spawn` (:1903) needs only `aliveCount < N` and never checks for a crash. R6c `crash_not_absorbing`: after the overflow crash, `spawn A` and an ingress into the new A#5 succeed while P stays dead/crashed.
- **Why it matters.** The new actors run in a world whose cores are dead: sends to the cores are dropped and calls end NotAdmitted. pure-stage ends the simulation instead.
- **Crash as a loophole.** crash is not a loophole that makes `deadlock_freedom` vacuous: R6b deadlocks without any crash. But crash is reachable in GraphOk ∧ LocalOk designs through five paths that no check rules out:
  - prio overflow (N4);
  - `spawn` misuse (N2, N5);
  - a dead supervisor (N6);
  - a child with an empty tombstone label (excluded by `tombstoneHandled`);
  - a missing template.
  So the real guarantee is "deadlock-free or crashed".
- **Fix:**
  - Add a `crashed : Bool` world flag set by `crashWorld`, and disable every action (including `spawn`, `ingress` and `stutter`'s alternatives) once it is set, or make the `Run` stop there.
  - Separately, prove a `no_crash` theorem under `prioSized`, wiring `prioSizeFails` into LocalOk, and under a spawn discipline. That keeps crash a *chosen* outcome (permanent-core terminate) rather than a hidden one.

**N4 (med): the `prioSized` bound is unsound under root respawn.**

- **Evidence.** `simultaneousTombstones` (:521) counts a core parent's children as `population` (N for a root), assuming each child instance tombstones at most once while it is alive. But `maySpawnRoot` (:1900) counts only *alive* instances, so a dead child whose tombstone is still on the lane can be replaced.
- **Counterexample.** R6c `sub_prioSized` shows `prioSized` holds and `prioSizeFails = []` at N=1 (demand 1, capacity 4). Yet `respawn_overflow` reaches a crash after five spawn/terminate cycles while P has not yet drained its lane. Fair does not prevent this, because spawn is unforced and recvPrio may come late.
- **Fix.** Either count live instances plus pending tombstones in `maySpawnRoot` (refuse a root spawn while its predecessor's tombstone is queued), or make the bound N × (respawns between drains), which has no static bound.

**N5 (med): a parent cannot restart a child.**

- **Evidence.** `spawnChild` (:1131) requires the child id to be `absent`, and a dead id is never reused. The child id is `peer child k`, so after the first child dies a parent at key k can never spawn that template again. A second spawn while the child is alive also fails. Either failure is `crashWorld` (:1212-1215). R6c `respawn_child_crashes`.
- **pure-stage.** `AddStage` uses `stage_name(&mut stage_count, …)` (mod.rs:1331-1334) and gets a fresh name every time, so a reconnecting handler is ordinary Amaru behaviour.
- **Fix.** Index children by (key, generation), or allow reuse of a dead id with a fresh incarnation. Turn the spawn failure into a branch (`onFull`-style) rather than a crash, or rule it out statically.

**N6 (med): a dead lone-terminable core supervisor turns a later child termination into a crash.**

- **Evidence.** `enqueueTombstone` (:979-993) crashes when the supervisor is not alive. That is no longer a silent drop, so the R5 silent-drop concern is fixed.
- **How the crash is reached.** `rootOf`/`maySpawnRoot` (:1893-1902) still allow root spawns of a child whose core supervisor is dead. R6c `dead_supervisor_crash` (GraphOk ∧ LocalOk):
  1. Q is a lone-terminable core supervisor. Y terminates and Q receives its tombstone.
  2. Q terminates, which marks X, and Q seals.
  3. A new Y#1 is spawned as a root under the dead Q. Y#1 terminates, and the tombstone to the dead Q crashes the world.
- **pure-stage.** This cannot happen there: children are wired by their live supervisor and removed with it (mod.rs:1507-1516). `expect_stage` panics on a missing supervisor (mod.rs:1322).
- **Fix.** Require the supervisor to be alive in `maySpawnRoot`. Or forbid lone-terminable cores as supervisors in Graph (only permanent cores or per-peer parents).

**N7 (low): Examples and Semantics both define `Deadlock.overflowDesc`** (Examples.lean:91 and Semantics.lean:7186), so neither can be imported with the other. Rename one of them.

**N8 (low): stale docs.**
- SEMANTICS.md:71 (a call to a dead target "waits in awaitReply"; it is now NotAdmitted) and SEMANTICS.md:120-126 (`killSubtree`/`plantTombstone`).
- THEOREM.md:14-19 ("a subtree kill credits it").
- WorldCrashed's doc (:1090-1091), which says "A priority-lane overflow, which leaves the actor alive, is not this state". `offerPrio` now crashes the roster.

**N9 (low): the seal lags behind pure-stage.** A marked (shutting-down) sender's parked entry stays on hosts until its seal, so a host's `recvBulk` can admit and handle it in between. pure-stage removes it inside `terminate_stage`. Fix: call `releaseOutbound` from `markShutdown`/`markTree`, not only from the seal.

**N10 (low): `localOkB` is no longer kernel-decidable** (workaround 2). Certificates now need `simp`, and `native_decide` is excluded. Fix: make `effectsOk` and its relatives structural (for example, a mutual `effsOk`/`effOk` over `Eff`/`List Eff`) so that `decide` works again.

## Verdict

**No go.** There are two high findings:
- **N1:** `deadlock_freedom` is refuted (modulo `off_idle_reachable`) by a design that passes checkBool, LocalOk and Assumptions.
- **N2:** GraphOk excludes the new supervision model.

F1, F2, F6, F7, F10, F11 and F12 are fixed. F3, F4, F5 and F9 are partial. F8 is mostly fixed, and deferring F13 is harmless.
