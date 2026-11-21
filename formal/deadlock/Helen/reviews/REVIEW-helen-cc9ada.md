# Helen review, round 12: `snapshot/lean-r5-wip` at `cc9ada5ce`

Reviewed 2026-11-21, 08:56–09:12 CET. Baseline is round 11 at `ceb6673ab`.

The unpacked tree is byte-identical to `git archive cc9ada5ce formal/deadlock`: `diff -rq` against a fresh archive in /tmp/cc9 found no differences. Probes are in `HelenR12/` and are local only.

**Commits since ceb6673ab** (CET):

| Commit | Time | Change |
|---|---|---|
| c5a3407d5 | 05:59 | label nonempty; `self_schedule_fits`, `cell_wake_fits` |
| 1af443cae | 08:22 | N39 |
| bf1063118 | 08:26 | pace added |
| f4818759d | 08:32 | pace dropped |
| 9bab053e6 | 08:40 | slot mail |
| 857732702 | 08:42 | drained-signal doc |
| cc9ada5ce | 08:55 | dead root keeps its population slot |

The pace is fully gone. `git diff bf1063118^ f4818759d` is empty, and no "pace" or "per second" text remains.

**Decision provenance** (DECISIONS.md:179-331). I cannot verify the quotes themselves, but the timestamps are consistent:
- The "08:04 CET call" precedes 9bab053e6 (08:40).
- The "08:06 call" precedes 857732702 (08:42).
- "08:44 CET, his own answer" precedes cc9ada5ce (08:55).
- The N39 quote carries no time.

## 0. Build (per module, `timeout 600`)
- **Green:** Basic, Graph, Semantics, Local, Occupy, Safety, Tomb, Compat, Failures, Examples, Counterexample, Orphan, Outlive.
- **Red:**

| Module | Errors | Note |
|---|---|---|
| FairRun | 60 | expected per DECISIONS:220-225 |
| Proof | 53 | |
| Theorem | 53 | |
| Intra | 11 | |
| RunInv | 8 | |
| Occ | 8 | via RunInv |
| Json | 6 | |

No `sorry`, `native_decide`, `implemented_by`, `extern` or `unsafe` appears in the green modules.

## 1. Q1: are the rules faithful to the decisions, and are the guards exercised?
**N39: core terminate crashes the node.**
- `execRun` `.terminate` (Semantics.lean:1700-1720) gives `crashWorld` for every `multiplicity = .one`. This is the only terminate site.
- A callTimeout continuation reaches it through the same `exec`.
- Cores are never children: `Hold.rooted`, and `dropDescendants`/`abortChildren` only follow `isChild`. So no supervisor kill reaches a core.
- `shutdownActor` and `terminateStage` are called only from the per-peer branches (:1712-1718) and on recorded children (:1484, :1492).
- `apply` returns `none` once `w.crashed` (:2616-2618), so crashed is absorbing.
- `coreFlagFails` (Graph.lean:785) rejects a terminable core.
- LocalOk now allows terminate and reliable targets for any core (Local.lean diff: `bulkScopeOf`, `transitionOk`, `permanentTarget`). This is consistent with the decision.

**Slot mail (9bab053e6) and population (cc9ada5ce).**
- **Definitions** (Semantics.lean:1513-1565):
  - `actorHoldsSlotMail`/`actorHoldsSubtreeMail` read the core's **box**, its **prio lane**, and **parked** entries, matching `p.sender` or `p.msg.sender`.
  - "Consumed" therefore means dequeued by `recvBulk`/`recvPrio`, or the parked entry leaving that core.
  - A call request from a member is box mail. Once it is dequeued, a reply still owed to the dead caller is not mail.
  - Parked sends of a dying sender are dropped at the mark (`releaseOutbound` in `markShutdown`, :1408) and at the seal, so they never enqueue after death.
- **Root population.** `rootOutstanding` (:2512) counts a root that is alive, shutting down, has its tombstone queued, or has `slotMailHeld`. `loneOutstanding` (:2527) counts a root that is alive or has `slotMailHeld`. `maySpawnRoot` (:2540) requires `< N`.
- **Pools and children.** Pools go through `freeSlot` and `slotRespawnBlocked` (:1580-1589, :1612). A per-peer child uses `slotRespawnBlocked` (:1621).
- All of this matches DECISIONS:226-331 as written.

**Each guard exercised on a GraphOk + LocalOk design, blocking and then unblocking:**

| Guard | Probe | Blocked | Unblocked |
|---|---|---|---|
| `loneOutstanding` | `Guards.lean` (Outlive, N=2) | after two roots: count 2, `spawn` disabled | H then K drain the key-0 `M`s: count 2→1, spawn enabled; then 0 |
| `rootOutstanding` | `Guards3.lean` (R under core S) | both tombstones consumed, count still 2 from core mail | same drain: 2→1, spawn enabled; then 0 |
| per-peer child `spawnChild` | `Guards2.lean` (a): R→C→X, X non-terminable, mails core H | C@0.0 terminated, `slotMailHeld` true, `exec R` leaves C@0.1 absent | after `recvBulk H`, `exec R` births C@0.1 |
| pool `freeSlot` | `Guards2.lean` (b): M→W(pw)→Y, Y mails H | `freeSlot = none`, W@0.1 absent | after `recvBulk H`, W@0.1 is born |

Only **non-terminable** descendants can leave core mail behind. Terminable members are confined to their subtree (`bulkScopeOf`).

**Lone root, shutting down, with or without mail:**
- Gen 1 stopped before R@1's seal (R@1 life 2, with core mail) is counted: `loneOutstanding = 2`.
- A root shutting down with no core mail (`noMail`) is not counted: 0, spawn enabled.
- That matches DECISIONS:316-318. It is harmless: a shutting-down actor cannot send, and its parked sends were dropped at the mark.

**Vacuity:** none. Every guard is reached and cleared in a reachable run.

## 2. Q2: E4 variants
**Closed:**
- **Pool hosts outside the subtree** (`PoolE4.lean`):
  - reliable mail to a pool child of another core is rejected by `permanentTarget` (Local.lean:308-316);
  - superseding edges must be non-blocking cell writes.
- **Parked sends after death:** dropped at the mark.
- **Descendants sealed by terminate:** their mail is counted, being subtree members at that key.
- **Cross-template keys:** `isMember` is subtree- and key-exact.
- **Generation wraparound:** generations are `Nat`.

**Re-runs:**

| Probe | Result |
|---|---|
| E1 (`G.lean`) | G@0.1 born, no crash |
| E2 (`E.lean`) | the second root is now refused |
| E3 | rejected by GraphOk |
| E4 (`D.lean`) | the run is refused (`none`), as is the branch's `outlive_refused` |
| Branch R6a–R8c | exit 0 |
| `NV.lean` | passes after one API change: dropped the label argument |
| R10fuzz `kImpl0` (depth 12, 37,437 states) | no crash |
| R10fuzz `gImpl` (depth 18) | no `orphanBlock` |
| `fuzzA` (450 seeds, both modes, 313 s each) | 43 valid, hits [] |

**Survives: N43.** Mail on a **live non-core member** of the same subtree key is not slot mail, so it outlives respawns.

`ChildSub.lean` (N=1):
- **Design** (render "pass", `localIssues` [], `l1 A = l1 B = true`): root R births two non-terminable children A and B plus a terminable child X. X sends `M` to A and to B (siblings, allowed), then terminates. R's `dead/X` handler re-spawns X. A and B each send `P` to the other on `Ping`.
- **Why respawn is never blocked:** X's mail sits on A and B, which are per-peer, so `slotMailHeld` is false. Respawn is blocked only while the slot is occupied or its tombstone is queued.
- **Run:**
  1. Generations X@0.0 through X@0.3 each fill one place in A and in B.
  2. X@0.4 parks on A.
  3. B dequeues Ping and parks on A.
  4. A dequeues Ping, which admits X@0.4's `M`.
  5. X@0.4 fills B.
  6. A parks on B.
- **Final state, action 56:** A `parked→B`, B `parked→A`, both boxes 5/5. A's box holds `M` from X@0.0, X@0.1, X@0.2, X@0.3 and X@0.4. No `recvBulk`/`recvPrio`/`exec`/`finish`/`callTimeout` is enabled for any roster id. `runtimeBusy = false`, and only stutter is enabled.
- **This is a real deadlock in a checked design at cc9ada5ce.** The same file gives the same result at ceb6673ab, so it is pre-existing and part of the N32 class.

`PoolSub.lean` is the same pattern inside a pool subtree: core M with pool children A, B and C, all in subtree `pw`. C's child X mails A and B, C terminates, and M re-spawns C. At N=1 it ends with A `parked→B`, B `parked→A`, both 5/5, nothing enabled.

## 3. Q3: can a blocked slot cause a deadlock?
Not by itself:
- A blocked `spawnChild` returns `some w`, a no-op, and the program continues.
- A refused root `spawn` disables only the environment's `spawn` action, which is not in `runtimeBusy`.
- No actor ever *waits* on a slot. A send or call to an absent per-peer target is `route = none`, which becomes `noteStale` and a failure continuation, not a park.
- A core can reliably target only a pool child of its own (`permanentTarget`). If that child is dead and not respawned, the core gets `noteStale`, not a park.
- A core waiting on a reply from a respawn has a deadline (`callTimeout`).

The scenarios you listed reduce to an l1-checked cycle between live actors, or to a timeout. I found no deadlock caused by the guards. The N43 deadlock comes from the guard **not** blocking.

## 4. Q4: did any green statement get weaker?
Statements were diffed against ceb6673ab:
- **`no_tombstone_overflow`** (Tomb.lean:11650): stronger. The `label ≠ ""` hypothesis is gone, replaced by `tombstone_label_ne` (:11518) plus `wire_reach`. **N40 fixed.**
- **Unchanged:** `hold_reach` (:10674), `Side` (:9024), `Reachable` (Semantics.lean:2672, still init plus `apply` on every `Action`), the `Action` type, and `prioSized`.
- **LocalOk changed only for cores.** Terminate and reliable targets are allowed. That weakens a hypothesis, so it strengthens the theorems.
- **New since round 11** (c5a3407d5): `self_schedule_fits` (:11572) and `cell_wake_fits` (:11597). Both take GraphOk + LocalOk + Reachable and conclude label-deduplicated or `prioLoad < capPrio`. **N41 fixed.**
- **Axioms:**

| Declarations | Axioms |
|---|---|
| `no_tombstone_overflow`, `hold_reach`, `reach_pack`, `hold_step`, `side_step`, `self_schedule_fits`, `cell_wake_fits`, `tombstone_label_ne` | propext, Classical.choice, Quot.sound |
| `side_init`, `wire_reach`, `outlive_checked` | propext, Quot.sound |
| `outlive_refused`, `orphan_respawn` | propext |
| `Side` | none |
| my `nv_subtree_seal`, `nv_pool_seal` | propext, Classical.choice, Quot.sound |

- **N42 partly open.** `markTree` is removed. Helen/AxAll and AxAll8 still fail on `isChild_peer`. `abortDesc`, `abortActor`, `admitDead` and `shutdownDesc` (Semantics.lean:1377-1446) are now unused by the step relation (N44).
- **`outlive_refused`** proves only refusal. The re-enable is my Guards probe.

## 5. Findings
| # | Sev | Where | Finding |
|---|---|---|---|
| N43 | **high** | Semantics.lean:1522-1565 (`actorHoldsSlotMail`/`slotCoreMail`/`subtreeCoreMail` read only `.core` hosts); Local.lean:308-316 and `memberProgramOk` (sibling sends allowed); DECISIONS:229-232 | A terminable child's mail to a **live sibling**, or to a pool child in the same pool subtree, is not slot mail. The child is re-spawned freely, and the dead generations' mail exceeds the `l1` sizing. The result is a reachable deadlock in a GraphOk + LocalOk + l1 design (`ChildSub.lean`, `PoolSub.lean`). The guard is faithful to the decision's wording ("sent to a core"), but the decision's own rationale (channel mail cannot be removed) applies to every surviving receiver. The fix needs Roland: either hold the slot on mail at **any** live host that is not sealed with the slot, with the drained signal from every receiver, or have LocalOk forbid a respawnable member from sending to a longer-lived non-core host. |
| N44 | low | Semantics.lean:1377-1446; Helen/AxAll(8).lean | `abortDesc`, `abortActor`, `admitDead` and `shutdownDesc` are dead code. The AxAll probes are stale. |
| N45 | info | Semantics.lean:1202 `tombstoneLabel` | Tombstones from roots at different keys share a label (`dead/R#0` twice on S's lane in Guards3). Counting uses the sender, so nothing breaks. A handler cannot tell the keys apart by label alone. |
| N46 | info | DECISIONS.md:179-331 | I can't confirm the quoted decisions, but their timestamps precede the commits. N39 has no time. |

**Status of earlier items:**

| Item | Status |
|---|---|
| N32 | E4 itself refused; class open as N43 |
| N39 | resolved by the decision; implementation verified |
| N40 | fixed |
| N41 | fixed |
| N42 | partly fixed (AxAll stale, N44) |
| N31, N33–N38 | unchanged and fixed |

## 6. Verdict
**NO-GO** for the headline repair. The semantics implements the stated decisions faithfully, and the green set got stronger, not weaker. But N43 is a reachable deadlock in a checked design, so the deadlock-freedom headline would be false as stated. It is the N32 class through non-core receivers, and it needs a decision on scope.

## 7. Workarounds
1. Copied `.lake` from ceb667.
2. Built per module, because the default target is red.
3. Verified the unpacked tree against `git archive` from my ab612c clone, after a `git fetch`. The unpacked directory has no `.git`.
4. Copied probes from HelenR11 into HelenR12/.
5. Changed NV for the API: dropped the label argument and added an Outlive import for the axiom prints.
6. Wrote new probes: PoolE4, PoolSub, ChildSub, Guards, Guards2, Guards3. They import the library modules Outlive and Orphan.
7. Ran ChildSub once in the ceb667 tree, in a temporary `HelenR12x/` directory that I then deleted.
8. Capped every run with `timeout 600`.
9. pure-stage was not re-read this round. The N39 citation is from round 11.
