# Helen: review of snapshot/lean-r5-wip @ 25fc0d224 (round 8)

Fri 20 Nov 2026, 15:55 CET. Read-only: no pushes, no comments. Worktree: /workspace/lean-review-25fc0d (detached).
I did not review the tombstone bound or restart discipline (N13), as instructed.

## 1. Build and axioms

- `lake build Deadlock.Semantics Deadlock.Local Deadlock.Graph Deadlock.Examples` finished with EXIT 0 in 12.8 s (build.log). It printed 168 warning lines and no errors. I reused `.lake` copied from the e5f48c worktree.
- A grep for `sorry|native_decide|ofReduceBool|implemented_by|extern|unsafe` over Basic, Graph, Semantics, Local, Examples, Occupy and every Helen/*.lean file found **nothing**.
- `Helen/AxAll8.lean` runs `#print axioms` on all 411 theorems in the green files. The awk generator missed the 5 `@[simp] noteStale_*` lemmas, so I added those by hand.
  - Every result is a subset of {propext, Classical.choice, Quot.sound}. 66 of them use Classical.choice.
  - None depends on sorryAx or ofReduceBool.
- The new R8 probes depend on `[propext]` only. R8Search.lean and R8fuzz.lean contain only `#eval` and `partial def` search code, with no theorems.
- `Rank.deadlock_freedom` (Rank.lean) is unchanged and still red.

## 2. Flip audit (branch Helen/R7a-d vs my originals in lean-review-e5f48c)

I ran all four branch files. Every statement checks, and every axiom set is [propext] (R7b `reporter_gap` adds Quot.sound).

| File | What changed | Honest? |
|---|---|---|
| R7a | C's capacity went from 2 to 3. They added `ingC "miss"` and a call edge from `miss`, so `call_local` still holds under the path reserve (the TimedOut path now pays its landing floor). `orig_outcome_blind_holds_by_choice` and `orig_branch_label_uncounted_refuted` are unchanged. They added `replies_per_path` (N14). | Yes. The design was tuned only so that the positive example stays LocalOk. The point of R7a (outcome-visible counts) is untouched. |
| R7b (N11) | `landDesc`/`landImpl`/`LI` are byte-identical. `land_local : LocalOk LI` became `localOkB LI = false`. They added `land_reserve` (pathReserve 4 > floor idle 2) and `land_gate` (the 4th action, the ingress, is refused). The Fair-run scaffold and `deadlock_freedom_false` were removed. | Yes. The original design is now rejected by `LocalOk`. I re-proved it independently in `R8b.orig_land_rejected` (`¬ LocalOk LI` by `unfold LocalOk; decide`). |
| R7c | They renamed refuted→crashes. Root respawn is no longer refused, consistent with N13 being out of scope. `dead_supervisor` now has a non-vacuous prefix (fixes N18). Tombstone labels are now `#gen`. They added `pool_sized`, `pool_slots` and `old_mail_charged`. | Yes, with one caveat: `old_mail_charged` runs on `mailImpl`, which is **not** LocalOk (`R8c.mail_not_local`). The file does not claim it is, but it does not exercise a valid design either. |
| R7d (N12) | `pcDesc`/`pcImpl`/`PI` are byte-identical. **`pc_local : LocalOk PI` is kept.** `pc_assumptions`, `pc_pending_gap`, `pc_overrun`, the Fair-run scaffold and `deadlock_freedom_false` were removed. They added `pc_pending` (pending = 2, and the 5th action, an ingress, is refused) and `own_on_timed_out`. | Honest, but **not the requested flip**. See below. |

**N12 is not rejected by LocalOk.** My original `pcImpl 4 0 2` still passes `LocalOk` (`R8b.orig_pc_still_local`). The fix lives in the runtime ingress gate: `tokenHold` reserves `own + reserve(onTimedOut)` while the call is parked, so the original trace dies at action 5 (`R8b.orig_pc_trace_refused`).

I think this is sound, because ingress is the environment's declared contract (`ingressLegal`) and the gate is what enforces it. I checked it exhaustively:
- **R8b.lean:** a bounded DFS of every action interleaving, to depth 16 (105 distinct states), finds no self-park and no box overrun for `PI`.
- **Parameter sweep:** the same holds for all 28 LocalOk variants `pcImpl capA∈1..6 capB∈0..1 k∈0..3`.
- **landImpl:** no variant `landImpl cap occW occM` passes LocalOk at all.

THEOREM.md should still say this explicitly: the Rust ingress adapter must respect the token reserve, not just mailbox room (see N24).

## 3. Fix table

| # | Verdict | Evidence |
|---|---|---|
| N11 path reserve | **Fixed** | `pathReserve`/`effReserve` (Semantics.lean:1832-1852) give each branch its own landing state via `focus`, and nested branches recurse. `[]` pays `landFloor` of the landing state (:1826). `sendsOk` (Local.lean:50-53) checks `pathReserve ≤ floorState(from)`. The gate (`tokenHold` :1873-1890, `receiveIngress` :2011) uses the same function for every open phase. **Attacks:** <br>(a) **Chain of branches:** recursion through `focus`. The runtime `pickState` (`execRun`) does the same. <br>(b) **Parked continuation:** `tokenHold` `.parked _ false k` uses `pathReserve(contAt k)`. <br>(c) **Self-loop:** from = to, so the sends must fit inside floor(from) − floor(to) = 0, and are rejected. <br>(d) **"Worst program at the landing state":** the landing floor is static, and the landing state's own transitions are checked separately against that floor. That makes it inductive; nothing needs maximising. <br>**Fuzz** (R8fuzz.lean): 60 000 random single-core designs with ingress, self-sends, nested peer/call/trySend branches and random landing states. 4 514 passed GraphOk+LocalOk. A depth-16 DFS of each found **0** self-parks and **0** overruns. |
| N12 parked-call pending | **Fixed (by gate, not by LocalOk)** | `pending` (:1857-1868) and `tokenHold` take the max over rest, NotAdmitted, own+TimedOut and Timeout. **Attacks:** <br>(a) **Parked trySend:** a trySend never parks (Full takes the branch). A parked blocking send reserves `pathReserve(rest)` after its own message was charged at park. <br>(b) **awaitReply:** reserves max(rest, onTimedOut). The own message is already in the target's box and already charged. <br>(c) **Nested calls in a branch:** the recursion is via `focus`. <br>Minor: the parked-call `own` is counted twice, since it was charged at park time and is counted again in `tokenHold`. This is conservative, and `own` is always 0 for the self-template `tokenHold` the gate uses. It only matters if the proof states the invariant as `tokens ≥ tokenHold` for all dst (N23). |
| N5 pools | **Partially fixed** | `Template.slots`. `spawnChild` (:1295-1321) gives a core one child per free slot, as `(slot, maxGen)`. `population` (:537) is slots under a core and pop(sup)×slots under a per-peer parent. `simultaneousTombstones` (:568-577). The core spawn path is reachable under GraphOk+LocalOk (`R7c.pool_sized`, `pool_slots`). **But:** <br>(1) **A slot is reused before the old child seals.** `freeSlot` (:1280-1287) uses `aliveAt`, so a `shuttingDown` occupant frees its slot (`R8c.slot_reused_before_seal`: gen 0 at life 2 while gen 1 is born). See N21. <br>(2) **The core cannot address its pool** (N20). <br>(3) **A pool under a per-peer parent is GraphOk, and its population is multiplied, but it can never be born.** LocalOk rejects the spawn, and without LocalOk `spawnChild` returns `none` and the roster crashes (`R8c.nested_pool_unbirthable`). So "product along the tree" is defined but unreachable beyond core→pool→per-peer children. <br>Prio sizing: the lane counts `slots` tombstones per pool. With reuse-before-seal, one slot can have two tombstones outstanding; this is part of the N13 question, which I did not judge. |
| N14 replies per path | **Fixed** | `pathReplies`/`repliesMatch` (Semantics.lean:2424-2441). A branch replaces the tail. Used at Local.lean:162-163 and in the reporter at :449-454. `R7a.replies_per_path` checks. |
| N15 generation labels | **Cosmetic only** | `tombstoneLabel` = `base#gen` (:1090-1097). But `findDeliver` (:518-524) falls back to the base label, and `tombstoneHandled` requires a base handler in every state. So a stale `dead/Hand#0` runs the same `dead/Hand` handler as a current tombstone (`R8c.stale_runs_base_handler`). The handler has no way to see the generation, and it cannot have one transition per generation because generations are unbounded. An unmatched stale tombstone cannot happen: the base handler always matches. This is no longer unsafe, but the parent still cannot tell a stale death from a current one (N22). |
| N16 old-generation mail | **Charge fixed, credit wrong, so not fixed** | `withKeyTokens` = `budget − queuedFromKey` (:739-740), counted over box and parked mail of every generation (:726-735). But `creditSender` (:427-428) and the seal refund credit `m.sender`, which is the **dead** id. The live generation never gets its tokens back. It also truncates in `Nat`: `R8c.nat_truncation` queues 2 > budget 1, and gen 2 gets 0. This leads to a valid design in which a restarted stage is deaf to ingress forever (N21). |
| N17 reporter | **Fixed** | `floorGap`/`programGap` take `tr`/`BranchAt` (Local.lean:414-424). `localIssues LI` = ["…needs 4 slot(s) toward A and idle holds 2"], and `R7b.reporter_gap` checks. Nit: for a per-peer parent spawning a pool, the reporter says "spawns a stage it does not supervise", which is misleading. |
| N18 vacuous conjunct | **Fixed** | R7c `dead_supervisor_refused` now asserts that the prefix `isSome` and is not crashed, and that the spawn is `none`. |
| N19 crash list | **Mostly fixed. The list is incomplete but harmless.** | THEOREM.md:19-38 lists: permanent-core terminate, self-schedule overflow, cell-wake overflow and tombstone overflow, and says spawnScope rules out the `Eff.spawn` crash. Every `crashWorld` site: <br>:928 `offerPrio` (cell wake, listed) <br>:1134 `enqueueTombstone`: full lane (listed), **parent not alive** and **empty label** (not listed) <br>:1374 self-schedule (listed) <br>:1389 `Eff.spawn` → none (ruled out by spawnScope, stated) <br>:1399 permanent core (listed) <br>:1408 terminate fall-through, e.g. a lone terminable with a parked call (**not listed**) <br>:1409 missing template (**not listed**) <br>The `TermStep` wrappers are at :1418/:1423. <br>I believe each unlisted site is unreachable under GraphOk+LocalOk. The parent is alive whenever a child is, because markTree marks children and supervisorLive refuses roots. The label is non-empty by tombstoneHandled. Calls to a lone terminable are rejected by permanentTarget. But THEOREM.md neither lists these sites nor argues it. |
| maySpawnRoot refusal | **Gone. No smuggled refusal of the tombstone kind.** | `maySpawnRoot` (:2211-2213) = perPeer ∧ slots=0 ∧ rootOf ∧ aliveCount<N ∧ supervisorLive. `tombstoneRoom` (:2201) is now dead code, with no caller anywhere. The silent no-ops that remain: <br>a full pool (`freeSlot = none` → `some w`, :1307) <br>a live per-peer child (:1312) <br>a dead parent (:1318) <br>a dead core supervisor (`supervisorLive`) <br>The last two match pure-stage: a dead stage spawns nothing. The full-pool no-op models connector.rs's fixed worker count. **The real smuggled refusal is N21:** the leaked tokens make the ingress gate refuse a restarted stage forever. |

## 4. New findings

**N20 (med): a pool is unaddressable by its own core and by anyone outside it.**
- `route` from a core to a per-peer role has no key, so it fails (`noteStale`). `R8c.pool_route_fails` shows the job lands in `failures` and W's box stays empty.
- `LocalOk` also rejects the reliable send (`R8c.pool_unaddressable_local`). `permanentTarget` allows reliable sends to a terminable target only within the same subtree.
- So a pool child can receive only ingress. This cannot model the connector (manager/connector.rs:60-70), whose manager sends work to its workers.
- Fix: let a core route to `(pool, slot)` explicitly, for example `Eff.send` with a slot selector, or a reply-addressed handle returned by the spawn. Count that edge with per-slot occupancy.

**N21 (high): a restarted generation can be permanently refused ingress, and this depends on scheduling.** High because it removes Rust behaviours from a valid design, so the theorem silently says nothing about those runs, and because it breaks the token invariant the proof repair needs. Valid design `R8c.starveImpl`: GraphOk ∧ LocalOk (`starve_ok`).
- R0 sends itself 2 `Self` and terminates. R1 is spawned while R0 is still `shuttingDown`, which `openSubtreeKey`/`freeSlot` allow because they check only `alive`.
- `withKeyTokens` charges R1 for R0's 2 queued messages (tokens 1 of budget 3). R0's seal then refunds those 2 to the dead R0.
- R1 holds 1 token, but the gate needs `tokenHold + 1 = 3`. Every action from that world is disabled (`starved_frozen`), and the ingress is `none` (`restart_starved`).
- If R1 is spawned after the seal, it gets full tokens and accepts ingress (`order_dependent`).
- Rust has no such state: a new stage has an empty mailbox. This removes behaviours, which weakens the theorem (runs that could deadlock through R1 are excluded). It also breaks the `tokens + outstanding = budget` invariant the proof needs.
- Fix: credit to the live generation of `(name, key)` (`creditSender` via `findLive`). Or simpler: since the old generation's self-mail is refunded at seal anyway, compute `queuedFromKey` only over hosts that are alive and ≠ the key's own template, and credit the key, not the id. Also free a slot or key only at `dead` (not `shuttingDown`), or prove the charge is returned.

**N22 (low): stale tombstones are still indistinguishable to the handler** (N15 is cosmetic). Fix one of three ways:
- deliver a stale generation (gen < newest gen at that key) to a distinct `base/stale` label that has its own declared handler;
- drop it, mirroring `skip_if_terminated`;
- or model the Rust comparison (`ConnectionDied` carries the id) as a guard.

**N23 (low, proof hazard): `tokenHold` for a parked call counts `own` after it has already been charged.** As stated, `tokens ≥ tokenHold` is not inductive across the park step whenever `tname target = dst`. The gate only uses dst = self, so `own` = 0 in practice. State the invariant per dst with `own` excluded, or drop `own` from the parked case.

**N24 (low/doc): N12's safety rests on the ingress gate, an environment obligation.** LocalOk accepts `pcImpl 4 0 2`. If a Rust ingress adapter checked only mailbox room, the original R7d trace would be a real self-park. THEOREM.md should name this obligation next to `ingressLegal`, or Assumptions should state it.

**N25 (low): unreachable population and reporter text for pools under per-peer parents.** GraphOk should reject `slots≠0` under a per-peer supervisor, matching `spawnChild`/`spawnEffect`. The reporter should say "slots must be 0 under a per-peer parent".

**N26 (low/doc): the crash list in THEOREM.md omits three `crashWorld` sites:** the tombstone to a non-alive parent or with an empty label, the terminate fall-through, and the missing template. Add each with its one-line unreachability argument, or prove one lemma that they are unreachable under LocalOk.

**Decide performance:** no problem. Every probe file checks in under 4 s, and the full green build takes 12.8 s.

**Refutation hunt:** I found no refutation of `deadlock_freedom`.
- Exhaustive bounded search on the original N11/N12 designs and their parameter variants.
- 4 514 random LocalOk designs from the fuzzer.
- The N21 starvation is a lost behaviour, not a `Deadlock` (the actor is idle).

## 5. Verdict

**NO GO** (narrowly). The one blocking item is N21; everything else is low.

N11 and N12 (the round-7 highs) are fixed. I found no deadlock refutation. Nothing outside the tombstone question refuses a root spawn.

N21 is a restart-time token leak that permanently silences a valid, restarted stage. It is scheduling-dependent, and it falsifies the token invariant the pending proof will need. It and N20 (pool unaddressable) sit in exactly the code this snapshot added for N5 and N16. Once N21 is fixed (credit the live generation, or free slots and keys only at `dead`), this becomes **go (conditional on the tombstone decision)**. N20 can follow as an expressiveness item, unless pools are meant to model the connector now.

## Workarounds and disclosures

- **R7b and R7d definitions:** copied verbatim into R8b.lean, because Helen files are not a lake library. The R7c definitions were copied into R8c.lean, with the branch's theorems renamed `r7_*` and re-checked.
- **Search code:** the explorer and fuzzer (`R8Search.lean`, `R8fuzz.lean`, and section S of R8b) are `#eval`-only and use `partial def`. Their results are evidence, not proofs. Every concrete trace I rely on is re-proved by `decide`.
- **String results:** `localIssues` and other string-built results were read via `#eval`.
- **AxAll8.lean:** generated by awk, plus 5 `@[simp]` lemmas added by hand.
- **Fair-run scaffold:** I attempted no Fair-run construction this round because I found no deadlock trace. The OffIdle hypothesis was therefore not needed.
- **`.lake`:** copied from the previous worktree to speed up the build.
