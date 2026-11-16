# Adversarial review: `formal/deadlock` at rkuhn-bot/amaru@908593cb6 (branch experiment/lean-deadlock)

Reviewer: Helen. This review only read code. Nothing was pushed or commented on, and no one was contacted.
Source: `git fetch origin experiment/lean-deadlock` in /workspace/amaru-research/repo. It succeeded on the first try, with no TLS error and no workaround. The tree was extracted with `git archive 908593cb6 formal/deadlock` to /workspace/lean-review-908593/.

## Build

- elan was installed from the official elan-init.sh to ~/.elan. The toolchain is leanprover/lean4:v4.35.0 (Lake 5.0.0).
- `lake build Deadlock` completed successfully: 22 jobs, about 25 s. There were only linter warnings (unused simp args, simpa→simp). Log: /workspace/lean-review-908593/build.log.
- No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `extern` appears in the sources. The build log shows 0 "declaration uses 'sorry'" messages.
- `#print axioms`, run from Deadlock.lean:156–159:
  - `below_idle`, `never_stuck`, `deadlock_freedom` and `cell_fresh` each depend only on [propext, Classical.choice, Quot.sound], as claimed.
  - `native_decide` appears only in Deadlock/Examples.lean, in the checker regression tests (`safe_pass` etc.). It is not on the path to the main theorems.

## Verdict (one paragraph)

**No. The two headline theorems are true for a trivial reason.**
- The model is a closed system. The initial world is quiescent: every actor is idle with an empty mailbox.
- No action introduces work. There is no peer/ingress input, no initial program and no timer. So no send, call, effect or cell write can ever happen.
- I proved this mechanically: `Review/Vacuity.lean` gives `¬ Deadlock ρ ∧ CellFresh ρ` for **every** `Impl`, every `N` and every `Run`. It uses no `LocalOk`, `GraphOk`, `Assumptions` or `Fair`.
- In fact `Run I N` is empty: once at most N spawns per template have happened, no action is enabled.
- The per-step invariants are still real work. `step_inv`, `OccInv`, `CallTagInv` and `inv2_reachable` are stated over arbitrary worlds satisfying the invariant. The height/FIFO-position induction (`below_idle`: `Nat.strongRecOn` on residual height, plus `phaseFuel` and `parkIndex`) is a genuine well-founded argument. It does not exploit the vacuity.
- So most of the proof should survive once the model gets an environment. What it currently "proves" about Amaru is nothing.
- Independently of that, the model cannot express Amaru's per-peer subtree. Every per-connection stage both sends and terminates, and `mux` is a terminable call target. So even a non-vacuous version would apply only to a network Amaru is not.

## Findings, ranked

### F1 (fatal). The model has no stimulus, so `Deadlock` and `CellFresh` are trivially true and `Run` is empty

Lean:
```lean
-- Semantics.lean:479-485
inductive Action where
  | recvBulk (s : InstId) | recvPrio (s : InstId) | exec (s : InstId)
  | finish (s : InstId) | spawn (template : String)
-- Semantics.lean:504-508  initActor: phase := .idle, box := [], prio := [], parked := []
-- Semantics.lean:472      spawn:     phase := .idle, box := [], prio := [], parked := []
```

Why this vacates the claim:
- `receiveBulk` needs a non-empty box or parked list (:263–284). `receivePrio` needs a non-empty `prio` (:288–289). `execHead` needs `.run` (:455–457). `finishWait` needs `awaitEffect` or `awaitPeer` (:460–463).
- `readCells` only touches `cell` and `observed`.
- So "every actor idle with empty lanes" is invariant, and the only applicable action is `spawn`.
- `waitKind` is therefore always `none`, so `¬Deadlock` holds. No cell value ever changes, so the `CellFresh` premise `value < value'` never holds.
- `spawn` is capped by `aliveCount w template < w.N`, and nothing ever dies. After at most N spawns per template no action is enabled, so no infinite `Run` exists. This last step is argued, not mechanised.

Mechanised counterexample. It is in /workspace/lean-review-908593/formal/deadlock/Review/Vacuity.lean and checks with `lake env lean`:
```lean
theorem vacuous (I : Impl) (N : Nat) (ρ : Run I N) : ¬ Deadlock ρ ∧ CellFresh ρ
-- 'Deadlock.Review.vacuous' depends on axioms: [propext, Quot.sound]
```
Its key lemmas are `quiet_init`, `step_quiet` (every applicable action from a quiet world is `spawn`, and the result is quiet with the same cell values) and `run_quiet`.

Fix:
1. Add environment actions:
   - `deliverPeer (id) (label)`, i.e. ingress into a declared `ingress` edge with its `ingressLegal` bound. This finally gives `ingressFails` a semantics.
   - Optionally a `tick`/timer action.
   - Optionally an initial program per template (`initial : Cont`).
2. Add a sanity theorem that rules out this class of bug: `∃ I N ρ, LocalOk I ∧ GraphOk I.desc ∧ Fair ρ ∧ ∃ i s, waitKind ((ρ.cfg i).st s) ≠ none`. For example, take one of the JSON examples with programs and give a concrete fair run, as a lasso.
3. Re-prove the new action's preservation cases for `Inv`, `OccInv`, `CallTagInv`, `TermOk` and the lane invariant.

### F2 (critical). `Run` is infinite with no stutter, so global deadlock is excluded by definition

Lean:
```lean
-- Semantics.lean:523-528
structure Run (I : Impl) (N : Nat) where
  cfg : Nat → World
  act : Nat → Action
  ...
  valid : ∀ i, apply I (act i) (cfg i) = some (cfg (i + 1))
```

Why:
- A world where no action is enabled has no `Run` through it.
- The classic total deadlock is exactly such a world. Example: A is parked on B's full box, B is parked on A's full box, and nobody is idle with mail.
- So it is never a counterexample to `deadlock_freedom`. Only *partial* deadlocks that coexist with an infinite stream of other steps can be.
- This survives F1's fix unless the stimulus is always enabled.

Counterexample sketch, after F1 is fixed with a bounded ingress:
- Cores A and B have capacity 1, and A–B blocking send edges are wrongly discharged, for instance by a buggy `l1`.
- Ingress puts one message into each. Each handler sends to the other twice, both park, and nothing is enabled.
- No infinite run extends that prefix, so the theorem says nothing.

Fix (either):
- Quantify over *maximal* executions, finite or infinite. Deadlock is then "a finite maximal execution ends with some live actor in a wait, or an infinite one has `Stuck`".
- Or state a safety form over `Reachable`: `∀ w reachable, ∀ s waiting, ∃ w' reachable from w with s not waiting`. The safety form also avoids needing Fair to be satisfiable.

### F3 (high). `Fair.bulk` is stated on `CanReceive`, not `Enabled`, so it can be unsatisfiable exactly on deadlocking runs

Lean:
```lean
-- Semantics.lean:540-542
bulk : ∀ (s : InstId), (∀ i, ∃ j, i ≤ j ∧ CanReceive (ρ.cfg j) s) →
    (∀ i, ∃ j, i ≤ j ∧ ρ.act j = .recvBulk s)
-- Semantics.lean:193-195  findTr = first transition matching (template, state, label)
-- Semantics.lean:240,243   deliver refuses a call (`none`) if that first match has acceptsCall = false
-- Local.lean:81-89         callTotal: `I.transitions.any … tr.acceptsCall`  (some match, not the first)
```

Why:
- `LocalOk` does not forbid duplicate `(template, fromState, label)` transitions.
- `callTotal` is satisfied by *some* accepting transition. `findTr` picks the *first*.
- So a call can sit at the head of an idle callee's box with `CanReceive` true forever while `recvBulk` is never enabled.
- `Fair.bulk` then demands an action that `valid` forbids. No fair run exists, and the theorem is vacuous precisely for the run that deadlocks.

Counterexample:
- Template D has state s and transitions `[⟨D,s,"L",[],s,false,1⟩, ⟨D,s,"L",[.reply],s,true,1⟩]`.
- Caller C runs `.call D "L" 0`.
- This passes `transitionOk`, `callTotal` and `replyFails`. Once stimulus exists, C waits in `awaitReply` forever, and the run is not `Fair`.

Fix:
- State `Fair.bulk` with `Enabled I (ρ.cfg j) (.recvBulk s)`.
- Add a LocalOk check that `(template, fromState, label)` keys are unique, or that `findTr`'s result is accepting for every call label.
- Then prove `CanReceive → Enabled` under LocalOk as a lemma, not as a fairness premise.

### F4 (high). Amaru violates both stated restrictions; the model cannot describe Amaru's per-peer subtree

The restrictions, in Lean:
```lean
-- Graph.lean:572-580  callTermFails: "call {e.label} targets terminable template {e.dst}"
-- Local.lean:51-55,74 noBulkSend on every program of a terminable template (send, trySend, call all forbidden)
-- README.md:256-260   "Charging a send requires the sender's template not to be terminable … narrower than Amaru"
```

Evidence that Amaru breaks them (rkuhn-bot/amaru@908593cb6):

**Calls into `mux`, which is terminable** (mux.rs:478–480 `MuxMessage::Terminate => … eff.terminate()`, plus `or_terminate` at :408):
- protocol/miniprotocol.rs:232 and :278: `eff.call(stage.muxer(), NETWORK_SEND_TIMEOUT, …MuxMessage::Send…)`. This covers every mini-protocol.
- blockfetch/initiator.rs:276, :280, :391, :397: `.call(&mux, range)` and `.call(&mux, ClientDone)`.
- blockfetch/responder.rs:231, :238, :244, :252: `.call(&mux, StartBatch | Block | BatchDone | NoBlocks)`.
- My own R9 turns Register and SetSduTimeout into calls to mux, which makes this worse. connection.rs:471 currently sends `SetSduTimeout`.

**Terminable stages that bulk-send:**
- connection: it terminates at connection.rs:316, :431, :441, :468, and sends at :252, :258, :320, :403, :471, :594–612.
- mux: it terminates at :480, and sends at mux.rs:449, :463, :474, :660, :846, :858, :881.
- blockfetch initiator: it terminates at initiator.rs:281/:392/:417/:428, and calls mux.

**Subtree kill, which the model lacks:** connection.rs:307 says "Parent termination aborts children without delivering their tombstones". The model has only a self-`terminate` and no parent kill or supervision tombstones (`eff.supervise`, connection.rs:362, :371). A sibling blocked in `eff.call(mux, …)` when mux dies alone is today released only by NETWORK_SEND_TIMEOUT (an internal timeout, against A-int) or by the parent's abort.

Consequence: any faithful description of Amaru fails `GraphOk.lifecycle` and `LocalOk`. The theorem covers a restricted network that Amaru is not.

Fix:
- Model per-peer subtrees as units: a `group` of terminable templates killed atomically by the owner.
- Allow calls and sends *within* a subtree to terminable members.
- Require cross-subtree calls to target non-terminable cores.
- Add the dead-instance lift (owed > 0 counted toward occupancy) so terminable senders can send.
- Model tombstones as a guaranteed message to the supervisor.

### F5 (high). Per-peer routing uses a constant `hint`, so pairing is inexpressible and respawned instances are unreachable

Lean:
```lean
-- Semantics.lean:33-35  Eff.send (dst label : String) (hint : Nat)   -- a literal in the program
-- Semantics.lean:210-212 route: InstId.peer dst hint, live only
-- Semantics.lean:470,474 spawn: id := InstId.peer template (w.nextIx template); nextIx += 1
```

Why:
- Programs are per template, so every instance of `chainsync` sends to `mux` with the same literal index.
- The pairing "chainsync_i ↔ mux_i" cannot be expressed.
- After a terminate and respawn, the new index is `nextIx`, which no program names. Its routes silently drop (`route = none`, then `proceed`, :386, :392, :408).
- Churn is therefore modelled only as message loss. This is partly old gap 7.

Counterexample: perPeer templates P and M, with P's program `.call M "Send" 0`. With N = 2, instance P#1 always calls M#0, never M#1. After M#0 dies and respawns as M#2, every call to M is skipped as "target not alive". The caller proceeds as if it had been answered.

Fix: give `Cont`/`Actor` a `peerKey` (the subtree id), and route `perPeer` targets by the sender's key (`.sameSubtree`) or by a reference passed in the message. Spawn should create a whole subtree with one fresh key.

### F6 (medium). `Assumptions` is decorative: all three fields are theorems, and A-int/A-peer are hard-wired into `finishWait` + `Fair.weak`

Lean:
```lean
-- Local.lean:150-158
internal_complete : ∀ w id k, (w.st id).phase = .awaitEffect k → Enabled I w (.finish id)
peer_complete     : ∀ w id k, (w.st id).phase = .awaitPeer k   → Enabled I w (.finish id)
rust_refines : ∀ tr ∈ I.transitions, ∃ tr' ∈ I.transitions, tr'.template = tr.template ∧ … (take tr' := tr)
-- Proof.lean:57-65 enabled_finish_effect / enabled_finish_peer prove the first two with no hypothesis.
-- Proof.lean:67-91 not_stuck_effect / not_stuck_peer: no `Assumptions` argument at all.
```

Why:
- This does not smuggle in the conclusion. It does mean "every effect and every peer wait completes" is *built into the semantics*, because `finish` is always enabled and weakly fair. It is not a visible trust-boundary item.
- `rust_refines` is the identity statement. Rust ⊑ Impl is not stated anywhere (README:391 "Nothing here reads the Rust").
- `untimedPeer` (Graph.lean:582–586) is a self-declared template flag that is not tied to any `.peer` effect. `effectsOk` skips `.peer` and `.internal` (Local.lean:36–42).

Fix:
- Make `finish` of `awaitPeer` enabled only along declared peer edges with `timeout = some _`.
- State A-int as a fairness premise on `.finish` of `awaitEffect` only, and A-peer as "timed peer waits finish".
- Drop `rust_refines` or replace it with a refinement relation to an extracted trace model.

### F7 (medium). Internal call timeouts are inexpressible, so "timeouts only on peer edges" is neither checked nor modelled

- The model's `call` has no timeout branch (Semantics.lean:404–411).
- Amaru has internal call timeouts:
  - connection.rs:454: `.call(manager, HANDSHAKE_RECORD_TIMEOUT, …)`
  - tx_submission/responder.rs:609: `.call(&self.mempool_stage, mempool_insert_timeout, …)`
  - miniprotocol.rs:232/278: `NETWORK_SEND_TIMEOUT` on the mux call
- Exporting these as plain calls is conservative for deadlock. But the checker cannot flag them as A-int violations, which Roland's rule requires.

Fix: give `Eff.call` an optional timeout. Make the checker reject `timeout ≠ none` unless the edge's dst is a peer proxy, so that only `.peer` edges may time out.

### F8 (medium). Reliable messages may be dropped: `trySend` and unhandled labels

Lean:
```lean
-- Graph.lean:395  kindOk: .trySend, .nonBlocking => true   (no reliability check)
-- Graph.lean:431-439 cellFails only constrains edges marked `superseding`
-- Semantics.lean:396-403 trySend to a full box: message dropped, sender proceeds
-- Semantics.lean:239-241 deliver: non-call with no transition → consumed, phase idle
-- Semantics.lean:301-304 enqueue to dead/absent: dropped; a call "proceeds" with no reply
```

Why:
- Roland's t37u says dropping is acceptable only for superseding messages.
- The checker accepts a `reliable` trySend that is not ingress, and it accepts a bulk label that the receiver's current typestate does not handle.
- Neither causes a deadlock in the model. Both hide lost-delivery bugs, which are later liveness failures (obligation liveness is out of scope, F10).

Fix:
- `trySend` must be `ingress` or `superseding`.
- Add a check that every bulk label sent on an edge has a transition in every receiver state allowed by `targetStates`.
- Make a call to a dead target an explicit error continuation, not a silent `proceed`.

### F9 (low). `Deadlock`/`Stuck` granularity and unused definitions

- `Stuck` compares only the wait kind and its destination (Semantics.lean:566–570). An actor that is released and re-parks on the same destination forever counts as stuck, which is over-approximation and harmless. The `.peer` kind is excluded from `Deadlock` (:572–579). That is acceptable given A-peer, but it should be stated.
- Partial deadlock is covered (`∃ s i`).
- The case "a caller in `awaitReply` while its own box fills" is covered only indirectly, through its parked senders.
- `PartialDeadlock`, `GlobalDeadlock` and `CallerMailboxFull` (:581–596) are defined but no theorem uses them. Either prove them as corollaries or delete them.
- The `cell` arm of `Deadlock` is dead code (`waitKind_ne_cell`, :598). Cell waits do not exist as phases, so "waits on a cell" is not a notion the theorem can speak about.

### F10 (low, scope). Receive-side and obligation liveness are still out of scope

- README:386–390 states this.
- "Receive-side starvation" is not a conclusion. It is *assumed* by `Fair.bulk`, which is strong fairness on idle-with-mail.
- "Every reliable message is eventually delivered and every call gets its reply" is not stated, even though `CallTagInv` nearly gives the reply half.

Fix: add `Delivered ρ`: every message enqueued at step i to an actor alive from i onward is dequeued later. It follows from `queued_forever_false` plus FIFO.

### F11 (low). `CellFlags` are unverified attestations

- `singleWriter`, `orderMonotone`, `noPerMessageObligation`, `readPoints` and the others (Basic.lean:116–130) are booleans checked only for `= true` (Graph.lean:422–439).
- No check ties `singleWriter` to the set of programs that write `.cell R L`.
- The semantics uses `max` (Semantics.lean:426), so monotonicity is forced by the model, not checked against Rust.

Fix: compute the writer set from `I.transitions` and require that it has size 1 for `singleWriter`.

## Status of my 9 gaps from the 3268af09 review

| # | Gap | Status at 908593cb6 |
|---|-----|---------------------|
| 1 | ¬Deadlock missing | Partly fixed: the statement is now `¬ Deadlock ρ`, but it is vacuous (F1, F2) and Fair can be unsatisfiable (F3). |
| 2 | Conclusions by construction (finishWait always enabled, no cell waitKind, credit_clear assumed) | Partly fixed: credit is now the proved `OccInv`. `finish` is still always enabled (F6). The cell wait kind exists only as an unreachable arm (F9). |
| 3 | Refines mixed trust assumptions with model facts | Fixed in form: occupancy (`OccInv`, `l1_fit`, `l1_park_unreachable`) and compatibility closure (`compatFails`) are proved or checked. But the trust boundary is now empty in content (F6): `rust_refines` is a tautology. |
| 4 | Cells unmodelled / lost wakeup | Fixed in the model: `readCells` runs on every deliver, spawn and terminate. `dirty` is cleared. `lane_has_room` shows declared wakes fit. Not exercised (F1), and `CellFlags` are unverified (F11). |
| 5 | Reply holes | Mostly fixed: an unaccepted call is refused, `performReply` checks `dst = sender`, `replyCount = 1` and no terminate before reply, `callTermFails` is in place, and `CallTagInv` is proved. New hole: duplicate transitions with first-match `findTr` (F3). |
| 6 | Generic labels | Partly fixed: real labels are on effects. Programs are still static lists with no data-dependent branching, and the routing hint is constant (F5). |
| 7 | Fixed peer indices, no churn | Partly fixed: indices are fresh and unbounded. But terminable templates cannot send (F4), and constant hints make respawned instances unreachable (F5), so churn is not modelled meaningfully. |
| 8 | Receive-side / obligation liveness | Open (F10). |
| 9 | terminate resumed parked calls as sends | Fixed: terminate is refused while a parked call exists, and `releaseParked` skips calls (Semantics.lean:373–376, :438). |

## Target shape and what is missing

Proposed: `deadlock_freedom I (hG) (hL) (hA) : ∀ N ρ, Fair ρ → ¬Deadlock ρ ∧ CellFresh ρ`.

Present: two separate theorems with the same hypotheses. The conjunction is trivial to assemble.

Missing for the statement to mean something:
1. An environment, plus a witness theorem that a non-trivial fair run exists (F1).
2. Maximal executions, or a safety form (F2).
3. `Fair.bulk` stated on `Enabled`, plus unique-transition keys (F3).
4. Subtree-scoped termination and routing, so that Amaru's mux/connection subtree is describable (F4, F5).
5. Peer-only timeouts, made explicit (F6, F7).
