# 03 — Candidate theory: occupancy-bounded, state-indexed wait graphs for pure-stage

Status: second cut, 2026-11-15 ~11:30 (Europe/Berlin), after Helen's reviews 1–3 and inventory passes 1–2.
Definitions, semantics `⟦·⟧^∞`, assumptions (A-int, A-peer), fairness (F1–F3) and obligations (O1, O1', O3;
O4, O5) are in `01-definitions.md`; literature in `02-survey.md`. Part I is generic and stands alone. Part II
instantiates it for Amaru at pragma `main` `33d62a6f` (pre-fix tree `9a4273855`), using
`wait-graph-inventory.md`, `wait-graph-inventory-v2.md` and the JSON files. "Design change" means the minimal
change the theorem would need, for discussion; nothing here touches Amaru.

Binding rules: reliable sends stay reliable (no drops, no resend schemes); only superseding messages may be
dropped/overwritten, superseding argued from Amaru's own semantics; mailboxes may be enlarged; internal timeouts are
erased unless expiry tears down the bearer; a callback on an effect's thread belongs to the effect; no other node
implementation is used as justification (at most as the source of an idea).

---

# Part I — Generic theory

## 1. The wait graph

Template wait graph `G = (V, E)`:

* `V`: core stages, per-peer template stages (one node per template stage), producer nodes (input senders, detach
  injectors, callbacks; `01` §1.1), pseudo-stages for effect providers that violate A-int.
* Edge `s → t` labelled with message kind `k` for every `send`/`call` of `k` from `s` to `t` in some transition
  program of `s`; tagged **intra / core↔inst / cross** (cross = between two instances, drawn as a self-loop on the
  template, conservatively) / **core**; **blocking** (`send`; `call` admission and reply wait; a `call` whose expiry
  is *not* a bearer teardown, since `⟦·⟧^∞` erases it) or **non-blocking** (`try_send`, call reply, schedule/timer,
  internal effect, resource, timed peer effect, `call` whose expiry tears down the bearer); **reliable** or
  **superseding** (`01` §8).

**Mechanical closure (required; Helen review 4).** Both inventory passes missed (g) and (h), and both misses were
edges reached through a `StageRef` carried inside a message. The edge set is therefore closed mechanically, not by
reading:
1. **Ref-carrying messages:** for every message type with a `StageRef` field (e.g. `cr` in `ManagerMessage::FetchBlocks`,
   `handler` in `ChainSyncInitiatorMsg`, `caller` in calls), add an edge from every stage that sends to a ref of that
   field to every stage that can construct (own) such a ref. Over-approximate when the constructor is not unique.
2. **`send_any`** targets (typestate builders, e.g. the blockfetch initiator's collector) count as sends with the
   same blocking/reliability classification as `send`.
3. **SCCs by script:** recompute strongly connected components of the residual graph from `wait-graph.json` with a
   script after every inventory change; a cycle verdict cites the script output, not a hand trace.

Every cycle of the instance graph `G(N)` maps onto a closed walk of `G`, so acyclicity on `G` holds for all `N`
and for every intermediate topology during creation/teardown.

## 2. Lemma 1 — occupancy bounds (credit discharge)

For mailbox `t`, `Prod(t)` = **all** producers (stages, per-peer instances counted `N` times, injectors, input
senders, callbacks) and **all** message kinds. `w_{p,k}(t)` is an occupancy bound if in every reachable
configuration `in_{p,k}(t) := #(k-messages from p in box_t) + [p is executing a k-send/call to t] ≤ w_{p,k}(t)`.
`W(t) := Σ_p Σ_k w_{p,k}(t)`.

**Lemma 1.** If `W(t) ≤ c_t`, no send or call admission into `t` ever parks. (Proof: at the start of any send the
total, including that message, is `≤ c_t`, so a slot is free and, inductively, nobody is parked.)

Bounds come from protocol structure (request/response window; explicit credits; one-shot sends; a stage has at most
one outstanding call). Credits returned by message are ordinary edges; the bound is a reachability invariant, so
there is no circularity. Buffer accounting in the sense of Parks (1995) and Dally & Seitz (1987); inductive
occupancy invariants of exactly this kind are what the xMAS line of work derives automatically for hardware queues
(`02` §A').

## 3. Lemma 2 — superseding edges (last-value cells)

Setting: producer `s` writes values of kind `k` for consumer `t` into a shared cell `R` and signals `t` with a
wake-up. **Conditions:**

* **(i) Order.** `R` has a single writer, or writes are totally ordered (version counter), and `t`'s behaviour
  depends only on the greatest element of `R` in that order, or on the join of a semilattice that is monotone under
  every write. In chain order, "latest" is *not* a join if a rollback can retract an earlier write.
* **(ii) No per-message obligation on the wake.** The wake message itself carries no credit, ack, reply ref or
  causal context that some other stage relies on. (Reliable messages that `t` *emits* while handling the wake are
  separate edges and are accounted for where they belong; they do not make the wake reliable.)
* **(iii) Visibility.** The write to `R` happens-before the wake, and `t`'s read observes it (part of A-int for
  resources).
* **(iv) Read points.** `t` reads `R` in init/restart and at every point at which a lost wake could otherwise be
  missed: with a bulk-mailbox wake, on **every** transition; with a priority-lane wake or a timer poll, on the
  wake/poll handler (and in init/restart).
* **(v) Idempotence.** A spurious wake or an unchanged `R` is harmless (version check).
* **(vi) Split conclusion.** Under (i)–(v) the edge `s → t` is **non-blocking unconditionally** (it is a cell write
  plus a non-blocking wake). **No lost update** (the final value `t` acts on is `R`'s maximum) holds *conditional on
  `t`'s liveness*, which comes from Theorem A applied to the graph *without* this edge — no circularity.

Wake-up options, with the producer's occupancy reduced to `W_s(t) = 1` by a **dirty bit** (wake only on clean→dirty;
`t` clears the bit *before* reading `R`):

* **W1 bulk `try_send`**: `Full` ⇒ `box_t` non-empty ⇒ `t` will run a transition; needs (iv) on every transition.
* **W2 priority lane**: needs a cross-stage priority send (pure-stage today only schedules to *self*) and
  `Σ W(priority producers into t) ≤` priority capacity (10).
* **W3 timer poll**: no wake message at all; `t` polls `R` on its own timer. The edge disappears; the extra delay
  (poll period) is a Theorem B bound.

Lemma 2 applies **only** to superseding kinds; reliable kinds use Lemma 1, Lemma 3 or structural flow control.

## 3a. Lemma 3 — ingress teardown

If `mux → h` delivers peer traffic, `L(h)` is the legal outstanding inbound amount from the mini-protocol session
type, and `c_h ≥ L(h) + Σ_{p≠mux} W_p(h)`, then replacing the blocking delivery by `try_send` + bearer teardown on
`Full` makes the edge non-blocking, and every teardown is a protocol violation of that peer (admissible, `01` §8).

## 3b. Lemma 4 — state-indexed wait graph

Some cycles of `G` cannot occur because the sender and the receiver are never in the matching states at the same
time. Let each stage `s` have a finite abstraction `α_s` of its control state, taken **from its typestate** where
one exists (`make_states!` states), evaluated at the moment of a blocking effect.

* The **state-indexed graph** `G^α` has nodes `(s, a)`, `a ∈ A_s`, and an edge `(s, a) → (t, b)` iff (1) in some
  concrete state abstracted to `a`, `s` may perform a blocking send/call to `t` (the edge carries this sender-state
  predicate), and (2) `b ∈ B(s, a, t)`, where `B` comes from an **inductive invariant `I`** over global abstract
  configurations stating which abstract states `t` can be in *at any time while `s` is parked on `t` in `a`* (not
  just at the moment of parking: `t` keeps running transitions until `s` is admitted).

**Lemma 4.** Suppose (S1) `I` is inductive — preserved by every step of `⟦·⟧^∞`, including environment, lifecycle
and termination steps; (S2) the per-state edge sets are complete — every blocking effect possible in a concrete
state abstracted to `a` appears from `(s, a)`. Then every instantaneous wait `s ⇝ t` of a reachable configuration
is an instance of an edge of `G^α`, and if `G^α` restricted to residual edges is acyclic, heights
`h(s, a)` are well defined and Theorem A's induction goes through over `(stage, abstract state)` unchanged
(for `s` parked in `a` on `t`, every state `b` that `t` passes through until `s` is admitted has `h(t, b) < h(s, a)`).

`h` is a Roscoe–Dathi variant function (`02` §B'): a value on (process, state) that strictly decreases along every
ungranted request. Lemma 4 is that method specialised to bounded mailboxes, with the variant read off the typestate
graph. Its cost is the invariant `I`, which must be proven (or checked inductively) per instance.

## 4. Theorem A (internal deadlock freedom, reliable sends unchanged)

`E_res` = blocking edges of `G^α` (or `G`, with the trivial abstraction) not discharged by Lemma 1 (credit),
Lemma 2 (superseding, only for superseding kinds), or Lemma 3 (ingress teardown).

**Hypotheses.**
* **H1 (acyclicity).** `(V^α, E_res)` is acyclic, with `V^α` the `(stage, abstract state)` nodes of Lemma 4 and
  S1–S2 discharged for every non-trivial abstraction used; cross edges as self-loops.
* **H2 (effects).** A-int for every internal effect; every callback on an effect's thread belongs to the effect and
  performs no blocking operation on a stage. Otherwise the provider is a pseudo-stage and, for every stage that
  awaits *any* effect of that provider, `E` contains an edge to each stage the callback blocks on.
  **No stage-dependent wait on a worker thread:** synchronous blocking inside a transition (`wrap_sync`, `block_on`
  in callbacks) must not wait on a stage, since it occupies the runtime worker as well as the stage.
* **H3 (peer isolation).** No node with an untimed peer wait has an incoming edge in `E_res`; timed peer waits end
  within their timeout (A-peer).
* **H4 (reply obligation).** Every admitted internal `call` request is answered by the callee **in the transition
  that dequeues it, after finitely many effects**; deferred replies add edges caller → every possible trigger.
* **H5 (lifecycle).** No internal `call` targets a stage that can **terminate before replying to an admitted
  request** while the caller lives; no send to a never-created name (simulation drops, tokio panics); priority
  bounds hold (overflow panics, not a wait).
* **H6 (fairness and finiteness).** F1–F3; every transition program is finite; no stage-dependent wait on a worker
  thread (shared with H2).
* **H7 (bounds, inductive under lifecycle).** Every occupancy bound used for a discharge holds with the concrete
  capacities **and is inductive across restarts and re-creation**: either stages are re-created only under **fresh
  names**, or it is proven that the old mailbox is dropped together with its parked senders and that those senders
  resume (so stale messages cannot consume a re-created stage's credit).

**Theorem A.** Under H1–H7, for every `N`, every adversarial environment, and every fair run of `⟦·⟧^∞`, no stage is
stuck forever (O1), and no stage with an incoming residual edge waits forever on a peer (O3).

**Proof sketch.** (1) *Projection*: every instantaneous wait is an instance of an `E_res` edge (non-blocking edges
never park; Lemmas 1–3 discharge theirs; H2 makes A-int violators explicit; Lemma 4 for state-indexed edges).
(2) *Heights* over `V^α` are finite and `N`-independent. (3) *Induction on `h`*: every transition of a stage at
height `h` terminates — base case by A-int/A-peer/H3; step: a parked `s` targets `t` whose transitions all
terminate (IH), `t` keeps dequeuing (F1, F3), each dequeue admits the head parked sender (F2), finitely many senders
are ahead of `s`; a call is answered when dequeued (H4). (4) Safety half: no reachable `⇝`-cycle, since it would
project onto a cycle of `E_res`; this half needs no fairness. ∎

**Which half a simulation test checks.**
* *Safety half* (no reachable `⇝`-cycle): checked by **any** schedule, including deliberately unfair custom
  deferral strategies (the #1475 repro defers stages on purpose). A found cycle is a counterexample to H1-soundness
  or to the extraction; no cycle found proves nothing beyond the explored runs.
* *Liveness half* (O1: nothing stuck forever): needs F1–F3; only runs under a fair strategy (FIFO or uniform random,
  run to quiescence) say anything, and only for the runs explored. Deferral strategies are unfair by design and
  cannot witness O1 either way.

**Positioning against the client–server rule** (Welch, Justo & Willcock 1993; Martin 1996; `02` §B'): "a network
whose client→server digraph is acyclic and whose servers always eventually accept/answer requests is deadlock-free".
Theorem A ≈ this rule with: residual blocking edges = client→server edges (H1), H4 = servers answer. What we add:
(a) **buffered** channels with shared bounded capacity — Lemma 1 lets edges run "backwards" (server→client
notifications, credits) without violating the order, which the synchronous rule cannot express; (b) superseding
edges (Lemma 2) and ingress teardown (Lemma 3); (c) state-dependent ordering (Lemma 4 = Roscoe–Dathi variants);
(d) effects, internal calls with erased timeouts, peers as an adversarial environment; (e) parameterisation by a
template graph.

## 4a. The chain-selection rule as a parameter (Praos now, Genesis later)

Decision (Roland): Amaru implements Praos only, so Praos is the target; the theory must let a later switch to
Genesis be shown deadlock-free without a second proof. Write `CS` for the chain-selection rule together with its
anchor rule.

**What does not depend on `CS`.** Theorem A's hypotheses H1–H7, Lemmas 1–3, every occupancy bound of §9, the mux and
protocol discharges of §8(b), and the requirements R1–R11 except where named below. Lemma 4's fetch token `T` and its
invariant are rule-independent: `select_chain` decides *which* tip to offer, never *whether* the token moves.

**What depends on `CS`** (each is a liveness or memory item, none is a wait-graph edge):
* `P1` **who writes the anchor and from what:** Praos: `adopt_chain` writes it (`tip − k` on the adopted chain), and
  `select_chain` reads it through a single-writer monotone cell (Lemma 2, M1) to prune and recompute.
* `P2` **the `BoundaryNotFound` race (β):** reachable under Praos and closed by the prune; the token is handed back
  (§8(a)), so the residual case is only a store hole (α), which terminates.
* `P3` **REQ-resolve's walk bound:** `k` under Praos (rollback ≤ `k`), memory ≤ `F·k` headers.
* `P4` **Theorem B (TB4):** the anchor cell's wake latency is on the critical path.

**What a Genesis variant must discharge** (a parametrisation, not a proof):
* `G1` **No new blocking edge.** The anchor hold is a **wait on internal state**, not a message wait: the anchor
  (a store value) stays put while `adopt_chain` and `select_chain` keep running. The information "common intersection
  of the compared candidates" must reach the anchor writer by a cell (Lemma 2) or by a store read (delay edge),
  never by a blocking send back into `select_chain`. Simplest: make `select_chain` the single writer of the anchor,
  as `min(adopted tip − k, common intersection of compared candidates)`; `adopt_chain` then no longer writes it, and
  `select_chain` reads the adopted tip from the existing tip cell. Re-run the checker; the edge set must not grow.
* `G2` **Cell soundness.** The common intersection is not monotone (a new deeper candidate lowers it), so this cell
  is latest-wins without M1: Lemma 2 needs that only the latest value matters to its reader. With `select_chain` as the
  single writer of the anchor, the race between reading a stale intersection and advancing the anchor disappears;
  with any other writer it must be argued separately.
* `G3` **Token.** `BoundaryNotFound` (β) becomes unreachable if the anchor never passes a compared candidate's
  intersection; the (α) branch is unchanged. Lemma 4's invariant needs no change.
* `G4` **Bounded hold.** The hold must end: candidates are resolved within Genesis's comparison window, or dropped by
  Genesis's own (peer-attributable) rules. Otherwise headers below `tip − k` accumulate. This is an O4 and memory
  obligation: REQ-resolve's walk bound and memory become `k + h` and `F·(k + h)`, with `h` the maximal hold in
  blocks.
* `G5` **Theorem B.** The hold lengthens nothing on the header → re-announce path except through `h` in TB4's
  memory/store terms; cell periods as before.

## 5. Theorem B (timeliness and per-peer fairness) — separate

Under A-int-q and per-stage transition bounds `τ_s`:
* Edges into a `P`-stage discharged by Lemma 1/2: a message waits ≤ `c_t · τ_t` at `t`.
* `N` per-peer producers with residual blocking edges into `t`: with FIFO admission (F2), a peer's message waits
  behind ≤ `N − 1` parked senders plus `c_t` queued messages — bounded per peer, so **no starvation (O5) without a
  quota**, but the bound grows with `N` (relevant to O4's design target).
* Superseding edges via W3 add the poll period; via W1 up to `c_t` messages.
* A lost or never-created token (a session waiting for a message that never comes) violates O4/O5 without any
  `⇝`-wait; the Lemma 4 invariant `I` is also the check for this (`01` §4).
* Ouroboros inputs from the papers only; ~10 ms/hop and ~1 s freshness are labelled design targets.

## 5a. Theorem B skeleton (Helen review 10)

**SHELVED (2026-11-15, by Roland's decision):** all Theorem B material is kept in `theorem-b-shelved.md`.

Items are numbered TB1–TB6 to keep them apart from the blockers B1–B6 of §8.

Not a proof; the shape of one, with every quantity labelled **[config]** (follows from configuration or protocol
parameters) or **[measure]** (must be measured on the implementation). Constants from Ouroboros are taken from the
papers' model only; the 5-slot figure is a working target, not a derived constant.

**TB1. Quantitative A-int.** Every internal effect `e` completes within `D_e` **[measure]**: store reads/writes, the
chain-store `FindBestCandidate`, header validation, and ledger block validation. Ledger validation is bounded by the
protocol parameters `maxBlockExUnits` and `maxBlockBodySize` **[config]** (the work per block is capped by them), but
the time per unit is **[measure]**, so `D_validate ≤ f(maxBlockExUnits, maxBlockBodySize)` with `f` measured.

**TB2. Per-stage service time and hop bound.** For stage `s`, `S_s = max over message kinds of the transition time`,
composed of its own CPU plus `D_e` of the effects it awaits **[measure]**. A message entering `s` waits at most
`(c_s + P_s) · S_s`, where `c_s` is the capacity **[config, §9 formula]** and `P_s` the number of senders that can be
parked on `s` at once **[config: number of producer instances]**, using FIFO admission of parked senders (F2,
tokio's fair semaphore). This is the per-hop bound; a path's bound is the sum over its hops.

**TB3. Utilisation below 1.** Every bound in TB2 assumes `s` is not overloaded in the long run: arrival work per unit
time `< 1`. For pull-based edges the arrival rate is bounded by configuration: e.g. at `track_peers`, `N_max · d`
outstanding results per round-trip, at `fetch_blocks`, `A · MAX_FETCHED_BLOCKS` per request **[config]**, times the
cost per message **[measure]**. Where no pull bound exists (submit API, inbound tx batches), admission control is
required: `L_max` (R11), the mempool's own capacity rejection, and the responder's requested counts.

**TB4. Critical-path budget.** Path: header arrives at the chainsync initiator → `track_peers` → validate header →
`select_chain` → `fetch_blocks` → blockfetch → `validate_block` → `adopt_chain` → re-announce (manager tip cell →
connection → chainsync responder). Budget = Σ hop bounds (TB2) + `D_e` of the effects on the path + the cell wake
latencies on it (dirty-bit: one hop; W3: period `π` **[config]**) + network transfer **[environment]**. Requirement:
the internal share is a stated fraction of Praos Δ; working target Δ = 5 slots, taken from the security model's
treatment of Δ-bounded delivery, not from any implementation. An internal stall on this path adds to the effective Δ
of every node running the same code (`01` §5), so the fraction must be small and stated.

**TB5. Per-peer fairness (O5).** A peer's message to a shared stage `t` waits behind at most `N_max − 1` other parked
per-peer senders plus `c_t` queued messages: `≤ (N_max − 1 + c_t) · S_t`. Independent of the adversary's sending rate,
because each peer instance has at most one parked send (a stage is sequential) and admission is FIFO.

**TB6. Timer budgets, kept separate.** For each protocol timeout `T`, show that local queueing alone cannot make it
fire against an honest peer:
* **R1 send timeout** `T_send` (1 s today): mux queueing `≤ (c_mux + P_mux) · S_mux` with `c_mux = d + 25`,
  `P_mux ≤ 10 + 3` (handlers, reader, writer, connection) **[config]**, `S_mux` **[measure]**; require `≤ T_send / k`
  with a stated safety factor `k`. At `d = 10`, `k = 10`: `48 · S_mux ≤ 100 ms`, i.e. `S_mux ≤ ≈ 2 ms`. Separately,
  `Sent` also waits for earlier segments of the other protocols on the same bearer (round-robin), up to ≈ 10 × 64 KiB:
  on an honest link of bandwidth `b` **[environment]** this is `640 KiB / b`, which must also be `< T_send` (≈ 5 Mbit/s
  at 1 s). Otherwise R1 can tear down an honest slow peer.
* **keepalive**, **chainsync** (`MustReply`/intersect timeouts) and **blockfetch** (range/batch timeouts): each
  `T` must exceed the round-trip **[environment]** plus the local queueing on both of our path's hops (handler
  mailbox and mux, TB2) plus, for blockfetch, the transfer time of the requested bytes at `b`. Values of `T` are
  **[config]**; the local terms come from TB2.

**What must be measured vs what follows from config:**

| Quantity | Source |
|---|---|
| `c_s` (all capacities), `P_s` (producer counts), `N_max`, `d`, `A`, `C`, `L_max`, `MAX_FETCHED_BLOCKS`, cell periods `π`, protocol timeouts `T` | **config** (§9 formulas) |
| `maxBlockExUnits`, `maxBlockBodySize`, `k`, slot length, Δ target | **protocol parameters / security model** |
| `D_e` per effect (store, `FindBestCandidate`, header and block validation per unit), `S_s` per stage, per-message cost for TB3 | **measure** |
| link bandwidth `b`, round-trip times | **environment** (assumptions for honest peers) |
| high-water marks per mailbox (M4) | **measure** (check against config formulas) |

## 6. Toy example: Manager ↔ PeerSelection

Stages `M`, `PS`, capacity `c`; `N` connection instances `C_i` sending to `M`.
* **Pre-fix:** `M → PS` (connection events) and `PS → M` (`AddPeer`, `Disconnect`, …), both reliable and blocking.
  No window on either (`W(PS)` unbounded, `W(M) ≥ N`), not superseding ⇒ residual cycle ⇒ **flagged**. Witness
  (`c = 10`, `N ≥ c + 1`): with `PS` deferred, `M` fills `box_PS` and parks; `≥ c` connection events fill `box_M`;
  `PS` dequeues one (admitting `M`'s message, refilling `box_PS`), sends `AddPeer`, parks on `box_M`; `M` parks again
  on `box_PS`. Stable in `⟦·⟧^∞`.
* **Post-fix (dcffd9dcb):** `M`'s notifications become writes to shared peer-tracking state (delay edge);
  `E_res = {PS → M, C_i → M}` ⇒ acyclic ⇒ the pair **passes**.
* **Seeded:** re-insert one blocking `M → PS` ⇒ flagged.

## 7. Residual cycles that cannot be discharged

Model-check the SCC for small `N`, `c` (explicit bounded FIFOs; Go behavioural types or xMAS-style tools, `02`).
All-`N` soundness then needs a cutoff; the `c + 2` shape is a **conjecture** needing German–Sistla-style symmetry
hypotheses our core stages do not obviously meet. Design so this is never needed.

---

# Part II — Amaru instantiation at `33d62a6f`

## 8. Per-cycle verdicts

### SCC result (inventory v3 §G3; script `scripts/wait-graph-sccs.py`, fork commit `cc57103ca`)

On `wait-graph-v3.json` (40 blocking edges, including carried-`StageRef` and `send_any` edges per §1):
* **One SCC of 16:** `accept`, `adopt_chain`, `block_source`, `blockfetch_initiator`, `chainsync_initiator`,
  `cleanup_replies`, `connect_worker`, `connection`, `connector`, `fetch_blocks`, `manager`, `mux`, `peer_selection`,
  `select_chain`, `track_peers`, `validate_block`. Deleting the token-discharged `NewBestTip` edge (Lemma 4, (a))
  removes `select_chain` and leaves **15**. The carried `cr` edge is what joins fetch, cleanup, block source and
  peer selection to the disconnect path.
* **One SCC of 2:** `mempool ↔ tx_submission_responder` — classified in pass 4 (§8(m), fix B4).

The cycles below are named walks inside these SCCs, kept for explanation. Per Helen review 6 the deliverable is no
longer a cycle enumeration but the **discharge check** of §10: delete every discharged edge, recompute SCCs, require
the rest acyclic.

### Pass 4: discharge checker result (inventory v4; checker `scripts/wait-graph-sccs.py`, fork commit `f54f38993`)

Both modes exit 1 (v4 §1). `N_max = max_inbound + max_outbound = 10 + 3 = 13` at the defaults; `manager` and
`peer_selection` bulk mailboxes are `10 + N_max = 23`.
* **now:** 3 of 43 blocking edges discharge — `connector → connect_worker [ConnectJob]` (L1, `W = 1`), `manager →
  accept [PullAccept]` (L1, `W = 1`), `select_chain → fetch_blocks [NewBestTip]` (L4, token). Residual: an SCC of
  **14** (`adopt_chain`, `block_source`, `blockfetch_initiator`, `chainsync_initiator`, `cleanup_replies`,
  `connection`, `connector`, `fetch_blocks`, `ledger`, `manager`, `mux`, `peer_selection`, `track_peers`,
  `validate_block`), the `mempool ↔ tx_submission_responder` pair, and the self-loop `peer_selection [Resolved]`.
* **after the 8 modelled fixes** (cap at accept, shared Adversarial set at `7·N_max`, `MAX_FETCH_PEERS` on broadcast,
  chainsync credit + Done-once, cleanup filter, fresh-start `FetchNextFrom(Origin)`, stake cell + W3, token): 8
  discharge — the three above, the three edges into `chainsync_initiator` (L1, `13 ≤ 14`, v4 §3; `AwaitReply` adds
  nothing), and `ledger ↔ track_peers` (L2). Residual: an SCC of **12**, the mempool pair, the `Resolved` self-loop.
* **Pass-4 blockers as reported:** `7·N_max = 91 > 23` (`peer_selection`); `manager`'s bulk sum `> 23`
  (`Accepted + HandshakeComplete ≤ 2·N_max = 26` alone, `SetLocalUse`/`FetchBlocks`/`NewTip` unbounded); the mempool
  pair (`InsertBatch` is an `eff.call` that parks the responder on admission; `SubscribeCapacity` and
  `CapacityAvailable` are blocking sends). `W(Resolved) ≤ max_outbound` already holds (v4 §2).
* **Modelling discrepancy (mine, against v4 §1/§6):** pass 4 models the cleanup filter as an **id** filter and so keeps
  `cleanup_replies → fetch_blocks` blocking at `5·MAX_FETCHED_BLOCKS = 5000`. The filter adopted in (g) also requires
  `hash ∈ cell.missing ∧ not yet forwarded for that id`, which bounds forwarded `Block`s by the batch (`≤ 25` per id)
  regardless of the 1000-per-flight cap. Under that filter the edge is L1 at 67 (row below). The 1000 vs 25 figures
  themselves are confirmed (v4 §6).

### Pass 5: checker on the full graph (inventory v5; fork commit `44f34827d`, tree `33d62a6f`)

v5 (`wait-graph-v5.json`, `wait-graph-inventory-v5.md`) has **78** blocking edges (v4: 43); every v4 key survives and
the 35 new ones are the protocol stages v4 left out (handshake, both chainsync/blockfetch/txsub/keepalive/peer-sharing
roles with the mux, `mux_reader`/`mux_writer`, `done_trap`, `connection → mux` `Register`/`SetSduTimeout`, the
`WaitForAtLeast` pair, `submit_api → mempool`, `forge_block`). Its own `after` mode discharges 22 and leaves three
components: (A) `mux` + 9 handlers (10), (B) `fetch_blocks`, `cleanup_replies`, `manager`, `connector`,
`validate_block`, `adopt_chain` (6), (C) `ledger ↔ track_peers`.

**Re-run** (`scripts/what-if-sccs.py` with `GRAPH=wait-graph-v5.json DIS=wait-graph-v5-discharge.json`):
* `scripts/what-if-v5-core.txt` adds 12 rows to v5's `after` set: the six edges into `manager` (L1 at
  `4·N_max + 2·max_outbound + 4`, corrected in pass 6 to `4·N_max + C + 4`), `cleanup_replies → fetch_blocks` (L1 at 67), the stake callback both ways (L2,
  M1 + W3), and the three edges into `mempool` (L1 at `max_inbound + L + 1`, `L` capped). **(B) and (C) vanish**; (B)
  was the checker comparing against the current capacities (23, 10), (C) the missing stake-cell row. Only (A) is left.
* Necessity (one row removed at a time): without `connector → manager` the pair `connector ↔ manager` survives; the
  `cleanup_replies → fetch_blocks`, `fetch_blocks → manager` and `adopt_chain → manager` rows are each individually
  redundant for acyclicity (the other `→ manager` rows already cut (g)), but stay in the set for Theorem B.
* `scripts/what-if-v5-all.txt` = core + the (A) rows of §8(b) below: **45 discharged, no SCC, no self-loop**. Minimal
  for (A): the nine `mux → handler` rows alone (`what-if-v5-minimal.txt`, 43); `done_trap` and the
  `connection → chainsync_responder` cell are not needed for acyclicity (they are needed for the handler sums).

### Pass 6: bounds checked against today's code (fork commit `3842d8947`)

Pass 6 checked every proposed bound against tree `33d62a6f` and discharged a row only where **today's code** meets it,
so its checker still exits 1 with the same three components (22 discharged, unchanged from v5). That is the expected
result: the rows of `what-if-v5-all.txt` are **requirements for the rewrite**, not facts about `33d62a6f`. Re-run with
the pass-6 discharge table (`wait-graph-v6-discharge.json`, `GRAPH=wait-graph-v5.json`) and the corrected rows below:
`what-if-v5-all.txt` **45 discharged, acyclic**; `what-if-v5-minimal.txt` 43, acyclic. The edge set is unchanged; the
corrections change bounds and the requirements behind them (manager formula; §8(b) per-handler table).

### Pass 7 and Helen review 11 (fork commit `7ccaa7ab3`; `wait-graph-inventory-v7-checks.md`; `helen-review-11-pass7.md`, the parent's summary)

Pass 7 is read-only against `33d62a6f` and changes no discharge row; the what-if result of pass 6 stands (45
discharged, acyclic). It checks the pending items R2, R5, R10, M1–M3. "Today" = `33d62a6f`; "requirement" = the rewrite.

**(1) Chainsync initiator `MsgDone`: a real violation today.** Normative source: the ChainSync state machine of the
Ouroboros Network Specification (`02`, §3.7.2, Fig. 3.1): `MsgDone` is a client transition **from `StIdle`** to
`StDone`. Under pipelining the server "process[es] the messages in turn" (§3.15), so it reaches `StIdle` only after
answering every earlier `MsgRequestNext`; a client that sends `MsgDone` while replies are due is in `StDone` while the
server is still legitimately sending. Hence `MsgDone` is legal only with **outstanding = `RequestNext` sent −
(`RollForward` + `RollBackward`) received = 0**; `AwaitReply` does not decrement it. Today `IntersectFound` sends one
`RequestNext(PIPELINE_DEPTH)` (`PIPELINE_DEPTH = 10`) and sets `CanAwait(1)` (`chainsync/initiator.rs:311–318`); a
header at `CanAwait(0)` moves to `Idle` (`:324–326`), and `pending_close` emits `Done` on that transition (`:174–175`,
`:350`) with up to 9 replies due. `Idle + RequestNext` has the same shape (`:343`, `RequestNext(1)` → `CanAwait(0)`). The
honest peer's replies then hit the done trap and tear the connection down: a local-cause teardown, not admissible
under `01` §8. **Requirement (R10):** an explicit `outstanding` counter in the initiator, `Done` gated on
`outstanding = 0`, asserted at the send site. (Haskell's typed-protocols pipelining "collect before done" is only the
source of the idea.)

**(2) TxSubmission `MsgDone` from `TxIdsBlocking`: legal.** The specification defines `MsgDone` as the client's
termination message "when the server is making a blocking call for more transaction identifiers" (§3.9.1); pass 7's
"violation" is withdrawn. Today `Done` is emitted only from `State::TxIdsBlocking` (`tx_submission/initiator.rs:223`,
via `:114–116`, `:139–140`). **Requirement:** keep it gated to that state (assert).

Blockfetch (`ClientDone` only from `Idle`, `Close` while busy defers), keepalive and peer sharing (`Done` only from
`Idle`, after the one outstanding reply) **hold today** (pass 7 §2).

**(3) REQ-resolve (new).** Today the responder's `NewTip` stores the tip and calls `next_header`
(`chainsync/responder.rs:85–96`); an off-chain follower pointer becomes `NeedRollback` and `find_ancestor_on_best_chain`
walks the **pointer's** stored parents (`responder.rs:183–197`, `read_chain_store.rs:144–162`). It resolves only if
`load_header` returns each ancestor; there is no `k` bound on the walk; an unstored point is `StartHeaderNotFound`
and `next_header` returns an error (`responder.rs:96, :189`), which terminates the handler. The consensus path does not
delete headers on rollback (only the dev `prune` command does, `rocksdb_store.rs:135`). **Requirement:** for every
live follower pointer `p` the responder can compute `intersect(p, best chain)` by walking stored parents. Sufficient
condition: header GC never prunes a header reachable from a live follower pointer back to the best chain. Bound:
rollback ≤ `k` (Praos common prefix), so the walk is ≤ `k` steps and memory ≤ `F·k` headers for `F` live followers.
An unstored `p` or a walk longer than `k` is an **internal invariant violation**: assert it in the simulation; never
blame or disconnect the peer for it. With REQ-resolve the latest-wins tip cell of R5 is sound for the responder.

**Re-register (R2).** Today two paths re-register a protocol id without the old session being `Done` on both sides
(pass 7 §1): the done trap is installed when the child **dies** (`connection.rs:636–688`), even when it died from a
timeout or error with no `MsgDone` (peer sharing `initiator.rs:130–137`, blockfetch agency timeout
`initiator.rs:321, 373`); and `start_initiators` registers a new initiator on the same id, in the same turn when use
returns (`connection.rs:694–699, 705–775`). **Requirement:** a per-connection handler that dies without having
completed `Done` tears the connection down; `start_initiators` never re-creates a handler in the turn its predecessor
died; a replacement is registered only after `Done` and then with `wanted := 0`, `incoming` cleared.

**Restart orphans (M1).** `supervise` delivers a tombstone and never recreates; the only same-connection recreation is
`start_initiators` (pass 7 §4). Today's orphans:

| Died | Orphaned state | Requirement |
|---|---|---|
| chainsync initiator | `track_peers` `upstream`/`deferred` keyed by `conn_id`, holding the dead handler (`track_peers/mod.rs:234, 594–597`); purged only on the next `Initialize` or `Terminated`; lost `RequestNext` stalls the follower | clean on handler death (R2 makes that `Terminated`) |
| blockfetch initiator | `fetch_blocks` `missing`, `req_id`, `timeout`, `widen`, `fetch_peers` (`fetch_blocks/mod.rs:412–455`) | the `FetchBlocks` cell is re-read by the replacement, or the death is `Terminated` (R2) and `fetch_blocks` re-plans |
| tx initiator | mempool `waiters`/`capacity_waiters` hold the dead caller (`mempool/stage.rs:72, 112, 186–195`) | bounded lists, purge dead callers; moot under the R5 seq/capacity cells |
| keepalive / peer-sharing initiator | next timer delivered to a dead stage and dropped (`keepalive/initiator.rs:137`, `peer_sharing/initiator.rs:113`, `simulation/running/mod.rs:2048–2050`) | harmless once R2 tears the connection down; otherwise the replacement arms its own timer |

**Lost sends (M2).** A send to a created-then-terminated stage is dropped in both runtimes (tokio: `mpsc` send fails,
`.ok()`, `tokio.rs:726`; sim: `NotFound`). A send to a **never-registered** name panics in tokio
(`tokio.rs:720–724`) but is logged and dropped in the simulation (`simulation/running/mod.rs:1307–1309`).
**Requirement:** the simulation is at least as strict as tokio (panic on a never-registered name). Lost reliable sends
that matter today: `RequestNext` to a dead chainsync initiator (follower stalls) — removed by R2 + M1.

**Schedule lane (M3).** Per-stage priority capacity 10 (`types.rs:44`); `schedule_after`/`schedule_at` panic at the cap
(`tokio.rs:864–870`); `set_timeout` arms one timer and does not occupy the lane (`effect.rs:463–467`). Outstanding
schedules: all stages ≤ 2 except `connection` (one per pre-`Established` `FetchBlocks`/`NewTip`/`SetLocalUse`, no cancel,
`connection.rs:272, 277, 281`). Supervision tombstones use the same priority queue without counting
(`tokio.rs:850–861`). **Requirement:** cancel-before-rearm everywhere (the `connection` re-schedules become the B3 cells),
so the lane is ≤ 2 per stage as a **hard** bound, plus tombstones ≤ number of children (to be added to the 10).

**`conn_id`s (R7).** Never reused in operation: `get_and_increment` with `wrapping_add(1)` from 0
(`connection_provider.rs:58–67`), `remove` does not recycle (`amaru-network/src/connection.rs:93–95`). Only a `u64` wrap
reuses an id: **assumption** (2^64 connections are not reached) **plus an assert** at the allocator.

**`MAX_FETCH_PEERS` (R11).** `fetch_blocks` passes `max_peers: MAX_FETCH_PEERS` to the selector and the widen room
(`fetch_blocks/mod.rs:33, 423–437, 509–530`), but sends `peers: None` when the selection is weak or empty, and the
manager then **broadcasts to every `may_initiate` connection** without reading `MAX_FETCH_PEERS`
(`manager/mod.rs:767–776`). So `A ≤ MAX_FETCH_PEERS` does not hold today and **`fetch_blocks` = 67 is unsound** until the
broadcast loop is capped at `MAX_FETCH_PEERS` (already listed under (g); now confirmed at the exact site).

### What still blocks the "after fixes" pass, and the smallest fix for each

Reproduced on `wait-graph-v4.json` with `scripts/what-if-sccs.py` (this directory): pass-4's `after` set leaves 12 + 2 +
self-loop; adding the rows below leaves **no SCC and no self-loop**. A minimal sufficient set
(`scripts/what-if-minimal-fixes.txt`, 13 extra rows: B1, B2, B4 and one edge of B5) already yields an acyclic
remainder; the full set (`what-if-all-fixes.txt`) adds B3 and the connection/cleanup rows. "Enlargement" = capacity
becomes a config formula, no protocol change; "structural" = a code change of message shape or flow.

| # | Blocker (edges) | Smallest fix within the rules | Kind | Bound after fix | Status |
|---|---|---|---|---|---|
| B1 | `{track_peers, fetch_blocks, cleanup_replies, block_source} → peer_selection [Adversarial]`, `peer_selection [Resolved]` self-loop | **Source dedup:** one helper used by all 7 `Adversarial` sites does an atomic check-and-set per `conn_id` on a grow-only resource. **The resource write is the linearisation point**: of any number of concurrent reports for one `conn_id`, exactly the one whose write inserts the id sends. `N_max` counts **`conn_id`s**, not peers: a reconnect gets a fresh id and may be reported again, but live ids are bounded by the cap at accept, so `W(Adversarial) ≤ N_max`. Then size `peer_selection` bulk to `1 + N_max + max_outbound` | structural (helper) + enlargement (formula) | `1 + N_max + max_outbound` = 17 at defaults ≤ current 23 (holds while `max_outbound ≤ 9`) | design; `block_source` knows only `Peer` at `:128`/`:152`: carry the `conn_id` in `BlockReceived`, or key by peer (then `≤` distinct peers `≤ N_max`) |
| B2 | `{peer_selection, fetch_blocks, adopt_chain, connection, connector, accept} → manager` | (a) **`SetLocalUse` → per-connection cell** (latest-wins, verified); (b) **`NewTip` → single-writer cell** (verified; version = adoption sequence number, not slot); (c) **`FetchBlocks` → cell** `(req_id, from, through, asked-set)`, ordered by `req_id` then `⊆`; `manager` diffs and dispatches only new `(id, peer)` pairs, one `PeersAsked` per diff, filtered at cleanup. Each cell has a dirty bit: **at most one wake message per cell per receiver** is outstanding, i.e. 3 wakes into `manager`. Then size `manager` bulk to the sum of the remaining reliable kinds | structural (3 cells) + enlargement | **`66 = 4·N_max + C + 4`** (`C` = connector workers; pass-6 correction of `62 = 4·N_max + 2·max_outbound + 4`), term by term in "Manager producers" below; reconciled with the mechanical producer list | (i) verified for SetLocalUse and NewTip; FetchBlocks cell is a design |
| B3 | `manager → connection [Initialize/Disconnect/FetchBlocks/NewTip/SetLocalUse]` (not needed for acyclicity once B2 holds; needed for Theorem B and for the timer finding) | forward the same three cells per connection (latest range per peer, latest tip, latest local use), one dirty-bit wake per cell per connection; a manager-side "disconnect sent" flag per `conn_id` makes `Disconnect` one-shot across its 5 send sites (`manager/mod.rs:604, 606, 626, 844, 946`); the connection reads the cells on reaching `Established`, replacing the handshake-time re-schedules | structural | mechanical list (`scripts/producers-ConnectionMessage-33d62a6f.txt`): bulk = `Initialize` 1 + `Handshake` result 1 + one-shot `Disconnect` 1 + 3 wakes = **6 ≤ 10**; `ChildDied` are supervision tombstones, `StopTimeout` is a heap timeout | design |
| B4 | `tx_submission_responder ↔ mempool`; `tx_submission_initiator ↔ mempool` (missing from the v4 JSON, see below) | keep `InsertBatch` as `eff.call` (H4 holds); **remove its timeout** (requirement: an eclipse lever and not admissible under `01` §8; a watchdog may only log or terminate the node, never disconnect a peer); **delete `SubscribeCapacity` and `CapacityAvailable`**: capacity becomes a single-writer cell (writer `mempool`) read by the responder to cap its next `RequestTxIds`/`RequestTxs` (Lemma 3); **`WaitForAtLeast` → a single-writer monotone seq cell** (Lemma 2, M1; see below); size `mempool` bulk so admission never parks | structural + enlargement | `max_inbound` (one `InsertBatch` per responder; the call parks it) + `L` (one `Insert` call per concurrent submit-API request, definition below) + 1 (`NewTip`, or 0 as a cell) = **`max_inbound + L + 1`**; `WaitForAtLeast` and `SubscribeCapacity` no longer occupy it | **decided (Roland): drop when full**, stop requesting while full; today matches except that tx ids are still requested while full (§8(m)) |
| B5 | `mux ↔ blockfetch_initiator` | L1 on `mux → blockfetch_initiator` with the pending range as a latest-wins cell (per-kind check below) | structural (small) | **4 ≤ 10** (`max(10, 2n+4)` at `n = 2`) | per-kind check done below |
| B6 | `cleanup_replies → fetch_blocks` | full (g) filter (id, hash ∈ missing, once) — already a modelled fix, mis-modelled as id-only | structural (as in (g)) | `2·(25 + A + 2) + 3 = 67`, `A = MAX_FETCH_PEERS = 5` | correct the v4 discharge row |

**Code checks for B2 (superseding rule (i), Helen review 7 item 2), at `33d62a6f`:**
* **`SetLocalUse` — latest-wins: yes.** `manager` forwards to the connection (`manager/mod.rs:875–888`); the connection
  assigns `s.desired_use = desired` and calls `converge_use` (`connection.rs:262–265`), which compares only
  `desired_use` with `actual_use` (`:571–585`). Earlier values are overwritten unread. No reply, ack or credit
  ((ii)); one writer per connection, `peer_selection` ((iii)).
* **`NewTip → manager` — latest-wins: yes, along the whole path.** `manager` only forwards the current tip to every
  connection (`manager/mod.rs:864–867`); the connection forwards to its chainsync responder (`connection.rs:256–259`);
  the responder sets `self.upstream = tip` and serves headers from the store via its own `pointer`
  (`chainsync/responder.rs:85–97`). No consumer needs intermediate tips. Single writer: `adopt_chain`
  (`adopt_chain/mod.rs:266`); the version must be the adoption order (a rollback lowers the tip).
* **`FetchBlocks`:** a new design; nothing in code to verify beyond the stash overwrite cited in B3.
* **Side finding:** in `Initial`/`Handshake` the connection re-schedules `FetchBlocks`, `NewTip` and `SetLocalUse` with
  `schedule_after(reconnect_delay)` (`connection.rs:268–282`). These sit in the priority schedule, whose capacity is
  10 with a panic on overflow (`01` §2); one `NewTip` per adopted block during a slow handshake could exceed it.
  The cells of B3 remove this; **to check** whether `schedule_after` shares the `schedule_at` panic.

**Code check (3), mempool admission:** `InsertBatch` is answered in the dequeuing transition: the loop validates and
inserts each tx and then `eff.send(&caller, results)` to the call's oneshot (`mempool/stage.rs:85–98`). A full pool
is an immediate `TxRejectReason::MempoolFull` (`amaru-mempool/src/strategies/in_memory_mempool.rs:85`), so **no path
holds the `InsertBatch` reply until capacity frees** — H4 holds; the only wait is admission into the mempool mailbox,
removed by sizing (B4). Two side notes: (1) `WaitForAtLeast` **does** hold its reply until `seq_no` is reached
(`stage.rs:69–74`, `notify_ready_waiters`); its callers are tx initiators (v4 §4), outside this SCC, but if that is an
`eff.call`, the caller waits on peer-supplied transactions (H4 shape) — **to classify in pass 5**; (2) the
responder's `InsertBatch` timeout terminates the connection (`responder.rs:614–616`), i.e. disconnects a peer for
local congestion, which `01` §8 does not admit (not attributable); with B4's sizing the admission never times out in
`⟦·⟧^∞`, but the code path should not exist.

**Manager producers, derived mechanically** (`scripts/producers.py`, output `scripts/producers-ManagerMessage-33d62a6f.txt`;
every production construction of a `ManagerMessage` plus every `StageRef<ManagerMessage>`/contramap, tests excluded).
Each line below is one script result; the right column is its term in `66 = 4·N_max + C + 4` (pass-6 corrections marked).

| Kind | Construction sites (script) | Queue | Bound after the fixes | Term |
|---|---|---|---|---|
| `AddPeer` | `peer_selection/mod.rs:359` (in `SendBudget`); `:1219` is the `AddPeer` arm of `peer_selection`, whose own `AddPeer` has no production sender (v4 §2) | bulk | `≤ max_outbound` (`using_occupancy` stops dials at the target) | `max_outbound` |
| `ConnectionResult` | `manager/connector.rs:101` | bulk | **`≤ C = DEFAULT_PARALLEL_CONNECTION = 10`** (one per finished attempt; `pump` keeps `C` workers busy, `connector.rs:32, :86`) — pass 6; was `max_outbound` | `C` |
| `RemovePeer` | `peer_selection/mod.rs:339` (`ban_peer`, outside the budget) | bulk | **today unbounded**: sent on every ban, also on a re-ban after cooldown (pass 6). **Requirement:** route it through the B1 dedup helper per `conn_id` ⇒ `≤ N_max` | `N_max` |
| `Disconnect` | `peer_selection/mod.rs:782, 945` (in the budget) | bulk | `≤ N_max` (one per live `conn_id`, `disconnect_sent`) | `N_max` |
| `Accepted` | `accept.rs:29` | bulk | **today unbounded**: one per TCP accept, then the next pull (`accept.rs:39`); the inbound cap runs only in `handshake_complete` (`manager/mod.rs:537–552`), after `Accepted` and `HandshakeComplete` are queued (pass 6). **Requirement:** cap at accept, before the id is minted ⇒ `≤ max_inbound` | `max_inbound` (with `AddPeer`: `N_max`) |
| `HandshakeComplete` | `connection.rs:454` (`eff.call`; reply is a oneshot) | bulk | `≤ N_max` | `N_max` |
| `Listen` | `amaru-node/src/stages/build_node.rs:516` (preload) | bulk | 1 | 1 |
| `SetLocalUse` | `peer_selection/mod.rs:466, 504, 894` | bulk → **cell** | 1 dirty-bit wake | 1 |
| `FetchBlocks` | `fetch_blocks/mod.rs:442, 546` | bulk → **cell** | 1 dirty-bit wake | 1 |
| `NewTip` | `adopt_chain/mod.rs:266` (`manager/mod.rs:111` is the `new_tip` helper, called only from tests) | bulk → **cell** | 1 dirty-bit wake | 1 |
| `ConnectionDied` | `manager/mod.rs:479` (`eff.supervise`) | supervision tombstone | `≤ N_max`; not counted against bulk or the schedule cap (v4 §2) | — |
| `Listen` (tombstone) | `manager/mod.rs:439` (`eff.supervise` of `accept`) | supervision tombstone | `≤ 1` | — |

`StageRef<ManagerMessage>` holders found by the script: `adopt_chain`, `fetch_blocks`, `peer_selection`, `accept`,
`connection`, `connector`, the graph builder, and Mithril's `block_source.rs:151` contramap, which belongs to the
separate Mithril bootstrap graph (it maps `NewTip` into Mithril input; it is not the node's `manager`). No producer
outside the table. **Reconciled (pass 6):** `AddPeer + Accepted ≤ max_outbound + max_inbound = N_max`; `RemovePeer + Disconnect + HandshakeComplete ≤ 3·N_max`; `ConnectionResult ≤ C`; `4` = `Listen` + three wakes. Total **`4·N_max + C + 4`** = 66 at the defaults (`N_max = 13`, `C = 10`), 494 at the mainnet-like config. Production today: `DEFAULT_MAILBOX_SIZE + target_upstream + target_downstream = 10 + 3 + 10 = 23` (`build_stage_graph.rs:71–72`, `types.rs:53`, `lib.rs:97–99`); the earlier "460" was that formula with an upstream + downstream of 450 and is withdrawn. Without the cells, the accept cap and the `RemovePeer` dedup, `SetLocalUse`, `FetchBlocks`, `NewTip`, `Accepted` and `RemovePeer` are unbounded and no capacity suffices.

**B5 per-kind occupancy, `blockfetch_initiator` bulk mailbox** (at `33d62a6f`; the handler is
`Pipelined<Instance>` with `n = 2` slots, `protocol/pipeline.rs:138–224`, `blockfetch/initiator.rs:225–410`).
Preconditions written down first:
* The latest-wins pending range is sound **only because of the cleanup filter** (B6/(g)): blocks for a non-current id are
  dropped at `cleanup_replies`, so a range for a non-current id is worthless and may be overwritten.
* Replacing an **unsent** range must never touch the **in-flight** range: the code keeps them apart (`pending_fetch` vs
  `inflight`, `initiator.rs:228–233`; the overwrite at `:324, :376` assigns only `pending_fetch`).
* **One range per id:** widen adds peers, not ranges (`fetch_blocks/mod.rs:509–549` re-sends the same `from`/`through`
  for the same `req_id` to new peers). Assert in `manager`'s diff dispatch that each `(id, peer)` gets at most one
  range.

| Kind | Producer | Bound | Why |
|---|---|---|---|
| `Network(Registered)` | mux | 1 | once; `pipelined` sets `registered` and arms receive (`pipeline.rs:150–153`) |
| `Network(FromNetwork)` | mux | **1** | the pipeline arms receive on one slot at a time (`recv_armed`, `pipeline.rs:202–216`); `Pull` is injected in-transition, not via the mailbox (`:122–129`, `:213–216`); a `Block` frame's `WantNext` is issued after that frame is consumed (`initiator.rs:331–352`), net zero |
| `Local(RequestRange)` | `connection.rs:252` | **1 wake** with the range cell (now: one per forwarded `FetchBlocks`, unbounded) | latest-wins, preconditions above |
| `Local(Close)` | `connection.rs:598` (`begin_stop`) | 1 | `stopping` set |
| `Internal(Timeout)` | `set_timeout` | 0 in bulk | heap timeout (`effect.rs:448–475`) |
| **Sum** | | **4 ≤ 10** | |

Side finding: at `33d62a6f`, a `Local` message arriving while the send cursor's slot is not in its switch state
**terminates the handler** ("pipeline full", `pipeline.rs:171–175`). A third outstanding range (two in flight with
`n = 2`) therefore kills the blockfetch initiator because of local overload, not peer behaviour. The range cell
removes this: the initiator takes the next range from the cell only when a slot is in switch.

**`WaitForAtLeast` (reclassified; Helen review 8).** At `33d62a6f` it is a blocking `eff.send` from the tx initiator
(`tx_submission/initiator.rs:107–110, 365–368`), and the notification is a blocking `eff.send` from `mempool` into a
contramap of the initiator's own mailbox (`mempool/stage.rs:69–74, 177–187`). This is a **2-cycle `mempool ↔
tx_submission_initiator` that is missing from `wait-graph-v4.json`** (added in `scripts/wait-graph-v4-plus.json`).
The wait it serves is **peer-unbounded**, not a delay: the mempool reaches `seq_no` only when transactions arrive,
which depends on peers or local submitters. The initiator itself is not parked (it returns `Ok(None)` and keeps
dequeuing, `:369`), so the peer's blocking `RequestTxIds` wait already lives in the initiator's protocol state
(`TxIdsBlocking`). **Fix:** a single-writer monotone sequence cell (writer `mempool`, value `last seq_no`; Lemma 2,
M1: sequence numbers only grow). The initiator registers interest, keeps dequeuing, and re-reads on a dirty-bit wake
or by W3. Both edges are deleted.

**`InsertBatch` timeout: remove it.** H4 is shown (reply in the dequeuing transition), so the 5 s timeout on
`responder.rs:608–616` only matters while the mempool mailbox is full, and its effect is to disconnect a peer for
local congestion: an eclipse lever, and not admissible under `01` §8. Requirement: no timeout on this call; a
watchdog may log, or terminate the **node**, but never disconnect a peer.

**`L` defined.** `L` is the maximum number of concurrently outstanding local submissions: each `POST` to the submit
API makes one `eff.call` with `MempoolMsg::Insert` (`amaru-node/src/submit_api.rs:84–88`). The submit API is an input
producer (`01` §1.1). At `33d62a6f` there is **no concurrency limit** on it, so `L` is unbounded today (finding):
make `L` a config constant enforced in the API (excess requests get HTTP 503 without touching the mempool).

**Timer table: `schedule_after` versus `schedule_at` (Helen review 8).** Observed behaviour in pure-stage at
`33d62a6f`: `schedule_after` is `schedule_at(now + delay)` (`effect.rs:418–426`); both go through
`StageEffect::Schedule`, which **panics** when the stage's outstanding schedules reach `priority_mailbox_size` (default
10): `tokio.rs:865–872` ("exceeded priority mailbox size"); the doc comment says the simulation does the same
(`effect.rs:392–397`). It never blocks and never drops. `set_timeout`/`set_timeout_at` use a per-stage heap of
logical slots, replace per slot, and are not counted (`effect.rs:448–475`, `tokio.rs:899–905`). Supervision tombstones
are not counted either (v4 §2). Requirement: **cancel-before-rearm per timer purpose**. Per stage (production uses
from `git grep`):

| Stage | Purposes (site) | Discipline | Outstanding |
|---|---|---|---|
| `fetch_blocks` | `Timeout` (`:454`), `Widen` (`:467`) | `Timeout` cancelled on completion (`:650`) or consumed; `Widen` cancelled before re-arm (`:474`) | ≤ 2 (+1 already-delivered stale) ≤ 10 |
| `track_peers` | `RecheckLedgerHeight` (`:706, :710`) | cancel before re-arm (`:694, :705`) | 1 |
| `forge_block` | `DueLead` (`protocol.rs:154`) | cancel before re-arm (`:166`) + generation | 1 |
| `peer_selection` | `Tick` (`:1068`) | `set_timeout` (heap) | 0 |
| ledger-check child | cadence (`peer_selection/mod.rs:1305`) | one-shot, re-armed on firing | 1 |
| `accept` | `PullAccept` (`accept.rs:39`) | re-armed once per processed `PullAccept` | 1 |
| keepalive initiator | `SendKeepAlive` (`keepalive/initiator.rs:137`) | re-armed once per response | 1 |
| peer-sharing initiator | `Tick` (`peer_sharing/initiator.rs:113`) | cancel before re-arm (`:111`) | 1 |
| tx-submission responder | retry (`responder.rs:735`) | cancel before re-arm (`:716`) | 1 |
| blockfetch initiator | 4 (Registered, one FromNetwork, one range wake, Close) | 4 / 10 ✓ | 4 | ≤ 4 frames (bodies ≤ 90 KiB) | structural (range cell) |
| `connection` | 6 (Initialize, Handshake result, one-shot Disconnect, 3 cell wakes) | 6 / 10 ✓ | 6 | negligible | structural (B3) |
| `connection` | **re-schedule of each `FetchBlocks`/`NewTip`/`SetLocalUse` received in `Initial`/`Handshake`** (`connection.rs:268–282`) | **none**: one schedule per message, re-armed on every firing while the handshake lasts | **unbounded ⇒ panic at 11** |
| `manager` | none | — | 0 |

So every stage is within 10 except `connection`, where a burst of 11 such messages before `Established` (e.g. one
`NewTip` per adopted block during a slow handshake, or repeated `SetLocalUse` to a pending connection) panics the
stage. Classification: a **crash-freedom** violation, not a wait edge (the schedule effect never waits), so it adds no
edge to the wait graph. Fix: B3 (the connection reads the three cells on reaching `Established`; at most one
"retry when established" purpose, cancel-before-rearm).

### (a) `select_chain → fetch_blocks → validate_block → select_chain` (+ `FetchNextFrom` 2-cycle) — **passes via Lemma 4**, with obligations

Not dischargeable by Lemma 1 at the current capacity: `W(fetch_blocks)` is **bounded but > 10** — the
`cleanup_replies` forward at `33d62a6f` is `≤ |asked|·MAX_FETCHED_BLOCKS` `Block`s per live id (each initiator flight
accepts up to `MAX_FETCHED_BLOCKS = 1000`, `blockfetch/initiator.rs:275, 396`, `responder.rs:44`, not the 25 of the
range) plus `NoBlocks`/`PeersAsked`/`NoPeersAvailable` (see (g)); even an LRU hash dedup (TODO at
`fetch_blocks/mod.rs:849`) would give `≤ 25` per id, still `> 10`. Not Lemma 2: `NewBestTip` is **reliable** (the flag is
already cleared and `fetch_blocks` starts a batch from that point; `new_tip` asserts `missing` is clear).

**Token as a conserved count**, expressed through the two stages' typestates (`select_chain ∈ {Holding,
NotHolding}` with `Holding ⇔ may_fetch_blocks`; `fetch_blocks ∈ {Recovering, Busy, Idle}` with
`Busy ⇔ missing.is_some()`, `Recovering` = unprocessed or in-handler `RecoverStoredBlocks`):

`T := #RecoverStoredBlocks(unprocessed or in handler) + #FetchNextFrom(queued or in handler) + [select_chain = Holding]
+ #NewBestTip(queued or in handler) + [fetch_blocks = Busy] = 1`.

* **Initial:** `T = 1` at the `build_stage_graph.rs:199–204` preload of `RecoverStoredBlocks` (the only production
  enqueue, before any stage runs; inventory v2 §2).
* **Moves, not creations:** `fetch_blocks`' `FetchNextFrom` sends (`fetch_blocks/mod.rs:396, 407, 652, 750`, via
  `:758`) are moves. **Per-site obligation:** each runs only in a transition that consumed the token (handles
  `NewBestTip`/`RecoverStoredBlocks`, or turns `missing` from `Some` to `None` in that same transition).
  `select_chain:489` converts an in-handler `FetchNextFrom` into `Holding` (conserves `T`); the then-branch converts it
  into a `NewBestTip` (conserves `T`); `select_chain:302/397` convert `Holding` into a `NewBestTip`.
  `select_chain:443` asserts one side of `T ≤ 1`; `fetch_blocks` `new_tip`/recovery assert `missing` is clear.
* **Sites verified (inventory v3 §C):** `fetch_next_from` (`:755–758`) is called only at 396, 407 (from `new_tip`
  / `recover_stored_blocks`, which assert `missing = None`, `:229, :256`), 652 (same transition sets `missing` from
  `Some` to `None` at `:645`; `:585` returns earlier if already `None`) and 750 (`timeout`, `missing = None` at
  `:746`; the `None` arm does not send). Each consumes the token. Accepted by Helen (review 6).
* **Termination** destroys the token and is **acceptable**: `or_terminate`/`or_terminate_with` call `eff.terminate()`,
  which never resolves (`types.rs:386–390`, `effect.rs:535–553`); both stages are wired before the graph runs and
  carry the root `DropGuard` (`tokio.rs:322–328`), so the runtime aborts every stage (`:200–205`) and the process exits
  with `consensus stage graph terminated unexpectedly` (`run.rs:536–547, 576–577`). Sites: v3 §C (8 in each stage).
  If either stage is ever made restartable, `T` must be re-established on restart (H7).
* **Second token leak — CONFIRMED** (v4 §5, `fetch_blocks/mod.rs:350–353`): `request_missing_blocks`, called only
  from `new_tip` (`:244`), returns on `BoundaryNotFound` with `missing = None`, no `FetchNextFrom`, no terminate; every
  term of `T` is then 0 and no later header restarts fetching (v4 §5 table: it is the only running-state return that
  loses `T` besides the fresh-start one).
  * **What `BoundaryNotFound` means (code check, Helen review 7 item 4).** `find_missing_blocks`
    (`amaru-ouroboros-traits/src/stores/chain_store/read_chain_store.rs:284–300`) walks ancestors of the tip on one
    snapshot via `ancestors_on_snapshot` (`:346–358`), which stops when a header's slot is `≤` the anchor's slot or a
    parent header is not in the store. `BoundaryNotFound` = the walk ended without meeting a stored block or the
    anchor. Two causes: **(α) missing parent header** — a hole in the header chain; the only production
    `remove_header` callers are the offline dev tools (`amaru/src/bin/amaru/cmd/dev/chain/prune.rs:97`,
    `remove.rs:102`), so at runtime this is store inconsistency; **(β) the tip's chain passes below the anchor
    without containing it** — the anchor is advanced concurrently by `adopt_chain` (`adopt_chain/mod.rs:330`) on the
    adopted chain, so a `NewBestTip` for a fork that diverges below the new anchor hits `BoundaryNotFound`
    **transiently**, as a race between `select_chain`'s choice and `adopt_chain`'s anchor move. Both are reachable;
    the arm cannot tell them apart today.
  * **Fix (both causes, no livelock):** distinguish them in `find_missing_blocks` (return the stopping header or a
    reason). (α) ⇒ terminate like the other `or_terminate` sites (store inconsistency). (β) ⇒ **move the token back as
    `fetch_next_from(eff, tip)` with the failing `tip`**, optionally via a delayed self-message. This cannot loop:
    `select_chain`'s `FetchNextFrom` handler (`select_chain/mod.rs:446–489`) sends a new `NewBestTip` only if
    `best_tip.point() != point`; with `point = tip = best_tip` it sets `may_fetch_blocks = true` and holds the token
    until the best tip **changes** (`:302–305`, `:397–404`). Each further `BoundaryNotFound` therefore needs a new
    best-tip change, i.e. new peer input, so there is no O1' livelock. **Residual liveness hole (confirmed by Helen,
    review 8):** the race is reachable, and if the dead fork stays best, fetching stalls. **`select_chain` does not
    prune on anchor moves today:** it never reads the anchor (no reference in `select_chain/mod.rs`); it prunes only
    on invalid validation results (`:81–82`, `:361–428`). `adopt_chain` drags the anchor to `tip − k` on the adopted
    chain (`adopt_chain/mod.rs:310–330`). **Fix:** Praos `maxvalid` only admits forks at most `k` deep, so when the
    anchor moves, `select_chain` must disqualify every candidate whose intersection with the adopted chain is below
    the new anchor and recompute best. The anchor reaches `select_chain` through a single-writer monotone cell
    (writer `adopt_chain`, ordered by height; Lemma 2, M1). Liveness then holds under honest majority with at least
    one honest peer. **Decided (Roland, 2026-11-15): the target is Praos.** The anchor rule is: on every anchor move,
    prune the candidates whose intersection with the adopted chain is below the anchor, then recompute best (filed
    upstream as pragma-org/amaru#1654). Under Ouroboros Genesis, `maxvalid-bg` may prefer a deeper fork by density,
    and the rule would instead be that the anchor does not advance past the common intersection of the candidates
    being compared; §4a states what of the theory depends on this choice and what a Genesis variant must discharge.
    Acceptance tests 7b and 7c.
* **Fresh-start hole:** if ledger tip and recovery hash are both Origin, `recover_stored_blocks` returns at
  `fetch_blocks/mod.rs:265–270` without `fetch_next_from`: `T` drops to 0. Not a `⇝`-deadlock, but an O4/O5
  violation (no `NewBestTip` ever). **Fix:** call `self.fetch_next_from(eff, Point::Origin)` in that branch (a move:
  the branch consumed the token).
* **Consequence for `G^α`:** `select_chain → fetch_blocks` only from `Holding`, and by `T` the receiver is then not
  `Busy`/`Recovering` and no `FetchNextFrom` is in flight, so `B = {Idle}`; `(fetch_blocks, Idle)` has only the
  blocking `Adversarial → peer_selection` (body-hash check before the `missing` test, `fetch_blocks/mod.rs:570–587`).
  `(fetch_blocks, Busy) → select_chain` and `→ validate_block`, `validate_block → select_chain` remain, and
  `select_chain` (`Holding`) → `(fetch_blocks, Idle)` closes no cycle **provided** nothing reachable from
  `(fetch_blocks, Idle)` and `cleanup_replies` returns to `select_chain` or `fetch_blocks`.
* **Remaining obligation — violated at `33d62a6f` (new finding, see (g)).** Inventory v2 §1 concludes that
  `peer_selection`/`block_source` do not reach back. Reading `manager` at `33d62a6f`, I find
  `manager → cleanup_replies` (`Blocks::NoPeersAvailable`/`PeersAsked`, blocking `eff.send(&cr, …)`,
  `manager/mod.rs:795, 798`) and `cleanup_replies → fetch_blocks` (blocking forward, `fetch_blocks/mod.rs:853–877`).
  So `(fetch_blocks, Idle) → peer_selection → manager → cleanup_replies → fetch_blocks` is a residual path, and (a)'s
  Lemma 4 argument is complete only once (g) is discharged. **With the (g) fix** (filtered `cleanup_replies →
  fetch_blocks`, `fetch_blocks` mailbox sized to `W ≤ 57 + 2A`, i.e. 67 with `A ≤ MAX_FETCH_PEERS`), every edge *into* `fetch_blocks` from
  `cleanup_replies` is Lemma-1-discharged, independently of `N`; the obligation is then met and so is the straggler
  half of (a). The token half still needs Lemma 4.
* Theorem B: `NewBestTip` can wait behind up to 10 straggler `Block`s in `box_fetch_blocks`.

### (b) `mux ↔ handler` = component (A) of pass 5 — **discharged by Lemma 1 on `mux → handler`, sized from the session types (Lemma 3)**

**Delivery is a blocking send.** All three `mux → handler` sites are `eff.send`: `Registered` in `register`
(`mux.rs:660`), `FromNetwork` in `PerProto::received` (`:846`, inside `while wanted > 0`) and in `want_next`
(`:858`). The mux never needs to stop block-sending; the handler mailbox only has to be shown never full.

**(i) Ingress bound, per handler.** The mux keeps a per-protocol `wanted` counter: it delivers a frame only against an
unmatched `WantNext` (`:842–849`, `:851–863`) and otherwise buffers bytes up to `max_buffer = ingress_limit(proto)`,
past which the bearer is torn down (`:828–840`; Lemma 3). So `W(FromNetwork → h) ≤ p_h`, the number of `WantNext`
the handler itself has issued and not yet had answered, **independent of the peer**. `p_h` comes from agency: the
`miniprotocol` driver (`protocol/miniprotocol.rs:225–281`) sends `WantNext` only when the protocol state hands agency
to the peer, and `ProtocolState::local` bails off-agency (e.g. `chainsync/responder.rs:274–300`, `(this, input) ⇒
bail`), which terminates the handler. Per protocol (want sites from the state machines at `33d62a6f`):

| Handler | `want_next` sites | `p_h` | `s_h` (Sends a handler can have admitted, call result honoured) |
|---|---|---|---|
| handshake (init/resp) | `initiator.rs:159`, `responder.rs:101` | 1 | 1 |
| chainsync initiator | `IntersectFound` + one per dequeued `RequestNext` (§8(c)) | `d + 1` | 1 |
| chainsync responder | `responder.rs:249, 268, 279–297` | 1 | 1 |
| blockfetch initiator | `recv_armed`, one slot at a time (B5) | 1 | 1 |
| blockfetch responder | after `BatchDone`/`NoBlocks`/init | 1 | 1 |
| tx-submission initiator | `initiator.rs:170, 215–221` | 1 | 1 |
| tx-submission responder | `responder.rs:205, 224, 233–240` | 1 | 1 |
| keepalive initiator / responder | `initiator.rs:179` / `responder.rs:108–131` | 1 | 1 |
| peer-sharing initiator / responder | `initiator.rs:259` / `responder.rs:198–223` | 1 | 1 |
| `done_trap` | never | 0 (+ `wanted` carried over, below) | 0 |

Handler bulk mailbox (capacity 10, the `Effects` default) after the fixes, all producers:

| Handler | `Registered` | `FromNetwork ≤ p_h` | local producers after the fixes | Sum ≤ 10 |
|---|---|---|---|---|
| handshake | 1 | 1 | — (`HandshakeResult` goes to `connection`) | 2 ✓ |
| chainsync responder | 1 | 1 | `NewTip` from `connection` (`connection.rs:258`): **unbounded at `33d62a6f`** (one per adopted tip); B3's tip cell extended one hop, 1 wake. Superseding verified: `local` does `self.upstream = tip` and recomputes `next_header` from the store (`chainsync/responder.rs:85–97`) | 3 ✓ |
| blockfetch responder | 1 | 1 | — | 2 ✓ |
| tx-submission initiator | 1 | 1 | `WaitForAtLeast` seq-cell wake 1 (replaces `WaitForAtLeastReached`); `Close` 1 (`begin_stop` once per stop, `connection.rs:602`) | 4 ✓ |
| tx-submission responder | 1 | 1 | capacity-cell wake 1 (B4, replaces `CapacityAvailable`); `InsertBatch` reply is a oneshot | 3 ✓ |
| keepalive initiator | 1 | 1 | `Close` 1 (`:608`); its timer is on the priority schedule | 3 ✓ |
| keepalive responder | 1 | 1 | — | 2 ✓ |
| peer-sharing initiator | 1 | 1 | `Close` 1 (`:612`) | 3 ✓ |
| peer-sharing responder | 1 | 1 | — | 2 ✓ |
| chainsync initiator | §8(c) | | | 13 ≤ 14 ✓ |
| blockfetch initiator | B5 | | | 4 ≤ 10 ✓ |

So every `mux → handler` edge is an L1 row with no capacity change; the only structural prerequisites are cells that
the fix set already contains (B3 tip cell, one hop further; B4 capacity cell; `WaitForAtLeast` seq cell). With these
rows **mux has no blocking out-edge left**: `mux → reader` and `mux → writer` are `W = 1` (§8(b′)), `Sent` replies go to
call oneshots (`tokio.rs:712–718`), and `done_trap` is a sink (its only effect is `terminate`). The mux is therefore a
**sink** of the residual graph, and every edge *into* it stays a reliable blocking edge: handler `WantNext`/`Send`
(`miniprotocol.rs:228/232/274/278`, blockfetch's own sites), `mux_reader → mux [FromNetwork]` (`mux.rs:573`),
`mux_writer → mux [Written]` (`:382`), `connection → mux [Register/SetSduTimeout]` (`connection.rs:403, 471`, and the
`register` helpers). Nothing is dropped, nothing is resent. **No edge in (A) needs a structural change of its own.**

**`done_trap`** (see also the pass-6 block below: re-register is not only the trap). Installed by `connection` after an initiator's expected stop (`connection.rs:638–690`) with
`Register` for the same protocol id; `do_register` keeps the old `PerProto`, **including `wanted`** (`mux.rs:694–700`).
The trap never asks, so `W ≤ 1 + wanted_carried ≤ 1 + p_prev`, up to `d + 2 = 12 > 10` if the chainsync initiator
stops with pipelined requests outstanding. Not a deadlock (sink), but (finding, to check) a legitimate straggler reply
then reaches the trap, which reports "frame after MsgDone" and terminates the connection. One-line fix: reset
`wanted` when a handler is replaced.

**(ii) Egress bound and the mux mailbox (Theorem B / O4, not needed for Theorem A).** Each handler's `Send` is an
`eff.call` that returns on `Sent`, which the mux emits when the bytes are cut into an SDU for the writer
(`PerProto::next_segment`, `:871–891`); the reply wait is a peer-level wait bounded by the writer's
`sdu_timeout` with teardown (`mux.rs:370–380`). With the call result honoured, `s_h = 1`, and

`W(mux_c) ≤ 1 [FromNetwork] + 1 [Written] + R_c + Σ_{h ∈ H_c} (p_h + s_h)`.

Duplex, all ten roles plus handshake: `Σ = (d + 2) + 10·2 = d + 22`, so **`W(mux_c) ≤ d + 24 + R_c`** (34 + `R_c` at
`d = 10`; current `MUX_MAILBOX_SIZE = 24`, whose doc comment counts one `WantNext` + one `Send` per handler and
misses the chainsync pipeline). `R_c` (`Register`/`SetSduTimeout`/`Buffer` from `connection`) is per converge wave
≤ `1 + 5 + 5 + 5` (timeout, responders, initiators, traps), but `connection` uses blocking **sends**, so admitted
waves can pile up while the mux has not dequeued them: `R_c` has **no bound at `33d62a6f`**. Smallest change for
Theorem B: make `Register`/`SetSduTimeout` a call (reply on processing; the mux is a sink, so it completes), then
`R_c ≤ 1` and **`mux_c = d + 25`** (35 at `d = 10`), ≈ 35 × (16 B + ≤ 64 KiB segment) per connection worst case.
Since the mux is a sink, an undersized mux mailbox only delays its producers (FIFO admission, F1), it cannot close a
cycle.

**The 1 s call timeout (the (b) caveat).** `miniprotocol` ignores `None` from the `Send` call (`:232`, `:278`;
`NETWORK_SEND_TIMEOUT = 1 s`, `protocol/mod.rs:48`) and advances the protocol state. Effect on the bounds:
* **(i) is unaffected.** `wanted` counts `WantNext`, which agency issues whether or not the `Send` completed; a
  timed-out request still in the mailbox is not a delivery. So the Theorem A discharge holds in both `⟦·⟧^∞` and the
  timed semantics.
* **(ii) breaks.** After `None` the handler may issue the next send its session type allows without a peer frame, so
  `s_h ≤ σ_h`: 1 for strict alternation, 2 for the chainsync responder (`AwaitReply` then `RollForward`), `d` for the
  chainsync initiator, `n` for the blockfetch initiator, and **the peer-requested range length** for the blockfetch
  responder (one `Block` send per point) — not bounded by any config constant. The bytes also accumulate in
  `PerProto.outgoing` until the writer's 30 s `sdu_timeout` tears the bearer down. So the mux formula, and the
  claim "a timeout never leaves Sends queued", need **teardown on `None`** (the minimal change already named for
  (b)); it also removes the internal-timeout-not-teardown violation of `01` §2.

**Pass 6 and Helen review 9 (`helen-review-9-mux.md`, the parent's summary of it): holds today vs requirement.**

*`Sent` (Helen's main hole) — does not apply as stated; holds today.* `next_segment` does `eff.send(&sent, Sent)`
(`mux.rs:881`), and `sent` is the call's oneshot (`tokio.rs:712–718`): it never parks the mux and takes no slot in the
handler mailbox, so it is not a term of `W(mux → h)`. What can pile up is `MuxMessage::Send` **on the mux**.

*`s_h` (outstanding `Send` per handler).* **Today:** on success `s_h = 1`, since each `eff.call` awaits. On timeout the
request stays queued and the reply is ignored (`effect.rs:319–320`); `miniprotocol.rs:232–235` and the blockfetch
responder (`responder.rs:230–244`) continue, so `s_h` is unbounded: one served range alone leaves `1 + 1000 + 1 =
1002` (`StartBatch`, `MAX_FETCHED_BLOCKS` bodies, `BatchDone`; `responder.rs:44, :126`), and the next range adds more.
**Requirement R1:** a send timeout tears down the **connection** (not just the handler) ⇒ `s_h = 1`. Recorded in `01`
§8 as the one admissible local-cause teardown (TCP backpressure: the peer is not reading), with the proof obligation
that the internal part of the wait is bounded below the timeout. `s_h` enters the mux mailbox, **not** the handler
mailbox: pass 6's per-handler column `1 + p_h + s_h + local` over-counts; `W(mux → h) = Registered + FromNetwork
+ local`, and R1 is needed for the mux formula and memory (Theorem B), not for the `mux → h` discharge.

*`wanted` and re-register.* **Today:** `want_next` delivers a buffered frame or increments `wanted` with no cap
(`mux.rs:854–861`); the mux enforces nothing, so `p_h` is whatever the handler issues. `Register` always sends
`Registered` (`mux.rs:439 → :660`). Re-register happens (1) via the done trap (`connection.rs:638–688`) and (2) when use
returns, via `start_initiators` registering a **new initiator on the same protocol id** (`connection.rs:736–774`);
`do_register` keeps `wanted`, the frame and the buffer (`mux.rs:694–700`). **Requirement R2:** on every non-trap
re-register, reset `wanted := 0` and clear `incoming`. Without it the new handler's occupancy is up to `2·p_h` (its own
asks plus the inherited ones) and frames meant for the old session are delivered to the new one (and lost to the
old). For the trap, keeping `wanted` is what makes it see post-`MsgDone` frames; a legitimate in-flight reply then hits
the trap and tears down the connection (finding; avoided if initiators send `MsgDone` only with nothing outstanding).

*`WantNext` sites: does outstanding `≤ 1` hold?* Helen's rule ("responders `WantNext` only in `StIdle`, never on
`Registered`") is **sufficient, not necessary**. What the bound needs is **consume-before-rearm (R4):** every
`WantNext` is issued in a transition that consumed the frame answering the previous one, or is the first after a fresh
registration (`wanted = 0`). Per flagged site, at `33d62a6f`:

| Site | State | Previous `WantNext` consumed? | `p_h = 1`? |
|---|---|---|---|
| chainsync responder `responder.rs:279, :283` | `Intersect` | yes: reached only by consuming `FindIntersect` | ✓ holds today |
| chainsync responder `:291, :294, :297` | `CanAwait` / `MustReply` | yes: `CanAwait` by consuming `RequestNext`; `MustReply` from `CanAwait` via `AwaitReply`, which issues no `WantNext` (`:287`) | ✓ holds today |
| keepalive responder `responder.rs:131` | `Waiting` | yes: reached by consuming `KeepAlive` | ✓ holds today |
| peer-sharing responder `responder.rs:223` | `Busy` | yes: reached by consuming `ShareRequest` | ✓ holds today |
| blockfetch responder `responder.rs:217–223` | `Registered` → `Pull` | first ask after registration | ✓ on a fresh registration; needs R2 on re-register |
| every responder `init` via `miniprotocol.rs:224` | on `Registered` | first ask after registration | ✓ on a fresh registration; responders are registered once per connection today, so ✓ holds today; R2 covers any future re-register |

So **`p_h = 1` holds today for every responder**; the "not `Idle`" sites are fine because each follows a consumed frame.
Initiators: handshake, tx, keepalive and peer-sharing initiators issue one `WantNext` per send from a state reached by
consuming the previous reply (pass-6 site table) ⇒ `p_h = 1`. **Chainsync initiator:** pass 6 finds `p_h = 1` in steady
state and **2** when a local `RequestNext` is processed while the post-intersect `WantNext` (`initiator.rs:316`) is still
open (`MustReply`/`CanAwait` arms `:345–348`). **Requirement R3:** either bound it as `p_h = 2` today, or, under the
§8(c) credit, `p_h ≤ d + 1` (one per credited `RequestNext` plus the intersect ask), which already contains the race and
is what the initiator's `R + F ≤ d + 1` sum counts; a guard (no local `RequestNext` while an ask is open) gives `p_h = 1`
but removes pipelining.

*Writer and reader.* Confirmed discharged: `OutgoingSdu ≤ 1` (`sending` gates `mux.rs:446–449, :469–474`; `Written`
clears it), `Read` alternates 1:1 with `FromNetwork` (`:392`, `:463`). `W = 1 ≤ 10` both. **Holds today.**

*Per-handler bounds under the requirements* (`W(mux → h)` = `Registered` 1 + `FromNetwork ≤ p_h` + local; capacity
10, chainsync initiator 14): handshake 2; chainsync responder 3 (needs the tip cell; today `NewTip` per adopted block
is unbounded); blockfetch responder 2; tx initiator 4 (seq cell + one-shot `Close`); tx responder 3 (capacity cell; plus
its inflight timeout on the priority path); keepalive initiator 3, responder 2; peer-sharing initiator 3, responder 2;
blockfetch initiator 4 (B5 range cell, `Close`); chainsync initiator `d + 3 = 13 ≤ 14` (credit + Done-once; R3 inside);
`done_trap` sink. Mux per connection (Theorem B only): `d + 24 + R_c`, `= d + 25` with R1 and `Register` as a call.

### (b') `mux ↔ reader`, `mux ↔ writer` — **pass** (one direction by credit)

`W(reader) = 1` (`Read` sent only after `received` returns), `W(writer) = 1` (`OutgoingSdu` only while `sending` is
false). `mux → reader/writer` discharged; the reverse edges (`FromNetwork`, `Written`) stay reliable blocking, which
is fine. Discharges H3 for the reader's untimed first-byte read.

### (c) chainsync initiator `↔ track_peers` — **real at `33d62a6f`**; fix by per-peer credit + Done-once flag

At `33d62a6f` there is **no** `RequestNext` credit: a recheck can emit one per released deferred header, and
`local` accepts `RequestNext` without ceiling. Reliable both ways (a missing `RequestNext` stalls that peer; results
are session steps). No drop, no disconnect.

**Fix (structural credit):** `track_peers` keeps per connection `outstanding_i = RequestNext sent − RollForward/
RollBackward results received`, sends `RequestNext` only while `outstanding_i < d = PIPELINE_DEPTH`, and
`recheck_deferred` **tops up to `d`** instead of sending one per released header. Then `track_peers → init_i` is
discharged by Lemma 1 if the per-kind bounds below sum to ≤ 14; `init_i → track_peers` stays blocking (backpressure
one way only) ⇒ the cycle is broken. No `N·d` shared mailbox is needed (in-flight results ≤ `N·(d + c)` sit in
`box_track_peers` or are parked); O5 holds by FIFO admission (§5).

Per-kind occupancy of one initiator mailbox (capacity `d + 4 = 14`), from inventory v3 §A. **Fix = credit + a
per-connection Done-once flag in `track_peers`** (Helen review 6, item 4):

| Kind | Producer | Bound after fix | Argument / obligation |
|---|---|---|---|
| `Local(RequestNext)` + `Network(FromNetwork)` (incl. the intersect frame) | `track_peers`; mux | **`R + F ≤ d + 1 = 11`** (v3 §A) | `FromNetwork` only for an unmatched `want_next` (`mux.rs:842–862`); `want_next` once at `IntersectFound` (`initiator.rs:316`) and once per dequeued `RequestNext` (`:343–348`); `AwaitReply` consumes one frame and issues one `want_next` (`:323`), net zero |
| `Local(Done)` | `connection` `begin_stop` (`:593–594`) | 1 | no second `Done` while `stopping` is non-empty (`:571–572`) |
| `Local(Done)` | `track_peers` (`:911, :931, :1063`) | **not capped at `33d62a6f`**; **1 with a per-connection Done-once flag** (part of the fix) | several results can already sit in `track_peers` and turn into several `Done`s before the initiator dequeues the first |
| `Network(Registered)` | mux (`:660`) | 1, consumed before any `want_next` (not concurrent with the pipeline) | |
| `Internal(Pull/Timeout)`, priority | — | 0 | chainsync uses `miniprotocol`; nothing scheduled |
| **Sum** | | **single session with Done-once: `11 + 1 + 1 = 13 ≤ 14` — not yet shown in general** | re-initialisation (`track_peers/mod.rs:892–898` purges `track_peers` state but not the initiator) can add another intersect `want_next` on top of queued frames, so `+1` is a single-session figure. **Obligation:** bound re-inits per live initiator (or drain on re-init), or raise 14 |

**OPEN (reachability):** list every reliable output of `recheck_deferred` and header handling (`NewTip →
select_chain`, `Adversarial → peer_selection`, `Done`/`RequestNext → initiators`) and show no residual path returns
to `track_peers`. Done in inventory v3 §B: `recheck_deferred` sends only via `try_roll_forward` (`:786` `Adversarial`, `:868`
`NewTip`, `:877` `RequestNext`); header handling adds `Done` (`:911, :931, :1063`), `Adversarial` (`:960, :1071`),
`RequestNext` (`:1015, :1049, :1069`). Return paths: the initiator (direct, this cycle), `select_chain` (only
`NewBestTip`, token-discharged), and `peer_selection → manager → connection → track_peers` = cycle (h).

### (d) ledger stake callback `→ track_peers` — **real at `33d62a6f`** (H2); fix: **Lemma 2 edge with M1 and W3** (accepted, Helen review 6)

At `33d62a6f` the callback `block_on`s a bulk send into `track_peers` on the ledger thread while `track_peers`
awaits that thread (`VolatileTipEffect`, `validate_header`): an H2 violation. Until fixed, model per `01` §7: an
edge to `track_peers` from every stage that awaits any ledger effect, which includes a self-loop on `track_peers`.
Mithril has the same shape (`mithril.rs:750`).

**Coalescible under Helen's a)–c), as a Lemma 2 edge** (this supersedes the earlier "fails Lemma 2" note):
* **(ii)** holds: `StakeDistUpdated` itself carries no credit/ack/reply/context. The reliable `NewTip`/`RequestNext`
  that a recheck emits belong to (c) and are bounded there (burst ≤ `|deferred|` ≤ `Σ_i credit_i`).
* **(i) / a) monotone cell** — pick one:
  * **M1 stable snapshots — holds in the code (inventory v3 §D; chosen):** `rotate_stake_distribution`
    (`state.rs:1269–1291`) is the only notifier; it runs only when `most_recent_snapshot() == current_epoch − 1` and
    `slot_in_epoch(tip) ≥ stability_window`, from the historical snapshot store (`overlay.rs:280`);
    `install_stake_distribution` pushes only a strictly greater epoch (`:576–579`); `rollback_to` (`:1032–1065`)
    neither touches `stake_distributions` nor calls the callback, and a fork that re-crosses a boundary skips the
    rotation (`:545–546`). So announced epochs are monotone and never retracted, and a raw-epoch `max` is sound.
    (The Shelley-spec rationale relayed by Helen is no longer needed as justification.)
  * **M2 version order (not needed):** order cell writes by `(ledger-version, epoch)` and keep the latest; correct across
    rollbacks. A raw-epoch `max` is wrong if a rollback retracts an announcement; the current code assigns
    (`max_epoch = max_epoch`), which is version-order "latest" only if delivery preserves ledger order.
* **(iii)**: write the cell under the same lock/release discipline as `resources.put(ResourcePoolSummaries)`, before
  the wake.
* **b) dirty bit** ⇒ `W(ledger → track_peers) = 1`. **Preferred wake: W3** (Helen review 4): drop the wake message;
  `track_peers`' existing recheck timer (`ensure_recheck_armed`) polls the cell. No new API; cost is recheck latency
  ≤ the timer period, a Theorem B bound. Alternative W2 (priority lane) needs a new cross-stage priority send and
  `Σ W(priority producers) ≤ 10`. W1 would require reading the cell on every transition.
* **(iv) / c)**: read the cell in init/restart (today `TrackPeers::new` copies a constructor value and runs no
  effect) and at the start of every `recheck_deferred`.
* **(v)**: an unchanged epoch makes `recheck_deferred` equivalent to a `RecheckLedgerHeight` timer tick; idempotent.
* **(vi)**: non-blocking unconditionally; no-lost-update conditional on `track_peers` liveness, i.e. on (c) being
  fixed.
With this, the callback no longer waits on a stage (H2 restored) and the edge leaves `E_res`.

### (e) `manager ↔ connection` (handshake `call` 10 s / `Disconnect`) — **passes the timeout test**

Inventory v2: on `None` or `Some(false)` the handshake call terminates the bearer (`connection.rs:464–468`), so its
expiry is a bearer teardown ⇒ peer-level, non-blocking edge in `⟦·⟧^∞`. The cycle via the call is gone. Other
`connection → manager` blocking sends, if any, remain to be listed (Helen review 1, item 5).

### (g) `fetch_blocks → manager → cleanup_replies → fetch_blocks` — **real at `33d62a6f`**; fix: filtered forward + Lemma 2 cell

Found while checking (a)'s obligation; missed by both inventory passes; confirmed real by Helen (review 4, checked
against `manager` ~775–800). All three sends block:
* `(fetch_blocks, Busy) → manager`: `ManagerMessage::FetchBlocks` (`fetch_blocks/mod.rs:440`, widen `:544`).
* `manager → cleanup_replies`: `Blocks::NoPeersAvailable` / `Blocks::PeersAsked` (`manager/mod.rs:795, 798`); `cr`
  is the `cleanup_replies` child carried in the message (`fetch_blocks/mod.rs:446, 810`).
* `cleanup_replies → fetch_blocks`: forwards `Block`/`NoBlocks`/`PeersAsked`/`NoPeersAvailable` (`:853–877`).
* Occupancy at `33d62a6f` (inventory v3 §E; Roland's 11:19 correction, with the per-flight figure corrected):
  forwarding filters on `id ≥ curr_id`; `curr_id` advances only on `Block(id' > curr)` and `Done(id)`
  (`blockfetch/initiator.rs:364`); `PeersAsked`, `NoBlocks`, `NoPeersAvailable` do not move it, and until the first
  `Block`/`Done` `curr_id = 0` forwards everything. Each initiator flight accepts up to `MAX_FETCHED_BLOCKS = 1000`
  blocks (`initiator.rs:275, 396`), **not 25**, so per live id `Block ≤ 1000·|asked_i|` (none after the first
  `Done(i)`). `manager` sends exactly one `PeersAsked` or `NoPeersAvailable` per `FetchBlocks` (`:793–798`); each widen
  is another `FetchBlocks` for the same id (`fetch_blocks/mod.rs:549`).
  * **Cap A facts:** `peers: Some` asks ≤ `MAX_FETCH_PEERS = 5` (`:426`, widen room `:509–510`). `peers: None` (weak
    or empty selection) asks every `may_initiate()` connection = every live connection with `local_use = Diffusion`
    (`connections.rs:150–155`), **uncapped** in the fetch loop; `peer_selection` holds the diffusion set to
    `target_upstream_peers` (default 3) only by refusing dials/promotions, and outbound handshakes start as
    `Diffusion` before demotion (`manager/mod.rs:906–909`), so the set can briefly exceed it.
  * **Cap K facts:** a new `req_id` does not wait for a `Block`/`Done` (`:412`); each initiator has one in-flight
    range plus one overwritten stash (`initiator.rs:324, 376`), so each peer produces for ≤ 2 ids; nothing bounds how
    many ids `fetch_blocks` issues. **Under the cleanup filter `K` is irrelevant** (only `cell.req_id` passes).
  * All three edges block and no invariant prevents simultaneous parking (v3 §E gives an interleaving). **Real.**
**Chosen fix (Helen review 4): make `cleanup_replies → fetch_blocks` Lemma-1-bounded by filtering on local knowledge.**
1. `fetch_blocks` publishes `(req_id, missing-hash set)` in a **single-writer last-value cell** (Lemma 2: (i) writes
   ordered by `req_id` and by shrinking `missing` within an id; (ii) the cell carries no obligation; (iii) written
   **before** `FetchBlocks → manager`; (iv) `cleanup_replies` reads it on every message; (v) a stale read only
   forwards something `fetch_blocks` already ignores; (vi) non-blocking). **No `fetch_blocks → cleanup_replies`
   message**: that would add the reverse edge and a new cycle.
2. `cleanup_replies` forwards a `Block` only if `id == cell.req_id ∧ hash ∈ cell.missing ∧` not yet forwarded for
   that id (local set, reset when `req_id` changes); `NoBlocks` at most once per `(id, peer)`;
   `PeersAsked`/`NoPeersAvailable` only for `cell.req_id`. `BlockReceived → block_source` and statistics still see
   every block.
3. **Causality:** the cell write precedes `fetch_blocks → manager → connection → initiator → cleanup_replies`, so at a
   request switch at most the old and the new id's budgets are in flight.
4. **Bound:** `W(cleanup_replies → fetch_blocks) ≤ 2·(25 + A + 2)` with `A = max |asked_i|` (initial selection plus
   one widen step per `FETCH_WIDEN_DELAYS` entry, 3 at `33d62a6f`; widen is capped by `MAX_FETCH_PEERS` room at
   `:510`; the broadcast path `peers: None` asks every initiating connection, so `A ≤` the configured maximum of
   initiating connections — see the connection cap in (h)). **Fix addition (Helen review 6):** an explicit
   `MAX_FETCH_PEERS` cap on the broadcast loop too (`manager/mod.rs:767–777` iterates all of `may_initiate()`
   uncapped), so `A ≤ MAX_FETCH_PEERS = 5` and the `fetch_blocks` mailbox `2·(25 + A + 2) + 3 = 67` does not scale
   with `N_max`. Plus 1 token (`NewBestTip`/`RecoverStoredBlocks`/`FetchNextFrom`, Lemma 4) and 2 armed self-schedules
   (`Timeout`, `Widen`; counted conservatively). **Size `fetch_blocks`' mailbox to `2·(25 + A + 2) + 1 + 2 = 57 + 2A`.**
   Independent of `N` given the cap on `A`. **`K` (number of live ids) is irrelevant under the filter**: only
   `cell.req_id` and its predecessor can be forwarded, so `W(cleanup_replies → fetch_blocks) ≤ 2·(25 + A + 2) + 3`
   regardless of how many requests were issued.
5. **Effect:** breaks (g), the straggler half of (a), and every path ending in `fetch_blocks`. `manager →
   cleanup_replies` stays blocking (no longer on a cycle through `fetch_blocks`). Lemma 4 is still needed for the
   token.

**Rejected options (and why):**
* **`PeersAsked` as the reply of a call** `fetch_blocks → manager`: same cycle — `fetch_blocks` then waits on
  `manager`, which still waits on stages that reach `fetch_blocks`; H4 fails (the reply is not produced in the
  dequeuing transition independently of other stages).
* **Window + credit on `fetch_blocks → manager`:** bounds the wrong edge; the unbounded inflow is the forwarded block
  stream into `fetch_blocks`, not `FetchBlocks` into `manager`.
* **`cleanup_replies` capacity ≥ 125 + k** (figure from before the 1000-per-flight correction; worse now): sound only with a proof bounding *all* inflow into `cleanup_replies`,
  including streams of timed-out requests, which depends on `N` and on pipelining. Fallback only.

**(g′) `cleanup_replies → block_source → peer_selection → manager → cleanup_replies`** — **real** (inventory v3 §g′:
simultaneous parking, no token ties the four transitions). Not through `fetch_blocks`, so the (g) fix does not cut it.
**Fix: break it at `block_source → peer_selection` by Lemma 1** (Helen review 5). One non-blocking edge per cycle is
enough, so `cleanup_replies → block_source` and `manager → cleanup_replies` stay blocking. `block_source` sends to
`peer_selection` only `Adversarial`: `:128` on every `BlockReceived` for a point already `Invalid` (repeats per copy),
`:152` on failed validation, once per peer in the point's `Pending` set (a `BTreeSet`, `:131`), repeated across
points. Discharged by the shared Adversarial dedup in (h).

**Rejected: bounding `manager → cleanup_replies`.** One `PeersAsked`/`NoPeersAvailable` per `FetchBlocks`, but
`FetchBlocks` is not token-bounded over time: a stuck `cleanup_replies` leads to the 5 s `Timeout` → `FetchNextFrom` →
`NewBestTip` → new request + widens, so `K` grows during the stall; also each flight accepts 1000 blocks.

**Reserve option (not needed now): `BlockReceived` as a resource** — a union-merged map keyed by block hash, written
by `cleanup_replies`, consumed by `block_source` on `Validation`; removes `cleanup_replies → block_source`; the
`Invalid` → immediate-`Adversarial` path (`:128`) moves to the writer side.

### (h) `track_peers → peer_selection → manager → connection → track_peers` — **real at `33d62a6f`**

Inventory v3 §F: `track_peers → peer_selection` (`Adversarial`, `:786, :960, :1071`), `peer_selection → manager`
(`RemovePeer` from `ban_peer`, `:339`), `manager → connection` (`Disconnect`, `:626, :844, :946`; the connection
mailbox also takes `FetchBlocks`, uncollapsed `NewTip` per adopted tip `:866`, `SetLocalUse`, `Initialize`),
`connection → track_peers` (`Terminated`, `connection.rs:320–328`, from `teardown` on `Disconnect` `:216–217`; shares
`track_peers`' 10 slots with every initiator's per-header results). No invariant stops the four parks.

**Fix: discharge every `Adversarial → peer_selection` edge (cuts (h) and (g′)).**
* **Seven `Adversarial` sites, none deduped at `33d62a6f`** (v3 §G5): `track_peers:786, :960, :1071`;
  `fetch_blocks:574` (hash mismatch, before the `missing` check, so stragglers send too); `fetch_blocks:871`
  (`cleanup_replies` decode failure); `block_source:128, :152`. `peer_selection` drops a repeat only after dequeuing
  (`:1206–1208`, per peer), i.e. after the slot was taken.
* **Dedup at the source** (Helen review 7, superseding review 6's `7·N_max` variant): one helper used by all 7
  sites, doing an atomic check-and-set per `conn_id` on a grow-only resource; the resource write linearises, so at
  most one `Adversarial` per `conn_id` is ever sent: `W(Adversarial → peer_selection) ≤ N_max`. (Review 6's
  check-then-set by each site separately gave `≤ 7·N_max = 91 > 23`; pass 4 modelled that variant.) Not a drop: a
  duplicate report carries no new obligation (ban is idempotent, `:1206–1208`). `Adversarial` stays a reliable
  **message**; how soon a bad peer is cut is Theorem B.
* **`peer_selection` producers (v3 §H1, complete):** `Initialize` (preload, `build_stage_graph.rs:231`, once); the 7
  `Adversarial` sites; `Resolved` from its own `detach` (`:664`, one per DNS candidate); `AddPeer` has no production
  sender (`:1214`); priority: `Tick` (one armed `set_timeout`, `:1068`); `ledger-check` sends nothing back
  (`:1297–1298`); **`manager` never sends `PeerSelectionMsg`**. ⇒ **`peer_selection` bulk `≥ 1 + N_max +
  max_outbound`** (`W(Resolved) ≤ max_outbound` holds in code, v4 §2: in-flight resolves are in `pending_resolve`,
  counted in `using_occupancy`). 17 at the defaults, within the current `10 + N_max = 23` while `max_outbound ≤ 9`.
* **`ban_peer` bypasses the regulate budget** (v3 §G4): a regulate round sends `≤ SendBudget = U + D` (default 13),
  but each processed `Adversarial` for a non-cooling peer sends one `RemovePeer` (`:339`) outside it, with no numeric
  cap (`≤ N_max` per processed `Adversarial` batch with the cap below). So `manager`'s sizing must include every
  `peer_selection → manager` message plus every other producer: **`manager`'s full producer table is pending the code
  agent's pass 4.** `peer_selection → manager` need not be discharged for (h)/(g′) once the `Adversarial` edges are,
  but it is an edge of the 15-SCC and must appear in the discharge table.
* **Connection cap at accept (Helen review 6; replaces the stall lemma).** v3 §H3: `conn_id`s are minted in the
  network resource (`amaru-network/src/connection.rs:79–82`) on `connect` (connect worker) and `accept` (accept
  stage), **not** by `manager`; `accept` mints while `manager` may be parked, so the stall lemma of review 5 **fails
  and is dropped**. Fix: refuse or close **before minting an id** when live ids `≥ N_max = max_inbound +
  max_outbound`, one config constant. Then every `N_max`-dependent bound holds unconditionally.

**FINDING (resource exhaustion, independent of deadlock).** At `33d62a6f` `max_inbound` (default 10, set from
`target_downstream_peers`, `build_stage_graph.rs:99`) is enforced only at `handshake_complete`
(`manager/mod.rs:537–540`); `accept` (`accept.rs:27–29`) allocates a `conn_id` and starts a connection stage
first. Pre-handshake connections are therefore **unbounded** (each holds a stage, a socket and mailboxes until the
handshake times out or is refused). There is no single connection cap (v3 §H2); `target_upstream_peers` is a soft
selection target.

### (m) `mempool ↔ tx_submission_responder` — **real (v4 §4); fix B4**

Edges found in v3 §G1 via carried refs: `mempool → tx_submission_responder` on `caller`/`capacity_callback`
(`SubscribeCapacity`, `Insert`, `InsertBatch`, `WaitForAtLeast`; `mempool :70, :85, :99, :187, :195`;
`responder.rs:687–692`), plus the responder's sends into `mempool`. Rules to classify each edge against (Helen
review 6, item 7) before any fix is proposed:
1. **"Mempool full" is not an A-int delay.** Space frees only through block adoption, which depends on peers, so a
   responder waiting on mempool admission is a **peer-unbounded** wait (not erased by `⟦·⟧^∞`, must not sit on a
   residual cycle).
2. The responder **never blocks on admission when full**; it uses TxSubmission2's own flow control to request fewer
   (or zero) transactions. Protocol check (Ouroboros Network Specification, `02`, §3.9): in `StIdle` the server has
   agency (Fig. 3.8) and the timeout table lists no timeout for it (Table 3.11; only `StTxIdsNonBlocking` and `StTxs`
   are timed, 10 s), so staying quiet is legal for as long as needed.
3. Admission is a **`call` with a oneshot reply** ⇒ the reply edge is non-blocking.
4. Mempool → responder notifications (capacity) are **superseding** ⇒ a Lemma 2 cell (latest capacity), not queued
   messages.
5. The responder's **ingress** is bounded by its own requested counts (Lemma 3).

Classification (v4 §4): `InsertBatch` is an `eff.call` that parks the responder on mempool admission (`responder.rs:608–612`,
5 s timeout, then the connection is terminated) — violates rule 2's "never block when full" only through admission,
since the reply is immediate (code check (3) above); `SubscribeCapacity` (`:692`) and `CapacityAvailable`
(`mempool/stage.rs:193–196`) are blocking sends, the latter superseding in value; the reply is a oneshot (rule 3
holds); ingress is bounded by the responder's requested counts (rule 5 holds, `:502–510`, `:553–556`). Fix: B4.

**Decided (Roland, 2026-11-15): drop when full.** The responder drops the batch when the mempool is full and stops
requesting tx ids and txs while full; it resumes when capacity returns, via the mempool capacity cell and its wake.
No buffering, no retry, no acks withheld beyond what the protocol needs.

*Protocol legality of dropping* (Ouroboros Network Specification §3.9.1): `ack` in `MsgRequestTxIds*` is "the number of
outstanding transaction identifiers that can now be acknowledged", counted in FIFO order; nothing in the protocol ties
an acknowledgement to the transaction having been fetched or accepted, and `MsgReplyTxs` itself may omit requested
ids (treated "as if this peer had never announced them"). So acknowledging a dropped transaction, or an id whose body
was never requested, is protocol-legal. The only constraints are: `MsgRequestTxIdsBlocking` iff no unacknowledged ids
remain, the outstanding-id bound, and never re-requesting an id.

*Today (`33d62a6f`) vs requirement:*

| Behaviour | Today | Requirement |
|---|---|---|
| Bodies while full | not requested: `txs_to_request` stops at `is_near_capacity` (`responder.rs:553`); if `Pending` ids remain, `AwaitingCapacity` sends nothing (`:164–166`, `:465–466`) | **holds** |
| Tx ids while full | still requested when no `Pending` id is left (`:469–471`, `:627–628`, `:766`): one more window (≤ `max_window`) is pulled while full, then the bodies are gated | **requirement:** gate `RequestTxIds` on the capacity cell too |
| `MempoolFull` at insert (race between the check and the insert) | per-tx rejection is only logged (`:618–622`); entries were set `Done` before the insert (`:598–605`) and are acknowledged on the next `RequestTxIds`: **dropped**, no buffer, no retry | **holds** |
| Ids held while full | `Pending` ids stay unacknowledged until capacity returns (bounded by `max_window`); their bodies are fetched later | allowed as "resume" (no body is buffered, no request outstanding); a stricter variant acknowledges them unfetched (legal, see above) — design choice, not needed for any bound |
| Resume | `SubscribeCapacity` (blocking send, `:692`) → `CapacityAvailable` → `recheck_back_pressure` (`:116–125`, `:746–768`) | **requirement:** capacity cell + dirty-bit or W3 wake (B4); the two sends are deleted |
| Admission wait | `InsertBatch` call with 5 s timeout, then terminate (`:607–617`) | **requirement:** remove the timeout (B4); with sizing, admission never waits |

So today's code already drops rather than buffers, and stops fetching bodies while full; it does not yet stop
requesting tx ids while full, and its wake is the two blocking sends that B4 replaces.

*Occupancy bound.* The drop rule does not change the mempool mailbox bound: each responder still has at most one
`InsertBatch` call outstanding (the race case is dropped by the mempool's immediate reply, H4), so the bound stays
**`max_inbound + L_max + 1`** with B4. For reference, today's code also puts one `SubscribeCapacity` per responder
(the `capacity_subscribed` flag, `:682–692`) plus one `WaitForAtLeast` per tx-submission initiator (≤ `N_max`) into the same mailbox, i.e.
`2·max_inbound + N_max + L + 1` (with `L` unbounded today); B4 removes the second and third terms.

### Summary at `33d62a6f`

| Cycle | Verdict | Discharge |
|---|---|---|
| pre-fix `manager ↔ peer_selection` (`9a4273855`) | flagged | — |
| post-fix pair | passes | acyclic |
| (a) chain pipeline | passes via Lemma 4 once (g) is fixed; token sites verified; termination exits the process; token holes (O4/O5): fresh start, and `BoundaryNotFound` (**confirmed**) | `T = 1`; `fetch_next_from(Origin)`; `BoundaryNotFound`: terminate on store hole, `fetch_next_from(tip)` on the anchor race |
| (b) mux ↔ handler = pass-5 component (A) | **passes** | Lemma 1 on all `mux → handler` edges, `FromNetwork ≤ p_h` by agency and `wanted` (Lemma 3), handler sums ≤ 4 ≤ 10 with the tip/capacity/seq cells; mux becomes a sink. Teardown on `None` needed only for the mux formula (Theorem B) |
| (b') mux ↔ reader/writer | passes | Lemma 1 |
| (c) chainsync ↔ track_peers | **real**; fix discharges (v4 §3) | per-peer `RequestNext` credit + Done-once flag; `13 ≤ 14` confirmed, `AwaitReply` adds nothing |
| (d) ledger callback | **real** (H2) | Lemma 2 edge, **M1** (holds in code, v3 §D), dirty bit, **W3**, read in init + every recheck — accepted |
| (e) manager ↔ connection handshake | passes (expiry = teardown) | peer-level edge |
| (g) fetch_blocks → manager → cleanup_replies → fetch_blocks | **real** (v3 §E) | filtered forward on a `(req_id, missing)` Lemma 2 cell + explicit `MAX_FETCH_PEERS` on broadcast; `fetch_blocks` mailbox 67 (Lemma 1); `K` irrelevant |
| (g′) cleanup_replies → block_source → peer_selection → manager → cleanup_replies | **real** | source-dedup helper (`≤ N_max`), `peer_selection ≥ 1 + N_max + max_outbound`; plus B2 for `manager` |
| (h) track_peers → peer_selection → manager → connection → track_peers | **real** | as (g′); `N_max` from the cap at accept |
| (m) mempool ↔ tx_submission_responder | **real** (v4 §4) | B4: delete `SubscribeCapacity`/`CapacityAvailable`, capacity cell, size mempool; **drop when full** (decided), gate `RequestTxIds` on capacity |

## 9. Required capacities versus defaults (after the fixes of §8 and B1–B6)

Per Helen review 7 item 1: every size is a formula in config constants (`N_max = max_inbound + max_outbound`,
`MAX_FETCH_PEERS = A`, `d = PIPELINE_DEPTH`, `L` = max concurrent submit-API `Insert` calls, defined in §8), computed where the stage is built; Theorem B
uses the enlarged size (queueing delay grows linearly with capacity).

**Memory model.** A mailbox is a tokio bounded `mpsc` of `Box<dyn SendData>` (`pure-stage/src/tokio.rs:146–158`):
capacity is a semaphore count, slots are 16-byte boxes allocated in blocks as occupancy grows, so an enlarged
capacity costs memory only when it is used. Worst case = occupancy × (16 B + message heap size). Message sizes are
**assumptions** (not measured): control messages ≤ 1 KiB including trace context; a `Block`-carrying message ≤ the
maximum block body size, taken as 90 KiB (current mainnet parameter, environment data, not verified here); an
`InsertBatch` ≤ the responder's `fetch_batch_bytes`. Configs: **defaults** `max_outbound = 3`, `max_inbound = 10`
(`N_max = 13`); **mainnet-like (assumed, not sourced)** `max_outbound = 20`, `max_inbound = 100` (`N_max = 120`).

| Mailbox | Required capacity (formula) | Defaults: required / current | Mainnet-like: required | Worst-case memory (defaults / mainnet-like) | Kind of change |
|---|---|---|---|---|---|
| `peer_selection` | `1 + N_max + max_outbound` (Initialize + source-deduped Adversarial + Resolved) | 17 / 23 ✓ | 141 (current formula `10 + N_max` = 130 ✗) | 17 KiB / 141 KiB | structural (dedup helper) + formula |
| `manager` | `4·N_max + C + 4` (AddPeer + Accepted ≤ N_max with cap at accept; RemovePeer deduped, Disconnect, HandshakeComplete ≤ N_max each; ConnectionResult ≤ C = 10; Listen; 3 cell wakes) | 66 / 23 ✗ | 494 | 66 KiB / 494 KiB | structural (3 cells) + enlargement |
| `fetch_blocks` | `2·(25 + A + 2) + 3` with `A = MAX_FETCH_PEERS` | 67 / 10 ✗ | 67 | ≈ 4.5 MiB / same (≤ 50 `Block`s × 90 KiB) | structural (filter) + enlargement; independent of `N_max` |
| chainsync initiator | `d + 3 = 13` per session (credit + Done-once) | 13 / 14 ✓ | 13 / 14 ✓ | ≤ 14 frames | structural (credit, flag) |
| blockfetch initiator | `2n + 4` with range cell (pending per-kind check) | 8 / 10 ✓ (pending) | same | ≤ 10 frames (bodies ≤ 90 KiB) | structural (small) |
| `mux` (per connection) | not needed for Theorem A (sink after §8(b)); Theorem B: `d + 24 + R_c`, `R_c ≤ 1` with `Register` as a call | 35 / 24 ✗ (Theorem B only) | 35 | ≈ 35 × 64 KiB worst case per connection | enlargement + teardown on `None` + `Register` call |
| protocol handlers (10 roles) | `1 + p_h +` local wakes; `p_h = 1` except chainsync initiator (§8(c)) | ≤ 4 / 10 ✓ | same | negligible | cells already in the fix set (tip cell to the chainsync responder) |
| `done_trap` | sink; `1 + wanted carried` (≤ `d + 2`) | ≤ 12 / 10 (irrelevant: sink) | same | negligible | reset `wanted` on handler replacement (finding) |
| `connection` | 5 (Initialize, one-shot Disconnect, 3 cell wakes) | 5 / 10 ✓ | 5 | negligible | structural (B3) |
| `mempool` | `max_inbound + L + 1` (one `InsertBatch` per responder, `L` submit-API calls, NewTip or 0 as cell); `WaitForAtLeast`, `SubscribeCapacity` become cells | `11 + L` / 10 ✗ | `101 + L` | `max_inbound × fetch_batch_bytes` dominates | structural (B4) + enlargement; `L` needs a cap (finding) |
| `cleanup_replies` | not needed (off-cycle after B6) | — / 10 | — | — | none |
| `track_peers` | not needed for Theorem A (edges into it are one-way after the fixes); Theorem B: `N_max·(d + 1)` results + `N_max` `Terminated` | — / 10 | — | — | none (Theorem B may want `N_max·(d+2)`) |
| `block_source`, `validate_block`, `adopt_chain`, `select_chain` | not needed for Theorem A (off-cycle after the fixes) | — / 10 | — | — | none |
| priority schedule (each stage) | purposes per stage (timer table, §8): all ≤ 2 except `connection` (unbounded re-schedules ⇒ panic) | ≤ 2 / 10 ✓ except `connection` ✗ | same | negligible | B3 for `connection`; elsewhere already cancel-before-rearm |

At the defaults only `manager`, `fetch_blocks` and `mempool` need enlargement; `peer_selection` fits once the source
dedup exists. At mainnet-like configs `peer_selection`'s current formula falls short by `max_outbound − 9`.

## 10. Deliverable for Theorem A on this graph, and acceptance tests

**Deliverable (Helen review 6, item 6): a discharge checker, not a cycle list.**
* **Script:** reads the wait graph (`wait-graph-vN.json`, closed per §1), deletes every edge that has a discharge
  record, recomputes SCCs, and **passes iff the remainder is acyclic**: every SCC a singleton and no blocking
  self-loop (self-loops include the template's cross-instance loops, §1). It prints the surviving SCCs otherwise.
  The existing SCC script (`scripts/wait-graph-sccs.py`, fork commit `cc57103ca`) is the second half; the deletion
  step and the record format are not written yet.
* **Discharge table** (input to the script, and the human-checkable artefact): one row per deleted edge with
  *edge* (sender → receiver, message kinds), *lemma* (1 occupancy, 2 superseding cell, 3 ingress teardown, 4
  state-indexed), *W bound* (formula, with its parameters `A`, `N_max`, `d`, …), *capacity* (derived from config,
  not a literal), *code location* (send site and the invariant's sites). A row without a cited bound is not a
  discharge. Edges that are non-blocking by construction (calls whose expiry is a teardown, `try_send`, oneshot
  replies, cells) are recorded as such, with location.
* **What-if after review 8:** on `scripts/wait-graph-v4-plus.json` (v4 plus the two `mempool ↔
  tx_submission_initiator` edges), the review-7 fix set leaves that new 2-cycle; adding the seq cell (both edges
  deleted) leaves **no SCC and no self-loop** (`scripts/what-if-review8-fixes.txt`; minimal set
  `what-if-review8-minimal.txt`). Timer fixes add no edges (schedules never wait). The v4 JSON also omits other
  protocol stages (chainsync/blockfetch responders, keepalive, peer sharing, tx initiator, handshake); their mux
  edges must be added before the result counts.
* **Status (pass 5, v5 graph, 78 blocking edges):** v5's own `after` set (22) plus `what-if-v5-core.txt` (enlarged
  `manager`/`fetch_blocks`/`mempool` as formulas, stake cell) leaves only (A); plus `what-if-v5-mux.txt` (§8(b)) the
  remainder is **acyclic: 45 discharged, no SCC, no self-loop**. Rows still to be written into the discharge JSON
  with their bounds: the 12 core rows and the 11 mux rows.
* **Status (pass 4):** the deletion step and row format exist (`f54f38993`, `wait-graph-v4-discharge.json`); both
  modes exit 1. With B1–B6 added (reproduced with `scripts/what-if-sccs.py`), the remainder is acyclic, so the
  checker **would pass** once those rows carry verified bounds; B5's per-kind check and B4's `WaitForAtLeast`
  classification are still pending.
* Rows expected after the proposed fixes: `select_chain → fetch_blocks` (L4, `T = 1`); `cleanup_replies →
  fetch_blocks` (L1, `≤ 2·(25 + A + 2) + 3`, cap 67); the `Adversarial → peer_selection` edges and `Resolved` self-loop (L1, `≤ N_max`
  with the source dedup, cap `≥ 1 + N_max + max_outbound`); the `→ manager` edges (L1 after B2, cap `4·N_max + C + 4`); `track_peers → chainsync initiator` (L1, 13 per session, confirmed v4 §3); ledger → `track_peers` (L2, M1 + W3); `mux ↔ reader/writer` (L1, 1); handshake call (teardown on
  expiry); mempool (B4); `mux → blockfetch_initiator` (B5, pending).

**Acceptance tests**

1. `9a4273855`: flags `manager ↔ peer_selection`.
2. `33d62a6f` (no fixes): the checker reports the 16-SCC and the `mempool ↔ tx_submission_responder` SCC; with only
   the `NewBestTip` row it reports 15 + 2. The `manager`/`peer_selection` pair alone passes.
3. The ledger callback is flagged as an H2 violation (non-stage producer that a stage waits on).
4. `mux ↔ reader` is discharged by credit (`W(reader) = 1`).
5. A seeded blocking `manager → peer_selection` edge is flagged.
6. (a) is discharged via Lemma 4 (`T = 1`) and **flagged once the `may_fetch_blocks` gate is removed** (seeded bug:
   `select_chain` sends `NewBestTip` unconditionally).
7. **Fresh start:** ledger tip and recovery hash both Origin, one honest peer: reaches `CanValidateHeaders` on a
   fetched block (fails at `33d62a6f`; passes after `fetch_next_from(Origin)` at `fetch_blocks/mod.rs:265–270`). O4/O5.
   **7b. `BoundaryNotFound` injection (Helen review 7's "test 8"):** inject `BoundaryNotFound` for a `NewBestTip`,
   once as a store hole (missing parent header) and once as the anchor race (fork below a freshly advanced anchor).
   Pass iff the node either terminates (hole) or fetches within bounded time after the best tip changes (race), with
   no repeated `NewBestTip`/`BoundaryNotFound` loop without new peer input. Fails at `33d62a6f` (confirmed: the arm
   at `fetch_blocks/mod.rs:350–353` drops the token). O4/O5 and O1'.
   **7c. Anchor race (Helen review 8's "test 9"):** script a race in which `adopt_chain` moves the anchor past the fork point of
   `select_chain`'s current best. Pass iff the node switches best within bounded time (Praos rule: disqualify
   candidates intersecting below the anchor) and keeps fetching. Fails at `33d62a6f` (`select_chain` does not read
   the anchor).
8. **(g) fix:** `cleanup_replies → fetch_blocks` discharged by Lemma 1 at 67 with `A ≤ MAX_FETCH_PEERS`, including
   on the broadcast path. Seeded bugs flagged: filter removed; cell written after `FetchBlocks → manager`; a
   `fetch_blocks → cleanup_replies` message added; broadcast loop without the `MAX_FETCH_PEERS` cap.
   Simulation (safety half): many peers streaming duplicate/straggler blocks (up to 1000 per flight) across request
   switches never park `cleanup_replies` on `fetch_blocks`.
9. **(h)/(g′) fix:** with the source-dedup helper at all 7 `Adversarial` sites and `peer_selection ≥ 1 + N_max +
   max_outbound`, the `Adversarial` edges and the `Resolved` self-loop are deleted and neither (h) nor (g′) survives, while `cleanup_replies →
   block_source`, `manager → cleanup_replies` and `connection → track_peers` stay blocking. Seeded bugs: any one
   site skipping the set ⇒ flagged. Simulation (safety half): one invalid block held by many peers, delivered
   repeatedly, plus repeated header failures, never parks a sender on `peer_selection`.
10. **(c) fix:** credit + Done-once: per-kind sum ≤ 14 checked; seeded bug: Done-once flag removed ⇒ flagged; re-init
    without the bound ⇒ flagged until the general bound is shown.
11. **Connection cap:** every capacity in the discharge table is derived from `N_max`/`MAX_FETCH_PEERS`/`d`; the
    checker fails on a literal or a missing cap. Separate test for the **finding**: with the cap at accept, a flood of
    pre-handshake connections never creates more than `N_max` ids (fails at `33d62a6f`).
12. **Mechanical closure:** the SCC script with `StageRef`-in-message and `send_any` edges reproduces the 16-SCC
    (v3 §G3); without them it misses the `cr` join (regression check for the extractor).
13. **(m):** once classified (pass 4), a responder facing a full mempool never parks on admission; the capacity
    notification is a cell.
14. **(b) / component (A):** with the nine `mux → handler` rows (L1, `FromNetwork ≤ p_h`) the checker leaves mux as
    a sink and passes. Seeded bugs flagged: a handler issuing a second `want_next` while the peer has agency (sum
    rises); the `connection → chainsync_responder` `NewTip` as a plain send (unbounded); a `mux → handler` delivery
    that ignores `wanted`. Simulation: a peer that stops reading TCP while sending at full rate never parks the mux on
    a handler; with teardown on `None`, no handler has two `Send`s admitted.
15. **Chainsync `MsgDone` with replies in flight is impossible** (Helen review 11): drive the initiator to
    `IntersectFound` (one `RequestNext(10)`), deliver one `RollForward`, then `Close`. Pass iff `MsgDone` is not sent
    until 9 more `RollForward`/`RollBackward` have been received (`AwaitReply` not counted) and the send-site assertion
    never fires. Fails at `33d62a6f` (`CanAwait(0) → Idle` shortcut). Same for `Idle + RequestNext`.
16. **Restart orphans** (Helen's "test 10"): kill each per-connection initiator (chainsync, blockfetch, tx, keepalive,
    peer sharing) mid-session, with and without a prior `Close`. Pass iff either the connection is torn down (R2) and
    `track_peers`, `fetch_blocks` and the mempool hold no entry for the dead handler afterwards, or a replacement is
    registered only after `Done` with `wanted = 0` and empty `incoming`; no lost `RequestNext` stalls a follower; no
    frame of the old session reaches the replacement or a trap.
17. **Schedule overflow** (Helen's "test 11"): hold a connection in `Handshake` while the manager delivers more than 10
    `FetchBlocks`/`NewTip`/`SetLocalUse`. Pass iff no panic and the priority high-water mark of every stage stays ≤ 2
    (plus tombstones). Fails at `33d62a6f` (panic in `connection`). Also: the simulation panics on a send to a
    never-registered name (M2).

## 11. Known gaps and weakest points

0. **Requirements for the rewrite** (pass 6, Helen reviews 10 and 11, pass 7; `helen-review-10-requirements.md`,
   `helen-review-11-pass7.md`, both the parent's summaries). "Today" = `33d62a6f`.
   * **R1** send timeout ⇒ **connection** teardown (`s_h = 1`; `01` §8); margin `(c_mux + P_mux) · S_mux ≤ T_send / k`
     from Theorem B (§5a TB6); `Send`s in the mux mailbox ≤ 10 per connection.
   * **R2** a per-connection handler that dies without completing `Done` tears the connection down;
     `start_initiators` never resurrects a handler in the same turn; a replacement registers only after `Done`, with
     `wanted := 0` and `incoming` cleared. Violated today (pass 7 §1).
   * **R3** chainsync initiator `p_h ≤ d + 1` under the credit (today 2 on the intersect race).
   * **R4** consume-before-rearm for `WantNext`. **Holds today.**
   * **R5** cells (`SetLocalUse`/`NewTip`/`FetchBlocks` into manager and per connection incl. the chainsync responder,
     mempool capacity, `WaitForAtLeast` seq, stake M1 + W3): single writer or lattice merge; read on init, restart and
     every transition; stated wake (dirty bit, or W3 period into Theorem B). The responder's tip cell requires
     REQ-resolve.
   * **R6** cap at accept before the id is minted.
   * **R7** `RemovePeer`/`Adversarial` through the per-`conn_id` dedup helper, pruned only on termination; `conn_id`s
     never reused (holds today, except the `u64` wrap: assumption + assert at the allocator).
   * **R8** capacities as formulas: manager `4·N_max + C + 4`, `fetch_blocks` 67 (needs R11), mempool
     `max_inbound + L_max + 1`, `peer_selection` `1 + N_max + max_outbound`.
   * **R9** (Theorem B) `Register`/`SetSduTimeout` as a call; mux `d + 25`.
   * **R10** chainsync initiator: explicit `outstanding = RequestNext − (RollForward + RollBackward)`, `MsgDone` only
     from `StIdle` with `outstanding = 0`, asserted at the send site (violated today). TxSubmission `MsgDone` only from
     `TxIdsBlocking` (holds today; assert). Blockfetch, keepalive, peer sharing hold today.
   * **R11** `MAX_FETCH_PEERS` caps **every** fetch dispatch including the `peers: None` broadcast
     (`manager/mod.rs:767–776`, violated today); named `L_max` for submit-API calls.
   * **R12** mempool full ⇒ the responder drops the batch and requests neither tx ids nor txs until the capacity
     cell shows room; no buffering, no retry; acknowledgements as the protocol needs (FIFO count, dropped ids
     included). Today: drops and gates bodies (**holds**); still requests ids while full (requirement).
   * **R13** (Praos anchor rule) the anchor reaches `select_chain` through a single-writer monotone cell; on each move,
     candidates intersecting below it are pruned and the best is recomputed (pragma-org/amaru#1654). A Genesis switch
     must discharge `G1`–`G5` of §4a.
   * **REQ-resolve** every live follower pointer resolves to its best-chain intersection by walking stored parents,
     ≤ `k` steps, memory ≤ `F·k`; header GC never prunes a header reachable from a live pointer; a violation is an
     internal assert, never a peer fault.
   * Plus: B4's `InsertBatch` timeout removal, the chainsync credit + Done-once, the token fixes of (a).
   **Missing items:**
   * **M1** restart re-init: `track_peers` cleans `upstream`/`deferred` on `Terminated`; mempool waiter lists bounded
     and dead callers purged (moot under R5); `fetch_blocks` re-plans when a blockfetch initiator dies; orphan timers
     are harmless under R2. Violated today (pass 7 §4).
   * **M2** the simulation is at least as strict as tokio: panic on a never-registered name. Violated today.
   * **M3** schedule lane: cancel-before-rearm, ≤ 2 per stage (hard bound), plus tombstones ≤ children. Violated
     today only by `connection`.
   * **M4** debug assertions at every discharged send site (occupancy + parked ≤ bound), a park on a discharged edge
     fails the simulation, per-mailbox high-water marks against the §9 formulas.
1. **Pass 5:** with the enlarged capacities (as formulas), the stake cell and the §8(b) rows, the v5 graph is
   acyclic in the what-if run (`what-if-v5-all.txt`). Remaining work is bookkeeping (rows into the JSON) plus the
   design items below; for the mux, Theorem B still needs teardown on `None` and `Register` as a call (`R_c`).
   Findings from (A): `done_trap` inherits `wanted` (possible spurious disconnect on a straggler reply);
   `MUX_MAILBOX_SIZE = 24` ignores the chainsync pipeline; with `None` ignored the blockfetch responder can queue
   one `Send` per peer-requested point.
1a. **Pass 4 (history):** the checker exits 1 in both modes (v4). B1–B6 (§8) make the remainder
   acyclic in the what-if run; their rows need verified bounds in the discharge JSON, and the v4 row for
   `cleanup_replies → fetch_blocks` must be re-modelled with the full filter.
2. **Code checks done (review 8):** B5 = 4 ≤ 10; `WaitForAtLeast` is a blocking 2-cycle with `tx_submission_initiator`
   (missing from v4) and peer-unbounded (seq cell fix); `schedule_after` = `schedule_at`, panics at 10; only
   `connection` exceeds the timer bound; `select_chain` does not prune on anchor moves. **Graph completeness:** the
   v4 JSON omits several protocol stages; pass 5 must add them mechanically.
3. **Decided (Roland, 2026-11-15):** (a) the tx-submission responder **drops** when the mempool is full and stops
   requesting while full (R12; today matches except for tx-id requests); (b) the target is **Praos**, with the theory
   parametrised by the chain-selection rule so that a later Genesis switch can be checked (§4a).
14. **Findings without a deadlock:** `connection` re-schedule panic (crash freedom); blockfetch "pipeline full"
    terminate on local overload; submit API without a concurrency cap (`L` unbounded); `InsertBatch` timeout
    disconnects peers (to be removed).
4. **`BoundaryNotFound`** confirmed as a token leak with two causes; the fix (terminate on a store hole, move the
   token back on the anchor race) needs `find_missing_blocks` to distinguish them.
5. **Connection cap (finding).** `max_inbound` is enforced only at `handshake_complete`, after `accept` minted an id:
   pre-handshake connections are unbounded (resource exhaustion). Every `N_max` bound assumes the cap at accept.
6. **Superseding cells** for `SetLocalUse`, `NewTip`, `FetchBlocks` are designs; (i) is verified in code for the
   first two; `FetchBlocks`' diff-dispatch semantics need review by the code owners.
7. **Theorem B with enlarged mailboxes:** queueing delay grows with `manager` 66/494 and `fetch_blocks` 67; the
   latency bounds must be recomputed with these sizes.
8. **Lemma 4 invariants are proof obligations,** not derived; extraction for untyped stages is manual.
9. **Internal call timeouts:** `miniprotocol`'s ignored `None`; the responder's `InsertBatch` timeout disconnects a
   peer for local congestion (not attributable).
10. **H7 under lifecycle:** `cleanup_replies` is re-ensured under a fixed name; per-connection names must be fresh.
11. **Fairness F1 on tokio** is practical behaviour; F2 is documented.
12. **Runtime oracle:** `Blocked::Deadlock` sees only global deadlock; a `⇝`-cycle oracle would check the safety half.
13. **Memory figures** rest on assumed message sizes and an assumed mainnet-like config; measure `size_of` and real
    configs before sizing.
