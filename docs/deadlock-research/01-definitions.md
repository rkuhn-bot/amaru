# 01 — System model and proof obligations

Status: first cut, 2026-11-15. Basis: pure-stage on pragma `main` (read-only; semantics checked at `4b8c0171` in
`crates/amaru-pure-stage`, inventory at `33d62a6f`, see `wait-graph-inventory.md`). Nothing here changes Amaru.

Binding modelling assumptions agreed with Roland are marked **[R]**; ones Helen asked for are marked **[H]**.
The model is generic (any network of run-forever stages with bounded shared mailboxes); Amaru specifics are
given only as instances. No property of any other node implementation is assumed. The only Ouroboros inputs are
taken from the protocol papers (§5).

---

## 1. Syntax: what a stage is

A **stage template** is `T = (Q_T, q0_T, Msg_T, δ_T, c_T)`:

* `Q_T` — the stage's control states (typestate states; for untyped stages, one state `⊤`).
* `δ_T : Q_T × Msg_T → Prog(Q_T)` — one *transition program* per received message. A transition program is a
  finite tree (no unbounded loops **without an effect in them**) of effects ending in a new control state.
* `c_T ∈ ℕ` — capacity of the stage's **bulk mailbox** (default 10; `manager`/`peer_selection` use
  `10 + target_up + target_down`; `mux` 24; chainsync initiator 14; blockfetch initiator `max(10, 2n+4)`).

Effects (`Eff`), classified by **how a stage can be stuck in them** (the classification is the whole point):

| Effect | pure-stage API | Waits on | Class |
|---|---|---|---|
| `send(t, m)` | `Effects::send` | a free slot in `t`'s bulk mailbox (FIFO admission among parked senders) | **blocking** |
| `call(t, d, m)` | `Effects::call` | admission into `t` (as `send`) **and then** `t` dequeuing it and replying | **blocking** (admission + reply) |
| `reply(r, m)` | `send` to a call-reply `StageRef` | nothing (oneshot) | non-blocking |
| `try_send(t, m)` | `Effects::try_send` | nothing; `Full`/`Gone` ⇒ message dropped | non-blocking |
| `ext(e)` internal | `external`, chain store, ledger request, `Performance` worker, `Resources` | the effect provider, **not a stage** | **delay** **[R]** |
| `peer(e, d)` | network read/write through reader/writer stages | the remote peer, bounded by timeout `d` | **external, timed** |
| `peer(e, ∞)` | e.g. reader's first header byte (`mux.rs:495`) | the remote peer, unbounded | **external, untimed** |
| `wait(d)`, `clock` | `wait`, `clock` | time | delay |
| `schedule`, `set_timeout`, `cancel` | priority path, own stage | nothing (overflow of the priority budget panics) | non-blocking |
| `detach(e, inj)` | `Effects::detach` | nothing for the issuer; a spawned *injector* later does a blocking send into the issuer's own mailbox | non-blocking for the issuer; the injector is a **producer node** (§1.1) |
| `spawn`, `wire_up`, `supervise`, `terminate` | lifecycle | see §6 | lifecycle |

### 1.1 Producer nodes [H]

Everything that can put a message into a bulk mailbox is a node of the wait graph, not only stages:
stages, `detach` injector tasks, external **input senders** (`StageGraph` inputs, e.g. `track_peers_sender`), and
**callbacks** running on an effect provider's thread. A producer node that no stage ever waits on (an injector, a
plain input sender) has no incoming wait edges and cannot lie on a cycle, but it **does** consume capacity and
must be counted in every credit bound (`03` §4). A producer that a stage *does* wait on (a callback on an effect
thread) is covered by §7.

**[R] Internal-effect assumption (A-int).** Every `ext(e)` completes after finite time, *independently of the
progress of any stage*. Formally: an effect provider is never in a state where its completion depends on a
stage dequeuing a message. Consequence: internal effects are *delay* edges and never part of a wait-for cycle.
An effect whose implementation **does** wait on a stage mailbox (the ledger stake callback,
`build_node.rs:500–511`) is **not** covered by A-int; §7 says how it must be modelled.

**[R] Peer assumption (A-peer).** Peers are adversarial: any peer may stop reading and writing forever at any
moment, send arbitrary well-formed traffic within protocol limits, or disconnect. The only liveness the proof may
use is *ours*: every timed peer effect `peer(e, d)` returns (successfully or with a timeout error) within `d`.

---

## 2. Semantics: configurations and steps

Let `S(σ)` be the set of live stages in configuration `σ` (finite at every instant; changes by spawn/terminate).
For each `s ∈ S(σ)` the configuration records

* `ctl_s` — either `Idle(q)` (waiting to receive, control state `q`) or `Busy(q, k)` where `k` is the remaining
  transition program, whose head is the **pending effect** `pend_s`;
* `box_s` — the bulk mailbox, a FIFO sequence with `|box_s| ≤ c_s` (the message being processed is *not* counted);
* `park_t` — the FIFO queue of senders parked on `t` (stages blocked in `send/call(t, ·)` plus injectors);
* `prio_s` — the priority queue (timers, tombstones), separately bounded;
* `env` — state of each peer connection (abstract, adversarial).

Steps (interleaving semantics, one stage acts per step; this is what the deterministic simulation implements and
what tokio refines):

1. **Receive.** `Idle(q)` with `prio_s ≠ ε` or `box_s ≠ ε`: take a priority message if any, else the head of
   `box_s`; become `Busy(q, δ(q, m))`. If a bulk message was taken and `park_s ≠ ε`, the **head** parked sender's
   message is appended to `box_s` and that sender resumes (*FIFO admission*). `try_send` cannot overtake a parked
   sender (`effect.rs:259–270`; tokio's bounded mpsc uses a fair FIFO semaphore,
   [`batch_semaphore.rs`](https://github.com/tokio-rs/tokio/blob/master/tokio/src/sync/batch_semaphore.rs) module docs).
2. **Send.** `pend_s = send(t, m)`: if `|box_t| < c_t` and `park_t = ε`, append and continue; else append `s`
   to `park_t` and `s` is **parked**. Send to a terminated `t` returns immediately (message lost).
3. **Call.** Admission as in (2); after admission `s` waits for `reply`; `reply` never blocks.
4. **Internal effect / wait.** `s` is *delayed*; by A-int the step that resumes `s` is eventually enabled.
5. **Peer effect.** `s` waits; the environment may resume it at any time; a timed effect is resumed with an error
   at the latest after `d`.
6. **Finish.** Program exhausted ⇒ `Idle(q')`.

**Internal timeouts are erased, with one exception [H].** For the *deadlock* obligations we use the semantics `⟦·⟧^∞` in which every
timeout on an edge between two stages (notably `call` deadlines between stages, today e.g. the 1 s wire-send call
handler→mux and the 10 s handshake call connection→manager) is set to `∞`. Timeouts on peer effects stay finite.
This is the precise form of the side condition "a timeout breaking an internal cycle does not count".
*Exception:* an internal timeout may stay finite iff its expiry is a **peer-level fault**, i.e. it tears down the
bearer of exactly the peer whose traffic is involved (and nothing else), so that it is semantically a peer
effect. Example to be checked: the 1 s handler→mux wire-send `call`. If its expiry tears down that connection it
counts as a peer edge; if the caller proceeds with `None` and the typestate is now out of step with the wire,
it is an internal timeout and must be erased.
(In `⟦·⟧^∞` a `call` to a terminated stage waits forever; see §6.)

**Fairness (F).** (F1) *weak fairness*: a stage whose next step is continuously enabled eventually takes it;
(F2) *FIFO admission* as in step 1; (F3) *non-Zeno timers*: a stage receives only finitely many priority
messages in any bounded time interval (so priority traffic cannot starve the bulk mailbox forever).
Tokio gives F2 by construction; F1 is the usual "every woken task is eventually polled" property of the tokio
runtime, which pure-stage does not state as a bound. The simulation's FIFO/random strategies are fair for
safety purposes; any *safety* result below is scheduler-independent (it quantifies over all interleavings).
Custom deferral strategies (as in the #1475 repro) are unfair by design: they can exhibit or refute the *safety*
half (reachability of a `⇝`-cycle) but say nothing about O1's liveness half (`03` §4).

**Worker threads.** A transition that blocks synchronously (`wrap_sync` closures, `block_on` inside a callback)
occupies a runtime worker thread as well as the stage. Such a wait must never depend on a stage (part of A-int and
of `03` H2/H6).

---

## 3. Wait-for relation (instantaneous)

In configuration `σ`, `s ⇝ t` ("`s` waits for `t`") iff

* `s` is parked on `t` (pending `send`/`call` admission to `t` and not admitted), **or**
* `s` has an admitted `call` to `t` and no reply yet, **or**
* `s` is blocked in an effect whose provider is (transitively) parked on `t` (only arises when A-int is violated; §7).

`s` is **stuck** in a run `ρ` from position `i` if its pending effect never completes in `ρ` after `i`.

---

**Mechanical closure of the edge set.** The wait-for relation is only as good as the extracted edge set. Edges
reached through a `StageRef` carried in a message (reply refs, collector refs, `caller`) and `send_any` targets are
edges like any other: for every message type with a `StageRef` field, add an edge from each stage that sends to that
ref to every stage that can construct it; include `send_any`; recompute SCCs from `wait-graph.json` by script after
every inventory change (`03` §1).

## 4. Deadlock notions

Let `Core` be the static stages and `Inst(N)` the stages of the `N` active per-peer subtrees.

* **Buffer deadlock (capacity deadlock).** A reachable `σ` with a cycle `s₀ ⇝ s₁ ⇝ … ⇝ s₀` where every edge is
  "parked on a full mailbox". Stable: nobody on the cycle can receive, so no mailbox on it drains (in `⟦·⟧^∞`).
* **Call deadlock.** As above but at least one edge is a call-reply wait.
* **Protocol deadlock.** A stage is in a control state where progress needs a message that no other stage will
  ever send, while its mailbox is *not* the problem (it keeps receiving). This is a liveness bug in a session,
  not a buffer problem. pure-stage stages never block on receive, so protocol deadlock does **not** stop the stage
  from draining its mailbox; it is out of scope for the buffer argument and covered per protocol (typestate
  projection, as for BlockFetch) except where it makes a *caller* wait: an admitted call that is never answered.
* **Global deadlock.** Every live stage is stuck (what `Blocked::Deadlock` in the simulation reports — it is only
  returned when no stage is busy or sleeping, `simulation/running/mod.rs` `block_reason`).
* **Partial deadlock [H].** A non-empty set `D ⊆ S(σ)` of stages that are stuck forever in every fair
  continuation, while other stages (typically peer subtrees and timers) keep running. **This is the obligation**;
  global deadlock is the special case `D = S(σ)`. Note the simulation classifies a partial deadlock as `Sleeping`
  or `Busy` whenever any other stage has a timer or effect outstanding.

**Obligation O1 (internal deadlock freedom).** For every `N ≥ 0`, every capacity assignment allowed by the
configuration, every adversarial environment, and every fair run of `⟦·⟧^∞`: no stage is stuck forever on a
pending `send`, `call`, or A-int-violating effect.

Equivalently (Theorem A proof, `03` §4): no reachable configuration contains a `⇝`-cycle, *and* every `⇝`-chain
ends in a stage that eventually makes progress.

**Obligation O2 (no internal reliance on timeouts).** O1 holds in `⟦·⟧^∞`. (Already built into O1.)

**Obligation O1' (no livelock in internal cycles) [H].** A stage that is not stuck but loops forever on
retries (e.g. `try_send` → `Full` → reschedule → `try_send` …, or `call` → `None` → retry) without any message
on the cycle being consumed is a livelock. Converting a blocking edge into a non-blocking one with a retry loop
must come with a progress measure. Under the binding rule of §8 reliable messages are never converted to
drop-and-resend schemes, so retry loops can only appear around superseding messages or around peer-level
operations; each needs a progress argument. Separate obligation; not implied by O1.

**Obligation O3 (peer isolation).** Any stage that can be stuck on an untimed peer effect is not the target of
any blocking edge that can actually park (see `03` §4 budget lemma). Otherwise a single stalled peer can park an
internal stage forever, which *is* an internal deadlock in our sense even though no internal cycle exists.

---

## 5. Timely path: bounded blocking — separate theorem [H]

Fairness and timeliness are **not** part of deadlock freedom; they are a second theorem built on top of O1.
Inputs from the Ouroboros papers only:
* Praos assumes Δ-bounded delivery between honest parties; an internal stall on the header path adds to the
  effective Δ of every node running the same code (a correlated loss, not an individual crash).
* Genesis chain selection compares per-peer candidate fragments (density rule) and needs all of them; so
  starvation of one peer's candidate updates is a correctness problem for chain selection, not only a speed issue.
* Honest parties tolerate any number of adversarial peers given one honest path; so no internal mechanism may let
  adversarial peers starve the honest peer's updates (per-peer fairness), and no mechanism may make disconnecting
  an honest peer cheap for an adversary (eclipse lever).

Timely path `P = header → validate → cmp_tip → fetch decision → adopt → announce`, plus "disconnect invalid peer".
Concretely the stages on it today include chainsync initiators, `track_peers`, `select_chain`, `fetch_blocks`,
`validate_block`, `adopt_chain`, and the `manager`→`connection` disconnect.

**Obligation O4 (bounded blocking).** There is a bound `B` (independent of `N`; a per-hop budget of the order of 10 ms is a **labelled design
target**, not a derived quantity) such that
for every message on `P` the time from its emission to the end of its processing at the next `P`-stage is
`≤ B`, given quantitative versions of the assumptions:

* (A-int-q) every internal effect used by a `P`-stage has a worst-case duration `δ_e`;
* every `P`-stage's transition has worst-case duration `τ_s` excluding blocking sends;
* no `P`-stage has, transitively through blocking edges, a peer effect (timeouts of seconds are far above `B`).

**Lost or missing tokens.** O4/O5 must also catch a session that waits for a message that never comes and
never will (e.g. a credit/token that was never created or was destroyed): no stage is in a `⇝`-wait, so O1 does not
see it. A conserved-count invariant of the kind used in `03` §8(a) (Lemma 4) doubles as the check: the count must be
exactly the intended number in every reachable configuration, including fresh start.

**Obligation O5 (per-peer fairness).** For each peer `p`, the delay between `p`'s header arriving and `p`'s
candidate being updated in chain selection is bounded independently of the behaviour of other peers (a freshness
target of the order of 1 s for density comparisons is likewise a labelled design target).

Note O4/O5 are *not* implied by O1: bounded mailboxes bound queue length (`c_s · τ_s`), but FIFO admission puts a
`P`-sender behind *all parked senders*, and with `N` per-peer senders that wait is `O(N · τ_s)`.

---

## 6. Lifecycle

* **Spawn/activation.** New per-peer stages add nodes and edges of the template; the proof must hold for every
  intermediate topology (rules out "it is only acyclic once wiring is complete").
* **Fresh names.** Credit/occupancy invariants (`03` H7) are inductive across restarts only if re-created stages
  get fresh names, or if the old mailbox is provably dropped together with its parked senders and those resume.
  Fixed-name re-creation (e.g. `ensure_child` under a constant name) must be argued separately.
* **Termination.** Send to a terminated stage returns (message lost) — non-blocking. `call` to a terminated or
  never-existing stage waits out its deadline (`tokio.rs:647–650`); in `⟦·⟧^∞` it is stuck forever ⇒
  obligation: *no internal `call` may target a stage that can terminate while the caller lives*, or such calls
  must be treated as external-timed (only legitimate if the callee's existence is itself peer-driven).
* **Priority mailbox [H].** Timers and tombstones use a separate bounded priority path. Overflow of
  self-scheduled messages panics (crash, not wait); the bound for tombstones/timeouts must be shown to hold, or
  the priority path becomes a wait edge like a bulk send.
* **Unknown target.** The simulation drops a send to an unknown stage, tokio panics on a name never inserted:
  the two runtimes differ, so the model must forbid sends to never-created names.
* **Supervision.** Child death is delivered on the priority path (non-blocking); unsupervised death stops the
  parent. Whether a restarted stage reuses its mailbox and what happens to senders parked on the old one is *not yet
  checked*; until it is, restarts must be modelled as termination plus creation.
* **Teardown races.** Disconnect is a blocking `manager → connection` send (`manager/mod.rs:946`); while the
  connection subtree is stuck, this is a potential edge into a stage that waits on a peer (O3).

---

## 7. Effect callbacks (A-int violations)

**Definition [H].** A callback that runs on an effect provider's thread is *part of that effect*. Hence, under
A-int, it may not wait on a stage (no blocking `send`, no `block_on` of a stage send, no `call`).

An internal-effect provider `L` that, while serving some request, performs a **blocking** operation on a stage
mailbox (example: the ledger thread's `StakeDistUpdated` send into `track_peers` during stake rotation, called
from inside a ledger request) is modelled in one of two ways:

1. **Forbidden (design rule R-cb).** Effect implementations may only use non-blocking operations towards stages
   (`try_send`, resource write, detached injector). Then A-int holds and nothing else changes. *Recommended.*
2. **Modelled soundly.** `L` becomes a **pseudo-stage** with a request queue. Every stage `s` that can await *any*
   effect served by `L` gets edges `s → L` (reply wait), and `L` gets the blocking edge `L → t`. Because `L`
   serialises requests, the callback can be in progress while `s`'s own unrelated request is queued, so the
   collapsed rule is: **for every caller `s` of any `L`-effect, add a blocking edge `s → t`**. (It is not enough
   to add the edge only for the effect that triggers the callback.)

---

## 8. Edge kinds: reliable vs superseding; admissible drops and disconnects

**Binding rule [R].** Every message kind on every edge is classified as

* **reliable** — delivery is needed for correctness. Reliable sends stay reliable: they are never dropped,
  overwritten, or replaced by a drop-and-resend scheme. The only tools for reliable edges are mailbox capacity
  (which may be enlarged) and structural credit/flow control.
* **superseding** — the receiver's behaviour depends only on the latest value, or on the join of all values in a
  semilattice (e.g. `max` of an epoch number). Only superseding messages may be dropped or overwritten
  (last-value cell plus coalescing wake-up). The superseding property must be argued from Amaru's own semantics
  for each message kind.

Rejecting work at an admission point (mempool full) is a domain decision of the receiver after delivery, not a
message drop, and is unaffected by this rule.

Generic security arguments:
* Dropping a message of a *stateful session* (e.g. a chainsync step) corrupts that session's state: such
  messages are reliable.
* Disconnecting a peer is admissible iff the trigger is attributable to that peer alone (a protocol violation:
  exceeding the legal outstanding amount from the mini-protocol session type). Disconnecting on *our* internal
  congestion lets an adversary cause disconnects of honest peers (eclipse lever) and is not admissible.
* **Ingress teardown.** Replacing a blocking ingress delivery (mux → handler) by "tear down the bearer when the
  handler's mailbox is full" is admissible iff the handler's capacity, after subtracting every other producer's
  occupancy bound, is at least the protocol-legal outstanding amount of inbound messages given by the mini-protocol
  session type (agency plus pipelining depth). Then a full mailbox implies a protocol violation by that peer.
* **Send-timeout teardown (the one admissible local-cause teardown).** A handler's `Send` to the mux is a call
  whose reply (`Sent`) is emitted only when the bytes are cut into an SDU for the writer, i.e. after the previous
  SDU went into the TCP send buffer. If the call times out, the **whole connection** is torn down, not only the
  handler. Justification: the wait is TCP backpressure, i.e. the peer is not reading what it asked for, which is
  attributable to that peer. Condition (proof obligation for Theorem B): the internal part of that wait (admission
  to and dequeue from the mux mailbox, which is a sink of the wait graph) is bounded well below the timeout;
  otherwise our own congestion could trigger it. This rule replaces "continue after `None`", which leaves the
  `Send` queued and makes per-handler outstanding sends unbounded.

## 9. Summary of the formal objects

* Configuration semantics `⟦·⟧^∞` (internal timeouts erased).
* Fairness F1–F3.
* Assumptions A-int, A-peer (and A-int-q for O4).
* Producer nodes (§1.1); callbacks belong to their effect (§7).
* Theorem A (deadlock freedom): O1, O1', O3; O2 is built into O1.
* Theorem B (timeliness/fairness, separate): O4, O5.
