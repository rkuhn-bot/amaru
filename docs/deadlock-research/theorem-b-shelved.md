# Theorem B (timeliness and per-peer fairness) — SHELVED

**Status: SHELVED on 2026-11-15, by Roland's decision** ("Please shelf the timing part for now (store all relevant
research and findings so that we can resume later)"). Theorem A (deadlock freedom) continues without it. This file
holds everything gathered for Theorem B so far, so that the work can resume from here. Nothing in it is a proof.
"Today" = pragma-org/amaru main at `33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6`.

Ground rules that still apply: internal effects always complete (A-int) and are delay edges; only peer communication
can stall. Ouroboros inputs come from the papers and the network specification only; constants taken from them are
design targets. The Haskell node is not an authority.

## 1. What Theorem B is meant to state

Theorem A (`03` §4) gives O1: no reachable state in which a set of stages waits on each other forever. Theorem B adds
O4 (timeliness: the header → select → fetch → adopt → re-announce path completes within a stated budget) and O5 (no
per-peer starvation), defined in `01` §4. `01` §5 gives the motivation from the papers: Praos assumes Δ-bounded
delivery between honest parties, so an internal stall on the header path adds to the effective Δ of every node
running the same code (a correlated loss); under Genesis, starving one peer's candidate updates is a correctness
problem for chain selection, not only a speed issue.

Early shape (`03` §5): under A-int-q and per-stage transition bounds `τ_s`, edges discharged by Lemma 1/2 wait
`≤ c_t · τ_t`; with FIFO admission (F2) a peer's message waits behind `≤ N − 1` parked senders plus `c_t` queued
messages, so O5 holds without a quota but the bound grows with `N`; superseding edges add the W3 poll period or, via
W1, up to `c_t` messages; a lost token violates O4/O5 without any wait edge (the Lemma 4 invariant is the check).

## 2. Skeleton TB1–TB6 (copied from `03` §5a, Helen review 10)

Every quantity is labelled **[config]** (follows from configuration or protocol parameters), **[measure]** (must be
measured on the implementation) or **[environment]** (assumption about honest peers' links).

**TB1. Quantitative A-int.** Every internal effect `e` completes within `D_e` **[measure]**: store reads/writes, the
chain-store `FindBestCandidate`, header validation, and ledger block validation. Ledger validation is bounded by the
protocol parameters `maxBlockExUnits` and `maxBlockBodySize` **[config]** (the work per block is capped by them), but
the time per unit is **[measure]**, so `D_validate ≤ f(maxBlockExUnits, maxBlockBodySize)` with `f` measured.

**TB2. Per-stage service time and hop bound.** For stage `s`, `S_s` = max over message kinds of the transition time,
composed of its own CPU plus `D_e` of the effects it awaits **[measure]**. A message entering `s` waits at most
`(c_s + P_s) · S_s`, where `c_s` is the capacity **[config, `03` §9 formula]** and `P_s` the number of senders that
can be parked on `s` at once **[config: number of producer instances]**, using FIFO admission of parked senders (F2,
tokio's fair semaphore). This is the per-hop bound; a path's bound is the sum over its hops.

**TB3. Utilisation below 1.** Every bound in TB2 assumes `s` is not overloaded in the long run: arrival work per unit
time `< 1`. For pull-based edges the arrival rate is bounded by configuration: e.g. at `track_peers`, `N_max · d`
outstanding results per round-trip; at `fetch_blocks`, `A · MAX_FETCHED_BLOCKS` per request **[config]**, times the
cost per message **[measure]**. Where no pull bound exists (submit API, inbound tx batches), admission control is
required: `L_max` (R11), the mempool's own capacity rejection, and the responder's requested counts (R12).

**TB4. Critical-path budget.** Path: header arrives at the chainsync initiator → `track_peers` → validate header →
`select_chain` → `fetch_blocks` → blockfetch → `validate_block` → `adopt_chain` → re-announce (manager tip cell →
connection → chainsync responder). Budget = Σ hop bounds (TB2) + `D_e` of the effects on the path + the cell wake
latencies on it (dirty bit: one hop; W3: period `π` **[config]**) + network transfer **[environment]**. Requirement:
the internal share is a stated fraction of Praos Δ; working target Δ = 5 slots, taken from the security model's
treatment of Δ-bounded delivery, not from any implementation. The anchor cell's wake latency (R13) is on this path.

**TB5. Per-peer fairness (O5).** A peer's message to a shared stage `t` waits behind at most `N_max − 1` other parked
per-peer senders plus `c_t` queued messages: `≤ (N_max − 1 + c_t) · S_t`. Independent of the adversary's sending
rate, because each peer instance has at most one parked send (a stage is sequential) and admission is FIFO.

**TB6. Timer budgets, kept separate.** For each protocol timeout `T`, show that local queueing alone cannot make it
fire against an honest peer (R1 send timeout; keepalive; chainsync `MustReply`/intersect; blockfetch range/batch).
Each `T` must exceed the round-trip **[environment]** plus the local queueing on both of our path's hops (handler
mailbox and mux, TB2) plus, for blockfetch, the transfer time of the requested bytes at link bandwidth `b`.

## 3. Numbers and derivations so far

All are derivations from config formulas plus a stated safety factor; none is measured.

| # | Quantity | Derivation | Value | Status |
|---|---|---|---|---|
| N1 | mux mailbox per connection `c_mux` | `d + 24 + R_c`, `R_c ≤ 1` once `Register`/`SetSduTimeout` is a call (R9) ⇒ `d + 25` (`03` §8(b)(ii)) | 35 at `d = 10` (today 24, too small for Theorem B only) | config formula |
| N2 | parked senders on the mux `P_mux` | ≤ 10 handlers + reader + writer + connection | ≤ 13 | config |
| N3 | R1 margin | `(c_mux + P_mux) · S_mux ≤ T_send / k`, safety factor `k` | at `d = 10`, `k = 10`, `T_send` = 1 s (today): `48 · S_mux ≤ 100 ms` ⇒ **`S_mux ≲ 2 ms` per message** | requirement on a [measure] quantity |
| N4 | bearer head-of-line wait for `Sent` | `Sent` also waits for earlier segments of other protocols on the same bearer (round-robin), ≤ ≈ 10 × 64 KiB = 640 KiB; time `640 KiB / b` must be `< T_send` | **honest link ≥ ≈ 5 Mbit/s** at `T_send` = 1 s (640 KiB ≈ 5.2 Mbit); below that, R1 can tear down a slow honest peer | environment assumption; open: whether the safety factor `k` applies here too (it would raise the figure to ≈ 52 Mbit/s) |
| N5 | mux memory | ≈ 35 × (16 B + ≤ 64 KiB segment) per connection | ≈ 2.2 MiB worst case per connection at `d = 10` | config |
| N6 | ledger validation `D_validate` | capped in work by `maxBlockExUnits`, `maxBlockBodySize` | time per unit **unmeasured** | [measure] |
| N7 | Praos Δ target | working target from the security model | Δ = 5 slots | design target, not derived |
| N8 | enlarged mailboxes feed TB2 | latency grows linearly with capacity (Helen review 7 (1)(c)) | manager `4·N_max + C + 4` = 66 at defaults, 494 mainnet-like; `fetch_blocks` 67; mempool `max_inbound + L_max + 1`; `peer_selection` `1 + N_max + max_outbound` | bounds to recompute |
| N9 | `track_peers` | `N_max·(d + 1)` results + `N_max` `Terminated`; Theorem B may want `N_max·(d + 2)` | — | open |
| N10 | `box_fetch_blocks` | `NewBestTip` can wait behind ≤ 10 straggler `Block`s (`03` §8(a)) | ≤ 10 · `S_fetch_blocks` | config |
| N11 | design targets from early drafts | ~10 ms per hop, ~1 s freshness | — | labelled design targets only |

**Genesis dependency (`03` §4a, `G5`/`P4`):** under a later Genesis switch the anchor hold `h` (in blocks) enters only
through TB4's memory/store terms (REQ-resolve walk and memory `k + h`, `F·(k + h)`); cell periods are unchanged. The
hold must itself be bounded (`G4`), which is an O4 obligation.

## 4. Requirements that depend on Theorem B

* **R1** (`03` §11 item 0): connection teardown on send timeout is admissible only with the margin N3 (`01` §8,
  "Send-timeout teardown": the internal part of the wait must be bounded well below the timeout; otherwise our own
  congestion could trigger it). Deadlock freedom does not need R1; Theorem B and memory do.
* **R5**: every cell with a W3 wake states its period `π`; the period enters TB4 (`03` §3 W3). Includes the stake
  cell (M1 + W3) and the anchor cell (R13).
* **R8**: the enlarged capacities are what TB2 must use (N8).
* **R9**: `Register`/`SetSduTimeout` as a call and mux `d + 25` — Theorem B only.
* **R11/R12**: the admission-control half of TB3 (submit API `L_max`; mempool drop-when-full and no requests while
  full).
* **B3** (`03` §8 table): `manager → connection` cells are not needed for acyclicity once B2 holds, but are needed
  for Theorem B and for the timer finding.
* **M4**: per-mailbox high-water marks are the measurement that checks the config formulas.
* **`03` §4a `P4`/`G5`**: anchor wake latency and Genesis hold `h`.
* **Timer finding** (pragma-org/amaru#1655, `issues/2-timer.md`): connections in `Initial`/`Handshake` re-schedule
  `FetchBlocks`/`NewTip`/`SetLocalUse` every `reconnect_delay` (2 s) and can overflow the 10 schedule slots; the fix
  (cells per connection, B3) removes the schedules, and the delay until a new connection sees the latest values
  (≤ handshake time, `SDU_TIMEOUT_HANDSHAKE` = 10 s) is a TB4/TB6 term.

## 5. Open measurements

| Quantity | What | How to measure (proposal) |
|---|---|---|
| `D_e` per effect | store read/write, `FindBestCandidate`, header validation, ledger validation per ExUnit and per byte | micro-benchmarks per effect on a mainnet-like store; for ledger validation, replay blocks at or near `maxBlockExUnits`/`maxBlockBodySize` and fit `f`; report max and p99.9 |
| `S_s` per stage | max transition time over message kinds (own CPU + awaited `D_e`) | instrument the pure-stage runtime: timestamp at dequeue and at transition end per stage and message kind; run the simulation and a mainnet-like sync; take the max |
| `S_mux` | per-message mux transition time | same instrumentation on the mux stage under full load (10 handlers, `d = 10`); check against N3 (≈ 2 ms) |
| per-message cost for TB3 | arrival work per unit time at pull-bounded stages | from `S_s` × config arrival bounds (`N_max · d`, `A · MAX_FETCHED_BLOCKS`) |
| high-water marks (M4) | per-mailbox occupancy + parked | debug counters at every discharged send site; compare with the `03` §9 formulas |
| `b`, round-trip | honest link assumptions | environment assumption to state, not measure; N4 gives the minimum `b` |

## 6. Sources (all from `02`, citations verified there or here)

* D. Coutts, N. Davies, M. Fontaine, K. Knutsson, A. Santos, M. Szamotulski, A. Vieth, *Ouroboros Network
  Specification* ("The Shelley Networking Protocol"), version dated 10 November 2026,
  https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf. Relevant: §3.9.3 Table 3.11
  (tx-submission timeouts: only `StTxIdsNonBlocking` and `StTxs`, 10 s; verified against the PDF layout), §3.9.2 limits,
  §3.15 pipelining, and the per-protocol timeout tables for TB6 (not yet extracted for chainsync, blockfetch and
  keepalive — a resume item).
* W. J. Dally, C. L. Seitz, *Deadlock-Free Message Routing in Multiprocessor Interconnection Networks*, IEEE Trans.
  Computers, 1987, https://doi.org/10.1109/TC.1987.1676939 — buffer-accounting backbone; the hop bound TB2 is the
  latency counterpart of its buffer occupancy.
* J. Duato, *A New Theory of Deadlock-Free Adaptive Routing in Wormhole Networks*, IEEE TPDS, 1993,
  https://doi.org/10.1109/71.250114 — refinement for kept cycles (`02` §A).
* Not yet in `02`, verified against Crossref on 2026-11-15, needed for the Δ target and `01` §5:
  B. David, P. Gaži, A. Kiayias, A. Russell, *Ouroboros Praos: An Adaptively-Secure, Semi-synchronous Proof-of-Stake
  Blockchain*, EUROCRYPT 2018, LNCS, https://doi.org/10.1007/978-3-319-78375-8_3;
  C. Badertscher, P. Gaži, A. Kiayias, A. Russell, V. Zikas, *Ouroboros Genesis*, ACM CCS 2018,
  https://doi.org/10.1145/3243734.3243848. The value Δ = 5 slots has **not** been located in either paper; it is a
  working target (resume item: find the section that treats Δ, or keep it labelled as a target).

## 7. Related Helen review points (files in this directory; all are the parent's summaries)

* `helen-review-10-requirements.md`: "Theorem B needs" (1)–(6) — the source of TB1–TB6; R1 margin must be a number
  from Theorem B; cell wake periods go into Theorem B.
* `helen-review-7-pass4.md` item (1)(c): Theorem B must use the enlarged mailbox sizes, since latency grows linearly
  with capacity.
* `helen-review-4-g-h.md` (d): W3 wake costs latency ≤ the timer period (Theorem B).
* `helen-review-9-mux.md`: mux semantics (`Sent`, `s_h`, `wanted`), the basis of N1–N4.
* `helen-review-1.md`: Ouroboros inputs from the papers only (Δ-bounded delivery; Genesis needs all candidates).
* `helen-review-2.md` item 5: O4/O5 must catch a lost token (Lemma 4 invariant doubles as the check).

## 8. How to resume

1. Re-read this file, `01` §4–§5 and §8 (send-timeout teardown), `03` §5, §5a, §4a, §8(b), §9, §11.
2. Check that main has not moved the relevant code since `33d62a6f` (mux, handlers, manager, tx-submission
   responder, recheck timer); refresh N1, N2, N8 if capacities or producer counts changed.
3. Extract the timeout tables for chainsync, blockfetch and keepalive from the network specification (TB6).
4. Locate Δ in the Praos paper, or keep "5 slots" explicitly as a target; decide the TB4 fraction of Δ.
5. Add the instrumentation of §5 (stage timing, mux timing, M4 high-water marks) — on the fork only.
6. Measure `D_e`, `S_s`, `S_mux`, ledger `f`; plug them into N3, TB2, TB4, TB5.
7. Decide whether the safety factor `k` also applies to N4, and state the honest-link assumption `b`.
8. Resolve N9 (`track_peers` `d + 1` vs `d + 2`).
9. If Genesis is adopted by then, add `h` (`03` §4a G4/G5) to TB4.
10. Write Theorem B as `03` §5 proper; unshelve the R1/R9 requirements accordingly.
