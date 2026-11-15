# Helen review 10 (critical pass on R1–R9) — parent's summary, not Helen's verbatim text

Source: the parent agent's summary in the 12:16 (UTC+1) message of 2026-11-15. Helen's original text was not supplied.

- **R1:** the margin must be a number from Theorem B: worst-case mux queueing for a `Send` ≤ (mux capacity + parked
  senders) × mux service time ≤ timeout / k. With `s_h = 1` and ≤ 10 handlers per connection, `Send`s in the mux
  mailbox are ≤ 10.
- **R2:** re-register only after the old session reached `Done` on both sides; any other replacement (use returns
  mid-session) tears the connection down.
- **R10 (new):** `MsgDone` only from `StIdle` with nothing pipelined outstanding; the initiator collects every reply
  first. Asserted at the send site.
- **R5:** every cell has a single writer or a lattice merge, is read on init, restart and each transition, and has a
  stated wake (dirty bit or W3 period; the period goes into Theorem B). The chainsync responder's `NewTip` cell must
  compute `RollBackward` intersections from the store (needs off-chain points within `k` to resolve); otherwise it is a
  correctness bug.
- **R7:** `conn_id`s are never reused; the dedup set is pruned only on termination.
- **R11 (new):** a `MAX_FETCH_PEERS` constant (`A = 5`, implied by `fetch_blocks` 67) and a named cap for `L`.
- **Missing:** M1 restart/supervision re-init; M2 lost sends (tokio panics versus the simulation dropping on unknown
  names); M3 priority lane `ΣW ≤ 10`; M4 debug assertions at every discharged send site (occupancy + parked ≤ bound;
  a park on a discharged edge fails the simulation; per-mailbox high-water marks against the formulas).
- **Theorem B needs:** (1) quantitative A-int: `D_e` per internal effect, ledger validation bounded via
  `maxBlockExUnits`/`maxBlockBodySize`, measured; (2) per-stage service time `S_s`, hop bound (capacity + parked) ×
  `S_s`, FIFO parked admission; (3) utilisation < 1 at config maxima (pull-based: `N_max` × credit × cost) or admission
  control; (4) critical-path budget header → validate → select → fetch → adopt → re-announce plus cell poll periods, as
  a share of Praos Δ (working target 5 slots, from the security model, not Haskell); (5) per-peer fairness: ≤ `N_max − 1`
  others plus capacity; (6) separate timer budgets (R1 margin, keepalive, chainsync, blockfetch), showing no protocol
  timeout fires on an honest peer from local queueing alone.

Pass 7 is checking M1–M3 and R2/R5/R10 in code; those are pending.
