# Helen review 11 (on pass 7) — parent's summary, not Helen's verbatim text

Source: the parent agent's summary in the 12:22 (UTC+1) message of 2026-11-15. Pass 7 is
`scripts/wait-graph-inventory-v7-checks.md` at fork commit `7ccaa7ab3` (copied here as
`wait-graph-inventory-v7-checks.md`).

Rulings:
1. **Chainsync initiator `Done` is a real violation.** `MsgDone` is legal only from `StIdle` with zero outstanding;
   outstanding = `RequestNext` sent − (`RollForward` + `RollBackward`) received; `AwaitReply` does not decrement it.
   The `CanAwait(0) → Idle` shortcut (`initiator.rs:311–326, 343`) lets `Done` go out with replies due; the honest
   peer's replies then hit the done trap, a local-cause teardown. Requirement: track outstanding explicitly and gate
   `Done` on 0. Justification: the ChainSync state machine of the Ouroboros network specification; Haskell code may be
   mentioned only as the source of the idea.
2. **TxSubmission `Done` from `TxIdsBlocking` is legal** (the client's termination reply to a blocking request). Gate it
   to that state.
3. **REQ-resolve (new):** for every live follower pointer `p`, the responder can compute `intersect(p, best chain)` by
   walking stored parents. Sufficient: header GC never prunes headers reachable from a live follower pointer back to the
   best chain. Bound: rollback ≤ `k`, so the walk is ≤ `k` steps and memory ≤ `F·k` headers. An unstored `p` or a walk
   longer than `k` is an internal invariant violation: assert it in the simulation; never blame or tear down the peer.

Updated requirements:
- R2: any per-connection handler death without `Done` tears down the connection; `start_initiators` must not resurrect
  handlers in the same turn.
- M1: `track_peers` cleans `upstream`/`deferred` on `Terminated`; bound the mempool waiter lists and purge dead callers
  (mostly moot under R5 cells).
- M2: the simulation must be at least as strict as tokio: panic on a never-registered name.
- Schedule: cancel-before-rearm, so the lane is ≤ 2 per stage (hard bound).
- `conn_id` wrap at 2^64: an assumption plus an assert.
- R11: `fetch_blocks` = 67 is unsound until `MAX_FETCH_PEERS` caps the peers: `None` broadcast at `manager:767–776`.
- Pass-7 orphans: `fetch_blocks` `missing`/`req_id` on blockfetch restart, mempool waiters, keepalive/peer-sharing timers
  dropped at dead stages.
- Tests: chainsync `Done` with 9 replies in flight must be impossible; restart orphan test; schedule overflow test.
