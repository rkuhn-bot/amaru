# Helen review 8, 2026-11-15 ~11:47

Recorded from the parent agent's message of 11:47 (UTC+1). This is the parent's summary of Helen's review 8, not her
original wording.

- B1: state that the resource write is the linearisation point, and that N_max counts conn_ids (a reconnect gets a new id, still bounded by the accept cap).
- B2/B3: count the dirty-bit wakes (≤1 per cell per receiver) explicitly. Name every term of 62 = 4·N_max + 2·max_outbound + 4. Derive manager's producer list MECHANICALLY with the script (extend scripts/ to list every send/StageRef path into manager), not by hand, and reconcile it with the formula.
- B4: define L.
- B5: write down that the latest-wins pending range depends on the cleanup filter (non-current ids are irrelevant). Replacing an unsent range must never touch the in-flight range. Widen adds peers, not ranges, so assert one range per id. Then run the per-kind occupancy check for mux ↔ blockfetch_initiator.
- WaitForAtLeast: reclassify it as peer-unbounded, not a delay. Fix: a single-writer monotone seq cell (Lemma 2, M1). The tx initiator registers interest, keeps dequeuing, and re-reads on a dirty-bit wake or W3. The peer's blocking RequestTxIds wait lives in the initiator's protocol state.
- InsertBatch timeout: requirement is to REMOVE it (H4 is shown; it is an eclipse lever and violates 01 §8). A watchdog may only log or terminate the node, never disconnect a peer.
- schedule_after: check in pure-stage what a full 10-slot schedule does (block, drop or panic) for schedule_after versus schedule_at. Requirement: cancel-before-rearm per timer purpose. Count the timer purposes for each stage and show ≤ 10, or size the table; classify by the observed behaviour.
- BoundaryNotFound: the race is reachable and the stall is a real liveness hole. Praos maxvalid only allows forks ≤ k deep, so when the anchor moves, select_chain must disqualify candidates whose intersection is below the new anchor and recompute best; the anchor reaches it through a single-writer monotone cell. Liveness holds under honest majority with ≥ 1 honest peer. Record the Genesis divergence (maxvalid-bg may prefer deeper forks; the Genesis-correct rule is to not advance the anchor past the common intersection of the compared candidates). OPEN QUESTION FOR ROLAND: does Amaru claim Praos-only or Genesis sync? Check in code whether select_chain already prunes on anchor moves.
- Acceptance test 9: a scripted race where the anchor passes the current best's fork point; the node must switch best within bounded time and keep fetching.
