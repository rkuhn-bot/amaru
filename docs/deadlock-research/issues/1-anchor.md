Checked against `main` at 33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6.

## What happens

`select_chain` picks the best tip without ever reading the anchor. `adopt_chain` keeps moving the anchor forward behind the adopted tip. If the anchor passes the fork point of the candidate that `select_chain` currently considers best, that candidate can no longer be fetched, and the node stops fetching blocks for good.

The sequence:

1. A fork peer announces a taller tip. `select_chain` makes it the best tip and sends `NewBestTip` to `fetch_blocks`, consuming `may_fetch_blocks`.
2. Before `fetch_blocks` processes it, `adopt_chain` adopts the previous best and drags the anchor forward past the fork's intersection with the adopted chain.
3. `fetch_blocks` walks back from the new best tip looking for missing bodies. The walk stops at the anchor slot without reaching a stored body, so `find_missing_blocks` returns `BoundaryNotFound`.
4. `fetch_blocks` clears `missing` and returns. It neither sends `FetchNextFrom` nor terminates.
5. `may_fetch_blocks` stays false, so every later (honest) best tip only updates `select_chain`'s state. No `NewBestTip` is sent again and nothing times out.

## Where

- `select_chain` sends `NewBestTip` only while `may_fetch_blocks` is set and clears it as it sends ([select_chain/mod.rs#L302-L305](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L302-L305), [#L397-L402](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L397-L402)); the flag is set again only by `FetchNextFrom` ([#L437](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L437)). The stage has no anchor read outside its tests.
- `adopt_chain` drags the anchor forward ([adopt_chain/mod.rs#L328-L330](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/adopt_chain/mod.rs#L328-L330)).
- The missing-block walk stops at the anchor slot ([read_chain_store.rs#L353](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-ouroboros-traits/src/stores/chain_store/read_chain_store.rs#L353)) and returns `BoundaryNotFound` ([#L284-L300](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-ouroboros-traits/src/stores/chain_store/read_chain_store.rs#L284-L300)).
- `fetch_blocks` drops the fetch permission on `BoundaryNotFound` ([fetch_blocks/mod.rs#L350-L353](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L350-L353)).

## Why it matters

This is a liveness failure with no recovery: the node keeps following headers but never fetches or adopts another block. The race needs only an ordinary fork and normal adoption timing, so it is reachable on a live network. It is one reachable cause of the `BoundaryNotFound` stall; the other is a best tip whose ancestry is not in the store at all.

## Proposed fix

Under Praos: candidates whose intersection with the current chain lies below the anchor are no longer eligible (the node cannot roll back past the anchor). When the anchor moves, `select_chain` prunes those candidates and recomputes the best tip; if the best changes and `fetch_blocks` holds the permission, it is sent the new best.

Under Genesis the rule would be different: the anchor must not advance past the common intersection of the candidates being compared, so pruning would not be the right response. Which of the two applies to Amaru is an open design question, and the fix depends on that decision.

Independently, `fetch_blocks` should not end up holding no fetch permission after `BoundaryNotFound`: a store inconsistency (missing ancestor) should terminate loudly, while the anchor race should hand the permission back so that `select_chain` can offer the recomputed best.

## How found

Analysis of the stage wait graph, tracking the `may_fetch_blocks` permission as a token that must never be lost. Both cases are reproduced by intentionally failing simulation tests on the analysis fork:

- [rkuhn-bot/amaru pull 45](https://github.com/rkuhn-bot/amaru/pull/45) — the anchor drag strands a fork (this race)
- [rkuhn-bot/amaru pull 46](https://github.com/rkuhn-bot/amaru/pull/46) — `BoundaryNotFound` leaves fetching stopped
