Checked against `main` at 33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6.

## What happens

Every submit-API request does a `Sender::call` with `MempoolMsg::Insert` into the mempool stage. The HTTP server has no limit on concurrent requests, so the number of `Insert` calls waiting for admission to, or sitting in, the mempool's bulk mailbox (capacity 10) is unbounded. A burst of local submissions fills the mailbox, and every other producer then waits behind it.

## Where

- Router and server, no concurrency limit: [submit_api.rs#L44-L53](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-node/src/submit_api.rs#L44-L53).
- One `call` per request, 5 s timeout that also covers admission: [submit_api.rs#L84-L89](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-node/src/submit_api.rs#L84-L89), [sender.rs#L62-L80](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-pure-stage/src/sender.rs#L62-L80), [responder_params.rs#L45-L46](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/tx_submission/responder_params.rs#L45-L46).
- Mempool stage with the default mailbox: [build_stage_graph.rs#L117](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-node/src/stages/build_stage_graph.rs#L117).
- Other producers into the same mailbox: `adopt_chain` sends `NewTip` with a blocking send ([mod.rs#L263-L264](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/adopt_chain/mod.rs#L263-L264)); each tx-submission responder calls `InsertBatch` and terminates on timeout ([responder.rs#L607-L617](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/tx_submission/responder.rs#L607-L617)).

## Why it matters

- `adopt_chain` parks on the mempool mailbox while local HTTP clients hold it, so block adoption and the `NewTip` that follows it to the manager are delayed by local submit traffic.
- Tx-submission responders wait for the same slots; when their 5 s call times out they terminate, which disconnects honest peers because of local load.
- Without a cap there is no finite bound on mempool mailbox occupancy, which the deadlock and timeliness arguments for the stage graph need.

## Proposed fix

Introduce a named cap `L_max` on concurrent submit-API inserts (for example a semaphore in the handler, or a concurrency-limit layer on the router) and answer `503` immediately when it is exhausted, instead of queueing. Then size the mempool bulk mailbox from configuration so that admission never waits: one `InsertBatch` per inbound responder, `L_max` submit calls, and one `NewTip`, i.e. `max_inbound + L_max + 1`.

## How found

Analysis of the stage wait graph: counting the producers into the mempool mailbox, the submit API is the one term with no bound. Found by code reading; there is no simulation reproduction yet.
