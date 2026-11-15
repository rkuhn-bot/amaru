This issue reports a wait-graph analysis of the pure-stage network on `main` at 33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6, done as the first step towards a deadlock-freedom argument for the node. The analysis is read-only and changes no code.

## Method

Nodes are stage mailboxes, plus the few other things a stage can wait on. There is an edge `M1 → M2` when a stage that has taken a message from `M1` can park on `M2` before it receives again. Edges are classified as follows:

- **blocking**: `eff.send` into a bounded bulk mailbox. The sender parks until a slot frees up and receives nothing meanwhile.
- **timeout**: `eff.call`, or peer I/O with a finite deadline.
- **delay**: ledger, chain store, `Performance` worker, timers. These take time but complete without any stage making progress.
- **drop**: `try_send`, a send to a terminated stage, or a call reply via oneshot.

A buffer deadlock needs a cycle made only of blocking edges, with every mailbox on it full at the same moment. A cycle in the edge labels is therefore necessary but not sufficient. Whether the mailboxes can actually fill depends on credit: how many messages each producer can have in flight towards a mailbox, compared with its capacity. Each cycle below is described by its edges, the schedule that would close it, and the credit that may prevent that schedule.

Capacities: bulk default 10 ([`DEFAULT_MAILBOX_SIZE`](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-pure-stage/src/types.rs#L53)). `mux` has 24, the chain-sync initiator has `PIPELINE_DEPTH + 4` = 14 ([chainsync/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/chainsync/mod.rs#L33)), and `manager`/`peer_selection` have `10 + targets`. `track_peers`, `select_chain`, `fetch_blocks` and `validate_block` are all 10 ([build_stage_graph.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-node/src/stages/build_stage_graph.rs#L112-L115)), independent of the number of peers.

## Regression check: #1475 is fixed

On the pre-fix parent 9a4273855, `manager` blocking-sent `Connected`/`Disconnected`/`ConnectFailed` to `peer_selection`, and `peer_selection` blocking-sent `AddPeer`/`Disconnect`/`SetLocalUse` back to `manager`. That is a two-node cycle of blocking edges, and it produced the mainnet lockup. Since dcffd9dcb, `manager` records lifecycle on the peer-tracking resource (a delay edge) and has no send to `peer_selection`. The remaining `peer_selection → manager` blocking edge is acyclic. Any checker built for this must flag 9a4273855 and pass 33d62a6f.

## 1. Ledger stake callback ↔ `track_peers` (real wait cycle)

This is the clearest finding, because it breaks the assumption that internal effects always complete on their own.

Edges:
- **ledger thread → `track_peers` mailbox (blocking).** At stake-distribution rotation, the ledger calls the notify callback *on the ledger thread, before the current ledger request returns* ([state.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-ledger/src/state.rs#L1267-L1289)). The node's callback does `rt.block_on(track_peers_sender.send(StakeDistUpdated(..)))` ([build_node.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-node/src/stages/build_node.rs#L500-L511)). That is a blocking input send into `track_peers`' bulk mailbox of 10.
- **`track_peers` → ledger thread (wait).** `track_peers` refreshes the volatile tip through `VolatileTipEffect` ([track_peers/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L993), [L1086](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L1086)). That goes through `BlockValidator::request` and waits for the same ledger thread to answer.

Schedule:
1. During sync, chain-sync initiators keep `track_peers`' 10 slots full. That is normal, because hundreds of peers fan into one mailbox.
2. `validate_block` sends a block across an epoch boundary, and the ledger thread starts the stake rotation and calls the callback.
3. The callback parks on the full `track_peers` mailbox. The ledger thread is now stuck inside that request.
4. `track_peers` takes its next message and issues `VolatileTipEffect`. The request queues behind the stuck one on the ledger thread, and `track_peers` parks.
5. Nobody drains `track_peers`, so the callback never returns, so the ledger never answers. Every other ledger user (block validation, relay candidates, tx validation) stalls with it, and all initiators then park on `track_peers`.

No timeout is involved anywhere, so this never recovers. The data already goes through `resources.put`, so the message only serves as a wakeup. A callback running on an effect's thread is part of that effect, so it must never wait on a stage.

## 2. Chain pipeline: `select_chain` → `fetch_blocks` → `validate_block` → `select_chain`

Edges (all blocking, all capacity 10):
- `select_chain → fetch_blocks`: `NewBestTip` ([select_chain/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L305), [L478](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L478-L481)).
- `fetch_blocks → validate_block`: one `DownloadedBlock` per block, up to a batch of 25 ([fetch_blocks/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L310), [L395](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L395), [L641](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L641)).
- `validate_block → select_chain`: validation result ([validate_block/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/validate_block/mod.rs#L111-L115)).
- There is also a shorter loop: `fetch_blocks → select_chain` via `FetchNextFrom` ([L758](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L758)), with `select_chain → fetch_blocks` coming back.

Other producers fill these mailboxes too. `track_peers` sends `NewTip` into `select_chain` for every stored header from every peer ([track_peers/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L868)). The `cleanup_replies` child forwards `Block`/`NoBlocks`/`PeersAsked` into `fetch_blocks` ([fetch_blocks/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L851-L877)).

The schedule that would close it: `fetch_blocks` is parked sending a block into a full `validate_block`. `validate_block` is parked sending a result into `select_chain`, which is full of `NewTip` from `track_peers`. `select_chain` is parked sending `NewBestTip` into `fetch_blocks`, which is full of block replies.

What prevents it today is the `may_fetch_blocks` credit. `select_chain` sends to `fetch_blocks` only in answer to an unanswered `FetchNextFrom`; the assert at [L443](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/select_chain/mod.rs#L443) enforces at most one outstanding. `fetch_blocks` sends `FetchNextFrom` only after setting `missing = None` (batch done at [L644-L653](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L644-L653), timeout at [L746-L750](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/fetch_blocks/mod.rs#L746-L750)). Until `NewBestTip` arrives it only handles stragglers, timers and bookkeeping, and none of those send to `validate_block` or `select_chain`. So whenever `select_chain` is parked on `fetch_blocks`, `fetch_blocks` is not parked and will drain its mailbox. The short `FetchNextFrom` loop is excluded the same way: `fetch_blocks` cannot send a second `FetchNextFrom` while the first is unanswered.

On this reading, the cycle exists in the edge labels but cannot close. The protection is implicit, though: it rests on an invariant spread across two stages, and nothing in the types states it. Any new send to `validate_block` or `select_chain` from `fetch_blocks` outside a credit window, or any `select_chain → fetch_blocks` send not paired with a `FetchNextFrom`, would reopen the cycle. A simulation reproduction attempt (catch-up, ≥3 peers, a deferring scheduling strategy) is running on an experiment branch to confirm.

## 3. Per-connection mux ↔ handler

Edges:
- **mux → handler (blocking).** `FromNetwork` for each reassembled message while `wanted > 0` ([mux.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/mux.rs#L842-L848)), or directly from `want_next` when data is already buffered ([L852-L864](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/mux.rs#L852-L864)).
- **handler → mux (blocking).** `WantNext` ([miniprotocol.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/protocol/miniprotocol.rs#L228)). The wire send right after it is a `call` with the 1 s `NETWORK_SEND_TIMEOUT` ([L232-L235](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/protocol/miniprotocol.rs#L232-L235)), but its *admission* still needs a slot in the mux mailbox.
- Fan-in: up to ten mini-protocol handlers, the reader (`FromNetwork` segments) and the writer (`Written`) all share the one mux mailbox of 24.

Schedule:
1. Handler H's mailbox fills. `FromNetwork` alone cannot do it, because the mux pushes at most `wanted` of those. It needs H's other producers, e.g. `RequestNext`/`Done` from `track_peers` for chain-sync, or fetch requests for block-fetch.
2. The mux pushes the next `FromNetwork` to H and parks. While parked, it neither receives nor issues the next `Read` to the reader ([L453-L464](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/mux.rs#L453-L464)).
3. H, processing its current message, sends `WantNext` (or a call admission) into the mux mailbox. Other handlers and the reader have meanwhile filled it, so H parks too.
4. Neither drains. Every mini-protocol on that bearer stops, keep-alive included, and TCP backpressure stalls the peer. The remote side will eventually drop the connection, but a stuck bearer also leaks the stages it holds, and keep-alive timing is then controlled by the peer, not by us.

Whether step 1 and step 3 can both happen comes down to counting. For each handler, its in-flight messages from all producers must stay below its capacity, and the sum over all handlers plus reader and writer must stay below 24. One complication: when the 1 s call deadline fires after admission, the `Send` stays queued in the mux mailbox while the handler moves on. So a slow mux lets one handler accumulate several admitted `Send`s, and the simple "at most one call per handler" count does not hold. The same expiry also needs a defined meaning: if the wire message is still sent later, fine; if it is dropped while the typestate believes it was sent, the protocol state desyncs.

## 4. Chain-sync initiators ↔ `track_peers` (the #1475 shape, with N-fold fan-in)

Edges:
- **each initiator → `track_peers` (blocking).** One `ChainSyncInitiatorMsg` per wire reply ([chainsync/initiator.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/chainsync/initiator.rs#L169-L173)).
- **`track_peers` → that initiator (blocking).** `RequestNext` ([track_peers/mod.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L877), [L1015](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L1015), [L1049](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L1049), [L1069](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L1069)) and `Done` ([L911](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L911), [L931](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L931), [L1063](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-consensus/src/stages/track_peers/mod.rs#L1063)).

`track_peers` has 10 slots shared by every upstream peer, plus the ledger callback (section 1). With N peers each pipelining up to `PIPELINE_DEPTH` headers, up to N·`PIPELINE_DEPTH` messages may want into those 10 slots. Initiators parking on `track_peers` is therefore routine during sync. That is backpressure and harmless in itself.

The schedule that deadlocks: `track_peers` handles initiator I's message and parks sending `RequestNext` to I because I's 14 slots are full, while I is parked sending its next reply into the full `track_peers`. This is the same two-node shape as #1475, except that the second mailbox is shared by all peers.

What may prevent it: chain-sync requests act as tokens. After intersecting, I starts with `PIPELINE_DEPTH` requests outstanding ([initiator.rs](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/chainsync/initiator.rs#L313-L316)). Each reply becomes one message to `track_peers`, and each such message produces at most one `RequestNext` back. If that is exact, I's mailbox never holds more than `PIPELINE_DEPTH` + a few control messages, which is what the `+ 4` is sized for. Then `track_peers → I` never parks and the cycle cannot close. The proof needs an exact per-initiator count of every message kind `track_peers` and the mux can put into I's mailbox (`RequestNext`, `Done`, `FromNetwork`, tombstone-related traffic). It also needs every `track_peers` code path to send at most one `RequestNext` per received message. Neither is checked yet.

Fairness is a separate concern from deadlock: one fast peer can occupy most of `track_peers`' 10 slots and delay header processing for everyone else.

## 5. What the typestate graph covers today

`make_states!`/`on_receive!` produce a `TypeGraph` with `Send`, `Call`, `SendAny`, `External`, `Detach`, `Wait` and others. Only block-fetch (initiator/responder) and forge use it. All consensus stages (`manager`, `peer_selection`, `track_peers`, `select_chain`, `fetch_blocks`, `validate_block`) and chain-sync are plain `async fn` transitions. `project()` yields a protocol role's wire send/recv machine. It does not carry target mailbox identity (roles are `ToMux`/`ToCollector`), capacity, blocking versus timeout, fan-in, `try_send`, dynamic spawn, supervision, or effect-thread callbacks. Extracting the wait graph from the types needs that information, so it is worth adding as the consensus stages move onto the typestate API.

## Next steps

- An exhaustive pass listing every send with its producer, target, message kinds and grep counts, plus credit bounds for every blocking edge and a table of required capacity against current capacity per mailbox.
- A simulation reproduction attempt for section 2, on an experiment branch outside this repo.
- Fix section 1, which needs no theory: make the stake notification a non-blocking, coalescing wakeup.
