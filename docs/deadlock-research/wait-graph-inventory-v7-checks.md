# Wait-graph inventory, pass 7 checks

Read-only against `33d62a6f`. Line numbers are that tree. Nothing here changes a discharge row.

## 1. Re-register

`do_register` on an occupied protocol id keeps `wanted` and the incoming buffer and only swaps the handler (`crates/amaru-protocols/src/mux.rs:694-700`).

Two production paths register a protocol id that already has a handler. Neither waits for the peer to finish the old session.

**Done trap** (`crates/amaru-protocols/src/connection.rs:636-688`). `on_expected_stop` runs when `ChildDied` names a child that `begin_stop` put in `stopping` (`connection.rs:219-226`, `587-613`). For ChainSync, BlockFetch, TxSubmission, KeepAlive, and PeerSharing it clears the initiator slot and calls `install_done_trap`, which `Register`s a new handler on the same protocol id. That is a re-register.

The old session is not guaranteed Done on both sides:

- `begin_stop` only sends `Done` or `Close` (`connection.rs:594`, `598`, `602`, `608`, `612`). The trap is installed when the child stage dies, not when the peer has processed that message.
- A child already in `stopping` that dies from `eff.terminate()` or a protocol error is still "expected". The trap is installed even if `MsgDone` was never sent. Peer-sharing does this on a share timeout (`crates/amaru-protocols/src/peer_sharing/initiator.rs:130-137`). Blockfetch does it on the agency timeout (`crates/amaru-protocols/src/blockfetch/initiator.rs:321`, `373`).
- Chainsync, keepalive, and peer sharing defer the wire `Done` until a later state (section 2). The trap can therefore be installed only after a delayed `Done`, or, on the error path above, with no `Done` at all.

`ChildId::Mux`, `Handshake`, and `Responder` do not install a trap (`connection.rs:691`). An unexpected `ChildDied` tears the connection down (`connection.rs:228-235`) and does not re-register. `StopTimeout` while `stopping` is non-empty also tears the connection down (`connection.rs:237-242`).

**Use returns** (`connection.rs:694-699`, `705-775`). When the last expected child has died, `stopping` is empty, and `desired_use > None` (initiator, or a duplex responder), `on_expected_stop` calls `start_initiators` in the same turn as the trap. `start_initiators` also runs later, when `SetLocalUse` raises `desired_use` and the initiator `Option` is still `None`. Each `is_none` arm creates a new stage and `Register`s it on the same protocol id, replacing the trap.

This is mid-session. The new `Register` happens without a peer `Done`, and it inherits the trap's `wanted` and buffer. A frame the peer sent for the old session is delivered to the new handler, or, if it arrives before the swap, to the trap, which terminates the mux (`mux.rs:252-260`).

## 2. MsgDone send sites

The question is the initiator wire send: only from the idle state, with no pipelined request still outstanding.

| Initiator | Wire site | Verdict |
| --- | --- | --- |
| Chainsync | `Message::Done` only from `Idle` (`chainsync/initiator.rs:350`). Stage sends that action immediately from `Idle` (`initiator.rs:126`) or after `pending_close` once the state is `Idle` (`initiator.rs:127-129`, `174-175`). | Violation. See below. |
| Blockfetch | `ClientDone` only from `Idle` (`blockfetch/initiator.rs:279-281`, `390-392`). `Close` during `Busy` or `Streaming` sets `pending_close` and waits (`initiator.rs:317-319`, `369-371`). | Holds. One protocol state for both pipeline slots. The agency timeout terminates with no `ClientDone` (`initiator.rs:321`, `373`); that is not a send site. |
| Tx submission | `Message::Done` only from `State::TxIdsBlocking` (`tx_submission/initiator.rs:223`). | Violation. See below. |
| Keepalive | `Message::Done` only from `Idle` (`keepalive/initiator.rs:181`). `Close` in `Waiting` sets `pending_close` (`initiator.rs:94-96`) and the action is emitted after the response (`initiator.rs:127-128`), before the next timer (`initiator.rs:137`). | Holds. The in-flight cookie is the response just consumed. |
| Peer sharing | `Message::Done` only from `Idle` (`peer_sharing/initiator.rs:261`). `Close` in `Busy` sets `closing` (`initiator.rs:159-161`) and `Done` is emitted after `SharePeers` (`initiator.rs:190-192`). | Holds. That reply consumed the one outstanding request. |

**Chainsync violation.** `IntersectFound` sends `RequestNext(PIPELINE_DEPTH)` with `PIPELINE_DEPTH = 10` and sets the counter to `CanAwait(1)` (`chainsync/initiator.rs:311-318`, `chainsync/mod.rs:27`). A header at `CanAwait(0)` moves to `Idle` (`initiator.rs:324-326`). `pending_close` then emits `Done` on that transition (`initiator.rs:174-175`, `350`). The peer was asked for ten headers and can still be sending the rest. `Idle` plus `RequestNext` is the same shape: the send is `RequestNext(1)` but the next state is `CanAwait(0)` (`initiator.rs:343`), so the first header returns to `Idle`.

**Tx-submission violation.** `Close` during `TxIdsBlocking` returns `Done` immediately (`tx_submission/initiator.rs:114-116`). A blocking `RequestTxIds` that arrives while `pending_close` is set also returns `Done` (`initiator.rs:139-140`). Both go out from `TxIdsBlocking` (`initiator.rs:223`), which is the state where the peer's blocking request is outstanding. Other states only set `pending_close` (`initiator.rs:117-119`) and wait for that blocking request. There is no idle-and-drained send.

## 3. Chainsync responder, jumped tip, rolled-back point

`NewTip` stores the new tip and calls `next_header` (`chainsync/responder.rs:85-96`). It does not intersect the ancestors of the new tip with the follower's point. `find_common_ancestor` (`amaru-ouroboros-traits/src/stores/chain_store/read_chain_store.rs:173-198`) is not called on this path.

`next_header` (`responder.rs:152-179`):

- `Idle`, `Intersect`, and `Done` return `None` (`responder.rs:163-165`). A tip that arrives outside `CanAwait` or `MustReply` produces no rollback and no roll forward.
- If the pointer equals the tip, `CanAwait` yields `AwaitReply` and `MustReply` yields `None` (`responder.rs:167-168`). The skipped intermediates are not sent.
- Otherwise `next_best_chain_header` (`read_chain_store.rs:35-46`). A pointer that `is_on_best_chain` rejects (`read_chain_store.rs:37-38`) becomes `NeedRollback`, and the responder calls `find_ancestor_on_best_chain` on the pointer hash (`responder.rs:183-197`). That walks the pointer's stored parents until one is on the best chain (`read_chain_store.rs:144-162`) and emits `RollBackward` to that fork point (`responder.rs:193-195`). It is not a walk of the new tip.

An off-chain point is resolvable only when `load_header` returns it (`read_chain_store.rs:146-147`). There is no `k` bound on that walk. `is_on_best_chain` is the best-chain slot index (`amaru-stores/src/rocksdb/consensus/base_read_chain_store.rs:94-106`), so a point that shares a slot with a different best-chain header is off-chain. The consensus path does not delete headers on rollback; `remove_header` is the dev command (`rocksdb_store.rs:135`, `amaru/src/bin/amaru/cmd/dev/chain/prune.rs:97`). A point that was never stored, or that was removed, is `StartHeaderNotFound` (`read_chain_store.rs:147`, `responder.rs:189`) and `next_header` returns the error at `responder.rs:96`.

## 4. Restart without tearing the connection down

`supervise` does not recreate a stage. It delivers a tombstone. The only production recreate-on-the-same-connection is `start_initiators` after an expected initiator death (section 1): ChainSync, BlockFetch, TxSubmission, KeepAlive, PeerSharing.

These deaths do not tear the connection down, and they do not send `Terminated`. `notify_chainsync_terminated` runs only from connection teardown (`connection.rs:310-312`, `319-329`).

There is no field named `outstanding_i`. What stays behind:

| Stage that died | State left on the other side |
| --- | --- |
| Chainsync initiator | `track_peers` `upstream` and `deferred`, both keyed by `conn_id` and holding the dead `handler` (`track_peers/mod.rs:234`, `594-597`). `sent_request_next` is a bool on the header args (`track_peers/mod.rs:257`, `876-877`, `1015`), not a counter that is cleared on death. Purged on the next `Initialize` (`track_peers/mod.rs:897`) or on `Terminated`. Mux `wanted` and `incoming` survive the swap (`mux.rs:694-700`). |
| Blockfetch initiator | `fetch_blocks` `missing`, `req_id`, `timeout`, `widen`, and `fetch_peers` (`fetch_blocks/mod.rs:412-455`). In-flight `Blocks` still go to `cleanup_replies`. The connection drops a new `FetchBlocks` only while `stopping` contains `BlockFetch` (`connection.rs:248-254`). Mux credit as above. |
| Tx initiator | Mempool `waiters` and `capacity_waiters` hold the dead `caller` (`mempool/stage.rs:72`, `112`, `186-187`, `194-195`). Mux credit as above. |
| Keepalive initiator | The next-cookie `schedule_after` (`keepalive/initiator.rs:137`) is delivered to a dead stage and dropped (`simulation/running/mod.rs:2048-2050`). `PeerTrack` RTT is kept. Mux credit as above. |
| Peer-sharing initiator | The share timer (`peer_sharing/initiator.rs:113`) is dropped the same way. Recorded shared peers stay in `PeerTrack`. Mux credit as above. |

Responder, mux, handshake, reader, and writer death is unexpected and tears the connection down (`connection.rs:228-235`). `ledger-check` is not restarted (`peer_selection/mod.rs:1199`). Accept, forge, mempool, and the consensus stages are not per-connection and are not recreated.

## 5. Lost sends

A blocking `Send` to a stage that has terminated:

| Send | Site | Does the loss matter |
| --- | --- | --- |
| `RequestNext` to the chainsync handler | `track_peers/mod.rs:877`, `1015`, `1049`, `1069` | Yes. The dead initiator never asks for the next header. The replacement does not see this send. The follower stalls until some later `Initialize`. |
| `Done` to the chainsync handler | `track_peers/mod.rs:911`, `931`, `1063` | The session is already being stopped. The wire `Done` is not sent. `track_peers` does not purge on this path. |
| Waiter wakeup `()` | `mempool/stage.rs:70`, `187` | The waiter entry is removed before the send. A dead initiator misses a wakeup it can no longer use. The mempool is not stuck. A replacement initiator registers its own waiter. |
| Capacity wakeup `()` | `mempool/stage.rs:195` | Same. The subscriber is already gone. |
| `Insert` / `InsertBatch` reply | `mempool/stage.rs:85`, `99` | The caller has exited. The sender is resumed (below), so other mempool clients are not stuck. |
| `FetchBlocks`, `NewTip`, `SetLocalUse`, `Disconnect` to a connection | manager stage arms, `manager/mod.rs:864-870` and the fetch loop `776` | The connection is gone, so the command is dropped. `ConnectionDied` is what removes it from the manager map. A command sent after that removal is lost. No live stage is waiting on it. |
| `Done`, `Close`, `RequestRange`, `NewTip` to an initiator | `connection.rs:594-612` and the chainsync `NewTip` forward | Lost when the child died first. `begin_stop` then treats the later `ChildDied` as expected only if the child was already in `stopping`. |

**Tokio panics, the simulation drops.** `StageEffect::Send` to a name that is not in the sender map panics in tokio (`amaru-pure-stage/src/tokio.rs:720-724`, `"stage ref contained unknown name"`). The simulation logs and drops that send, then resumes the sender (`simulation/running/mod.rs:1307-1309`).

A stage that was created and then terminated does not hit that panic in tokio. The sender map is insert-only (`tokio.rs:278`, `840`); the `mpsc` send fails because the receiver is gone, and `.ok()` drops it (`tokio.rs:726`). The simulation has removed the stage, so the same send is the `NotFound` drop above. Both runtimes drop it. The panic-versus-drop split is a name the tokio map never contained.

`TrySend` to a missing name returns `Gone` in both (`tokio.rs` try-send arm, `simulation/running/mod.rs:1220-1221`). A scheduled self-message to a terminated stage is dropped (`simulation/running/mod.rs:2048-2050`).

## 6. Priority and schedule lane

Each stage has its own priority mailbox of 10 (`amaru-pure-stage/src/types.rs:44`). `schedule_after` and `schedule_at` increment `scheduled_pending` and panic at the cap (`tokio.rs:864-870`). A due message also panics if the priority queue is already full (`simulation/running/mod.rs:2052-2054`). `set_timeout` / `set_timeout_at` do not occupy that mailbox: the runtime arms one timer (`effect.rs:463-467`). That excludes the connection `StopTimeout`, the blockfetch agency timeout, and the peer-selection `Tick` (`peer_selection/mod.rs:1066-1068`).

Outstanding `schedule_after` / `schedule_at` per stage:

| Stage | Producers | Outstanding |
| --- | --- | --- |
| `accept` | reschedule `PullAccept` (`accept.rs:39`) | 1 |
| `connection` | reschedule of `FetchBlocks`, `NewTip`, `SetLocalUse` while not yet established (`connection.rs:272`, `277`, `281`) | one per deferred message, no cancel, no cap |
| keepalive initiator | next cookie (`keepalive/initiator.rs:137`) | 1, armed after the previous one fires |
| peer-sharing initiator | `arm_timer` (`peer_sharing/initiator.rs:109-113`) | 1, previous cancelled |
| tx responder | inflight timeout (`tx_submission/responder.rs:713-739`) | 1, previous cancelled |
| `ledger-check` | self reschedule (`peer_selection/mod.rs:1305`) | 1 |
| `track_peers` | one `RecheckLedgerHeight` (`track_peers/mod.rs:686-712`) | 1 |
| `fetch_blocks` | `Timeout` (`fetch_blocks/mod.rs:454`) and `Widen` (`fetch_blocks/mod.rs:467`) | 2, both cancelled before the next attempt (`fetch_blocks/mod.rs:411`, `649-650`) |
| `forge` | one `DueLead` (`forge_block/protocol.rs:154`), previous cancelled (`protocol.rs:165-166`) | 1 |

The connection reschedule is the producer that can pass 10: every manager message received before `Established` adds a schedule and none is cancelled. Every other producer stays at or under 2.

`supervise` tombstones are pushed onto the same priority path without incrementing `scheduled_pending` (`tokio.rs:850-861`). A burst of child deaths is not part of the schedule count above and still lands in the priority queue.

## 7. Connection ids

Not reused in operation. `ConnectionId::get_and_increment` returns the current value and then `wrapping_add(1)` (`amaru-ouroboros-traits/src/connections/connection_provider.rs:58-62`), starting at 0 (`connection_provider.rs:65-67`). The production allocator is `Connections::add_connection` (`amaru-network/src/connection.rs:79-82`). `remove` deletes the map entry and does not return the id (`amaru-network/src/connection.rs:93-95`). The same counter is used by the in-memory test provider (`amaru-node/src/tests/in_memory_connection_provider.rs:428-429`). The only reuse is the `u64` wrap.

## 8. Fetch peer set, `peers: None`

`fetch_blocks` calls `Performance::select_peers_for_fetch` with `max_peers: MAX_FETCH_PEERS` (`fetch_blocks/mod.rs:33`, `423-429`). It sends `peers: None` when the selection is weak or empty (`fetch_blocks/mod.rs:431-434`). Otherwise it sends `Some(selected.peers)` (`fetch_blocks/mod.rs:435-437`). The widen path uses `MAX_FETCH_PEERS` minus the peers already asked (`fetch_blocks/mod.rs:509-530`) and returns without asking when a broadcast has not named anyone yet (`fetch_blocks/mod.rs:506-508`).

`ManagerMessage::FetchBlocks` with `peers: None` broadcasts to every connection whose id is in `PeerTrack::may_initiate()` (`manager/mod.rs:767-776`). `Some(wanted)` filters to those peers (`manager/mod.rs:779-791`). The broadcast does not read `MAX_FETCH_PEERS`.

A cap on the `None` path would touch the loop at `manager/mod.rs:771-776`. The existing `MAX_FETCH_PEERS` touches the selector arguments at `fetch_blocks/mod.rs:426` and the widen room at `fetch_blocks/mod.rs:510`, not the broadcast.
