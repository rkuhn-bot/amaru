# Wait-graph inventory, pass 4

Tree: `33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6`. Read-only. The discharge checker is `scripts/wait-graph-sccs.py` on `experiment/deadlock-chain-pipeline` in the rkuhn-bot fork. No node code is changed.

`N_max = max_inbound + max_outbound`. In this tree `max_inbound` is the downstream target (`DEFAULT_PEERS_MAX_DOWNSTREAM = 10`, `DEFAULT_MAX_INBOUND = 10`) and `max_outbound` is `target_upstream_peers` (`DEFAULT_PEERS_MAX_UPSTREAM = 3`). At the defaults, `N_max = 13`. Manager and peer selection mailboxes are `10 + max_outbound + max_inbound` (`build_stage_graph.rs:71-73`), so 23. The chainsync initiator bulk mailbox is `PIPELINE_DEPTH + 4 = 14` (`chainsync/mod.rs:27-33`).

An edge is L1-discharged only when the sum of every producer into that mailbox is at most the capacity. One producer's own bound is not enough.

## 1. Discharge checker

The script reads `wait-graph-v4.json` and `wait-graph-v4-discharge.json` from the same directory. Each row names the edge, the lemma (L1 credit/occupancy, L2 superseding cell, L3 ingress teardown, L4 state-indexed), the W formula, the capacity, the code location, and a status for `now` and for `after`. A status of `discharged` deletes that edge and the script recomputes the strongly connected components. It exits 0 only when every component is one stage and no blocking self-loop remains. A self-loop is a cycle even though its component has size one.

`now` is this tree. `after` deletes an edge only where the row says the proposed fix discharges it. The fixes modelled, and only those, are:

- a connection cap before an id is minted, on both mint paths, with `N_max = max_inbound + max_outbound`
- a shared grow-only reported set, so every Adversarial site together satisfies `W ≤ 7·N_max`
- an explicit `MAX_FETCH_PEERS` on the `peers: None` path
- a per-connection RequestNext credit topped up to `PIPELINE_DEPTH`, and a Done-once flag in track_peers
- a cleanup → fetch_blocks filter on a `(req_id, missing)` cell
- a fresh-start `FetchNextFrom(Origin)`
- the stake callback replaced by a monotone cell polled on track_peers' recheck timer
- `NewBestTip` discharged by the select_chain / fetch_blocks token

The fresh-start send restores the startup token (section 5). It does not delete a wait edge. The `(req_id, missing)` cell and the `MAX_FETCH_PEERS` cap on the broadcast path cut stale ids and cap the fan-out at 5, and the occupancy of a live id is still `5 · MAX_FETCHED_BLOCKS = 5000` (section 6), which is above every mailbox of 10. Those three fixes are in the table and leave the edges blocking.

Both modes exit 1.

### now

Kept 40 blocking edges, discharged 3:

- `connector → connect_worker [ConnectJob]` (L1). One job per worker until `WorkerDone`. `W = 1 ≤ 10`.
- `manager → accept [PullAccept]` (L1). One bulk pull at listen. Later pulls are priority self-schedules. `W = 1 ≤ 10`.
- `select_chain → fetch_blocks [NewBestTip]` (L4). The token. Section 5.

Residual SCC, size 14: `adopt_chain`, `block_source`, `blockfetch_initiator`, `chainsync_initiator`, `cleanup_replies`, `connection`, `connector`, `fetch_blocks`, `ledger`, `manager`, `mux`, `peer_selection`, `track_peers`, `validate_block`.

Residual SCC, size 2: `mempool`, `tx_submission_responder`.

Residual self-loop: `peer_selection → peer_selection [Resolved]`.

`select_chain`, `accept`, and `connect_worker` are outside the size-14 component. Each still has a one-way blocking edge into it (`FetchNextFrom`, `NewTip`, `BlockValidationResult` into select_chain; `Accepted` into manager; `WorkerDone` into connector). `ledger` is inside because the stake send and `VolatileTipEffect` wait on each other (section 1, stake row).

### after the proposed fixes

Kept 35, discharged 8. The three above, plus:

- `track_peers → chainsync_initiator [RequestNext/Done]`, `mux → chainsync_initiator [Registered/FromNetwork]`, `connection → chainsync_initiator [Done]` (L1). Joint sum in section 3 is 13 ≤ 14.
- `ledger → track_peers [StakeDistUpdated]` and `track_peers → ledger [VolatileTipEffect]` (L2). The cell removes the send, so the epoch-transition join no longer waits on a stage and the effect is a delay again.

Residual SCC, size 12: `adopt_chain`, `block_source`, `blockfetch_initiator`, `cleanup_replies`, `connection`, `connector`, `fetch_blocks`, `manager`, `mux`, `peer_selection`, `track_peers`, `validate_block`.

Residual SCC, size 2: `mempool`, `tx_submission_responder` (unchanged; section 4).

Residual self-loop: `peer_selection → peer_selection [Resolved]`.

`chainsync_initiator` leaves the component. The credit and the Done-once flag delete every edge into its mailbox. `chainsync_initiator → track_peers` and `chainsync_initiator → mux` stay, and nothing in the size-12 component points back, so they are one-way. `ledger` leaves with the cell. The size-12 component is held together by manager, peer selection, the fetch/cleanup burst, the blockfetch initiator, and the connection teardown path. `7·N_max = 91 > 23` is why the Adversarial edges, and the Resolved self-loop that shares their mailbox, stay.

## 2. Manager mailboxes

Bulk capacity 23 at the defaults. Priority schedule capacity 10. `SendBudget` (`peer_selection/mod.rs:92-114`) limits one regulate round to `max_outbound + max_inbound` sends of `AddPeer`, `Disconnect`, and `SetLocalUse`. The round can run again as soon as those sends have been queued. `ban_peer` does not take a budget token.

| Kind | Mailbox | Sender | W now | W after the fixes |
| --- | --- | --- | --- | --- |
| `AddPeer` | bulk | `start_dial`, `peer_selection/mod.rs:359`, inside the budget | ≤ `max_outbound`. `using_occupancy` stops new dials at the upstream target. The arm at `:1219` has no production sender, so it adds 0 | same, ≤ `max_outbound` (3) |
| `RemovePeer` | bulk | `ban_peer`, `:339`, outside the budget | one per report that is not already cooling, and a peer can be reported again after the cooldown. Unbounded | ≤ `N_max`. The grow-only reported set emits one Adversarial per peer, and ban sends one `RemovePeer` for it |
| `Disconnect` | bulk | regulate, `:782` and `:945`, inside the budget | one per live `conn_id` until `disconnect_sent` clears, and ids are uncapped, so unbounded across cooldowns | ≤ `N_max` once each peer is reported once |
| `SetLocalUse` | bulk | regulate, `:466`, `:504`, `:894`, inside the budget | repeats while `wanted != applied`, after `LOCAL_USE_MIN_INTERVAL`. Unbounded | unbounded. The listed fixes do not stop a later round |
| `FetchBlocks` | bulk | `fetch_blocks/mod.rs:440` and `:544` | ≤ 4 messages per batch (the request plus three widens). A timeout clears `missing` and the next batch is sent without waiting for manager to drain. Unbounded | unbounded. No fetch credit in the fix list |
| `NewTip` | bulk | `adopt_chain/mod.rs:266` | one per adopted block. Unbounded | unbounded |
| `ConnectionResult` | bulk | `connector.rs:101` | ≤ `max_outbound`. Selection will not have more dials in flight than the upstream target, and the connector pool's own cap is 10 | same, ≤ `max_outbound` (3) |
| `Accepted` | bulk | `accept.rs:29` | unbounded. Accept mints the id and sends before `handshake_complete` applies `max_inbound` (`manager/mod.rs:537-540`, `accept.rs:27-29`) | ≤ `N_max`, from the cap before the mint |
| `HandshakeComplete` | bulk | `connection.rs:454`, a call | one per handshake in flight. Connections are uncapped, so unbounded | ≤ `N_max` |
| `Listen` | bulk | preload in `build_node` | 1 | 1 |
| `ConnectionDied` | priority tombstone | supervise, `manager/mod.rs:479`. Collected by `poll_with_ingress` (`tokio.rs:857-860`); `scheduled_pending` is not incremented | one per supervised connection exit. Unbounded while accept is uncapped | ≤ `N_max` |
| `Listen` | priority tombstone | the accept child, `manager/mod.rs:439` | ≤ 1 until manager processes it and wires accept again | ≤ 1 |
| scheduled priority | priority | manager has no `schedule_at` / `set_timeout` | 0 ≤ 10 | 0 ≤ 10 |

`HandshakeComplete`'s reply is a oneshot (`tokio.rs:712-718`). It is not a stage edge and it is not in the table above.

After the fixes, `Accepted` and `HandshakeComplete` for the same connection can both sit in the bulk mailbox while manager is parked, so those two kinds alone are ≤ `2·N_max = 26`, and 26 > 23. `RemovePeer` (≤ 13), `ConnectionResult` (≤ 3), and `Listen` (1) can sit with them. `FetchBlocks` and `NewTip` are still unbounded. No L1 discharge of an edge into manager.

The priority schedule itself fits. Tombstones are a different queue: the cap of 10 is the `schedule_at` panic, and a blocked manager can hold `N_max` `ConnectionDied` tombstones plus one `Listen` beside it.

### Resolved into peer selection

`eff.detach` at `peer_selection/mod.rs:664` returns immediately. One `Resolved` arrives when DNS finishes. `pending_resolve` is part of `using_occupancy` (`:410-411`) and is excluded from the next selection (`:634`). The round asks for `open = target_upstream_peers - occupancy` (`:619`). `select_outbound` allots at most `open` picks (`peer_mix.rs:159-196`, `select_outbound.rs:224-249`). Only an unresolved pick is detached, and it is inserted into `pending_resolve` first (`:661`). In-flight resolves are therefore ≤ `max_outbound`. Each produces one mailbox message, so

`W(Resolved) ≤ max_outbound`

which is 3 at the defaults. This bound holds in the current code. It does not L1-discharge the edge: the same mailbox also receives Adversarial, and after the grow-only set that is ≤ `7·N_max = 91`, and 91 > 23. The self-loop remains in both checker modes.

## 3. Chainsync initiator bulk mailbox

Capacity 14. The numbers below are the mailbox after the per-connection credit and the Done-once flag. `outstanding = RequestNext sent − RollForward/RollBackward dequeued`, and track_peers sends only while `outstanding < PIPELINE_DEPTH`, topping up on the recheck. `PIPELINE_DEPTH = 10`.

| Kind | Bound | Where it comes from |
| --- | --- | --- |
| `RequestNext` | ≤ 10 | the credit |
| `FromNetwork` | jointly with `RequestNext`, `R + F ≤ 11` | `IntersectFound` issues one extra `want_next` beside the wire `RequestNext(PIPELINE_DEPTH)` (`initiator.rs:314-318`). That wire message is one network message, not ten mailbox messages |
| `AwaitReply` | inside `F`, no extra term | `CanAwait` consumes the frame and issues one `want_next` (`initiator.rs:323`). Net zero against the credit. The frame occupies one bulk slot and is already counted in `F` |
| `RollForward` / `RollBackward` | inside `F` | they do not issue `want_next` (`initiator.rs:324-331`) |
| `Done` from connection | ≤ 1 | the stopping set (`connection.rs:571-594`) |
| `Done` from track_peers | ≤ 1 | the Done-once flag. The sends are `:911`, `:931`, `:1063` |
| `Registered` | ≤ 1, and not together with the pipeline | mux sends it once (`mux.rs:660`), and it is consumed before `want_next` |
| `Pull`, `Timeout` | 0 on this bulk mailbox | the initiator arms no priority mail, and these are not bulk producers |

A full credit (`R = 10`) leaves room for one network frame (`F ≤ 1`) plus the two `Done`s: `10 + 1 + 1 + 1 = 13`. `AwaitReply` does not add a fourteenth term. `Registered` is not simultaneous with that sum. `13 ≤ 14`.

That joint sum is why the three edges into this mailbox are L1-discharged in the `after` mode, and why `chainsync_initiator` leaves the size-12 component. The edge the other way, one header result per initiator into track_peers, is `W ≤ N_max = 13 > 10` and stays.

## 4. Mempool and the tx-submission responder

Classification only. No change is proposed. The size-2 component is the same in both modes. There is no `try_send` on any of these edges. `eff.try_send` is not used on a stage mailbox in the four protocol crates.

The call reply is a oneshot. `StageEffect::Call` builds `oneshot::channel` (`tokio.rs:766`) and a send whose `StageRef` carries that sender completes in `sender.send(msg)` without parking (`tokio.rs:712-718`). Admission is a separate wait: `await_call` parks on `tx.send` into the callee's mailbox until the deadline (`tokio.rs:623-647`). `NotAdmitted` means the deadline fired before the request was queued. `TimedOut` means it was queued and stays queued.

| Edge | Mechanism | Line | Against the four rules |
| --- | --- | --- | --- |
| responder → mempool `InsertBatch` | `eff.call`, parks the responder | `responder.rs:608-612`, timeout `ResponderParams::mempool_insert_timeout` (default 5s, `responder_params.rs:45-46`) | The responder blocks on admission while the mempool mailbox is full. The batch is that peer's `ReplyTxs`, so the wait is peer-dependent. On `None` the responder logs the timeout and terminates the connection (`:614-616`). This violates "never block on admission while the mempool is full". The reply half matches "a call with a oneshot reply": the result send at `mempool/stage.rs:99` is the oneshot and does not park the mempool. `TimedOut` leaves the `InsertBatch` queued |
| responder → mempool `SubscribeCapacity` | blocking `eff.send` | `responder.rs:692` | A blocking send, not a call and not a oneshot. `capacity_subscribed` keeps one outstanding subscription (`:682-691`). The caller stored by the mempool is `me_ref().contramap` onto the responder's own mailbox (`:687-689`). This is the edge that closes the cycle |
| mempool → responder `CapacityAvailable` | blocking `eff.send` of `()` | `mempool/stage.rs:193-196`, drained on `NewTip` when something was evicted (`:107-108`) | The payload is the fact that capacity exists, and the list is drained in one go, so a later wake replaces an earlier one. The message is superseding. The implementation is a blocking send into the responder mailbox, not a cell, so the superseding rule describes the value and the edge still waits. It is the back edge of the size-2 component |
| mempool → responder `InsertBatch` reply | oneshot | `mempool/stage.rs:99` | Not a blocking stage edge, so it is not in the SCC. This is the oneshot half of the admission rule |

`notify_ready_waiters` (`stage.rs:187`) sends to `WaitForAtLeast` callers. Those callers are the tx initiator (`initiator.rs:108`, `:355`, `:365`), not this responder. That pair is outside this component.

Ingress. The responder calls `want_next` only when it sends `RequestTxIds` or `RequestTxs` (`responder.rs:205`, `:231-240`). `req` is the window room capped by `max_reply_tx_ids` of the mux ingress (`:502-510`); the default window is `max_window = 10` (`responder_params.rs:36-37`). `txs_to_request` stops a body batch on mempool near-capacity, on `fetch_batch_bytes`, and on the ingress limit (`:553-556`). One reply frame is outstanding per `want_next` the responder itself issued, and that frame carries at most the count it asked for. The rule "ingress is bounded by the tx counts it requested" holds. `responder_params.rs:25-27` is the same bound already applied in those two caps. No L3 teardown is claimed, and this ingress edge is not one of the three blocking edges of the SCC.

## 5. Token leak

The state-indexed count is

```
T = [RecoverStoredBlocks queued]
  + [FetchNextFrom queued]
  + [select_chain.may_fetch_blocks]
  + [NewBestTip queued]
  + [fetch_blocks.missing.is_some()]
```

`may_fetch_blocks` starts false (`select_chain/mod.rs:116`). `Initialize` loads the best header and does not set it (`:164-171`). The only startup message on fetch_blocks is the preloaded `RecoverStoredBlocks` (`build_stage_graph.rs:199-204`). select_chain clears the flag immediately before each `NewBestTip` that comes from a better tip or a invalidated tip (`:302-305`, `:397-404`) and refuses a second `FetchNextFrom` while the flag is still false (`:443`).

### BoundaryNotFound

Confirmed. `find_missing_blocks` returns `BoundaryNotFound` when the ancestor walk from the tip header meets neither a header whose body is stored nor the anchor (`read_chain_store.rs:280-300`). The only caller is `request_missing_blocks`, which is only called from `new_tip` (`fetch_blocks/mod.rs:244`, `:345-353`).

`new_tip` runs because a `NewBestTip` was dequeued, so that term of `T` is already consumed. The assert at `:229` requires `missing` to be `None`. select_chain has already cleared `may_fetch_blocks`. The arm sets `missing = None` and returns. It does not send `FetchNextFrom`. It does not terminate. The stage function returns the state (`:827`) and the node keeps running. Every term is then 0.

A later header cannot restart the fetch. select_chain sends `NewBestTip` only while `may_fetch_blocks` is set, and the only production sender of `FetchNextFrom` is `fetch_next_from` (`:755-758`). The fresh-start fix sends that once at origin and does not cover this arm.

### Every other return of those handlers

| Handler | Return | `missing` afterwards | `FetchNextFrom` | Node | `T` |
| --- | --- | --- | --- | --- | --- |
| `NewTip` / `StartHeaderNotFound` | `terminate` (`:346-348`) | unchanged `None` | no | stops | shutdown |
| `NewTip` / `BoundaryNotFound` | `return` (`:350-353`) | `None` | no | keeps running | drops to 0 |
| `NewTip` / store error | `terminate` (`:356-358`) | unchanged | no | stops | shutdown |
| `NewTip` / `Found`, empty batch | `request_blocks` (`:382-407`) | set `None` at `:383` | yes, at `:396` or `:407` | keeps running | moves to `FetchNextFrom` |
| `NewTip` / empty batch, `has_block` error | `terminate` (`:399-401`) | already set `None` | no | stops | shutdown |
| `NewTip` / `Found`, non-empty | `request_blocks` (`:410-456`) | `Some` at `:421` | no | keeps running | moves to `missing` |
| `RecoverStoredBlocks`, ledger tip origin, stored tip not origin | `terminate` (`:265-268`) | unchanged `None` | no | stops | shutdown |
| `RecoverStoredBlocks`, origin to origin | `return` (`:265-270`) | unchanged `None` | no | keeps running | drops to 0. This is the startup token, and it is the hole the fresh-start `FetchNextFrom(Origin)` fills |
| `RecoverStoredBlocks`, broken chain, missing header, or `has_block` error | `terminate` (`:275-277`, `:280-286`, `:321-323`) | unchanged | no | stops | shutdown |
| `RecoverStoredBlocks` then `request_blocks` | the empty and non-empty rows above (`:332`) | `None` or `Some` | yes when the batch is empty | running, or shutdown on the `has_block` error | conserved, or shutdown |
| `Block`, decode failure | `return` (`:559-564`) | unchanged | no | running | unchanged |
| `Block`, body hash mismatch | `return` after Adversarial (`:570-582`) | unchanged | no | running | unchanged. The token stays in `missing` until timeout |
| `Block`, `missing` already `None` | `return` (`:585-588`) | `None` | no | running | the token is already in `FetchNextFrom` or later |
| `Block`, parent or point mismatch | `return` (`:607-623`) | unchanged | no | running | stays in `missing` |
| `Block`, `store_block` failure | `terminate` (`:628-633`) | still `Some` | no | stops | shutdown |
| `Block`, accepted, batch remains | falls through (`:643`) | still `Some` | no | running | stays in `missing` |
| `Block`, accepted, batch empty | `missing = None` then send (`:644-652`) | `None` | yes | running | moves to `FetchNextFrom` |
| `NoBlocks`, wrong id or `missing` is `None` | `return` (`:697-698`) | unchanged | no | running | unchanged |
| `NoBlocks`, recorded | `return` (`:700-707`) | stays `Some` | no | running | stays in `missing` |
| `Timeout`, wrong id | `return` (`:725-727`) | unchanged | no | running | unchanged |
| `Timeout`, `missing` is `None` | `None` arm (`:743`) | `None` | no | running | unchanged. The timeout is armed only after `missing = Some` (`:421`, `:454`). The completion path and the retry path cancel it and send `FetchNextFrom` in that same transition. A timeout already queued arrives later, and the token has already moved |
| `Timeout`, `missing` is `Some` | clear and send (`:744-750`) | `None` | yes | running | moves to `FetchNextFrom` |

`PeersAsked`, `NoPeersAvailable`, and `Widen` are not in the requested list. Each returns without clearing `missing` when the id is current (`:657-658`, `:710-711`, `:500-501`), and a stale id returns immediately. They do not send `FetchNextFrom`.

On the select_chain side, `handle_fetch_next_from` either sends one `NewBestTip` while leaving the flag false (`:446-482`) or sets the flag and sends nothing (`:483-489`). That replaces the `FetchNextFrom` term and does not create a second one. A `NewBestTip` produced there is the message that can later hit `BoundaryNotFound` and drop `T` to 0.

The L4 discharge of the `NewBestTip` edge still holds in both checker modes. The leak stalls the pipeline. It does not let `NewBestTip` and `FetchNextFrom` be in flight together: the flag is already false, and the `BoundaryNotFound` arm does not send.

## 6. The two block caps

`MAX_FETCHED_BLOCKS = 1000` (`blockfetch/responder.rs:44`). Both arms that start a range set the in-flight counter to that constant: the idle `Fetch` arm (`initiator.rs:275`) and the stashed-range arm (`initiator.rs:396`). Each streamed body decrements it (`:341`). A further body is rejected and the initiator terminates (`:335-336`). The server refuses a range that would contain more than 1000 blocks (`responder.rs:126-134`). So one block-fetch request accepts at most 1000 bodies, and the client will forward that many `Block` messages toward cleanup before `BatchDone`.

`MAX_MISSING_BLOCKS_PER_BATCH = 25` (`fetch_blocks/mod.rs:32`) is the consensus batch. `find_missing_blocks` is called with that limit (`:345`), and recovery truncates `to_fetch` to it (`:318`). The range passed to the manager is the first missing point through the last, so an in-range reply from a peer that serves exactly the requested points has length at most 25.

The two caps do not tighten each other. The initiator does not know about 25; it arms 1000 for every request, including a batch of 25. A peer can therefore deliver up to 1000 bodies on a request whose consensus batch named 25 points. cleanup forwards every decoded body with `id >= curr_id` (`fetch_blocks/mod.rs:876-880`) and moves `curr_id` to that id on the first such body, so the whole stream of the live id is forwarded. The mailbox occupancy of one live request is bounded by 1000 per asked peer, not by 25. With `MAX_FETCH_PEERS = 5` that is 5000, which is why the cleanup and fetch_blocks edges stay blocking after the `(req_id, missing)` cell and the explicit peer cap.
