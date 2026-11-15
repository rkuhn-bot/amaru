# Wait-graph inventory v3

Commit `33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6`. Read-only apart from `scripts/wait-graph-sccs.py` on `experiment/deadlock-chain-pipeline` of the rkuhn-bot fork. No pull request.

Edges are blocking `eff.send` / `eff.call` / `send_any` waits: the sender parks until a mailbox slot exists. A carried `StageRef` is an edge from the stage that sends to that ref to the stage that constructed it. `send_any` is included. Superseding is not claimed for any edge below.

Mailbox sizes used below: chainsync initiator bulk 14 (`PIPELINE_DEPTH + 4`, `chainsync/mod.rs:27–33`); default bulk 10 (`types.rs:53`); manager and peer_selection `10 + upstream + downstream` = 23 at the defaults 3 and 10 (`build_stage_graph.rs:71–91`, `amaru-node/src/lib.rs:97–99`). A child created with `eff.stage` takes the parent effect's mailbox size, which for manager-spawned stages is the graph default 10, not 23 (`effect.rs:567–601`). `cleanup_replies` is created that way from `fetch_blocks` and is 10.

## (A) One chainsync initiator bulk mailbox, under the proposed credit

The credit is not in the tree. The accounting assumes it: `outstanding_i` is RequestNext sends completed minus RollForward/RollBackward results dequeued by `track_peers`, a send happens only while `outstanding_i < PIPELINE_DEPTH` (10), and `recheck_deferred` tops up to that same depth instead of one RequestNext per released header. The ceiling on RequestNext is therefore 10. The wire `RequestNext(PIPELINE_DEPTH)` inside `IntersectFound` (`initiator.rs:315`) is one network message, not ten local mailbox messages.

| Kind | Bound | Why |
| --- | --- | --- |
| `Inputs::Local(RequestNext)` | ≤ 10 | Every queued RequestNext has been sent and not yet dequeued, so it is still inside `outstanding_i`. |
| `Inputs::Network(FromNetwork)` | ≤ 11 alone; jointly with RequestNext, `R + F ≤ 11` | A `FromNetwork` is delivered only for an unmatched `want_next` (`mux.rs:842–847`, `:852–862`). `want_next` is issued once on `IntersectFound` (`initiator.rs:316`) and once per local RequestNext the initiator has already dequeued (`:343–348`). `AwaitReply` consumes one frame and issues one `want_next` (`:323`), net zero. RollForward/RollBackward do not issue `want_next` (`:324–331`). Frames still queued plus RequestNext still queued are at most the outstanding credit plus that one intersect credit. |
| `Inputs::Local(Done)` from connection | ≤ 1 | `begin_stop` sends one Done and records `ChildId::ChainSync` (`connection.rs:593–594`). `converge_use` returns while `stopping` is non-empty (`:571–572`), so a second Done is not sent until the first stop has finished. |
| `Inputs::Local(Done)` from `track_peers` | not capped at 1 | Sites `:911` (unknown intersection, does not purge), `:931`, `:1063`. Each arm sends one. The initiator can already have queued several results in `track_peers` (mailbox 10) before `track_peers` runs, and `track_peers` can turn more than one of them into a Done before the initiator dequeues the first. |
| `Inputs::Network(Registered)` | ≤ 1, and not together with a live pipeline | Sent once at register (`mux.rs:660`). The initiator has to run, consuming it, before it issues `want_next` or `track_peers` is asked for RequestNext. |
| `Inputs::Internal(Pull)`, `Internal::Timeout` | 0 | Chainsync uses `miniprotocol`, not `protocol/pipeline.rs`. Neither the initiator nor `miniprotocol` calls `set_timeout` or injects `Pull`. |

Priority mailbox of this stage: nothing is scheduled. No `schedule_at`, no `set_timeout`, and the initiator supervises no child, so no tombstone is delivered here. Bound 0. (`RecheckLedgerHeight` is scheduled on `track_peers`, `track_peers/mod.rs:706`.)

The joint occupancy the credit actually gives is `R + F + Done_connection + Done_track_peers ≤ 11 + 1 + Done_track_peers`, with Registered already consumed. That is ≤ 14 only while `Done_track_peers ≤ 2`. The code does not keep `Done_track_peers` that small. The proposed credit does not show this mailbox sufficient at 14.

Re-initializing the same stage (`track_peers/mod.rs:892–898` purges `track_peers` state and does not drain the initiator) can issue another intersect `want_next` on top of frames already queued, so the `+ 1` is a single-session figure.

## (B) Reliable blocking outputs of `recheck_deferred` and header handling

`recheck_deferred` (`track_peers/mod.rs:1085–1120`) only sends by calling `try_roll_forward`. That function's sends:

| Line | Receiver | Message |
| --- | --- | --- |
| 786 | `peer_selection` | `Adversarial` |
| 868 | `select_chain` | `NewTip` |
| 877 | chainsync initiator `handler` | `RequestNext` |

Header handling adds these, which recheck does not send (the height-ok path sets `sent_request_next` so recheck will not send a second RequestNext):

| Line | Receiver | Message |
| --- | --- | --- |
| 911, 931, 1063 | initiator | `Done` |
| 960, 1071 | `peer_selection` | `Adversarial` |
| 1015, 1049, 1069 | initiator | `RequestNext` |

`StakeDistUpdated` and `RecheckLedgerHeight` only call `recheck_deferred`. `VolatileTipEffect` is an external effect.

Return paths:

- Chainsync initiator. Direct. Every protocol result is sent to `track_peers` (`initiator.rs:169–172`). RequestNext and Done both sit in a stage with that edge. This is cycle (c).
- `select_chain`. Its only blocking sends are `NewBestTip` to `fetch_blocks` (`select_chain/mod.rs:305`, `:400`, `:478`), and only while answering the `may_fetch_blocks` token (`:302–305`, `:397–404`, assert at `:443`). That edge is treated as discharged. No other `eff.send` exists in the stage, so nothing remains that leads back to `track_peers`.
- `peer_selection`. Yes. `Adversarial` calls `ban_peer`, which sends `RemovePeer` (`peer_selection/mod.rs:339`). `manager.remove_peer` sends `ConnectionMessage::Disconnect` (`manager/mod.rs:626`, and `disconnect_live` at `:946`). `connection` on `Disconnect` calls `teardown` (`connection.rs:216–217`), which sends `InitiatorResult::Terminated` to `track_peers` (`:319–329`). The same stage also sends `Disconnect` (`:782`, `:945`) along that path, and `SetLocalUse` (`:466`, `:504`, `:894`), after which the initiator's results arrive at `track_peers` on `:169`.

## (C) `FetchNextFrom` sites, and termination

`fetch_next_from` is `:755–758`. Call sites are only 396, 407, 652, 750.

| Site | Transition | Consumes the token? |
| --- | --- | --- |
| 396, 407 | `request_blocks`, called only from `new_tip` (`:244`, the `NewTip` arm at `:815`) and `recover_stored_blocks` (`:332`, the `RecoverStoredBlocks` arm at `:816`). | Yes. Both are the NewBestTip transition or the startup Recover injection. The empty-batch arm sets `missing = None` at `:383` before the send. `new_tip` and `recover` already assert `missing` is `None` (`:229`, `:256`). |
| 652 | `block`, after the batch becomes empty. | The same transition sets `missing` from `Some` to `None` at `:645`. `:585` returns first when `missing` is already `None`, so this send only runs on that edge. |
| 750 | `timeout`, in the `Some(from)` arm. | The same transition sets `missing = None` at `:746`. The `None` arm does not send. |

`BoundaryNotFound` (`:350–353`) clears `missing` and returns without `FetchNextFrom`. It is not one of the four sites. It runs from `request_missing_blocks` while `missing` was already `None`, so it does not close an open batch; it also does not give the token back.

`or_terminate` / `or_terminate_with` log and then `eff.terminate()` (`types.rs:386–390`). `terminate` never resolves (`effect.rs:535–553`). `select_chain` and `fetch_blocks` are wired in `build_stage_graph` before the graph runs, so their tasks carry the root `DropGuard` that sets the graph termination flag (`tokio.rs:322–328`). The runtime then aborts every stage (`tokio.rs:200–205`). `run.rs:536–547` records `CONSENSUS_DIED` and cancels the process; after shutdown, `:576–577` returns the error `consensus stage graph terminated unexpectedly`. In the simulation a top-level terminate sets the simulation flag and returns `Blocked::Terminated` (`simulation/running/mod.rs:1437–1443`).

`select_chain` sites: `:227` tip header missing; `:332` validation-target header missing; `:338` `set_block_valid` failed; `:375` best-candidate header missing after `FindBestCandidate`; `:417` `FindBestCandidate` failed; `:452` best header missing on `FetchNextFrom`; `:459` its parent point missing; `:518` `load_parent_point` parent missing.

`fetch_blocks` sites: `:268` origin ledger tip with a non-origin stored candidate; `:277` broken ancestor chain; `:283` recovery tip header missing; `:323` `has_block` failed during replay; `:348` start header not found; `:358` `find_missing_blocks` failed; `:401` `has_block` failed on the empty-batch path; `:630` `store_block` failed.

## (D) Announced stake-distribution epochs

Announced epochs do not decrease, and rollback does not retract them. The distributions that are announced are computed from a historical snapshot, and the callback runs only after the stability window.

`rotate_stake_distribution` (`state.rs:1269–1291`) is the only notifier. `BackgroundTasks::run` calls it only when `rotation` is `Some` (`:1259`). `try_compute_rewards` (`:530–548`) builds that rotation only when the held front is missing or strictly older than `previous_epoch`, and it starts the task only when `most_recent_snapshot() == current_epoch - 1` and `slot_in_epoch(tip) >= stability_window`. `previous_epoch` is `snapshots.for_epoch(current_epoch - 1)` (`:541`). That snapshot is the historical store written by `next_snapshot` at the epoch boundary (`state/volatile/overlay.rs:280`), not the volatile fragment.

`install_stake_distribution` (`:576–579`) pushes only when the new epoch is strictly greater than the front, then keeps two. `rollback_to` (`:1032–1065`) rewrites only the volatile DB and refuses a target older than the immutable tip. It does not touch `stake_distributions` and does not call the callback. After the stability window the epoch boundary is at or behind the immutable tip, so a rollback cannot un-cross it. A fork switch that re-crosses a boundary finds `front.epoch >= previous_epoch.epoch()` and skips the rotation (`:545–546`).

`PoolSummaries::max_epoch` is the greatest key (`has_stake_distribution/mod.rs:59–60`). The announced map is the retained front plus the new distribution, and the new epoch is strictly greater than that front, so the announced maximum moves forward. Nothing on the rollback path removes a key.

## (E) Cycle (g): fetch_blocks → manager → cleanup_replies → fetch_blocks

The three edges exist and are blocking.

| Edge | Producers and bound | Capacity | Fits? |
| --- | --- | --- | --- |
| `fetch_blocks` → manager, `FetchBlocks` (`:440`, `:544`) | Only `fetch_blocks`. One initial send plus at most three widens (`FETCH_WIDEN_DELAYS`, `:40–41`), one armed at a time (`:459–468`). While the stage is parked on one send it does not produce the next. At most four messages from this producer. | manager 23 | This producer alone fits. The mailbox is shared. |
| manager → `cleanup_replies`, `PeersAsked` or `NoPeersAvailable` (`:795`, `:798`) | See below: exactly one of those two per `FetchBlocks` the manager finishes. Other producers of the same mailbox are the blockfetch initiators, `send_any` of `Block`, `NoBlocks`, and `Done` (`initiator.rs:312`, `:348`, `:364`). Each in-flight range accepts up to `MAX_FETCHED_BLOCKS` (1000, `responder.rs:44`) blocks. | `cleanup_replies` 10 | No. |
| `cleanup_replies` → `fetch_blocks`, forwarded `Block` / `NoBlocks` / `PeersAsked` / `NoPeersAvailable` (`:855–877`) | One forward per collector message that passes the id check (NoPeersAvailable is always forwarded). The block term is the same per-peer burst. | `fetch_blocks` 10 | No. |

No state invariant keeps the three sends from being parked together. The `may_fetch_blocks` token does not cover any of these edges. A workable interleaving: manager is inside an earlier `FetchBlocks`, has finished the per-connection sends, and blocks on the `cr` send because `cleanup_replies` is blocked forwarding to `fetch_blocks`; `fetch_blocks` has since taken a widen or a later batch and blocks on the next `FetchBlocks` because other producers (`peer_selection`'s `RemovePeer` among them) have filled manager. `fetch_blocks` being inside the send is what stops it draining, which is what lets `cleanup_replies` fill it.

`manager.fetch_blocks` can also park earlier, on a `ConnectionMessage::FetchBlocks` send (`:776`, `:789`). That is a different wait. It does not stop the `cr` send from being the one that parks once those connection sends have completed.

### How many `PeersAsked` / `NoPeersAvailable` per `FetchBlocks`

Exactly one. `contacted.is_empty()` sends `NoPeersAvailable` (`:793–795`); otherwise one `PeersAsked` carrying the whole peer list (`:796–798`). Not one message per peer. Each widen is another `FetchBlocks` and therefore another single reply, still for the same `req_id` (`fetch_blocks/mod.rs:549`).

### Cap A

On the `peers: Some` path, the first request asks at most `MAX_FETCH_PEERS` (5) (`:426`), and each widen asks at most the remaining room up to 5 (`:509–510`). That path is bounded by 5.

On the `peers: None` path (weak or empty selection, `:431–433`), manager asks every connection in `may_initiate()` (`manager/mod.rs:767–777`). That function is every live connection whose recorded `local_use` is `Diffusion` (`performance/peers/connections.rs:150–155`). There is no `MAX_FETCH_PEERS` check on this loop.

`Diffusion` is not the whole inbound population. Outbound handshakes are stored as `Diffusion` (`manager/mod.rs:906–909`). Inbound handshakes are stored as `None`. `peer_selection` stops dialing and stops promoting when `using_occupancy() >= target_upstream_peers` (`peer_selection/mod.rs:493–494`, `:614–617`). The default target is `DEFAULT_PEERS_MAX_UPSTREAM` = 3. So the broadcast set is the diffusion set, which selection holds to that target, and the fetch code itself will ask all of them. Raising `peers_max_upstream` raises Cap A. Cap A is not 5.

### Cap K

A new `req_id` does not wait for a `Block` or a `Done`. `request_blocks` increments `req_id` (`fetch_blocks/mod.rs:412`) from `new_tip` or from the end of recovery. The next batch starts once `missing` is `None`, which timeout (`:746`) and the empty-batch path do before `FetchNextFrom`. `cleanup_replies` advances `curr_id` only on `Block` (`:880`, `id.max`) and `Done` (`:884`, `(id + 1).max`). `PeersAsked`, `NoBlocks`, and `NoPeersAvailable` do not move it. Until the first `Block` or `Done`, `curr_id` stays 0 and `id >= curr_id` is true for every id, so old and new replies are both forwarded.

`fetch_blocks` itself has one current id. Each blockfetch initiator has one in-flight range and overwrites a single stashed range (`initiator.rs:324`, `:376`). A peer therefore still produces collector messages for at most two ids. Distinct ids still producing across peers are at most two per asked initiator. The asked set on the broadcast path is the diffusion set from Cap A. Nothing smaller stops `fetch_blocks` from issuing the next id.

## (g′) cleanup_replies → block_source → peer_selection → manager → cleanup_replies

Real as a wait-graph cycle. The last edge is the carried `cr` and is taken only while manager is handling `FetchBlocks`. A `RemovePeer` from `peer_selection` does not itself send to `cr`. The cycle is simultaneous parking, not one message travelling the whole loop.

| Edge | Bound | Capacity | Fits? |
| --- | --- | --- | --- |
| `cleanup_replies` → `block_source`, `BlockReceived` (`:875`) | One per decoded `Block`. Same burst as Cap A times up to 1000 blocks per in-flight range. `Validation` (`validate_block/mod.rs:117`, `:149`) and `AdoptedTip` (`adopt_chain/mod.rs:268`) share this mailbox. | `block_source` 10 | No. |
| `block_source` → `peer_selection`, `Adversarial` | `:128` sends again on every later `BlockReceived` for a point already marked invalid. `:152` sends once per peer in the pending set for that point; the set is a `BTreeSet`, so one inclusion per peer. Not every `BlockReceived` sends. | peer_selection 23 | No hard producer cap at 23. |
| `peer_selection` → manager | One `RemovePeer` per ban (`:339`). See (G4). | manager 23 | A single regulate round fits in the `U + D` slots only while those slots are empty. |
| manager → `cleanup_replies` | One `PeersAsked` or one `NoPeersAvailable` per `FetchBlocks`, plus the block burst from initiators sharing the mailbox. | 10 | No. |

Nothing in these four transitions forbids all four sends being parked at once. `block_source` parks on `:128` or `:152` only when it is reporting an invalid block, so the cycle needs that report to be in progress while manager is inside `fetch_blocks()` and `cleanup_replies` is inside the `BlockReceived` send. Those are independent messages. No token ties them.

## (F) Cycle (h): track_peers → peer_selection → manager → connection → track_peers

Real. `Terminated` is `connection.rs:320–328`, reached from `teardown` (`:309–316`) on `Disconnect` (`:216–217`).

| Edge | Bound | Capacity | Fits? |
| --- | --- | --- | --- |
| `track_peers` → `peer_selection`, `Adversarial` | One per failing header (`:786`, `:960`, `:1071`). No per-connection credit. `peer_selection` drops a repeat only after the message has been dequeued and the peer is already cooling (`:1206–1208`). | 23 | No. |
| `peer_selection` → manager, `RemovePeer` | One per peer that is not already cooling. | 23 | See (G4). |
| manager → connection, `Disconnect` | One per `RemovePeer` / `Disconnect` for that id (`:844`, `:946`). The same mailbox also receives `FetchBlocks`, `NewTip`, `SetLocalUse`, `Initialize`. | connection 10 | `NewTip` is one per adopted tip (`manager/mod.rs:866`) and is not collapsed. Not shown ≤ 10. |
| connection → `track_peers`, `Terminated` | One per teardown of a connection that has a chainsync initiator. The mailbox is shared with every initiator's results (`initiator.rs:169`), which are one per header and are not capped by `PIPELINE_DEPTH` in `track_peers`. | `track_peers` 10 | The one `Terminated` needs a slot the header stream is not required to leave free. |

No invariant stops the four parks. Connection sends `Terminated` and then `terminate`s; it can sit on that send while other initiators fill `track_peers`, `track_peers` sits on an `Adversarial` for a different peer, `peer_selection` sits on `RemovePeer`, and manager sits on `Disconnect` to a connection whose mailbox is full.

## (G1) StageRef fields

For each message type that carries a `StageRef`, the edge is from the stage that sends to the ref to the stage that constructed it.

| Message and field | Constructed by | Sent to by | Edge |
| --- | --- | --- | --- |
| `ManagerMessage::FetchBlocks.cr` | `fetch_blocks`, the `cleanup_replies` child | manager `:795`, `:798` | manager → `cleanup_replies` |
| `ConnectionMessage::FetchBlocks.cr`, `BlockFetchMessage::RequestRange.cr`, `Fetch.cr` | the same ref, forwarded | blockfetch initiator `send_any` | initiator → `cleanup_replies` |
| `ChainSyncInitiatorMsg.handler` | chainsync initiator `eff.me_ref` (`initiator.rs:150`) | `track_peers` RequestNext/Done | `track_peers` → initiator |
| `MuxMessage::Register.handler` | the protocol stage being registered | mux `:660`, `:846`, `:858` | mux → that protocol |
| `MuxMessage::Send`'s `StageRef<Sent>` | the `eff.call` site | mux `:881` | mux → the caller's reply |
| `HandshakeComplete.caller` | connection's call (`connection.rs:454`) | manager `:519`, `:525`, `:551`, `:560`, `:564` | manager → connection |
| `HandshakeComplete.stage` | the connection stage | manager's later sends (`Disconnect`, `FetchBlocks`, `NewTip`, `SetLocalUse`) | manager → connection |
| `ConnectorMsg::WorkerDone.worker` | the connect worker `eff.me` (`connector.rs:124`) | connector `:74`, `:81` on the next job | connector → that worker |
| `MempoolMsg::{SubscribeCapacity, Insert, InsertBatch, WaitForAtLeast}.caller` | tx-submission responder. `capacity_callback` is `me_ref().contramap` (`responder.rs:687–692`) | mempool `:70`, `:85`, `:99`, `:187`, `:195` | mempool → tx-submission responder |

## (G2) `send_any`

Production `send_any` is only the three blockfetch collector sends (`initiator.rs:312` `NoBlocks`, `:348` `Block`, `:364` `Done`). The target is `flight.cr`, the carried `cleanup_replies` ref. All three are blocking. The pure-stage UI test is not a node edge.

## (G3) SCCs

`scripts/wait-graph-sccs.py` reads `wait-graph-v3.json` and prints components of more than one stage. On this edge list (40 blocking edges):

One component of 16: `accept`, `adopt_chain`, `block_source`, `blockfetch_initiator`, `chainsync_initiator`, `cleanup_replies`, `connect_worker`, `connection`, `connector`, `fetch_blocks`, `manager`, `mux`, `peer_selection`, `select_chain`, `track_peers`, `validate_block`.

One component of 2: `mempool`, `tx_submission_responder`.

Dropping the discharged `NewBestTip` edge removes `select_chain` and leaves a component of 15. Cycles (g), (g′), (h), and (c) do not need `select_chain`. The token discharges the select/fetch cycle and does not split the rest. The carried `cr` edge is what joins fetch, cleanup, block source, and peer selection into the same component as the disconnect path.

## (G4) peer_selection → manager, and the way back

A regulate round sends at most `target_upstream_peers + target_downstream_peers` manager commands (`SendBudget`, `peer_selection/mod.rs:92–114`, default 13). That is the bound the 23-slot mailbox comment describes, and it holds for `AddPeer`, `Disconnect`, and `SetLocalUse` made through `budget.send`.

`ban_peer` does not use the budget. Each `Adversarial` for a peer that is not cooling sends one `RemovePeer` (`:339`) and then sets the cooldown. Repeats while cooling do not send (`:1206–1208`). There is no numeric cap on how many distinct peers can be banned while manager is not draining. Those `RemovePeer`s are extra on top of the regulate budget and on top of `FetchBlocks`, `Accepted`, `ConnectionResult`, and `NewTip`. peer_selection → manager is not bounded by the mailbox.

Manager never sends `PeerSelectionMsg`. It does have a blocking path back. `FetchBlocks` to a connection (`:776`, `:789`) is delivered to the blockfetch initiator (`connection.rs:252`); `send_any` of a `Block` reaches `cleanup_replies`; a header that fails to decode sends `Adversarial` (`fetch_blocks/mod.rs:871`), and a decoded block sends `BlockReceived` (`:875`) which `block_source` can turn into `Adversarial` (`:128`, `:152`). `PeersAsked` / `NoPeersAvailable` do not continue to `peer_selection`. `Disconnect` continues to `track_peers` as `Terminated`, not to `peer_selection`.

## (G5) Every `Adversarial` send

| Site | When | Deduped per connection at the send? |
| --- | --- | --- |
| `track_peers/mod.rs:786` | Header validation failed in `try_roll_forward`. | No. One per failure. The connection is purged after the send. |
| `track_peers/mod.rs:960` | RollForward body did not decode. | No. |
| `track_peers/mod.rs:1071` | RollBackward failed for a reason other than an unknown point. A RequestNext is sent first (`:1069`). | No. |
| `fetch_blocks/mod.rs:574` | Block body hash does not match the header. Runs before the `missing` check (`:585`), so a straggler still sends. | No. |
| `fetch_blocks/mod.rs:871` | `cleanup_replies` could not decode the header. | No. |
| `block_source/mod.rs:128` | `BlockReceived` for a point already marked invalid. | No. Every such message sends again. |
| `block_source/mod.rs:152` | Validation failed. One send per peer in the pending set. | The set inserts each peer once (`:131`), so one send per peer per invalidation of that point. Not per connection, and not across points. |

The receive side in `peer_selection` (`:1206–1208`) ignores a report for a peer that is already cooling. That drops the effect after the mailbox slot has been taken. It is per peer, not per connection.

## (H1) Producers into `peer_selection`

Bulk mailbox (23 at the defaults):

| Kind | Sender | Line | Deduped per connection? |
| --- | --- | --- | --- |
| `Initialize` | preload in `build_stage_graph` | `build_stage_graph.rs:231` | Once at startup. |
| `Adversarial` | `track_peers` | `:786`, `:960`, `:1071` | No. |
| `Adversarial` | `fetch_blocks` | `:574` | No. |
| `Adversarial` | `cleanup_replies` | `:871` | No. |
| `Adversarial` | `block_source` | `:128` | No. Repeats for the same peer and point. |
| `Adversarial` | `block_source` | `:152` | One per peer in the pending set for that point. The fan-out is the whole set. |
| `Resolved` | `peer_selection` itself, via `detach` | `:664` | One per DNS candidate, not per connection. |
| `AddPeer` | none in production | the arm is `:1214` | The comment says the variant is mostly for testing. No production sender. |

Priority, not bulk: `Tick`, one armed `set_timeout` (`:1068`). `ledger-check` does not send back (`:1297–1298`).

## (H2) Connection caps

There is no single cap on the number of connections.

Inbound bearers kept after handshake: `max_inbound`, default `DEFAULT_MAX_INBOUND` = 10 (`manager/mod.rs:276–277`). The node sets it from `target_downstream_peers` (`build_stage_graph.rs:99`), whose default is `DEFAULT_PEERS_MAX_DOWNSTREAM` = 10. The check is `handshake_complete` (`manager/mod.rs:537–540`): a new inbound peer is refused when live inbound peers already reach `max_inbound`. `accept` (`accept.rs:27–29`) does not consult the cap. It allocates a `conn_id` and starts a connection stage first; refusal happens later and sends `Disconnect`.

Initiating connections, the set Cap A iterates: not a constant in `manager.fetch_blocks`. It is `may_initiate()`, the connections whose `local_use` is `Diffusion`. Selection holds the diffusion occupancy to `target_upstream_peers` (default `DEFAULT_PEERS_MAX_UPSTREAM` = 3) by refusing further dials and promotions (`peer_selection/mod.rs:493–494`, `:614–617`). Outbound handshakes start as `Diffusion` (`manager/mod.rs:906–909`) before selection can demote them, so the set can briefly include a bearer whose demotion has not been applied. The fetch loop does not enforce either target.

Pending accepts plus live inbound plus outbound can exceed `max_inbound + target_upstream_peers`.

## (H3) Where `conn_id`s come from

The id is minted in the network resource, `Connections::add_connection` (`amaru-network/src/connection.rs:79–82`), on `connect` (`:207`) and on `accept` (`:304`). Production callers of those two operations are the connect worker (`connector.rs:123`) and the accept stage (`accept.rs:27`). The id then enters the manager as `ConnectionResult` (`connector.rs:101`) or `Accepted` (`accept.rs:29`). `AddPeer` from `peer_selection` is what causes the outbound dial; it does not contain the id. Manager does not mint ids, and no other production stage does.

## Obligation (1), with manager → cleanup_replies included

`peer_selection` and `block_source` still do not send `FetchBlocks`, and manager sends to `cr` only inside `fetch_blocks()` (`:757–799`). A message that starts at either stage does not travel manager → `cleanup_replies`.

The static graph is a different statement. Because that edge is in the graph, both stages reach `fetch_blocks`: `peer_selection` → manager → `cleanup_replies` → `fetch_blocks`, and `block_source` → `peer_selection` along the same hops. They also reach `track_peers` by `RemovePeer` → `Disconnect` → `Terminated`, and from `track_peers` the `NewTip` edge reaches `select_chain`. `Initialize` on that path does not emit `NewTip`; a later header result does. The token still discharges `select_chain` → `fetch_blocks`. It does not discharge (g), (g′), or (h).
