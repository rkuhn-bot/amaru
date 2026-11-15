# Wait-graph inventory, pass 5

Tree: `33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6`. The graph is `scripts/wait-graph-v5.json`. The discharge table is `scripts/wait-graph-v5-discharge.json`. Both are emitted by `scripts/extract_wait_graph_v5.py`, which is the classification of every production `eff.send`, `eff.call`, `.send_any`, and typestate `session.send` under `crates/`, tests left out, plus every `StageRef` those messages carry and the submit API's `Sender::call`.

A call reply and a mux `Sent` reply complete through `oneshot::send` (`tokio.rs:712-718`). Those are in the JSON with `blocking: false` and are not edges the checker walks. Per-connection protocols are one node each; every live connection repeats that shape.

## Mailboxes

`stage_with_mailbox_size` on the graph builder sets that stage's own queue, and the `Effects` it runs with keep the builder's default of 10 (`tokio.rs:286`). A child created with `eff.stage` therefore has a bulk mailbox of 10 even when its parent is manager or peer selection, whose own mailboxes are `10 + max_outbound + max_inbound` (23 at the defaults). Explicit exceptions: mux 24, chainsync initiator 14, blockfetch initiator `max(10, 2n+4)`.

`N_max = max_inbound + max_outbound` is 13 at the defaults.

## Stages left out

| Stage | Reason |
| --- | --- |
| `mithril_block_source` and its validate/adopt wiring | built by the mithril sync command, not by `build_node` |
| pure-stage tests, simulations, and the world injector | not in the node graph |
| `FindBestCandidate` and the store's anchor read | external effects on the chain store. The anchor cell in the fix set therefore deletes no edge |

`ledger_check` is in the graph. It receives one bulk `()` from peer selection and then wakes itself on the priority mailbox. `forge_block` is in the graph; `build_stage_graph` wires it only when forging credentials are set. The submit API is not a stage. Its HTTP handler calls into the mempool, and that call is an edge.

## Diff against v4

v4 has 43 blocking edges. v5 has 78. Every v4 blocking key is still present. v5 adds 35, which is the hole v4 left:

- `tx_submission_initiator → mempool` `WaitForAtLeast` (`initiator.rs:107`, `:365`) and the reverse `WaitForAtLeastReached` (`mempool/stage.rs:70`, `:187`)
- `submit_api → mempool` `Insert` (`submit_api.rs:85`)
- handshake, chainsync responder, blockfetch responder, keepalive, peer sharing, and the tx initiator, each both ways with the mux
- `mux_reader` and `mux_writer`
- `done_trap`
- `connection → chainsync_responder` `NewTip` (`connection.rs:258`)
- `connection → mux` `Register` / `SetSduTimeout`
- `Close` from connection to the tx, keepalive, and peer-sharing initiators
- `handshake → connection` `HandshakeResult`
- `peer_selection → ledger_check`
- `forge_block → select_chain` `TipFromUpstream` (`forge_block/protocol.rs:455`) and `adopt_chain → forge_block` `AdoptedTip`

v4's `now` component of 14 was the consensus core plus the chainsync initiator. With the protocol stages linked through the mux and the connection, `now` is one component of 24, plus the `Resolved` self-loop. `select_chain`, `accept`, `connect_worker`, `mux_reader`, `mux_writer`, `done_trap`, `ledger_check`, `forge_block`, and `submit_api` sit outside it because the edge that would return to them is either discharged or a oneshot.

## The fix set, and what it discharges

| Fix | What it does to the graph | Checker |
| --- | --- | --- |
| B1, Adversarial dedup per `conn_id` | one report per connection, so the seven sites together are ≤ `N_max`. With `Resolved` ≤ `max_outbound` and one `Initialize`, the peer-selection sum is 17 ≤ 23 | discharges every edge into peer selection, including the self-loop |
| B2, cells for `SetLocalUse`, `NewTip`, `FetchBlocks` into manager | those three kinds become one slot each. The remaining reliable kinds are `AddPeer` ≤ `max_outbound`, `RemovePeer` ≤ `N_max`, `Disconnect` ≤ `N_max`, `HandshakeComplete` ≤ `N_max`, `Accepted` ≤ `N_max`, `ConnectionResult` ≤ `max_outbound`, `Listen` = 1, and the three cells. Sum `4·N_max + 2·max_outbound + 4` = 62 > 23 | no edge into manager is discharged |
| B3, the same cells on each connection | bulk kinds are `Initialize`, `Disconnect`, `HandshakeResult`, and one cell each for `FetchBlocks`, `NewTip`, `SetLocalUse`. Sum 6 ≤ 10 | discharges `manager → connection` and `handshake → connection` |
| B4, delete `SubscribeCapacity` and `CapacityAvailable` | those two sends are gone; capacity is a cell. What remains into the mempool is one parked `InsertBatch` per inbound responder (≤ `max_inbound`), `L` in-flight submit calls, and one `NewTip`. `L` is not capped by the HTTP server. Sum `max_inbound + L + 1` ≥ 11 > 10 | the two deleted edges go; `InsertBatch`, `Insert`, and `NewTip` stay |
| B5, blockfetch pending range becomes a cell | initiator bulk sum 4 ≤ 10 | discharges both edges into the blockfetch initiator |
| B6, cleanup forwards a hash only when it is in `missing` and not yet forwarded | the surviving occupancy is 67 > 10 | `cleanup_replies → fetch_blocks` stays |
| `WaitForAtLeast` becomes a monotone sequence cell | both the send and the notification are deleted | both edges discharged |
| anchor via a cell | the anchor is already a store effect | no edge |
| fetch-permission token | already in the code | `NewBestTip` discharged in both modes |
| RequestNext credit and Done-once | joint initiator sum 13 ≤ 14, `AwaitReply` counted inside the one network frame | discharges the three edges into the chainsync initiator |
| cap at accept, before the id is minted | supplies `N_max` for the sums above | `Accepted` stays, because 62 > 23 |

The stake callback is not in this fix set. Both directions stay.

`now` discharges 6 edges and exits 1. `after` discharges 22 and exits 1.

### now

One component of 24: `adopt_chain`, `block_source`, `blockfetch_initiator`, `blockfetch_responder`, `chainsync_initiator`, `chainsync_responder`, `cleanup_replies`, `connection`, `connector`, `fetch_blocks`, `handshake`, `keepalive_initiator`, `keepalive_responder`, `ledger`, `manager`, `mempool`, `mux`, `peer_selection`, `peer_sharing_initiator`, `peer_sharing_responder`, `track_peers`, `tx_submission_initiator`, `tx_submission_responder`, `validate_block`.

Self-loop: `peer_selection → peer_selection` `Resolved`.

### after

Component of 10: `mux` with `handshake`, `chainsync_responder`, `blockfetch_responder`, `tx_submission_initiator`, `tx_submission_responder`, `keepalive_initiator`, `keepalive_responder`, `peer_sharing_initiator`, `peer_sharing_responder`. Each still has `WantNext`/`Send` into the mux and `Registered`/`FromNetwork` back. The chainsync and blockfetch initiators leave, because their inbound mux edge is discharged and nothing in this component points at them.

Component of 6: `fetch_blocks`, `cleanup_replies`, `manager`, `connector`, `validate_block`, `adopt_chain`. B2 and B6 do not bring those mailboxes under capacity, so `FetchBlocks`, `NewTip`, `PeersAsked`, the filtered block forward, `DownloadedBlock`, and `AdoptChain` still close it. `Connect` and `ConnectionResult` keep the connector inside.

Component of 2: `ledger`, `track_peers`.

No blocking self-loop remains. `peer_selection` becomes a source: its only remaining edge is into manager, and B1 removed every edge back.

## Edges that still block after the fixes

56 edges. A line cited from `miniprotocol.rs` is the shared send/call every framework protocol uses; the blockfetch lines are that protocol's own calls.

| Edge | Lines |
| --- | --- |
| `handshake → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → handshake` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `chainsync_initiator → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `chainsync_responder → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → chainsync_responder` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `tx_submission_initiator → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → tx_submission_initiator` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `tx_submission_responder → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → tx_submission_responder` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `keepalive_initiator → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → keepalive_initiator` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `keepalive_responder → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → keepalive_responder` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `peer_sharing_initiator → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → peer_sharing_initiator` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `peer_sharing_responder → mux` WantNext/Send | `amaru-protocols/src/protocol/miniprotocol.rs:228`, `amaru-protocols/src/protocol/miniprotocol.rs:232`, `amaru-protocols/src/protocol/miniprotocol.rs:274`, `amaru-protocols/src/protocol/miniprotocol.rs:278` |
| `mux → peer_sharing_responder` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `blockfetch_initiator → mux` WantNext/Send | `amaru-protocols/src/blockfetch/initiator.rs:276`, `amaru-protocols/src/blockfetch/initiator.rs:280`, `amaru-protocols/src/blockfetch/initiator.rs:288`, `amaru-protocols/src/blockfetch/initiator.rs:346`, `amaru-protocols/src/blockfetch/initiator.rs:391`, `amaru-protocols/src/blockfetch/initiator.rs:397` |
| `blockfetch_responder → mux` WantNext/Send | `amaru-protocols/src/blockfetch/responder.rs:231`, `amaru-protocols/src/blockfetch/responder.rs:238`, `amaru-protocols/src/blockfetch/responder.rs:244`, `amaru-protocols/src/blockfetch/responder.rs:252` |
| `mux → blockfetch_responder` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `mux → done_trap` Registered/FromNetwork | `amaru-protocols/src/mux.rs:660`, `amaru-protocols/src/mux.rs:846`, `amaru-protocols/src/mux.rs:858` |
| `mux_reader → mux` FromNetwork | `amaru-protocols/src/mux.rs:573` |
| `mux_writer → mux` Written | `amaru-protocols/src/mux.rs:382` |
| `connection → mux` Register/SetSduTimeout | `amaru-protocols/src/connection.rs:403`, `amaru-protocols/src/connection.rs:471`, `amaru-protocols/src/chainsync/mod.rs:67`, `amaru-protocols/src/chainsync/mod.rs:91`, `amaru-protocols/src/tx_submission/mod.rs:118`, `amaru-protocols/src/keepalive/mod.rs:93`, `amaru-protocols/src/peer_sharing/mod.rs:109`, `amaru-protocols/src/peer_sharing/responder.rs:67`, `amaru-protocols/src/blockfetch/initiator.rs:465`, `amaru-protocols/src/blockfetch/responder.rs:304`, `amaru-protocols/src/mux.rs:275` |
| `connection → chainsync_responder` NewTip | `amaru-protocols/src/connection.rs:258` |
| `connection → tx_submission_initiator` Close | `amaru-protocols/src/connection.rs:602` |
| `connection → keepalive_initiator` Close | `amaru-protocols/src/connection.rs:608` |
| `connection → peer_sharing_initiator` Close | `amaru-protocols/src/connection.rs:612` |
| `connection → track_peers` Terminated | `amaru-protocols/src/connection.rs:320` |
| `connection → manager` HandshakeComplete | `amaru-protocols/src/connection.rs:454` |
| `chainsync_initiator → track_peers` ChainSyncInitiatorMsg | `amaru-protocols/src/chainsync/initiator.rs:169` |
| `tx_submission_responder → mempool` InsertBatch | `amaru-protocols/src/tx_submission/responder.rs:608` |
| `submit_api → mempool` Insert | `amaru-node/src/submit_api.rs:85` |
| `blockfetch_initiator → cleanup_replies` Block/NoBlocks/Done | `amaru-protocols/src/blockfetch/initiator.rs:312`, `amaru-protocols/src/blockfetch/initiator.rs:348`, `amaru-protocols/src/blockfetch/initiator.rs:364` |
| `track_peers → select_chain` NewTip | `amaru-consensus/src/stages/track_peers/mod.rs:868` |
| `forge_block → select_chain` TipFromUpstream | `amaru-consensus/src/stages/forge_block/protocol.rs:455` |
| `fetch_blocks → select_chain` FetchNextFrom | `amaru-consensus/src/stages/fetch_blocks/mod.rs:396`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:407`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:652`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:750`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:758` |
| `validate_block → select_chain` BlockValidationResult | `amaru-consensus/src/stages/validate_block/mod.rs:111`, `amaru-consensus/src/stages/validate_block/mod.rs:142` |
| `fetch_blocks → validate_block` DownloadedBlock | `amaru-consensus/src/stages/fetch_blocks/mod.rs:310`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:395`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:641` |
| `validate_block → adopt_chain` AdoptChain | `amaru-consensus/src/stages/validate_block/mod.rs:119` |
| `validate_block → block_source` Validation | `amaru-consensus/src/stages/validate_block/mod.rs:117`, `amaru-consensus/src/stages/validate_block/mod.rs:149` |
| `adopt_chain → manager` NewTip | `amaru-consensus/src/stages/adopt_chain/mod.rs:266` |
| `adopt_chain → block_source` AdoptedTip | `amaru-consensus/src/stages/adopt_chain/mod.rs:268` |
| `adopt_chain → mempool` NewTip | `amaru-consensus/src/stages/adopt_chain/mod.rs:264` |
| `adopt_chain → forge_block` AdoptedTip | `amaru-consensus/src/stages/adopt_chain/mod.rs:274` |
| `fetch_blocks → manager` FetchBlocks | `amaru-consensus/src/stages/fetch_blocks/mod.rs:440`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:544` |
| `manager → cleanup_replies` PeersAsked/NoPeersAvailable | `amaru-protocols/src/manager/mod.rs:795`, `amaru-protocols/src/manager/mod.rs:798` |
| `cleanup_replies → fetch_blocks` Block/NoBlocks/PeersAsked/NoPeersAvailable | `amaru-consensus/src/stages/fetch_blocks/mod.rs:855`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:859`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:863`, `amaru-consensus/src/stages/fetch_blocks/mod.rs:877` |
| `cleanup_replies → block_source` BlockReceived | `amaru-consensus/src/stages/fetch_blocks/mod.rs:875` |
| `peer_selection → manager` AddPeer/RemovePeer/Disconnect/SetLocalUse | `amaru-consensus/src/stages/peer_selection/mod.rs:339`, `amaru-consensus/src/stages/peer_selection/mod.rs:359`, `amaru-consensus/src/stages/peer_selection/mod.rs:466`, `amaru-consensus/src/stages/peer_selection/mod.rs:504`, `amaru-consensus/src/stages/peer_selection/mod.rs:782`, `amaru-consensus/src/stages/peer_selection/mod.rs:894`, `amaru-consensus/src/stages/peer_selection/mod.rs:945`, `amaru-consensus/src/stages/peer_selection/mod.rs:1219` |
| `manager → connector` Connect | `amaru-protocols/src/manager/mod.rs:359` |
| `connector → manager` ConnectionResult | `amaru-protocols/src/manager/connector.rs:101` |
| `connect_worker → connector` WorkerDone | `amaru-protocols/src/manager/connector.rs:124` |
| `accept → manager` Accepted | `amaru-protocols/src/accept.rs:29` |
| `ledger → track_peers` StakeDistUpdated | `amaru-ledger/src/state.rs:1288`, `amaru-node/src/stages/build_node.rs:504` |
| `track_peers → ledger` VolatileTipEffect | `amaru-consensus/src/stages/track_peers/mod.rs:993`, `amaru-consensus/src/stages/track_peers/mod.rs:1086` |

## Pass 6, after checking the code

The checker still exits 1 in `after`. The bounds below were checked against `33d62a6f`. A row is discharged only where the code matches the bound. The nine `mux → handler` edges and the six edges into manager stay blocking.

### Manager mailbox

Production size is `DEFAULT_MAILBOX_SIZE + target_upstream_peers + target_downstream_peers` (`build_stage_graph.rs:71-72`). `DEFAULT_MAILBOX_SIZE` is 10 (`types.rs:53`). The defaults are 3 upstream and 10 downstream (`lib.rs:97-99`), so the mailbox is 23. The unit test `peer_mailbox_size(40, 10)` is 60. Nothing in this tree sizes the manager mailbox to 460. 460 would be that same formula with upstream + downstream = 450.

The proposed occupancy `4·N_max + 2·max_outbound + 4` is 62 at the defaults, which is already larger than 23. Two of its terms also do not match the send sites:

- `ConnectionResult` (`connector.rs:101`) is one per finished attempt, and `pump` keeps `DEFAULT_PARALLEL_CONNECTION` (10) workers busy (`connector.rs:32`, `:86`). That is not `max_outbound` (3).
- `Accepted` (`accept.rs:29`) is sent for every TCP accept, then the accept stage schedules another pull (`accept.rs:39`). The inbound cap runs later, inside `handshake_complete` (`manager/mod.rs:537-552`), after both `Accepted` and `HandshakeComplete` (`connection.rs:454`) are already queued.
- `RemovePeer` (`peer_selection/mod.rs:339`) is sent on every ban, and a peer can be banned again after the cooldown. There is no one-per-connection guard on that send.
- `AddPeer` (`peer_selection/mod.rs:359`) does stay within `target_upstream_peers`: `start_dial` records the peer as dialing, and `using_occupancy` stops further dials.
- `Listen` is one preload (`build_node.rs:516`).
- `SetLocalUse`, `NewTip`, and `FetchBlocks` are ordinary sends. There is no cell.

### Mux → handler

`next_segment` does `eff.send(&sent, Sent)` (`mux.rs:881`). That `sent` ref is the oneshot from `eff.call` (`tokio.rs:712-718`): the send does not park and does not take a slot in the handler mailbox. So undequeued `Sent` is not part of `W(mux → h)`. What does pile up is `MuxMessage::Send` on the mux, and only when a call times out.

`eff.call` awaits `Sent` or `NETWORK_SEND_TIMEOUT`. On timeout the request stays queued and the reply is ignored (`effect.rs:319-320`). Both miniprotocol (`miniprotocol.rs:232-235`) and the blockfetch responder (`responder.rs:230-244`) discard the admission and continue. A served range is at most `MAX_FETCHED_BLOCKS` (1000) bodies (`responder.rs:44`, `:126`). One timed-out range can leave 1 `StartBatch` + 1000 `Block` + 1 `BatchDone` outstanding, and the next range can add more. On the success path each `call` awaits, so `s_h = 1`. The constant bound needs a per-handler send credit that is not released by a timeout, or a monotone "acked up to n" cell. Neither is in the code.

`want_next` delivers a buffered frame or else increments `wanted` with no cap (`mux.rs:854-861`). The outstanding count is whatever the handler has issued.

`Register` sends `Registered` on every call (`mux.rs:439` → `:660`), once per register message. `do_register`'s occupied arm keeps `wanted`, the frame, and the buffer, and swaps the handler (`mux.rs:694-700`). Re-register is not only the trap. `on_expected_stop` installs the trap (`connection.rs:638-688`) and, when use comes back, `start_initiators` registers a new initiator on the same protocol id (`connection.rs:736-774`). Inherited `wanted` means a late reply is delivered to whichever handler is installed. The trap treats `FromNetwork` as a protocol error and terminates the mux (`mux.rs:252-261`). A legitimate in-flight reply after `MsgDone` does hit the trap. The fix is to zero `wanted` and clear `incoming` on that register. Until then the bound is not `p_h`.

### Per handler

`p_h` is the peak `WantNext` the state machine issues before the matching frame is delivered. `s_h` is outstanding `Send` on the success path, then the timeout path. Local inputs are the handler's own mailbox messages that are not `FromNetwork`.

| Handler | p_h | s_h success | s_h after timeout | Local inputs | 1+p_h+s_h+local vs 10 |
| --- | --- | --- | --- | --- | --- |
| handshake initiator | 1 | 1 | unbounded | none after the propose | fails on timeout |
| handshake responder | 1 | 1 | 1 (one reply, no want_next on it) | none | 3 ≤ 10 only if timeout cannot add a second send; the call result is discarded |
| chainsync initiator | 1 in steady state; 2 if `RequestNext` is processed while the post-intersect `WantNext` is still open | 1 | unbounded | `RequestNext` per header, one `Done` | the mailbox is 14, not 10; `d+1` is not what the code holds |
| chainsync responder | 1 | 1 | unbounded | `NewTip` per adopted block, no cell | fails |
| blockfetch initiator | 1 per pipeline slot, slots share one `wanted`; `n=2` | 1 | unbounded | one stashed range, `Close` | the "4 ≤ 10" figure does not include a timed-out `Send` |
| blockfetch responder | 1 | 1 | ≤ 1002 per range, then more | none (the range is handled inside the transition) | fails |
| tx initiator | 1 | 1 | unbounded | `Close`, and the mempool wake | fails |
| tx responder | 1 | 1 | unbounded | capacity wake, inflight timeout | fails |
| keepalive initiator | 1 | 1 | unbounded | `Close`, timer is priority | fails on timeout |
| keepalive responder | 1 | 1 | 1 per response | none | same timeout hole |
| peer-sharing initiator | 1 | 1 | unbounded | `Close`, timer is priority | fails on timeout |
| peer-sharing responder | 1 | 1 | 1 per share | none | same timeout hole |
| done trap | inherited `wanted` | 0 | 0 | `Registered` | not a constant `p_h` |

### WantNext sites

The mux does not enforce these. Each row is the protocol state at the call. The actual send is `miniprotocol.rs:228` for a network outcome and `:274` for a local outcome, except blockfetch, which sends `WantNext` itself.

| Handler | Site | State at the call | What it does |
| --- | --- | --- | --- |
| chainsync initiator | `initiator.rs:341` via `:274` | `Idle`, after `Registered` runs `init` (no `want_next`, `:299`) | one `WantNext` with `FindIntersect` |
| chainsync initiator | `initiator.rs:316` via `:228` | `Intersect`, on `IntersectFound` | one `WantNext`, not two up front, and `RequestNext(PIPELINE_DEPTH)` is a single wire message |
| chainsync initiator | `initiator.rs:323` via `:228` | `CanAwait(n)`, on `AwaitReply` | re-issues one `WantNext` |
| chainsync initiator | `initiator.rs:343`, `:345`, `:348` via `:274` | `Idle`, `CanAwait`, or `MustReply`, on local `RequestNext` | one `WantNext` each; `MustReply` can add one while an earlier `WantNext` is still open |
| chainsync responder | `responder.rs:249` via `:228` | `Idle`, on `Registered` | initial `WantNext` |
| chainsync responder | `responder.rs:268` via `:228` | `Idle`, on `Done` | `WantNext` |
| chainsync responder | `responder.rs:279`, `:283` via `:274` | `Intersect` | `WantNext` with the intersect reply. Not `Idle` |
| chainsync responder | `responder.rs:287` via `:274` | `CanAwait` | `AwaitReply` sends and does **not** `WantNext` |
| chainsync responder | `responder.rs:291`, `:294`, `:297` via `:274` | `CanAwait` or `MustReply` | `WantNext` with the roll. Not `Idle` |
| handshake initiator | `initiator.rs:159` via `:274` | `Propose`, after `Registered` | one `WantNext` with `Propose`. `init` itself has no `want_next` (`:128`) |
| handshake responder | `responder.rs:101` via `:228` | `Propose`, on `Registered` | initial `WantNext` |
| handshake responder | `responder.rs:123-126` via `:274` | `Confirm` | the reply has no `want_next` |
| tx initiator | `initiator.rs:170` via `:228` | `Idle`, on `Registered` | `Init` plus `WantNext` |
| tx initiator | `initiator.rs:215`, `:218`, `:221` via `:274` | `Idle` | `WantNext` with each reply |
| tx responder | `responder.rs:205` via `:228` | `Init`, on `Registered` | initial `WantNext` |
| tx responder | `responder.rs:224` via `:228` | `TxIdsBlocking`, on `Done` | `WantNext`, and the state returns to `Init` |
| tx responder | `responder.rs:233-240` via `:274` | `Idle` | `WantNext` with each request. The network replies (`:216-222`) do not |
| keepalive initiator | `initiator.rs:179` via `:274` | `Idle` | `WantNext` with the cookie. The reply (`:169`) does not |
| keepalive responder | `responder.rs:108` via `:228` | `Idle`, on `Registered` | initial `WantNext` |
| keepalive responder | `responder.rs:121` via `:228` | `Idle`, on `Done` | `WantNext` |
| keepalive responder | `responder.rs:131` via `:274` | `Waiting` | `WantNext` with the response. Not `Idle` |
| peer-sharing initiator | `initiator.rs:259` via `:274` | `Idle` | `WantNext` with the request |
| peer-sharing responder | `responder.rs:198` via `:228` | `Idle`, on `Registered` | initial `WantNext` |
| peer-sharing responder | `responder.rs:213` via `:228` | `Idle`, on `Done` | `WantNext` |
| peer-sharing responder | `responder.rs:223` via `:274` | `Busy` | `WantNext` with `SharePeers`. Not `Idle` |
| blockfetch initiator | `initiator.rs:290`, `:298` | `Busy` | `WantNext` on `Pull` and `StartBatch` |
| blockfetch initiator | `initiator.rs:346` | `Streaming` | `WantNext` per block |
| blockfetch initiator | `initiator.rs:400` | `Idle`, after a stashed fetch | `WantNext` after the range `call` |
| blockfetch responder | `responder.rs:217-223` | `Idle` | `Registered` is rewritten to `Pull`, then `WantNext`. This is a `WantNext` in the `Registered` transition |
| blockfetch responder | `responder.rs:248`, `:256` | end of the `Idle` range transition | one `WantNext` after the batch, not per block |
| blockfetch responder | `responder.rs:264` | `Idle`, on `ClientDone` | `WantNext` |

Sites that are not "responders `WantNext` only in `StIdle`, never on `Registered`":

- chainsync responder from `Intersect`, `CanAwait`, and `MustReply` (`responder.rs:279`, `:291`, `:294`, `:297`)
- keepalive responder from `Waiting` (`responder.rs:131`)
- peer-sharing responder from `Busy` (`responder.rs:223`)
- blockfetch responder's `Pull` on `Registered` (`responder.rs:217-223`)
- every responder `init` that sets `want_next`, which runs because `Registered` takes the `init` arm (`miniprotocol.rs:224`)

The chainsync initiator does re-issue on `AwaitReply` (`initiator.rs:323`) and does not issue two `WantNext` up front on `IntersectFound`.

### The other mux outputs

`OutgoingSdu` is at most one: `sending` gates both sends (`mux.rs:446-449`, `:469-474`) and `Written` clears it. `Read` alternates with `FromNetwork`: one `Read` at init (`mux.rs:392`), and the next only after a segment has been handed to the mux (`mux.rs:463`). Both are `W = 1` against a mailbox of 10, and both stay discharged.

### Checker

`now`: exit 1. 72 blocking edges kept, 6 discharged. One component of 24, plus the `Resolved` self-loop.

`after`: exit 1. 56 blocking edges kept, 22 discharged. Components of 10 (mux and the handlers whose return edge is still open), 6 (`fetch_blocks`, `cleanup_replies`, `manager`, `connector`, `validate_block`, `adopt_chain`), and 2 (`ledger`, `track_peers`).
