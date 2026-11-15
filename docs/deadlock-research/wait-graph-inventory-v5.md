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
