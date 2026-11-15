# Wait-graph inventory, pass 2

Tree: `33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6` (merge of #1647). Read from the local checkout of that commit. No pragma-org write, and no comment on issue 1653.

Cycle (a), `select_chain → fetch_blocks → validate_block → select_chain`, is discharged by the `may_fetch_blocks` token, as a state-indexed wait graph. The five checks below are the remaining obligations. A message is **reliable** when the receiver needs that delivery, and **superseding** only when Amaru’s own handler keeps the latest value or a join. Nothing below is a proposal to drop a reliable message.

## (1) No residual blocking path from `peer_selection` or `block_source` back to the chain

`fetch_blocks` can blocking-send `Adversarial` while idle. In `block`, the body-hash check sends it before `missing` is consulted:

```570:587:crates/amaru-consensus/src/stages/fetch_blocks/mod.rs
        if block.header.body().block_body_hash != block.body_hash() {
            // ...
            eff.send(
                &self.peer_selection,
                PeerSelectionMsg::Adversarial(/* ... */),
            )
            .await;
            return;
        }

        let Some(missing) = self.missing.as_mut() else {
            debug!(consensus::blocks::STRAGGLER, peer);
            return;
        };
```

A mismatched body is reported even when `missing` is `None`. The `cleanup_replies` child, which is a separate stage, always blocking-sends `BlockReceived` to `block_source`, and on a decode failure blocking-sends `Adversarial` to `peer_selection`. It forwards `Block` / `NoBlocks` / `PeersAsked` to `fetch_blocks` only when `id >= curr_id` (`fetch_blocks/mod.rs:853–877`).

Those edges do not come back.

`block_source` has two blocking sends, both `Adversarial` to `peer_selection` (`block_source/mod.rs:128` and `:152`). It has no send to `select_chain` or `fetch_blocks`. `AdoptedTip` only stores the point and prunes (`:179–181`, `:160–163`).

`peer_selection` blocking-sends only to `manager` and to its ledger-check child:

| Message | Site |
| --- | --- |
| `AddPeer` | `peer_selection/mod.rs:359`, `:1219` |
| `RemovePeer` | `:339` inside `ban_peer` (`:314`) |
| `Disconnect` | `:782`, `:945` |
| `SetLocalUse` | `:466`, `:504`, `:894` |
| `()` to `peer-selection/ledger-check` | `:1203` |

`SendBudget::send` is `eff.send` (`:111`). The ledger-check child reads the ledger and calls `Performance::set_ledger_candidates`. It does not send to a stage (`:1297–1298`).

`manager` turns those four messages into connector or connection traffic, not into chain traffic:

- `AddPeer` → `ConnectorMsg::Connect` (`manager/mod.rs:342–359`). The connector’s `ConnectionResult` comes back to `manager`.
- `RemovePeer` / `Disconnect` → `ConnectionMessage::Disconnect` (`:844`, `:946`).
- `SetLocalUse` → `ConnectionMessage::SetLocalUse` (`:888`).

`FetchBlocks` and `NewTip` are the manager sends that reach `fetch_blocks`’s peers and the chainsync responder. `peer_selection` never emits either message. `manager` emits them only when `fetch_blocks` or `adopt_chain` already sent them (`:864–870`).

On `Disconnect` / a diffusion demotion, `connection` blocking-sends `InitiatorMessage::Done` and `BlockFetchMessage::Close` to the initiators (`connection.rs:594`, `:598`). `Done` is consumed by the chainsync initiator; it is not forwarded to `select_chain`. Teardown sends `InitiatorResult::Terminated` straight to `track_peers` (`connection.rs:319–329`). The `Terminated` arm purges the session and may clear a performance resource (`track_peers/mod.rs:902–905`, `:607–610`). It does not send to `select_chain`. `BlockFetchMessage::Close` calls `ClientDone` and terminates the handler; it does not `send_any` to the fetch collector.

So the idle `Adversarial` edge, and the cleanup child’s sends, end at `peer_selection` (and, for `BlockReceived`, at `block_source` → `peer_selection`). They do not reach `select_chain` or `fetch_blocks`. They do not put an edge back onto cycle (a).

## (2) `RecoverStoredBlocks` has no runtime sender

The only production enqueue is the startup preload:

```199:204:crates/amaru-node/src/stages/build_stage_graph.rs
    stage_graph
        .preload(
            &fetch_blocks,
            [FetchBlocksMsg::RecoverStoredBlocks { from: ledger_tip, to: recovery_best_hash, trace_context }],
        )
```

No `eff.send` of `RecoverStoredBlocks` exists. The message constructor and the bench only build the value. The stage arm at `fetch_blocks/mod.rs:816` is the receiver.

`preload` runs while the graph is being built, before any stage is scheduled. The first `FetchNextFrom` this node sends is produced by processing that preloaded message (`fetch_next_from` at `:758`, reached from the recovery `request_blocks` path). The first `NewBestTip` can be sent only after `select_chain` has dequeued that `FetchNextFrom` (or a later one). The injection is therefore before the first exchange.

`select_chain` is preloaded with `Initialize` only (`build_stage_graph.rs:213–215`), not with `FetchNextFrom`.

## (3) `FetchNextFrom(Origin)` is not the only token creation

`may_fetch_blocks` starts `false` (`select_chain/mod.rs:116`). The only assignment to `true` is the else branch of `handle_fetch_next_from`:

```446:490:crates/amaru-consensus/src/stages/select_chain/mod.rs
        if let Some(best_tip) = &self.best_tip
            && best_tip.point() != point
        {
            // ...
            eff.send(&self.downstream, NewBestTip { /* best_tip */ }).await;
        } else {
            // ...
            self.may_fetch_blocks = true;
        }
```

That branch runs for every dequeued `FetchNextFrom` whose point equals the current best, and for every `FetchNextFrom` when there is no best. A later “already at this tip” resume creates a token the same way. The then-branch does not create one: it answers immediately with `NewBestTip` and leaves the flag false. The assert at `:443` rejects a second `FetchNextFrom` while a token is still held.

The only production sender of `FetchNextFrom` is `fetch_blocks::fetch_next_from` (`:755–758`). Its point is the argument from the call site (`:396`, `:407`, `:652`, `:750`), not a hard-coded origin. It is origin only when that point is origin.

The comment at `select_chain/mod.rs:51–53` about preloading `FetchNextFrom(Point::Origin)` describes a graph with no fetch stage. This node’s graph does not do that.

One related fact: if both the ledger tip and the recovery hash are origin, `recover_stored_blocks` returns at `fetch_blocks/mod.rs:265–270` without calling `fetch_next_from`. Nothing else sends `FetchNextFrom`, and `may_fetch_blocks` stays false, so `select_chain` will not send `NewBestTip` for later headers. That is a missing first token, not a second creation site.

## (4) Cycle (c): one chainsync initiator mailbox

Bulk mailbox `CHAINSYNC_INITIATOR_MAILBOX = PIPELINE_DEPTH + 4` with `PIPELINE_DEPTH = 10` (`chainsync/mod.rs:27–33`), so 14. The mailbox type is `Inputs<InitiatorMessage>`. Producers, and what the code actually bounds:

| Kind | Who sends it | How many this code will enqueue |
| --- | --- | --- |
| `Local(RequestNext)` | `track_peers` only (`:877`, `:1015`, `:1049`, `:1069`) | No counter. See the per-message table. A recheck can emit one per released deferred header in a single turn, and those sit until the initiator dequeues them. `PIPELINE_DEPTH` is not read here. |
| `Local(Done)` | `track_peers` `:911`, `:931`, `:1063`; `connection` `begin_stop` `:594` | One `Done` per such arm. `begin_stop` sends one. Both can be queued together. The unknown-intersection arm (`:911`) sends `Done` and returns without `purge_connection`, so a later `IntersectFound` for the same handler can send another. |
| `Network(FromNetwork)` | `mux` `:846` and `:858`, and only while `wanted > 0` | One delivered frame per unmatched `want_next`. `RollForward` / `RollBackward` do not call `want_next` (`chainsync/initiator.rs:324–331`). The intersect result asks the peer for `RequestNext(PIPELINE_DEPTH)` but issues a single `want_next` and stores `CanAwait(1)` (`:315–318`). Further `want_next`s are one per local `RequestNext` the initiator actually runs (`:343–348`). Frames already credited can be queued; frames not yet credited cannot. |
| `Network(Registered)` | `mux` `:660`, once, when the protocol is registered | 1 |
| `Internal(Timeout)`, `Internal(Pull)` | not armed | 0. The chainsync initiator is a `miniprotocol`, not the blockfetch pipeline driver, and neither it nor `miniprotocol` calls `set_timeout`. |

`connection` teardown does **not** put `Terminated` in this mailbox. It sends that value to `track_peers` (`connection.rs:319–329`). A child tombstone is priority ingress, not a bulk slot.

### One `RequestNext` per received `ChainSyncInitiatorMsg`

`track_peers` sends to the initiator only from the arms below. `recheck_deferred` (`:1085`) is not a new upstream message; it sends the `RequestNext` that the receive arm withheld, and only when `sent_request_next` is false.

| Received `ChainSyncInitiatorMsg` | `RequestNext` in that turn | Later, for the same header |
| --- | --- | --- |
| `Initialize` (`:892`) | 0 | no |
| `Terminated` (`:902`) | 0 | no |
| `IntersectFound`, point in the store (`:907`) | 0 | no |
| `IntersectFound`, point missing (`:909`) | 0, sends `Done` | no |
| `IntersectNotFound` (`:926`) | 0, sends `Done` | no |
| `RollForward`, header does not decode (`:950`) | 0, sends `Adversarial` | no |
| `RollForward` while that connection is already deferred (`:973`, `FollowUp`) | 0 | one on recheck (`sent_request_next: false`, `:304`) |
| `RollForward`, ledger height too low (`:997`) | 0, returns before `:1015` | one on recheck (`:271`) |
| `RollForward`, height ok (`:1015` then `try_roll_forward`) | 1, at `:1015`. The args carry `sent_request_next: true`, so `:877` does not send a second. Stake and clock defers store that flag (`:634`, `:667`), so recheck does not send again | no |
| `RollBackward`, point known (`:1048`) | 1 | no |
| `RollBackward`, unknown point (`:1058`) | 0, sends `Done` | no |
| `RollBackward`, any other error (`:1067`) | 1, then `Adversarial` | no |

No arm sends two `RequestNext`s for one received message. The early send and the late send are alternatives, joined by `sent_request_next` / `rn_sent`.

That does not cap the mailbox. `track_peers` is single-threaded and each `RequestNext` completes when it is queued, so it can enqueue one per header it has already accepted while this initiator is busy. A recheck walks every deferred header and can send one `RequestNext` per header whose flag is clear, in that one turn, until this mailbox is full and `track_peers` parks. `local` accepts `RequestNext` in `Idle`, `CanAwait`, and `MustReply` with no ceiling (`initiator.rs:122–125`), and `CanAwait(n)` / `MustReply(n)` only grow.

Cycle (c) stays a real cycle of reliable blocking edges: initiator → `track_peers` (`ChainSyncInitiatorMsg`, one per protocol result, reliable) and `track_peers` → initiator (`RequestNext`, reliable; a missing one stalls that peer’s header stream). Occupancy of `RequestNext` on one initiator is not bounded by `PIPELINE_DEPTH`. The credit that would create a bound is: `track_peers` keeps, per connection, `RequestNext` sent minus roll-forward/roll-backward results received, and does not send when that equals `PIPELINE_DEPTH`. With also at most one unmatched `FromNetwork`, one `Done`, and one `Registered`, the mailbox would need `PIPELINE_DEPTH + 4`, which is the current size. That counter is not in the code, so 14 is not sufficient.

`track_peers` itself is one mailbox of size 10 for every initiator. Each initiator blocking-sends every result, including `Initialize` and `Terminated` (`initiator.rs:169–172`). N initiators times one in-flight result is already more than 10 once N > 10, and without a per-peer credit each initiator may have many results queued. The structural credit that would bound it is one unacknowledged `ChainSyncInitiatorMsg` per peer, which needs a mailbox of at least N. Current size 10 does not meet that for the configured upstream target once other peers are connected, and it does not meet `N * PIPELINE_DEPTH` if the pipeline credit above is the one installed instead.

## (5) `StakeDistUpdated` rechecks; init does not re-read

The arm is only:

```355:358:crates/amaru-consensus/src/stages/track_peers/mod.rs
        TrackPeersMsg::StakeDistUpdated(max_epoch) => {
            state.max_epoch = max_epoch;
            state.recheck_deferred(&eff).await;
        }
```

`recheck_deferred` always does two things beyond storing the epoch:

1. It re-reads the volatile tip, not the stake map: `VolatileTipEffect` (`:1086–1087`), and stores that height.
2. For every deferred header that this tip and the new `max_epoch` unblock, it calls `try_roll_forward`. That calls `validate_header` (`:767`), which calls `ledger.validate_header` (`:558–561`). A success can blocking-send `NewTip` to `select_chain` (`:868`) and, if `sent_request_next` is false, `RequestNext` (`:876`). A hard failure can blocking-send `Adversarial` (`:786`).

An empty deferred queue still pays for the tip read. The stake distribution itself was written by the ledger callback into `ResourcePoolSummaries` before the message was sent (`build_node.rs:500–511`). `track_peers` does not read that resource by name; `ValidateHeaderEffect` observes it when a deferred header is retried.

The epoch test in the recheck is `max_epoch < epoch` (`:1104`). A greater epoch covers every header a lesser epoch would have released, so a later greater epoch subsumes an earlier one for that threshold. The code assigns `max_epoch = max_epoch` rather than taking a max, so a lesser epoch processed later moves the threshold backward. The message is not “read the resource and return”: the recheck can emit reliable `NewTip` and `RequestNext` messages. It is not a droppable wake-up.

Init and restart do not re-read. `TrackPeers::new` copies the caller’s `max_epoch` and sets `ledger_applied_block_height` to 0 (`:368–388`). It runs no effect. `build_stage_graph` passes the epoch it already had when the ledger was opened (`build_stage_graph.rs:221–223`). There is no restart method on the stage. The first `VolatileTipEffect` on the header path is the rate-limited read at `:988–993`, which starts from height 0, not a re-read during construction.

The callback that produces the message runs on the ledger thread, inside `rotate_stake_distribution`, before that call returns (`amaru-ledger/src/state.rs:1287–1288`). The node callback `block_on`s `track_peers_sender.send` (`build_node.rs:503–511`). `track_peers` waits on that same ledger through `VolatileTipEffect` and `validate_header`. A callback on the ledger thread is part of the ledger effect, and this one waits on a stage. That edge stays a cycle. Mithril has the same shape at `mithril.rs:750`.

## Mailbox capacity

Current sizes: default bulk 10 (`types.rs:53`); priority 10 (`types.rs:44`); `manager` and `peer_selection` `10 + U + D` (`build_stage_graph.rs:71–91`); `mux` 24 (`mux.rs:62`); chainsync initiator `PIPELINE_DEPTH + 4`; blockfetch handler `max(10, 2*n + 4)` (`blockfetch/initiator.rs:58–60`) with default `n = 2`. `U` and `D` are the configured upstream and downstream targets (3 and 10 in the comment, mailbox 23).

“Sufficient” means the occupancy of reliable messages, summed over producers, is strictly below the current capacity. Superseding streams are counted as one slot because the handler keeps a single value; the mailbox does not overwrite, so a burst of them still fills slots until the consumer runs.

| Mailbox | Required capacity | Current | Sufficient |
| --- | --- | --- | --- |
| `select_chain` | No finite bound in N. Producers: `track_peers` `NewTip` (one per stored header, reliable; same hash is a no-op at `:252`, a different hash is not), `fetch_blocks` `FetchNextFrom` (one at a time, reliable), `validate_block` result (one per block, reliable), `forge_block` `ForgeTip` (one, reliable, same `TipFromUpstream` variant). Credit that would bound the header fan-in: one unacknowledged `NewTip` per upstream peer. Then `N + 3`. | 10 | no |
| `fetch_blocks` | One `NewBestTip` from `select_chain` (the token). Plus, for the open id, up to `MAX_FETCH_PEERS * MAX_MISSING_BLOCKS_PER_BATCH` = `5 * 25` = 125 `Block`s from `cleanup_replies`, and a handful of `NoBlocks` / `PeersAsked` / `NoPeersAvailable`. Recovery replay sends one `DownloadedBlock` per stored ancestor before that cap (`:298–310`); that length is the stored chain, not a function of N. | 10 | no |
| `validate_block` | No bound independent of chain length: recovery and a live batch both blocking-send every `DownloadedBlock`, and Mithril sends `ValidateBlockMsg` (`mithril/block_source.rs:137`). Credit that would bound it: at most W unacknowledged blocks, W < 10, shared with Mithril’s one in-flight send. | 10 | no |
| `adopt_chain` | One validation/adopt message in flight from `validate_block`. Reliable. | 10 | yes, for that single producer |
| `track_peers` | No bound below 10. Credit: one unacknowledged `ChainSyncInitiatorMsg` per peer, plus one `StakeDistUpdated` if a greater epoch overwrites. Then `N + 1`. | 10 | no |
| chainsync initiator | `PIPELINE_DEPTH + 4` only after the per-connection `RequestNext` credit in section (4). Without it, unbounded in deferred headers. | 14 | no |
| `mux` | Intended `10 * (WantNext + Send) + FromNetwork + Written + Register + SetSduTimeout` = 24, if each of 10 handlers has at most one of each and a timed-out `Send` is not left queued. `miniprotocol` ignores the call result (`miniprotocol.rs:232–235`, `:278–281`) and `Effects::call` leaves a timed-out request queued (`effect.rs:319–320`). That breaks the “one Send” half. No strict bound under 24. | 24 | no |
| reader | 1 `Read`. `mux` sends the next `Read` only after `received` returns (`mux.rs:392`, `:463`). | 10 | yes |
| writer | 1 `OutgoingSdu`. `mux` sends only while `sending` is false, then sets it (`mux.rs:446–474`). | 10 | yes |
| blockfetch handler | `2*n + 4` is the comment’s budget (one local and one network message per slot, `Registered`, `Close`, one stashed range). `pending_fetch` keeps one range (`initiator.rs:324`, `:376`). A range id is reliable: `cleanup_replies` matches it. The stash is one slot of state, not a proof that a third range cannot be queued. | `max(10, 2n+4)` | no for a third range; the `2n+4` term matches the comment’s own budget and is not enforced against `widen` |
| `manager` | Reliable handshake calls and connect results are one per bearer in flight, up to `U + D` if every target connects at once, plus one `FetchBlocks`. `NewTip` is superseding: `chainsync` responder does `self.upstream = tip` and serves intermediate headers from the store (`responder.rs:85–96`). `SetLocalUse` is superseding (`connection.rs:262–264`, `desired_use = desired`). Without a cap on overlapping rounds of `AddPeer` / `Disconnect`, the reliable burst is not bounded by `U + D`. | `10+U+D` | no |
| `peer_selection` | `Adversarial` for a new peer is reliable. A repeat for the same peer is a join: `ban_peer` removes it once, and a second report while cooling is ignored (`:1206–1208`). Distinct peers do not subsume each other. One `Resolved` per `detach` (`:664`). No cap was found that keeps concurrent dials ≤ U. | `10+U+D` | no |
| `mempool` | `Insert` / `InsertBatch` are reliable. `NewTip` revalidates every transaction against the ledger and then `set_tip` (`mempool/stage.rs:101–105`); a later tip replaces the tip a revalidation uses. One slot if a greater tip overwrites. Calls add one admission each. | 10 | no, once inserters and a tip overlap with no credit |
| `block_source` | `BlockReceived` is reliable per distinct point (it records the peer). `AdoptedTip` is superseding (`adopted_tip = tip`). `Validation` is reliable per point. Burst is the number of blocks in flight, which is the fetch batch above. | 10 | no |
| `forge_block` | `AdoptedTip` assigns `adopted_tip` and `adopted_parent` (`forge_block/protocol.rs:205–206`). Superseding. One slot. | 10 | yes for that single stream |
| priority (every stage) | `schedule_at` counts `scheduled_pending` and panics at 10 (`tokio.rs:867–869`; simulation `running/mod.rs:1360–1366`). `set_timeout` uses `TimeoutHeap` and does not take that budget (`effect.rs:463–467`). Tombstones are priority `Tombstone` messages and are not counted; a blocked parent does not process them until the bulk send returns. | 10 | the panic is the bound; it is not a wait |

`NewBestTip` is reliable. `select_chain` coalesces tips that arrive while the token is false into `best_tip`, and the one message it does send has to be delivered: the flag is already false, and `fetch_blocks` starts a batch from that point (`new_tip` asserts `missing` is clear). It is not a last-value mailbox message.

## Other edges that were still open

`Effects::call` maps both not-admitted and timed-out to `None` (`effect.rs:340`). The request stays queued on timeout. Callers:

- `connection` handshake, 10s: `None` or `Some(false)` terminates the bearer (`connection.rs:464–468`). No retry.
- `miniprotocol` mux send, 1s: result ignored, and the protocol state has already stepped (`miniprotocol.rs:266–281`). No teardown, no retry. The bearer stays up with the state ahead of the wire if the send was never admitted.
- blockfetch `session.call`: the admission is discarded and `finish()` runs anyway (`initiator.rs:276`, `:397`; responder `:231–252`). `Busy` / `Streaming` timeout calls `timed_out`, which terminates (`initiator.rs:415–417`). No retry loop.
- tx-submission `InsertBatch`: `None` terminates the mini-protocol (`tx_submission/responder.rs:614–616`). No retry.
- submit API: `CallError::TimedOut` becomes HTTP 503 (`submit_api.rs:100`). No node-side retry loop.

`wrap_sync` / `wrap_sync_f` return `future::ready` after the closure (`effect.rs:784–799`). Store, mempool, metrics, forge, consensus-mode, random, and performance effects that use it do not take a `StageRef`. `ValidateHeaderEffect`, `VolatileTipEffect`, and block validation use `external` and wait on the ledger thread, not on a stage, except when that thread is inside the stake callback above.

Simulation `send` to an unknown stage drops the message and resumes the sender (`simulation/running/mod.rs:1307–1308`). Tokio `send` expects the name in the sender map and panics if it is absent (`tokio.rs:724`). A terminated stage whose sender is still in the map completes the send with an error, and the runtime discards that error (`:726`).

`reader → mux` `FromNetwork` and `writer → mux` `Written` are reliable and are not discharged by the one-outstanding `Read` / `OutgoingSdu` credits; those credits only bound the opposite direction.
