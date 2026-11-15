# Pure-stage wait-graph patterns

Analysed tree: `pragma-org/amaru` `main` at **`33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6`** (merge of #1647, 2026-11-14). Read-only fetch. No code changes.

This is a pattern lift, not a full inventory and not a deadlock-freedom proof. Nodes are mailboxes (and the few other waits that are not pure delays). An edge `M1 → M2` means a stage that has already taken a message from `M1` can wait on `M2` before it receives again.

## Edge classes

| Class | Meaning | Breaks an infinite buffer cycle? |
| --- | --- | --- |
| `blocking` | `Effects::send` into another stage’s bulk mailbox. Parks until a slot exists. The stage does not receive while parked. | No |
| `timeout` | `Effects::call`, or peer I/O wrapped in a finite timeout. The waiter resumes when the deadline fires. | Yes, it is bounded |
| `peer-unbounded` | Peer I/O with no timeout. | No, if the peer never proceeds |
| `delay` | Ledger, chain store, `Performance` worker, resources, timers, `wait`, `clock`. Takes time. Under Roland’s assumption it finishes without a stage making progress. | Yes, by assumption |
| `drop` | `try_send`, send to blackhole, send to a terminated stage, call reply on the oneshot. Does not park on a mailbox. | Yes |
| `violation` | Looks like a delay, but completion waits on a stage mailbox. | No. The assumption does not apply |

`blocking` is the only class that matches Dally & Seitz buffer deadlock. A cycle made only of `blocking` edges is a buffer-deadlock candidate. Sized mailboxes are an occupancy argument on top of that, not a different edge class. The #1475 lockup was a `blocking` cycle whose mailboxes were too small for the burst.

While a stage is parked on any effect, bulk mail stays queued. Priority timers are copied into a side queue (`poll_with_ingress`) but are not delivered until the effect returns. A timer does not unblock a stage stuck in `send`.

## 1. Topology (representative)

Bulk default is **10** (`DEFAULT_MAILBOX_SIZE`, `crates/amaru-pure-stage/src/types.rs:53`). Priority cap is **10** (`PRIORITY_MAILBOX_SIZE`, same file line 44). Priority mail does not use the bulk buffer. The message being processed does not occupy a bulk slot (`tokio.rs` docs around line 228).

Static core, created in `build_stage_graph` (`crates/amaru-node/src/stages/build_stage_graph.rs`):

| Stage | Capacity | Created by |
| --- | --- | --- |
| `manager`, `peer_selection` | `10 + target_upstream + target_downstream` (23 at 3/10) | `stage_with_mailbox_size`, lines 89–91, helper 71–73 |
| `track_peers`, `select_chain`, `fetch_blocks`, `validate_block`, `adopt_chain`, `mempool`, `block_source`, optional `forge_block` | 10 | `stage`, lines 112–138 |

Per-peer subtree, created when a connection stage runs, one copy per bearer:

| Stage | Capacity | Created / supervised |
| --- | --- | --- |
| `connection` `{conn}-{peer}` | 10 (inherits the creator’s `mailbox_size`) | manager `stage` + `supervise` with tombstone `ConnectionDied` (`manager/mod.rs:474–479`) |
| `mux` | **24** (`MUX_MAILBOX_SIZE`, `mux.rs:62`) | connection `do_initialize`, supervised with `ChildDied(Mux)` (`connection.rs:361–364`) |
| `reader-*`, `writer-*` | 10 | mux `init`, each supervised with `MuxMessage::Terminate` (`mux.rs:364–391`) |
| `handshake` | 10 | connection, supervised (`connection.rs:370–385`) |
| chainsync initiator | **14** = pipeline depth + 4 (`chainsync/mod.rs:33`, `64`) | connection `register_chainsync_initiator` |
| blockfetch initiator | `max(10, 2n+4)` (`blockfetch/initiator.rs:60`) | `register_blockfetch_initiator` (`initiator.rs:456`) |
| other mini-protocols (chainsync responder, blockfetch responder, tx-submission, keep-alive, peer-sharing) | 10 | `eff.stage` in each `register_*` |

Other dynamic stages: `accept` (supervised; death is re-delivered as `Listen`, `manager/mod.rs:438–439`), connector workers (`manager/connector.rs:78–79`), `peer-selection/ledger-check` (explicitly unsupervised, `peer_selection/mod.rs` around the `wire_up` of `get_ledger_candidates`).

Unsupervised child death terminates the parent (`tokio.rs:467–470`). A parent that leaves `run_stage` drops the abort guards on children it wired (`tokio.rs:401–402`, `855`). Root `terminate` is documented as tearing down a graph that was started before `run` (`effect.rs:535–538`). On Tokio, only those static tasks signal network shutdown (`tokio.rs:193`).

## 2. Communication patterns

A stage runs one transition at a time. `send` / `call` / `external` / `wait` all go through the airlock (`effect_box.rs:37–67`) and the interpreter does not receive until the effect returns (`tokio.rs:474–487`).

### Blocking send

`Effects::send` (`effect.rs:251–257`). Tokio path: `mpsc::Sender::send` (`tokio.rs:720–727`). Completes when the message is queued, or immediately with `Err` if the receiver is already dropped (`.ok()` swallows that). Missing name panics (`expect` on the sender map).

Simulation path: full mailbox parks the sender (`simulation/running/mod.rs:1303–1305`); unknown stage drops the message and resumes the sender (`1307–1308`).

### Call

`Effects::call` (`effect.rs:306–343`). One deadline covers admission and the reply.

- Admission is a bulk send of the request. If the deadline wins first, the request is never queued (`tokio.rs:630–645`).
- The reply is a `oneshot`, not a mailbox write (`tokio.rs:712–718`). The callee does not park on the caller’s mailbox to answer.
- The caller does not receive bulk mail until the call returns. A full caller mailbox therefore cannot block the reply itself. It can block some other stage that is doing a normal `send` to the caller.
- `None` means not admitted or timed out. The caller’s transition continues.

Production timeouts found: handshake record **10s** (`connection.rs:48`, call at `454`); mini-protocol wire send **1s** (`protocol/mod.rs:48`, `miniprotocol.rs:232–235`); blockfetch typestate `MuxClient::TIMEOUT` is that same 1s (`blockfetch/initiator.rs:153`).

### Drop / non-park

- `try_send` returns `Full` / `Gone` / `Queued` without parking (`effect.rs:259–287`, `tokio.rs:729–759`). A parked blocking sender owns the next slot, so `try_send` loses to it.
- Blackhole send is dropped (`tokio.rs:708–710`).
- `SendBudget` in peer selection (`peer_selection/mod.rs:92–114`) counts sends. Each send is still `eff.send`, so a full manager mailbox still parks peer selection.

### Delay (internal)

These park the stage, then finish without another stage:

- Chain-store effects compute the answer inside `run` and return a ready future (`store_effects.rs:792–797` for `GetBestChainTipEffect`; `wrap_sync` at `effect.rs:784–790`). No stage channel.
- `Performance` worker (`performance/mod.rs:17–21`, loop at `238–251`). `enqueue` returns immediately (`effects/mod.rs:54–57`). `enqueue_query` awaits a oneshot from that thread (`60–69`). `dispatch` does not touch a `StageRef` (no matches under `crates/amaru-consensus/src/performance`). Queue is unbounded; depth `100_001` panics (`performance/mod.rs:137–139`, `396–406`). That is a crash, not a wait on a stage.
- Ledger requests other than the stake callback below: `BlockValidator::request` `try_send`s onto a bounded queue (16) and panics if that queue is full (`block_validator.rs:50`, `209–228`), then awaits the oneshot. The wait is on the ledger thread.
- `schedule_at` / `set_timeout` do not wait for mailbox space (`effect.rs:380–402`, `463–475`). `wait` waits on the clock only.
- `detach` resumes the stage at once (`effect.rs:498–532`). The later injection is a blocking `tx.send` from a spawned task (`tokio.rs:813–820`). That task is not a stage and the issuer is not waiting, so it is not an `M1 → M2` edge. It can occupy a bulk slot.

`Resources::get` holds the collection read lock only for the lookup (`resources.rs:65–67`). No `get_mut` showed up in consensus effect code. Nothing found that holds that lock across a stage send.

### Assumption violation

Stake rotation runs on the ledger thread and calls the notify callback before the ledger request returns (`amaru-ledger/src/state.rs:1267–1289`). The node callback **blocks that thread** on a bulk send to `track_peers`:

```500:511:crates/amaru-node/src/stages/build_node.rs
    block_validator.set_on_stake_dist_updated(Arc::new(move |summaries| {
        let max_epoch = summaries.max_epoch();
        resources.put::<ResourcePoolSummaries>(Arc::new(summaries));
        let send = async {
            if track_peers_sender.send(TrackPeersMsg::StakeDistUpdated(max_epoch)).await.is_err() {
                amaru_observability::warn!(node::build::STAKE_DIST_NOTIFY_FAILED);
            }
        };
        // The callback runs on the ledger thread; its join also covers notification delivery.
        let rt = tokio::runtime::Builder::new_current_thread().build().expect("cannot build current thread runtime");
        rt.block_on(send);
    }));
```

`track_peers_sender` is the stage input (`build_stage_graph.rs:225–226`), and input send is `mpsc::Sender::send` (`tokio.rs:515–523`). If `track_peers`’s bulk mailbox (capacity 10) is full, the ledger thread does not finish the current request.

`track_peers` itself awaits that same thread: `VolatileTipEffect` (`track_peers/mod.rs:993` and `:1086`) goes through `Ledger::volatile_tip` → `BlockValidator::request` (`effects/ledger_effects.rs:123–125`, `block_validator.rs:302–305`). A full `track_peers` mailbox plus an in-flight `volatile_tip` plus a stake rotation already running on the ledger thread is a wait cycle. The “ledger is a delay” assumption is false for this callback. Other ledger queries (`ValidateBlock`, `registered_relay_candidates`, tx validation) share the thread, so they inherit the same stall.

`Performance` and the chain store do not have this shape.

## 3. What the typestate API already captures

`make_states!` / `on_receive!` build a `TypeGraph` (`typestate/session.rs:195–221`): per state, per input, a remainder of `EffectAst` (`typestate/list.rs:762–776`). Variants include `Send`, `Call`, `SendAny`, `External`, `Detach`, `Wait`, `SetTimeout`, `Schedule`, `Terminate`, `AddStage`. There is no `TrySend`. `Send` in this API is the blocking session send.

`Proto::type_graph()` is implemented for protocols that use the macros. On this tree that is blockfetch initiator/responder and forge (`blockfetch/initiator.rs:70–90`, `blockfetch/responder.rs:46–58`, `forge_block/protocol.rs:45–130`). Consensus stages (`manager`, `peer_selection`, `track_peers`, `select_chain`, `fetch_blocks`, …) are plain `async fn` transitions. They do not appear in any `TypeGraph`.

`project` (`session.rs:730`) turns a `TypeGraph` into a communicating finite-state machine of **wire** send/recv for one protocol role. Plumbing and local effects are hidden. It checks the protocol against the network spec (`blockfetch/spec.rs:91–95`). It does not emit mailbox ids, capacities, blocking-versus-timeout, fan-in, or who else sends to the same mailbox.

Blockfetch’s graph does show the two mux edges the runtime uses:

- `Call<ToResponder, _>` with `TIMEOUT = NETWORK_SEND_TIMEOUT` (`initiator.rs:77–78`, `153–157`) → `timeout`
- `Send<ToMux, WantNext>` (`initiator.rs:82–87`) → `blocking`

The generic mini-protocol driver matches that split: `WantNext` is `eff.send`, the wire message is `eff.call` (`miniprotocol.rs:228–235`). Chainsync does not use this typestate; its send to `track_peers` is an ordinary `eff.send` (`chainsync/initiator.rs:169–173`).

So `type_graph` + `project` can list Send/Call remainders of the few typestate handlers. They cannot produce the wait graph. Missing: untyped stages, target mailbox identity (roles are `ToMux` / `ToCollector`, not stage names), capacity, fan-in, `try_send` versus `send`, call timeout versus unbounded send, dynamic spawn, supervision, and the ledger-thread callback.

## 4. Template wait graph and blocking cycles

Per-peer stages are one template, copied per connection. Core stages are shared. External effects that match the assumption are drawn as `delay` and are not part of a buffer cycle.

### Blocking cycles present on this commit

These are cycles of `blocking` edges only. Each side parks without receiving. This does **not** prove they fill in production. It proves the edge labels alone do not satisfy “every cycle has a non-blocking edge”.

1. **Chain pipeline, three stages, all capacity 10.**
   - `select_chain` → `fetch_blocks`: `eff.send(downstream, NewBestTip)` (`select_chain/mod.rs:305`)
   - `fetch_blocks` → `validate_block`: `eff.send(downstream, downloaded)` (`fetch_blocks/mod.rs:310`, also `:395`, `:641`)
   - `validate_block` → `select_chain`: `eff.send(select_chain, block_validation_result)` (`validate_block/mod.rs:111–115`)
   - Shorter cycle inside that: `select_chain` → `fetch_blocks` → `select_chain` via `FetchNextFrom` (`fetch_blocks/mod.rs:758`)

2. **Mux and one handler (per connection).**
   - mux → handler: `eff.send(handler, FromNetwork)` while assembling an ingress message (`mux.rs:846` and `:858`)
   - handler → mux: `eff.send(muxer, WantNext)` (`miniprotocol.rs:228`; blockfetch remainder `Send<ToMux, WantNext>`)
   - The handler’s wire `Send` is a `call` with a 1s timeout, so that edge is `timeout`, not part of this cycle.
   - Fan-in: up to ten handlers share one mux mailbox of 24 (`mux.rs:57–62`). Mux blocked on handler A’s full mailbox stops mux receiving, so every other handler’s `WantNext` and call-admission wait on that same mailbox.

3. **Chain-sync fan-in (the live analogue of #1475).**
   - each chainsync initiator → `track_peers`: `eff.send(pipeline, ChainSyncInitiatorMsg)` (`chainsync/initiator.rs:169–173`)
   - `track_peers` → that initiator: `eff.send(handler, RequestNext)` and `Done` (`track_peers/mod.rs:877`, also `:911`, `:931`, `:1015`, `:1049`, `:1063`)
   - `track_peers` capacity is 10, not scaled by peer count (`build_stage_graph.rs:112`). Initiator capacity is 14. Hundreds of peers share the one mailbox of 10. A initiator blocked on `track_peers`, and `track_peers` blocked on `RequestNext` into that initiator, is a two-cycle of `blocking` edges. Not executed here.

`peer_selection` → `manager` is still `blocking` (`peer_selection/mod.rs:111`, call sites `:339`, `:359`, `:782`, `:894`, `:945`, `:1219`). `manager` has **no** send back to `peer_selection` (no `peer_selection` identifier in `crates/amaru-protocols/src/manager`). That historical 2-cycle is gone. The `SendBudget` only caps how many blocking sends one round attempts.

### Edges that are not buffer cycles

- `connection` → `manager` handshake: `call`, 10s (`connection.rs:454`). Manager answers on the oneshot (`manager/mod.rs:519`, `:560`).
- Reader → socket: first header byte has `timeout: None` (`mux.rs:495–497`). That is `peer-unbounded`. The following header and body use the SDU timeout (`:509`, `:556`). After a segment, the reader `send`s `FromNetwork` to mux (`mux.rs:573`) and only then does mux ask for the next read (`:463`).
- Writer → socket: SDU timeout, and the connection implementation also wraps `write_all` in 100s (`network/connection.rs:328`). Then `Written` is a blocking send back to mux (`mux.rs:382`).
- `peer_selection` → `Performance::query_peer_view` and similar: `delay`.
- `ledger-check` child reads the ledger and writes `set_ledger_candidates` (`peer_selection/mod.rs:1283–1298`). It does not send to the parent. `delay`, except when the ledger thread is inside the stake callback above.

## 5. Mux ingress when a handler mailbox is full

Mux does not drop and does not fault. `PerProto::received` blocking-sends each extracted message to the handler (`mux.rs:842–848`). That parks the mux transition.

The next `Read` is sent to the reader only after `received` returns (`mux.rs:453–464`). The reader is idle, not inside `recv`, so the socket is not read. The kernel window closes and the peer’s send blocks. The peer is pulled into the wait only as TCP backpressure, after the internal `mux → handler` send is already parked.

`WantNext` with nothing buffered only increments `wanted` (`mux.rs:859–862`). It does not send. The stall is the `FromNetwork` send, not `WantNext` by itself.

A full mux mailbox parks the reader on `FromNetwork` (`mux.rs:573`) the same way. The reader has already finished `recv` for that segment.

## 6. Lifecycle

- Send to a **terminated** stage: simulation drops and resumes the sender (`simulation/running/mod.rs:1307–1308`). Tokio: receiver dropped ⇒ `send` returns `Err` immediately, ignored (`tokio.rs:726`). The sender map entry is not removed; the closed sender stays. A name never inserted panics.
- Call to a gone or blackhole target waits out the deadline, then `NotAdmitted` (`effect.rs:321–322`, `tokio.rs:647–650`). It does not finish early.
- `try_send` to a closed or missing stage is `Gone` (`tokio.rs:754`).
- Child exit delivers `CanSupervise(name)` or a custom tombstone on the **priority** path (`tokio.rs:857–861`), not the bulk mailbox. The parent receives it ahead of bulk mail (`tokio.rs:452–455`). Unsupervised tombstone (`CanSupervise`) stops the parent (`:467–470`).
- Connection shutdown is `eff.terminate()` (handshake refusal at `connection.rs:431`). Manager learns it from the supervised tombstone `ConnectionDied` (`manager/mod.rs:479`, handled `:849`). Current `connection_died` (`:651`) closes the socket and updates local state. It does **not** send to `peer_selection`. It records the close on the peer-tracking resource (`record_closed`, `:949–951`), a `delay`.
- Disconnect of a live bearer is a blocking `ConnectionMessage::Disconnect` to that connection stage (`manager/mod.rs:946`).

## 7. Scheduler

Production: `TokioBuilder::run` spawns one task per static stage on a Tokio handle (`tokio.rs:188–198`, used from `build_node.rs`). There is no pure-stage run queue. A stage parked on `send` is a task waiting on `mpsc`. Other stage tasks run. Tokio is work-stealing and cooperative; pure-stage states no fairness bound. A `wrap_sync` store read runs on the stage task inside `run()` and holds that worker until the read returns. The interpreter yields only between effects, and only if 100ms have passed (`tokio.rs:787–790`).

Simulation: one stage at a time. Default strategy is FIFO on the runnable deque (`simulation_builder.rs:283`, `random.rs:35–39`). `RandStdRng` picks uniformly. Neither is round-robin over stages. A stage that becomes runnable often can starve another under FIFO only in the sense of queue order; a custom strategy can defer a stage on purpose (the #1475 repro did). Blocked sends are not runnable. `send_cycle` (`simulation/running/mod.rs:1847`) reports stages that lie on a cycle of **currently parked sends**. That is a dynamic check of `blocking` edges only, not of calls, peer I/O, or the ledger callback.

## 8. Pre-#1475 lockup

Fix commit **`dcffd9dcbbef45b2df3dd75a00416004be6d8f9a`** (Roland Kuhn, 2026-10-12), message “rework peer sharing resource to remove pure-stage messaging cycles”, body `fixes #1454, #1475`. It is an ancestor of `33d62a6f1`. Merged as #1502 (`93afff843`). Parent, the pre-fix tree: **`9a4273855972f9efcfbb84579a3f63084d030eda`**.

On that parent, both directions are unbounded `eff.send`:

- manager → `peer_selection`, while handling a manager message (so manager is not receiving):
  - `ConnectFailed` `manager/mod.rs:366` and `:591`
  - `Connected` `:499`
  - `Disconnected` `:526`, `:536`, and `connection_died` `:575`
  - `ShareRequest` `:744`
- `peer_selection` → manager, while handling the notify (so peer selection is not receiving):
  - `AddPeer` `peer_selection/mod.rs:563` and `:1056`
  - `Disconnect` `:1067`, `:1088`, `:1122`
  - `RemovePeer` `:496`
  - `SetLocalUse` `:694`, `:732`
  - `ConnectFailed` / outbound `Disconnected` call `regulate_peers`, which is the path that sends `AddPeer`

Same construction as above: both edges are `blocking`. With mailboxes of 10 and 24 injector handshakes, manager can fill `peer_selection` and park on the next notify while `peer_selection`, once scheduled, parks on `AddPeer` / `Disconnect` / `SetLocalUse` into the manager mailbox manager is not draining. That is a blocking-only cycle. The historical test commit `10f60eb22` (“same injector burst no longer blocks manager on peer selection”) describes that schedule: defer manager and peer selection, 24 upstreams, `DEFAULT_MAILBOX_SIZE`, stop when manager is parked sending to peer selection. That commit is **not** an ancestor of this `main`; the parent sources above are.

On `33d62a6f1` the manager→`peer_selection` sends are gone. Handshake and death go to `PeerTrack::record_connection_established` / `record_connection_closed` (`manager/mod.rs:932`, `:951`), which wait on the performance worker (`delay`), not on the peer-selection mailbox. `peer_selection` still blocking-sends to manager, but nothing in the manager transition sends back, so that pair is not a cycle. The fix removes the cycle. It does not remove the other `blocking` cycles in section 4.

## What this does and does not show

The method can be applied by hand to the edges above, and it does separate the #1475 cycle from the current manager/peer-selection pair. It does not yet show deadlock freedom. Three `blocking`-only cycles are still in the template (chain pipeline, mux/handler, chainsync/`track_peers`), and the stake-distribution callback is an internal wait on `track_peers`. `TypeGraph::project` does not emit those edges. A later extractor has to see untyped `eff.send` / `eff.call`, mailbox capacities, dynamic names, and the ledger-thread callback, and it has to treat `external` / timers as `delay` unless the effect waits on a stage.
