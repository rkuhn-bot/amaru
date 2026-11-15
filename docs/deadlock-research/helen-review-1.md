# Helen review 1 of wait-graph-inventory (33d62a6f), 2026-11-15
1. Credit-bounded blocking edges: blocking edge M1→M2 counts as non-blocking if an invariant caps in-flight msgs on it below M2's free capacity, counting EVERY producer of M2 (stages, detach tasks, input senders, ledger callback) and every message kind. State the bound per edge, or say there is none. Expected: mux↔reader/writer discharged (at most 1 Read/Written outstanding); mux→handler FromNetwork discharged iff mux pushes only when wanted>0 (check mux.rs:842–862); handler→mux: 10 handlers×(WantNext+call admission)+FromNetwork+Written ≤ 24?; track_peers→initiator: RequestNext as credit ≤ pipeline depth, Done and other sends (lines 911, 931, 1015, 1049, 1063) must fit in the +4.
2. Cycle (a) chain pipeline is likely real (range fetch emits many blocks; select_chain also gets fan-in from track_peers). Repro in sim with #1475-style deferring strategy, catch-up, N≥3. Fix: select_chain→fetch_blocks becomes last-value/overwrite (resource + coalescing wakeup), like the Haskell 10 ms (Genesis 40 ms) STM poll. Validation results are not lossy; keep that edge blocking.
3. (c): no drop (corrupts candidate fragment), no disconnect (eclipse lever). Make track_peers→initiator credit-bounded and keep initiator→track_peers blocking (acyclic backpressure). Fairness: per-peer quota q, or capacity ≥ N·q, or per-peer candidate state in a resource (Haskell: per-client thread + TVar). Header path ~10 ms/hop; GDD needs candidates fresh within ~1 s.
4. (b): teardown is OK only if overflow implies a protocol violation. Size handler ingress (msgs+bytes) to the legal max given in-flight requests, and tear down on excess. HOL blocking stalls keep-alive, so the remote kills us after 97 s. Haskell demux never blocks.
5. Missing edges: priority mailbox full (tombstones/timers as wait edges); connection's outgoing sends (manager→connection Disconnect is blocking, so any blocking connection→manager send closes a cycle); exhaustive transitive closure (every eff.send/send_any/input sender, with a grep count); internal 1 s call timeout on handler→mux: on expiry, bearer teardown or typestate desync? caller behaviour on None, and retry loops (livelock); wrap_sync never waits on a stage (one line of proof per effect); sim drops a send to an unknown stage, tokio panics.
6. Ledger callback is a real violation. Fix: coalescing non-blocking notify (data is already in resources.put). Definition: a callback on an effect's thread is part of that effect and may not wait on a stage.
7. Acceptance: 9a4273855 fails and 33d62a6f passes; the checker must flag the ledger callback (non-stage producer) and must discharge mux↔reader by credit.

## CORRECTION (Roland via Helen, 2026-11-15): Haskell node is NOT an authority
Drop every "Haskell does X, so do X". Re-ground on generic theory:
- Credit-bounded edges = buffer accounting (per edge/producer in-flight ≤ k, sum ≤ capacity); Parks 1995, Dally & Seitz 1987.
- Last-value edges sound iff the message type is superseding (receiver depends only on the latest value, or on the join of a semilattice). NewBestTip/FetchNextFrom must be shown superseding from Amaru semantics. Validation results are not superseding.
- Ingress teardown is safe iff buffer ≥ protocol-legal outstanding amount from the mini-protocol session type (agency/pipelining).
- Disconnect-on-slowness and dropping stateful-session msgs: generic security arguments.
- Ledger callback: generic (a callback on an effect's thread belongs to the effect).
Ouroboros inputs, papers only: Δ-bounded delivery (Praos); per-peer candidates, with Genesis density needing all of them; honest parties tolerate any number of adversarial peers given one honest path.
The 10 ms/hop and GDD ~1 s figures are Haskell constants: at most a labelled design target. The 10/60/97 s timeouts are only environment data on remote peer behaviour.
Haskell's lack of a proof: mention once, as motivation ("acyclic by design + testing" is not enough), never as a model.

## REFINEMENT (Roland via Helen): Haskell as inspiration
A Haskell pattern may be cited as where an idea came from, never as the goal or the justification. Justification must be generic or come from Amaru semantics.

## BINDING RULE (Roland via Helen): dropping messages
- Drop/overwrite ONLY superseding messages (e.g. tip updates). Never drop where delivery is needed for correctness (no resend schemes).
- Main theorem: deadlock freedom with reliable sends kept as they are, under concrete per-actor mailbox sizes; mailboxes may be enlarged.
1. Classify each edge as reliable or superseding (superseding argued from Amaru semantics).
2. For every cycle of reliable blocking edges: occupancy bound per edge summed over all producers (fan-in, detach tasks, input senders, callbacks) < receiver capacity; required capacity as a function of N peers, pipeline depth and targets, compared with the current constants.
3. Where no bound exists (unbounded fan-in or per-request bursts, e.g. block range fetch_blocks→validate_block), fix with a structural credit/flow bound, not a drop.
4. Output table: mailbox | required capacity formula | current value | sufficient?
