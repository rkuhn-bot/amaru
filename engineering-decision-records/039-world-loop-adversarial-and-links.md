---
type: architecture
status: proposed
---

# Adversarial behaviour and network faults in world-loop tests

Extends [EDR-011](./011-deterministic-simulation-testing.md).
Status is proposed. This record comes from the 2026-10-11 design review of `test_peer_share_reply_addresses` on `rk/share-own-address` ([#41](https://github.com/rkuhn-bot/amaru/pull/41)).

Line numbers below are from `rk/tui-up-dn` at `57af57c39` unless the citation says `rk/share-own-address` (`7673dc2cf`). The share scenario and `WorldLoop::enqueue` exist only on that branch.

## Context

[EDR-011](./011-deterministic-simulation-testing.md) runs a network of nodes on one discrete-event heap so a failing seed can be replayed.
The world loop is that simulator: `WorldConnectionProvider` owns the `(time, sequence)` heap, and `WorldLoop` is the only popper (`world_connection_provider.rs:127-133`, `world_loop.rs:55-60`).

Peer sharing was the first gossip scenario hung on that harness.
`test_peer_share_reply_addresses` (`generated.rs:825` on `rk/share-own-address`) builds eleven chain injectors (`SHARE_INJECTORS`, `generated.rs:800` and `:842-847`), two further injectors standing in for a never-dialed address and an adversarial peer (`generated.rs:849-852`), and six nodes through `spawn_catch_up` (`generated.rs:912-921`).
The first injector is attached with `with_injector`, and `schedule_reveals` publishes a one-header chain (`generated.rs:838`, `:923-924`).
Those injectors, and the reveal path, are the sync-test helpers `spawn_injector`, `world_with_injector`, and `spawn_catch_up` (`generated.rs:144-167` and `:206-208` on this branch; `generated.rs:149-172` and `:211-213` on `rk/share-own-address`).
A search of `crates/amaru-node/src/tests/world` on both branches finds no ejector.
The assertions read share replies, so chain-sync is not the behaviour under test.

The same scenario marks a live peer adversarial by putting `PeerSelectionMsg::adversarial` on a mailbox the test names itself.
After 60s of simulated time it looks up `peer_selection-2` and calls `WorldLoop::enqueue` with `StageRef::named_for_tests` (`generated.rs:925-929` on `rk/share-own-address`).
`enqueue` is `world_loop.rs:152-160` on that branch and is absent from `rk/tui-up-dn`.
The stage graph constructs the stage as `"peer_selection"` (`build_stage_graph.rs:91`); the test then has to know the suffixed name the running graph actually has.
That couples every future fault to a stage name and a message variant.

The provider under both branches is a delayed byte pipe, not a TCP stack.

- A `send` whose peer endpoint still exists schedules `SendAck` at the current simulated time and a `Deliver` of the whole buffer (`world_connection_provider.rs:659-671`).
  The inbox is an unbounded `VecDeque` (`world_connection_provider.rs:290`).
  Nothing in that path consults how much the peer has already read.
- `Deliver` times are a seeded sample in a range chosen when the provider is built (`world_connection_provider.rs:300-313`, `:535-541`).
  The sample does not depend on the number of bytes.
  The long-tail bucket is capped at `HONEST_PAYLOAD_DELAY_MAX_NANOS`, five preprod slots (`world_connection_provider.rs:36-41`).
- One destination stays in order: a later `Deliver` is pushed out to `max(hop, last_deliver_at)` (`world_connection_provider.rs:270-272`, `:544-549`).
- `connect` always enqueues a handshake hop in the 1–5ms wire range, plus a timeout (`world_connection_provider.rs:644-656`, `:531-532`).
  Refusal is decided when that hop pops: no listener yields `"connection refused"` (`world_loop.rs:472-506`).
  The refusal therefore waits out the wire delay.
- `listen` stores an unbounded `pending_handshakes` queue (`world_connection_provider.rs:281-282`, `:621-629`).
- The peer address of an outbound bearer is synthesised as `127.0.0.1:(5000 + connection id)` at pair time (`world_connection_provider.rs:614`; the same formula is `tests.rs:78-79`).
  On this branch `local_addr` returns `NotFound` for every connection (`world_connection_provider.rs:685-688`).
  On `rk/share-own-address` the endpoint stores that ephemeral address for the initiator and the listener address for the responder, and `local_addr` returns it (`world_connection_provider.rs:293-294`, `:593-613`, `:687-691` on that branch).
- `close` schedules `Close` with a zero delay (`world_connection_provider.rs:680-682`).
  The loop removes the endpoint, fails in-flight sends and recvs on both halves, and schedules `Close` for the peer.
  The comment on that arm calls the result an RST visible on both halves at once (`world_loop.rs:563-572`).
  `ConnectionProvider` exposes `close` and no separate write shutdown (`crates/amaru-ouroboros-traits/src/connections/connection_provider.rs:40`).
  The production provider shuts down the write half (`crates/amaru-network/src/connection.rs:357-365`).
- Abrupt faults are a different heap event. `schedule_peer_disconnects` plants `PeerDisconnect` hops, and popping one picks a live pair and runs the same `Close` path (`world_connection_provider.rs:162`, `:455-479`; `world_loop.rs:575-577`).
- A hop whose time is past the horizon is left on the heap (`world_connection_provider.rs:349-355`).
  There is no per-link delay the scenario can change after `new`.

`SimulationRunning::breakpoint` installs a named predicate `Fn(&Effect) -> bool` (`crates/amaru-pure-stage/src/simulation/running/mod.rs:241-243`).
`run` stops before the matching effect is interpreted (`running/mod.rs:66-68`, `:1045-1051`) and returns `Blocked::Breakpoint` (`crates/amaru-pure-stage/src/simulation/blocked.rs:28-30`).
The caller inspects the effect with `breakpoint_effect` (`running/mod.rs:921-924`), then either `interpret_breakpoint` (`running/mod.rs:938-941`) or `discard_breakpoint` (`running/mod.rs:931-933`).
`WorldLoop::new` installs one such breakpoint, `world_external`, matching every `Effect::External` (`world_loop.rs:117-119`).
`run_graph_until_clock` treats every `Blocked::Breakpoint` as that network hook and interprets it immediately (`world_loop.rs:361-363`, `:378-385`).
No scenario action runs at that pause.

The manager/peer-selection repro ([#37](https://github.com/rkuhn-bot/amaru/pull/37), `rk/repro-manager-peerselection-deadlock`) is the other caller this work has to serve.
It drives one node against many injectors, holds wire delay fixed, and uses one timestamp of `PeerDisconnect` to close most connections together (`crates/amaru-node/src/tests/world/deadlock.rs:15-27` on that branch).
That file is not on `rk/tui-up-dn`.

## Decision

Gossip scenarios and network faults stay inside the world loop.
They stay deterministic, and every trigger and action is visible in the traces the tests already read: the heap log (`HeapLogEntry`) and the stage trace.

### Scenario shape

A peer-sharing scenario, and any later gossip scenario of the same kind, is a set of real nodes with no chain.
About twenty nodes is the size we are aiming at.
The scenario does not spawn injectors or ejectors, and it does not reveal headers.
Chain-sync stays in the sync scenarios that already use `spawn_injector` and `world_with_injector`.

### Adversarial behaviour

Two different jobs.

Single-node tinkering rewrites one external effect on one `SimulationRunning`.
That is the existing override, not a world action.
`override_external_effect` takes a remaining count and a transform (`crates/amaru-pure-stage/src/simulation/running/mod.rs:255-268`).
`usize::MAX` keeps the override; any smaller count is removed after that many applications (`running/mod.rs:257-258`, `:1702-1708`).
`OverrideResult::no_match` passes the effect on, `handled` substitutes the stage response, and `replaced` substitutes another effect of the same response type (`running/mod.rs:1639-1654`, enum at `:1674-1680`).
The running simulation applies that when it is about to run an `Effect::External` (`running/mod.rs:1301-1310`).
Rewriting one message send is one such override with `remaining: 1` and `replaced`.
The world breakpoint does not do it.

World behaviour is a named breakpoint plus time checkpoints.

A world breakpoint is an author-chosen name, a predicate over `&Effect`, and a closure:

```rust
fn on_hit(effect: &Effect, view: &WorldView) -> (WorldEffect, Keep)
```

The name is the label the execution trace highlights when the breakpoint hits.
The same name can be installed on any number of simulated nodes.
The predicate is the one `SimulationRunning::breakpoint` already takes (`running/mod.rs:241-243`): the run pauses on `Blocked::Breakpoint` before the effect is interpreted.
`run_graph_until_clock` tells this name apart from `world_external` (`world_loop.rs:361-363`).
`world_external` stays the network hook (`world_loop.rs:117-119`, `:378-385`).

On a hit the world calls the closure, applies the returned `WorldEffect`, and records the breakpoint name, the paused effect, and the `WorldEffect` in the trace.
It then `interpret_breakpoint` (`running/mod.rs:938-941`), so the paused effect still runs.
`Keep::Detach` removes the breakpoint from the node that paused.
`Keep::Attach` leaves it installed.
One-shot versus standing is that return value, decided on each hit.
Other nodes that carry the same name are left as they are.

`WorldView` starts with only the current simulated time.
Fields are added when a closure needs them.

`WorldEffect` is a small enum.
The first variants cover “do nothing”, “set a link’s delay and rate”, and “close a connection”.
Later variants extend the enum.
The exact starting set is open; see Discussion points.

A time checkpoint is the other trigger.
When simulated time reaches it, the world applies a `WorldEffect` and records that in the trace.
There is no paused effect.
“After time T, the next effect that matches P” arms the named breakpoint when the clock passes T.

```rust
/// Decided on each hit. Detach removes the breakpoint from the node that paused.
enum Keep {
    Attach,
    Detach,
}

/// What the closure may read. Starts as the clock; grows on demand.
struct WorldView {
    now: Instant,
}

/// Applied by the world at a breakpoint hit or a time checkpoint.
/// The link selector and the exact variant list are open.
enum WorldEffect {
    None,
    SetLinkDelayAndRate { delay: Duration, rate: u64 },
    CloseConnection { conn: ConnectionId },
}

impl WorldLoop {
    /// `name` is chosen by the scenario and highlighted in the trace on a hit.
    /// The same `name` may be installed on any number of `nodes` (graph indexes).
    pub fn breakpoint<P, F>(
        &mut self,
        name: &str,
        nodes: impl IntoIterator<Item = usize>,
        predicate: P,
        on_hit: F,
    ) where
        P: Fn(&Effect) -> bool + Send + 'static,
        F: Fn(&Effect, &WorldView) -> (WorldEffect, Keep) + Send + 'static,
    {
    }

    /// Other trigger: apply `effect` when simulated time reaches `at`.
    pub fn at(&mut self, at: Instant, effect: WorldEffect) {}
}
```

### Connection-provider realism

`WorldConnectionProvider` grows the TCP/IP behaviour the production socket already has, still as one deterministic heap.
Per-connection FIFO stays (`last_deliver_at`).

- Backpressure.
  Each direction has a send buffer and a receive window.
  A `send` completes when its bytes fit in the send buffer.
  A slow `recv` leaves the window closed, and further `send`s on that direction stay parked.
  The unbounded inbox and the immediate `SendAck` go away.
- Orderly close and reset.
  Orderly close is a write shutdown of one half, matching `writer.shutdown()` on the production provider.
  Data already accepted on that half is still delivered.
  Reset fails both halves and discards buffered bytes, which is what `NetworkEvent::Close` does today.
- Immediate connection refused.
  A `connect` whose target has no listener fails in the `connect` call, at the current simulated time.
  It does not wait for the 1–5ms wire hop.
  A listener that exists and whose backlog is full is a different outcome (the attempt waits, then refuses or times out).
- Bounded listen backlog.
  `pending_handshakes` has a finite cap.
  Handshakes past the cap are refused.
- Local addresses.
  An established bearer has a concrete local socket.
  The outbound port is an ephemeral port drawn from a deterministic allocator.
  The inbound local address is the listener.
  `local_addr` returns that socket.
  The hard-coded `127.0.0.1:(5000 + connection id)` used as the initiator's peer address today is replaced by the same allocator, so the peer identity and `local_addr` stay one value.

### Link model

On top of that pipe, each link has a base delay and a rate, set by the scenario.
Arrival time of a message is

```text
arrival = base_delay + size / rate
```

queued so it cannot pass an earlier message on the same link.
The current `max(hop, last_deliver_at)` rule is that queue, with `base_delay + size / rate` in place of the seeded hop sample.

The scenario changes a link's base delay and rate while the run is going by returning `WorldEffect::SetLinkDelayAndRate` from a world breakpoint, or by a time checkpoint that applies the same effect.
A breakpoint hit records the name, the paused effect, and that `WorldEffect`.
A time checkpoint records the `WorldEffect` at that instant.
A rewrite of one message on one node stays on `override_external_effect`.

Packet loss is added delay on that message.
There is no separate drop-from-the-link event.
A delay past the scenario horizon is a silent link: `pop_at_or_before` never delivers it, and the peer sees no close.
The delay API accepts values beyond the horizon.
`PeerDisconnect` remains the abrupt-close fault.
Silence is not a second fault type.

Slow start is a warmth term, not a congestion window.
Each link keeps `w`, a decaying exponential moving average of bytes recently sent.
The extra delay grows when `w` is small:

```text
delay = base_delay + (size / rate) * max(1, W_full / max(w, W0))
```

`W0` is about ten segments, about 14 KB.
`w` resets after about one retransmission timeout of idle, by analogy with Linux `tcp_slow_start_after_idle`.
The update runs when the heap pops the send, so the same seed produces the same `w`.
There is no per-segment scoreboard.
A scenario that does not configure a link keeps the seeded hop the provider already draws.

## Consequences

- Gossip tests stop carrying a chain, an injector, and a reveal schedule whose only job is to make `spawn_catch_up` construct a node.
- A world fault is a named breakpoint or a time checkpoint returning a `WorldEffect`.
  It does not grow a `named_for_tests` call site per stage.
  One external effect on one node stays an `override_external_effect`.
- Backpressure, half-close, refusal, and backlog become things a world test can observe, because the production socket already behaves that way and the sim currently does not.
- Silent peers, loss, and a cold link are three settings of one delay formula.
  A test reads them back from the trace instead of inferring them from a missing `Deliver`.
- In-order delivery means a message scheduled past the horizon holds every later message on that link behind it.
  Restoring the link is a later trigger that lowers the delay.
  That interaction is called out under Discussion points.
- Implementing the provider and the link model is a behaviour change for every existing world test.
  The migration section names the first two callers.

## Alternatives considered

### Per-node stage enqueue

`WorldLoop::enqueue` plus `StageRef::named_for_tests("peer_selection-2")` is enough for one adversarial flag.
The review rejected it as the general mechanism: each new fault learns another stage name and another message type, and the injection is invisible to the network trace.
World behaviour is a named breakpoint on the nodes the scenario lists.

### Auto-generated breakpoint names

The world could mint a name when the scenario registers a predicate.
The trace would then highlight an identifier the author did not write.
The decision keeps the name the scenario chooses, and that name is what the trace shows on a hit.

### Rewrite one delivery as a world effect

Dropping or rewriting the bytes of one delivery could have been a `WorldEffect`.
That job is already `override_external_effect` on the one `SimulationRunning` (`running/mod.rs:255-268`, `:1639-1654`).
`WorldEffect` stays the world-scoped operations: link delay and rate, closing a connection, and later extensions.

### Simulate a congestion window

A per-segment window, loss detection, and retransmission would reproduce TCP more closely.
The review rejected that state.
Warmth `w` gives a cold link a larger delay, stays deterministic, and keeps a single FIFO queue per link.

### A separate silent-failure event

A heap event that means “this link is down, deliver nothing, emit no close” duplicates what a delay beyond the horizon already does via `pop_at_or_before`.
The review keeps one knob.
`PeerDisconnect` is unchanged, because an RST is a close the peer observes.

### Give gossip tests a smaller fake peer

A stub that answers share requests without a node would avoid the injector, and it would also skip the bearer, the share initiator, and the performance row.
The scenario exists to assert those.

## Discussion points

These are open.
The decision above does not settle them.

- What a link is.
  One direction of one connection, the pair of directions, a node pair across connections, or a node's uplink.
  And whether a mid-run change applies to bearers that already exist, to bearers opened afterwards, or to both.
  `WorldEffect::SetLinkDelayAndRate` needs that selector.
- The exact starting set of `WorldEffect`.
  The sketch has `None`, a link delay and rate, and close-connection.
  Which of those ship first, and whether close is orderly or reset, is open.
- Name uniqueness, and collision with `world_external`.
  One author-chosen name may be installed on many nodes.
  Whether two registrations may reuse a name for different predicates, and whether `world_external` is reserved, is open.
  `run_graph_until_clock` currently treats every `Blocked::Breakpoint` as the network hook (`world_loop.rs:361-363`).
- Whether an adversarial mark should be the result of behaviour the peer can actually commit (a bad header on the wire, for example) rather than a direct `PeerSelectionMsg`.
  The trigger is a world breakpoint or a time checkpoint either way.
  Which `WorldEffect` or override the share scenario uses is part of the migration, not fixed here.
- In-order recovery.
  Because a late message blocks the rest of the link, a silent link stays silent for later messages until a trigger sets the delay back under the horizon.
  The API has to allow that second update, including for bytes already queued.
- Which work lands first.
  TCP realism (buffers, half-close, refusal, backlog, local addresses) and the link model (rate, warmth, mid-run updates) touch the same `send` / `Deliver` path.
  Doing either one alone still leaves the other half of the review undone.

## Migration

1. Rewrite `test_peer_share_reply_addresses` as about twenty chainless nodes.
   The adversarial peer is a named world breakpoint, installed on the nodes that should hit it, or a time checkpoint that applies a `WorldEffect`.
   A rewrite of one send on one node, if the scenario still needs one, is `override_external_effect` on that node.
   The never-connected address and the listen-address check stay assertions on the trace.
   The injector store, `with_injector`, and `schedule_reveals` leave this scenario.
2. After `WorldEffect::SetLinkDelayAndRate` exists, use a world breakpoint or a time checkpoint in the manager/peer-selection repro ([#37](https://github.com/rkuhn-bot/amaru/pull/37)) so the stall is a property of those links, not only of a fixed wire delay and a `PeerDisconnect` storm.

## References

- [EDR-011](./011-deterministic-simulation-testing.md)
- `test_peer_share_reply_addresses` on `rk/share-own-address` ([#41](https://github.com/rkuhn-bot/amaru/pull/41))
- Manager/peer-selection repro ([#37](https://github.com/rkuhn-bot/amaru/pull/37))
