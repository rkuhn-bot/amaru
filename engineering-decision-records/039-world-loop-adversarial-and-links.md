---
type: architecture
status: proposed
---

# Adversarial behaviour and network faults in world-loop tests

Extends [EDR-011](./011-deterministic-simulation-testing.md).

## Context

The world loop is the discrete-event network from [EDR-011](./011-deterministic-simulation-testing.md). `WorldConnectionProvider` owns the `(time, sequence)` heap, and `WorldLoop` is the only popper (`world_connection_provider.rs:127-133`, `world_loop.rs:55-60`). Line numbers are from `rk/tui-up-dn` at `57af57c39` unless noted.

A `send` completes at the current simulated time and schedules a `Deliver` of the whole buffer (`world_connection_provider.rs:659-671`). The inbox is unbounded (`world_connection_provider.rs:290`). Delay is a seeded sample chosen at construction, independent of size (`world_connection_provider.rs:535-541`), and a later `Deliver` on the same connection waits behind the previous one (`world_connection_provider.rs:544-549`). A connect to an address with no listener is refused when the 1–5ms handshake hop pops (`world_loop.rs:472-506`), the round trip a TCP RST takes after the SYN. `close` fails both halves at once (`world_loop.rs:563-572`). The production provider shuts down the write half (`crates/amaru-network/src/connection.rs:357-365`). `local_addr` on this branch returns `NotFound` (`world_connection_provider.rs:685-688`).

`SimulationRunning::breakpoint` takes `Fn(&Effect) -> bool` (`crates/amaru-pure-stage/src/simulation/running/mod.rs:241-243`). `run_effect` pauses before interpreting a match (`running/mod.rs:1045-1051`). `WorldLoop::new` installs `world_external` on every `Effect::External` (`world_loop.rs:117-119`) and treats every `Blocked::Breakpoint` as that hook (`world_loop.rs:361-363`).

`override_external_effect` replaces or handles one external effect, counted by `remaining` (`running/mod.rs:255-268`, `:1639-1654`).

`test_peer_share_reply_addresses` on `rk/share-own-address` (`7673dc2cf`, `generated.rs:825`) builds the share scenario from chain injectors and marks a peer adversarial by enqueueing `PeerSelectionMsg::adversarial` onto `peer_selection-2` (`generated.rs:925-929`).

## Decision

### Scenarios

A peer-sharing scenario, and any gossip scenario of the same kind, is about twenty real nodes with no chain and no injectors. Chain-sync scenarios keep `spawn_injector` and `world_with_injector`.

### One node

Rewriting one external effect on one node is `override_external_effect`. One send is `remaining: 1` and `OverrideResult::replaced`.

### World breakpoint

A world breakpoint has a name chosen by the scenario and one closure:

```rust
Fn(&Effect, Instant, usize) -> Option<(Vec<WorldEffect>, Keep)>
```

The trace highlights that name on a hit. The same name may be installed on any number of nodes. Registering a name that is already in use panics. `world_external` is reserved for the world loop, and reusing it panics too.

`SimulationRunning::breakpoint` takes `Fn(&Effect, Instant) -> bool`, passing `self.now()` (`running/mod.rs:320-321`). Callers of today's `Fn(&Effect) -> bool` take that `Instant`. The node index comes from a wrapper `WorldLoop` builds for each installed node.

The closure runs twice on a hit. The wrapper's predicate is `on_hit(effect, now, index).is_some()`. `None` leaves the run going, and the closure is not called again. On `Some`, handling `Blocked::Breakpoint` calls `on_hit` again with the same arguments and uses that `Vec` and `Keep`. The closure is pure: the same inputs return the same `Option`.

The world applies the `Vec` in order, records the name, the paused effect, and each `WorldEffect`, then `interpret_breakpoint` (`running/mod.rs:938-941`). `Keep::Detach` removes the breakpoint from the node that paused. `Keep::Attach` leaves it. Other nodes that carry the same name stay as they are.

`at(Instant, Vec<WorldEffect>)` applies that vector, in order, when simulated time reaches the instant, and records each effect.

`WorldEffect` gains variants as scenarios need them. The initial variants are `SetLink` and `CloseConnection`. `CloseConnection` is an orderly close, the write shutdown the production provider already performs. A reset effect is added later, on the real network and on the simulated one.

### Adversarial classification

The receiving node classifies a peer from the bytes it reads. The scenario produces those bytes with an effect override on the sending node, or with a world breakpoint on that send.

### Connection provider

`WorldConnectionProvider` follows TCP/IP for the behaviours below. Per-connection FIFO stays.

- A send completes when its bytes fit in the send buffer. A full receive window parks further sends in that direction.
- Orderly close shuts down one write half. Data already accepted on that half is still delivered. Reset, once that effect exists, fails both halves and discards buffered bytes.
- Once the listen backlog is full, a further connect is refused or times out.
- `pending_handshakes` is bounded. Handshakes past the cap are refused.
- An established bearer has a concrete local address. The outbound port comes from a deterministic ephemeral allocator. The inbound local address is the listener. `local_addr` returns that socket, and the peer identity uses the same address.

### Links

A link is every connection from node index `from` to node index `to`, those that already exist and those opened later. The opposite direction is another link.

Arrival of a send is

```text
base + (size / rate) * max(1, W_full / max(w, W0))
```

queued so it cannot pass an earlier send on the same link. `w` is a decaying exponential moving average of bytes recently sent on the link. `W0` is about ten segments, about 14 KB. `w` resets after about one retransmission timeout of idle. The update runs when the heap pops the send. A scenario that leaves a link unconfigured keeps the seeded hop the provider already draws.

Packet loss is added delay. A delay past the scenario horizon delivers nothing and shows no close. The delay value may exceed the horizon. `PeerDisconnect` remains an abrupt close of a live pair.

`Apply::Prospective` is the default. Sends issued after the change use the new delay and rate. Sends already scheduled keep their arrival. A later send still waits behind an earlier one: its arrival is at least the previous send's.

`Apply::Retroactive` re-times every not-yet-delivered send on that direction. The world keeps, per direction, a queue of those sends, each with its base send time, size, and the extra-delay factor it was given. A change recomputes `sent_at + delay + (size / rate) * extra` with the new parameters, then walks the queue in order and raises each arrival to at least the previous one. A retroactive delay past the horizon holds the queue. A later retroactive `SetLink` inside the horizon releases it in that order.

```rust
enum Keep {
    Attach,
    Detach,
}

/// `Prospective` is the default.
enum Apply {
    /// In-flight sends keep their scheduled arrival.
    Prospective,
    /// Re-time every not-yet-delivered send on this from->to direction.
    Retroactive,
}

enum WorldEffect {
    SetLink { from: usize, to: usize, delay: Duration, rate: u64, apply: Apply },
    /// Orderly close. Reset is a later variant, on the real network and the simulated one.
    CloseConnection { conn: ConnectionId },
}

impl WorldLoop {
    /// `name` is highlighted in the trace on a hit.
    /// A name already in use panics. `world_external` is reserved and panics if reused.
    ///
    /// `on_hit` runs twice per hit. The predicate is `on_hit(effect, now, index).is_some()`.
    /// `None` leaves the run going. On `Some`, handling `Blocked::Breakpoint` calls `on_hit`
    /// again with the same arguments. The closure is pure.
    pub fn breakpoint<F>(&mut self, name: &str, nodes: impl IntoIterator<Item = usize>, on_hit: F)
    where
        F: Fn(&Effect, Instant, usize) -> Option<(Vec<WorldEffect>, Keep)> + Send + 'static,
    {
    }

    pub fn at(&mut self, at: Instant, effects: Vec<WorldEffect>) {}
}
```

## Consequences

- Gossip scenarios are nodes. The chain, the injectors, and the reveal schedule stay with chain-sync.
- A hit is recorded under the name the scenario chose, with the paused effect and each `WorldEffect`.
- A world-breakpoint closure returns the same value for the same effect, time, and node index, because a hit evaluates it twice.
- `Apply::Prospective` leaves in-flight arrivals in place, and FIFO keeps a later send behind them. `Apply::Retroactive` moves the whole pending queue.
- The receiver's classification is the adversarial mark. The share scenario's adversary is a sender whose bytes were modified.
- `CloseConnection` matches production write shutdown. Reset is its own later effect on both networks.
- A duplicate breakpoint name, including `world_external`, panics at registration.

## Alternatives considered

### Enqueue `PeerSelectionMsg::adversarial`

`test_peer_share_reply_addresses` does this (`generated.rs:925-929` on `rk/share-own-address`). The mark then exists with no bytes for the receiver to judge. The receiver classifies the peer from the bytes the scenario arranged.

### Stage-name injection

`WorldLoop::enqueue` with `StageRef::named_for_tests("peer_selection-2")` ties each fault to a stage name. Faults are world breakpoints and time checkpoints.

### Two closures

A predicate and a separate action closure can disagree, and they observe the clock at different moments. One closure is evaluated twice, and purity makes both results the same hit.

### `WorldView`

Time and the node index are arguments. The node index is closed over by the per-node wrapper.

### Generated names

The trace shows the name the scenario wrote.

### Byte rewrite as a `WorldEffect`

One external effect is `override_external_effect`. A world breakpoint matches the send whose bytes the receiver will read. `WorldEffect` starts as link delay and rate, and orderly close.

### A congestion window

Warmth `w` is the slow-start term, with one FIFO queue per link.

### A silent-failure event

A delay past the horizon leaves the hop undelivered and unclosed (`world_connection_provider.rs:349-355`). `PeerDisconnect` is the abrupt close.

### A stub peer for gossip

A stub that answers share requests skips the bearer and the performance row the scenario asserts.

## References

- [EDR-011](./011-deterministic-simulation-testing.md)
- `test_peer_share_reply_addresses` on `rk/share-own-address` ([#41](https://github.com/rkuhn-bot/amaru/pull/41))
