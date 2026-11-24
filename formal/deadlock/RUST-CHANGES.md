# Rust changes required by the deadlock model

Amaru is unchanged. This list is the production work the Lean model requires
and does not do. Each entry stays `pending` until that Rust change lands.
Line numbers are from the Amaru tree this model was read against.

## 1. Connector workers become ten static stages

- Location: `crates/amaru-protocols/src/manager/connector.rs:32`, `:72-86`
- Change: replace the lazy pool of up to `DEFAULT_PARALLEL_CONNECTION = 10`
  with 10 static stages. `start` creates a `connect-worker-{n}` on demand and
  reuses it from `idle`. That pool goes away.
- Decision: pools removed, 2026-11-23. A connector worker is a fixed stage.
  The model does not invent ten core templates for them.
- Status: pending

## 2. Accept does not terminate

- Location: `crates/amaru-protocols/src/accept.rs:34-36`
- Change: make the accept call a detached effect whose result returns to the
  stage as a message. The stage never terminates on `AcceptError::Other`.
- Decision: N67. The Lean model is a static core. The completion is an
  ingress message (`Accepted` or `AcceptError`) on a non-blocking self-edge,
  and the stage does not terminate. Production is unchanged.
- Status: pending

## 3. No Listen tombstone and no accept respawn

- Location: `crates/amaru-protocols/src/manager/mod.rs:439`, `:861`
- Change: remove the `Listen(addr)` tombstone and the respawn path, or make
  that path unreachable. `:439` supervises the accept stage with
  `ManagerMessage::Listen(listen_addr)`. `:861` handles that message by
  calling `listen` again.
- Decision: N67. The Lean model has no `Listen(addr)` tombstone and no
  respawn. Production is unchanged.
- Status: pending

## 4. Re-issue an accept only after the result is handled

- Location: `crates/amaru-protocols/src/accept.rs:27`, `:39`
- Change: issue the next accept only after the previous result has been
  handled. `Network::new(&eff).accept(...).await` at `:27` is the call.
  `:39` always schedules `PullAccept` after
  `state.manager_config.accept_interval`, including when the result is
  still outstanding and including after `AcceptError::Other` terminates
  the stage at `:34-36`.
- Decision: the Lean model does not issue the accept. The completion is
  environment ingress. Nothing checks that a new accept waits until the
  previous result has been handled. Completions arrive on the bulk lane.
- Status: pending

## 5. Tombstones count toward the priority lane, and overflow crashes

- Location: `crates/amaru-pure-stage/src/simulation/running/mod.rs:1323`
  at fork `main` (`34a45300`), `:1447` in the tree on
  `snapshot/lean-r5-wip` (`af03a9b9e`). `supervisor.tombstones.push_back(msg)`
  appends to an unbounded `VecDeque`. On tokio, `tokio.rs:584` pushes a
  `PriorityMessage::Tombstone` into the receive queue, and the limit at
  `:860-866` counts only schedules.
- Change: bound the tombstone queue. Every queued tombstone counts against
  the stage's priority capacity, next to self-schedules and cell wakes. A
  tombstone that does not fit crashes, like the schedule overflow panic.
- Decision: Roland, 2026-11-20 16:22 CET: tombstones count toward the
  priority lane, overflow crashes, and pure-stage will be changed to match.
  The Lean model does this with `offerPrio`/`crashWorld`, sizes it statically
  with `prioSized`, and proves it does not overflow in `no_tombstone_overflow`.
  This is the DECISIONS.md entry for 2026-11-20, "A slot has one outstanding
  tombstone".
- Status: pending

## 6. Withhold a tombstone until the dead stage's in-flight mail is consumed

- Location: net-new in pure-stage. The tombstone is pushed in the
  terminate path at `simulation/running/mod.rs:1323` (`34a45300`) and on
  tokio at `tokio.rs:850-856` and `:584`.
- Change: tag each message with its sender's slot and generation. A live
  receiver reports when it consumes those tagged messages. A terminated
  stage's tombstone is not delivered while mail from that stage, or from
  the descendants sealed with it, still sits in a live receiver's bulk
  mailbox, priority queue or tokio channel. Mail at a dead receiver counts
  as consumed. Parked sends of the killed stage are dropped at the kill.
  The supervisor does not wait: the tombstone stays queued and is skipped
  (entry 7). The signal is that finite set of messages, never a mailbox
  becoming empty.
- Decision: Roland, 2026-11-21 08:04 and 08:06 CET (drained signal,
  "net-new functionality in pure-stage"), revised 11:46 — 11:50 CET (delayed
  tombstone, applies to every supervisor). In Lean these are `mailInFlight`,
  `tombstoneWaits`, `receivePrio` and `rootOutstanding`, and the occ_head fix
  rests on them (Helen N66). This is the DECISIONS.md entry for 2026-11-21,
  "Implementation work not covered by the Lean model".
- Status: pending

## 7. A receive skips a waiting tombstone in place

- Location: `crates/amaru-pure-stage/src/simulation/running/resume.rs:65`
  (`data.tombstones.pop_front()` first), and on tokio
  `crates/amaru-pure-stage/src/tokio.rs:452-454` (`take_tombstone` at
  `:549-552` comes before a due timeout, a schedule or bulk). The lines are
  the same at `34a45300` and `af03a9b9e`.
- Change: if the head tombstone is still waiting (entry 6), leave it in
  place and deliver the next ready priority message, then bulk. Do not stall
  the receive on a tombstone that is not ready, and do not deliver it out of
  turn.
- Decision: N55, Helen round 14 (`649a06c40`), GO condition 3: "Record N55 as
  pure-stage work". Roland's 11:46 rule gives the skip-in-place shape. In
  Lean, `receivePrio` skips a waiting tombstone and keeps the rest of the
  lane in order. `hold_drop` covers this.
- Status: pending

## 8. An unsupervised root keeps its population slot until its mail drains

- Location: net-new. It goes wherever a scheduler counts live roots against
  `N`. No Amaru site is identified. Helen's round-17 inventory finds no
  unsupervised per-peer root. A connection is supervised by the manager with
  `ConnectionDied` (`manager/mod.rs:479` in `af03a9b9e`), so entry 6 covers it.
- Change: a dead root that has no supervisor keeps one of the `N` population
  slots while any surviving receiver not sealed with it still holds mail
  from its subtree (bulk, priority or parked). The drain uses the same
  consumption reports as entry 6.
- Decision: Roland, 2026-11-21 08:44 CET ("a dead root occupies its
  population slot until its core mail is consumed") and 09:30 CET (any live
  host not sealed together with it, not only cores). In Lean these are
  `loneOutstanding`, `slotMailHeld` and `may_root_parts`. The E4 witness is
  `outlive_refused`. DECISIONS.md says the scheduler holds that slot.
- Status: pending. Whether Amaru has such a root today is unverified.

## 9. Cells become a pure-stage primitive

- Location: net-new pure-stage effect. No current site.
- Change: a cell write is an effect whose resource holds a map keyed by
  reader stage name, with one cell per reader. Each cell holds a
  `(counter, value)` pair ordered by the counter, plus a wake-pending flag. A
  write stores the value atomically. If no wake is pending, it sets the flag
  and enqueues one regular wake message. The reader's handler reads and
  clears the flag atomically.
- Decision: Roland, 2026-11-19, "note for later". Cells are not a pure-stage
  primitive today, so `cell`, `tryWake` and `CellFresh` deviate from
  pure-stage. The matching Lean change is also deferred: the uncharged
  priority wake becomes a regular message with one reserved mailbox slot per
  cell label and reader. This is in SEMANTICS.md under "Later" and in
  CHANGES-R5.md under "Later".
- Status: pending (later)
