Checked against `main` at 33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6.

## What happens

While a connection is in `Initial` or `Handshake`, every `FetchBlocks`, `NewTip` and `SetLocalUse` it receives is put back with `schedule_after(reconnect_delay)`. When the scheduled message fires and the connection is still not established, it is scheduled again. Nothing cancels an earlier schedule, so each such message keeps one schedule outstanding until the handshake finishes, and the count grows with every new message.

Pure-stage allows at most `PRIORITY_MAILBOX_SIZE = 10` outstanding schedules per stage and panics when a stage exceeds that.

## Where

- The three re-schedule arms: [connection.rs#L267-L283](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/connection.rs#L267-L283) (`schedule_after` at L272, L277, L281).
- `manager` forwards every adopted tip to every connection in its map, established or not: [mod.rs#L864-L868](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/manager/mod.rs#L864-L868).
- `reconnect_delay` defaults to 2 s ([mod.rs#L326](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/manager/mod.rs#L326)); the handshake phase can last up to `SDU_TIMEOUT_HANDSHAKE` = 10 s ([mux.rs#L53](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/mux.rs#L53)).
- The limit and the panic: [types.rs#L41-L44](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-pure-stage/src/types.rs#L41-L44), [tokio.rs#L864-L870](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-pure-stage/src/tokio.rs#L864-L870).

## Why it matters

During catch-up `adopt_chain` adopts many blocks per second, and each adoption produces a `NewTip` for every connection. A connection that is still dialling or handshaking for a couple of seconds therefore collects more than 10 outstanding schedules, and the connection stage panics. The pure-stage documentation treats this as a programming error that must fail loudly, so this is a crash path that depends only on adoption rate and handshake latency, not on anything a peer does wrong.

## Proposed fix

Cancel before re-arming, so that each connection has a fixed, small number of outstanding schedules:

- `NewTip` and `SetLocalUse` are latest-wins for the connection (the chain-sync responder only uses the latest tip; `converge_use` only compares the latest desired use). Keep the latest value in the connection state and deliver it on reaching `Established`, instead of scheduling each message.
- For `FetchBlocks`, keep only the newest request per connection (older request ids are already superseded at `fetch_blocks`), or cancel the previous schedule id before scheduling the new one.

With that, the connection stage has at most one retry timer (or none) instead of one per message.

## How found

Analysis of the stage wait graph: while building the per-stage table of outstanding schedules, every other stage cancels before re-arming and stays at 2 or fewer; this is the one producer without a bound. Found by code reading; there is no simulation reproduction yet.
