Checked against `main` at 33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6.

## What happens

The block-fetch initiator runs a pipeline of `BLOCKFETCH_PIPELINE_N = 2` request slots. When a local message (a `RequestRange` forwarded by the connection) arrives while the slot under the send cursor is not idle, the pipeline driver logs "pipeline full" and terminates the handler. With two ranges in flight, a third outstanding range is enough. The connection treats the death as unexpected and tears down the whole connection.

## Where

- The check and the termination: [pipeline.rs#L172-L177](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/protocol/pipeline.rs#L172-L177).
- Pipeline depth: [initiator.rs#L42-L45](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/blockfetch/initiator.rs#L42-L45).
- The connection forwards every `FetchBlocks` to the initiator as `RequestRange` without any credit check: [connection.rs#L248-L254](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/connection.rs#L248-L254).
- An unexpected child death tears down the connection: [connection.rs#L228-L235](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/connection.rs#L228-L235).
- The initiator has code to stash a newer range while busy ([initiator.rs#L317-L324](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/blockfetch/initiator.rs#L317-L324), [initiator.rs#L369-L376](https://github.com/pragma-org/amaru/blob/33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6/crates/amaru-protocols/src/blockfetch/initiator.rs#L369-L376)), but under the pipelined driver a local message never reaches a non-idle slot (the driver terminates first), so that stash does not help here.

A `Close` arriving while both slots are busy hits the same branch, so the handler ends without `ClientDone` instead of finishing the session.

## Why it matters

A third range is reachable without any misbehaving peer: `fetch_blocks` issues a new request after a timeout, a widen, or a best-tip change while a slow but honest peer is still streaming the previous ranges. The result is a disconnect caused by our own request rate, not by anything the peer did. Disconnecting an honest peer because of local load is undesirable in general, and an adversary who can influence our re-request rate (slow peers, tip churn) could use it to push honest peers off the node.

## Proposed fix

The local side must never exceed the pipeline depth it chose, and must not tear down when it would. Keep at most one pending range per initiator as local state (latest wins: ranges for superseded request ids are discarded by `cleanup_replies` anyway) and send it when a slot returns to idle, or give the sender an explicit credit of `n` outstanding ranges. Either way the "pipeline full" branch becomes unreachable and can be an assertion.

## How found

Analysis of the stage wait graph, during the per-kind occupancy check of the block-fetch initiator's mailbox. Found by code reading; there is no simulation reproduction yet.
