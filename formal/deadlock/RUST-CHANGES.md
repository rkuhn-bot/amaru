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
- Decision: N67. The model does not express an accept restart. Written as a
  core, that terminate crashes the node.
- Status: pending

## 3. No Listen tombstone and no accept respawn

- Location: `crates/amaru-protocols/src/manager/mod.rs:439`, `:861`
- Change: remove the `Listen(addr)` tombstone and the respawn path, or make
  that path unreachable. `:439` supervises the accept stage with
  `ManagerMessage::Listen(listen_addr)`. `:861` handles that message by
  calling `listen` again.
- Decision: N67. Same decision as the accept terminate.
- Status: pending
