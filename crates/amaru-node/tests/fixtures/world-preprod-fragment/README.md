# Preprod fragment fixture for WorldLoop

The dissemination test primes one world node from a real preprod chain/ledger
store and starts the other node from bootstrap state only. The fragment HEAD
must appear on every honest node after `WorldLoop`.

The RocksDB stores are too large to commit. This directory keeps the discovery
inputs and the commands that produce the stores.

## Discover the target epoch (do not guess)

Amaru bootstrap lists snapshots from `<public_url>/preprod/index.json`
(`amaru-bootstrap::AnonymousS3Client::list_snapshots`, same URL as
`DEFAULT_PUBLIC_URL`). Each entry is a `<slot>.<hash>` point. Epochs come from
`EraHistory::slot_to_epoch_unchecked_horizon` on preprod. The latest snapshot
state is the maximum of those epochs. `run_until` targets the epoch after it.

Refresh the committed index, then recompute:

```sh
curl -sS https://pub-b844360df4774bb092a2bb2043b888e5.r2.dev/preprod/index.json \
  -o crates/amaru-node/tests/fixtures/world-preprod-fragment/index.json

cargo test -p amaru-node --lib --features test-utils \
  test_target_epoch_is_discovered_from_bootstrap_index
```

Update `meta.json` if the latest published snapshot moved. The test fails when
`meta.json` disagrees with the index mapped through era history.

Default chain/ledger dirs are `./chain.preprod.db` and `./ledger.preprod.db`
(`amaru_node::default_chain_dir` / `default_ledger_dir`). The commands below
use explicit fixture paths instead.

## Produce the stores

From the repository root, with a release build of `amaru` and the `run_until`
example. `TARGET` is `meta.json`'s `target_epoch`.

```sh
ROOT=crates/amaru-node/tests/fixtures/world-preprod-fragment
TARGET=307

# 1. Bootstrap the latest published snapshot window into bootstrap/
cargo run --release --bin amaru -- node bootstrap \
  --network preprod \
  --chain-dir "$ROOT/bootstrap/chain" \
  --ledger-dir "$ROOT/bootstrap/ledger"

# 2. Copy bootstrap → primed, then sync the next epoch from sleipnir
rm -rf "$ROOT/primed"
cp -a "$ROOT/bootstrap" "$ROOT/primed"

cargo run --release -p amaru-node --example run_until -- \
  --network preprod \
  --epoch "$TARGET" \
  --peer-address sleipnir.rkuhn.info:3001 \
  --chain-dir "$ROOT/primed/chain" \
  --ledger-dir "$ROOT/primed/ledger"
```

The primed store is the `run_until` output. The receiver node in the test is
copied from `bootstrap/` (no fragment). Do not commit `bootstrap/` or `primed/`.

`meta.json`'s `fragment_head` is the last header after the snapshot that has a
stored body (the linear HEAD). It is not the first epoch-boundary header.

## Run the dissemination test

```sh
cargo test -p amaru-node --lib --features test-utils -- --ignored \
  test_world_disseminates_preprod_fragment
```
