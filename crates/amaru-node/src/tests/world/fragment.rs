// Copyright 2026 PRAGMA
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Discover the `run_until` target epoch from Amaru's published bootstrap index.
//!
//! Bootstrap lists `<network>/index.json` (see `amaru-bootstrap::AnonymousS3Client::list_snapshots`)
//! and maps each `<slot>.<hash>` point through [`EraHistory::slot_to_epoch_unchecked_horizon`].
//! The latest snapshot epoch is that maximum; the fragment target is the epoch after it.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use amaru_kernel::{Epoch, EraHistory, Header, Point, Slot};
use amaru_ouroboros::BaseReadChainStore;
use amaru_stores::rocksdb::{RocksDbConfig, consensus::RocksDBStore};
use serde::Deserialize;

/// Public CDN base used by `amaru-bootstrap` (`DEFAULT_PUBLIC_URL`) for anonymous index fetch.
pub const SNAPSHOT_PUBLIC_URL: &str = "https://pub-b844360df4774bb092a2bb2043b888e5.r2.dev";

/// `<slot>.<hash>` point as published in `<network>/index.json`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnapshotPoint {
    pub point: String,
    pub slot: Slot,
    pub epoch: Epoch,
}

/// Result of mapping a bootstrap index through era history.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BootstrapIndex {
    pub latest: SnapshotPoint,
    pub target_epoch: Epoch,
}

/// Committed metadata written next to the on-disk fixture stores.
#[derive(Debug, Clone, Deserialize)]
pub struct FragmentMeta {
    pub network: String,
    pub index_source: String,
    pub latest_snapshot_point: String,
    pub latest_snapshot_epoch: u64,
    pub target_epoch: u64,
    pub peer: String,
}

/// Parse `<slot>.<hash>` the same way `amaru-bootstrap` does.
pub fn parse_slot_from_point(point: &str) -> anyhow::Result<u64> {
    point
        .split('.')
        .next()
        .and_then(|s| s.parse::<u64>().ok())
        .ok_or_else(|| anyhow::anyhow!("invalid snapshot point format: {point}"))
}

/// Map published index points to epochs. Latest snapshot state is the maximum epoch;
/// `run_until` must target the epoch after that.
pub fn bootstrap_index_from_points(points: &[String], era_history: &EraHistory) -> anyhow::Result<BootstrapIndex> {
    let mut snapshots = Vec::with_capacity(points.len());
    for point in points {
        let slot = Slot::from(parse_slot_from_point(point)?);
        let epoch = era_history.slot_to_epoch_unchecked_horizon(slot)?;
        snapshots.push(SnapshotPoint { point: point.clone(), slot, epoch });
    }
    let latest = snapshots
        .into_iter()
        .max_by_key(|s| s.epoch)
        .ok_or_else(|| anyhow::anyhow!("bootstrap index listed no snapshots"))?;
    Ok(BootstrapIndex { target_epoch: latest.epoch + 1, latest })
}

pub fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/world-preprod-fragment")
}

pub fn load_committed_index(root: &Path) -> anyhow::Result<Vec<String>> {
    let bytes = fs::read(root.join("index.json"))?;
    Ok(serde_json::from_slice(&bytes)?)
}

pub fn load_committed_meta(root: &Path) -> anyhow::Result<FragmentMeta> {
    let bytes = fs::read(root.join("meta.json"))?;
    Ok(serde_json::from_slice(&bytes)?)
}

pub fn stores_ready(root: &Path) -> bool {
    dir_is_populated(&root.join("bootstrap/chain"))
        && dir_is_populated(&root.join("bootstrap/ledger"))
        && dir_is_populated(&root.join("primed/chain"))
        && dir_is_populated(&root.join("primed/ledger"))
}

fn dir_is_populated(path: &Path) -> bool {
    fs::read_dir(path).ok().is_some_and(|mut entries| entries.next().is_some())
}

pub fn copy_dir(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let dest = dst.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_dir(&entry.path(), &dest)?;
        } else {
            fs::copy(entry.path(), dest)?;
        }
    }
    Ok(())
}

pub fn open_chain_store(chain_dir: &Path) -> anyhow::Result<RocksDBStore> {
    Ok(RocksDBStore::open(&RocksDbConfig::new(chain_dir.to_path_buf()))?)
}

/// Headers on the best chain from `after` (exclusive) through `tip` (inclusive).
///
/// For a linear fragment this ends at the fragment HEAD, not the first header after the intersection.
pub fn fragment_headers_to_tip(
    store: &dyn BaseReadChainStore,
    after: &Point,
    tip: &Point,
) -> anyhow::Result<Vec<Header>> {
    if *tip == Point::Origin {
        anyhow::bail!("primed chain tip is Origin");
    }
    let mut headers = Vec::new();
    let mut cursor = after.clone();
    loop {
        let Some(next) = store.next_best_chain(&cursor) else {
            anyhow::bail!("best chain does not reach tip {tip} from {after}");
        };
        let header = store.load_header(&next.hash()).ok_or_else(|| anyhow::anyhow!("missing header for {next}"))?;
        headers.push(header);
        if next == *tip {
            return Ok(headers);
        }
        cursor = next;
    }
}

#[cfg(test)]
mod tests {
    use amaru_kernel::PREPROD_ERA_HISTORY;

    use super::*;

    #[test]
    fn test_target_epoch_is_discovered_from_bootstrap_index() {
        let root = fixture_root();
        let points = load_committed_index(&root).expect("committed preprod/index.json");
        let discovered =
            bootstrap_index_from_points(&points, &PREPROD_ERA_HISTORY).expect("map index through era history");
        let meta = load_committed_meta(&root).expect("committed meta.json");

        assert_eq!(meta.network, "preprod");
        assert_eq!(meta.index_source, format!("{SNAPSHOT_PUBLIC_URL}/preprod/index.json"));
        assert_eq!(discovered.latest.point, meta.latest_snapshot_point);
        assert_eq!(discovered.latest.epoch.as_u64(), meta.latest_snapshot_epoch);
        assert_eq!(discovered.target_epoch.as_u64(), meta.target_epoch);
        assert_eq!(discovered.target_epoch, discovered.latest.epoch + 1);
        assert_eq!(meta.peer, "sleipnir.rkuhn.info:3001");
    }

    #[test]
    fn test_parse_slot_from_bootstrap_point() {
        assert_eq!(
            parse_slot_from_point("130982398.6b78e3cbc65e4cc9ca036c03ab125697b9a31954f55219bf7ad5397d63286c43")
                .unwrap(),
            130_982_398
        );
    }
}
