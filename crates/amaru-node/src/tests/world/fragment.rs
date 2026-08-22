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
    collections::BTreeSet,
    fs, io,
    path::{Path, PathBuf},
};

use amaru_consensus::stages::select_chain::cmp_tip;
use amaru_kernel::{Epoch, EraHistory, Header, HeaderHash, IsHeader, Slot};
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
    /// Last header after the snapshot that has a stored body. Display form of [`Point`].
    pub fragment_head: String,
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
            match fs::copy(entry.path(), &dest) {
                Ok(_) => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(e),
            }
        }
    }
    Ok(())
}

pub fn open_chain_store(chain_dir: &Path) -> anyhow::Result<RocksDBStore> {
    Ok(RocksDBStore::open_for_readonly(&RocksDbConfig::new(chain_dir.to_path_buf()))?)
}

/// Hash part of a `<slot>.<hash>` bootstrap index point.
pub fn header_hash_from_snapshot_point(point: &str) -> anyhow::Result<HeaderHash> {
    let hash = point
        .split_once('.')
        .map(|(_, hash)| hash)
        .ok_or_else(|| anyhow::anyhow!("invalid snapshot point format: {point}"))?;
    hash.parse().map_err(|e| anyhow::anyhow!("invalid snapshot hash in {point}: {e}"))
}

/// Headers on the parent chain from `after` (exclusive) through `head` (inclusive).
///
/// For a linear fragment this ends at the fragment HEAD, not the first header after the intersection.
pub fn linear_fragment_to_head(
    store: &dyn BaseReadChainStore,
    after: HeaderHash,
    head: Header,
) -> anyhow::Result<Vec<Header>> {
    let mut headers = vec![head.clone()];
    let mut current = head;
    loop {
        let Some(parent) = current.parent() else {
            anyhow::bail!("reached origin before snapshot {after}");
        };
        if parent == after {
            headers.reverse();
            return Ok(headers);
        }
        current = store.load_header(&parent).ok_or_else(|| anyhow::anyhow!("missing parent {parent}"))?;
        headers.push(current.clone());
    }
}

/// Best-chain headers after `after` that already have bodies.
///
/// `run_until` can leave headers ahead of the last stored block. The disseminable HEAD is the
/// last header in this list, not the first header after the snapshot.
pub fn linear_fragment_with_bodies(store: &dyn BaseReadChainStore, after: HeaderHash) -> anyhow::Result<Vec<Header>> {
    let Some(mut cursor) = store.load_point(&after) else {
        anyhow::bail!("snapshot header {after} is not in the store");
    };
    let mut headers = Vec::new();
    while let Some(next) = store.next_best_chain(&cursor) {
        if !store.has_block(&next.hash())? {
            break;
        }
        let header = store.load_header(&next.hash()).ok_or_else(|| anyhow::anyhow!("missing header for {next}"))?;
        headers.push(header);
        cursor = next;
    }
    if headers.is_empty() {
        anyhow::bail!("primed store has no fragment bodies after {after}");
    }
    Ok(headers)
}

/// Last header on the parent walk from `candidate` toward `after` that still has a stored body.
///
/// After `build_node` realigns the best-chain pointer to the ledger snapshot, `next_best_chain`
/// no longer walks the fragment. Recovery still starts from `find_best_candidate`; the
/// disseminable HEAD is this header, not `get_best_chain_tip`.
pub fn last_body_on_candidate(
    store: &dyn BaseReadChainStore,
    candidate: HeaderHash,
    after: HeaderHash,
) -> anyhow::Result<Header> {
    if candidate == after {
        anyhow::bail!("recovery candidate is the snapshot {after}; no fragment to serve");
    }
    let mut current = store
        .load_header(&candidate)
        .ok_or_else(|| anyhow::anyhow!("missing recovery candidate header {candidate}"))?;
    loop {
        if store.has_block(&current.hash())? {
            if current.hash() == after {
                anyhow::bail!("no stored body after snapshot {after}");
            }
            return Ok(current);
        }
        let Some(parent) = current.parent() else {
            anyhow::bail!("reached origin before a stored body on candidate {candidate}");
        };
        if parent == after {
            anyhow::bail!("no stored body between snapshot {after} and candidate {candidate}");
        }
        current = store.load_header(&parent).ok_or_else(|| anyhow::anyhow!("missing parent {parent}"))?;
    }
}

/// Latest stored body reachable from `after` by walking children (not `next_best_chain`).
///
/// After realign the best-chain pointer is the snapshot, but fragment headers remain as
/// children. Recovery's `find_best_candidate` walks that same tree. The clock offset must
/// be taken from this header so served HEADs are not in the future.
pub fn latest_body_after(store: &dyn BaseReadChainStore, after: HeaderHash) -> anyhow::Result<Header> {
    let mut best = None;
    let mut to_visit = store.get_children(&after);
    let mut seen = BTreeSet::new();
    while let Some(hash) = to_visit.pop() {
        if !seen.insert(hash) {
            continue;
        }
        let Some(header) = store.load_header(&hash) else {
            continue;
        };
        if store.has_block(&hash)? && best.as_ref().is_none_or(|current| cmp_tip(Some(&header), Some(current)).is_gt())
        {
            best = Some(header);
        }
        to_visit.extend(store.get_children(&hash));
    }
    best.ok_or_else(|| anyhow::anyhow!("no stored body after snapshot {after}"))
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
        assert!(!meta.fragment_head.is_empty(), "meta.fragment_head records a previous production HEAD");
    }

    #[test]
    fn test_parse_slot_from_bootstrap_point() {
        let point = "130982398.6b78e3cbc65e4cc9ca036c03ab125697b9a31954f55219bf7ad5397d63286c43";
        assert_eq!(parse_slot_from_point(point).unwrap(), 130_982_398);
        assert_eq!(
            header_hash_from_snapshot_point(point).unwrap().to_string(),
            "6b78e3cbc65e4cc9ca036c03ab125697b9a31954f55219bf7ad5397d63286c43"
        );
    }

    #[test]
    #[ignore = "requires preprod fragment stores; see tests/fixtures/world-preprod-fragment/README.md"]
    fn test_primed_store_fragment_head_is_last_header_with_body() {
        let root = fixture_root();
        assert!(stores_ready(&root), "stores missing under {}", root.display());
        let meta = load_committed_meta(&root).expect("meta.json");
        let tmp = tempfile::tempdir().expect("copy primed chain");
        copy_dir(&root.join("primed/chain"), &tmp.path().join("chain")).expect("copy primed chain");
        let store = open_chain_store(&tmp.path().join("chain")).expect("open primed chain");
        let snapshot = header_hash_from_snapshot_point(&meta.latest_snapshot_point).expect("snapshot hash");
        let fragment = linear_fragment_with_bodies(&store, snapshot).expect("fragment with bodies");
        let head = fragment.last().expect("HEAD");
        let walked = linear_fragment_to_head(&store, snapshot, head.clone()).expect("parent walk");
        assert_eq!(walked.last().map(|h| h.point()), Some(head.point()));
        assert!(fragment.len() >= 2, "fragment must be more than a single header");
        assert_ne!(
            format!("{}", fragment[0].point()),
            format!("{}", head.point()),
            "HEAD must not be the first header after the snapshot"
        );
    }
}
