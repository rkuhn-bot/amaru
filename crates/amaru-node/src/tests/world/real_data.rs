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

//! Recorded-chain world tests.
//!
//! Fragments taken from a live network. Production `build_node`; only the
//! connections resource is the simulated wire. See EDR-011
//! "World tests: generated vs recorded chains".

use std::{sync::Arc, time::Duration};

use amaru_ouroboros::ConnectionsResource;
use amaru_pure_stage::trace_buffer::TraceBuffer;

use super::{
    HONEST_PAYLOAD_DELAY_MAX_NANOS, HeapLogKind, LONG_TAIL_PAYLOAD_EVERY, WorldConnectionProvider, WorldLoop,
    build_world_node,
    support::{
        SEED, entry_chainsync_initiator_kind, entry_chainsync_roll_forward_hash, entry_is_validate_header_of,
        fragment_trace_guards, tm_validate_header,
    },
};
use crate::tests::configuration::NodeTestConfig;

/// Recorded preprod fragment (EDR-011): production validation, simulated wire only.
/// Produced by `run_until` after bootstrap. Node A is primed from that store (not
/// `with_validated_blocks` on a synthetic `any_headers_chain`). Node B starts from
/// bootstrap only and must adopt A's chain-store best tip.
///
/// World startup does not realign the chain store to the ledger tip: marked-valid
/// blocks on the persisted best chain are the ones that must disseminate. Long-tail
/// payload delay is a world setting, not a theorem. Horizon only runs the world far
/// enough for sampled Deliveries to pop. `k` stays at the production value (2160).
///
/// `target_upstream_peers=1` is isolation (one intended hop). Dest-keyed pairing already completes
/// `Connected` only for the connect that targeted that listener.
///
/// Missing stores are produced on first run (CDN bootstrap + live `run_until`).
/// Not `#[tokio::test]`: production graphs may `Handle::block_on` DurationDist::Zero effects.
#[test]
#[ignore = "first run downloads a preprod snapshot and syncs one epoch from the network"]
fn test_world_disseminates_preprod_fragment() {
    use std::cmp::Ordering;

    use amaru_consensus::stages::select_chain::cmp_tip;
    use amaru_kernel::{IsHeader, PREPROD_ERA_HISTORY, PREPROD_GLOBAL_PARAMETERS, Peer};
    use amaru_ouroboros::BaseReadChainStore;
    use amaru_protocols::store_effects::{ResourceHeaderStore, ResourceParameters};

    use super::fragment::{
        copy_dir, covers_following_epoch, ensure_fragment_stores, fixture_root, header_hash_from_snapshot_point,
        linear_fragment_to_head, load_committed_meta, open_chain_store, parse_slot_from_point,
    };

    let _guards = fragment_trace_guards();

    let root = fixture_root();
    ensure_fragment_stores(&root).expect("produce preprod fragment stores");
    let meta = load_committed_meta(&root).expect("meta.json");
    assert_eq!(meta.peer, "sleipnir.rkuhn.info:3001");

    let primed_tmp = tempfile::tempdir().expect("primed temp");
    let receiver_tmp = tempfile::tempdir().expect("receiver temp");
    copy_dir(&root.join("primed/chain"), &primed_tmp.path().join("chain")).expect("copy primed chain");
    copy_dir(&root.join("primed/ledger"), &primed_tmp.path().join("ledger")).expect("copy primed ledger");
    copy_dir(&root.join("bootstrap/chain"), &receiver_tmp.path().join("chain")).expect("copy bootstrap chain");
    copy_dir(&root.join("bootstrap/ledger"), &receiver_tmp.path().join("ledger")).expect("copy bootstrap ledger");

    let primed_chain_path = primed_tmp.path().join("chain");
    let snapshot_hash = header_hash_from_snapshot_point(&meta.latest_snapshot_point).expect("snapshot hash");
    let (served_head, served_fragment) = {
        let store = open_chain_store(&primed_chain_path).expect("open primed chain");
        let served_tip = store.get_best_chain_tip();
        assert_ne!(served_tip.hash(), snapshot_hash, "primed best tip must be after the bootstrap snapshot");
        assert!(store.has_block(&served_tip.hash()).expect("has_block"), "best tip must have a stored body");
        let head = store.load_header(&served_tip.hash()).expect("best tip header");
        let fragment = linear_fragment_to_head(&store, snapshot_hash, head.clone()).expect("parent walk to best tip");
        assert_eq!(fragment.last().map(|h| h.point()), Some(head.point()));
        assert_ne!(
            format!("{}", fragment[0].point()),
            format!("{}", head.point()),
            "best tip must not be the first header after the snapshot"
        );
        let snapshot_slot = parse_slot_from_point(&meta.latest_snapshot_point).expect("snapshot slot");
        assert!(
            covers_following_epoch(head.slot().as_u64(), snapshot_slot),
            "fragment should cover most of an epoch after the snapshot; got {} headers from {} to {}",
            fragment.len(),
            fragment[0].point(),
            head.point()
        );
        (head, fragment)
    };
    let served_tip = served_head.point();

    let offset = PREPROD_ERA_HISTORY
        .slot_to_relative_time_unchecked_horizon(served_head.slot())
        .expect("fragment slot in era history")
        + Duration::from_secs(30);

    let runtime = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
    let handle = runtime.handle().clone();
    let provider = Arc::new(WorldConnectionProvider::with_long_tail_payload_delay(SEED));

    let listen_primed = "127.0.0.1:9321";
    let listen_receiver = "127.0.0.1:9320";
    let peer_primed = Peer::new(listen_primed);

    // Isolation: one intended hop. Dest-keyed pairing still owns handshake matching.
    let node_primed = NodeTestConfig::default()
        .with_no_upstream_peers()
        .with_listen_address(listen_primed)
        .with_seed(21)
        .with_target_upstream_peers(1)
        .with_peer_mix("static~1")
        .with_keep_persisted_best_chain()
        .with_trace_buffer(TraceBuffer::new_shared(50_000, 64_000_000))
        .with_ledger_dir(primed_tmp.path().join("ledger"))
        .with_chain_dir(primed_tmp.path().join("chain"))
        .with_global_epoch_offset(offset);
    let node_receiver = NodeTestConfig::default()
        .with_upstream_peer(peer_primed)
        .with_listen_address(listen_receiver)
        .with_seed(22)
        .with_target_upstream_peers(1)
        .with_peer_mix("static~1")
        .with_trace_buffer(TraceBuffer::new_shared(50_000, 64_000_000))
        .with_ledger_dir(receiver_tmp.path().join("ledger"))
        .with_chain_dir(receiver_tmp.path().join("chain"))
        .with_global_epoch_offset(offset);

    let connections: ConnectionsResource = provider.clone();
    let sim_primed = build_world_node(&node_primed, connections.clone(), &handle).expect("primed node");
    let sim_receiver = build_world_node(&node_receiver, connections, &handle).expect("receiver node");

    let primed_store = {
        let store = sim_primed.resources().get::<ResourceHeaderStore>().expect("primed chain store");
        Arc::clone(&*store)
    };
    let receiver_store = {
        let store = sim_receiver.resources().get::<ResourceHeaderStore>().expect("receiver chain store");
        Arc::clone(&*store)
    };

    assert_eq!(
        primed_store.get_best_chain_tip(),
        served_tip,
        "world startup must keep the primed store's validated best tip"
    );
    for earlier in &served_fragment[..served_fragment.len() - 1] {
        assert_eq!(
            cmp_tip(Some(&served_head), Some(earlier)),
            Ordering::Greater,
            "served HEAD must win cmp_tip against earlier headers"
        );
    }
    assert!(receiver_store.load_header(&served_tip.hash()).is_none(), "receiver must start without the served HEAD");
    assert_ne!(
        receiver_store.get_best_chain_tip(),
        served_tip,
        "receiver best tip starts at bootstrap, not the served HEAD"
    );
    // Header + body payloads. One in LONG_TAIL_PAYLOAD_EVERY can sit at the hop cap.
    // Horizon is coverage so those sampled Deliveries pop, not a Praos deadline.
    let hop_coverage = (served_fragment.len() as u64).saturating_mul(2);
    let long_tail_hops = hop_coverage.div_ceil(LONG_TAIL_PAYLOAD_EVERY);
    let horizon_nanos =
        long_tail_hops.saturating_add(1).saturating_mul(HONEST_PAYLOAD_DELAY_MAX_NANOS).saturating_add(2_000_000_000);
    eprintln!(
        "catch-up served HEAD {served_tip} snapshot={snapshot_hash} fragment_len={} horizon_nanos={horizon_nanos}",
        served_fragment.len()
    );

    let mut world = WorldLoop::new(provider, vec![sim_primed, sim_receiver]);
    let wall_start = std::time::Instant::now();
    world.run_until_horizon_with(horizon_nanos, Duration::from_secs(2), |world| {
        let primed = world.graphs()[0].resources().get::<ResourceHeaderStore>().expect("primed store");
        let receiver = world.graphs()[1].resources().get::<ResourceHeaderStore>().expect("receiver store");
        let have = served_fragment.iter().filter(|h| receiver.load_header(&h.hash()).is_some()).count();
        eprintln!(
            "catch-up wall={:?} sim={:?} next={:?} events={} have={have}/{} primed_tip={} receiver_tip={}",
            wall_start.elapsed(),
            world.graphs()[0].now().sim_elapsed(),
            world.peek_next_event_time(),
            world.heap_len(),
            served_fragment.len(),
            primed.get_best_chain_tip(),
            receiver.get_best_chain_tip(),
        );
    });
    let wall = wall_start.elapsed();

    for graph in world.graphs() {
        let params = graph.resources().get::<ResourceParameters>().expect("production GlobalParameters");
        assert_eq!(params.consensus_security_param, PREPROD_GLOBAL_PARAMETERS.consensus_security_param);
        assert_eq!(params.consensus_security_param, 2160, "production k, not chain_length");
    }

    let receiver_after = world.graphs()[1].resources().get::<ResourceHeaderStore>().expect("receiver store");
    let primed_after = world.graphs()[0].resources().get::<ResourceHeaderStore>().expect("primed store");
    let log = world.heap_log();
    let receiver_traces = world.graphs()[1].trace_buffer().lock().hydrate_without_timestamps();
    let receiver_have = served_fragment.iter().filter(|h| receiver_after.load_header(&h.hash()).is_some()).count();
    let rf_hashes: Vec<_> = receiver_traces.iter().filter_map(entry_chainsync_roll_forward_hash).collect();
    let roll_forwards = rf_hashes.len();
    let validated = receiver_traces.iter().filter(|e| tm_validate_header() == **e).count();
    let connects = log.iter().filter(|e| matches!(e.kind, HeapLogKind::ConnectAttempt { .. })).count();
    let accepts = log.iter().filter(|e| matches!(e.kind, HeapLogKind::Accepted { .. })).count();
    let delivers = log.iter().filter(|e| matches!(e.kind, HeapLogKind::Deliver { .. })).count();
    let first = served_fragment.first().expect("fragment");
    let mut unique_rf = Vec::new();
    for hash in &rf_hashes {
        if !unique_rf.contains(hash) {
            unique_rf.push(*hash);
        }
    }
    let dropped = world.graphs()[1].trace_buffer().lock().dropped_messages();
    let saw_head_rf = unique_rf.contains(&served_head.hash());
    let saw_rollback = receiver_traces
        .iter()
        .any(|entry| entry_chainsync_initiator_kind(entry).is_some_and(|kind| kind.starts_with("RollBackward")));
    eprintln!(
        "catch-up after WorldLoop wall={wall:?} sim={:?} next={:?} primed_tip={} receiver_tip={} have={receiver_have}/{} rf={roll_forwards} unique_rf={} vh={validated} dropped={dropped} connect={connects} accept={accepts} deliver={delivers} first={} head_rf={saw_head_rf} rollback={saw_rollback}",
        world.graphs()[0].now().sim_elapsed(),
        world.peek_next_event_time(),
        primed_after.get_best_chain_tip(),
        receiver_after.get_best_chain_tip(),
        served_fragment.len(),
        unique_rf.len(),
        first.point()
    );
    assert!(
        receiver_after.load_header(&served_tip.hash()).is_some(),
        "receiving node must have the served HEAD in store before tip equality is compared"
    );

    let head_hash = served_head.hash();
    let receiver_got_roll_forward =
        receiver_traces.iter().any(|entry| entry_chainsync_roll_forward_hash(entry) == Some(head_hash));
    assert!(
        receiver_got_roll_forward,
        "B must see a typed chainsync RollForward of the served HEAD (not a Debug substring OR); head={head_hash}"
    );
    let receiver_validated = receiver_traces.iter().any(|entry| entry_is_validate_header_of(entry, &head_hash));
    assert!(receiver_validated, "B must run production ValidateHeaderEffect on the served HEAD; head={head_hash}");

    let primed_tip = primed_after.get_best_chain_tip();
    let receiver_tip = receiver_after.get_best_chain_tip();
    let primed_header = primed_after.load_header(&primed_tip.hash()).expect("primed tip header");
    let receiver_header = receiver_after.load_header(&receiver_tip.hash()).expect("receiver tip header");
    assert_ne!(
        cmp_tip(Some(&receiver_header), Some(&served_head)),
        Ordering::Less,
        "receiver tip must reach at least the served HEAD after production validation"
    );
    assert_eq!(
        cmp_tip(Some(&receiver_header), Some(&primed_header)),
        Ordering::Equal,
        "receiver tip must be cmp_tip-equal to the primed chain-store best tip"
    );
    assert_eq!(receiver_tip, primed_tip);
}
