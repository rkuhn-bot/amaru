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

//! Serve-only chain injector for world tests.
//!
//! This graph is not [`super::build_world_node`]. It speaks mux (handshake, keepalive,
//! ChainSync responder, BlockFetch responder), serves headers and blocks from a store
//! prefix, and does not run consensus or forge.
//!
//! The injector scans what is in the DB and publishes that inventory to a shared handle
//! owned by [`super::WorldLoop`]. WorldLoop holds the reveal cursor and decides when each
//! block becomes visible. The injector does not pick the advertised tip on its own.

use std::{collections::BTreeSet, net::SocketAddr, sync::Arc, time::Duration};

use amaru_consensus::stages::select_chain::cmp_tip;
use amaru_kernel::{
    BlockHeight, Header, HeaderHash, IsHeader, NetworkMagic, PREPROD_ERA_HISTORY, Peer, Point, Slot, Transaction,
};
use amaru_mempool::InMemoryMempool;
use amaru_metrics::Meter;
use amaru_ouroboros::{
    BaseReadChainStore, ConnectionsResource, ResourceMempool, WriteChainStore,
    in_memory_chain_store::InMemoryChainStore,
};
use amaru_protocols::{
    chainsync::ChainSyncInitiatorMsg,
    manager::{Manager, ManagerConfig, ManagerMessage},
    metrics_effects::ResourceMeter,
    store_effects::ResourceHeaderStore,
};
use amaru_pure_stage::{
    Effects, StageGraph, StageRef,
    simulation::{Fifo, SimulationBuilder, SimulationRunning},
};
use parking_lot::Mutex;
use tokio::runtime::Handle;

/// One header the injector found in the source store, in chain order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InventoryBlock {
    pub point: Point,
    pub hash: HeaderHash,
    pub slot: Slot,
    pub height: BlockHeight,
    pub has_body: bool,
}

impl InventoryBlock {
    fn from_header(header: &Header, has_body: bool) -> Self {
        Self {
            point: header.point(),
            hash: header.hash(),
            slot: header.slot(),
            height: header.block_height(),
            has_body,
        }
    }
}

/// Shared injector handle owned by [`super::WorldLoop`].
///
/// The injector graph writes the scanned inventory here. WorldLoop reads it after the
/// first step and drives reveal. Do not hang this off [`SimulationRunning`].
pub struct InjectorShared {
    inner: Mutex<InjectorInner>,
}

struct InjectorInner {
    inventory: Vec<InventoryBlock>,
    revealed: usize,
    manager: StageRef<ManagerMessage>,
    graph_index: usize,
    source: Arc<dyn BaseReadChainStore>,
    serving: Arc<InMemoryChainStore>,
}

impl InjectorShared {
    fn new(
        manager: StageRef<ManagerMessage>,
        graph_index: usize,
        source: Arc<dyn BaseReadChainStore>,
        serving: Arc<InMemoryChainStore>,
    ) -> Arc<Self> {
        Arc::new(Self {
            inner: Mutex::new(InjectorInner {
                inventory: Vec::new(),
                revealed: 0,
                manager,
                graph_index,
                source,
                serving,
            }),
        })
    }

    fn publish_inventory(&self, inventory: Vec<InventoryBlock>) {
        self.inner.lock().inventory = inventory;
    }

    pub fn inventory(&self) -> Vec<InventoryBlock> {
        self.inner.lock().inventory.clone()
    }

    pub fn revealed_tip(&self) -> Point {
        let inner = self.inner.lock();
        inner.revealed.checked_sub(1).and_then(|i| inner.inventory.get(i)).map(|b| b.point).unwrap_or(Point::Origin)
    }

    pub(super) fn manager(&self) -> StageRef<ManagerMessage> {
        self.inner.lock().manager.clone()
    }

    pub(super) fn graph_index(&self) -> usize {
        self.inner.lock().graph_index
    }

    fn copy_prefix_through(&self, through: usize) -> anyhow::Result<Option<InventoryBlock>> {
        let mut inner = self.inner.lock();
        if inner.inventory.is_empty() || through >= inner.inventory.len() {
            anyhow::bail!("reveal index {through} is outside inventory of {}", inner.inventory.len());
        }
        while inner.revealed <= through {
            let block = inner.inventory[inner.revealed].clone();
            copy_revealed_block(inner.source.as_ref(), inner.serving.as_ref(), &block)?;
            inner.revealed += 1;
        }
        Ok(inner.inventory.get(through).cloned())
    }

    fn next_unrevealed_index(&self) -> Option<usize> {
        let inner = self.inner.lock();
        (inner.revealed < inner.inventory.len()).then_some(inner.revealed)
    }

    fn index_of(&self, hash: HeaderHash) -> anyhow::Result<usize> {
        self.inner
            .lock()
            .inventory
            .iter()
            .position(|b| b.hash == hash)
            .ok_or_else(|| anyhow::anyhow!("hash {hash} is not in the injector inventory"))
    }

    pub(super) fn reveal_through(&self, hash: HeaderHash) -> anyhow::Result<Option<InventoryBlock>> {
        let through = self.index_of(hash)?;
        self.copy_prefix_through(through)
    }

    pub(super) fn reveal_next_block(&self) -> anyhow::Result<Option<InventoryBlock>> {
        let Some(through) = self.next_unrevealed_index() else {
            return Ok(None);
        };
        self.copy_prefix_through(through)
    }
}

fn copy_revealed_block(
    source: &dyn BaseReadChainStore,
    serving: &InMemoryChainStore,
    block: &InventoryBlock,
) -> anyhow::Result<()> {
    let header = source.load_header(&block.hash).ok_or_else(|| anyhow::anyhow!("missing header {}", block.hash))?;
    serving.store_header(&header)?;
    if let Some(body) = source.load_block(&block.hash)? {
        serving.store_block(&block.hash, &body)?;
    }
    if serving.get_anchor_point() == Point::Origin {
        serving.set_anchor_point(&header.point())?;
    }
    serving.roll_forward_chain(&header.point())?;
    Ok(())
}

/// Walk the disseminable fragment already stored in `store`.
///
/// Uses `next_best_chain` when that still names the fragment (InMemory / live tip).
/// After `realign_chain_store_to` the best-chain pointer is the snapshot, so this falls
/// back to walking children after that snapshot — the same tree recovery uses.
pub fn scan_inventory(store: &dyn BaseReadChainStore) -> Vec<InventoryBlock> {
    let tip = store.get_best_chain_tip();
    let realigned =
        tip != Point::Origin && store.next_best_chain(&tip).is_none() && !store.get_children(&tip.hash()).is_empty();
    if realigned {
        let linear = walk_next_best(store, tip);
        if !linear.is_empty() {
            return linear;
        }
        return children_fragment(store, tip.hash());
    }
    walk_next_best(store, Point::Origin)
}

fn walk_next_best(store: &dyn BaseReadChainStore, mut cursor: Point) -> Vec<InventoryBlock> {
    let mut out = Vec::new();
    while let Some(next) = store.next_best_chain(&cursor) {
        let Some(header) = store.load_header(&next.hash()) else {
            break;
        };
        let has_body = store.has_block(&header.hash()).unwrap_or(false);
        out.push(InventoryBlock::from_header(&header, has_body));
        if !has_body {
            break;
        }
        cursor = next;
    }
    out
}

fn children_fragment(store: &dyn BaseReadChainStore, after: HeaderHash) -> Vec<InventoryBlock> {
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
        if store.has_block(&hash).unwrap_or(false)
            && best.as_ref().is_none_or(|current| cmp_tip(Some(&header), Some(current)).is_gt())
        {
            best = Some(header);
        }
        to_visit.extend(store.get_children(&hash));
    }
    let Some(head) = best else {
        return Vec::new();
    };
    let mut headers = vec![head.clone()];
    let mut current = head;
    loop {
        let Some(parent) = current.parent() else {
            return Vec::new();
        };
        if parent == after {
            headers.reverse();
            return inventory_from_headers(store, headers);
        }
        let Some(header) = store.load_header(&parent) else {
            return Vec::new();
        };
        headers.push(header.clone());
        current = header;
    }
}

fn inventory_from_headers(store: &dyn BaseReadChainStore, headers: Vec<Header>) -> Vec<InventoryBlock> {
    headers
        .into_iter()
        .map(|header| {
            let has_body = store.has_block(&header.hash()).unwrap_or(false);
            InventoryBlock::from_header(&header, has_body)
        })
        .collect()
}

/// Build the serve-only injector graph.
///
/// Listens and accepts (`accept_interval = 0` so extra inbounds are not gated on the 100ms
/// Wait). Serves ChainSync/BlockFetch from an InMemory copy of the revealed prefix. The
/// source store is scanned as-is; after realign that source still advertises the snapshot.
pub fn build_injector(
    source: Arc<dyn BaseReadChainStore>,
    connections: ConnectionsResource,
    listen: SocketAddr,
    tokio_handle: &Handle,
    graph_index: usize,
) -> anyhow::Result<(SimulationRunning, Arc<InjectorShared>)> {
    let serving = Arc::new(InMemoryChainStore::new());
    let mut stage_graph = SimulationBuilder::default().with_eval_strategy(Fifo);
    put_serve_resources(&mut stage_graph, connections, serving.clone());

    let manager = stage_graph.stage("manager", amaru_protocols::manager::stage);
    let manager = stage_graph.wire_up(
        manager,
        Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default().with_accept_interval(Duration::ZERO).with_reconnect_delay(Duration::ZERO),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        ),
    );
    let manager_ref = manager.without_state();
    let shared = InjectorShared::new(manager_ref.clone(), graph_index, source.clone(), serving);
    let scan_shared = shared.clone();
    let scan = stage_graph.stage("scan", move |_state: (), _msg: Scan, _eff| {
        let scan_shared = scan_shared.clone();
        let source = source.clone();
        async move {
            scan_shared.publish_inventory(scan_inventory(source.as_ref()));
        }
    });
    let scan = stage_graph.wire_up(scan, ());

    stage_graph
        .preload(&manager_ref, [ManagerMessage::Listen(listen)])
        .map_err(|_| anyhow::anyhow!("failed to preload injector Listen"))?;
    stage_graph.preload(&scan, [Scan]).map_err(|_| anyhow::anyhow!("failed to preload injector Scan"))?;

    Ok((stage_graph.run(tokio_handle), shared))
}

fn put_serve_resources(
    stage_graph: &mut SimulationBuilder,
    connections: ConnectionsResource,
    store: Arc<InMemoryChainStore>,
) {
    stage_graph.resources().put::<ConnectionsResource>(connections);
    stage_graph.resources().put::<ResourceHeaderStore>(store);
    stage_graph.resources().put::<ResourceMempool<Transaction>>(Arc::new(InMemoryMempool::default()));
    stage_graph.resources().put::<ResourceMeter>(Arc::new(Meter::default()));
}

/// Thin ChainSync client used to observe injector reveals. Not [`super::build_world_node`].
pub fn build_injector_peer(
    connections: ConnectionsResource,
    injector: SocketAddr,
    tokio_handle: &Handle,
) -> anyhow::Result<SimulationRunning> {
    let store = Arc::new(InMemoryChainStore::new());
    let mut stage_graph = SimulationBuilder::default().with_eval_strategy(Fifo);
    put_serve_resources(&mut stage_graph, connections, store);

    let manager = stage_graph.stage("manager", amaru_protocols::manager::stage);
    let pipeline = stage_graph.stage("pipeline", peer_pipeline);
    let pipeline = stage_graph.wire_up(pipeline, ());
    let manager = stage_graph.wire_up(
        manager,
        Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default().with_accept_interval(Duration::ZERO).with_reconnect_delay(Duration::ZERO),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            pipeline.without_state(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        ),
    );
    let manager_ref = manager.without_state();
    stage_graph
        .preload(&manager_ref, [ManagerMessage::AddPeer(Peer::new(&injector.to_string()))])
        .map_err(|_| anyhow::anyhow!("failed to preload injector peer AddPeer"))?;
    Ok(stage_graph.run(tokio_handle))
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Scan;

async fn peer_pipeline(_state: (), _msg: ChainSyncInitiatorMsg, _eff: Effects<ChainSyncInitiatorMsg>) {}

#[cfg(test)]
mod tests {
    use amaru_kernel::{
        BlockHeight, NetworkPoint, PREPROD_ERA_HISTORY, Slot, any_headers_chain_with_root,
        cardano::network_block::make_encoded_block, utils::tests::run_strategy,
    };
    use amaru_ouroboros::WriteChainStore;

    use super::*;

    #[test]
    fn test_scan_inventory_empty_store_is_empty() {
        let store = InMemoryChainStore::new();
        assert!(scan_inventory(&store).is_empty());
    }

    #[test]
    fn test_scan_inventory_lists_linear_fragment_in_chain_order() {
        let (store, headers) = primed_linear_store(3);
        let inventory = scan_inventory(&store);
        assert_eq!(inventory.len(), 3);
        for (got, header) in inventory.iter().zip(headers.iter()) {
            assert_eq!(got.hash, header.hash());
            assert_eq!(got.point, header.point());
            assert_eq!(got.slot, header.slot());
            assert_eq!(got.height, header.block_height());
            assert!(got.has_body);
        }
    }

    fn primed_linear_store(n: usize) -> (InMemoryChainStore, Vec<Header>) {
        let conway_start_slot = Slot::from(68_774_400);
        let root = NetworkPoint::Specific(conway_start_slot, amaru_kernel::Hash::new([0u8; 32]));
        let headers = run_strategy(any_headers_chain_with_root(n, root.with_height(BlockHeight::from(0))));
        let store = InMemoryChainStore::new();
        store.set_anchor_point(&headers[0].point()).unwrap();
        for header in &headers {
            store.store_header(header).unwrap();
            store.store_block(&header.hash(), &make_encoded_block(header, &PREPROD_ERA_HISTORY)).unwrap();
            store.roll_forward_chain(&header.point()).unwrap();
        }
        (store, headers)
    }
}
