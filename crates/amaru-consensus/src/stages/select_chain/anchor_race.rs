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

//! Acceptance test 9.
//!
//! `select_chain` picks a fork whose fork point is still above the anchor. Adopting
//! the previous best then runs `drag_anchor_forward`, which moves the anchor past
//! that fork point before `fetch_blocks` searches for missing blocks. The search
//! stops on slot and returns `BoundaryNotFound`. The fork stays the best tip, so
//! the honest chain is never fetched.

use std::{sync::Arc, time::Duration};

use amaru_kernel::{EraHistory, Header, IsHeader, Point, RawBlock, make_header};
use amaru_ouroboros::MempoolMsg;
use amaru_ouroboros_traits::{
    BaseReadChainStore, MissingBlocksResult, ReadChainStore, WriteChainStore, in_memory_chain_store::InMemoryChainStore,
};
use amaru_protocols::{manager::ManagerMessage, store_effects::ResourceHeaderStore};
use amaru_pure_stage::{
    Effects, Instant, StageGraph, StageRef,
    simulation::{Blocked, Run, SimulationBuilder, SimulationRunning},
    trace_buffer::TraceBuffer,
};

use super::{SelectChain, SelectChainMsg, stage};
use crate::{
    performance::ResourcePerformance,
    stages::{
        adopt_chain::{self, AdoptChain, AdoptChainMsg},
        block_source::BlockSourceMsg,
        fetch_blocks::{self, FetchBlocks, FetchBlocksMsg},
        peer_selection::PeerSelectionMsg,
        test_utils::{start_in_era, test_runtime},
    },
};

/// `k` for this script. Adopting the honest tip drags the anchor to height `tip - k`.
const SECURITY_PARAM: u64 = 2;
const STEP_BUDGET: usize = 2_000;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct Announce {
    select: StageRef<SelectChainMsg>,
    tip: Point,
    parent: Point,
}

#[derive(Debug, Clone, Copy, PartialEq, serde::Serialize, serde::Deserialize)]
struct Tick;

async fn announce(state: Announce, _tick: Tick, eff: Effects<Tick>) -> Announce {
    eff.send(&state.select, SelectChainMsg::tip_from_upstream(state.tip, state.parent)).await;
    state
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
enum HoldMsg {
    Tip(super::NewBestTip),
    Release,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct HoldBestTip {
    fetch: StageRef<FetchBlocksMsg>,
    held: Option<super::NewBestTip>,
    released: bool,
}

async fn hold_best_tip(mut state: HoldBestTip, msg: HoldMsg, eff: Effects<HoldMsg>) -> HoldBestTip {
    match msg {
        HoldMsg::Tip(tip) if state.released => forward(&state, &eff, tip).await,
        HoldMsg::Tip(tip) => state.held = Some(tip),
        HoldMsg::Release => {
            state.released = true;
            if let Some(tip) = state.held.take() {
                forward(&state, &eff, tip).await;
            }
        }
    }
    state
}

async fn forward(state: &HoldBestTip, eff: &Effects<HoldMsg>, tip: super::NewBestTip) {
    eff.send(&state.fetch, FetchBlocksMsg::new_tip(tip.tip, tip.parent)).await;
}

#[derive(Debug, Clone, Default, PartialEq, serde::Serialize, serde::Deserialize)]
struct Asked(Vec<(Point, Point)>);

async fn record_fetches(mut asked: Asked, msg: ManagerMessage, _eff: Effects<ManagerMessage>) -> Asked {
    if let ManagerMessage::FetchBlocks { from, through, .. } = msg {
        asked.0.push((from, through));
    }
    asked
}

fn header(height: u64, slot: u64, parent: Option<amaru_kernel::HeaderHash>) -> Header {
    make_header(height, slot, parent)
}

fn drive(rt: &tokio::runtime::Runtime, running: &mut SimulationRunning) -> Blocked {
    let mut blocked = Blocked::Idle;
    for _ in 0..STEP_BUDGET {
        blocked = running.run(Run::skip_and_resolve());
        match &blocked {
            Blocked::Breakpoint(_) => continue,
            Blocked::Busy { .. } => {
                rt.block_on(running.await_external_effect());
            }
            Blocked::Idle | Blocked::Sleeping { .. } | Blocked::Terminated(_) | Blocked::Deadlock(_) => {
                return blocked;
            }
        }
    }
    blocked
}

/// Acceptance test 9: a fork stranded by the anchor drag must lose to the honest chain.
#[test]
fn test_09_anchor_past_fork_point_switches_to_honest_chain() {
    let anchor = header(10, 100, None);
    let fork_point = header(11, 110, Some(anchor.hash()));
    let honest_12 = header(12, 120, Some(fork_point.hash()));
    let dragged = header(13, 130, Some(honest_12.hash()));
    let honest_14 = header(14, 140, Some(dragged.hash()));
    let honest = header(15, 150, Some(honest_14.hash()));
    let fork_12 = header(12, 115, Some(fork_point.hash()));
    let fork_13 = header(13, 125, Some(fork_12.hash()));
    let fork_14 = header(14, 135, Some(fork_13.hash()));
    let fork_15 = header(15, 145, Some(fork_14.hash()));
    let fork = header(16, 155, Some(fork_15.hash()));

    let store = Arc::new(InMemoryChainStore::new());
    for header in
        [&anchor, &fork_point, &honest_12, &dragged, &honest_14, &honest, &fork_12, &fork_13, &fork_14, &fork_15, &fork]
    {
        store.store_header(header).expect("store header");
    }
    let body = RawBlock::from([1u8].as_slice());
    store.store_block(&anchor.hash(), &body).expect("anchor body");
    store.store_block(&fork_point.hash(), &body).expect("fork-point body");
    store.roll_forward_chain(&anchor.point()).expect("best chain anchor");
    store.roll_forward_chain(&fork_point.point()).expect("best chain fork point");
    store.set_anchor_point(&anchor.point()).expect("anchor still below the fork point");

    let since = start_in_era().relative_time;
    let mut network = SimulationBuilder::default()
        .with_trace_buffer(TraceBuffer::new_shared(100, 1_000_000))
        .with_global_epoch_offset(since)
        .with_initial_clock(Instant::at_offset(Duration::from_secs(10), since));
    network.resources().put::<ResourceHeaderStore>(store.clone());
    network.resources().put::<EraHistory>(EraHistory::default());
    network.resources().put::<ResourcePerformance>(Arc::new(crate::performance::Performance::new()));

    let select_build = network.stage("select_chain", stage);
    let fetch_build = network.stage("fetch_blocks", fetch_blocks::stage);
    let hold_build = network.stage("hold_best_tip", hold_best_tip);
    let adopt_build = network.stage("adopt_chain", adopt_chain::stage);
    let manager_build = network.stage("block_manager", record_fetches);
    let fork_build = network.stage("aa_fork_peer", announce);
    let honest_build = network.stage("bb_honest_peer", announce);

    let fetch = network.wire_up(
        fetch_build,
        FetchBlocks::new(
            StageRef::named_for_tests("validate_block"),
            select_build.sender(),
            manager_build.sender(),
            StageRef::<BlockSourceMsg>::named_for_tests("block_source"),
            StageRef::<PeerSelectionMsg>::named_for_tests("peer_selection"),
        ),
    );
    let hold = network.wire_up(hold_build, HoldBestTip { fetch: StageRef::clone(&fetch), held: None, released: false });
    let select = network.wire_up(select_build, SelectChain::new(hold.contramap(HoldMsg::Tip)));
    let adopt = network.wire_up(
        adopt_build,
        AdoptChain::new(
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::<MempoolMsg>::blackhole(),
            SECURITY_PARAM,
            fork_point.point(),
        ),
    );
    let manager = network.wire_up(manager_build, Asked::default());
    let fork_peer = network
        .wire_up(fork_build, Announce { select: StageRef::clone(&select), tip: fork.point(), parent: fork_15.point() });
    let honest_peer = network.wire_up(
        honest_build,
        Announce { select: StageRef::clone(&select), tip: honest.point(), parent: honest_14.point() },
    );

    network.preload(&select, [SelectChainMsg::fetch_next_from(Point::Origin)]).expect("arm fetching");

    let rt = test_runtime();
    let mut running = network.run(rt.handle());
    running.breakpoint("acceptance-9-step", |_| true);

    let armed = drive(&rt, &mut running);
    assert!(matches!(armed, Blocked::Idle), "fetch token must be armed before the peers announce; blocked={armed:?}");

    let reachable = store.find_missing_blocks(fork.hash(), 25).expect("missing-block search before the anchor drag");
    assert!(
        matches!(reachable, MissingBlocksResult::Found(_)),
        "precondition: the fork is fetchable while its fork point is above the anchor; search={reachable:?}"
    );

    running.enqueue_msg(&fork_peer, [Tick]);
    running.enqueue_msg(&honest_peer, [Tick]);
    let selected = drive(&rt, &mut running);
    let best = running.get_state(&select).and_then(|state| state.best_tip.as_ref().map(IsHeader::hash));
    let held = running.get_state(&hold).and_then(|state| state.held.as_ref().map(|tip| tip.tip));
    assert_eq!(
        (best, held, &selected),
        (Some(fork.hash()), Some(fork.point()), &Blocked::Idle),
        "precondition: the fork peer's tip is selected and held until adoption moves the anchor"
    );

    running.enqueue_msg(&adopt, [AdoptChainMsg::new(honest.point(), honest.block_height())]);
    let adopted = drive(&rt, &mut running);
    assert!(
        matches!(adopted, Blocked::Idle),
        "adopting the honest chain must finish before the held fork tip is fetched; blocked={adopted:?}"
    );
    assert_eq!(
        store.get_anchor_point(),
        dragged.point(),
        "precondition: drag_anchor_forward must move the anchor past the fork point"
    );
    let stranded = store.find_missing_blocks(fork.hash(), 25).expect("missing-block search after the anchor drag");
    assert!(
        matches!(stranded, MissingBlocksResult::BoundaryNotFound),
        "precondition: the fork no longer meets a stored body or the anchor; search={stranded:?}"
    );

    running.enqueue_msg(&hold, [HoldMsg::Release]);
    let blocked = drive(&rt, &mut running);
    let best = running.get_state(&select).and_then(|state| state.best_tip.as_ref().map(IsHeader::hash));
    let fetched = running.get_state(&manager).map(|state| state.0.clone()).unwrap_or_default();
    let resumed = fetched.iter().any(|(_, through)| *through == honest.point());
    assert!(
        best == Some(honest.hash()) && resumed,
        "acceptance test 9: after the anchor moves past the fork point the node must switch to the honest chain and resume fetching within {STEP_BUDGET} steps; best={best:?} honest={} fork={} resumed={resumed} fetched={fetched:?} blocked={blocked:?}",
        honest.hash(),
        fork.hash()
    );
}
