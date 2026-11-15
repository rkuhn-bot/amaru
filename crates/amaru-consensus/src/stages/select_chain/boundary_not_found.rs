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

//! Acceptance test 8.
//!
//! A best tip whose missing-block walk never meets a stored body or the anchor
//! (`BoundaryNotFound` in `request_missing_blocks`) must not leave fetching stopped.
//! Within a bounded number of simulated steps the node either terminates or asks
//! the network for a later honest tip. The same best tip must not cycle
//! `FetchNextFrom` → `NewBestTip` → `BoundaryNotFound`.

use std::{collections::BTreeMap, sync::Arc, time::Duration};

use amaru_kernel::{BlockHeight, Hash, Header, HeaderHash, IsHeader, Point, Slot, make_header};
use amaru_ouroboros_traits::{WriteChainStore, in_memory_chain_store::InMemoryChainStore};
use amaru_protocols::{manager::ManagerMessage, store_effects::ResourceHeaderStore};
use amaru_pure_stage::{
    Effect, Instant, StageGraph, StageRef, register_data_deserializer,
    simulation::{Blocked, Run, SimulationBuilder, SimulationRunning},
    trace_buffer::{TerminationReason, TraceBuffer, TraceEntry},
};

use super::{SelectChain, SelectChainMsg, stage};
use crate::{
    performance::ResourcePerformance,
    stages::{
        block_source::BlockSourceMsg,
        fetch_blocks::{self, FetchBlocks, FetchBlocksMsg},
        peer_selection::PeerSelectionMsg,
        test_utils::{start_in_era, test_runtime},
    },
};

/// One observation of a missing-block walk that produced no fetch is the most a tip may cost.
const MAX_BOUNDARY_NOT_FOUND_PER_TIP: usize = 1;
const STEP_BUDGET: usize = 800;

#[derive(Debug, Clone, Default, PartialEq, serde::Serialize, serde::Deserialize)]
struct Asked(Vec<(Point, Point)>);

async fn record_fetches(
    mut asked: Asked,
    msg: ManagerMessage,
    _eff: amaru_pure_stage::Effects<ManagerMessage>,
) -> Asked {
    if let ManagerMessage::FetchBlocks { from, through, .. } = msg {
        asked.0.push((from, through));
    }
    asked
}

fn header(height: u64, slot: u64, parent: Option<HeaderHash>) -> Header {
    make_header(height, slot, parent)
}

fn is_fetch_stage(name: &str) -> bool {
    name.split('-').next() == Some("fetch_blocks")
}

/// `NewTip`s that returned to receive without a `FetchBlocks` send, counted per tip hash.
fn boundary_not_found_per_tip(trace: &[TraceEntry]) -> BTreeMap<HeaderHash, usize> {
    let mut counts = BTreeMap::new();
    let mut open: Option<Point> = None;
    let mut fetched = false;
    let close = |counts: &mut BTreeMap<HeaderHash, usize>, open: &mut Option<Point>, fetched: &mut bool| {
        if let Some(tip) = open.take()
            && !*fetched
        {
            *counts.entry(tip.hash()).or_default() += 1;
        }
        *fetched = false;
    };
    for entry in trace {
        match entry {
            TraceEntry::Input { stage, input } if is_fetch_stage(stage.as_str()) => {
                if let Ok(FetchBlocksMsg::NewTip { tip, .. }) = input.cast_ref::<FetchBlocksMsg>() {
                    close(&mut counts, &mut open, &mut fetched);
                    open = Some(*tip);
                }
            }
            TraceEntry::Suspend(Effect::Send { from, msg, .. }) if is_fetch_stage(from.as_str()) => {
                if msg
                    .cast_ref::<ManagerMessage>()
                    .is_ok_and(|message| matches!(message, ManagerMessage::FetchBlocks { .. }))
                {
                    fetched = true;
                }
            }
            TraceEntry::Terminated { stage, .. } if is_fetch_stage(stage.as_str()) => {
                close(&mut counts, &mut open, &mut fetched);
            }
            TraceEntry::Suspend(_)
            | TraceEntry::Resume { .. }
            | TraceEntry::Clock(_)
            | TraceEntry::Input { .. }
            | TraceEntry::State { .. }
            | TraceEntry::Terminated { .. }
            | TraceEntry::InvalidBytes(..) => {}
        }
    }
    close(&mut counts, &mut open, &mut fetched);
    counts
}

fn fetch_stage_terminated(trace: &[TraceEntry]) -> bool {
    trace.iter().any(|entry| {
        matches!(
            entry,
            TraceEntry::Terminated { stage, reason: TerminationReason::Voluntary | TerminationReason::Aborted }
                if is_fetch_stage(stage.as_str())
        )
    })
}

fn resumed_for(trace: &[TraceEntry], tip: Point) -> bool {
    trace.iter().any(|entry| match entry {
        TraceEntry::Suspend(Effect::Send { from, msg, .. }) if is_fetch_stage(from.as_str()) => msg
            .cast_ref::<ManagerMessage>()
            .is_ok_and(|message| matches!(message, ManagerMessage::FetchBlocks { through, .. } if *through == tip)),
        TraceEntry::Suspend(_)
        | TraceEntry::Resume { .. }
        | TraceEntry::Clock(_)
        | TraceEntry::Input { .. }
        | TraceEntry::State { .. }
        | TraceEntry::Terminated { .. }
        | TraceEntry::InvalidBytes(..) => false,
    })
}

fn drive(rt: &tokio::runtime::Runtime, running: &mut SimulationRunning) -> Blocked {
    running.breakpoint("acceptance-8-step", |_| true);
    let mut blocked = Blocked::Idle;
    for _ in 0..STEP_BUDGET {
        blocked = running.run(Run::skip_and_resolve());
        match &blocked {
            Blocked::Breakpoint(_) => continue,
            Blocked::Busy { .. } => {
                rt.block_on(running.await_external_effect());
            }
            Blocked::Idle | Blocked::Sleeping { .. } | Blocked::Terminated(_) | Blocked::Deadlock(_) => break,
        }
    }
    running.clear_breakpoints();
    blocked
}

/// Acceptance test 8: after `BoundaryNotFound`, terminate or resume, and do not retry the same tip.
#[test]
fn test_08_boundary_not_found_terminates_or_resumes() {
    let _fetch_msg = register_data_deserializer::<FetchBlocksMsg>();
    let _manager_msg = register_data_deserializer::<ManagerMessage>();
    let _select_msg = register_data_deserializer::<SelectChainMsg>();

    let anchor = header(10, 100, None);
    let unknown = Hash::new([0xAB; 32]);
    let disconnected = header(11, 500, Some(unknown));
    let honest = header(20, 600, Some(anchor.hash()));
    let disconnected_parent = Point::Specific(Slot::from(1), unknown, BlockHeight::from(0));

    let store = Arc::new(InMemoryChainStore::new());
    store.store_header(&anchor).expect("anchor header");
    store.store_header(&disconnected).expect("disconnected header");
    store.store_header(&honest).expect("honest header");
    store.set_anchor_point(&anchor.point()).expect("anchor point");

    let since = start_in_era().relative_time;
    let mut network = SimulationBuilder::default()
        .with_trace_buffer(TraceBuffer::new_shared(100, 1_000_000))
        .with_global_epoch_offset(since)
        .with_initial_clock(Instant::at_offset(Duration::from_secs(10), since));
    network.resources().put::<ResourceHeaderStore>(store);
    network.resources().put::<ResourcePerformance>(Arc::new(crate::performance::Performance::new()));

    let select_build = network.stage("select_chain", stage);
    let fetch_build = network.stage("fetch_blocks", fetch_blocks::stage);
    let manager_build = network.stage("manager", record_fetches);
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
    let fetch_input = fetch.contramap(|msg: super::NewBestTip| FetchBlocksMsg::NewTip {
        tip: msg.tip,
        parent: msg.parent,
        trace_context: msg.trace_context,
    });
    let select = network.wire_up(select_build, SelectChain::new(fetch_input));
    let _manager = network.wire_up(manager_build, Asked::default());
    network
        .preload(
            &select,
            [
                SelectChainMsg::fetch_next_from(Point::Origin),
                SelectChainMsg::tip_from_upstream(disconnected.point(), disconnected_parent),
                SelectChainMsg::tip_from_upstream(honest.point(), anchor.point()),
            ],
        )
        .expect("preload chain selection");

    let rt = test_runtime();
    let mut running = network.run(rt.handle());
    let blocked = drive(&rt, &mut running);
    let trace = running.trace_buffer().lock().hydrate_without_timestamps();
    let per_tip = boundary_not_found_per_tip(&trace);
    let terminated = fetch_stage_terminated(&trace) || matches!(blocked, Blocked::Terminated(_));
    let resumed = resumed_for(&trace, honest.point());

    if matches!(blocked, Blocked::Idle | Blocked::Sleeping { .. }) {
        let best = running.get_state(&select).and_then(|state| state.best_tip.as_ref().map(IsHeader::hash));
        assert_eq!(
            best,
            Some(honest.hash()),
            "precondition: the honest tip must be the best tip before the acceptance checks; blocked={blocked:?}"
        );
    }

    assert!(
        terminated || resumed,
        "acceptance test 8: after BoundaryNotFound the node must terminate or resume fetching within {STEP_BUDGET} steps; terminated={terminated} resumed={resumed} blocked={blocked:?} boundary_not_found={per_tip:?}"
    );
    let repeated: Vec<_> = per_tip.iter().filter(|(_, count)| **count > MAX_BOUNDARY_NOT_FOUND_PER_TIP).collect();
    assert!(
        repeated.is_empty(),
        "acceptance test 8: BoundaryNotFound must occur at most {MAX_BOUNDARY_NOT_FOUND_PER_TIP} time per best tip; counts={per_tip:?}"
    );
}
