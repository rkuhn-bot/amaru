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

//! Height-deferred headers released in one turn, while the initiator still has a full mailbox.
//!
//! The initiator mailbox is [`CHAINSYNC_INITIATOR_MAILBOX`] (pipeline depth + 4). `track_peers`
//! uses the default 10-slot mailbox. Releasing a deferred batch sends one `RequestNext` per
//! header without returning to receive.

use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use amaru_kernel::{EraName, Header, IsHeader, PREPROD_ERA_HISTORY, Peer, Point, make_header};
use amaru_ouroboros::ConnectionId;
use amaru_ouroboros_traits::{Nonces, in_memory_chain_store::InMemoryChainStore};
use amaru_protocols::{
    chainsync::{CHAINSYNC_INITIATOR_MAILBOX, ChainSyncInitiatorMsg, HeaderContent, InitiatorMessage, InitiatorResult},
    store_effects::ResourceHeaderStore,
};
use amaru_pure_stage::{
    DEFAULT_MAILBOX_SIZE, Effects, Instant, StageGraph, StageRef,
    simulation::{Blocked, Run, SimulationBuilder, running::OverrideResult},
    trace_buffer::TraceBuffer,
};

use super::{NewTip, TrackPeers, TrackPeersMsg, stage};
use crate::{
    effects::{ValidateHeaderEffect, VolatileTipEffect},
    performance::ResourcePerformance,
    stages::{
        peer_selection::PeerSelectionMsg,
        test_utils::{start_in_era, test_runtime},
    },
};

const DEFERRED: u64 = 16;
const CONWAY_START: u64 = 68_774_401;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct InitiatorState {
    peer: Peer,
    conn_id: ConnectionId,
    track_peers: StageRef<TrackPeersMsg>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
enum InitiatorIngress {
    Forward { header: Header, handler: StageRef<InitiatorMessage> },
    RequestNext,
    Done,
}

fn local_ingress(msg: InitiatorMessage) -> InitiatorIngress {
    match msg {
        InitiatorMessage::RequestNext => InitiatorIngress::RequestNext,
        InitiatorMessage::Done => InitiatorIngress::Done,
    }
}

async fn initiator(state: InitiatorState, msg: InitiatorIngress, eff: Effects<InitiatorIngress>) -> InitiatorState {
    if let InitiatorIngress::Forward { header, handler } = msg {
        let tip = header.point();
        eff.send(
            &state.track_peers,
            TrackPeersMsg::FromUpstream(ChainSyncInitiatorMsg {
                peer: state.peer,
                conn_id: state.conn_id,
                handler,
                msg: InitiatorResult::RollForward(HeaderContent::new(&header, EraName::Conway), tip),
            }),
        )
        .await;
    }
    state
}

async fn count_tips(count: u64, _msg: NewTip, _eff: Effects<NewTip>) -> u64 {
    count + 1
}

fn chain(from_height: u64, count: u64, parent: Option<amaru_kernel::HeaderHash>) -> Vec<Header> {
    let mut parent = parent;
    let mut headers = Vec::with_capacity(count as usize);
    for offset in 0..count {
        let height = from_height + offset;
        let header = make_header(height, CONWAY_START + height - 1, parent);
        parent = Some(header.hash());
        headers.push(header);
    }
    headers
}

/// Releasing every height-deferred header must still deliver those headers downstream.
#[test]
fn test_deferred_release_makes_progress_with_full_initiator_mailbox() {
    let deferred = chain(1, DEFERRED, None);
    let burst = chain(DEFERRED + 1, CHAINSYNC_INITIATOR_MAILBOX as u64, deferred.last().map(IsHeader::hash));
    let peer = Peer::for_test(4101);
    let conn_id = ConnectionId::initial();
    let epoch = start_in_era().epoch;
    let advanced = deferred.last().expect("deferred chain").point();
    let release = Arc::new(AtomicBool::new(false));

    let since = start_in_era().relative_time;
    let mut network = SimulationBuilder::default()
        .with_trace_buffer(TraceBuffer::new_shared(100, 1_000_000))
        .with_global_epoch_offset(since)
        .with_initial_clock(Instant::at_offset(Duration::from_secs(10), since));
    let store = Arc::new(InMemoryChainStore::new());
    network.resources().put::<ResourceHeaderStore>(store);
    network.resources().put::<ResourcePerformance>(Arc::new(crate::performance::Performance::new()));

    let track_build = network.stage("aa_track_peers", stage);
    let down_build = network.stage("mm_downstream", count_tips);
    let init_build = network.stage_with_mailbox_size("zz_initiator", initiator, CHAINSYNC_INITIATOR_MAILBOX);

    let downstream = network.wire_up(down_build, 0u64);
    let initiator_ref =
        network.wire_up(init_build, InitiatorState { peer, conn_id, track_peers: track_build.sender() });
    let handler = initiator_ref.contramap(local_ingress);
    let downstream_ref = StageRef::clone(&downstream);
    let track = network.wire_up(
        track_build,
        TrackPeers::new(
            PREPROD_ERA_HISTORY.clone(),
            StageRef::<PeerSelectionMsg>::named_for_tests("peer_selection"),
            downstream_ref,
            0,
            epoch,
        ),
    );

    let mut intake = vec![
        TrackPeersMsg::FromUpstream(ChainSyncInitiatorMsg {
            peer,
            conn_id,
            handler: handler.clone(),
            msg: InitiatorResult::Initialize,
        }),
        TrackPeersMsg::FromUpstream(ChainSyncInitiatorMsg {
            peer,
            conn_id,
            handler: handler.clone(),
            msg: InitiatorResult::IntersectFound(Point::Origin, deferred.last().expect("deferred chain").point()),
        }),
    ];
    intake.extend(deferred.iter().map(|header| {
        TrackPeersMsg::FromUpstream(ChainSyncInitiatorMsg {
            peer,
            conn_id,
            handler: handler.clone(),
            msg: InitiatorResult::RollForward(HeaderContent::new(header, EraName::Conway), header.point()),
        })
    }));
    let first_batch: Vec<_> = intake.drain(..DEFAULT_MAILBOX_SIZE.min(intake.len())).collect();
    network.preload(&track, first_batch).expect("preload first deferred batch");

    let rt = test_runtime();
    let mut running = network.run(rt.handle());
    let flag = release.clone();
    running.override_external_effect::<VolatileTipEffect>(usize::MAX, move |_| {
        if flag.load(Ordering::SeqCst) {
            OverrideResult::handled(advanced)
        } else {
            OverrideResult::handled(Point::Origin)
        }
    });
    running.override_external_effect::<ValidateHeaderEffect>(usize::MAX, |_| {
        OverrideResult::handled(Ok(Nonces::for_tests()))
    });

    let mut parked = drive_until_sleep(&rt, &mut running);
    while !intake.is_empty() {
        let n = DEFAULT_MAILBOX_SIZE.min(intake.len());
        let batch: Vec<_> = intake.drain(..n).collect();
        running.enqueue_msg(&track, batch);
        parked = drive_until_sleep(&rt, &mut running);
    }
    let deferred_len = running.get_state(&track).map(|state| state.deferred.len()).unwrap_or(usize::MAX);
    assert_eq!(
        deferred_len, DEFERRED as usize,
        "fixture: intake must height-defer every header before the burst; blocked={parked:?}"
    );

    release.store(true, Ordering::SeqCst);
    running.enqueue_msg(&track, [TrackPeersMsg::RecheckLedgerHeight]);
    running.enqueue_msg(
        &initiator_ref,
        burst.into_iter().map(|header| InitiatorIngress::Forward { header, handler: handler.clone() }),
    );
    let blocked = drive_bounded(&rt, &mut running);
    let tips = running.get_state(&downstream).copied().unwrap_or(0);
    let still_deferred = running.get_state(&track).map(|state| state.deferred.len());
    assert!(
        !matches!(blocked, Blocked::Deadlock(_)) && tips >= DEFERRED,
        "releasing {DEFERRED} height-deferred headers must make progress with initiator mailbox {CHAINSYNC_INITIATOR_MAILBOX} and track_peers mailbox {DEFAULT_MAILBOX_SIZE}; tips={tips} deferred={still_deferred:?} blocked={blocked:?}"
    );
}

const STEP_BUDGET: usize = 4_000;

fn drive_until_sleep(
    rt: &tokio::runtime::Runtime,
    running: &mut amaru_pure_stage::simulation::SimulationRunning,
) -> Blocked {
    for _ in 0..STEP_BUDGET {
        match running.run(Run::default()) {
            Blocked::Busy { .. } => {
                rt.block_on(running.await_external_effect());
            }
            other @ (Blocked::Idle
            | Blocked::Sleeping { .. }
            | Blocked::Deadlock(_)
            | Blocked::Breakpoint(_)
            | Blocked::Terminated(_)) => return other,
        }
    }
    panic!("deferred intake did not settle within {STEP_BUDGET} steps");
}

fn drive_bounded(
    rt: &tokio::runtime::Runtime,
    running: &mut amaru_pure_stage::simulation::SimulationRunning,
) -> Blocked {
    running.breakpoint("mailbox-cycle-step", |_| true);
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
