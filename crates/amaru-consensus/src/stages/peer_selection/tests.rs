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

use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use amaru_kernel::PeerCandidate;
use amaru_observability::tracing::Level;
use amaru_ouroboros::{ConnectionDirection, ConnectionId, ObservedAt, PeerTracking};
use amaru_protocols::{connection::LocalUse, manager::ManagerMessage};
use amaru_pure_stage::{Effect, simulation::SimulationRunning, trace_buffer::TraceEntry};

use super::*;
use crate::{
    performance::{PeerView, ResourcePerformance, ViewConnection},
    stages::{
        peer_selection::test_setup::{SIM_INITIAL_CLOCK_SECS, TestPrep, setup, sim_t0, test_prep},
        test_utils::start_in_era,
    },
};

fn peer_view(
    generation: u64,
    connections: Vec<ViewConnection>,
    connect_failures: BTreeMap<Peer, ObservedAt>,
) -> PeerView {
    PeerView { generation, connections, connect_failures, uninteresting: Vec::new() }
}

fn view_conn(peer: Peer, conn_id: ConnectionId, direction: ConnectionDirection, local_use: LocalUse) -> ViewConnection {
    ViewConnection {
        peer,
        conn_id,
        direction,
        full_duplex_capable: true,
        full_duplex: direction == ConnectionDirection::Inbound,
        advertisable: false,
        local_use,
    }
}

fn connected(peer: Peer, conn_id: ConnectionId, wanted: LocalUse, applied: LocalUse) -> OutboundIntent {
    let mut bearer = DesiredBearer::adopt(&view_conn(peer, conn_id, ConnectionDirection::Outbound, applied), wanted);
    bearer.local_use_sent_at = Some(sim_t0());
    OutboundIntent::Connected(bearer)
}

fn far_deadlines(state: &mut PeerSelection) {
    state.next_churn_at = Some(sim_t0() + Duration::from_secs(3600));
    state.next_sweep_at = Some(sim_t0() + Duration::from_secs(30));
}

fn suspends(running: &SimulationRunning) -> Vec<Effect> {
    running
        .trace_buffer()
        .lock()
        .iter_entries()
        .filter_map(|(_, entry)| if let TraceEntry::Suspend(effect) = entry { Some(effect) } else { None })
        .collect()
}

fn manager_sends(running: &SimulationRunning) -> Vec<ManagerMessage> {
    suspends(running)
        .into_iter()
        .filter_map(|effect| {
            if let Effect::Send { msg, .. } = effect { msg.cast::<ManagerMessage>().ok().map(|msg| *msg) } else { None }
        })
        .collect()
}

fn timeout_delays(running: &SimulationRunning) -> Vec<Duration> {
    suspends(running)
        .into_iter()
        .filter_map(|effect| if let Effect::SetTimeout { delay, .. } = effect { Some(delay) } else { None })
        .collect()
}

fn ps_state(running: &SimulationRunning) -> PeerSelection {
    let mut found = None;
    for (_, entry) in running.trace_buffer().lock().iter_entries() {
        if let TraceEntry::State { stage, state } = entry
            && stage.as_str() == "ps-1"
            && let Ok(state) = state.cast::<PeerSelection>()
        {
            found = Some(*state);
        }
    }
    found.expect("peer selection state")
}

fn counted_external<T: amaru_pure_stage::ExternalEffect>(running: &SimulationRunning) -> usize {
    suspends(running)
        .into_iter()
        .filter(|effect| matches!(effect, Effect::External { effect, .. } if effect.is::<T>()))
        .count()
}

#[test]
fn initialize_dials_static_peers_and_arms_one_timeout() {
    let prep = test_prep(&["10.0.0.1:1", "10.0.0.2:2"]);
    let (running, _guards, mut logs) = setup(&prep, PeerSelectionMsg::Initialize);
    let sends = manager_sends(&running);
    assert_eq!(sends.iter().filter(|msg| matches!(msg, ManagerMessage::AddPeer(_))).count(), 2);
    let delays = timeout_delays(&running);
    assert_eq!(delays.len(), 1);
    assert_eq!(delays[0], Duration::from_secs(1));
    logs.assert_and_remove(Level::INFO, &["peer_selection.connect_initial", "static_peers=2"])
        .assert_no_remaining_at([Level::WARN, Level::ERROR]);
}

#[test]
fn refill_after_a_close_dials_the_next_static_peer() {
    let gone = TestPrep::peer("1.1.1.1:1");
    let next = TestPrep::peer("2.2.2.2:2");
    let mut prep = test_prep(&["2.2.2.2:2"]);
    prep.state.target_upstream_peers = 1;
    prep.state
        .outbound_peers
        .insert(gone, connected(gone, ConnectionId::initial(), LocalUse::Diffusion, LocalUse::Diffusion));
    far_deadlines(&mut prep.state);
    prep.scripted_view = Some(peer_view(1, Vec::new(), BTreeMap::new()));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let sends = manager_sends(&running);
    assert_eq!(sends, vec![ManagerMessage::AddPeer(next)]);
    assert!(!ps_state(&running).outbound_peers.contains_key(&gone));
}

#[test]
fn dial_with_no_outcome_is_held_off() {
    let peer = TestPrep::peer("4.4.4.4:4");
    let mut prep = test_prep(&["4.4.4.4:4"]);
    prep.state.target_upstream_peers = 1;
    prep.state.connection_timeout = Duration::ZERO;
    let since = amaru_pure_stage::Instant::at_offset(Duration::from_secs(2), start_in_era().relative_time);
    prep.state.outbound_peers.insert(peer, OutboundIntent::Dialing { since, candidate: PeerCandidate::from(peer) });
    far_deadlines(&mut prep.state);

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let state = ps_state(&running);
    assert!(state.outbound_peers.is_empty());
    assert!(state.dial_holdoff.contains_key(&PeerCandidate::from(peer)));
    assert!(manager_sends(&running).is_empty());
}

#[test]
fn banned_inbound_reconnect_is_disconnected() {
    let peer = TestPrep::peer("5.5.5.5:5");
    let conn_id = ConnectionId::initial();
    let mut prep = test_prep(&[]);
    prep.state.cooldowns.cooldown_until.insert(peer, sim_t0() + Duration::from_secs(60));
    far_deadlines(&mut prep.state);
    prep.scripted_view = Some(peer_view(
        1,
        vec![view_conn(peer, conn_id, ConnectionDirection::Inbound, LocalUse::None)],
        BTreeMap::new(),
    ));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(manager_sends(&running), vec![ManagerMessage::Disconnect(peer, conn_id)]);
    assert!(!ps_state(&running).inbound_peers.contains_key(&peer));
}

#[test]
fn adversarial_reports_during_a_ban_remove_the_peer_once() {
    let peer = TestPrep::peer("6.6.6.6:6");
    let prep = test_prep(&[]);
    let (running, _guards, mut logs) = crate::stages::peer_selection::test_setup::setup_preload(
        &prep,
        [PeerSelectionMsg::adversarial(peer), PeerSelectionMsg::adversarial(peer), PeerSelectionMsg::adversarial(peer)],
    );
    let removes = manager_sends(&running)
        .into_iter()
        .filter(|msg| matches!(msg, ManagerMessage::RemovePeer(p) if *p == peer))
        .count();
    assert_eq!(removes, 1);
    assert_eq!(counted_external::<crate::performance::PeerAdversarialEffect>(&running), 1);
    assert_eq!(
        ps_state(&running).cooldowns.cooldown_until.get(&peer).copied(),
        Some(sim_t0() + Duration::from_secs(1))
    );
    logs.assert_and_remove(Level::DEBUG, &["peer_selection.peer.adversarial_duplicate"])
        .assert_and_remove(Level::DEBUG, &["peer_selection.peer.adversarial_duplicate"]);
    let _ = logs;
}

#[test]
fn a_round_sends_at_most_upstream_plus_downstream_commands() {
    let mut prep = test_prep(&[]);
    prep.state.target_upstream_peers = 1;
    prep.state.target_downstream_peers = 1;
    far_deadlines(&mut prep.state);
    let mut ids = ConnectionId::initial();
    let mut connections = Vec::new();
    for n in 1..=5u16 {
        let peer = TestPrep::peer(&format!("7.0.0.{n}:7"));
        let conn_id = ids.get_and_increment();
        prep.state.cooldowns.cooldown_until.insert(peer, sim_t0() + Duration::from_secs(60));
        connections.push(view_conn(peer, conn_id, ConnectionDirection::Inbound, LocalUse::None));
    }
    prep.scripted_view = Some(peer_view(1, connections, BTreeMap::new()));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let disconnects =
        manager_sends(&running).into_iter().filter(|msg| matches!(msg, ManagerMessage::Disconnect(..))).count();
    assert_eq!(disconnects, 2);
}

#[test]
fn idle_tick_skips_the_round_when_nothing_is_due() {
    let mut prep = test_prep(&["8.8.8.8:8"]);
    far_deadlines(&mut prep.state);
    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(counted_external::<crate::performance::SelectOutboundEffect>(&running), 0);
    assert_eq!(counted_external::<crate::effects::GenerateRandomSeed>(&running), 0);
    assert_eq!(timeout_delays(&running), vec![Duration::from_secs(1)]);
    assert!(manager_sends(&running).is_empty());
}

#[test]
fn a_due_sweep_runs_a_round_without_a_new_view() {
    let mut prep = test_prep(&[]);
    prep.state.next_churn_at = Some(sim_t0() + Duration::from_secs(3600));
    prep.state.next_sweep_at = Some(sim_t0());
    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(counted_external::<crate::performance::SelectOutboundEffect>(&running), 1);
}

#[test]
fn the_timeout_is_armed_for_the_earliest_deadline() {
    let mut prep = test_prep(&[]);
    far_deadlines(&mut prep.state);
    prep.state
        .dial_holdoff
        .insert(PeerCandidate::from(TestPrep::peer("9.9.9.1:9")), sim_t0() + Duration::from_millis(200));
    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(counted_external::<crate::performance::SelectOutboundEffect>(&running), 0);
    assert_eq!(timeout_delays(&running), vec![Duration::from_millis(200)]);
}

#[test]
fn a_failure_next_to_a_live_outbound_keeps_that_connection() {
    let peer = TestPrep::peer("9.9.9.9:9");
    let conn_id = ConnectionId::initial();
    let alias = PeerCandidate::host("relay.example".parse().unwrap(), 3001);
    let mut prep = test_prep(&[]);
    prep.state
        .outbound_peers
        .insert(peer, OutboundIntent::Dialing { since: sim_t0(), candidate: PeerCandidate::from(peer) });
    // A failed dial unbinds the name. Keeping this binding shows the failure was not applied.
    prep.state.bound.insert(alias.clone(), peer);
    far_deadlines(&mut prep.state);
    let mut connect_failures = BTreeMap::new();
    connect_failures.insert(peer, ObservedAt::new(Duration::from_secs(10), start_in_era().relative_time));
    prep.scripted_view = Some(peer_view(
        1,
        vec![view_conn(peer, conn_id, ConnectionDirection::Outbound, LocalUse::Diffusion)],
        connect_failures,
    ));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let state = ps_state(&running);
    match state.outbound_peers.get(&peer) {
        Some(OutboundIntent::Connected(bearer)) => {
            assert_eq!(bearer.id, conn_id);
            assert_eq!(bearer.wanted, LocalUse::Diffusion);
        }
        other => panic!("live outbound was not kept: {other:?}"),
    }
    assert!(state.bound.contains_key(&alias), "failure must not unbind the live peer");
    assert!(!manager_sends(&running).iter().any(|msg| matches!(msg, ManagerMessage::Disconnect(..))));
}

#[test]
fn churn_demotes_the_worst_non_static_peer_without_asking_per_peer() {
    let mut prep = test_prep(&[]);
    prep.state.next_churn_at = Some(sim_t0());
    prep.state.next_sweep_at = Some(sim_t0() + Duration::from_secs(30));
    let mut ids = ConnectionId::initial();
    let mut connections = Vec::new();
    for name in ["1.1.1.1:1", "2.2.2.2:2", "3.3.3.3:3"] {
        let peer = TestPrep::peer(name);
        let conn_id = ids.get_and_increment();
        prep.state.outbound_peers.insert(peer, connected(peer, conn_id, LocalUse::Diffusion, LocalUse::Diffusion));
        connections.push(view_conn(peer, conn_id, ConnectionDirection::Outbound, LocalUse::Diffusion));
    }
    prep.scripted_view = Some(peer_view(1, connections, BTreeMap::new()));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let demoted: Vec<_> = manager_sends(&running)
        .into_iter()
        .filter_map(|msg| {
            if let ManagerMessage::SetLocalUse { peer, local_use: LocalUse::Maintenance, .. } = msg {
                Some(peer)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(demoted, vec![TestPrep::peer("1.1.1.1:1")]);
    assert_eq!(counted_external::<crate::performance::IsStaticPeerEffect>(&running), 0);
}

#[test]
fn a_share_result_with_new_candidates_dials_on_the_next_round() {
    let learned = TestPrep::peer("8.8.8.8:8");
    let donor = TestPrep::peer("9.9.9.9:9");
    let mut prep = test_prep(&[]);
    prep.state.target_upstream_peers = 1;
    prep.peer_mix = "shared~1".parse().expect("shared-only mix");
    far_deadlines(&mut prep.state);
    prep.learned_share = Some((donor, std::net::SocketAddr::from(learned)));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(manager_sends(&running), vec![ManagerMessage::AddPeer(learned)]);
}

fn set_local_uses(running: &SimulationRunning) -> Vec<(Peer, LocalUse)> {
    manager_sends(running)
        .into_iter()
        .filter_map(|msg| {
            if let ManagerMessage::SetLocalUse { peer, local_use, .. } = msg { Some((peer, local_use)) } else { None }
        })
        .collect()
}

fn wanted(state: &PeerSelection, peer: Peer) -> LocalUse {
    match state.outbound_peers.get(&peer) {
        Some(OutboundIntent::Connected(bearer)) => bearer.wanted,
        other => panic!("expected a connected bearer for {peer}, got {other:?}"),
    }
}

fn drive_until(running: &mut SimulationRunning, until: amaru_pure_stage::Instant) {
    use amaru_pure_stage::simulation::{Externals, Run, TimeAdvance};
    running.run(Run { time: TimeAdvance::Until(until), externals: Externals::Resolve });
}

#[test]
fn an_uninteresting_mark_demotes_on_the_next_round_and_promotes_when_due() {
    let peer = TestPrep::peer("1.2.3.4:4");
    let conn_id = ConnectionId::initial();
    let mut prep = test_prep(&["1.2.3.4:4"]);
    prep.state.target_upstream_peers = 1;
    far_deadlines(&mut prep.state);
    prep.established = Some((peer, conn_id));
    prep.uninteresting = Some((peer, conn_id, false));

    let (mut running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let state = ps_state(&running);
    assert_eq!(wanted(&state, peer), LocalUse::Maintenance);
    assert_eq!(state.demoted_until.get(&peer).copied(), Some(sim_t0() + UNINTERESTING_RETRY));
    assert_eq!(set_local_uses(&running), vec![(peer, LocalUse::Maintenance)]);

    let deadline = sim_t0() + UNINTERESTING_RETRY;
    drive_until(&mut running, deadline);
    let state = ps_state(&running);
    assert_eq!(wanted(&state, peer), LocalUse::Diffusion);
    assert!(!state.demoted_until.contains_key(&peer));
    let uses = set_local_uses(&running);
    assert_eq!(uses.first().copied(), Some((peer, LocalUse::Maintenance)));
    assert_eq!(uses.last().copied(), Some((peer, LocalUse::Diffusion)));
    assert_eq!(uses.iter().filter(|(_, local_use)| *local_use == LocalUse::Diffusion).count(), 1);
}

#[test]
fn a_repeated_uninteresting_mark_keeps_the_demotion_deadline() {
    let peer = TestPrep::peer("1.2.3.5:5");
    let conn_id = ConnectionId::initial();
    let mut prep = test_prep(&["1.2.3.5:5"]);
    prep.state.target_upstream_peers = 1;
    far_deadlines(&mut prep.state);
    prep.established = Some((peer, conn_id));
    prep.uninteresting = Some((peer, conn_id, false));

    let (mut running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let deadline = ps_state(&running).demoted_until.get(&peer).copied();
    assert_eq!(deadline, Some(sim_t0() + UNINTERESTING_RETRY));

    let performance = running.resources().get::<ResourcePerformance>().expect("performance").clone();
    performance.record_uninteresting(
        peer,
        conn_id,
        true,
        ObservedAt::new(Duration::from_secs(SIM_INITIAL_CLOCK_SECS), start_in_era().relative_time),
    );
    drive_until(&mut running, sim_t0() + Duration::from_secs(1));

    let state = ps_state(&running);
    assert_eq!(wanted(&state, peer), LocalUse::Maintenance);
    assert_eq!(state.demoted_until.get(&peer).copied(), deadline);
    assert_eq!(set_local_uses(&running), vec![(peer, LocalUse::Maintenance)]);
}

#[test]
fn an_uninteresting_mark_after_rollback_demotes_for_180s() {
    let peer = TestPrep::peer("1.2.3.6:6");
    let conn_id = ConnectionId::initial();
    let mut prep = test_prep(&["1.2.3.6:6"]);
    prep.state.target_upstream_peers = 1;
    far_deadlines(&mut prep.state);
    prep.established = Some((peer, conn_id));
    prep.uninteresting = Some((peer, conn_id, true));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let state = ps_state(&running);
    assert_eq!(wanted(&state, peer), LocalUse::Maintenance);
    assert_eq!(state.demoted_until.get(&peer).copied(), Some(sim_t0() + UNINTERESTING_RETRY_AFTER_ROLLBACK));
}

#[test]
fn an_uninteresting_mark_for_a_gone_peer_does_nothing() {
    let peer = TestPrep::peer("5.5.5.5:5");
    let mut prep = test_prep(&[]);
    prep.state.target_upstream_peers = 1;
    far_deadlines(&mut prep.state);
    prep.uninteresting = Some((peer, ConnectionId::initial(), false));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    let state = ps_state(&running);
    assert!(state.seen_generation > 0);
    assert!(!state.demoted_until.contains_key(&peer));
    assert!(!state.outbound_peers.contains_key(&peer));
    assert!(set_local_uses(&running).is_empty());
}

#[test]
fn a_ledger_candidate_write_dials_on_the_next_round() {
    let peer = TestPrep::peer("8.8.8.8:8");
    let mut prep = test_prep(&[]);
    prep.state.target_upstream_peers = 1;
    prep.peer_mix = "ledger~1".parse().expect("ledger-only mix");
    far_deadlines(&mut prep.state);
    prep.ledger_write = Some(BTreeSet::from([PeerCandidate::from(peer)]));

    let (running, _guards, _logs) = setup(&prep, PeerSelectionMsg::Tick);
    assert_eq!(manager_sends(&running), vec![ManagerMessage::AddPeer(peer)]);
}
