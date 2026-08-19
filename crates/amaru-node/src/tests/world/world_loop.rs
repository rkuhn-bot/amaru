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
    collections::{BTreeMap, VecDeque},
    future::Future,
    net::SocketAddr,
    num::NonZeroUsize,
    task::{Context, Waker},
};

use amaru_kernel::Peer;
use amaru_ouroboros::ConnectionId;
use amaru_protocols::network_effects::{
    AcceptEffect, AcceptError, ConnectEffect, ConnectError, ReceiveError, RecvEffect, SendEffect, SendError,
};
use amaru_pure_stage::{Effect, Name, SendData, simulation::SimulationRunning};

use super::{NetworkEvent, WorldConnectionProvider};

/// World loop over N SimulationRunning graphs + WorldConnectionProvider heap.
///
/// Completes Network UntilResolved effects only via `resume_external_box` /
/// `provide_external_result`. Provider futures are kicked once (never `.await`ed)
/// so `connect`/`send`/`accept` can schedule heap events without hanging.
pub struct WorldLoop {
    provider: WorldConnectionProvider,
    graphs: Vec<SimulationRunning>,
    /// Pending connect operations (FIFO; conn id is assigned inside the provider).
    pending_connects: VecDeque<(usize, Name)>,
    pending_accepts: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    pending_sends: BTreeMap<ConnectionId, VecDeque<(usize, Name)>>,
    pending_recvs: BTreeMap<ConnectionId, VecDeque<(usize, Name, NonZeroUsize)>>,
}

type Completion = (usize, Name, Box<dyn SendData>);

impl WorldLoop {
    pub fn new(provider: WorldConnectionProvider, graphs: Vec<SimulationRunning>) -> Self {
        Self {
            provider,
            graphs,
            pending_connects: VecDeque::new(),
            pending_accepts: BTreeMap::new(),
            pending_sends: BTreeMap::new(),
            pending_recvs: BTreeMap::new(),
        }
    }

    /// Run until no more events at-or-before horizon.
    ///
    /// Exhaust newly-ready graphs, else pop-if-at≤horizon, resume the waiting graph, repeat.
    pub async fn run_until_horizon(&mut self, horizon_nanos: u64) {
        loop {
            self.exhaust_ready_graphs();

            let Some(entry) = self.provider.pop_event_at_or_before(horizon_nanos) else {
                break;
            };
            self.provider.set_time(entry.time_nanos);

            let completions = self.completions_for_event(&entry.event);
            for (graph_idx, stage_name, result) in completions {
                let graph = &mut self.graphs[graph_idx];
                if let Err(e) = graph.resume_external_box(&stage_name, result) {
                    eprintln!("Failed to resume stage {stage_name}: {e}");
                }
                kick_external(graph);
            }
        }
    }

    fn exhaust_ready_graphs(&mut self) {
        loop {
            let mut any_ready = false;
            for graph_idx in 0..self.graphs.len() {
                loop {
                    let effect = {
                        let graph = &mut self.graphs[graph_idx];
                        graph.receive_inputs();
                        if !graph.has_runnable() {
                            break;
                        }
                        match graph.try_effect() {
                            Ok(effect) => effect,
                            Err(_) => break,
                        }
                    };
                    self.track_external_effect(graph_idx, &effect);
                    let graph = &mut self.graphs[graph_idx];
                    graph.handle_effect(effect);
                    kick_external(graph);
                    any_ready = true;
                }
            }
            if !any_ready {
                break;
            }
        }
    }

    fn completions_for_event(&mut self, event: &NetworkEvent) -> Vec<Completion> {
        match event {
            NetworkEvent::Connected { initiator_conn, listener } => {
                let mut out = Vec::new();
                if let Some((graph_idx, stage_name)) = self.pending_connects.pop_front() {
                    out.push((
                        graph_idx,
                        stage_name,
                        Box::new(Ok::<ConnectionId, ConnectError>(*initiator_conn)) as Box<dyn SendData>,
                    ));
                }
                if self.pending_accepts.get(listener).is_some_and(|q| !q.is_empty())
                    && let Some((responder_conn, initiator_addr)) = self.provider.take_handshake(*listener)
                {
                    self.provider.schedule_event(
                        0,
                        NetworkEvent::Accepted { listener: *listener, responder_conn, initiator_addr },
                    );
                }
                out
            }
            NetworkEvent::Accepted { listener, responder_conn, initiator_addr } => {
                if let Some((graph_idx, stage_name)) =
                    self.pending_accepts.get_mut(listener).and_then(|q| q.pop_front())
                {
                    if self.pending_accepts.get(listener).is_some_and(|q| q.is_empty()) {
                        self.pending_accepts.remove(listener);
                    }
                    let peer = Peer::from_addr(initiator_addr);
                    vec![(
                        graph_idx,
                        stage_name,
                        Box::new(Ok::<_, AcceptError>((peer, *responder_conn))) as Box<dyn SendData>,
                    )]
                } else {
                    Vec::new()
                }
            }
            NetworkEvent::SendAck { conn } => {
                if let Some((graph_idx, stage_name)) = self.pending_sends.get_mut(conn).and_then(|q| q.pop_front()) {
                    if self.pending_sends.get(conn).is_some_and(|q| q.is_empty()) {
                        self.pending_sends.remove(conn);
                    }
                    vec![(graph_idx, stage_name, Box::new(Ok::<(), SendError>(())) as Box<dyn SendData>)]
                } else {
                    Vec::new()
                }
            }
            NetworkEvent::Deliver { conn, data } => {
                self.provider.deliver_to_inbox(*conn, data.clone());
                if let Some((graph_idx, stage_name, bytes_needed)) =
                    self.pending_recvs.get_mut(conn).and_then(|q| q.pop_front())
                {
                    if let Some(result) = self.provider.try_complete_recv(*conn, bytes_needed) {
                        if self.pending_recvs.get(conn).is_some_and(|q| q.is_empty()) {
                            self.pending_recvs.remove(conn);
                        }
                        vec![(
                            graph_idx,
                            stage_name,
                            Box::new(result.map_err(|e| ReceiveError::new(*conn, e))) as Box<dyn SendData>,
                        )]
                    } else {
                        self.pending_recvs.entry(*conn).or_default().push_front((graph_idx, stage_name, bytes_needed));
                        Vec::new()
                    }
                } else {
                    Vec::new()
                }
            }
            NetworkEvent::Close { conn } => {
                self.provider.close_endpoint(*conn);
                let mut out = Vec::new();
                if let Some(queue) = self.pending_sends.remove(conn) {
                    for (graph_idx, stage_name) in queue {
                        out.push((
                            graph_idx,
                            stage_name,
                            Box::new(Err::<(), SendError>(SendError::new(*conn, "connection closed")))
                                as Box<dyn SendData>,
                        ));
                    }
                }
                if let Some(queue) = self.pending_recvs.remove(conn) {
                    for (graph_idx, stage_name, _) in queue {
                        out.push((
                            graph_idx,
                            stage_name,
                            Box::new(Err::<amaru_kernel::NonEmptyBytes, ReceiveError>(ReceiveError::new(
                                *conn,
                                "connection closed",
                            ))) as Box<dyn SendData>,
                        ));
                    }
                }
                out
            }
        }
    }

    fn track_external_effect(&mut self, graph_idx: usize, effect: &Effect) {
        use std::any::Any;

        if let Effect::External { at_stage, effect: eff } = effect {
            let eff_any = &**eff as &dyn Any;

            if eff_any.downcast_ref::<ConnectEffect>().is_some() {
                self.pending_connects.push_back((graph_idx, at_stage.clone()));
            } else if let Some(accept) = eff_any.downcast_ref::<AcceptEffect>() {
                self.pending_accepts.entry(accept.listener_addr).or_default().push_back((graph_idx, at_stage.clone()));
            } else if let Some(send) = eff_any.downcast_ref::<SendEffect>() {
                self.pending_sends.entry(send.conn).or_default().push_back((graph_idx, at_stage.clone()));
            } else if let Some(recv) = eff_any.downcast_ref::<RecvEffect>() {
                self.pending_recvs.entry(recv.conn).or_default().push_back((graph_idx, at_stage.clone(), recv.bytes));
            }
        }
    }

    /// Run until no more events and all graphs idle/terminated.
    pub async fn run_to_completion(&mut self) {
        self.run_until_horizon(u64::MAX).await
    }

    /// Get the event log.
    pub fn heap_log(&self) -> Vec<super::HeapLogEntry> {
        self.provider.heap_log()
    }

    /// Check if any events remain on heap before horizon.
    pub fn has_events_before(&self, horizon_nanos: u64) -> bool {
        self.provider.peek_next_event_time().is_some_and(|t| t <= horizon_nanos)
    }

    /// Peek next event time on heap.
    pub fn peek_next_event_time(&self) -> Option<u64> {
        self.provider.peek_next_event_time()
    }
}

/// Poll `await_external_effect` once so provider methods run and Ready
/// futures (Listen, Close, Recv-hits-inbox) complete. Never waits.
fn kick_external(graph: &mut SimulationRunning) {
    let mut fut = std::pin::pin!(graph.await_external_effect());
    let _ = Future::poll(fut.as_mut(), &mut Context::from_waker(Waker::noop()));
}
