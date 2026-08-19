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
    net::SocketAddr,
    num::NonZeroUsize,
};

use amaru_kernel::NonEmptyBytes;
use amaru_ouroboros::ConnectionId;
use amaru_protocols::network_effects::{
    AcceptEffect, AcceptError, ConnectEffect, ConnectError, ReceiveError, RecvEffect, SendEffect, SendError,
};
use amaru_pure_stage::{
    Name,
    simulation::{Blocked, Effect, SimulationRunning},
};

use super::{NetworkEvent, WorldConnectionProvider};

/// World loop over N SimulationRunning graphs + WorldConnectionProvider heap.
///
/// NO oneshot. Completes Network UntilResolved via provide_external_result.
/// ASYNC method awaited by #[tokio::test].
pub struct WorldLoop {
    provider: WorldConnectionProvider,
    graphs: Vec<SimulationRunning>,
    /// Pending connect operations (FIFO queue since conn_id unknown at track time).
    pending_connects: VecDeque<(usize, Name)>,
    /// Other operations tracked by key.
    pending_ops: BTreeMap<OperationKey, (usize, Name)>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum OperationKey {
    Accept(SocketAddr),
    Send(ConnectionId),
    Recv(ConnectionId, NonZeroUsize), // Include bytes_needed for Recv completion
}

impl WorldLoop {
    pub fn new(provider: WorldConnectionProvider, graphs: Vec<SimulationRunning>) -> Self {
        Self { provider, graphs, pending_connects: VecDeque::new(), pending_ops: BTreeMap::new() }
    }

    /// Run until no more events at-or-before horizon.
    ///
    /// ASYNC, awaited by test. NO block_on, NO Runtime::new.
    /// Completes Network UntilResolved with provide_external_result (NO oneshot).
    pub async fn run_until_horizon(&mut self, horizon_nanos: u64) {
        loop {
            // Exhaust all newly-ready graphs
            loop {
                let mut any_ready = false;
                for (graph_idx, graph) in self.graphs.iter_mut().enumerate() {
                    graph.receive_inputs();
                    while graph.has_runnable() {
                        match graph.try_effect() {
                            Ok(effect) => {
                                // Track External effects BEFORE handle_effect
                                self.track_external_effect(graph_idx, &effect);
                                graph.handle_effect(effect);
                                any_ready = true;
                            }
                            Err(Blocked::Busy { .. }) => break,
                            Err(_) => break,
                        }
                    }
                }
                if !any_ready {
                    break;
                }
            }

            // Pop one event if at≤horizon
            if let Some(entry) = self.provider.pop_event_at_or_before(horizon_nanos) {
                self.provider.set_time(entry.time_nanos);

                // Determine completion info from event
                let completion = match &entry.event {
                    NetworkEvent::Connected { initiator_conn } => {
                        // Match against pending_connects queue (FIFO)
                        if let Some((graph_idx, stage_name)) = self.pending_connects.pop_front() {
                            Some((
                                graph_idx,
                                stage_name,
                                Box::new(Ok::<ConnectionId, ConnectError>(*initiator_conn))
                                    as Box<dyn amaru_pure_stage::SendData>,
                            ))
                        } else {
                            None
                        }
                    }
                    NetworkEvent::Accepted { listener, responder_conn, initiator_addr } => {
                        if let Some((graph_idx, stage_name)) = self.pending_ops.remove(&OperationKey::Accept(*listener))
                        {
                            let peer = amaru_kernel::Peer::from_addr(initiator_addr);
                            Some((
                                graph_idx,
                                stage_name,
                                Box::new(Ok::<_, AcceptError>((peer, *responder_conn)))
                                    as Box<dyn amaru_pure_stage::SendData>,
                            ))
                        } else {
                            None
                        }
                    }
                    NetworkEvent::SendAck { conn } => {
                        if let Some((graph_idx, stage_name)) = self.pending_ops.remove(&OperationKey::Send(*conn)) {
                            Some((
                                graph_idx,
                                stage_name,
                                Box::new(Ok::<(), SendError>(())) as Box<dyn amaru_pure_stage::SendData>,
                            ))
                        } else {
                            None
                        }
                    }
                    NetworkEvent::Deliver { conn, data } => {
                        // Add data to inbox
                        self.provider.deliver_to_inbox(*conn, data.clone());

                        // Try to complete pending Recv
                        let recv_key = self
                            .pending_ops
                            .keys()
                            .find(|k| matches!(k, OperationKey::Recv(c, _) if c == conn))
                            .cloned();

                        if let Some(OperationKey::Recv(_, bytes_needed)) = recv_key {
                            if let Some((graph_idx, stage_name)) =
                                self.pending_ops.remove(&OperationKey::Recv(*conn, bytes_needed))
                            {
                                if let Some(result) = self.provider.try_complete_recv(*conn, bytes_needed) {
                                    Some((
                                        graph_idx,
                                        stage_name,
                                        Box::new(result) as Box<dyn amaru_pure_stage::SendData>,
                                    ))
                                } else {
                                    // Not enough data yet, re-insert
                                    self.pending_ops
                                        .insert(OperationKey::Recv(*conn, bytes_needed), (graph_idx, stage_name));
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    NetworkEvent::Close { conn } => {
                        self.provider.close_endpoint(*conn);

                        // Resume parked Send or Recv on this conn
                        if let Some((graph_idx, stage_name)) = self.pending_ops.remove(&OperationKey::Send(*conn)) {
                            Some((
                                graph_idx,
                                stage_name,
                                Box::new(Err::<(), SendError>(SendError::IoError(std::io::Error::other(
                                    "connection closed",
                                )))) as Box<dyn amaru_pure_stage::SendData>,
                            ))
                        } else {
                            // Try Recv
                            let recv_key = self
                                .pending_ops
                                .keys()
                                .find(|k| matches!(k, OperationKey::Recv(c, _) if c == conn))
                                .cloned();
                            if let Some(key @ OperationKey::Recv(_, _)) = recv_key {
                                if let Some((graph_idx, stage_name)) = self.pending_ops.remove(&key) {
                                    Some((
                                        graph_idx,
                                        stage_name,
                                        Box::new(Err::<NonEmptyBytes, ReceiveError>(ReceiveError::IoError(
                                            std::io::Error::other("connection closed"),
                                        )))
                                            as Box<dyn amaru_pure_stage::SendData>,
                                    ))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }
                    }
                };

                // Provide result if we found a waiting stage
                if let Some((graph_idx, stage_name, result)) = completion {
                    let graph = &mut self.graphs[graph_idx];
                    if let Err(e) = graph.resume_external_box(&stage_name, result) {
                        eprintln!("Failed to resume stage {}: {}", stage_name, e);
                    }
                    // await_external_effect ONLY on THIS graph (the one that was Busy)
                    graph.await_external_effect().await;
                }
            } else {
                break;
            }
        }
    }

    /// Track which stage is issuing which external effect.
    fn track_external_effect(&mut self, graph_idx: usize, effect: &Effect) {
        use std::any::Any;

        if let Effect::External { at_stage, effect: eff } = effect {
            let eff_any = &**eff as &dyn Any;

            if let Some(_connect) = eff_any.downcast_ref::<ConnectEffect>() {
                // Queue pending connect (conn_id unknown until provider assigns it)
                self.pending_connects.push_back((graph_idx, at_stage.clone()));
            } else if let Some(accept) = eff_any.downcast_ref::<AcceptEffect>() {
                self.pending_ops.insert(OperationKey::Accept(accept.listener_addr), (graph_idx, at_stage.clone()));
            } else if let Some(send) = eff_any.downcast_ref::<SendEffect>() {
                self.pending_ops.insert(OperationKey::Send(send.conn), (graph_idx, at_stage.clone()));
            } else if let Some(recv) = eff_any.downcast_ref::<RecvEffect>() {
                self.pending_ops.insert(OperationKey::Recv(recv.conn, recv.bytes), (graph_idx, at_stage.clone()));
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
        self.provider.peek_next_event_time().map_or(false, |t| t <= horizon_nanos)
    }

    /// Peek next event time on heap.
    pub fn peek_next_event_time(&self) -> Option<u64> {
        self.provider.peek_next_event_time()
    }
}
