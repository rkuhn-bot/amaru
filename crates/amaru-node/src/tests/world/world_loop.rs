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

#![expect(clippy::panic, clippy::expect_used)]

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    future::Future,
    net::SocketAddr,
    num::NonZeroUsize,
    sync::Arc,
    task::{Context, Waker},
    time::Duration,
};

use amaru_kernel::Peer;
use amaru_ouroboros::{ConnectionId, ToSocketAddrs};
use amaru_protocols::network_effects::{
    AcceptEffect, AcceptError, ConnectEffect, ConnectError, ReceiveError, RecvEffect, SendEffect, SendError,
};
use amaru_pure_stage::{
    Effect, Instant, Name, SendData,
    simulation::{Blocked, SimulationRunning},
};

use super::{GraphWakeReason, HeapLogEntry, NetworkEvent, WorldConnectionProvider, WorldHeapItem};

/// World loop: pops the one physical `(time, sequence)` heap.
///
/// The heap lives on [`WorldConnectionProvider`]. Network hops enqueue there;
/// graph wakes call [`WorldConnectionProvider::schedule_item`] onto the same
/// structure. Shared [`WorldConnectionProvider::alloc_sequence`] keeps one
/// global `(time, sequence)` order. [`SimulationRunning`] bodies live in
/// `graphs` by index so a heap entry can name them (`WorldHeapItem::Graph`).
/// That Vec is not a scheduler — a graph runs only when its wake is popped.
/// Completes Network UntilResolved effects only via `resume_external_box`.
pub struct WorldLoop {
    provider: Arc<WorldConnectionProvider>,
    graphs: Vec<SimulationRunning>,
    heap_log: Vec<HeapLogEntry>,
    /// Sequences of graph wakes superseded by an earlier reschedule.
    cancelled: BTreeSet<u64>,
    /// Current heap token `(time, sequence)` per graph, if scheduled.
    graph_on_heap: Vec<Option<(u64, u64)>>,
    /// Pending connects keyed by destination listener, not a process-wide FIFO.
    pending_connects: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    pending_accepts: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    /// Accepts already paired on `ConnectAttempt` and waiting for the matching `Accepted` hop.
    claimed_accepts: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    pending_sends: BTreeMap<ConnectionId, VecDeque<(usize, Name)>>,
    pending_recvs: BTreeMap<ConnectionId, VecDeque<(usize, Name, NonZeroUsize)>>,
}

type Completion = (usize, Name, Box<dyn SendData>);

enum Posted {
    Connect { stage: Name, addr: ToSocketAddrs },
    Accept { stage: Name, listener: SocketAddr },
    Send { stage: Name, conn: ConnectionId },
    Recv { stage: Name, conn: ConnectionId, bytes: NonZeroUsize },
}

impl WorldLoop {
    pub fn new(provider: Arc<WorldConnectionProvider>, mut graphs: Vec<SimulationRunning>) -> Self {
        for graph in &mut graphs {
            graph.breakpoint("world_external", |effect| matches!(effect, Effect::External { .. }));
        }
        let graph_on_heap = vec![None; graphs.len()];
        let mut world = Self {
            provider,
            graphs,
            heap_log: Vec::new(),
            cancelled: BTreeSet::new(),
            graph_on_heap,
            pending_connects: BTreeMap::new(),
            pending_accepts: BTreeMap::new(),
            claimed_accepts: BTreeMap::new(),
            pending_sends: BTreeMap::new(),
            pending_recvs: BTreeMap::new(),
        };
        for index in 0..world.graphs.len() {
            world.schedule_graph_if_needed(index);
        }
        world
    }

    pub fn graph(&self, index: usize) -> &SimulationRunning {
        &self.graphs[index]
    }

    /// Borrow the node graphs owned by this world.
    pub fn graphs(&self) -> &[SimulationRunning] {
        &self.graphs
    }

    /// Run until no more heap events or graph wakes at-or-before horizon.
    ///
    /// Synchronous: the loop never waits on wall-clock time. Production graphs may
    /// `Handle::block_on` `DurationDist::Zero` effects, which cannot run inside an
    /// existing Tokio context.
    pub fn run_until_horizon(&mut self, horizon_nanos: u64) {
        while let Some(entry) = self.provider.pop_at_or_before(horizon_nanos) {
            if self.cancelled.remove(&entry.sequence) {
                continue;
            }

            self.provider.set_time(entry.time_nanos);
            self.heap_log.push(HeapLogEntry::from(&entry));

            match entry.item {
                WorldHeapItem::Network(event) => {
                    let completions = self.completions_for_event(&event);
                    for completion in completions {
                        let graph_idx = completion.0;
                        self.resume(completion);
                        self.schedule_graph_if_needed(graph_idx);
                    }
                }
                WorldHeapItem::Graph { index, reason: _ } => {
                    self.graph_on_heap[index] = None;
                    self.wake_and_run_graph(index);
                    self.schedule_graph_if_needed(index);
                }
            }
        }
    }

    fn schedule_graph_if_needed(&mut self, index: usize) {
        let graph = &mut self.graphs[index];
        graph.receive_inputs();
        let now = self.provider.current_time_nanos();
        let (time_nanos, reason) = if graph.has_runnable() {
            (now, GraphWakeReason::Runnable)
        } else if let Some(wakeup) = graph.next_wakeup() {
            (instant_nanos(wakeup), GraphWakeReason::Sleeping)
        } else {
            return;
        };
        self.schedule_graph(index, time_nanos, reason);
    }

    fn schedule_graph(&mut self, index: usize, time_nanos: u64, reason: GraphWakeReason) {
        if let Some((old_time, old_seq)) = self.graph_on_heap[index] {
            if old_time <= time_nanos {
                return;
            }
            self.cancelled.insert(old_seq);
        }
        let sequence = self.provider.schedule_item(time_nanos, WorldHeapItem::Graph { index, reason });
        self.graph_on_heap[index] = Some((time_nanos, sequence));
    }

    fn wake_and_run_graph(&mut self, index: usize) {
        let time_nanos = self.provider.current_time_nanos();
        let instant = Instant::at_offset(Duration::from_nanos(time_nanos), Duration::ZERO);
        let graph = &mut self.graphs[index];
        let clock_behind = instant_nanos(graph.now()) < time_nanos;
        let wakeup_due = graph.next_wakeup().is_some_and(|t| instant_nanos(t) <= time_nanos);
        if clock_behind || wakeup_due {
            graph.skip_to_next_wakeup(Some(instant));
        }
        self.run_graph_until_clock(index);
    }

    /// Run until the graph wants to advance the clock. External effects fall out via the breakpoint.
    fn run_graph_until_clock(&mut self, index: usize) {
        loop {
            match self.graphs[index].run_until_sleeping_or_blocked() {
                Blocked::Breakpoint(_, effect) => {
                    self.on_external(index, effect);
                }
                Blocked::Deadlock(deadlock) => {
                    panic!("graph {index} deadlock: {deadlock:?}");
                }
                Blocked::Idle | Blocked::Sleeping { .. } | Blocked::Busy { .. } | Blocked::Terminated(_) => {
                    break;
                }
            }
        }
    }

    fn on_external(&mut self, graph_idx: usize, effect: Effect) {
        let posted = classify_network(&effect);
        self.graphs[graph_idx].handle_effect(effect);
        kick_external(&mut self.graphs[graph_idx]);
        if let Some(posted) = posted {
            self.track_or_complete(graph_idx, posted);
        }
    }

    fn track_or_complete(&mut self, graph_idx: usize, posted: Posted) {
        match posted {
            Posted::Connect { stage, addr } => {
                let addrs = addr.clone().to_socket_addrs().unwrap_or_default();
                if let Some(target) = addrs.first().copied() {
                    self.pending_connects.entry(target).or_default().push_back((graph_idx, stage));
                } else {
                    self.resume((
                        graph_idx,
                        stage,
                        Box::new(Err::<ConnectionId, ConnectError>(ConnectError::new(addr, "connection refused")))
                            as Box<dyn SendData>,
                    ));
                }
            }
            Posted::Accept { stage, listener } => {
                self.pending_accepts.entry(listener).or_default().push_back((graph_idx, stage));
            }
            Posted::Send { stage, conn } => {
                if self.provider.can_send(conn) {
                    self.pending_sends.entry(conn).or_default().push_back((graph_idx, stage));
                } else {
                    self.resume((
                        graph_idx,
                        stage,
                        Box::new(Err::<(), SendError>(SendError::new(conn, "connection reset"))) as Box<dyn SendData>,
                    ));
                }
            }
            Posted::Recv { stage, conn, bytes } => {
                self.pending_recvs.entry(conn).or_default().push_back((graph_idx, stage, bytes));
                for completion in self.drain_recvs(conn) {
                    self.resume(completion);
                }
            }
        }
    }

    fn take_pending_connect(&mut self, listener: SocketAddr) -> Option<(usize, Name)> {
        let queue = self.pending_connects.get_mut(&listener)?;
        let item = queue.pop_front()?;
        if queue.is_empty() {
            self.pending_connects.remove(&listener);
        }
        Some(item)
    }

    fn drain_recvs(&mut self, conn: ConnectionId) -> Vec<Completion> {
        let mut out = Vec::new();
        while let Some((graph_idx, stage, bytes_needed)) =
            self.pending_recvs.get(&conn).and_then(|q| q.front().cloned())
        {
            match self.provider.try_complete_recv(conn, bytes_needed) {
                Some(result) => {
                    if let Some(queue) = self.pending_recvs.get_mut(&conn) {
                        queue.pop_front();
                    }
                    if self.pending_recvs.get(&conn).is_some_and(|q| q.is_empty()) {
                        self.pending_recvs.remove(&conn);
                    }
                    out.push((
                        graph_idx,
                        stage,
                        Box::new(result.map_err(|e| ReceiveError::new(conn, e))) as Box<dyn SendData>,
                    ));
                }
                None => break,
            }
        }
        out
    }

    fn completions_for_event(&mut self, event: &NetworkEvent) -> Vec<Completion> {
        match event {
            NetworkEvent::ConnectAttempt { target } => {
                let Some((graph_idx, stage_name)) = self.take_pending_connect(*target) else {
                    return Vec::new();
                };
                if let Some(initiator_conn) = self.provider.pair_if_listening(*target) {
                    // Pair at most one queued accept per ConnectAttempt. Extra inbound
                    // handshakes stay queued until a later accept() posts.
                    if let Some(waiting) = self.pending_accepts.get_mut(target).and_then(|q| q.pop_front()) {
                        if self.pending_accepts.get(target).is_some_and(|q| q.is_empty()) {
                            self.pending_accepts.remove(target);
                        }
                        if let Some((responder_conn, initiator_addr)) = self.provider.take_handshake(*target) {
                            self.claimed_accepts.entry(*target).or_default().push_back(waiting);
                            self.provider.schedule_wire(NetworkEvent::Accepted {
                                listener: *target,
                                responder_conn,
                                initiator_addr,
                            });
                        } else {
                            self.pending_accepts.entry(*target).or_default().push_front(waiting);
                        }
                    }
                    vec![(
                        graph_idx,
                        stage_name,
                        Box::new(Ok::<ConnectionId, ConnectError>(initiator_conn)) as Box<dyn SendData>,
                    )]
                } else {
                    vec![(
                        graph_idx,
                        stage_name,
                        Box::new(Err::<ConnectionId, ConnectError>(ConnectError::new(
                            (*target).into(),
                            "connection refused",
                        ))) as Box<dyn SendData>,
                    )]
                }
            }
            NetworkEvent::Accepted { listener, responder_conn, initiator_addr } => {
                let waiting = self
                    .claimed_accepts
                    .get_mut(listener)
                    .and_then(|q| q.pop_front())
                    .or_else(|| self.pending_accepts.get_mut(listener).and_then(|q| q.pop_front()));
                if self.claimed_accepts.get(listener).is_some_and(|q| q.is_empty()) {
                    self.claimed_accepts.remove(listener);
                }
                if self.pending_accepts.get(listener).is_some_and(|q| q.is_empty()) {
                    self.pending_accepts.remove(listener);
                }
                if let Some((graph_idx, stage_name)) = waiting {
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
                self.drain_recvs(*conn)
            }
            NetworkEvent::Close { conn } => {
                let peer = self.provider.close_endpoint(*conn);
                let out = fail_pending_on(&mut self.pending_sends, &mut self.pending_recvs, *conn);
                if let Some(peer) = peer {
                    self.provider.schedule_wire(NetworkEvent::Close { conn: peer });
                }
                out
            }
        }
    }

    fn resume(&mut self, (graph_idx, stage_name, result): Completion) {
        self.graphs[graph_idx]
            .resume_external_box(&stage_name, result)
            .unwrap_or_else(|e| panic!("failed to resume stage {stage_name}: {e}"));
        kick_external(&mut self.graphs[graph_idx]);
    }

    /// Run until no more events and all graphs idle/terminated.
    pub fn run_to_completion(&mut self) {
        self.run_until_horizon(u64::MAX);
        self.assert_graphs_settled();
    }

    pub fn assert_graphs_settled(&mut self) {
        for (graph_idx, graph) in self.graphs.iter_mut().enumerate() {
            match graph.run_until_sleeping_or_blocked() {
                Blocked::Idle | Blocked::Terminated(_) => {}
                other @ (Blocked::Sleeping { .. }
                | Blocked::Deadlock(_)
                | Blocked::Breakpoint(..)
                | Blocked::Busy { .. }) => {
                    panic!("graph {graph_idx} expected idle/terminated, got {other:?}")
                }
            }
        }
    }

    /// Get the event log (network events and graph wakes, in pop order).
    pub fn heap_log(&self) -> Vec<HeapLogEntry> {
        self.heap_log.clone()
    }

    /// Take the event log, leaving it empty.
    pub fn take_heap_log(&mut self) -> Vec<HeapLogEntry> {
        std::mem::take(&mut self.heap_log)
    }

    /// Check if any events remain on the unified heap before horizon.
    pub fn has_events_before(&self, horizon_nanos: u64) -> bool {
        self.peek_next_event_time().is_some_and(|t| t <= horizon_nanos)
    }

    /// Peek next event time on the one physical heap.
    pub fn peek_next_event_time(&self) -> Option<u64> {
        self.provider.peek_next_event_time()
    }

    /// Live heap contents (not pop order), excluding cancelled graph wakes.
    ///
    /// Sorted by `(time, sequence)` so tests can assert a graph wake and a
    /// `NetworkEvent` share one heap before the loop pops either.
    pub fn heap_contents(&self) -> Vec<HeapLogEntry> {
        let mut entries: Vec<_> = self
            .provider
            .heap_entries()
            .iter()
            .filter(|entry| !self.cancelled.contains(&entry.sequence))
            .map(HeapLogEntry::from)
            .collect();
        entries.sort_by_key(|e| (e.time_nanos, e.sequence));
        entries
    }
}

fn instant_nanos(instant: Instant) -> u64 {
    u64::try_from(instant.sim_elapsed().as_nanos()).expect("sim time fits u64")
}

fn classify_network(effect: &Effect) -> Option<Posted> {
    use std::any::Any;

    let Effect::External { at_stage, effect: eff } = effect else {
        return None;
    };
    let eff_any = &**eff as &dyn Any;
    if let Some(connect) = eff_any.downcast_ref::<ConnectEffect>() {
        Some(Posted::Connect { stage: at_stage.clone(), addr: connect.addr.clone() })
    } else if let Some(accept) = eff_any.downcast_ref::<AcceptEffect>() {
        Some(Posted::Accept { stage: at_stage.clone(), listener: accept.listener_addr })
    } else if let Some(send) = eff_any.downcast_ref::<SendEffect>() {
        Some(Posted::Send { stage: at_stage.clone(), conn: send.conn })
    } else {
        eff_any.downcast_ref::<RecvEffect>().map(|recv| Posted::Recv {
            stage: at_stage.clone(),
            conn: recv.conn,
            bytes: recv.bytes,
        })
    }
}

fn fail_pending_on(
    pending_sends: &mut BTreeMap<ConnectionId, VecDeque<(usize, Name)>>,
    pending_recvs: &mut BTreeMap<ConnectionId, VecDeque<(usize, Name, NonZeroUsize)>>,
    conn: ConnectionId,
) -> Vec<Completion> {
    let mut out = Vec::new();
    if let Some(queue) = pending_sends.remove(&conn) {
        for (graph_idx, stage_name) in queue {
            out.push((
                graph_idx,
                stage_name,
                Box::new(Err::<(), SendError>(SendError::new(conn, "connection closed"))) as Box<dyn SendData>,
            ));
        }
    }
    if let Some(queue) = pending_recvs.remove(&conn) {
        for (graph_idx, stage_name, _) in queue {
            out.push((
                graph_idx,
                stage_name,
                Box::new(Err::<amaru_kernel::NonEmptyBytes, ReceiveError>(ReceiveError::new(conn, "connection closed")))
                    as Box<dyn SendData>,
            ));
        }
    }
    out
}

/// Poll `await_external_effect` once so provider methods run and Ready
/// futures (Listen, Close) complete. Never waits.
fn kick_external(graph: &mut SimulationRunning) {
    let mut fut = std::pin::pin!(graph.await_external_effect());
    let _ = Future::poll(fut.as_mut(), &mut Context::from_waker(Waker::noop()));
}
