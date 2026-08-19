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
    collections::{BTreeMap, VecDeque},
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
    AcceptEffect, AcceptError, ConnectEffect, ConnectError, ListenEffect, ReceiveError, RecvEffect, SendEffect,
    SendError,
};
use amaru_pure_stage::{
    Effect, Instant, Name, SendData,
    simulation::{Blocked, SimulationRunning},
};

use super::{HeapLogEntry, NetworkEvent, WorldConnectionProvider};

/// World loop over N SimulationRunning graphs + WorldConnectionProvider heap.
///
/// Completes Network UntilResolved effects only via `resume_external_box` /
/// `provide_external_result`. Provider futures are kicked once (never `.await`ed)
/// so `connect`/`send`/`accept` can schedule heap events without hanging.
pub struct WorldLoop {
    provider: Arc<WorldConnectionProvider>,
    graphs: Vec<SimulationRunning>,
    /// Pending connects keyed by destination listener, not a process-wide FIFO.
    pending_connects: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    pending_accepts: BTreeMap<SocketAddr, VecDeque<(usize, Name)>>,
    pending_sends: BTreeMap<ConnectionId, VecDeque<(usize, Name)>>,
    pending_recvs: BTreeMap<ConnectionId, VecDeque<(usize, Name, NonZeroUsize)>>,
}

type Completion = (usize, Name, Box<dyn SendData>);

enum Posted {
    Listen { addr: SocketAddr },
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
        Self {
            provider,
            graphs,
            pending_connects: BTreeMap::new(),
            pending_accepts: BTreeMap::new(),
            pending_sends: BTreeMap::new(),
            pending_recvs: BTreeMap::new(),
        }
    }

    /// Run until no more heap events or graph wakeups at-or-before horizon.
    pub async fn run_until_horizon(&mut self, horizon_nanos: u64) {
        loop {
            let heap_time = self.provider.peek_next_event_time();
            let wakeup_time = self.next_graph_wakeup_nanos();
            let next = match (heap_time, wakeup_time) {
                (Some(h), Some(w)) => Some(h.min(w)),
                (Some(h), None) => Some(h),
                (None, Some(w)) => Some(w),
                (None, None) => None,
            };
            let Some(next) = next else {
                if self.fail_orphaned_connects() {
                    continue;
                }
                break;
            };
            if next > horizon_nanos {
                break;
            }

            self.advance_clocks(next);
            self.exhaust_ready_graphs();

            if self.provider.peek_next_event_time() == Some(next)
                && let Some(entry) = self.provider.pop_event_at_or_before(next)
            {
                for completion in self.completions_for_event(&entry.event) {
                    self.resume(completion);
                }
            }
        }
    }

    fn next_graph_wakeup_nanos(&mut self) -> Option<u64> {
        let now = self.provider.current_time_nanos();
        let mut sleep: Option<u64> = None;
        for graph in &mut self.graphs {
            graph.receive_inputs();
            if graph.has_runnable() {
                return Some(now);
            }
            if let Some(t) = graph.next_wakeup() {
                let nanos = u64::try_from(t.sim_elapsed().as_nanos()).expect("sim time fits u64");
                sleep = Some(sleep.map_or(nanos, |s| s.min(nanos)));
            }
        }
        sleep
    }

    fn advance_clocks(&mut self, time_nanos: u64) {
        let already = self.provider.current_time_nanos();
        self.provider.set_time(time_nanos);
        let instant = Instant::at_offset(Duration::from_nanos(time_nanos), Duration::ZERO);
        for graph in &mut self.graphs {
            let due = graph
                .next_wakeup()
                .is_some_and(|t| u64::try_from(t.sim_elapsed().as_nanos()).expect("sim time fits u64") <= time_nanos);
            if time_nanos > already || due {
                graph.skip_to_next_wakeup(Some(instant));
            }
        }
    }

    fn exhaust_ready_graphs(&mut self) {
        loop {
            let mut progressed = false;
            for graph_idx in 0..self.graphs.len() {
                loop {
                    match self.graphs[graph_idx].run_until_sleeping_or_blocked() {
                        Blocked::Breakpoint(_, effect) => {
                            self.on_external(graph_idx, effect);
                            progressed = true;
                        }
                        Blocked::Deadlock(deadlock) => {
                            panic!("graph {graph_idx} deadlock: {deadlock:?}");
                        }
                        Blocked::Idle | Blocked::Sleeping { .. } | Blocked::Busy { .. } | Blocked::Terminated(_) => {
                            break;
                        }
                    }
                }
            }
            if !progressed {
                break;
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
            Posted::Listen { addr } => {
                if self.provider.has_listener(addr) {
                    let n = self.pending_connects.get(&addr).map(|q| q.len()).unwrap_or(0);
                    for _ in 0..n {
                        self.provider.pair_connect(addr);
                    }
                }
            }
            Posted::Connect { stage, addr } => {
                let addrs = addr.clone().to_socket_addrs().unwrap_or_default();
                if let Some(listener) =
                    addrs.iter().copied().find(|a| self.provider.has_listener(*a)).or_else(|| addrs.first().copied())
                {
                    self.pending_connects.entry(listener).or_default().push_back((graph_idx, stage));
                } else {
                    self.resume((
                        graph_idx,
                        stage,
                        Box::new(Err::<ConnectionId, ConnectError>(ConnectError::new(addr, "no listener")))
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
            NetworkEvent::Connected { initiator_conn, listener } => {
                let mut out = Vec::new();
                if let Some((graph_idx, stage_name)) = self.take_pending_connect(*listener) {
                    out.push((
                        graph_idx,
                        stage_name,
                        Box::new(Ok::<ConnectionId, ConnectError>(*initiator_conn)) as Box<dyn SendData>,
                    ));
                }
                if self.pending_accepts.get(listener).is_some_and(|q| !q.is_empty())
                    && let Some((responder_conn, initiator_addr)) = self.provider.take_handshake(*listener)
                {
                    self.provider.schedule_wire(NetworkEvent::Accepted {
                        listener: *listener,
                        responder_conn,
                        initiator_addr,
                    });
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
    pub async fn run_to_completion(&mut self) {
        self.run_until_horizon(u64::MAX).await;
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

    /// Get the event log.
    pub fn heap_log(&self) -> Vec<HeapLogEntry> {
        self.provider.heap_log()
    }

    /// Take the event log, leaving it empty.
    pub fn take_heap_log(&self) -> Vec<HeapLogEntry> {
        self.provider.take_heap_log()
    }

    /// Check if any events remain on heap before horizon.
    pub fn has_events_before(&self, horizon_nanos: u64) -> bool {
        self.provider.peek_next_event_time().is_some_and(|t| t <= horizon_nanos)
    }

    /// Peek next event time on heap.
    pub fn peek_next_event_time(&self) -> Option<u64> {
        self.provider.peek_next_event_time()
    }

    fn fail_orphaned_connects(&mut self) -> bool {
        let addrs: Vec<SocketAddr> =
            self.pending_connects.keys().copied().filter(|addr| !self.provider.has_listener(*addr)).collect();
        let mut any = false;
        for addr in addrs {
            if let Some(queue) = self.pending_connects.remove(&addr) {
                for (graph_idx, stage) in queue {
                    any = true;
                    self.resume((
                        graph_idx,
                        stage,
                        Box::new(Err::<ConnectionId, ConnectError>(ConnectError::new(addr.into(), "no listener")))
                            as Box<dyn SendData>,
                    ));
                }
            }
        }
        any
    }
}

fn classify_network(effect: &Effect) -> Option<Posted> {
    use std::any::Any;

    let Effect::External { at_stage, effect: eff } = effect else {
        return None;
    };
    let eff_any = &**eff as &dyn Any;
    if let Some(listen) = eff_any.downcast_ref::<ListenEffect>() {
        Some(Posted::Listen { addr: listen.addr })
    } else if let Some(connect) = eff_any.downcast_ref::<ConnectEffect>() {
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
