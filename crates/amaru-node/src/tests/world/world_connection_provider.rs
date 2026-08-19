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
    collections::{BTreeMap, BTreeSet, VecDeque},
    net::SocketAddr,
    num::NonZeroUsize,
    sync::Arc,
    time::Duration,
};

use amaru_kernel::{NonEmptyBytes, Peer};
use amaru_ouroboros::{ConnectionId, ConnectionProvider, ToSocketAddrs};
use amaru_pure_stage::BoxFuture;
use parking_lot::Mutex;
use tokio_util::bytes::{Bytes, BytesMut};

/// Discrete-event network simulator for deterministic testing.
///
/// Provider methods schedule heap events synchronously and return a Future that
/// [`super::WorldLoop`] completes via `resume_external_box` / `provide_external_result`.
/// There is no oneshot table and the provider never wakes a peer.
#[derive(Clone)]
pub struct WorldConnectionProvider {
    inner: Arc<Mutex<WorldInner>>,
}

impl Default for WorldConnectionProvider {
    fn default() -> Self {
        Self::new()
    }
}

/// Event types scheduled on the heap.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NetworkEvent {
    /// Completes a parked `accept()` via the world loop.
    Accepted { listener: SocketAddr, responder_conn: ConnectionId, initiator_addr: SocketAddr },
    /// Completes a parked `connect()` via the world loop.
    Connected { initiator_conn: ConnectionId, listener: SocketAddr },
    /// Completes a parked `send()` via the world loop.
    SendAck { conn: ConnectionId },
    /// Delivers bytes to `conn`'s inbox and may complete a parked `recv()`.
    Deliver { conn: ConnectionId, data: Bytes },
    /// Closes `conn` and resumes parked `send`/`recv` on that connection only.
    Close { conn: ConnectionId },
}

/// Heap entry: (time_nanos, sequence, event)
/// Ordered by (time, sequence) for deterministic FIFO at same time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HeapEntry {
    pub time_nanos: u64,
    pub sequence: u64,
    pub event: NetworkEvent,
}

/// Heap log entry for replay: (seq, at, kind, conn).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeapLogEntry {
    pub sequence: u64,
    pub time_nanos: u64,
    pub kind: &'static str,
    pub conn: Option<ConnectionId>,
}

struct WorldInner {
    heap: BTreeSet<HeapEntry>,
    heap_log: Vec<HeapLogEntry>,
    next_sequence: u64,
    current_time_nanos: u64,
    listeners: BTreeMap<SocketAddr, Listener>,
    endpoints: BTreeMap<ConnectionId, ConnectionEndpoint>,
    next_conn_id: ConnectionId,
    /// Connects that arrived before any matching listener existed.
    pending_outbounds: Vec<Vec<SocketAddr>>,
}

struct Listener {
    pending_handshakes: VecDeque<PendingHandshake>,
}

struct PendingHandshake {
    responder_endpoint: ConnectionEndpoint,
    responder_conn: ConnectionId,
    initiator_addr: SocketAddr,
    initiator_peer_conn_id_slot: Arc<Mutex<Option<ConnectionId>>>,
}

struct ConnectionEndpoint {
    inbox: VecDeque<Bytes>,
    read_buffer: BytesMut,
    peer_conn_id: Arc<Mutex<Option<ConnectionId>>>,
}

impl WorldConnectionProvider {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(WorldInner {
                heap: BTreeSet::new(),
                heap_log: Vec::new(),
                next_sequence: 0,
                current_time_nanos: 0,
                listeners: BTreeMap::new(),
                endpoints: BTreeMap::new(),
                next_conn_id: ConnectionId::initial(),
                pending_outbounds: Vec::new(),
            })),
        }
    }

    /// Advance simulated time to the given instant (in nanoseconds).
    pub fn set_time(&self, time_nanos: u64) {
        let mut inner = self.inner.lock();
        assert!(time_nanos >= inner.current_time_nanos, "time cannot go backward");
        inner.current_time_nanos = time_nanos;
    }

    /// Get current simulated time in nanoseconds.
    pub fn current_time_nanos(&self) -> u64 {
        self.inner.lock().current_time_nanos
    }

    /// Pop one event at-or-before the horizon. Returns the full HeapEntry (preserving time/seq).
    pub fn pop_event_at_or_before(&self, horizon_nanos: u64) -> Option<HeapEntry> {
        let mut inner = self.inner.lock();
        let first = inner.heap.iter().next()?;
        if first.time_nanos > horizon_nanos {
            return None;
        }
        let entry = inner.heap.pop_first()?;

        let (kind, conn) = match &entry.event {
            NetworkEvent::Accepted { responder_conn, .. } => ("Accepted", Some(*responder_conn)),
            NetworkEvent::Connected { initiator_conn, .. } => ("Connected", Some(*initiator_conn)),
            NetworkEvent::SendAck { conn } => ("SendAck", Some(*conn)),
            NetworkEvent::Deliver { conn, .. } => ("Deliver", Some(*conn)),
            NetworkEvent::Close { conn } => ("Close", Some(*conn)),
        };
        inner.heap_log.push(HeapLogEntry { sequence: entry.sequence, time_nanos: entry.time_nanos, kind, conn });

        Some(entry)
    }

    /// Get the heap log for replay.
    pub fn heap_log(&self) -> Vec<HeapLogEntry> {
        self.inner.lock().heap_log.clone()
    }

    /// Peek at the next event time without popping.
    pub fn peek_next_event_time(&self) -> Option<u64> {
        self.inner.lock().heap.iter().next().map(|e| e.time_nanos)
    }

    /// Manually schedule an event at a specific time (for testing).
    pub fn schedule_event_at(&self, time_nanos: u64, event: NetworkEvent) {
        let mut inner = self.inner.lock();
        schedule_event_locked(&mut inner, time_nanos, event);
    }

    /// Schedule an event at current_time + delta_nanos.
    pub fn schedule_event(&self, delta_nanos: u64, event: NetworkEvent) {
        let mut inner = self.inner.lock();
        let time_nanos = inner.current_time_nanos + delta_nanos;
        schedule_event_locked(&mut inner, time_nanos, event);
    }

    /// Add data to an endpoint inbox (Deliver).
    pub fn deliver_to_inbox(&self, conn: ConnectionId, data: Bytes) {
        let mut inner = self.inner.lock();
        if let Some(endpoint) = inner.endpoints.get_mut(&conn) {
            endpoint.inbox.push_back(data);
        }
    }

    /// Try to complete recv from buffered inbox data.
    ///
    /// Returns `Some` when enough bytes are available. Otherwise leaves unread bytes in the
    /// buffer so a later Deliver can finish the same recv.
    pub fn try_complete_recv(
        &self,
        conn: ConnectionId,
        bytes_needed: NonZeroUsize,
    ) -> Option<std::io::Result<NonEmptyBytes>> {
        let mut inner = self.inner.lock();
        try_complete_recv_locked(&mut inner, conn, bytes_needed)
    }

    /// Install a queued handshake as the responder endpoint and return its ids.
    ///
    /// Used by the world loop after `Connected` so `Accepted` can be heap-scheduled
    /// when accept was already posted.
    pub fn take_handshake(&self, listener: SocketAddr) -> Option<(ConnectionId, SocketAddr)> {
        let mut inner = self.inner.lock();
        install_handshake_locked(&mut inner, listener)
    }

    /// Remove a closed endpoint.
    pub fn close_endpoint(&self, conn: ConnectionId) {
        let mut inner = self.inner.lock();
        inner.endpoints.remove(&conn);
    }
}

fn schedule_event_locked(inner: &mut WorldInner, time_nanos: u64, event: NetworkEvent) {
    let sequence = inner.next_sequence;
    inner.next_sequence += 1;
    inner.heap.insert(HeapEntry { time_nanos, sequence, event });
}

fn try_complete_recv_locked(
    inner: &mut WorldInner,
    conn: ConnectionId,
    bytes_needed: NonZeroUsize,
) -> Option<std::io::Result<NonEmptyBytes>> {
    let endpoint = inner.endpoints.get_mut(&conn)?;

    while let Some(data) = endpoint.inbox.pop_front() {
        endpoint.read_buffer.extend_from_slice(&data);
    }

    if endpoint.read_buffer.len() >= bytes_needed.get() {
        let bytes = endpoint.read_buffer.split_to(bytes_needed.get()).freeze();
        Some(NonEmptyBytes::try_from(bytes).map_err(|_| std::io::Error::other("empty bytes")))
    } else {
        None
    }
}

fn install_handshake_locked(inner: &mut WorldInner, listener: SocketAddr) -> Option<(ConnectionId, SocketAddr)> {
    let handshake = inner.listeners.get_mut(&listener)?.pending_handshakes.pop_front()?;
    let responder_conn = handshake.responder_conn;
    let initiator_addr = handshake.initiator_addr;
    inner.endpoints.insert(responder_conn, handshake.responder_endpoint);
    *handshake.initiator_peer_conn_id_slot.lock() = Some(responder_conn);
    Some((responder_conn, initiator_addr))
}

/// Pair an outbound connect with an existing listener and schedule `Connected`.
fn pair_connect_locked(inner: &mut WorldInner, target_addr: SocketAddr) -> ConnectionId {
    let initiator_conn = inner.next_conn_id.get_and_increment();
    let responder_conn = inner.next_conn_id.get_and_increment();
    let initiator_peer_conn_id_slot = Arc::new(Mutex::new(None));
    let responder_peer_conn_id_slot = Arc::new(Mutex::new(Some(initiator_conn)));

    inner.endpoints.insert(
        initiator_conn,
        ConnectionEndpoint {
            inbox: VecDeque::new(),
            read_buffer: BytesMut::with_capacity(65536),
            peer_conn_id: initiator_peer_conn_id_slot.clone(),
        },
    );

    let Some(listener) = inner.listeners.get_mut(&target_addr) else {
        return initiator_conn;
    };
    listener.pending_handshakes.push_back(PendingHandshake {
        responder_endpoint: ConnectionEndpoint {
            inbox: VecDeque::new(),
            read_buffer: BytesMut::with_capacity(65536),
            peer_conn_id: responder_peer_conn_id_slot,
        },
        responder_conn,
        initiator_addr: SocketAddr::from(([127, 0, 0, 1], 5000 + initiator_conn.as_u64() as u16)),
        initiator_peer_conn_id_slot,
    });

    let time_nanos = inner.current_time_nanos;
    schedule_event_locked(inner, time_nanos, NetworkEvent::Connected { initiator_conn, listener: target_addr });
    initiator_conn
}

impl ConnectionProvider for WorldConnectionProvider {
    fn listen(&self, addr: SocketAddr) -> BoxFuture<'static, std::io::Result<SocketAddr>> {
        let mut inner = self.inner.lock();
        inner.listeners.entry(addr).or_insert_with(|| Listener { pending_handshakes: VecDeque::new() });

        let waiting = std::mem::take(&mut inner.pending_outbounds);
        let (matched, still_waiting): (Vec<_>, Vec<_>) = waiting.into_iter().partition(|addrs| addrs.contains(&addr));
        inner.pending_outbounds = still_waiting;
        for _ in matched {
            pair_connect_locked(&mut inner, addr);
        }
        drop(inner);
        Box::pin(async move { Ok(addr) })
    }

    fn accept(&self, listener_addr: SocketAddr) -> BoxFuture<'static, std::io::Result<(Peer, ConnectionId)>> {
        let mut inner = self.inner.lock();
        if let Some((responder_conn, initiator_addr)) = install_handshake_locked(&mut inner, listener_addr) {
            let time_nanos = inner.current_time_nanos;
            schedule_event_locked(
                &mut inner,
                time_nanos,
                NetworkEvent::Accepted { listener: listener_addr, responder_conn, initiator_addr },
            );
        }
        drop(inner);
        Box::pin(std::future::pending())
    }

    fn connect(&self, addrs: Vec<SocketAddr>, _timeout: Duration) -> BoxFuture<'static, std::io::Result<ConnectionId>> {
        let mut inner = self.inner.lock();
        if let Some(target_addr) = addrs.iter().copied().find(|a| inner.listeners.contains_key(a)) {
            pair_connect_locked(&mut inner, target_addr);
        } else {
            inner.pending_outbounds.push(addrs);
        }
        drop(inner);
        Box::pin(std::future::pending())
    }

    fn connect_addrs(
        &self,
        addr: ToSocketAddrs,
        timeout: Duration,
    ) -> BoxFuture<'static, std::io::Result<ConnectionId>> {
        match addr.to_socket_addrs() {
            Ok(addrs) => self.connect(addrs, timeout),
            Err(e) => {
                let msg = e.to_string();
                Box::pin(async move { Err(std::io::Error::other(msg)) })
            }
        }
    }

    fn send(&self, conn: ConnectionId, data: NonEmptyBytes) -> BoxFuture<'static, std::io::Result<()>> {
        let inner_guard = self.inner.lock();
        let peer_conn_id = inner_guard.endpoints.get(&conn).map(|endpoint| *endpoint.peer_conn_id.lock());
        drop(inner_guard);

        self.schedule_event(0, NetworkEvent::SendAck { conn });
        if let Some(Some(peer_id)) = peer_conn_id {
            self.schedule_event(0, NetworkEvent::Deliver { conn: peer_id, data: Bytes::copy_from_slice(&data) });
        }
        Box::pin(std::future::pending())
    }

    fn recv(&self, conn: ConnectionId, bytes: NonZeroUsize) -> BoxFuture<'static, std::io::Result<NonEmptyBytes>> {
        if let Some(result) = self.try_complete_recv(conn, bytes) {
            return Box::pin(async move { result });
        }
        Box::pin(std::future::pending())
    }

    fn close(&self, conn: ConnectionId) -> BoxFuture<'static, std::io::Result<()>> {
        self.schedule_event(0, NetworkEvent::Close { conn });
        Box::pin(async move { Ok(()) })
    }
}
