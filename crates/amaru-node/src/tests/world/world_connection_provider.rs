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
use tokio::sync::oneshot;
use tokio_util::bytes::{Bytes, BytesMut};

/// Discrete-event network simulator for deterministic testing.
///
/// This provider implements the EDR-011 heap-based event scheduler for network effects.
/// Unlike InMemoryConnectionProvider (instant VecDeque + same-call wakers), WorldConnectionProvider:
///
/// - Owns completion of UntilResolved futures (connect, accept, send, recv) as heap events
/// - Enforces sequential ordering: SendAck → Deliver, Connected → Accepted
/// - Never wakes a peer synchronously
/// - Replays all network events from the heap log
/// - Even δ=0 Deliver events go on the heap (send is not instant)
///
/// The world runner pops events at-or-before a horizon time, exhausting all newly-ready
/// stage graphs before advancing the clock.
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
    /// Connection accepted by listener: completes accept() future.
    Accepted { listener: SocketAddr, responder_conn: ConnectionId, initiator_addr: SocketAddr },
    /// Connection established: completes connect() future.
    Connected { initiator_conn: ConnectionId },
    /// Send acknowledged: sender may proceed.
    SendAck { conn: ConnectionId },
    /// Deliver message: wake receiver to consume from inbox.
    Deliver { conn: ConnectionId, data: Bytes },
    /// Connection closed: wake send and recv on this conn only (not peer).
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
    /// Event heap ordered by (time, sequence).
    heap: BTreeSet<HeapEntry>,
    /// Heap log for replay.
    heap_log: Vec<HeapLogEntry>,
    /// Monotonic sequence for deterministic FIFO ordering.
    next_sequence: u64,
    /// Current simulated time in nanoseconds.
    current_time_nanos: u64,
    /// Active listeners by address.
    listeners: BTreeMap<SocketAddr, Listener>,
    /// All connection endpoints by ConnectionId.
    endpoints: BTreeMap<ConnectionId, ConnectionEndpoint>,
    /// Next connection ID to assign.
    next_conn_id: ConnectionId,
    /// Pending connect operations waiting for Connected.
    pending_connects: BTreeMap<ConnectionId, oneshot::Sender<std::io::Result<ConnectionId>>>,
    /// Pending accept operations waiting for Accepted.
    pending_accepts: BTreeMap<SocketAddr, VecDeque<oneshot::Sender<std::io::Result<(Peer, ConnectionId)>>>>,
    /// Pending send operations waiting for SendAck (multiple per conn).
    pending_sends: BTreeMap<ConnectionId, VecDeque<oneshot::Sender<std::io::Result<()>>>>,
    /// Pending recv operations waiting for Deliver.
    pending_recvs: BTreeMap<ConnectionId, PendingRecv>,
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
    /// Inbox: data waiting to be consumed by recv.
    inbox: VecDeque<Bytes>,
    /// Read buffer for partial reads.
    read_buffer: BytesMut,
    /// Peer's ConnectionId for message routing.
    peer_conn_id: Arc<Mutex<Option<ConnectionId>>>,
}

struct PendingRecv {
    bytes_needed: NonZeroUsize,
    completion: oneshot::Sender<std::io::Result<NonEmptyBytes>>,
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
                pending_connects: BTreeMap::new(),
                pending_accepts: BTreeMap::new(),
                pending_sends: BTreeMap::new(),
                pending_recvs: BTreeMap::new(),
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

        // Log the event for replay
        let (kind, conn) = match &entry.event {
            NetworkEvent::Accepted { responder_conn, .. } => ("Accepted", Some(*responder_conn)),
            NetworkEvent::Connected { initiator_conn } => ("Connected", Some(*initiator_conn)),
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

    /// Execute one popped event: resolve its completion future.
    pub fn execute_event(&self, entry: HeapEntry) {
        let mut inner = self.inner.lock();
        match entry.event {
            NetworkEvent::Connected { initiator_conn } => {
                if let Some(tx) = inner.pending_connects.remove(&initiator_conn) {
                    let _ = tx.send(Ok(initiator_conn));
                }
            }
            NetworkEvent::Accepted { listener, responder_conn, initiator_addr } => {
                if let Some(queue) = inner.pending_accepts.get_mut(&listener) {
                    if let Some(tx) = queue.pop_front() {
                        let _ = tx.send(Ok((Peer::from_addr(&initiator_addr), responder_conn)));
                    }
                }
            }
            NetworkEvent::SendAck { conn } => {
                if let Some(queue) = inner.pending_sends.get_mut(&conn) {
                    if let Some(tx) = queue.pop_front() {
                        let _ = tx.send(Ok(()));
                    }
                    if queue.is_empty() {
                        inner.pending_sends.remove(&conn);
                    }
                }
            }
            NetworkEvent::Deliver { conn, data } => {
                if let Some(endpoint) = inner.endpoints.get_mut(&conn) {
                    endpoint.inbox.push_back(data);
                }
                if let Some(pending) = inner.pending_recvs.remove(&conn) {
                    if let Some(endpoint) = inner.endpoints.get_mut(&conn) {
                        Self::try_complete_recv_internal(&mut inner.pending_recvs, conn, endpoint, pending);
                    }
                }
            }
            NetworkEvent::Close { conn } => {
                inner.endpoints.remove(&conn);
                // Unpark sends on this conn only
                if let Some(mut queue) = inner.pending_sends.remove(&conn) {
                    while let Some(tx) = queue.pop_front() {
                        let _ = tx.send(Err(std::io::Error::other("connection closed")));
                    }
                }
                // Unpark recv on this conn only
                if let Some(pending) = inner.pending_recvs.remove(&conn) {
                    let _ = pending.completion.send(Err(std::io::Error::other("connection closed")));
                }
            }
        }
    }

    /// Schedule an event at current_time + delta_nanos.
    fn schedule_event(&self, delta_nanos: u64, event: NetworkEvent) {
        let mut inner = self.inner.lock();
        let time_nanos = inner.current_time_nanos + delta_nanos;
        let sequence = inner.next_sequence;
        inner.next_sequence += 1;
        inner.heap.insert(HeapEntry { time_nanos, sequence, event });
    }

    fn try_complete_recv_internal(
        pending_recvs: &mut BTreeMap<ConnectionId, PendingRecv>,
        conn: ConnectionId,
        endpoint: &mut ConnectionEndpoint,
        pending: PendingRecv,
    ) {
        while let Some(data) = endpoint.inbox.pop_front() {
            endpoint.read_buffer.extend_from_slice(&data);
        }
        if endpoint.read_buffer.len() >= pending.bytes_needed.get() {
            let bytes = endpoint.read_buffer.split_to(pending.bytes_needed.get()).freeze();
            if let Ok(non_empty) = NonEmptyBytes::try_from(bytes) {
                let _ = pending.completion.send(Ok(non_empty));
            } else {
                let _ = pending.completion.send(Err(std::io::Error::other("empty bytes")));
            }
        } else {
            // Not enough bytes: re-insert the pending recv
            pending_recvs.insert(conn, pending);
        }
    }
}

impl ConnectionProvider for WorldConnectionProvider {
    fn listen(&self, addr: SocketAddr) -> BoxFuture<'static, std::io::Result<SocketAddr>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let mut w = inner.lock();
            w.listeners.insert(addr, Listener { pending_handshakes: VecDeque::new() });
            Ok(addr)
        })
    }

    fn accept(&self, listener_addr: SocketAddr) -> BoxFuture<'static, std::io::Result<(Peer, ConnectionId)>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let (tx, rx) = oneshot::channel();
            {
                let mut w = inner.lock();
                w.pending_accepts.entry(listener_addr).or_default().push_back(tx);

                // Check if there's a pending handshake to complete immediately
                if let Some(listener) = w.listeners.get_mut(&listener_addr) {
                    if let Some(handshake) = listener.pending_handshakes.pop_front() {
                        // Schedule Accepted event (δ=0, UntilResolved)
                        let event = NetworkEvent::Accepted {
                            listener: listener_addr,
                            responder_conn: handshake.responder_conn,
                            initiator_addr: handshake.initiator_addr,
                        };
                        let time_nanos = w.current_time_nanos;
                        let sequence = w.next_sequence;
                        w.next_sequence += 1;
                        w.heap.insert(HeapEntry { time_nanos, sequence, event });

                        // Register responder endpoint
                        w.endpoints.insert(handshake.responder_conn, handshake.responder_endpoint);

                        // Link initiator to responder
                        *handshake.initiator_peer_conn_id_slot.lock() = Some(handshake.responder_conn);
                    }
                }
            }
            // Park: wait for Accepted event
            rx.await.map_err(|_| std::io::Error::other("accept cancelled"))?
        })
    }

    fn connect(&self, addrs: Vec<SocketAddr>, _timeout: Duration) -> BoxFuture<'static, std::io::Result<ConnectionId>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let (tx, rx) = oneshot::channel();
            let initiator_conn = {
                let mut w = inner.lock();
                let target_addr = addrs
                    .into_iter()
                    .find(|a| w.listeners.contains_key(a))
                    .ok_or_else(|| std::io::Error::other("no listener found"))?;

                let initiator_conn = w.next_conn_id.get_and_increment();
                let responder_conn = w.next_conn_id.get_and_increment();

                let initiator_peer_conn_id_slot = Arc::new(Mutex::new(None));
                let responder_peer_conn_id_slot = Arc::new(Mutex::new(Some(initiator_conn)));

                let initiator_endpoint = ConnectionEndpoint {
                    inbox: VecDeque::new(),
                    read_buffer: BytesMut::with_capacity(65536),
                    peer_conn_id: initiator_peer_conn_id_slot.clone(),
                };

                let responder_endpoint = ConnectionEndpoint {
                    inbox: VecDeque::new(),
                    read_buffer: BytesMut::with_capacity(65536),
                    peer_conn_id: responder_peer_conn_id_slot,
                };

                // Register initiator endpoint immediately
                w.endpoints.insert(initiator_conn, initiator_endpoint);

                // Queue handshake for accept
                let listener = w.listeners.get_mut(&target_addr).unwrap();
                listener.pending_handshakes.push_back(PendingHandshake {
                    responder_endpoint,
                    responder_conn,
                    initiator_addr: SocketAddr::from(([127, 0, 0, 1], 5000 + initiator_conn.as_u64() as u16)),
                    initiator_peer_conn_id_slot,
                });

                // Register pending connect
                w.pending_connects.insert(initiator_conn, tx);

                // Schedule Connected event (δ=0, UntilResolved)
                let time_nanos = w.current_time_nanos;
                let sequence = w.next_sequence;
                w.next_sequence += 1;
                w.heap.insert(HeapEntry { time_nanos, sequence, event: NetworkEvent::Connected { initiator_conn } });

                initiator_conn
            };
            // Park: wait for Connected event
            rx.await.map_err(|_| std::io::Error::other("connect cancelled"))?
        })
    }

    fn connect_addrs(
        &self,
        addr: ToSocketAddrs,
        timeout: Duration,
    ) -> BoxFuture<'static, std::io::Result<ConnectionId>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let addrs = addr.to_socket_addrs().map_err(std::io::Error::other)?;
            let provider = WorldConnectionProvider { inner };
            provider.connect(addrs, timeout).await
        })
    }

    fn send(&self, conn: ConnectionId, data: NonEmptyBytes) -> BoxFuture<'static, std::io::Result<()>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let (rx, peer_conn_id) = {
                let mut w = inner.lock();
                let endpoint = w
                    .endpoints
                    .get(&conn)
                    .ok_or_else(|| std::io::Error::other(format!("connection {conn} not found")))?;
                let peer_conn_id = *endpoint.peer_conn_id.lock();
                let (tx, rx) = oneshot::channel();
                w.pending_sends.entry(conn).or_default().push_back(tx);
                (rx, peer_conn_id)
            };

            // Schedule SendAck immediately (δ=0), Deliver after that
            let provider = WorldConnectionProvider { inner: inner.clone() };
            provider.schedule_event(0, NetworkEvent::SendAck { conn });
            if let Some(peer_id) = peer_conn_id {
                provider
                    .schedule_event(0, NetworkEvent::Deliver { conn: peer_id, data: Bytes::copy_from_slice(&data) });
            }

            rx.await.map_err(|_| std::io::Error::other("send cancelled"))?
        })
    }

    fn recv(&self, conn: ConnectionId, bytes: NonZeroUsize) -> BoxFuture<'static, std::io::Result<NonEmptyBytes>> {
        let inner = self.inner.clone();
        Box::pin(async move {
            let rx = {
                let mut w = inner.lock();
                let endpoint = w
                    .endpoints
                    .get_mut(&conn)
                    .ok_or_else(|| std::io::Error::other(format!("connection {conn} not found")))?;

                // Try to complete immediately if enough data in inbox
                while let Some(data) = endpoint.inbox.pop_front() {
                    endpoint.read_buffer.extend_from_slice(&data);
                }

                if endpoint.read_buffer.len() >= bytes.get() {
                    let result = endpoint.read_buffer.split_to(bytes.get()).freeze();
                    return result.try_into().map_err(|_| std::io::Error::other("empty bytes"));
                }

                // Not enough data: park pending recv
                let (tx, rx) = oneshot::channel();
                w.pending_recvs.insert(conn, PendingRecv { bytes_needed: bytes, completion: tx });
                rx
            };

            rx.await.map_err(|_| std::io::Error::other("recv cancelled"))?
        })
    }

    fn close(&self, conn: ConnectionId) -> BoxFuture<'static, std::io::Result<()>> {
        let provider = self.clone();
        Box::pin(async move {
            // Schedule Close event (δ=0) and return immediately
            provider.schedule_event(0, NetworkEvent::Close { conn });
            Ok(())
        })
    }
}
