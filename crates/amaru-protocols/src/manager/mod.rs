// Copyright 2025 PRAGMA
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

use std::{collections::BTreeMap, net::SocketAddr, num::NonZeroU8, sync::Arc, time::Duration};

use amaru_kernel::{EraHistory, NetworkMagic, Peer, Point};
use amaru_observability::{Instrument, TraceContext, debug, debug_span, error, info};
use amaru_ouroboros::{ConnectionDirection, ConnectionId, MempoolMsg};
use amaru_pure_stage::{DeserializerGuards, Effects, Instant, StageRef, TrySend, register_data_deserializer};

use crate::{
    accept::{self, PullAccept},
    blockfetch::Blocks,
    chainsync::ChainSyncInitiatorMsg,
    connection::{self, ConnectionMessage, LocalUse},
    network_effects::{ConnectError, Network, NetworkOps},
    peer_sharing::{SharePeersReply, ShareResult},
    protocol::Role,
    protocol_messages::version_number::VersionNumber,
    tx_submission::ResponderParams,
};

pub mod connector;

/// Messages the [`Manager`] sends to the consensus `peer_selection` stage.
///
/// Notifications are sent *only after the handshake completes successfully*, so that
/// `full_duplex` status is known accurately.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum PeerSelectionNotify {
    /// A connection has been established and the handshake completed successfully.
    /// This is the only moment at which `peer_selection` learns about a usable connection.
    Connected {
        peer: Peer,
        conn_id: ConnectionId,
        direction: ConnectionDirection,
        full_duplex_capable: bool,
        full_duplex: bool,
        advertisable: bool,
    },

    /// A connection has been terminated (graceful disconnect, error, handshake refusal,
    /// or network error).
    ///
    /// The connection is gone. peer-selection owns redial via `Dial` message.
    Disconnected { peer: Peer, conn_id: ConnectionId, direction: ConnectionDirection },

    /// The outbound connection attempt failed (timeout, refusal, or another network error).
    ///
    /// The manager does not retry. Peer selection decides whether to [`ManagerMessage::AddPeer`] again.
    ConnectFailed { peer: Peer },

    /// Inbound peer-sharing request: select addresses to advertise and reply on `reply_to`.
    ShareRequest { peer: Peer, amount: u8, reply_to: StageRef<SharePeersReply> },
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ManagerMessage {
    /// Start one outbound connection attempt to the given peer.
    ///
    /// A failed attempt is reported as [`PeerSelectionNotify::ConnectFailed`] and is not retried.
    /// After a successful session dies, peer selection issues a new `AddPeer`; the manager does not redial.
    AddPeer(Peer),
    /// Remove a peer and terminate all of its connections.
    RemovePeer(Peer),
    /// Terminate the given connection only.
    Disconnect(Peer, ConnectionId),
    /// Start listening for incoming connections on the given socket address.
    Listen(SocketAddr),
    /// Fetch blocks on the given chain fragment.
    ///
    /// When `peers` is `Some`, only those peers' initiating connections are asked.
    /// When `None`, every initiating connection is asked (cold-start / empty-selection fallback).
    ///
    /// Each connection is offered the request without waiting. One that cannot take it is
    /// skipped. [`Blocks::NoPeersAvailable`] is sent when no initiating connection exists
    /// to attempt. [`Blocks::NoneAccepted`] is sent when at least one did and none admitted
    /// the request, so the fetch stage can ask other peers, or pause, without waiting out
    /// the timeout in silence. The connection reports [`Blocks::PeersAsked`] itself once its
    /// block-fetch handler has admitted the request.
    FetchBlocks { from: Point, through: Point, cr: StageRef<Blocks>, id: u64, peers: Option<Vec<Peer>> },
    /// Start periodic peer-sharing requests on one outbound connection.
    ///
    /// The initiator schedules the first request after `initial_delay`, then every `interval`
    /// after each reply. Results are delivered on `reply_to` until the connection ends.
    /// If no initiating connection exists, or that connection does not accept the request,
    /// an empty [`ShareResult`] is sent once.
    RequestSharePeers {
        peer: Peer,
        amount: u8,
        initial_delay: std::time::Duration,
        interval: std::time::Duration,
        reply_to: StageRef<ShareResult>,
    },
    /// Server-side peer-sharing: ask peer selection for addresses to return to `peer`.
    ShareRequest { peer: Peer, amount: u8, reply_to: StageRef<SharePeersReply> },
    /// Advertise this new tip to all downstream peers.
    NewTip(Point, TraceContext),
    /// INTERNAL message sent by the connector stage after a connection attempt completes.
    ConnectionResult(Peer, Result<ConnectionId, ConnectError>),
    /// INTERNAL message sent from the connection stage only!
    ///
    /// Must contain the connection ID so that we can then close the actual socket;
    /// the `peers` entry could already have been removed by RemovePeer.
    // TODO move to separate message type
    ConnectionDied(Peer, ConnectionId, Role),
    /// INTERNAL message sent by the accept stage after accepting a new connection.
    Accepted(Peer, ConnectionId),
    /// INTERNAL Sent by the connection stage after successful handshake.
    /// This allows the manager to notify peer_selection with accurate full_duplex status.
    HandshakeComplete {
        peer: Peer,
        stage: StageRef<ConnectionMessage>,
        conn_id: ConnectionId,
        role: Role,
        full_duplex_capable: bool,
        full_duplex: bool,
        advertisable: bool,
    },
    /// Ask a live connection to converge toward this local use.
    SetLocalUse { peer: Peer, conn_id: ConnectionId, local_use: LocalUse },
    /// Connection finished converging; used to update `may_initiate`.
    LocalUseApplied { peer: Peer, conn_id: ConnectionId, local_use: LocalUse },
}

impl ManagerMessage {
    fn message_type(&self) -> &'static str {
        match self {
            ManagerMessage::AddPeer(_) => "AddPeer",
            ManagerMessage::RemovePeer(_) => "RemovePeer",
            ManagerMessage::Disconnect(..) => "Disconnect",
            ManagerMessage::Listen(_) => "Listen",
            ManagerMessage::FetchBlocks { .. } => "FetchBlocks",
            ManagerMessage::RequestSharePeers { .. } => "RequestSharePeers",
            ManagerMessage::ShareRequest { .. } => "ShareRequest",
            ManagerMessage::NewTip(_, _) => "NewTip",
            ManagerMessage::ConnectionResult(..) => "ConnectionResult",
            ManagerMessage::ConnectionDied(..) => "ConnectionDied",
            ManagerMessage::Accepted(..) => "Accepted",
            ManagerMessage::HandshakeComplete { .. } => "HandshakeComplete",
            ManagerMessage::SetLocalUse { .. } => "SetLocalUse",
            ManagerMessage::LocalUseApplied { .. } => "LocalUseApplied",
        }
    }

    pub fn new_tip(tip: Point) -> Self {
        ManagerMessage::NewTip(tip, TraceContext::none())
    }
}

/// The manager stage is responsible for managing the connections to the peers.
///
/// It is important to keep in mind that inbound connections are controlled by the peer
/// and that the peer may bind the socket to a specific port before connecting. If this
/// manager listens on multiple IP addresses, then it is possible for the same peer to
/// open multiple inbound connections from the same remote SocketAddr, hence the same
/// [`Peer`]. These connections are distinguished by their [`ConnectionId`].
///
/// Outbound connections are controlled and to a given peer only one may be initiated at
/// a time. The [`Peer`] we connect to may also show up as inbound, therefore we need to
/// keep these separate.
///
/// ## Design
///
/// All connections are held in `Manager::connections` indexed by [`ConnectionId`].
/// For each peer we keep track of the outbound state (which is `None` in case no
/// outbound connection has been requested) and up to one inbound connection.
/// If a second connection comes in from the same peer, this new connection will be
/// terminated (the handshake will be run, sending [`crate::protocol_messages::handshake::RefuseReason::Refused`]).
///
/// An inbound connection is accepted (subject to connection limits and the above) and
/// after successful handshake the manager notifies `peer_selection` about the new connection.
/// When the connection dies, there are no retries and the manager immediately notifies
/// `peer_selection` about the disconnection.
///
/// An outbound connection is initiated by sending `ManagerMessage::AddPeer`. The manager makes
/// one attempt. If it fails, the manager notifies `peer_selection` with
/// [`PeerSelectionNotify::ConnectFailed`] and does not retry. After a successful connection and
/// handshake, the manager notifies `peer_selection` about the new connection. When the connection
/// dies, the manager notifies `peer_selection` and does **not** redial. Peer selection decides
/// whether to `AddPeer` again.
///
/// ## Behavioural contracts
///
/// - [`PeerSelectionNotify::Connected`] is always paired with a future [`PeerSelectionNotify::Disconnected`]
///   for the same `peer` and `conn_id`.
///
///   This also holds true if [`ManagerMessage::RemovePeer`] is processed between.
///
/// - Sending [`ManagerMessage::AddPeer`] will generate [`PeerSelectionNotify::ConnectFailed`]
///   if that attempt fails before [`ManagerMessage::RemovePeer`] is received.
#[derive(Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Manager {
    peers: BTreeMap<Peer, PeerState>,
    connections: BTreeMap<ConnectionId, Connection>,
    connector: StageRef<connector::ConnectorMsg>,
    magic: NetworkMagic,
    config: ManagerConfig,
    era_history: Arc<EraHistory>,
    chain_sync: StageRef<ChainSyncInitiatorMsg>,
    mempool: StageRef<MempoolMsg>,
    peer_selection: StageRef<PeerSelectionNotify>,
}

#[derive(Default, Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
enum OutboundState {
    #[default]
    None,
    /// `AddPeer` has been accepted and the attempt has not yet succeeded or failed.
    Scheduled,
    Connected {
        conn_id: ConnectionId,
    },
}

#[derive(Default, Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
struct PeerState {
    outbound: OutboundState,
    inbound: Option<ConnectionId>,
}

#[derive(Debug, PartialEq, serde::Serialize, serde::Deserialize)]
struct Connection {
    peer: Peer,
    stage: StageRef<ConnectionMessage>,
    direction: ConnectionDirection,
    /// Whether we may initiate mini-protocols on this connection.
    ///
    /// Outbound handshake already starts Diffusion initiators, so this is true from insert.
    /// Inbound stays false until [`ManagerMessage::LocalUseApplied`] reports [`LocalUse::Diffusion`].
    may_initiate: bool,
    full_duplex_capable: bool,
}

impl Manager {
    pub fn new(
        magic: NetworkMagic,
        config: ManagerConfig,
        era_history: Arc<EraHistory>,
        chain_sync: StageRef<ChainSyncInitiatorMsg>,
        mempool: StageRef<MempoolMsg>,
        peer_selection: StageRef<PeerSelectionNotify>,
    ) -> Self {
        Self {
            peers: BTreeMap::new(),
            connections: BTreeMap::new(),
            connector: StageRef::blackhole(),
            magic,
            config,
            era_history,
            chain_sync,
            mempool,
            peer_selection,
        }
    }

    pub fn config(&self) -> ManagerConfig {
        self.config
    }
}

/// Parameters for the Manager: connection timeout, reconnection delay, etc...
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ManagerConfig {
    /// How long one outbound TCP connect attempt may run before it fails.
    pub connection_timeout: Duration,
    pub reconnect_delay: Duration,
    pub accept_interval: Duration,
    pub tx_submission_params: ResponderParams,
    /// BlockFetch initiator pipeline depth. `1` drives the lock-step typestate
    /// instance; values greater than 1 wrap N instances in the CIP-0164 pipeliner.
    pub blockfetch_pipeline_n: NonZeroU8,
    /// Last-to-finish bound when stopping the diffusion initiator group.
    pub diffusion_stop_timeout: Duration,
    /// Last-to-finish bound when stopping the maintenance initiator group.
    pub maintenance_stop_timeout: Duration,
    /// Highest node-to-node protocol version offered in handshake.
    ///
    /// Defaults to [`VersionNumber::CURRENT`] (V15). Tests pin V14 to check fallback.
    pub max_n2n_version: VersionNumber,
}

impl ManagerConfig {
    pub fn with_reconnect_delay(mut self, reconnect_delay: Duration) -> Self {
        self.reconnect_delay = reconnect_delay;
        self
    }

    pub fn with_connection_timeout(mut self, connection_timeout: Duration) -> Self {
        self.connection_timeout = connection_timeout;
        self
    }

    pub fn with_accept_interval(mut self, accept_interval: Duration) -> Self {
        self.accept_interval = accept_interval;
        self
    }

    pub fn with_tx_submission_params(mut self, params: ResponderParams) -> Self {
        self.tx_submission_params = params;
        self
    }

    pub fn with_blockfetch_pipeline_n(mut self, n: NonZeroU8) -> Self {
        self.blockfetch_pipeline_n = n;
        self
    }

    pub fn with_max_n2n_version(mut self, version: VersionNumber) -> Self {
        self.max_n2n_version = version;
        self
    }
}

impl Default for ManagerConfig {
    fn default() -> Self {
        Self {
            connection_timeout: Duration::from_secs(2),
            reconnect_delay: Duration::from_secs(2),
            accept_interval: Duration::from_millis(100),
            tx_submission_params: ResponderParams::default(),
            blockfetch_pipeline_n: NonZeroU8::MIN,
            diffusion_stop_timeout: Duration::from_secs(300),
            maintenance_stop_timeout: Duration::from_secs(120),
            max_n2n_version: VersionNumber::CURRENT,
        }
    }
}

impl Manager {
    async fn add_peer(&mut self, peer: Peer, eff: &Effects<ManagerMessage>) {
        let already_dialing = matches!(
            self.peers.get(&peer).map(|state| &state.outbound),
            Some(OutboundState::Connected { .. } | OutboundState::Scheduled)
        );
        if already_dialing {
            info!(protocols::manager::peer::CONNECT_DISCARDED, peer, reason = "already_connected_or_scheduled");
            return;
        }
        info!(protocols::manager::peer::CONNECT, peer);
        self.peers.entry(peer).or_default().outbound = OutboundState::Scheduled;
        eff.ensure_child(&mut self.connector, "connector", connector::stage, || {
            connector::Connector::new(self.config.connection_timeout, eff.me())
        })
        .await;
        eff.send(&self.connector, connector::ConnectorMsg::Connect { peer }).await;
    }

    /// Report a failed attempt and forget the outbound dial. In-flight results for a peer that
    /// was removed, or that is already connected, are ignored.
    async fn abandon_attempt(&mut self, peer: Peer, eff: &Effects<ManagerMessage>) {
        let has_inbound = match self.peers.get(&peer) {
            Some(state) if matches!(state.outbound, OutboundState::Scheduled) => state.inbound.is_some(),
            _ => return,
        };
        if has_inbound {
            if let Some(state) = self.peers.get_mut(&peer) {
                state.outbound = OutboundState::None;
            }
        } else {
            self.peers.remove(&peer);
        }
        eff.send(&self.peer_selection, PeerSelectionNotify::ConnectFailed { peer }).await;
    }

    async fn connection_result(
        &mut self,
        peer: Peer,
        result: Result<ConnectionId, ConnectError>,
        eff: &Effects<ManagerMessage>,
    ) {
        match result {
            Ok(conn_id) => {
                info!(protocols::manager::peer::CONNECTED, peer, conn_id = conn_id.as_u64());
                self.start_connection_stage(eff, peer, conn_id, ConnectionDirection::Outbound).await;
            }
            Err(err) => {
                info!(protocols::manager::peer::CONNECT_FAILED, peer, error = err.to_string());
                self.abandon_attempt(peer, eff).await;
            }
        }
    }

    async fn listen(&mut self, listen_addr: SocketAddr, eff: &Effects<ManagerMessage>) {
        let network = Network::new(eff);
        match network.listen(listen_addr).await {
            Ok(listen_addr) => {
                info!(protocols::manager::listen::STARTED, listen_addr = listen_addr.to_string());
                let accept_stage = eff.stage("accept", accept::stage).await;
                let accept_stage = eff.supervise(accept_stage, ManagerMessage::Listen(listen_addr));
                let accept_stage =
                    eff.wire_up(accept_stage, accept::AcceptState::new(eff.me(), self.config(), listen_addr)).await;
                eff.send(&accept_stage, PullAccept).await;
            }
            Err(error) => {
                error!(
                    protocols::manager::listen::FAILED,
                    listen_addr = listen_addr.to_string(),
                    error = error.to_string()
                );
                return eff.terminate().await;
            }
        }
    }

    async fn accepted(&mut self, peer: Peer, conn_id: ConnectionId, eff: &Effects<ManagerMessage>) {
        // Always start a connection stage for every accepted inbound. Duplicate detection (to keep at
        // most one inbound per peer) is performed after handshake success; extras are terminated then.
        // This ensures the handshake is always run (as documented) for all accepted connections.
        self.start_connection_stage(eff, peer, conn_id, ConnectionDirection::Inbound).await;
    }

    /// Start a stage to handle the connection lifecycle.
    async fn start_connection_stage(
        &mut self,
        eff: &Effects<ManagerMessage>,
        peer: Peer,
        conn_id: ConnectionId,
        direction: ConnectionDirection,
    ) {
        let connection = eff.stage(format!("{conn_id}-{peer}"), connection::stage).await;
        let role = match direction {
            ConnectionDirection::Inbound => Role::Responder,
            ConnectionDirection::Outbound => Role::Initiator,
        };
        let connection = eff.supervise(connection, ManagerMessage::ConnectionDied(peer, conn_id, role));
        let connection = eff
            .wire_up(
                connection,
                connection::Connection::new(
                    peer,
                    conn_id,
                    role,
                    self.config,
                    self.magic,
                    self.chain_sync.clone(),
                    self.era_history.clone(),
                    self.mempool.clone(),
                    eff.me(), // manager itself to receive HandshakeComplete
                ),
            )
            .await;
        // The stage was just wired, so this is the first message. `try_send` keeps the manager
        // runnable if that mailbox cannot take it. Nothing is recorded in `connections` until
        // the handshake completes, and a dead stage is dropped by `ConnectionDied`.
        let _ = eff.try_send(&connection, ConnectionMessage::Initialize).await;
    }

    #[expect(clippy::too_many_arguments)]
    async fn handshake_complete(
        &mut self,
        peer: Peer,
        stage: StageRef<ConnectionMessage>,
        conn_id: ConnectionId,
        role: Role,
        full_duplex_capable: bool,
        full_duplex: bool,
        advertisable: bool,
        eff: &Effects<ManagerMessage>,
    ) {
        let direction = match role {
            Role::Initiator => ConnectionDirection::Outbound,
            Role::Responder => ConnectionDirection::Inbound,
        };
        info!(
            protocols::manager::peer::HANDSHAKE_COMPLETED,
            peer,
            conn_id = conn_id.as_u64(),
            full_duplex_capable,
            full_duplex,
            advertisable
        );
        let peer_state = self.peers.entry(peer).or_default();
        let accept_this = match direction {
            ConnectionDirection::Outbound => {
                if matches!(peer_state.outbound, OutboundState::Connected { .. }) {
                    false
                } else {
                    peer_state.outbound = OutboundState::Connected { conn_id };
                    true
                }
            }
            ConnectionDirection::Inbound => {
                if peer_state.inbound.is_some() {
                    false
                } else {
                    peer_state.inbound = Some(conn_id);
                    true
                }
            }
        };
        if accept_this {
            // Outbound handshake starts Diffusion initiators in the same connection turn,
            // so share/fetch must see `may_initiate` before `Connected` is processed.
            let may_initiate = direction == ConnectionDirection::Outbound;
            self.connections.insert(conn_id, Connection { stage, direction, full_duplex_capable, peer, may_initiate });
            eff.send(
                &self.peer_selection,
                PeerSelectionNotify::Connected {
                    peer,
                    conn_id,
                    direction,
                    full_duplex_capable,
                    full_duplex,
                    advertisable,
                },
            )
            .await;
        } else {
            // The duplicate was not inserted. `Full` leaves it running: the manager has no
            // entry that claims it was disconnected. `Gone` is already dead.
            match eff.try_send(&stage, ConnectionMessage::Disconnect).await {
                TrySend::Queued | TrySend::Gone => {
                    info!(protocols::manager::peer::DUPLICATE_TERMINATED, peer, conn_id = conn_id.as_u64());
                }
                TrySend::Full => {
                    debug!(
                        protocols::manager::peer::DISCONNECT_IGNORED,
                        peer,
                        reason = "not_admitted",
                        conn_id = conn_id.as_u64()
                    );
                }
            }
        }
    }

    async fn remove_peer(&mut self, peer: Peer, eff: &Effects<ManagerMessage>) {
        let Some(entry) = self.peers.get(&peer).cloned() else {
            info!(protocols::manager::peer::DISCONNECT_IGNORED, peer, reason = "not_connected");
            return;
        };
        // Drop a direction only once Disconnect is in that connection's mailbox, or the stage
        // is already gone. `Full` keeps the entry: the connection is still up and never heard it.
        let mut inbound = entry.inbound;
        let mut outbound = entry.outbound;
        if let Some(conn_id) = inbound {
            if self.disconnect_tracked(peer, conn_id, true, eff).await {
                inbound = None;
            } else {
                inbound = Some(conn_id);
            }
        }
        if let OutboundState::Connected { conn_id } = outbound {
            if self.disconnect_tracked(peer, conn_id, true, eff).await {
                outbound = OutboundState::None;
            } else {
                outbound = OutboundState::Connected { conn_id };
            }
        }
        let still_connected = inbound.is_some() || matches!(outbound, OutboundState::Connected { .. });
        if still_connected {
            if let Some(state) = self.peers.get_mut(&peer) {
                state.inbound = inbound;
                state.outbound = outbound;
            }
        } else {
            // No live connection remains. An in-flight dial (`Scheduled`) is forgotten too,
            // as it was when the peer entry was removed before the send.
            self.peers.remove(&peer);
        }
    }

    /// Offer `Disconnect` to a tracked connection.
    ///
    /// Returns whether the manager no longer tracks it. `forget_when_queued` is set for
    /// `RemovePeer`, which drops the entry once the message is admitted. A lone `Disconnect`
    /// leaves the entry until `ConnectionDied`, unless the stage is already `Gone`.
    async fn disconnect_tracked(
        &mut self,
        peer: Peer,
        conn_id: ConnectionId,
        forget_when_queued: bool,
        eff: &Effects<ManagerMessage>,
    ) -> bool {
        let Some(connection) = self.connections.get(&conn_id) else {
            return true;
        };
        let stage = connection.stage.clone();
        let direction = connection.direction;
        let direction_name = match direction {
            ConnectionDirection::Inbound => "inbound",
            ConnectionDirection::Outbound => "outbound",
        };
        info!(protocols::manager::peer::DISCONNECTING, peer, conn_id = conn_id.as_u64(), direction = direction_name);
        match eff.try_send(&stage, ConnectionMessage::Disconnect).await {
            TrySend::Full => false,
            TrySend::Gone => {
                self.forget_live_connection(peer, conn_id, direction, eff).await;
                true
            }
            TrySend::Queued if forget_when_queued => {
                self.forget_live_connection(peer, conn_id, direction, eff).await;
                true
            }
            TrySend::Queued => false,
        }
    }

    /// The connection is finished. Tell peer selection once and drop the manager entry.
    async fn forget_live_connection(
        &mut self,
        peer: Peer,
        conn_id: ConnectionId,
        direction: ConnectionDirection,
        eff: &Effects<ManagerMessage>,
    ) {
        if self.connections.remove(&conn_id).is_none() {
            return;
        }
        let drop_peer = if let Some(state) = self.peers.get_mut(&peer) {
            match direction {
                ConnectionDirection::Inbound => {
                    if state.inbound == Some(conn_id) {
                        state.inbound = None;
                    }
                }
                ConnectionDirection::Outbound => {
                    if state.outbound == (OutboundState::Connected { conn_id }) {
                        state.outbound = OutboundState::None;
                    }
                }
            }
            state.inbound.is_none() && matches!(state.outbound, OutboundState::None)
        } else {
            false
        };
        if drop_peer {
            self.peers.remove(&peer);
        }
        eff.send(&self.peer_selection, PeerSelectionNotify::Disconnected { peer, conn_id, direction }).await;
    }

    async fn connection_died(&mut self, peer: Peer, conn_id: ConnectionId, role: Role, eff: &Effects<ManagerMessage>) {
        // this is needed to clean up the socket in case the connection stage errored out
        close_connection(eff, &peer, conn_id).await;
        let Some(peer_state) = self.peers.get_mut(&peer) else {
            debug!(protocols::manager::peer::DISCONNECT_IGNORED, peer, reason = "peer_already_removed");
            return;
        };
        if let Some(Connection { direction, .. }) = self.connections.remove(&conn_id) {
            match direction {
                ConnectionDirection::Inbound => {
                    assert_eq!(peer_state.inbound, Some(conn_id));
                    assert_eq!(role, Role::Responder);
                    if peer_state.outbound == OutboundState::None {
                        info!(protocols::manager::peer::CONNECTION_DIED_HANDLED, peer, outcome = "peer_removed");
                        self.peers.remove(&peer);
                    } else {
                        info!(protocols::manager::peer::CONNECTION_DIED_HANDLED, peer, outcome = "kept_for_outbound");
                        peer_state.inbound = None;
                    }
                }
                ConnectionDirection::Outbound => {
                    assert_eq!(peer_state.outbound, OutboundState::Connected { conn_id });
                    assert_eq!(role, Role::Initiator);
                    if peer_state.inbound.is_none() {
                        info!(protocols::manager::peer::CONNECTION_DIED_HANDLED, peer, outcome = "peer_removed");
                        self.peers.remove(&peer);
                    } else {
                        info!(protocols::manager::peer::CONNECTION_DIED_HANDLED, peer, outcome = "kept_for_inbound");
                        peer_state.outbound = OutboundState::None;
                    }
                }
            }
            eff.send(&self.peer_selection, PeerSelectionNotify::Disconnected { peer, conn_id, direction }).await;
        } else {
            // No `connections` entry: either the handshake had not finished, or `RemovePeer` /
            // a `Gone` disconnect already notified peer selection. Only a still-scheduled dial
            // is a connect failure. A handshake that already completed must not be reported twice.
            debug!(
                protocols::manager::peer::DISCONNECT_IGNORED,
                peer,
                reason = "before_handshake",
                conn_id = conn_id.as_u64()
            );
            if role == Role::Initiator
                && matches!(self.peers.get(&peer).map(|state| &state.outbound), Some(OutboundState::Scheduled))
            {
                if let Some(state) = self.peers.get_mut(&peer) {
                    state.outbound = OutboundState::None;
                    if state.inbound.is_none() {
                        self.peers.remove(&peer);
                    }
                }
                eff.send(&self.peer_selection, PeerSelectionNotify::ConnectFailed { peer }).await;
            }
            // inbound pre-HS deaths require no further action (peer entry is only created on HS success)
        }
    }

    async fn fetch_blocks(
        &mut self,
        from: Point,
        through: Point,
        cr: StageRef<Blocks>,
        id: u64,
        peers: Option<Vec<Peer>>,
        eff: &Effects<ManagerMessage>,
    ) {
        debug!(protocols::manager::blocks::FETCH, from, through, peers = format!("{peers:?}"));
        let mut candidates = 0usize;
        let mut admitted = 0usize;
        let offer = async |stage: &StageRef<ConnectionMessage>| {
            let outcome =
                eff.try_send(stage, ConnectionMessage::FetchBlocks { from, through, cr: cr.clone(), id }).await;
            outcome == TrySend::Queued
        };
        match peers {
            None => {
                for conn in self.connections.values() {
                    if !conn.may_initiate {
                        continue;
                    }
                    candidates += 1;
                    if offer(&conn.stage).await {
                        admitted += 1;
                    }
                }
            }
            Some(wanted) => {
                for peer in wanted {
                    let Some(conn) = self.connections.values().find(|c| c.may_initiate && c.peer == peer) else {
                        continue;
                    };
                    candidates += 1;
                    if offer(&conn.stage).await {
                        admitted += 1;
                    }
                }
            }
        }
        // No initiating connection is a pause. Connections that exist but all refused
        // are reported at once: the fetch stage asks someone it has not already chosen,
        // or pauses on the timeout it already armed, instead of staying silent.
        if candidates == 0 {
            debug!(protocols::manager::blocks::FETCH_NO_PEERS, id);
            eff.send(&cr, Blocks::NoPeersAvailable(id)).await;
        } else if admitted == 0 {
            debug!(protocols::manager::blocks::FETCH_NONE_ACCEPTED, id, candidates);
            eff.send(&cr, Blocks::NoneAccepted(id)).await;
        } else {
            debug!(protocols::manager::blocks::FETCH_SENT, id, sent = admitted);
        }
    }

    async fn request_share_peers(
        &self,
        peer: Peer,
        amount: u8,
        initial_delay: std::time::Duration,
        interval: std::time::Duration,
        reply_to: StageRef<ShareResult>,
        eff: &Effects<ManagerMessage>,
    ) {
        let Some(stage) =
            self.connections.values().find(|c| c.may_initiate && c.peer == peer).map(|conn| conn.stage.clone())
        else {
            debug!(protocols::manager::sharing::REQUEST_NO_CONNECTION, peer);
            eff.send(&reply_to, ShareResult { peer, peers: Vec::new() }).await;
            return;
        };
        // `Full` and `Gone` never started the initiator. The empty result is the same
        // "not asked" reply as a missing connection, so `reply_to` is not left waiting.
        // The manager entry stays; `ConnectionDied` drops a stage that is already gone.
        if eff
            .try_send(
                &stage,
                ConnectionMessage::RequestSharePeers { amount, initial_delay, interval, reply_to: reply_to.clone() },
            )
            .await
            != TrySend::Queued
        {
            eff.send(&reply_to, ShareResult { peer, peers: Vec::new() }).await;
        }
    }
}

/// The manager stage is responsible for managing the connections to the peers.
///
/// The semantics of the operations are as follows:
/// - AddPeer: add a peer to the manager unless that peer is already added
/// - RemovePeer: drop the peer once each live connection accepts Disconnect, or is already gone
///
/// A peer can be added right after being removed even though the socket will be closed asynchronously.
pub async fn stage(mut manager: Manager, msg: ManagerMessage, eff: Effects<ManagerMessage>) -> Manager {
    let message_type = msg.message_type().to_string();
    let span = debug_span!(protocols::manager::message::PROCESS, message_type);

    async move {
        match msg {
            ManagerMessage::AddPeer(peer) => {
                let span = debug_span!(protocols::manager::peer::ADD, peer);
                manager.add_peer(peer, &eff).instrument(span).await;
            }
            ManagerMessage::Accepted(peer, conn_id) => {
                let span = debug_span!(protocols::manager::peer::ACCEPTED, peer, conn_id = conn_id.as_u64());
                manager.accepted(peer, conn_id, &eff).instrument(span).await;
            }
            ManagerMessage::RemovePeer(peer) => {
                let span = debug_span!(protocols::manager::peer::REMOVE, peer);
                manager.remove_peer(peer, &eff).instrument(span).await;
            }
            ManagerMessage::Disconnect(peer, conn_id) => {
                debug!(
                    protocols::manager::peer::DISCONNECTING,
                    peer,
                    conn_id = conn_id.as_u64(),
                    direction = "requested"
                );
                if let Some((stage, direction)) =
                    manager.connections.get(&conn_id).map(|connection| (connection.stage.clone(), connection.direction))
                {
                    // `Queued` leaves the entry until the connection stops and `ConnectionDied`
                    // arrives. `Full` leaves it too: the connection is still running. `Gone`
                    // drops it now, because the stage is already dead.
                    match eff.try_send(&stage, ConnectionMessage::Disconnect).await {
                        TrySend::Gone => {
                            manager.forget_live_connection(peer, conn_id, direction, &eff).await;
                        }
                        TrySend::Full => {
                            debug!(
                                protocols::manager::peer::DISCONNECT_IGNORED,
                                peer,
                                reason = "not_admitted",
                                conn_id = conn_id.as_u64()
                            );
                        }
                        TrySend::Queued => {}
                    }
                } else {
                    debug!(
                        protocols::manager::peer::DISCONNECT_IGNORED,
                        peer,
                        reason = "connection_not_found",
                        conn_id = conn_id.as_u64()
                    );
                }
            }
            ManagerMessage::ConnectionDied(peer, conn_id, role) => {
                let span = debug_span!(
                    protocols::manager::peer::CONNECTION_DIED,
                    peer,
                    conn_id = conn_id.as_u64(),
                    role = role.to_string(),
                );
                manager.connection_died(peer, conn_id, role, &eff).instrument(span).await;
            }
            ManagerMessage::HandshakeComplete {
                peer,
                stage,
                conn_id,
                role,
                full_duplex_capable,
                full_duplex,
                advertisable,
            } => {
                manager
                    .handshake_complete(
                        peer,
                        stage,
                        conn_id,
                        role,
                        full_duplex_capable,
                        full_duplex,
                        advertisable,
                        &eff,
                    )
                    .await;
            }
            ManagerMessage::Listen(listen_addr) => {
                manager.listen(listen_addr, &eff).await;
            }
            ManagerMessage::NewTip(tip, trace_context) => {
                for conn in manager.connections.values() {
                    // A tip that does not fit is skipped. The next header sends the newer one.
                    let _ = eff.try_send(&conn.stage, ConnectionMessage::NewTip(tip, trace_context.clone())).await;
                }
            }
            ManagerMessage::FetchBlocks { from, through, cr, id, peers } => {
                manager.fetch_blocks(from, through, cr, id, peers, &eff).await;
            }
            ManagerMessage::RequestSharePeers { peer, amount, initial_delay, interval, reply_to } => {
                manager.request_share_peers(peer, amount, initial_delay, interval, reply_to, &eff).await;
            }
            ManagerMessage::ShareRequest { peer, amount, reply_to } => {
                eff.send(&manager.peer_selection, PeerSelectionNotify::ShareRequest { peer, amount, reply_to }).await;
            }
            ManagerMessage::ConnectionResult(peer, conn_id) => {
                manager.connection_result(peer, conn_id, &eff).await;
            }
            ManagerMessage::SetLocalUse { peer, conn_id, local_use } => {
                if let Some(stage) = manager.connections.get(&conn_id).map(|connection| connection.stage.clone()) {
                    info!(
                        protocols::manager::peer::SET_LOCAL_USE,
                        peer,
                        conn_id = conn_id.as_u64(),
                        local_use = format!("{local_use:?}")
                    );
                    // `may_initiate` changes only when the connection reports `LocalUseApplied`.
                    // `Full` and `Gone` do not pretend the use was applied, and do not drop the entry.
                    let _ = eff.try_send(&stage, ConnectionMessage::SetLocalUse(local_use)).await;
                }
            }
            ManagerMessage::LocalUseApplied { peer, conn_id, local_use } => {
                info!(
                    protocols::manager::peer::LOCAL_USE_APPLIED,
                    peer,
                    conn_id = conn_id.as_u64(),
                    local_use = local_use.as_str(),
                );
                if let Some(connection) = manager.connections.get_mut(&conn_id) {
                    connection.may_initiate = local_use == LocalUse::Diffusion;
                }
            }
        }
        manager
    }
    .instrument(span)
    .await
}

/// Close the connection and log any errors.
async fn close_connection(eff: &Effects<ManagerMessage>, peer: &Peer, conn_id: ConnectionId) {
    if let Err(err) = Network::new(eff).close(conn_id).await {
        error!(protocols::manager::peer::CLOSE_FAILED, peer, error = err.to_string());
    }
}

pub fn register_deserializers() -> DeserializerGuards {
    let mut guards = vec![
        register_data_deserializer::<Manager>().boxed(),
        register_data_deserializer::<ManagerMessage>().boxed(),
        register_data_deserializer::<PeerSelectionNotify>().boxed(),
        register_data_deserializer::<Instant>().boxed(),
    ];
    guards.extend(connector::register_deserializers());
    guards
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use amaru_kernel::PREPROD_ERA_HISTORY;
    use amaru_pure_stage::{
        DEFAULT_MAILBOX_SIZE, StageGraph, StageResponse, TraceMatch,
        simulation::{Run, SimulationBuilder, SimulationRunning},
        trace_buffer::{TraceBuffer, TraceEntry},
        trace_match::{
            assert_trace_match_filter, tm_input, tm_resume_try_send, tm_send, tm_state_match, tm_try_send_match,
        },
    };
    use tokio::runtime::Runtime;

    use super::*;

    async fn hold(_state: (), _msg: ConnectionMessage, eff: Effects<ConnectionMessage>) {
        eff.wait(Duration::from_secs(3600)).await;
    }

    fn drop_other_stages(keep: &str) -> TraceMatch<'static> {
        let keep = keep.to_string();
        let description = format!("stage other than {keep}");
        TraceMatch::Property(
            Box::new(move |src| {
                src.entry().and_then(|entry| entry.at_stage()).is_some_and(|stage| stage.as_str() != keep)
            }),
            description,
        )
    }

    /// Drops resumes other than [`StageResponse::TrySend`]. The admission result is that resume.
    fn drop_resume_except_try_send() -> TraceMatch<'static> {
        TraceMatch::Property(
            Box::new(|src| match src.entry() {
                Some(TraceEntry::Resume { response: StageResponse::TrySend(_), .. }) => false,
                Some(TraceEntry::Resume { .. }) => true,
                _ => false,
            }),
            "Resume other than TrySend".to_string(),
        )
    }

    struct Fanout {
        manager: amaru_pure_stage::stage_ref::StageStateRef<ManagerMessage, Manager>,
        full: amaru_pure_stage::stage_ref::StageStateRef<ConnectionMessage, ()>,
        open: amaru_pure_stage::stage_ref::StageStateRef<ConnectionMessage, ()>,
        replies: amaru_pure_stage::stage_ref::StageStateRef<Blocks, Vec<Blocks>>,
        replies_ref: StageRef<Blocks>,
        full_peer: Peer,
        open_peer: Peer,
        running: SimulationRunning,
        guards: amaru_pure_stage::DeserializerGuards,
    }

    fn fanout(fill_open: bool) -> Fanout {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let full = network.stage("peer-full", hold);
        let open = network.stage("peer-open", hold);
        let replies = network.stage("replies", async |mut seen: Vec<Blocks>, msg: Blocks, _eff: Effects<Blocks>| {
            seen.push(msg);
            seen
        });
        let full_sender = full.sender();
        let open_sender = open.sender();
        let replies_sender = replies.sender();
        let full = network.wire_up(full, ());
        let open = network.wire_up(open, ());
        let replies = network.wire_up(replies, Vec::new());

        let full_peer = Peer::for_test(3001);
        let open_peer = Peer::for_test(3002);
        let mut ids = ConnectionId::initial();
        let full_id = ids.get_and_increment();
        let open_id = ids.get_and_increment();
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            full_id,
            Connection {
                peer: full_peer,
                stage: full_sender,
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        state.connections.insert(
            open_id,
            Connection {
                peer: open_peer,
                stage: open_sender,
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        let manager = network.wire_up(manager, state);

        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        park(&mut running, &full);
        park(&mut running, &open);
        stuff(&mut running, &full);
        if fill_open {
            stuff(&mut running, &open);
        }
        running.trace_buffer().lock().clear();
        Fanout {
            manager,
            full,
            open,
            replies,
            replies_ref: replies_sender,
            full_peer,
            open_peer,
            running,
            guards: _guards,
        }
    }

    fn park(running: &mut SimulationRunning, stage: &impl AsRef<StageRef<ConnectionMessage>>) {
        running.enqueue_msg(stage, [ConnectionMessage::new_tip(Point::Origin)]);
        running.run(Run::default()).assert_sleeping();
        assert_eq!(running.mailbox_len(stage), 0);
    }

    fn stuff(running: &mut SimulationRunning, stage: &impl AsRef<StageRef<ConnectionMessage>>) {
        for _ in 0..DEFAULT_MAILBOX_SIZE {
            running.enqueue_msg(stage, [ConnectionMessage::new_tip(Point::Origin)]);
        }
        assert_eq!(running.mailbox_len(stage), DEFAULT_MAILBOX_SIZE);
    }

    fn fetch(id: u64, cr: StageRef<Blocks>, peers: Option<Vec<Peer>>) -> ManagerMessage {
        ManagerMessage::FetchBlocks { from: Point::Origin, through: Point::Origin, cr, id, peers }
    }

    #[test]
    fn nonblocking_fetch_skips_full_peer() {
        let Fanout { manager, full, open, replies, replies_ref, full_peer, open_peer, mut running, guards: _guards } =
            fanout(false);
        let msg = fetch(7, replies_ref, Some(vec![full_peer, open_peer]));
        running.enqueue_msg(&manager, [msg.clone()]);
        running.run(Run::default()).assert_sleeping();

        assert!(running.get_state(&manager).is_some(), "manager waited on a full peer");
        assert_eq!(running.mailbox_len(&full), DEFAULT_MAILBOX_SIZE);
        assert_eq!(running.mailbox_len(&open), 1);
        assert!(running.get_state(&replies).unwrap().is_empty(), "manager does not emit PeersAsked");

        let name = manager.name().as_str();
        assert_trace_match_filter(
            &running,
            &[
                tm_input(name, &msg),
                tm_try_send_match(name, "peer-full", |sent: &ConnectionMessage| {
                    matches!(sent, ConnectionMessage::FetchBlocks { id: 7, .. })
                }),
                tm_resume_try_send(name, TrySend::Full),
                tm_try_send_match(name, "peer-open", |sent: &ConnectionMessage| {
                    matches!(sent, ConnectionMessage::FetchBlocks { id: 7, .. })
                }),
                tm_resume_try_send(name, TrySend::Queued),
                tm_state_match(name, |state: &Manager| state.connections.len() == 2),
            ],
            &[drop_resume_except_try_send(), drop_other_stages(name)],
        );
    }

    #[test]
    fn nonblocking_fetch_all_full_notifies_immediately() {
        let Fanout { manager, full, open, replies, replies_ref, full_peer, open_peer, mut running, guards: _guards } =
            fanout(true);
        let msg = fetch(7, replies_ref, Some(vec![full_peer, open_peer]));
        running.enqueue_msg(&manager, [msg.clone()]);
        running.run(Run::default()).assert_sleeping();

        assert!(running.get_state(&manager).is_some(), "manager waited on a full peer");
        assert_eq!(running.mailbox_len(&full), DEFAULT_MAILBOX_SIZE);
        assert_eq!(running.mailbox_len(&open), DEFAULT_MAILBOX_SIZE);
        assert_eq!(running.get_state(&replies).unwrap().as_slice(), &[Blocks::NoneAccepted(7)]);

        let name = manager.name().as_str();
        assert_trace_match_filter(
            &running,
            &[
                tm_input(name, &msg),
                tm_try_send_match(name, "peer-full", |sent: &ConnectionMessage| {
                    matches!(sent, ConnectionMessage::FetchBlocks { id: 7, .. })
                }),
                tm_resume_try_send(name, TrySend::Full),
                tm_try_send_match(name, "peer-open", |sent: &ConnectionMessage| {
                    matches!(sent, ConnectionMessage::FetchBlocks { id: 7, .. })
                }),
                tm_resume_try_send(name, TrySend::Full),
                tm_send(name, "replies", Blocks::NoneAccepted(7)),
                tm_state_match(name, |state: &Manager| state.connections.len() == 2),
            ],
            &[drop_resume_except_try_send(), drop_other_stages(name)],
        );
    }

    #[test]
    fn nonblocking_fetch_all_gone_notifies_immediately() {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let replies = network.stage("replies", async |mut seen: Vec<Blocks>, msg: Blocks, _eff: Effects<Blocks>| {
            seen.push(msg);
            seen
        });
        let replies_sender = replies.sender();
        let replies = network.wire_up(replies, Vec::new());
        let peer = Peer::for_test(3001);
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            ConnectionId::initial(),
            Connection {
                peer,
                stage: StageRef::named_for_tests("peer-gone"),
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        running.trace_buffer().lock().clear();

        let msg = fetch(7, replies_sender, Some(vec![peer]));
        running.enqueue_msg(&manager, [msg.clone()]);
        running.run(Run::default()).assert_idle();
        assert_eq!(running.get_state(&replies).unwrap().as_slice(), &[Blocks::NoneAccepted(7)]);

        let name = manager.name().as_str();
        assert_trace_match_filter(
            &running,
            &[
                tm_input(name, &msg),
                tm_try_send_match(name, "peer-gone", |sent: &ConnectionMessage| {
                    matches!(sent, ConnectionMessage::FetchBlocks { id: 7, .. })
                }),
                tm_resume_try_send(name, TrySend::Gone),
                tm_send(name, "replies", Blocks::NoneAccepted(7)),
                tm_state_match(name, |state: &Manager| state.connections.len() == 1),
            ],
            &[drop_resume_except_try_send(), drop_other_stages(name)],
        );
    }

    #[test]
    fn nonblocking_fetch_without_candidates_emits_no_peers() {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let replies = network.stage("replies", async |mut seen: Vec<Blocks>, msg: Blocks, _eff: Effects<Blocks>| {
            seen.push(msg);
            seen
        });
        let replies_sender = replies.sender();
        let replies = network.wire_up(replies, Vec::new());
        let state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        running.trace_buffer().lock().clear();

        let msg = fetch(7, replies_sender, None);
        running.enqueue_msg(&manager, [msg.clone()]);
        running.run(Run::default()).assert_idle();
        assert_eq!(running.get_state(&replies).unwrap().as_slice(), &[Blocks::NoPeersAvailable(7)]);

        let name = manager.name().as_str();
        assert_trace_match_filter(
            &running,
            &[
                tm_input(name, &msg),
                tm_send(name, "replies", Blocks::NoPeersAvailable(7)),
                tm_state_match(name, |state: &Manager| state.connections.is_empty()),
            ],
            &[drop_resume_except_try_send(), drop_other_stages(name)],
        );
    }

    #[test]
    fn nonblocking_new_tip_skips_full_peer() {
        let Fanout {
            manager,
            full,
            open,
            replies: _,
            replies_ref: _,
            full_peer: _,
            open_peer: _,
            mut running,
            guards: _guards,
        } = fanout(false);
        let tip = Point::Origin;
        let msg = ManagerMessage::new_tip(tip);
        running.enqueue_msg(&manager, [msg.clone()]);
        running.run(Run::default()).assert_sleeping();

        assert!(running.get_state(&manager).is_some(), "manager waited on a full peer");
        assert_eq!(running.mailbox_len(&full), DEFAULT_MAILBOX_SIZE);
        assert_eq!(running.mailbox_len(&open), 1);

        let name = manager.name().as_str();
        assert_trace_match_filter(
            &running,
            &[
                tm_input(name, &msg),
                tm_try_send_match(
                    name,
                    "peer-full",
                    |sent: &ConnectionMessage| matches!(sent, ConnectionMessage::NewTip(point, _) if *point == tip),
                ),
                tm_resume_try_send(name, TrySend::Full),
                tm_try_send_match(
                    name,
                    "peer-open",
                    |sent: &ConnectionMessage| matches!(sent, ConnectionMessage::NewTip(point, _) if *point == tip),
                ),
                tm_resume_try_send(name, TrySend::Queued),
                tm_state_match(name, |state: &Manager| state.connections.len() == 2),
            ],
            &[drop_resume_except_try_send(), drop_other_stages(name)],
        );
    }

    struct OnePeer {
        manager: amaru_pure_stage::stage_ref::StageStateRef<ManagerMessage, Manager>,
        connection: amaru_pure_stage::stage_ref::StageStateRef<ConnectionMessage, ()>,
        shares: amaru_pure_stage::stage_ref::StageStateRef<ShareResult, Vec<ShareResult>>,
        shares_ref: StageRef<ShareResult>,
        peer: Peer,
        conn_id: ConnectionId,
        running: SimulationRunning,
        guards: amaru_pure_stage::DeserializerGuards,
    }

    fn one_peer(fill: bool) -> OnePeer {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let connection = network.stage("peer-open", hold);
        let shares = network.stage(
            "shares",
            async |mut seen: Vec<ShareResult>, msg: ShareResult, _eff: Effects<ShareResult>| {
                seen.push(msg);
                seen
            },
        );
        let connection_sender = connection.sender();
        let shares_ref = shares.sender();
        let connection = network.wire_up(connection, ());
        let shares = network.wire_up(shares, Vec::new());
        let peer = Peer::for_test(3001);
        let conn_id = ConnectionId::initial();
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            conn_id,
            Connection {
                peer,
                stage: connection_sender,
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        state.peers.insert(peer, PeerState { outbound: OutboundState::Connected { conn_id }, inbound: None });
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        park(&mut running, &connection);
        if fill {
            stuff(&mut running, &connection);
        }
        running.trace_buffer().lock().clear();
        OnePeer { manager, connection, shares, shares_ref, peer, conn_id, running, guards: _guards }
    }

    fn tracked(state: &Manager, peer: Peer, conn_id: ConnectionId) -> bool {
        state.connections.contains_key(&conn_id)
            && matches!(
                state.peers.get(&peer).map(|peer_state| &peer_state.outbound),
                Some(OutboundState::Connected { conn_id: id }) if *id == conn_id
            )
    }

    #[test]
    fn remove_peer_full_keeps_the_connection() {
        let OnePeer { manager, connection, peer, conn_id, mut running, guards: _guards, .. } = one_peer(true);
        running.enqueue_msg(&manager, [ManagerMessage::RemovePeer(peer)]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager waited on a full connection");
        assert!(tracked(state, peer, conn_id), "Full must not mark the peer disconnected");
        assert_eq!(state.connections.get(&conn_id).map(|conn| conn.may_initiate), Some(true));
        assert_eq!(running.mailbox_len(&connection), DEFAULT_MAILBOX_SIZE);
    }

    #[test]
    fn remove_peer_queued_drops_the_connection() {
        let OnePeer { manager, connection, peer, conn_id: _, mut running, guards: _guards, .. } = one_peer(false);
        running.enqueue_msg(&manager, [ManagerMessage::RemovePeer(peer)]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(state.connections.is_empty());
        assert!(!state.peers.contains_key(&peer));
        assert_eq!(running.mailbox_len(&connection), 1, "Disconnect was admitted");
    }

    #[test]
    fn remove_peer_gone_drops_the_connection() {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let peer = Peer::for_test(3001);
        let conn_id = ConnectionId::initial();
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            conn_id,
            Connection {
                peer,
                stage: StageRef::named_for_tests("peer-gone"),
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        state.peers.insert(peer, PeerState { outbound: OutboundState::Connected { conn_id }, inbound: None });
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        running.trace_buffer().lock().clear();

        running.enqueue_msg(&manager, [ManagerMessage::RemovePeer(peer)]);
        running.run(Run::default()).assert_idle();
        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(state.connections.is_empty());
        assert!(!state.peers.contains_key(&peer));
    }

    #[test]
    fn disconnect_full_keeps_the_connection() {
        let OnePeer { manager, connection, peer, conn_id, mut running, guards: _guards, .. } = one_peer(true);
        running.enqueue_msg(&manager, [ManagerMessage::Disconnect(peer, conn_id)]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager waited on a full connection");
        assert!(tracked(state, peer, conn_id));
        assert_eq!(running.mailbox_len(&connection), DEFAULT_MAILBOX_SIZE);
    }

    #[test]
    fn disconnect_queued_leaves_the_entry_until_death() {
        let OnePeer { manager, connection, peer, conn_id, mut running, guards: _guards, .. } = one_peer(false);
        running.enqueue_msg(&manager, [ManagerMessage::Disconnect(peer, conn_id)]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(tracked(state, peer, conn_id), "Queued Disconnect is finished by ConnectionDied");
        assert_eq!(running.mailbox_len(&connection), 1);
    }

    #[test]
    fn disconnect_gone_drops_the_connection() {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let peer = Peer::for_test(3001);
        let conn_id = ConnectionId::initial();
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            conn_id,
            Connection {
                peer,
                stage: StageRef::named_for_tests("peer-gone"),
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        state.peers.insert(peer, PeerState { outbound: OutboundState::Connected { conn_id }, inbound: None });
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        running.trace_buffer().lock().clear();

        running.enqueue_msg(&manager, [ManagerMessage::Disconnect(peer, conn_id)]);
        running.run(Run::default()).assert_idle();
        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(state.connections.is_empty());
        assert!(!state.peers.contains_key(&peer));
    }

    #[test]
    fn set_local_use_full_does_not_change_initiation() {
        let OnePeer { manager, connection, peer, conn_id, mut running, guards: _guards, .. } = one_peer(true);
        running
            .enqueue_msg(&manager, [ManagerMessage::SetLocalUse { peer, conn_id, local_use: LocalUse::Maintenance }]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager waited on a full connection");
        assert_eq!(state.connections.get(&conn_id).map(|conn| conn.may_initiate), Some(true));
        assert!(tracked(state, peer, conn_id));
        assert_eq!(running.mailbox_len(&connection), DEFAULT_MAILBOX_SIZE);
    }

    #[test]
    fn set_local_use_queued_waits_for_the_connection_to_apply_it() {
        let OnePeer { manager, connection, peer, conn_id, mut running, guards: _guards, .. } = one_peer(false);
        running
            .enqueue_msg(&manager, [ManagerMessage::SetLocalUse { peer, conn_id, local_use: LocalUse::Maintenance }]);
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert_eq!(state.connections.get(&conn_id).map(|conn| conn.may_initiate), Some(true));
        assert_eq!(running.mailbox_len(&connection), 1);
    }

    #[test]
    fn share_request_full_replies_empty_and_keeps_the_connection() {
        let OnePeer { manager, connection, shares, shares_ref, peer, conn_id, mut running, guards: _guards } =
            one_peer(true);
        running.enqueue_msg(
            &manager,
            [ManagerMessage::RequestSharePeers {
                peer,
                amount: 3,
                initial_delay: Duration::from_secs(1),
                interval: Duration::from_secs(60),
                reply_to: shares_ref,
            }],
        );
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager waited on a full connection");
        assert!(tracked(state, peer, conn_id));
        assert_eq!(running.mailbox_len(&connection), DEFAULT_MAILBOX_SIZE);
        assert_eq!(running.get_state(&shares).unwrap().as_slice(), &[ShareResult { peer, peers: Vec::new() }]);
    }

    #[test]
    fn share_request_queued_does_not_reply_empty() {
        let OnePeer { manager, connection, shares, shares_ref, peer, conn_id, mut running, guards: _guards } =
            one_peer(false);
        running.enqueue_msg(
            &manager,
            [ManagerMessage::RequestSharePeers {
                peer,
                amount: 3,
                initial_delay: Duration::from_secs(1),
                interval: Duration::from_secs(60),
                reply_to: shares_ref,
            }],
        );
        running.run(Run::default()).assert_sleeping();

        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(tracked(state, peer, conn_id));
        assert_eq!(running.mailbox_len(&connection), 1);
        assert!(running.get_state(&shares).unwrap().is_empty());
    }

    #[test]
    fn share_request_gone_replies_empty_and_leaves_cleanup_to_the_tombstone() {
        let trace_buffer = TraceBuffer::new_shared(100, 1_000_000);
        let mut network = SimulationBuilder::default().with_trace_buffer(trace_buffer);
        let manager = network.stage("manager", stage);
        let shares = network.stage(
            "shares",
            async |mut seen: Vec<ShareResult>, msg: ShareResult, _eff: Effects<ShareResult>| {
                seen.push(msg);
                seen
            },
        );
        let shares_ref = shares.sender();
        let shares = network.wire_up(shares, Vec::new());
        let peer = Peer::for_test(3001);
        let conn_id = ConnectionId::initial();
        let mut state = Manager::new(
            NetworkMagic::PREPROD,
            ManagerConfig::default(),
            Arc::new(PREPROD_ERA_HISTORY.clone()),
            StageRef::blackhole(),
            StageRef::blackhole(),
            StageRef::blackhole(),
        );
        state.connections.insert(
            conn_id,
            Connection {
                peer,
                stage: StageRef::named_for_tests("peer-gone"),
                direction: ConnectionDirection::Outbound,
                may_initiate: true,
                full_duplex_capable: true,
            },
        );
        state.peers.insert(peer, PeerState { outbound: OutboundState::Connected { conn_id }, inbound: None });
        let manager = network.wire_up(manager, state);
        let rt = Runtime::new().unwrap();
        let mut running = network.run(rt.handle());
        let _guards = crate::deserializers::register_deserializers();
        running.run(Run::default()).assert_idle();
        running.trace_buffer().lock().clear();

        running.enqueue_msg(
            &manager,
            [ManagerMessage::RequestSharePeers {
                peer,
                amount: 3,
                initial_delay: Duration::from_secs(1),
                interval: Duration::from_secs(60),
                reply_to: shares_ref,
            }],
        );
        running.run(Run::default()).assert_idle();
        let state = running.get_state(&manager).expect("manager stayed runnable");
        assert!(tracked(state, peer, conn_id), "ConnectionDied drops a stage that is already gone");
        assert_eq!(running.get_state(&shares).unwrap().as_slice(), &[ShareResult { peer, peers: Vec::new() }]);
    }
}
