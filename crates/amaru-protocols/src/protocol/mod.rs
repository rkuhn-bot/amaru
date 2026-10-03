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

use std::{
    fmt::{Display, Formatter},
    marker::PhantomData,
    time::Duration,
};

use bytes::{Buf, BufMut, Bytes, BytesMut, TryGetError};

mod check;
mod limits;
mod miniprotocol;
mod pipeline;
mod want_next;

pub use check::ProtoSpec;
pub use limits::{
    BLOCK_FETCH_INGRESS, CHAIN_SYNC_INGRESS, CHAIN_SYNC_INGRESS_DEADLINE, HANDSHAKE_INGRESS, KEEP_ALIVE_INGRESS,
    PEER_SHARING_INGRESS, TX_SUBMISSION_INGRESS, ingress_deadline, ingress_limit,
};
pub use miniprotocol::{
    Inputs, Internal, Miniprotocol, Outcome, ProtocolState, Pull, StageState, Timeout, from_wire, miniprotocol, outcome,
};
pub(crate) use pipeline::{MuxClient, Pipelined, ToMux, WantNext, drive, pipelined};
pub use want_next::{WantNextError, check_want_next};

/// Input to a protocol step
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Input<L, R> {
    Local(L),
    Remote(R),
}

// TODO(network) find right value
pub const NETWORK_SEND_TIMEOUT: Duration = Duration::from_secs(1);

/// Slowest sustained rate at which a peer is still only slow.
///
/// A peer is expected to sustain 100 Mbps. Below this rate, in a challenging
/// situation, the connection is closed. The peer is not recorded as adversarial.
/// Bits per second.
pub const MIN_PEER_BANDWIDTH_BPS: u64 = 500_000;

/// Node-to-node mini-protocols that share one writer.
///
/// One lane per [`KnownProtocol`] variant. Adding a variant without counting it
/// fails the const assert below.
pub const MAX_PROTOCOLS_PER_CONNECTION: usize = {
    const fn one(protocol: KnownProtocol) -> usize {
        match protocol {
            KnownProtocol::Handshake => 1,
            KnownProtocol::ChainSync => 1,
            KnownProtocol::BlockFetch => 1,
            KnownProtocol::TxSubmission => 1,
            KnownProtocol::KeepAlive => 1,
            KnownProtocol::PeerShare => 1,
        }
    }
    one(KnownProtocol::Handshake)
        + one(KnownProtocol::ChainSync)
        + one(KnownProtocol::BlockFetch)
        + one(KnownProtocol::TxSubmission)
        + one(KnownProtocol::KeepAlive)
        + one(KnownProtocol::PeerShare)
};

#[derive(serde::Serialize, serde::Deserialize, PartialEq)]
pub struct ProtocolId<T: RoleT>(u16, PhantomData<T>);

impl<T: RoleT> ProtocolId<T> {
    pub fn encode(self, buffer: &mut BytesMut) {
        buffer.put_u16(self.0);
    }

    pub fn decode(buffer: &mut Bytes) -> Result<Self, TryGetError> {
        Ok(Self(buffer.try_get_u16()?, PhantomData))
    }
}

impl<T: RoleT> std::fmt::Display for ProtocolId<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: RoleT> std::hash::Hash for ProtocolId<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: RoleT> Ord for ProtocolId<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T: RoleT> PartialOrd for ProtocolId<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: RoleT> Eq for ProtocolId<T> {}

impl<T: RoleT> std::fmt::Debug for ProtocolId<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ProtocolId").field(&self.0).finish()
    }
}

impl<T: RoleT> Copy for ProtocolId<T> {}

impl<R: RoleT> Clone for ProtocolId<R> {
    fn clone(&self) -> Self {
        *self
    }
}

const RESPONDER: u16 = 0x8000;

#[derive(Debug, PartialEq, Eq, Clone, Copy, serde::Serialize, serde::Deserialize)]
pub enum Role {
    Initiator,
    Responder,
}

impl Display for Role {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Role::Initiator => write!(f, "initiator"),
            Role::Responder => write!(f, "responder"),
        }
    }
}

impl Role {
    pub const fn opposite(self) -> Role {
        match self {
            Role::Initiator => Role::Responder,
            Role::Responder => Role::Initiator,
        }
    }
}

mod sealed {
    pub trait Sealed {}
}
pub trait RoleT:
    Clone
    + Copy
    + std::fmt::Debug
    + std::hash::Hash
    + std::cmp::Ord
    + std::cmp::PartialOrd
    + std::cmp::Eq
    + std::cmp::PartialEq
    + serde::Serialize
    + serde::de::DeserializeOwned
    + Send
    + Sync
    + 'static
    + sealed::Sealed
{
    type Opposite: RoleT;

    const ROLE: Option<Role>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct Initiator;
impl sealed::Sealed for Initiator {}
impl RoleT for Initiator {
    type Opposite = Responder;

    const ROLE: Option<Role> = Some(Role::Initiator);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct Responder;
impl sealed::Sealed for Responder {}
impl RoleT for Responder {
    type Opposite = Initiator;

    const ROLE: Option<Role> = Some(Role::Responder);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct Erased;
impl sealed::Sealed for Erased {}
impl RoleT for Erased {
    type Opposite = Erased;

    const ROLE: Option<Role> = None;
}

pub const PROTO_HANDSHAKE: ProtocolId<Initiator> = ProtocolId::<Initiator>(0, PhantomData);

pub const PROTO_N2N_CHAIN_SYNC: ProtocolId<Initiator> = ProtocolId::<Initiator>(2, PhantomData);
pub const PROTO_N2N_BLOCK_FETCH: ProtocolId<Initiator> = ProtocolId::<Initiator>(3, PhantomData);
pub const PROTO_N2N_TX_SUB: ProtocolId<Initiator> = ProtocolId::<Initiator>(4, PhantomData);
pub const PROTO_N2N_KEEP_ALIVE: ProtocolId<Initiator> = ProtocolId::<Initiator>(8, PhantomData);
pub const PROTO_N2N_PEER_SHARE: ProtocolId<Initiator> = ProtocolId::<Initiator>(10, PhantomData);

pub enum KnownProtocol {
    Handshake,
    ChainSync,
    BlockFetch,
    TxSubmission,
    KeepAlive,
    PeerShare,
}

impl KnownProtocol {
    pub fn protocol_id<R: RoleT>(&self) -> ProtocolId<R> {
        match self {
            KnownProtocol::Handshake => PROTO_HANDSHAKE.for_role_t(),
            KnownProtocol::ChainSync => PROTO_N2N_CHAIN_SYNC.for_role_t(),
            KnownProtocol::BlockFetch => PROTO_N2N_BLOCK_FETCH.for_role_t(),
            KnownProtocol::TxSubmission => PROTO_N2N_TX_SUB.for_role_t(),
            KnownProtocol::KeepAlive => PROTO_N2N_KEEP_ALIVE.for_role_t(),
            KnownProtocol::PeerShare => PROTO_N2N_PEER_SHARE.for_role_t(),
        }
    }
}

impl<R: RoleT> TryFrom<ProtocolId<R>> for KnownProtocol {
    type Error = ProtocolId<R>;

    fn try_from(protocol_id: ProtocolId<R>) -> Result<Self, Self::Error> {
        match protocol_id.for_role_t::<Initiator>() {
            PROTO_HANDSHAKE => Ok(KnownProtocol::Handshake),
            PROTO_N2N_CHAIN_SYNC => Ok(KnownProtocol::ChainSync),
            PROTO_N2N_BLOCK_FETCH => Ok(KnownProtocol::BlockFetch),
            PROTO_N2N_TX_SUB => Ok(KnownProtocol::TxSubmission),
            PROTO_N2N_KEEP_ALIVE => Ok(KnownProtocol::KeepAlive),
            PROTO_N2N_PEER_SHARE => Ok(KnownProtocol::PeerShare),
            _ => Err(protocol_id),
        }
    }
}

/// Bytes on the wire for `payload` bytes of mini-protocol data.
///
/// Each segment carries [`crate::mux::SEGMENT_HEADER_LEN`] extra bytes. An empty
/// payload contributes nothing.
fn wire_bytes(payload: usize) -> u64 {
    if payload == 0 {
        return 0;
    }
    let payload = u64::try_from(payload).unwrap_or(u64::MAX);
    let segment = u64::try_from(crate::mux::MAX_SEGMENT_SIZE).unwrap_or(u64::MAX);
    let header = u64::try_from(crate::mux::SEGMENT_HEADER_LEN).unwrap_or(u64::MAX);
    let segments = payload.div_ceil(segment);
    payload.saturating_add(segments.saturating_mul(header))
}

/// Largest unsent buffer one lane can hold: one segment, or one max block when
/// the lane was empty.
fn max_unsent_per_lane() -> usize {
    crate::mux::MAX_SEGMENT_SIZE.max(crate::blockfetch::BLOCKFETCH_MAX_BLOCK_WIRE_BYTES)
}

/// Worst-case wire bytes ahead of and including `payload_len`.
///
/// One max segment is already in flight. Every registered lane holds
/// [`max_unsent_per_lane`]. The payload is counted too, so the deadline covers
/// admission and the drain of the last segment. Round-robin can serve the other
/// lanes first; this bound does not assume a friendlier order.
pub fn egress_backlog_wire_bytes(payload_len: usize) -> u64 {
    let inflight = wire_bytes(crate::mux::MAX_SEGMENT_SIZE);
    let lanes = wire_bytes(max_unsent_per_lane())
        .saturating_mul(u64::try_from(MAX_PROTOCOLS_PER_CONNECTION).unwrap_or(u64::MAX));
    inflight.saturating_add(lanes).saturating_add(wire_bytes(payload_len))
}

/// How long a sender may wait for the mux to accept `payload_len` bytes.
///
/// The connection has one writer. A peer sustaining [`MIN_PEER_BANDWIDTH_BPS`]
/// drains [`egress_backlog_wire_bytes`] before this payload is both admitted and
/// written. [`NETWORK_SEND_TIMEOUT`] is added on top so scheduling jitter cannot
/// fault that peer. A slower peer is dropped and is not recorded as adversarial.
///
/// ```text
/// wire(n) = 0, if n = 0
///         = n + ceil(n / MAX_SEGMENT_SIZE) * SEGMENT_HEADER_LEN, otherwise
/// backlog = wire(MAX_SEGMENT_SIZE)
///         + MAX_PROTOCOLS_PER_CONNECTION * wire(max(MAX_SEGMENT_SIZE, BLOCKFETCH_MAX_BLOCK_WIRE_BYTES))
///         + wire(payload_len)
/// deadline = ceil(backlog * 8 * 1000 / MIN_PEER_BANDWIDTH_BPS) milliseconds
///          + NETWORK_SEND_TIMEOUT
/// ```
///
/// For a 96 KiB block the backlog is 753_783 wire bytes: 12.061 s at 500 kbps,
/// plus the 1 s floor, 13.061 s. Counting the payload's own transmission and the
/// last segment's full drain is later than the moment of admission. That slack
/// is intentional. A tighter round-robin expression was not taken.
pub fn egress_admission_deadline(payload_len: usize) -> Duration {
    let millis =
        egress_backlog_wire_bytes(payload_len).saturating_mul(8).saturating_mul(1000).div_ceil(MIN_PEER_BANDWIDTH_BPS);
    Duration::from_millis(millis) + NETWORK_SEND_TIMEOUT
}

// The below are only for information regarding the allocated numbers, Amaru will not implement N2C protocols.

// pub const PROTO_N2C_CHAIN_SYNC: ProtocolId<Initiator> = ProtocolId::<Initiator>(5, PhantomData);
// pub const PROTO_N2C_TX_SUB: ProtocolId<Initiator> = ProtocolId::<Initiator>(6, PhantomData);
// pub const PROTO_N2C_STATE_QUERY: ProtocolId<Initiator> = ProtocolId::<Initiator>(7, PhantomData);
// pub const PROTO_N2C_TX_MON: ProtocolId<Initiator> = ProtocolId::<Initiator>(9, PhantomData);

#[cfg(test)]
pub const PROTO_TEST: ProtocolId<Initiator> = ProtocolId::<Initiator>(257, PhantomData);

impl<R: RoleT> ProtocolId<R> {
    pub const fn is_initiator(self) -> bool {
        self.0 & RESPONDER == 0
    }

    pub const fn is_responder(self) -> bool {
        !self.is_initiator()
    }

    pub const fn opposite(self) -> ProtocolId<R::Opposite> {
        ProtocolId(self.0 ^ RESPONDER, PhantomData)
    }

    pub const fn erase(self) -> ProtocolId<Erased> {
        ProtocolId(self.0, PhantomData)
    }

    pub const fn for_role(self, role: Role) -> ProtocolId<Erased> {
        match (role, self.role()) {
            (Role::Initiator, Role::Initiator) | (Role::Responder, Role::Responder) => self.erase(),
            (Role::Initiator, Role::Responder) | (Role::Responder, Role::Initiator) => self.opposite().erase(),
        }
    }

    pub const fn for_role_t<R2: RoleT>(self) -> ProtocolId<R2> {
        match R2::ROLE {
            Some(Role::Initiator) => ProtocolId(self.for_role(Role::Initiator).0, PhantomData),
            Some(Role::Responder) => ProtocolId(self.for_role(Role::Responder).0, PhantomData),
            None => ProtocolId(self.0, PhantomData),
        }
    }

    pub const fn role(self) -> Role {
        if let Some(role) = R::ROLE {
            role
        } else if self.is_initiator() {
            Role::Initiator
        } else {
            Role::Responder
        }
    }
}

impl ProtocolId<Initiator> {
    pub const fn responder(self) -> ProtocolId<Responder> {
        ProtocolId(self.0 | RESPONDER, PhantomData)
    }
}

impl ProtocolId<Responder> {
    pub const fn initiator(self) -> ProtocolId<Initiator> {
        ProtocolId(self.0 & !RESPONDER, PhantomData)
    }
}

#[cfg(test)]
mod egress_deadline_tests {
    use super::*;

    #[test]
    fn largest_block_worst_case_is_thirteen_seconds() {
        // wire(65535) = 65543
        // wire(98304) = 98320
        // 65543 + 7 * 98320 = 753_783
        // ceil(753_783 * 8 * 1000 / 500_000) = 12_061 ms, plus the 1 s floor.
        assert_eq!(egress_backlog_wire_bytes(crate::blockfetch::BLOCKFETCH_MAX_BLOCK_WIRE_BYTES), 753_783);
        assert_eq!(
            egress_admission_deadline(crate::blockfetch::BLOCKFETCH_MAX_BLOCK_WIRE_BYTES),
            Duration::from_millis(13_061)
        );
    }

    #[test]
    fn one_max_segment_is_longer_than_the_floor_and_the_backlog_covers_it() {
        let segment = crate::mux::MAX_SEGMENT_SIZE + crate::mux::SEGMENT_HEADER_LEN;
        let segment_ms = u64::try_from(segment).unwrap() * 8 * 1000 / MIN_PEER_BANDWIDTH_BPS;
        assert!(segment_ms > 1_000, "one max segment at 500 kbps takes longer than the 1 s floor");
        assert!(egress_admission_deadline(1) > Duration::from_millis(segment_ms));
        assert!(egress_admission_deadline(0) > NETWORK_SEND_TIMEOUT);
    }
}
