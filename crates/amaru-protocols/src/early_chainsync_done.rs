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
    sync::{Arc, Mutex},
};

use amaru_kernel::{EraName, NetworkPoint, NetworkTip, NonEmptyBytes, Point, cbor};
use amaru_ouroboros_traits::in_memory_chain_store::InMemoryChainStore;
use amaru_pure_stage::{
    Effects, StageRef,
    simulation::{Blocked, Externals, SimulationRunning, TimeAdvance},
};

use crate::{
    chainsync::ChainSyncInitiatorMsg,
    mux::{HandlerMessage, MuxMessage, Sent},
    protocol::PROTO_N2N_CHAIN_SYNC,
    protocol_messages::{
        version_data::{PeerSharing, VersionData},
        version_number::VersionNumber,
    },
    store_effects::ResourceHeaderStore,
};

/// One chainsync CBOR item is `array(label, ...)`. `RequestNext(n)` is `n` items of label 0.
const LABEL_REQUEST_NEXT: u16 = 0;
const LABEL_ROLL_FORWARD: u16 = 2;
const LABEL_FIND_INTERSECT: u16 = 4;
const LABEL_INTERSECT_FOUND: u16 = 5;
const LABEL_DONE: u16 = 7;

const STEP_BUDGET: usize = 4_000;

struct Wire {
    handlers: BTreeMap<crate::protocol::ProtocolId<crate::protocol::Erased>, StageRef<HandlerMessage>>,
    chainsync: Vec<Vec<u8>>,
}

/// An honest peer dribbles the post-intersect header burst. Lowering local use must not emit
/// `MsgDone` while `RequestNext` credits are still unanswered, and the late replies must not
/// drop the connection.
#[test]
fn test_msg_done_waits_for_pipelined_replies() {
    let wire = Arc::new(Mutex::new(Wire { handlers: BTreeMap::new(), chainsync: Vec::new() }));
    let mut network = SimulationBuilder::default();
    network.resources().put::<ResourceHeaderStore>(Arc::new(InMemoryChainStore::new()));

    let captured = Arc::clone(&wire);
    let mux = network.stage_with_mailbox_size(
        "peer-mux",
        move |_unit: (), msg: MuxMessage, eff: Effects<MuxMessage>| {
            let captured = Arc::clone(&captured);
            async move {
                peer_mux(&captured, msg, &eff).await;
            }
        },
        64,
    );
    let muxer = mux.sender();
    let pipeline = network.stage(
        "pipeline",
        async |mut seen: Vec<String>, msg: ChainSyncInitiatorMsg, _eff: Effects<ChainSyncInitiatorMsg>| {
            seen.push(msg.msg.message_type().to_string());
            seen
        },
    );
    let pipeline_ref = pipeline.sender();
    let connection = network.stage("connection", stage);
    let connection = network.wire_up(
        connection,
        Connection {
            params: Params {
                peer: Peer::for_test(3009),
                conn_id: ConnectionId::initial(),
                role: Role::Initiator,
                config: ManagerConfig::default(),
                magic: NetworkMagic::PREPROD,
                pipeline: pipeline_ref,
                era_history: Arc::new(PREPROD_ERA_HISTORY.clone()),
                mempool_stage: StageRef::blackhole(),
                manager: StageRef::blackhole(),
            },
            state: State::Established(Established {
                desired_use: LocalUse::None,
                actual_use: LocalUse::None,
                duplex: true,
                version_number: VersionNumber::CURRENT,
                version_data: VersionData::new(NetworkMagic::PREPROD, false, PeerSharing::Enabled, false),
                muxer,
                handshake: StageRef::blackhole(),
                keepalive_initiator: None,
                tx_submission_initiator: None,
                chainsync_initiator: None,
                blockfetch_initiator: None,
                peer_sharing_initiator: None,
                chainsync_responder: None,
                blockfetch_responder: None,
                peer_sharing_responder: None,
                stopping: BTreeSet::new(),
            }),
        },
    );
    let _mux = network.wire_up(mux, ());
    let pipeline = network.wire_up(pipeline, Vec::new());

    let rt = Runtime::new().unwrap();
    let mut running = network.run(rt.handle());

    running.enqueue_msg(&connection, [ConnectionMessage::SetLocalUse(LocalUse::Diffusion)]);
    let blocked = drive(&mut running, STEP_BUDGET);
    let labels = chainsync_labels_of(&wire);
    assert!(
        labels.contains(&LABEL_FIND_INTERSECT),
        "precondition: initiator asked for an intersection; labels={labels:?} pipeline={:?} blocked={blocked:?}",
        running.get_state(&pipeline)
    );

    deliver(&mut running, &wire, intersect_found());
    let blocked = drive(&mut running, STEP_BUDGET);
    let request_next = count_label(&wire, LABEL_REQUEST_NEXT);
    assert!(
        request_next >= 10,
        "precondition: IntersectFound pipelines RequestNext(10); counted={request_next} labels={:?} pipeline={:?} blocked={blocked:?}",
        chainsync_labels_of(&wire),
        running.get_state(&pipeline)
    );

    // Two headers: CanAwait(1) -> CanAwait(0) -> Idle, while eight RequestNext credits remain.
    deliver(&mut running, &wire, roll_forward());
    let blocked = drive(&mut running, STEP_BUDGET);
    assert!(
        matches!(blocked, Blocked::Idle | Blocked::Sleeping { .. }),
        "precondition: first header settled; blocked={blocked:?}"
    );
    deliver(&mut running, &wire, roll_forward());
    let blocked = drive(&mut running, STEP_BUDGET);
    assert!(
        matches!(blocked, Blocked::Idle | Blocked::Sleeping { .. }),
        "precondition: second header settled; blocked={blocked:?} pipeline={:?}",
        running.get_state(&pipeline)
    );

    running.enqueue_msg(&connection, [ConnectionMessage::SetLocalUse(LocalUse::Maintenance)]);
    let blocked = drive(&mut running, STEP_BUDGET);
    let rolls_before_done = 2;
    let outstanding_at_done = outstanding_when_done(&wire, rolls_before_done);

    // The peer still owes the rest of the burst. Deliver one of those replies to whoever is
    // registered for chainsync now (the initiator, or the done trap if MsgDone already went out).
    let handler_before_late = handler_name(&wire);
    deliver(&mut running, &wire, roll_forward());
    let blocked_after_late = drive(&mut running, STEP_BUDGET);
    let connection_up = running.contains_stage(connection.name());

    assert!(
        outstanding_at_done.is_none_or(|outstanding| outstanding == 0) && connection_up,
        "MsgDone went out with outstanding pipelined replies and the honest connection was torn down: \
         outstanding_at_done={outstanding_at_done:?} connection_up={connection_up} \
         handler_before_late={handler_before_late} labels={:?} pipeline={:?} \
         after_lower={blocked:?} after_late={blocked_after_late:?}",
        chainsync_labels_of(&wire),
        running.get_state(&pipeline)
    );
}

fn outstanding_when_done(wire: &Mutex<Wire>, rolls_received: i32) -> Option<i32> {
    let payloads = &wire.lock().expect("wire").chainsync;
    let mut request_next = 0i32;
    for payload in payloads {
        for label in chainsync_labels(payload) {
            if label == LABEL_DONE {
                return Some(request_next - rolls_received);
            }
            if label == LABEL_REQUEST_NEXT {
                request_next += 1;
            }
        }
    }
    None
}

fn count_label(wire: &Mutex<Wire>, want: u16) -> i32 {
    chainsync_labels_of(wire).into_iter().filter(|label| *label == want).count() as i32
}

fn chainsync_labels_of(wire: &Mutex<Wire>) -> Vec<u16> {
    wire.lock().expect("wire").chainsync.iter().flat_map(|payload| chainsync_labels(payload)).collect()
}

fn handler_name(wire: &Mutex<Wire>) -> String {
    wire.lock()
        .expect("wire")
        .handlers
        .get(&PROTO_N2N_CHAIN_SYNC.erase())
        .map(|handler| handler.name().to_string())
        .unwrap_or_default()
}

fn deliver(running: &mut SimulationRunning, wire: &Mutex<Wire>, bytes: NonEmptyBytes) {
    let handler = wire
        .lock()
        .expect("wire")
        .handlers
        .get(&PROTO_N2N_CHAIN_SYNC.erase())
        .cloned()
        .expect("chainsync handler registered");
    running.enqueue_msg(&handler, [HandlerMessage::FromNetwork(bytes)]);
}

fn drive(running: &mut SimulationRunning, budget: usize) -> Blocked {
    running.breakpoint("early-done-step", |_| true);
    let mut steps = 0usize;
    let blocked = loop {
        if steps == budget {
            break Blocked::Busy { external_effects: 0, stages: Vec::new() };
        }
        steps += 1;
        match running.run(Run::default()) {
            Blocked::Breakpoint(_) => {}
            Blocked::Busy { .. } => {
                match running.run(Run { time: TimeAdvance::StopAtWakeup, externals: Externals::Resolve }) {
                    Blocked::Breakpoint(_) => {}
                    other @ (Blocked::Idle
                    | Blocked::Sleeping { .. }
                    | Blocked::Deadlock(_)
                    | Blocked::Busy { .. }
                    | Blocked::Terminated(_)) => break other,
                }
            }
            other @ (Blocked::Idle | Blocked::Sleeping { .. } | Blocked::Deadlock(_) | Blocked::Terminated(_)) => {
                break other;
            }
        }
    };
    running.clear_breakpoint("early-done-step");
    blocked
}

async fn peer_mux(wire: &Mutex<Wire>, msg: MuxMessage, eff: &Effects<MuxMessage>) {
    match msg {
        MuxMessage::Register { protocol, handler, .. } => {
            wire.lock().expect("wire").handlers.insert(protocol, handler.clone());
            eff.send(&handler, HandlerMessage::Registered(protocol)).await;
        }
        MuxMessage::Send(protocol, bytes, reply) => {
            if protocol == PROTO_N2N_CHAIN_SYNC.erase() {
                wire.lock().expect("wire").chainsync.push(bytes.as_ref().to_vec());
            }
            eff.send(&reply, Sent).await;
        }
        MuxMessage::WantNext(_)
        | MuxMessage::Buffer(_, _)
        | MuxMessage::FromNetwork(_, _, _)
        | MuxMessage::Written
        | MuxMessage::Terminate
        | MuxMessage::SetSduTimeout(_) => {}
    }
}

fn chainsync_labels(bytes: &[u8]) -> Vec<u16> {
    let mut decoder = cbor::Decoder::new(bytes);
    let mut labels = Vec::new();
    while decoder.position() < bytes.len() {
        let len = decoder.array().expect("chainsync item").expect("definite chainsync array");
        labels.push(decoder.u16().expect("chainsync label"));
        for _ in 1..len {
            decoder.skip().expect("chainsync field");
        }
    }
    labels
}

fn intersect_found() -> NonEmptyBytes {
    let mut buf = Vec::new();
    let mut encoder = cbor::Encoder::new(&mut buf);
    encoder.array(3).expect("array").u16(LABEL_INTERSECT_FOUND).expect("label");
    encoder.encode(NetworkPoint::Origin).expect("point");
    encoder.encode(NetworkTip::from(Point::Origin)).expect("tip");
    NonEmptyBytes::from_slice(&buf).expect("non-empty")
}

fn roll_forward() -> NonEmptyBytes {
    let mut buf = Vec::new();
    let mut encoder = cbor::Encoder::new(&mut buf);
    encoder.array(3).expect("array").u16(LABEL_ROLL_FORWARD).expect("label");
    encoder.array(2).expect("header").u8(EraName::Conway.header_variant()).expect("era");
    encoder.tag(cbor::IanaTag::Cbor).expect("tag").bytes(&[0x00]).expect("bytes");
    encoder.encode(NetworkTip::from(Point::Origin)).expect("tip");
    NonEmptyBytes::from_slice(&buf).expect("non-empty")
}
