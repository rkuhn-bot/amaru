#!/usr/bin/env python3
# Copyright 2026 PRAGMA
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Write the v5 wait graph and its discharge table.

The edge list is the classification of every production ``eff.send``, ``eff.call``,
``.send_any``, and typestate ``session.send`` under ``crates/``, tests excluded, plus
StageRefs carried in those messages and the submit API's ``Sender::call``. A call reply
and a mux ``Sent`` reply are oneshots (``tokio.rs:712-718``) and are recorded with
``blocking: false``.

``now`` / ``after`` on each discharge row is the judgement for that edge. ``after``
applies only the fix set named in the inventory.
"""

from __future__ import annotations

import json
from pathlib import Path

COMMIT = "33d62a6f1ccde08d77fbc202a2cfb888d0b3f7c6"

# (from, to, message, blocking, via, lines, note)
EDGES: list[tuple] = []


def E(frm, to, message, blocking, via, lines, note=""):
    EDGES.append((frm, to, message, blocking, via, lines, note))


PROTO = [
    "crates/amaru-protocols/src/protocol/miniprotocol.rs:228",
    "crates/amaru-protocols/src/protocol/miniprotocol.rs:232",
    "crates/amaru-protocols/src/protocol/miniprotocol.rs:274",
    "crates/amaru-protocols/src/protocol/miniprotocol.rs:278",
]
MUX_IN = [
    "crates/amaru-protocols/src/mux.rs:660",
    "crates/amaru-protocols/src/mux.rs:846",
    "crates/amaru-protocols/src/mux.rs:858",
]


def protocol(name, extra_out=(), extra_in=()):
    E(name, "mux", "WantNext/Send", True, "call", list(extra_out) + PROTO,
      "call parks the protocol until mux admits the request; the Sent reply is a oneshot")
    E("mux", name, "Registered/FromNetwork", True, "carried-ref", list(extra_in) + MUX_IN)


protocol("handshake")
protocol("chainsync_initiator")
protocol("chainsync_responder")
protocol("tx_submission_initiator")
protocol("tx_submission_responder")
protocol("keepalive_initiator")
protocol("keepalive_responder")
protocol("peer_sharing_initiator")
protocol("peer_sharing_responder")

E(
    "blockfetch_initiator", "mux", "WantNext/Send", True, "call",
    [
        "crates/amaru-protocols/src/blockfetch/initiator.rs:276",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:280",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:288",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:346",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:391",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:397",
    ],
)
E("mux", "blockfetch_initiator", "Registered/FromNetwork", True, "carried-ref", MUX_IN)
E(
    "blockfetch_responder", "mux", "WantNext/Send", True, "call",
    [
        "crates/amaru-protocols/src/blockfetch/responder.rs:231",
        "crates/amaru-protocols/src/blockfetch/responder.rs:238",
        "crates/amaru-protocols/src/blockfetch/responder.rs:244",
        "crates/amaru-protocols/src/blockfetch/responder.rs:252",
    ],
)
E("mux", "blockfetch_responder", "Registered/FromNetwork", True, "carried-ref", MUX_IN)
E("mux", "done_trap", "Registered/FromNetwork", True, "carried-ref", MUX_IN,
  "the trap does not send back; a later frame terminates it")

E(
    "mux", "mux_reader", "Read", True, "direct",
    ["crates/amaru-protocols/src/mux.rs:392", "crates/amaru-protocols/src/mux.rs:463"],
    "the reading flag keeps one Read outstanding",
)
E(
    "mux_reader", "mux", "FromNetwork", True, "direct",
    ["crates/amaru-protocols/src/mux.rs:573"],
)
E(
    "mux", "mux_writer", "OutgoingSdu", True, "direct",
    ["crates/amaru-protocols/src/mux.rs:449", "crates/amaru-protocols/src/mux.rs:474"],
    "the sending flag keeps one OutgoingSdu outstanding",
)
E("mux_writer", "mux", "Written", True, "direct", ["crates/amaru-protocols/src/mux.rs:382"])
E(
    "mux", "handshake", "Sent", False, "oneshot",
    ["crates/amaru-protocols/src/mux.rs:881"],
    "representative oneshot; every protocol's Sent reply takes this path",
)

E(
    "handshake", "connection", "HandshakeResult", True, "direct",
    [
        "crates/amaru-protocols/src/handshake/initiator.rs:92",
        "crates/amaru-protocols/src/handshake/initiator.rs:98",
        "crates/amaru-protocols/src/handshake/initiator.rs:107",
        "crates/amaru-protocols/src/handshake/responder.rs:82",
    ],
)
E(
    "connection", "mux", "Register/SetSduTimeout", True, "direct",
    [
        "crates/amaru-protocols/src/connection.rs:403",
        "crates/amaru-protocols/src/connection.rs:471",
        "crates/amaru-protocols/src/chainsync/mod.rs:67",
        "crates/amaru-protocols/src/chainsync/mod.rs:91",
        "crates/amaru-protocols/src/tx_submission/mod.rs:118",
        "crates/amaru-protocols/src/keepalive/mod.rs:93",
        "crates/amaru-protocols/src/peer_sharing/mod.rs:109",
        "crates/amaru-protocols/src/peer_sharing/responder.rs:67",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:465",
        "crates/amaru-protocols/src/blockfetch/responder.rs:304",
        "crates/amaru-protocols/src/mux.rs:275",
    ],
)
E(
    "connection", "chainsync_initiator", "Done", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:594"],
)
E(
    "connection", "chainsync_responder", "NewTip", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:258"],
    "the responder keeps only the latest upstream tip; the send is still blocking and the fix set adds no cell",
)
E(
    "connection", "blockfetch_initiator", "RequestRange/Close", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:252", "crates/amaru-protocols/src/connection.rs:598"],
)
E(
    "connection", "tx_submission_initiator", "Close", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:602"],
)
E(
    "connection", "keepalive_initiator", "Close", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:608"],
)
E(
    "connection", "peer_sharing_initiator", "Close", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:612"],
)
E(
    "connection", "track_peers", "Terminated", True, "direct",
    ["crates/amaru-protocols/src/connection.rs:320"],
)
E(
    "connection", "manager", "HandshakeComplete", True, "call",
    ["crates/amaru-protocols/src/connection.rs:454"],
)
E(
    "manager", "connection", "Initialize/Disconnect/FetchBlocks/NewTip/SetLocalUse", True, "direct",
    [
        "crates/amaru-protocols/src/manager/mod.rs:498",
        "crates/amaru-protocols/src/manager/mod.rs:604",
        "crates/amaru-protocols/src/manager/mod.rs:626",
        "crates/amaru-protocols/src/manager/mod.rs:776",
        "crates/amaru-protocols/src/manager/mod.rs:789",
        "crates/amaru-protocols/src/manager/mod.rs:844",
        "crates/amaru-protocols/src/manager/mod.rs:866",
        "crates/amaru-protocols/src/manager/mod.rs:888",
        "crates/amaru-protocols/src/manager/mod.rs:946",
    ],
)
E(
    "manager", "connection", "HandshakeComplete reply", False, "oneshot",
    ["crates/amaru-protocols/src/manager/mod.rs:519", "crates/amaru-protocols/src/manager/mod.rs:560"],
)

E(
    "chainsync_initiator", "track_peers", "ChainSyncInitiatorMsg", True, "direct",
    ["crates/amaru-protocols/src/chainsync/initiator.rs:169"],
)
E(
    "track_peers", "chainsync_initiator", "RequestNext/Done", True, "carried-ref",
    [
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:877",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:911",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:931",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1015",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1049",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1063",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1069",
    ],
)

E(
    "tx_submission_initiator", "mempool", "WaitForAtLeast", True, "direct",
    [
        "crates/amaru-protocols/src/tx_submission/initiator.rs:107",
        "crates/amaru-protocols/src/tx_submission/initiator.rs:365",
    ],
)
E(
    "mempool", "tx_submission_initiator", "WaitForAtLeastReached", True, "carried-ref",
    [
        "crates/amaru-consensus/src/stages/mempool/stage.rs:70",
        "crates/amaru-consensus/src/stages/mempool/stage.rs:187",
    ],
    "caller is the initiator me_ref contramap; the send parks the mempool on the initiator mailbox",
)
E(
    "tx_submission_responder", "mempool", "InsertBatch", True, "call",
    ["crates/amaru-protocols/src/tx_submission/responder.rs:608"],
)
E(
    "tx_submission_responder", "mempool", "SubscribeCapacity", True, "direct",
    ["crates/amaru-protocols/src/tx_submission/responder.rs:692"],
)
E(
    "mempool", "tx_submission_responder", "CapacityAvailable", True, "carried-ref",
    ["crates/amaru-consensus/src/stages/mempool/stage.rs:195"],
)
E(
    "mempool", "tx_submission_responder", "InsertBatch reply", False, "oneshot",
    ["crates/amaru-consensus/src/stages/mempool/stage.rs:99"],
)
E(
    "submit_api", "mempool", "Insert", True, "call",
    ["crates/amaru-node/src/submit_api.rs:85"],
    "HTTP handler, not a stage; Sender::call parks until admission and the oneshot reply",
)
E(
    "mempool", "submit_api", "Insert reply", False, "oneshot",
    ["crates/amaru-consensus/src/stages/mempool/stage.rs:85"],
)

E(
    "blockfetch_initiator", "cleanup_replies", "Block/NoBlocks/Done", True, "send_any",
    [
        "crates/amaru-protocols/src/blockfetch/initiator.rs:312",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:348",
        "crates/amaru-protocols/src/blockfetch/initiator.rs:364",
    ],
)

E("track_peers", "select_chain", "NewTip", True, "direct",
  ["crates/amaru-consensus/src/stages/track_peers/mod.rs:868"])
E(
    "forge_block", "select_chain", "TipFromUpstream", True, "direct",
    ["crates/amaru-consensus/src/stages/forge_block/protocol.rs:455"],
    "present when forging credentials are configured",
)
E(
    "select_chain", "fetch_blocks", "NewBestTip", True, "direct",
    [
        "crates/amaru-consensus/src/stages/select_chain/mod.rs:305",
        "crates/amaru-consensus/src/stages/select_chain/mod.rs:400",
        "crates/amaru-consensus/src/stages/select_chain/mod.rs:478",
    ],
)
E(
    "fetch_blocks", "select_chain", "FetchNextFrom", True, "direct",
    [
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:396",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:407",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:652",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:750",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:758",
    ],
)
E(
    "validate_block", "select_chain", "BlockValidationResult", True, "direct",
    [
        "crates/amaru-consensus/src/stages/validate_block/mod.rs:111",
        "crates/amaru-consensus/src/stages/validate_block/mod.rs:142",
    ],
)
E(
    "fetch_blocks", "validate_block", "DownloadedBlock", True, "direct",
    [
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:310",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:395",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:641",
    ],
)
E(
    "validate_block", "adopt_chain", "AdoptChain", True, "direct",
    ["crates/amaru-consensus/src/stages/validate_block/mod.rs:119"],
)
E(
    "validate_block", "block_source", "Validation", True, "direct",
    [
        "crates/amaru-consensus/src/stages/validate_block/mod.rs:117",
        "crates/amaru-consensus/src/stages/validate_block/mod.rs:149",
    ],
)
E("adopt_chain", "manager", "NewTip", True, "direct",
  ["crates/amaru-consensus/src/stages/adopt_chain/mod.rs:266"])
E("adopt_chain", "block_source", "AdoptedTip", True, "direct",
  ["crates/amaru-consensus/src/stages/adopt_chain/mod.rs:268"])
E("adopt_chain", "mempool", "NewTip", True, "direct",
  ["crates/amaru-consensus/src/stages/adopt_chain/mod.rs:264"])
E("adopt_chain", "forge_block", "AdoptedTip", True, "direct",
  ["crates/amaru-consensus/src/stages/adopt_chain/mod.rs:274"])

E(
    "fetch_blocks", "manager", "FetchBlocks", True, "direct",
    [
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:440",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:544",
    ],
)
E("fetch_blocks", "peer_selection", "Adversarial", True, "direct",
  ["crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:574"])
E(
    "manager", "cleanup_replies", "PeersAsked/NoPeersAvailable", True, "carried-ref",
    ["crates/amaru-protocols/src/manager/mod.rs:795", "crates/amaru-protocols/src/manager/mod.rs:798"],
)
E(
    "cleanup_replies", "fetch_blocks", "Block/NoBlocks/PeersAsked/NoPeersAvailable", True, "direct",
    [
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:855",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:859",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:863",
        "crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:877",
    ],
)
E("cleanup_replies", "block_source", "BlockReceived", True, "direct",
  ["crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:875"])
E("cleanup_replies", "peer_selection", "Adversarial", True, "direct",
  ["crates/amaru-consensus/src/stages/fetch_blocks/mod.rs:871"])
E(
    "block_source", "peer_selection", "Adversarial", True, "direct",
    [
        "crates/amaru-consensus/src/stages/block_source/mod.rs:128",
        "crates/amaru-consensus/src/stages/block_source/mod.rs:152",
    ],
)
E(
    "track_peers", "peer_selection", "Adversarial", True, "direct",
    [
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:786",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:960",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1071",
    ],
)
E(
    "peer_selection", "manager", "AddPeer/RemovePeer/Disconnect/SetLocalUse", True, "direct",
    [
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:339",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:359",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:466",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:504",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:782",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:894",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:945",
        "crates/amaru-consensus/src/stages/peer_selection/mod.rs:1219",
    ],
)
E(
    "peer_selection", "peer_selection", "Resolved", True, "direct",
    ["crates/amaru-consensus/src/stages/peer_selection/mod.rs:664"],
)
E(
    "peer_selection", "ledger_check", "()", True, "direct",
    ["crates/amaru-consensus/src/stages/peer_selection/mod.rs:1203"],
    "the child writes the performance resource and reschedules itself; it sends nothing back",
)

E("manager", "connector", "Connect", True, "direct", ["crates/amaru-protocols/src/manager/mod.rs:359"])
E("connector", "manager", "ConnectionResult", True, "direct",
  ["crates/amaru-protocols/src/manager/connector.rs:101"])
E(
    "connector", "connect_worker", "ConnectJob", True, "direct",
    ["crates/amaru-protocols/src/manager/connector.rs:74", "crates/amaru-protocols/src/manager/connector.rs:81"],
)
E("connect_worker", "connector", "WorkerDone", True, "direct",
  ["crates/amaru-protocols/src/manager/connector.rs:124"])
E("manager", "accept", "PullAccept", True, "direct", ["crates/amaru-protocols/src/manager/mod.rs:442"])
E("accept", "manager", "Accepted", True, "direct", ["crates/amaru-protocols/src/accept.rs:29"])

E(
    "ledger", "track_peers", "StakeDistUpdated", True, "direct",
    ["crates/amaru-ledger/src/state.rs:1288", "crates/amaru-node/src/stages/build_node.rs:504"],
)
E(
    "track_peers", "ledger", "VolatileTipEffect", True, "effect",
    [
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:993",
        "crates/amaru-consensus/src/stages/track_peers/mod.rs:1086",
    ],
    "epoch_transition joins the rewards thread while that thread is blocked in the callback",
)

# Discharge rows: (lemma, w, capacity, location, now, after) keyed by (from, to, message)
ROWS: dict[tuple, tuple] = {}


def R(frm, to, message, lemma, w, capacity, location, now, after):
    ROWS[(frm, to, message)] = (lemma, w, capacity, location, now, after)


CAP_MUX = "mux bulk 24"
CAP_DEF = "bulk 10 (child of a stage whose Effects.mailbox_size is the graph default)"
CAP_CS = "chainsync initiator bulk 14"
CAP_BF = "blockfetch initiator bulk max(10, 2n+4); n=2 is 10"
CAP_CONN = "connection bulk 10"
CAP_MGR = "manager bulk 10+max_outbound+max_inbound (23)"
CAP_PS = "peer_selection bulk 23"
CAP_TP = "track_peers bulk 10"
CAP_MP = "mempool bulk 10"
CAP_SC = "select_chain bulk 10"
CAP_FB = "fetch_blocks bulk 10"
CAP_CL = "cleanup_replies bulk 10"
CAP_CON = "connector bulk 10"

for name in (
    "handshake", "chainsync_responder", "tx_submission_initiator", "tx_submission_responder",
    "keepalive_initiator", "keepalive_responder", "peer_sharing_initiator", "peer_sharing_responder",
    "blockfetch_responder",
):
    R(name, "mux", "WantNext/Send", "L1",
      "one protocol's pipelined sends, sharing the mux with every other protocol on the connection and with reader/writer",
      CAP_MUX, "miniprotocol.rs:274,278", "blocking", "blocking")
    R("mux", name, "Registered/FromNetwork", "L1",
      "one registered frame plus the bodies the protocol asked for; no fix caps this mailbox at 10",
      CAP_DEF, "mux.rs:660,846,858", "blocking", "blocking")

R("chainsync_initiator", "mux", "WantNext/Send", "L1",
  "shares the mux mailbox; the credit bounds the initiator, not the mux",
  CAP_MUX, "miniprotocol.rs:274,278", "blocking", "blocking")
R("mux", "chainsync_initiator", "Registered/FromNetwork", "L1",
  "inside the joint sum R+F+Dones <= 13",
  CAP_CS, "mux.rs:660,846,858; initiator.rs:316,323", "blocking", "discharged")
R("track_peers", "chainsync_initiator", "RequestNext/Done", "L1",
  "credit caps RequestNext at 10 and Done-once caps this Done at 1; joint sum <= 13",
  CAP_CS, "track_peers/mod.rs:877,911,931,1015,1049,1063,1069", "blocking", "discharged")
R("connection", "chainsync_initiator", "Done", "L1",
  "connection Done <= 1; joint sum <= 13",
  CAP_CS, "connection.rs:594", "blocking", "discharged")
R("chainsync_initiator", "track_peers", "ChainSyncInitiatorMsg", "L1",
  "one result in flight per initiator, W <= N_max = 13 > 10",
  CAP_TP, "chainsync/initiator.rs:169", "blocking", "blocking")

R("blockfetch_initiator", "mux", "WantNext/Send", "L1",
  "shares the mux; B5 bounds the initiator mailbox, not the mux",
  CAP_MUX, "blockfetch/initiator.rs:276,288,346", "blocking", "blocking")
R("mux", "blockfetch_initiator", "Registered/FromNetwork", "L1",
  "B5 makes the pending range a cell and the initiator bulk sum 4 <= 10",
  CAP_BF, "mux.rs:660,846,858", "blocking", "discharged")
R("connection", "blockfetch_initiator", "RequestRange/Close", "L1",
  "B5; the same sum 4 <= 10",
  CAP_BF, "connection.rs:252,598", "blocking", "discharged")
R("blockfetch_initiator", "cleanup_replies", "Block/NoBlocks/Done", "L1",
  "remaining starts at MAX_FETCHED_BLOCKS=1000 per request; B6 filters the far side, not this send",
  CAP_CL, "blockfetch/initiator.rs:275,312,348,364,396", "blocking", "blocking")

R("connection", "chainsync_responder", "NewTip", "L2",
  "the responder stores one upstream tip, so the value is superseding, and the fix set adds no cell. One per adopted block, unbounded, mailbox 10",
  CAP_DEF, "connection.rs:258; chainsync/responder.rs:85-92", "blocking", "blocking")

R("mux", "done_trap", "Registered/FromNetwork", "L1",
  "a peer can keep sending after MsgDone until the trap terminates; not shown <= 10",
  CAP_DEF, "mux.rs:250-261,660", "blocking", "blocking")
R("mux", "mux_reader", "Read", "L1", "one outstanding Read, sole producer, W=1 <= 10",
  CAP_DEF, "mux.rs:392,463", "discharged", "discharged")
R("mux_reader", "mux", "FromNetwork", "L1", "one reader shares the mux mailbox of 24 with every protocol",
  CAP_MUX, "mux.rs:573", "blocking", "blocking")
R("mux", "mux_writer", "OutgoingSdu", "L1", "one outstanding segment, sole producer, W=1 <= 10",
  CAP_DEF, "mux.rs:449,474", "discharged", "discharged")
R("mux_writer", "mux", "Written", "L1", "one writer shares the mux mailbox",
  CAP_MUX, "mux.rs:382", "blocking", "blocking")
R("connection", "mux", "Register/SetSduTimeout", "L1",
  "one register per protocol direction plus one timeout update, on top of the protocol sends; sum not <= 24",
  CAP_MUX, "connection.rs:403,471", "blocking", "blocking")
R("handshake", "connection", "HandshakeResult", "L1",
  "B3: SetLocalUse, NewTip and FetchBlocks are cells and the connection bulk sum is 6 <= 10",
  CAP_CONN, "handshake/initiator.rs:92,98,107; handshake/responder.rs:82", "blocking", "discharged")

R("connection", "tx_submission_initiator", "Close", "L1",
  "Close is one, and the mailbox still receives FromNetwork with no credit in the fix set",
  CAP_DEF, "connection.rs:602", "blocking", "blocking")
R("connection", "keepalive_initiator", "Close", "L1",
  "Close is one; FromNetwork shares the mailbox and no fix bounds it",
  CAP_DEF, "connection.rs:608", "blocking", "blocking")
R("connection", "peer_sharing_initiator", "Close", "L1",
  "Close is one; FromNetwork shares the mailbox and no fix bounds it",
  CAP_DEF, "connection.rs:612", "blocking", "blocking")
R("connection", "track_peers", "Terminated", "L1",
  "one per teardown, sharing track_peers with one header result per initiator. N_max=13 > 10",
  CAP_TP, "connection.rs:320", "blocking", "blocking")
R("connection", "manager", "HandshakeComplete", "L1",
  "one call per handshake, <= N_max after the accept cap. Manager sum after B2 is 4*N_max+2*max_outbound+4 = 62 > 23",
  CAP_MGR, "connection.rs:454", "blocking", "blocking")
R("manager", "connection", "Initialize/Disconnect/FetchBlocks/NewTip/SetLocalUse", "L1",
  "B3 cells for FetchBlocks, NewTip, SetLocalUse. With Initialize, Disconnect and HandshakeResult the bulk sum is 6 <= 10",
  CAP_CONN, "manager/mod.rs:498,776,866,888,946", "blocking", "discharged")

R("tx_submission_initiator", "mempool", "WaitForAtLeast", "L2",
  "replaced by a monotone sequence cell; the send is deleted",
  CAP_MP, "tx_submission/initiator.rs:107,365", "blocking", "discharged")
R("mempool", "tx_submission_initiator", "WaitForAtLeastReached", "L2",
  "the notification is the same cell; the blocking send at stage.rs:70 and :187 is deleted",
  CAP_DEF, "mempool/stage.rs:70,187", "blocking", "discharged")
R("tx_submission_responder", "mempool", "InsertBatch", "L1",
  "one parked call per inbound responder, so <= max_inbound. With submit's L and one NewTip the sum is max_inbound+L+1 >= 11 > 10",
  CAP_MP, "tx_submission/responder.rs:608", "blocking", "blocking")
R("tx_submission_responder", "mempool", "SubscribeCapacity", "L2",
  "B4 deletes the subscription; capacity is a cell",
  CAP_MP, "tx_submission/responder.rs:692", "blocking", "discharged")
R("mempool", "tx_submission_responder", "CapacityAvailable", "L2",
  "B4 deletes the notification",
  CAP_DEF, "mempool/stage.rs:195", "blocking", "discharged")
R("submit_api", "mempool", "Insert", "L1",
  "L is the number of HTTP calls in flight. The server does not cap it. Counted in max_inbound+L+1 > 10",
  CAP_MP, "submit_api.rs:85", "blocking", "blocking")
R("adopt_chain", "mempool", "NewTip", "L1",
  "the +1 in max_inbound+L+1. The sum exceeds 10, so the send still blocks",
  CAP_MP, "adopt_chain/mod.rs:264", "blocking", "blocking")

R("track_peers", "select_chain", "NewTip", "L1",
  "one per accepted header, unbounded, sharing the mailbox with forge, validation and FetchNextFrom",
  CAP_SC, "track_peers/mod.rs:868", "blocking", "blocking")
R("forge_block", "select_chain", "TipFromUpstream", "L1",
  "one per forged block. The anchor cell is a store read, not this edge",
  CAP_SC, "forge_block/protocol.rs:455", "blocking", "blocking")
R("select_chain", "fetch_blocks", "NewBestTip", "L4",
  "may_fetch_blocks is cleared before the send. The token still discharges the edge; BoundaryNotFound stalls rather than overlapping the two sends",
  CAP_FB, "select_chain/mod.rs:302-305,443,478", "discharged", "discharged")
R("fetch_blocks", "select_chain", "FetchNextFrom", "L1",
  "one in flight from this stage; the mailbox sum is not <= 10",
  CAP_SC, "fetch_blocks/mod.rs:758", "blocking", "blocking")
R("validate_block", "select_chain", "BlockValidationResult", "L1",
  "one per validated block into the same shared mailbox",
  CAP_SC, "validate_block/mod.rs:111,142", "blocking", "blocking")
R("fetch_blocks", "validate_block", "DownloadedBlock", "L1",
  "a batch is 25 and a replay sends the stored prefix; both exceed 10",
  "validate_block bulk 10", "fetch_blocks/mod.rs:310,395,641", "blocking", "blocking")
R("validate_block", "adopt_chain", "AdoptChain", "L1", "one per valid block; no credit",
  "adopt_chain bulk 10", "validate_block/mod.rs:119", "blocking", "blocking")
R("validate_block", "block_source", "Validation", "L1", "one per validated block; no credit",
  "block_source bulk 10", "validate_block/mod.rs:117,149", "blocking", "blocking")
R("adopt_chain", "manager", "NewTip", "L2",
  "B2 makes this a cell (W=1) but the manager sum is 4*N_max+2*max_outbound+4 = 62 > 23",
  CAP_MGR, "adopt_chain/mod.rs:266", "blocking", "blocking")
R("adopt_chain", "block_source", "AdoptedTip", "L2",
  "one stored tip, and the send stays blocking into a mailbox shared with BlockReceived. No cell in the fix set",
  "block_source bulk 10", "adopt_chain/mod.rs:268", "blocking", "blocking")
R("adopt_chain", "forge_block", "AdoptedTip", "L1",
  "one per adopted block; forge's mailbox is 10 and the fix set adds no credit",
  "forge_block bulk 10", "adopt_chain/mod.rs:274", "blocking", "blocking")
R("fetch_blocks", "manager", "FetchBlocks", "L2",
  "B2 cell (W=1); manager sum 62 > 23",
  CAP_MGR, "fetch_blocks/mod.rs:440,544", "blocking", "blocking")
R("manager", "cleanup_replies", "PeersAsked/NoPeersAvailable", "L1",
  "one of the two per finished FetchBlocks, sharing cleanup with up to 1000 bodies per peer",
  CAP_CL, "manager/mod.rs:795,798", "blocking", "blocking")
R("cleanup_replies", "fetch_blocks", "Block/NoBlocks/PeersAsked/NoPeersAvailable", "L1",
  "B6 keeps a hash only when it is in missing and not yet forwarded. That bound is 67 > 10",
  CAP_FB, "fetch_blocks/mod.rs:855-877", "blocking", "blocking")
R("cleanup_replies", "block_source", "BlockReceived", "L1",
  "sent for every decoded body before the id filter; up to 1000 per peer",
  "block_source bulk 10", "fetch_blocks/mod.rs:875", "blocking", "blocking")
R("fetch_blocks", "peer_selection", "Adversarial", "L1",
  "B1 dedups per conn_id, so every Adversarial site together is <= N_max. With Resolved <= max_outbound and one Initialize, 13+3+1=17 <= 23",
  CAP_PS, "fetch_blocks/mod.rs:574", "blocking", "discharged")
R("cleanup_replies", "peer_selection", "Adversarial", "L1", "inside the same 17 <= 23",
  CAP_PS, "fetch_blocks/mod.rs:871", "blocking", "discharged")
R("block_source", "peer_selection", "Adversarial", "L1", "inside the same 17 <= 23",
  CAP_PS, "block_source/mod.rs:128,152", "blocking", "discharged")
R("track_peers", "peer_selection", "Adversarial", "L1", "inside the same 17 <= 23",
  CAP_PS, "track_peers/mod.rs:786,960,1071", "blocking", "discharged")
R("peer_selection", "peer_selection", "Resolved", "L1",
  "W <= max_outbound on its own, and the mailbox sum is 17 <= 23 after B1",
  CAP_PS, "peer_selection/mod.rs:664", "blocking", "discharged")
R("peer_selection", "ledger_check", "()", "L1",
  "one bulk message; later wakes are priority self-schedules. W=1 <= 10",
  CAP_DEF, "peer_selection/mod.rs:1203,1304", "discharged", "discharged")
R("peer_selection", "manager", "AddPeer/RemovePeer/Disconnect/SetLocalUse", "L1",
  "B2 turns SetLocalUse into a cell. AddPeer <= max_outbound, RemovePeer and Disconnect <= N_max. They sit in the manager sum of 62 > 23",
  CAP_MGR, "peer_selection/mod.rs:339,359,782,945", "blocking", "blocking")

R("manager", "connector", "Connect", "L1",
  "W <= max_outbound, plus WorkerDone <= 10. 3+10 > connector mailbox 10",
  CAP_CON, "manager/mod.rs:359; connector.rs:32", "blocking", "blocking")
R("connector", "manager", "ConnectionResult", "L1",
  "W <= max_outbound and it shares the manager sum of 62",
  CAP_MGR, "connector.rs:101", "blocking", "blocking")
R("connector", "connect_worker", "ConnectJob", "L1", "one job until WorkerDone, W=1 <= 10",
  "connect_worker bulk 10", "connector.rs:72-81", "discharged", "discharged")
R("connect_worker", "connector", "WorkerDone", "L1", "<= 10 in flight, plus Connect <= 3, sum 13 > 10",
  CAP_CON, "connector.rs:124", "blocking", "blocking")
R("manager", "accept", "PullAccept", "L1", "one bulk pull, W=1 <= 10",
  "accept bulk 10", "manager/mod.rs:442", "discharged", "discharged")
R("accept", "manager", "Accepted", "L1",
  "unbounded now. After the cap at accept, <= N_max, inside the manager sum of 62 > 23",
  CAP_MGR, "accept.rs:29", "blocking", "blocking")

R("ledger", "track_peers", "StakeDistUpdated", "L1",
  "blocking send from the rewards thread. The fix set does not replace it",
  CAP_TP, "state.rs:1288; build_node.rs:504", "blocking", "blocking")
R("track_peers", "ledger", "VolatileTipEffect", "L1",
  "completion waits on the ledger thread, which joins that callback. The fix set does not remove the send",
  "ledger request queue 16", "state.rs:418; track_peers/mod.rs:993,1086", "blocking", "blocking")


# Fields added after checking the code: w_formula, capacity_formula, at_defaults, verified.
# verified false forces after=blocking. The checker does not read these fields.
VERIFY: dict[tuple, dict] = {}


def V(frm, to, message, **fields):
    VERIFY[(frm, to, message)] = fields


# Reader and writer. `sending` and the Read/FromNetwork alternation are in the code.
V("mux", "mux_reader", "Read", verified=True, lemma_checked="L1",
  w_formula="1", capacity_formula="10", at_defaults=10,
  check="init sends one Read (mux.rs:392); the next Read is sent only from the FromNetwork arm (mux.rs:463)")
V("mux", "mux_writer", "OutgoingSdu", verified=True, lemma_checked="L1",
  w_formula="1", capacity_formula="10", at_defaults=10,
  check="sending is set around the only two OutgoingSdu sends (mux.rs:446-449 and 469-474) and cleared on Written")

# Manager. The production mailbox is 10+upstream+downstream = 23, not the formula and not 460.
for _edge in (
    ("connection", "manager", "HandshakeComplete"),
    ("adopt_chain", "manager", "NewTip"),
    ("fetch_blocks", "manager", "FetchBlocks"),
    ("peer_selection", "manager", "AddPeer/RemovePeer/Disconnect/SetLocalUse"),
    ("connector", "manager", "ConnectionResult"),
    ("accept", "manager", "Accepted"),
):
    V(*_edge, verified=False, lemma_checked="L1",
      w_formula="4*N_max+2*max_outbound+4",
      capacity_formula="DEFAULT_MAILBOX_SIZE+target_upstream_peers+target_downstream_peers",
      at_defaults="formula 62, mailbox 23",
      check=(
          "mailbox is build_stage_graph.rs:71-72. ConnectionResult is bounded by "
          "DEFAULT_PARALLEL_CONNECTION=10 (connector.rs:32,86), not max_outbound. "
          "Accepted is capped only inside handshake_complete (manager/mod.rs:537-552), "
          "after accept.rs:29 has already queued it. RemovePeer (peer_selection/mod.rs:339) "
          "is sent on every ban, including after cooldown. The three cells are not in the code."
      ))

# Mux to handler. Sent is a oneshot, wanted is not reset on re-register, timeout drops the credit.
for _name in (
    "handshake", "chainsync_responder", "tx_submission_initiator", "tx_submission_responder",
    "keepalive_initiator", "keepalive_responder", "peer_sharing_initiator", "peer_sharing_responder",
    "blockfetch_responder",
):
    V("mux", _name, "Registered/FromNetwork", verified=False, lemma_checked="L1",
      w_formula="1+p_h+s_h+local", capacity_formula="10", at_defaults="not ≤ 10",
      check=(
          "Sent at mux.rs:881 is a oneshot (tokio.rs:712-718), so it is not a handler-mailbox slot. "
          "want_next increments unconditionally (mux.rs:854-861). do_register's Occupied arm "
          "(mux.rs:694-700) keeps wanted and the buffer. install_done_trap and a later "
          "start_initiators both Register the same protocol id (connection.rs:638-688, 736-774). "
          "A late frame is delivered to the trap, which terminates (mux.rs:252-261). "
          "eff.call discards a timeout and the Send stays queued (miniprotocol.rs:232-235; "
          "blockfetch/responder.rs:238)."
      ))


def main() -> None:
    missing = []
    rows = []
    edges = []
    for frm, to, message, blocking, via, lines, note in EDGES:
        edges.append({
            "from": frm, "to": to, "message": message, "blocking": blocking,
            "via": via, "lines": lines, "note": note,
        })
        if not blocking:
            continue
        key = (frm, to, message)
        if key not in ROWS:
            missing.append(key)
            continue
        lemma, w, capacity, location, now, after = ROWS[key]
        row = {
            "edge": f"{frm} -> {to} [{message}]",
            "from": frm, "to": to, "message": message,
            "lemma": lemma, "w": w, "capacity": capacity, "location": location,
            "now": now, "after": after,
        }
        extra = VERIFY.get((frm, to, message))
        if extra:
            row.update(extra)
            # A failed check stays blocking. Do not promote it.
            if extra.get("verified") is False:
                row["after"] = "blocking"
        rows.append(row)
    extra = [key for key in ROWS if not any(e[0] == key[0] and e[1] == key[1] and e[2] == key[2] and e[3] for e in EDGES)]
    if missing or extra:
        raise SystemExit(f"missing {missing} extra {extra}")
    graph = {
        "commit": COMMIT,
        "note": (
            "Every production stage send, call, and send_any on 33d62a6f, plus StageRefs carried "
            "in those messages and the submit API. blocking false is a oneshot reply. "
            "Per-connection protocols are one node each; N copies share that shape. "
            "A child spawned with eff.stage inherits Effects.mailbox_size, which for manager's "
            "children is the graph default 10, while manager's own mailbox is 10+U+D."
        ),
        "excluded": [
            {"name": "mithril_block_source", "reason": "built by the mithril sync path, not by build_node"},
            {"name": "pure-stage test stages", "reason": "tests and simulations are not in the node graph"},
            {"name": "FindBestCandidate / store anchor read", "reason": "an external effect on the chain store, not a stage send; the anchor cell therefore deletes no edge"},
        ],
        "capacities": {
            "graph_default_bulk": 10,
            "manager_and_peer_selection": "10+max_outbound+max_inbound = 23",
            "connection_and_its_default_children": 10,
            "mux": 24,
            "chainsync_initiator": 14,
            "blockfetch_initiator": "max(10, 2n+4)",
            "N_max": "max_inbound+max_outbound = 13 at defaults",
            "manager_after_B2": "4*N_max+2*max_outbound+4 = 62",
            "connection_after_B3": 6,
            "mempool_after_B4": "max_inbound+L+1",
            "blockfetch_initiator_after_B5": 4,
            "cleanup_filter_B6": 67,
            "peer_selection_after_B1": 17,
        },
        "edges": edges,
    }
    table = {
        "commit": COMMIT,
        "note": (
            "now is 33d62a6f. after applies B1 dedup per conn_id, B2 cells for SetLocalUse/NewTip/"
            "FetchBlocks into manager, B3 the same cells per connection, B4 delete capacity "
            "subscription, B5 blockfetch pending-range cell, B6 cleanup filter, plus the "
            "WaitForAtLeast sequence cell, the select_chain anchor cell, the fetch-permission "
            "token, RequestNext credit with Done-once, and the cap at accept. A cell or a "
            "deleted send is discharged. A cell whose mailbox sum still exceeds capacity stays blocking."
        ),
        "columns": ["edge", "lemma", "w", "capacity", "location", "now", "after", "w_formula", "capacity_formula", "at_defaults", "verified"],
        "verification": (
            "Rows with verified=false stay blocking in after. The manager mailbox in this tree is "
            "10+target_upstream_peers+target_downstream_peers (23 at the defaults of 3 and 10), "
            "from build_stage_graph.rs:71-72. No production path sizes it to 460."
        ),
        "rows": rows,
    }
    out = Path("scripts")
    (out / "wait-graph-v5.json").write_text(json.dumps(graph, indent=2) + "\n")
    (out / "wait-graph-v5-discharge.json").write_text(json.dumps(table, indent=2) + "\n")
    print(f"edges {len(edges)} blocking {sum(e['blocking'] for e in edges)} rows {len(rows)}")
    print("now discharged", sum(r["now"] == "discharged" for r in rows))
    print("after discharged", sum(r["after"] == "discharged" for r in rows))
    print("after still blocking", sum(r["after"] == "blocking" for r in rows))


if __name__ == "__main__":
    main()
