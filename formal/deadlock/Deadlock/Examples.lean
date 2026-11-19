import Deadlock.Graph

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Deadlock

def tpl (name : String) (cap : Nat) (states : List String) (initial : String) (mustFit : Bool) : Template where
  name := name
  multiplicity := .one
  capacity := .ofNat cap
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 1
  states := states
  initial := initial
  terminable := false
  untimedPeer := false
  mustFit := mustFit

def sendEdge (src ss dst label : String) (occ : Nat) : Edge where
  src := src
  srcState := ss
  dst := dst
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := label
  scope := .intra
  occupancy := .ofNat occ
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

def safeDesc : Description where
  name := "safe"
  freshNames := true
  templates := [tpl "source" 10 ["idle"] "idle" true, tpl "sink" 10 ["idle"] "idle" true]
  edges := [sendEdge "source" "idle" "sink" "Ping" 1]
  compatibility := .all
  steps := []

def managerPeerDesc : Description where
  name := "manager-peer"
  freshNames := true
  templates := [tpl "manager" 10 ["idle"] "idle" false, tpl "peer_selection" 10 ["idle"] "idle" false]
  edges :=
    [sendEdge "manager" "idle" "peer_selection" "ConnectionEvent" 11,
     sendEdge "peer_selection" "idle" "manager" "AddPeer" 11]
  compatibility := .all
  steps := []

def creditDesc : Description where
  name := "credit"
  freshNames := true
  templates := [tpl "client" 1 ["idle"] "idle" true, tpl "server" 1 ["idle"] "idle" true]
  edges :=
    [sendEdge "client" "idle" "server" "Request" 1,
     sendEdge "server" "idle" "client" "Response" 1]
  compatibility := .all
  steps := []

def tokenTemplates : List Template :=
  [tpl "select_chain" 10 ["idle", "holding"] "idle" false,
   tpl "fetch_blocks" 10 ["idle", "busy"] "idle" false]

def tokenEdges : List Edge :=
  [sendEdge "select_chain" "holding" "fetch_blocks" "NewBestTip" 11,
   sendEdge "fetch_blocks" "busy" "select_chain" "ReturnToken" 11]

def tokenAllowed : List Allowed :=
  [{ src := "select_chain", srcState := "holding", dst := "fetch_blocks", dstState := "idle" },
   { src := "fetch_blocks", srcState := "busy", dst := "select_chain", dstState := "idle" }]

def tokenDesc : Description where
  name := "token-pair"
  freshNames := true
  templates := tokenTemplates
  edges := tokenEdges
  compatibility := .explicit tokenAllowed
  steps := []

def tokenUngatedDesc : Description where
  name := "token-pair-ungated"
  freshNames := true
  templates := tokenTemplates
  edges := tokenEdges
  compatibility := .all
  steps := []

def overflowDesc : Description where
  name := "overflow"
  freshNames := true
  templates := [tpl "producer" 10 ["idle"] "idle" true, tpl "consumer" 10 ["idle"] "idle" true]
  edges := [sendEdge "producer" "idle" "consumer" "Burst" 11]
  compatibility := .all
  steps := []

theorem safe_pass : render safeDesc = "pass" := by decide

theorem manager_cycle : render managerPeerDesc =
    "fail: residual cycle\n  (peer_selection, idle) -> (manager, idle) -> (peer_selection, idle)" := by
  decide

theorem credit_pass : render creditDesc = "pass" := by decide

theorem token_explicit_rejected : render tokenDesc =
    "fail: compatibility mode explicit is not an invariance check; use groups" := by
  decide

theorem token_ungated_cycle : render tokenUngatedDesc =
    "fail: residual cycle\n  (select_chain, holding) -> (fetch_blocks, busy) -> (select_chain, holding)" := by
  decide

theorem overflow_mailbox : render overflowDesc =
    "fail: overflowing mailbox\n  mailbox consumer: occupancy 0*N+11 > capacity 0*N+10" := by
  decide

def lostReplyDesc : Description where
  name := "lost-reply"
  freshNames := true
  templates := [tpl "source" 10 ["idle"] "idle" true, tpl "sink" 10 ["idle"] "idle" true]
  edges := [{ (sendEdge "source" "idle" "sink" "Ping" 1) with effect := .call }]
  compatibility := .all
  steps := []

def lostWakeDesc : Description where
  name := "lost-wake"
  freshNames := true
  templates := [tpl "writer" 10 ["idle"] "idle" true, tpl "reader" 10 ["idle"] "idle" true]
  edges :=
    [{ (sendEdge "writer" "idle" "reader" "Wake" 1) with
        kind := .nonBlocking, reliability := .superseding, effect := .cell,
        cell := { singleWriter := true, orderMonotone := true, noPerMessageObligation := true,
                  visibility := true, readPoints := false, idempotent := true, dirtyBit := false } }]
  compatibility := .all
  steps := []

theorem lost_reply_fails : render lostReplyDesc =
    "fail: call source -[Ping]-> sink is not answered in the dequeue transition" := by
  decide

theorem lost_wake_fails : render lostWakeDesc =
    "fail: superseding edge Wake misses cell conditions readPoints, dirtyBit" := by
  decide

def undeclaredCellDesc : Description where
  name := "undeclared-cell"
  freshNames := true
  templates := [tpl "writer" 10 ["idle"] "idle" true, tpl "reader" 10 ["idle"] "idle" true]
  edges := []
  compatibility := .all
  steps := []
  cellEffects := [{ src := "writer", srcState := "idle", dst := "reader", label := "Ghost" }]

theorem undeclared_cell_fails : render undeclaredCellDesc =
    "fail: cell effect writer/idle -[Ghost]-> reader is not a declared cell edge" := by
  decide

def rs (role state : String) : RoleState := { role, state }

def fetchRoles : List String := ["select_chain", "fetch_blocks", "header_store"]

def fetchTuple (s f : String) : List RoleState :=
  [rs "select_chain" s, rs "fetch_blocks" f, rs "header_store" "idle"]

def fetchGroup (coarse : Bool) : CompatGroup where
  name := "fetch-token"
  roles := fetchRoles
  allowed :=
    [fetchTuple "idle" "idle", fetchTuple "holding" "idle", fetchTuple "idle" "busy"] ++
      if coarse then [fetchTuple "holding" "busy"] else []

def fetchTemplates : List Template :=
  tokenTemplates ++ [tpl "header_store" 10 ["idle"] "idle" false]

def fetchSteps (onTip : Bool) : List CompatStep :=
  [{ template := "select_chain", fromState := "holding", toState := "idle", label := "Release" },
   { template := "fetch_blocks", fromState := "busy", toState := "idle", label := "Return" }] ++
    if onTip then [{ template := "fetch_blocks", fromState := "idle", toState := "busy", label := "OnTip" }] else []

def fetchRelDesc (name : String) (coarse onTip : Bool) : Description where
  name := name
  freshNames := true
  templates := fetchTemplates
  edges := tokenEdges
  compatibility := .groups [fetchGroup coarse]
  steps := fetchSteps onTip

def tokenRelationDesc : Description := fetchRelDesc "token-relation" false false
def tokenGapDesc : Description := fetchRelDesc "token-relation-gap" false true
def tokenCoarseDesc : Description := fetchRelDesc "token-relation-coarse" true true

theorem token_relation_pass : render tokenRelationDesc = "pass" := by decide

theorem token_relation_gap : render tokenGapDesc =
    "fail: compatibility broken by transition fetch_blocks idle -> busy [OnTip]\n  pre: (select_chain: holding, fetch_blocks: idle, header_store: idle)\n  post: (select_chain: holding, fetch_blocks: busy, header_store: idle)" := by
  decide

theorem token_relation_coarse : render tokenCoarseDesc =
    "fail: residual cycle\n  (select_chain, holding) -> (fetch_blocks, busy) -> (select_chain, holding)" := by
  decide

/-- Two blocking sends into mailboxes of capacity 1, with occupancy 2 and
`mustFit` false. Lemma 1 does not discharge either edge, and overflow is not
reported, so the residual graph keeps the 2-cycle. -/
def mutualFullDesc : Description where
  name := "mutual-full"
  freshNames := true
  templates := [tpl "left" 1 ["idle"] "idle" false, tpl "right" 1 ["idle"] "idle" false]
  edges := [sendEdge "left" "idle" "right" "Ping" 2, sendEdge "right" "idle" "left" "Pong" 2]
  compatibility := .all
  steps := []

/-- A reliable `trySend` that is neither ingress nor superseding. The receive
path drops it when the mailbox is full. -/
def reliableTryDesc : Description where
  name := "reliable-try"
  freshNames := true
  templates := [tpl "source" 10 ["idle"] "idle" true, tpl "sink" 10 ["idle"] "idle" true]
  edges :=
    [{ (sendEdge "source" "idle" "sink" "Ping" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := false }]
  compatibility := .all
  steps := []

theorem mutual_full_rejected : render mutualFullDesc =
    "fail: residual cycle\n  (right, idle) -> (left, idle) -> (right, idle)" := by
  decide

theorem reliable_try_fails : render reliableTryDesc =
    "fail: reliable trySend Ping may be dropped; mark a self-edge ingress or use superseding" := by
  decide

/-- A connection subtree. `reader` waits, untimed, on the leading edge of a
segment header. `timer` is the mini-protocol timeout: its peer wait is timed
and `timeoutKills`, so one kill ends both roles. `opener` is outside the
subtree and only arms the timer. -/
def connRole (name : String) (untimed timeout : Bool) : Template :=
  { tpl name 2 ["idle"] "idle" false with
      multiplicity := .perPeer, terminable := true, untimedPeer := untimed,
      subtree := "conn", timeoutKills := timeout }

def openerTpl : Template :=
  { tpl "opener" 2 ["idle"] "idle" true with
      multiplicity := .perPeer, capacity := { a := 2, b := 2 } }

def muxIngress : Edge :=
  { src := "opener", srcState := "idle", dst := "opener", kind := .nonBlocking,
    reliability := .reliable, effect := .trySend, label := "Go", scope := .intra,
    occupancy := { a := 1, b := 0 }, repliesInDequeue := false, ingress := true,
    ingressLegal := some { a := 1, b := 0 }, cell := .none }

def armEdge : Edge :=
  { (sendEdge "opener" "idle" "timer" "Arm" 0) with
      occupancy := { a := 1, b := 0 }, scope := .cross }

def selfPeer (src label : String) : Edge :=
  { (sendEdge src "idle" src label 0) with kind := .nonBlocking, effect := .peer }

def muxDesc : Description where
  name := "mux-conn"
  freshNames := true
  templates := [openerTpl, connRole "timer" false true, connRole "reader" true false]
  edges := [muxIngress, armEdge, selfPeer "timer" "Timeout", selfPeer "reader" "Header"]
  compatibility := .all
  steps := []

theorem mux_pass : render muxDesc = "pass" := by decide

/-- A call from a permanent core into the connection names a terminable role
outside the caller's subtree. The checker rejects it. -/
def muxCrossDesc : Description where
  name := "mux-cross"
  freshNames := true
  templates :=
    [openerTpl, connRole "timer" false true, connRole "reader" true false,
     tpl "node" 2 ["idle"] "idle" true]
  edges :=
    [muxIngress, armEdge, selfPeer "timer" "Timeout", selfPeer "reader" "Header",
     { (sendEdge "node" "idle" "reader" "Open" 1) with
         effect := .call, scope := .coreInst, repliesInDequeue := true }]
  compatibility := .all
  steps := []

theorem mux_cross_fails : render muxCrossDesc =
    "fail: call Open targets terminable template reader" := by decide

end Deadlock
