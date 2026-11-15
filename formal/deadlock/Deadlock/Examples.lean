import Deadlock.Graph

set_option autoImplicit false

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

def managerPeerDesc : Description where
  name := "manager-peer"
  freshNames := true
  templates := [tpl "manager" 10 ["idle"] "idle" false, tpl "peer_selection" 10 ["idle"] "idle" false]
  edges :=
    [sendEdge "manager" "idle" "peer_selection" "ConnectionEvent" 11,
     sendEdge "peer_selection" "idle" "manager" "AddPeer" 11]
  compatibility := .all

def creditDesc : Description where
  name := "credit"
  freshNames := true
  templates := [tpl "client" 1 ["idle"] "idle" true, tpl "server" 1 ["idle"] "idle" true]
  edges :=
    [sendEdge "client" "idle" "server" "Request" 1,
     sendEdge "server" "idle" "client" "Response" 1]
  compatibility := .all

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

def tokenUngatedDesc : Description where
  name := "token-pair-ungated"
  freshNames := true
  templates := tokenTemplates
  edges := tokenEdges
  compatibility := .all

def overflowDesc : Description where
  name := "overflow"
  freshNames := true
  templates := [tpl "producer" 10 ["idle"] "idle" true, tpl "consumer" 10 ["idle"] "idle" true]
  edges := [sendEdge "producer" "idle" "consumer" "Burst" 11]
  compatibility := .all

theorem safe_pass : render safeDesc = "pass" := by native_decide

theorem manager_cycle : render managerPeerDesc =
    "fail: residual cycle\n  (peer_selection, idle) -> (manager, idle) -> (peer_selection, idle)" := by
  native_decide

theorem credit_pass : render creditDesc = "pass" := by native_decide

theorem token_pass : render tokenDesc = "pass" := by native_decide

theorem token_ungated_cycle : render tokenUngatedDesc =
    "fail: residual cycle\n  (select_chain, holding) -> (fetch_blocks, busy) -> (select_chain, holding)" := by
  native_decide

theorem overflow_mailbox : render overflowDesc =
    "fail: overflowing mailbox\n  mailbox consumer: occupancy 0*N+11 > capacity 0*N+10" := by
  native_decide

end Deadlock
