import Deadlock.Examples
import Deadlock.Local

set_option autoImplicit false

namespace Deadlock

/-- Producer capacity covers its two ingress edges. The sink's capacity is 1
while the only send into it declares occupancy 2 and `mustFit` is false, so
the second send parks and the residual graph is a single edge. -/
def parkDesc : Description where
  name := "park-resume"
  freshNames := true
  templates :=
    [tpl "producer" 2 ["idle", "busy"] "idle" true,
     tpl "sink" 1 ["idle"] "idle" false]
  edges :=
    [{ (sendEdge "producer" "idle" "producer" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     { (sendEdge "producer" "busy" "producer" "Go" 1) with
        effect := .trySend, kind := .nonBlocking, reliability := .reliable,
        ingress := true, ingressLegal := some (Affine.ofNat 1) },
     sendEdge "producer" "busy" "sink" "M" 2]
  compatibility := .all
  steps :=
    [{ template := "producer", fromState := "idle", toState := "busy", label := "Go" },
     { template := "producer", fromState := "busy", toState := "busy", label := "Go" },
     { template := "sink", fromState := "idle", toState := "idle", label := "M" }]

def parkTr (template fromState label toState : String) (program : List Eff) : Transition where
  template := template
  fromState := fromState
  label := label
  program := program
  toState := toState
  acceptsCall := false
  release := 1

def parkImpl : Impl where
  desc := parkDesc
  transitions :=
    [parkTr "producer" "idle" "Go" "busy" [.send "sink" "M" 0, .send "sink" "M" 0],
     parkTr "producer" "busy" "Go" "busy" [],
     parkTr "sink" "idle" "M" "idle" []]

theorem park_graph : render parkDesc = "pass" := by native_decide

theorem park_local : localOkB parkImpl = true := by native_decide

theorem park_checked : checkBool parkDesc = true := by native_decide

theorem park_graph_ok : GraphOk parkDesc := checkBool_sound parkDesc park_checked

theorem park_local_ok : LocalOk parkImpl := park_local

def producerId : InstId := .core "producer"

def sinkId : InstId := .core "sink"

def afterActs (acts : List Action) : Option World :=
  acts.foldl (fun acc a => acc.bind (apply parkImpl a)) (some (initWorld parkImpl 0))

def phaseTag : Phase → Nat
  | .parked _ _ _ => 1
  | .idle => 2
  | .run _ => 3
  | _ => 0

def producerTag (w : Option World) : Nat :=
  match w with
  | none => 0
  | some w => phaseTag ((w.st producerId).phase)

/-- Ingress, deliver it, then the two sends. The second send finds the sink full. -/
def parkActs : List Action :=
  [.ingress producerId "Go", .recvBulk producerId, .exec producerId, .exec producerId]

theorem parks_on_second_send : producerTag (afterActs parkActs) = 1 := by native_decide

/-- The sink then receives, which admits the parked send and resumes the producer. -/
theorem resumes_after_receive :
    producerTag (afterActs (parkActs ++ [.recvBulk sinkId])) = 2 := by native_decide

end Deadlock
