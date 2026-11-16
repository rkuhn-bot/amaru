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

theorem park_graph : render parkDesc = "pass" := by decide

theorem park_local : localOkB parkImpl = true := by decide

theorem park_checked : checkBool parkDesc = true := by decide

theorem park_graph_ok : GraphOk parkDesc := checkBool_sound parkDesc park_checked

theorem park_local_ok : LocalOk parkImpl := park_local

def producerId : InstId := .core "producer"

def sinkId : InstId := .core "sink"

def runFrom (I : Impl) : Option World → List Action → Option World
  | w, [] => w
  | none, _ :: _ => none
  | some w, a :: as => runFrom I (apply I a w) as

def afterActs (acts : List Action) : Option World :=
  runFrom parkImpl (some (initWorld parkImpl 0)) acts

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

theorem parks_on_second_send : producerTag (afterActs parkActs) = 1 := by decide

/-- The sink then receives, which admits the parked send and resumes the producer. -/
theorem resumes_after_receive :
    producerTag (afterActs (parkActs ++ [.recvBulk sinkId])) = 2 := by decide

theorem run_reachable (I : Impl) (N : Nat) (w0 : World) (h0 : Reachable I N w0)
    (acts : List Action) (w : World) (h : runFrom I (some w0) acts = some w) : Reachable I N w := by
  induction acts generalizing w0 with
  | nil =>
    simp [runFrom] at h
    cases h
    exact h0
  | cons a acts ih =>
    simp [runFrom] at h
    cases ha : apply I a w0 with
    | none =>
      cases acts <;> simp [runFrom, ha] at h
    | some w1 =>
      simp [ha] at h
      exact ih w1 (Reachable.step w0 w1 a h0 ha) h

theorem run_snoc (I : Impl) (w0 : World) (acts : List Action) (a : Action) :
    runFrom I (some w0) (acts ++ [a]) = (runFrom I (some w0) acts).bind (apply I a) := by
  induction acts generalizing w0 with
  | nil => simp [runFrom, Option.bind]
  | cons b bs ih =>
    simp [runFrom, List.cons_append]
    cases apply I b w0 with
    | none =>
      cases bs <;> simp [runFrom, Option.bind]
    | some w1 => simp [ih]

/-- The parked producer is a reachable world, not an extra initial state. -/
theorem park_reachable : ∃ w, afterActs parkActs = some w ∧ Reachable parkImpl 0 w ∧
    ∃ dst isCall k, (w.st producerId).phase = .parked dst isCall k := by
  have htag := parks_on_second_send
  cases hw : afterActs parkActs with
  | none => simp [producerTag, hw] at htag
  | some w =>
    have hR := run_reachable parkImpl 0 (initWorld parkImpl 0) Reachable.init parkActs w
      (by simpa [afterActs] using hw)
    cases hph : (w.st producerId).phase with
    | parked dst isCall k =>
      exact ⟨w, rfl, hR, ⟨dst, isCall, k, hph⟩⟩
    | idle => simp [producerTag, phaseTag, hw, hph] at htag
    | run _ => simp [producerTag, phaseTag, hw, hph] at htag
    | awaitReply _ _ => simp [producerTag, phaseTag, hw, hph] at htag
    | awaitEffect _ => simp [producerTag, phaseTag, hw, hph] at htag
    | awaitPeer _ => simp [producerTag, phaseTag, hw, hph] at htag
    | crashed => simp [producerTag, phaseTag, hw, hph] at htag

/-- From that reachable world, receiving at the sink is enabled and the producer is idle again. -/
theorem park_unblocks : ∃ w w', afterActs parkActs = some w ∧ Reachable parkImpl 0 w ∧
    (∃ dst isCall k, (w.st producerId).phase = .parked dst isCall k) ∧
    apply parkImpl (.recvBulk sinkId) w = some w' ∧ (w'.st producerId).phase = .idle := by
  obtain ⟨w, hw, hR, dst, isCall, k, hph⟩ := park_reachable
  have htag := resumes_after_receive
  have hrun : runFrom parkImpl (some (initWorld parkImpl 0)) parkActs = some w := by
    simpa [afterActs] using hw
  have hfold := run_snoc parkImpl (initWorld parkImpl 0) parkActs (.recvBulk sinkId)
  simp [afterActs, hfold, hrun, Option.bind] at htag
  cases ha : apply parkImpl (.recvBulk sinkId) w with
  | none => simp [ha, Option.bind, producerTag] at htag
  | some w' =>
    simp [ha, Option.bind, producerTag, phaseTag] at htag
    cases hph' : (w'.st producerId).phase <;> simp [hph', phaseTag] at htag
    exact ⟨w, w', hw, hR, ⟨dst, isCall, k, hph⟩, ha, hph'⟩

end Deadlock
