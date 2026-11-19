import Deadlock.Examples
import Deadlock.Local
import Deadlock.Progress

set_option autoImplicit false
set_option maxRecDepth 100000

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

/-! A per-peer producer parked on B while B is parked on C. The chain is height 2,
and two receives along it leave the producer idle. -/

def ingE (t label : String) : Edge :=
  { src := t, srcState := "idle", dst := t, kind := .nonBlocking, reliability := .reliable,
    effect := .trySend, label := label, scope := .intra, occupancy := .ofNat 1,
    repliesInDequeue := false, ingress := true, ingressLegal := some (Affine.ofNat 1), cell := .none }

def pTpl : Template :=
  { tpl "P" 2 ["idle", "busy"] "idle" true with multiplicity := .perPeer, capacity := { a := 2, b := 2 } }

def ingPs (st : String) : Edge :=
  { ingE "P" "Go" with srcState := st, occupancy := { a := 1, b := 0 }, ingressLegal := some { a := 1, b := 0 } }

def chainDesc : Description where
  name := "height-two"
  freshNames := true
  templates := [pTpl, tpl "B" 1 ["idle", "busy"] "idle" false, tpl "C" 1 ["idle"] "idle" false]
  edges := [ingPs "idle", ingPs "busy",
            { sendEdge "P" "busy" "B" "M" 0 with occupancy := { a := 3, b := 0 }, scope := .coreInst },
            sendEdge "B" "busy" "C" "N" 2]
  compatibility := .all
  steps := [{ template := "P", fromState := "idle", toState := "busy", label := "Go" },
            { template := "P", fromState := "busy", toState := "busy", label := "Go" },
            { template := "B", fromState := "idle", toState := "busy", label := "M" },
            { template := "B", fromState := "busy", toState := "busy", label := "M" },
            { template := "C", fromState := "idle", toState := "idle", label := "N" }]

def tr2 (t f label to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := label, program := p, toState := to,
    acceptsCall := false, release := 1 }

def chainImpl : Impl where
  desc := chainDesc
  transitions := [tr2 "P" "idle" "Go" "busy" [.send "B" "M" 0, .send "B" "M" 0, .send "B" "M" 0],
                  tr2 "P" "busy" "Go" "busy" [],
                  tr2 "B" "idle" "M" "busy" [.send "C" "N" 0, .send "C" "N" 0],
                  tr2 "B" "busy" "M" "busy" [],
                  tr2 "C" "idle" "N" "idle" []]

def P0 : InstId := .peer "P" 0
def Bc : InstId := .core "B"
def Cc : InstId := .core "C"

def chainActs : List Action :=
  [.spawn "P", .ingress P0 "Go", .recvBulk P0, .exec P0, .recvBulk Bc, .exec Bc, .exec Bc,
   .exec P0, .exec P0]

def chainAt (acts : List Action) : Option World := runFrom chainImpl (some (initWorld chainImpl 1)) acts

def waitTag (w : Option World) (x : InstId) : Nat :=
  match w with
  | some w => match (w.st x).phase with
    | .parked d false _ => if d = Bc then 1 else if d = Cc then 2 else 9
    | .idle => 3 | .run _ => 4 | _ => 0
  | none => 0

theorem chain_graph : checkBool chainDesc = true := by decide
theorem chain_local : localOkB chainImpl = true := by decide
theorem chain_graph_ok : GraphOk chainDesc := checkBool_sound chainDesc chain_graph

/-- P (per-peer) parked on B while B is parked on C: the height-2 case. -/
theorem height_two : waitTag (chainAt chainActs) P0 = 1 ∧ waitTag (chainAt chainActs) Bc = 2 := by decide

/-- B's own receive is disabled (B is parked). -/
theorem partner_blocked : ((chainAt chainActs).bind (apply chainImpl (.recvBulk Bc))) = none := by decide

theorem hCB : Cc ≠ Bc := by decide

theorem tag_cases (w : World) (x : InstId) (n : Nat) (h : waitTag (some w) x = n) :
    (∃ d k, (w.st x).phase = .parked d false k ∧
      n = (if d = Bc then 1 else if d = Cc then 2 else 9)) ∨
    ((w.st x).phase = .idle ∧ n = 3) ∨ (∃ k, (w.st x).phase = .run k ∧ n = 4) ∨ n = 0 := by
  unfold waitTag at h
  cases hp : (w.st x).phase with
  | parked d c k =>
    cases c
    · left; exact ⟨d, k, rfl, by simp [hp] at h; exact h.symm⟩
    · simp [hp] at h; omega
  | idle => right; left; simp [hp] at h; exact ⟨rfl, h.symm⟩
  | run k => right; right; left; simp [hp] at h; exact ⟨k, rfl, h.symm⟩
  | _ => simp [hp] at h; omega

theorem tag_waits (w : World) (x : InstId) (h : waitTag (some w) x = 1) : WaitsOn w x Bc := by
  rcases tag_cases w x 1 h with ⟨d, k, hp, hn⟩ | ⟨_, hn⟩ | ⟨_, _, hn⟩ | hn
  · unfold WaitsOn; rw [hp]
    by_cases hd : d = Bc
    · exact hd
    · by_cases hc : d = Cc <;> simp [hd, hc, hCB] at hn
  all_goals omega

theorem tag_waits_c (w : World) (x : InstId) (h : waitTag (some w) x = 2) : WaitsOn w x Cc := by
  rcases tag_cases w x 2 h with ⟨d, k, hp, hn⟩ | ⟨_, hn⟩ | ⟨_, _, hn⟩ | hn
  · unfold WaitsOn; rw [hp]
    by_cases hd : d = Bc
    · simp [hd] at hn
    · by_cases hc : d = Cc
      · exact hc
      · simp [hd, hc] at hn
  all_goals omega

theorem tag_idle (w : World) (x : InstId) (h : waitTag (some w) x = 3) : (w.st x).phase = .idle := by
  rcases tag_cases w x 3 h with ⟨d, k, hp, hn⟩ | ⟨hp, _⟩ | ⟨_, _, hn⟩ | hn
  · by_cases hd : d = Bc
    · simp [hd] at hn
    · by_cases hc : d = Cc <;> simp [hd, hc, hCB] at hn
  · exact hp
  all_goals omega

theorem after1 : waitTag (chainAt (chainActs ++ [.recvBulk Cc])) P0 = 1 := by decide
theorem final_idle : waitTag (chainAt (chainActs ++ [.recvBulk Cc, .recvBulk Bc])) P0 = 3 := by decide

theorem run_append (I : Impl) (w : Option World) (xs ys : List Action) :
    runFrom I w (xs ++ ys) = runFrom I (runFrom I w xs) ys := by
  induction xs generalizing w with
  | nil => rfl
  | cons a as ih =>
    cases w with
    | none => cases as <;> cases ys <;> simp [runFrom]
    | some w => simp [runFrom, ih]

/-- A reachable world of a `GraphOk` and `LocalOk` instance: a per-peer actor is
blocked through a height-2 chain, and `recvBulk` of C then of B leaves it unblocked. -/
theorem chain_witness : ∃ w w', Reachable chainImpl 1 w ∧ Blocked w P0 ∧
    ChainRun chainImpl P0 w [.recvBulk Cc, .recvBulk Bc] ∧
    runFrom chainImpl (some w) [.recvBulk Cc, .recvBulk Bc] = some w' ∧ ¬ Blocked w' P0 := by
  have h2 := height_two
  cases hw : chainAt chainActs with
  | none => simp [hw, waitTag] at h2
  | some w =>
    have hR := run_reachable chainImpl 1 (initWorld chainImpl 1) Reachable.init chainActs w
      (by simpa [chainAt] using hw)
    have hPB : WaitsOn w P0 Bc := tag_waits w P0 (by simpa [hw] using h2.1)
    have hBC : WaitsOn w Bc Cc := tag_waits_c w Bc (by simpa [hw] using h2.2)
    have ha1 := after1
    rw [chainAt, run_append, ← chainAt, hw] at ha1
    cases h1 : apply chainImpl (.recvBulk Cc) w with
    | none => simp [runFrom, h1, waitTag] at ha1
    | some w1 =>
      have hfin := final_idle
      rw [chainAt, run_append, ← chainAt, hw] at hfin
      simp only [runFrom, h1] at ha1 hfin
      cases h2' : apply chainImpl (.recvBulk Bc) w1 with
      | none => simp [h2', waitTag] at hfin
      | some w2 =>
        simp only [h2'] at hfin
        have hP1 : WaitsOn w1 P0 Bc := tag_waits w1 P0 ha1
        refine ⟨w, w2, hR, ?_, ?_, ?_, ?_⟩
        · unfold WaitsOn at hPB
          refine ⟨?_, ?_⟩
          · have : ((w.st P0).life == .alive) = true := by
              have hl : ((chainAt chainActs).map fun w => (w.st P0).life == .alive) = some true := by decide
              simpa [hw] using hl
            simpa using this
          · split at hPB <;> simp_all
        · refine ChainRun.cons w _ w1 _ ?_ h1 (ChainRun.cons w1 _ w2 _ ?_ h2' (ChainRun.nil _))
          · simp only [OnChain, actionSubject]
            exact ⟨InChain.step _ _ _ (chain_of_wait w P0 Bc hPB) hBC, trivial⟩
          · simp only [OnChain, actionSubject]
            exact ⟨chain_of_wait w1 P0 Bc hP1, trivial⟩
        · simp [runFrom, h1, h2']
        · rintro ⟨_, hb⟩
          rw [tag_idle w2 P0 hfin] at hb
          exact hb

/-! A mux-like connection. The timer's peer wait is the mini-protocol timeout.
Killing the subtree at that key leaves the timer and the untimed reader dead
together, and records one tombstone. The opener, outside the subtree, stays. -/

def muxImpl : Impl where
  desc := muxDesc
  transitions :=
    [tr2 "opener" "idle" "Go" "idle" [.send "timer" "Arm" 0],
     tr2 "timer" "idle" "Arm" "idle" [.peer]]

def openerId : InstId := .peer "opener" 0
def timerId : InstId := .peer "timer" 0
def muxReaderId : InstId := .peer "reader" 0

def muxActs : List Action :=
  [.spawn "opener", .spawn "timer", .spawn "reader",
   .ingress openerId "Go", .recvBulk openerId, .exec openerId,
   .recvBulk timerId, .exec timerId, .kill "conn" 0]

def muxAt (acts : List Action) : Option World :=
  runFrom muxImpl (some (initWorld muxImpl 1)) acts

def lifeTag (w : Option World) (i : InstId) : Nat :=
  match w with
  | some w => match (w.st i).life with
    | .alive => 1
    | .dead => 2
    | .absent => 0
  | none => 9

theorem mux_kill :
    lifeTag (muxAt muxActs) timerId = 2 ∧ lifeTag (muxAt muxActs) muxReaderId = 2 ∧
      lifeTag (muxAt muxActs) openerId = 1 ∧
      (muxAt muxActs).map (·.tombstone) = some (some 0) := by
  decide

end Deadlock
