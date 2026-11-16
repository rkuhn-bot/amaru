import Deadlock
set_option autoImplicit false
namespace Deadlock.Helen
open Deadlock

/-! ## F6: `Assumptions` is free for the default environment and pins the oracle to `true`. -/

theorem assumptions_default (D : Description) (trs : List Transition) :
    Assumptions { desc := D, transitions := trs } := by
  refine ⟨fun tr h => ⟨tr, h, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩ <;>
  · intro w id k hk
    simp [Enabled, apply, finishWait, hk, Env.always]

theorem assumptions_force_effect (I : Impl) (hA : Assumptions I) (w : World) (id : InstId) (k : Cont)
    (hk : (w.st id).phase = .awaitEffect k) : I.env.effectDone w id = true := by
  have h := hA.internal_complete w id k hk
  simp only [Enabled, apply, finishWait, hk] at h
  cases hc : I.env.effectDone w id <;> simp_all

theorem assumptions_force_peer (I : Impl) (hA : Assumptions I) (w : World) (id : InstId) (k : Cont)
    (hk : (w.st id).phase = .awaitPeer k) : I.env.peerDone w id = true := by
  have h := hA.peer_complete w id k hk
  simp only [Enabled, apply, finishWait, hk] at h
  cases hc : I.env.effectDone w id <;> simp_all

/-! ## (a): `∃ act, Enabled I w act` is witnessed off the wait chain.
A ↔ B: each, on ingress `Go`, sends `M` twice into the other's capacity-1 box.
C: an independent core with a self ingress `Tick`. -/

def ing (t label : String) : Edge where
  src := t
  srcState := "idle"
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := .ofNat 1
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat 1)
  cell := .none

def tr (t label : String) (p : List Eff) : Transition :=
  { template := t, fromState := "idle", label := label, program := p, toState := "idle",
    acceptsCall := false, release := 1 }

def cycDesc : Description where
  name := "cycle-plus-clock"
  freshNames := true
  templates := [tpl "A" 1 ["idle"] "idle" false, tpl "B" 1 ["idle"] "idle" false,
                tpl "C" 1 ["idle"] "idle" true]
  edges := [ing "A" "Go", ing "B" "Go", ing "C" "Tick",
            sendEdge "A" "idle" "B" "M" 2, sendEdge "B" "idle" "A" "M" 2]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "idle", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Go" },
            { template := "B", fromState := "idle", toState := "idle", label := "M" },
            { template := "C", fromState := "idle", toState := "idle", label := "Tick" }]

def cycImpl : Impl where
  desc := cycDesc
  transitions := [tr "A" "Go" [.send "B" "M" 0, .send "B" "M" 0], tr "A" "M" [],
                  tr "B" "Go" [.send "A" "M" 0, .send "A" "M" 0], tr "B" "M" [],
                  tr "C" "Tick" []]

def A : InstId := .core "A"
def B : InstId := .core "B"
def C : InstId := .core "C"

/-- The checker rejects it (the A/B residual cycle): GraphOk forbids this config. -/
theorem cyc_rejected : checkBool cycDesc = false := by native_decide

def cycActs : List Action :=
  [.ingress A "Go", .ingress B "Go", .recvBulk A, .recvBulk B,
   .exec A, .exec B, .exec A, .exec B]

def after (acts : List Action) : Option World := runFrom cycImpl (some (initWorld cycImpl 0)) acts

def tag (w : Option World) (x : InstId) : Nat :=
  match w with
  | none => 0
  | some w => match (w.st x).phase with
    | .parked d false _ => if d = A then 10 else if d = B then 11 else 1
    | .idle => 2 | .run _ => 3 | _ => 0

/-- A is parked on B and B is parked on A: a real two-actor deadlock. -/
theorem mutual_park : tag (after cycActs) A = 11 ∧ tag (after cycActs) B = 10 := by native_decide

/-- In that world the blocked actors' own targets cannot receive (both parked) … -/
theorem chain_disabled :
    (after cycActs).bind (apply cycImpl (.recvBulk A)) = none ∧
    (after cycActs).bind (apply cycImpl (.recvBulk B)) = none ∧
    (after cycActs).bind (apply cycImpl (.exec A)) = none ∧
    (after cycActs).bind (apply cycImpl (.exec B)) = none := by native_decide

/-- … yet `∃ act, Enabled` holds via the unrelated ingress into C, and C can cycle
forever while A and B stay parked. -/
theorem clock_enabled : ((after cycActs).bind (apply cycImpl (.ingress C "Tick"))).isSome = true := by
  native_decide

theorem still_parked :
    let w := after (cycActs ++ [.ingress C "Tick", .recvBulk C, .ingress C "Tick", .recvBulk C,
                                .ingress C "Tick", .recvBulk C])
    w.isSome = true ∧ tag w A = 11 ∧ tag w B = 10 := by native_decide

theorem deadlocked_world_reachable : ∃ w, after cycActs = some w ∧ Reachable cycImpl 0 w ∧
    Blocked w A ∧ ∃ act, Enabled cycImpl w act := by
  have hm := mutual_park
  have hc := clock_enabled
  cases hw : after cycActs with
  | none => simp [tag, hw] at hm
  | some w =>
    have hR := run_reachable cycImpl 0 (initWorld cycImpl 0) Reachable.init cycActs w
      (by simpa [after] using hw)
    refine ⟨w, rfl, hR, ?_, .ingress C "Tick", ?_⟩
    · simp only [tag, hw] at hm
      refine ⟨?_, ?_⟩
      · have : (w.st A).life = .alive ∨ (w.st A).life ≠ .alive := Classical.em _
        rcases this with h | h
        · exact h
        · exfalso
          -- parked phases only exist on live actors here; check concretely
          have hl : ((after cycActs).map (fun w => decide ((w.st A).life = .alive))) = some true := by
            native_decide
          simp [hw] at hl; exact h hl
      · split at hm <;> simp_all
    · simp only [hw, Option.bind] at hc
      intro hnone; simp [hnone] at hc

/-! ## (a) variant that PASSES GraphOk ∧ LocalOk: the park witness plus an
independent clock. The conclusion of `blocked_progress` at the parked world is
again witnessed by the clock, not by the sink on the producer's chain. -/

def parkClockDesc : Description :=
  { parkDesc with
    templates := parkDesc.templates ++ [tpl "clock" 1 ["idle"] "idle" true]
    edges := parkDesc.edges ++ [ing "clock" "Tick"]
    steps := parkDesc.steps ++ [{ template := "clock", fromState := "idle", toState := "idle", label := "Tick" }] }

def parkClockImpl : Impl where
  desc := parkClockDesc
  transitions := parkImpl.transitions ++ [tr "clock" "Tick" []]

theorem pc_graph : checkBool parkClockDesc = true := by native_decide
theorem pc_local : localOkB parkClockImpl = true := by native_decide

theorem pc_clock_enabled :
    ((runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs).bind
      (apply parkClockImpl (.ingress (.core "clock") "Tick"))).isSome = true := by native_decide

theorem pc_producer_parked :
    (match runFrom parkClockImpl (some (initWorld parkClockImpl 0)) parkActs with
     | some w => phaseTag ((w.st producerId).phase) | none => 0) = 1 := by native_decide

/-! ## (c): the old `vacuous` is now false for a substantive reason: a reachable
world with a real blocking-send wait in a GraphOk ∧ LocalOk instance. -/

def sendTag : Option World → Nat
  | some w => match (w.st producerId).phase with
    | .parked _ false _ => 1
    | .parked _ true _ => 5
    | _ => 0
  | none => 0

theorem park_is_send : sendTag (afterActs parkActs) = 1 := by native_decide

theorem not_vacuous : GraphOk parkDesc ∧ LocalOk parkImpl ∧
    ∃ w, Reachable parkImpl 0 w ∧ ∃ d, waitKind (w.st producerId) = some (.blockingSend d) := by
  refine ⟨park_graph_ok, park_local_ok, ?_⟩
  obtain ⟨w, hw, hR, d, isCall, k, hph⟩ := park_reachable
  refine ⟨w, hR, d, ?_⟩
  have ht := park_is_send
  rw [hw] at ht
  cases isCall with
  | false => simp [waitKind, hph]
  | true => simp [sendTag, hph] at ht

end Deadlock.Helen
#print axioms Deadlock.Helen.assumptions_default
#print axioms Deadlock.Helen.assumptions_force_peer
#print axioms Deadlock.Helen.deadlocked_world_reachable
#print axioms Deadlock.Helen.still_parked
#print axioms Deadlock.Helen.pc_local
#print axioms Deadlock.Helen.not_vacuous
