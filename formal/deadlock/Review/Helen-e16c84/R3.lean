import Deadlock
set_option autoImplicit false
namespace Deadlock.Helen3
open Deadlock

/-! ## (1) With `stutter`, `FinExec` is uninhabited. -/

theorem finexec_empty (I : Impl) (N : Nat) (e : FinExec I N) : False := by
  have hs := e.maximal .stutter
  simp only [apply] at hs
  have hb : runtimeBusy I (e.cfg e.len) = true := by
    cases h : runtimeBusy I (e.cfg e.len) with
    | true => rfl
    | false => simp [h] at hs
  obtain ⟨id, _, hid⟩ := _root_.List.any_eq_true.mp hb
  simp only [Bool.or_eq_true] at hid
  rcases hid with ((h | h) | h) | h
  · have := e.maximal (.recvBulk id); simp [apply] at this; simp [this] at h
  · have := e.maximal (.recvPrio id); simp [apply] at this; simp [this] at h
  · have := e.maximal (.exec id); simp [apply] at this; simp [this] at h
  · have := e.maximal (.finish id); simp [apply] at this; simp [this] at h

/-! ## (1) Stutter cannot hide a blocked actor in a checked reachable world. -/

theorem blocked_no_stutter (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    (N : Nat) (w : World) (hR : Reachable I N w) (id : InstId) (hB : Blocked w id) :
    ¬ Enabled I w .stutter := by
  intro hst
  obtain ⟨act, hon, hen⟩ := blocked_progress I hG hL hA N w hR id hB
  have hb : runtimeBusy I w = false := by
    cases h : runtimeBusy I w with
    | false => rfl
    | true => simp [Enabled, apply, h] at hst
  have hforced : forced act = true := by
    cases act <;> simp_all [OnChain, actionSubject, forced]
  exact quiet_no_forced I w
    (fun s hs => let h := off_idle_reachable I N w hR s hs; ⟨h.2, h.1⟩) hb act hforced hen

/-! ## (2) `Delivered` accepts a message lost to a killing `terminate`. -/

def ingE (t label : String) : Edge :=
  { src := t, srcState := "idle", dst := t, kind := .nonBlocking, reliability := .reliable,
    effect := .trySend, label := label, scope := .intra, occupancy := .ofNat 1,
    repliesInDequeue := false, ingress := true, ingressLegal := some (Affine.ofNat 1), cell := .none }

def trm (t label : String) (p : List Eff) : Transition :=
  { template := t, fromState := "idle", label := label, program := p, toState := "idle",
    acceptsCall := false, release := 1 }

def lossDesc : Description where
  name := "terminate-drops"
  freshNames := true
  templates := [tpl "S" 2 ["idle"] "idle" true, { tpl "W" 2 ["idle"] "idle" true with terminable := true }]
  edges := [ingE "S" "Go"]
  compatibility := .all
  steps := []

def lossImpl : Impl where
  desc := lossDesc
  transitions := [trm "S" "Go" [.send "W" "Start" 0, .send "W" "M" 0],
                  trm "W" "Start" [.internal, .terminate],
                  trm "W" "M" []]

def S : InstId := .core "S"
def W : InstId := .core "W"

def lossActs : List Action :=
  [.ingress S "Go", .recvBulk S, .exec S, .recvBulk W, .exec W, .exec S, .finish W, .exec W]

theorem loss_steps_ok : ((List.range (lossActs.length + 1)).all fun i =>
    (apply lossImpl (nthAct lossActs i) (replayCfg lossImpl lossActs i)).isSome) = true := by decide

theorem loss_quiet : runtimeBusy lossImpl (replayCfg lossImpl lossActs lossActs.length) = false := by decide

theorem loss_tail (i : Nat) (hi : lossActs.length ≤ i) :
    replayCfg lossImpl lossActs i = replayCfg lossImpl lossActs lossActs.length ∧
      runtimeBusy lossImpl (replayCfg lossImpl lossActs i) = false := by
  induction i with
  | zero => simp [lossActs] at hi
  | succ i ih =>
    by_cases hle : lossActs.length ≤ i
    · obtain ⟨heq, hb⟩ := ih hle
      have hact : nthAct lossActs i = .stutter := by simp [nthAct, Nat.not_lt_of_le hle]
      have hb' : runtimeBusy lossImpl (replayCfg lossImpl lossActs lossActs.length) = false := by
        rw [← heq]; exact hb
      rw [replayCfg, hact, apply, heq, hb']
      simp [Option.getD, hb']
    · have heq : i + 1 = lossActs.length := by omega
      simpa [heq] using loss_quiet

theorem loss_is_some (i : Nat) :
    (apply lossImpl (nthAct lossActs i) (replayCfg lossImpl lossActs i)).isSome = true := by
  by_cases hi : i < lossActs.length + 1
  · have hall := loss_steps_ok
    simp only [List.all_eq_true] at hall
    exact hall i (List.mem_range.mpr hi)
  · have hle : lossActs.length ≤ i := by omega
    obtain ⟨_, hb⟩ := loss_tail i hle
    simp [nthAct, Nat.not_lt_of_le hle, apply, hb]

def lossRun : Run lossImpl 0 where
  cfg := replayCfg lossImpl lossActs
  act := nthAct lossActs
  startN := rfl
  start := rfl
  valid := replay_valid lossImpl lossActs loss_is_some

theorem loss_fair : Fair lossRun := by
  have hquiet (j : Nat) (hj : lossActs.length ≤ j) :
      runtimeBusy lossImpl (lossRun.cfg j) = false ∧
        (∀ id, id ∉ (lossRun.cfg j).roster →
          ((lossRun.cfg j).st id).life ≠ .alive ∧ ((lossRun.cfg j).st id).phase = .idle) := by
    obtain ⟨_, hb⟩ := loss_tail j hj
    refine ⟨hb, fun id hid => ?_⟩
    have h := off_idle_reachable lossImpl 0 (lossRun.cfg j) (cfg_reachable lossRun j) id hid
    exact ⟨h.2, h.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a i hf hen
    obtain ⟨hb, hoff⟩ := hquiet (Nat.max i lossActs.length) (Nat.le_max_right _ _)
    exact False.elim (quiet_no_forced lossImpl _ hoff hb a hf (hen _ (Nat.le_max_left _ _)))
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i lossActs.length)
    obtain ⟨hb, hoff⟩ := hquiet j (Nat.le_trans (Nat.le_max_right _ _) hj)
    exact False.elim (quiet_no_forced lossImpl _ hoff hb (.recvBulk s) rfl hen)
  · intro s hio i
    obtain ⟨j, hj, hen⟩ := hio (Nat.max i lossActs.length)
    obtain ⟨hb, hoff⟩ := hquiet j (Nat.le_trans (Nat.le_max_right _ _) hj)
    exact False.elim (quiet_no_forced lossImpl _ hoff hb (.recvPrio s) rfl hen)

theorem m_accepted : ((lossRun.cfg 6).st W).box.map (·.label) = ["M"] := by decide

theorem m_dropped : ((lossRun.cfg 8).st W).box = [] ∧ ((lossRun.cfg 8).st W).life = .dead := by decide

theorem never_received (j : Nat) (hj : 6 ≤ j) : lossRun.act j ≠ .recvBulk W := by
  show nthAct lossActs j ≠ .recvBulk W
  by_cases h : j < lossActs.length
  · have : j = 6 ∨ j = 7 := by simp [lossActs] at h; omega
    rcases this with rfl | rfl <;> decide
  · simp [nthAct, h]

theorem no_drops (hot : Nat → Bool) (k : Nat) : drainDrops lossRun W 6 hot k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne := never_received (6 + k) (by omega)
    simp [drainDrops, ih, hne]

theorem delivered_clause_for_lost :
    (∃ j, 6 ≤ j ∧
      (0 < drainDrops lossRun W 6 (fun t => !((lossRun.cfg t).st W).box.isEmpty) (j - 6) ∨
        ((lossRun.cfg j).st W).box = [])) ∧
    (∀ j, ¬ (0 < drainDrops lossRun W 6 (fun t => !((lossRun.cfg t).st W).box.isEmpty) (j - 6))) := by
  refine ⟨⟨8, by omega, Or.inr m_dropped.1⟩, fun j => ?_⟩
  rw [no_drops]; omega

/-! ## (4) Height-2 chain through a per-peer producer. -/

def ingP : Edge :=
  { ingE "P" "Go" with occupancy := { a := 1, b := 0 }, ingressLegal := some { a := 1, b := 0 } }

def pTpl : Template := { tpl "P" 2 ["idle", "busy"] "idle" true with multiplicity := .perPeer, capacity := { a := 2, b := 2 } }

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

/-- Kernel-checked: a reachable world of a GraphOk ∧ LocalOk instance with a per-peer
actor blocked through a height-2 chain, and a `ChainRun` of two chain steps
(`recvBulk C`, then `recvBulk B`) after which it is no longer `Blocked`. -/
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

end Deadlock.Helen3

#print axioms Deadlock.Helen3.finexec_empty
#print axioms Deadlock.Helen3.blocked_no_stutter
#print axioms Deadlock.Helen3.loss_fair
#print axioms Deadlock.Helen3.delivered_clause_for_lost
#print axioms Deadlock.Helen3.chain_graph_ok
#print axioms Deadlock.Helen3.chain_local
#print axioms Deadlock.Helen3.chain_witness
