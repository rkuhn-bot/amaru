/-
Decidable checks on a finite wait-graph description.

Residual edges are the blocking waits that Lemmas 1–4 do not delete:
non-blocking edges (including a superseding cell or an ingress teardown, once their
side conditions have been accepted) are absent; a blocking send into a mailbox
whose occupancy bound fits its capacity is absent (Lemma 1); a blocking edge that
remains is drawn only toward target states the compatibility relation allows
(Lemma 4). Cross-instance edges are ordinary template edges, so a self-wait on one
template is a self-loop and the acyclicity check is uniform in the instance count.
-/

import Deadlock.Basic

set_option autoImplicit false

namespace Deadlock

inductive Path (E : Node → Node → Bool) : Node → Node → Prop where
  | single {a b : Node} : E a b = true → Path E a b
  | cons {a b c : Node} : E a b = true → Path E b c → Path E a c

def Acyclic (E : Node → Node → Bool) : Prop := ∀ a, ¬ Path E a a

def edgeBool (es : List (Node × Node)) (a b : Node) : Bool :=
  es.any fun e => decide (e.1 = a) && decide (e.2 = b)

theorem List.all_eq_true {α : Type} (p : α → Bool) (xs : List α) :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [List.all]
  | cons a xs ih =>
    rw [List.all_cons, Bool.and_eq_true, ih]
    constructor
    · intro h x hx
      cases hx with
      | head => exact h.1
      | tail _ ht => exact h.2 x ht
    · intro h
      exact ⟨h a (List.Mem.head xs), fun x hx => h x (List.Mem.tail a hx)⟩

theorem List.any_eq_true {α : Type} (p : α → Bool) (xs : List α) :
    xs.any p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [List.any]
  | cons a xs ih =>
    rw [List.any_cons, Bool.or_eq_true, ih]
    constructor
    · intro h
      cases h with
      | inl hp => exact ⟨a, List.Mem.head xs, hp⟩
      | inr h =>
        obtain ⟨x, hx, hp⟩ := h
        exact ⟨x, List.Mem.tail a hx, hp⟩
    · intro h
      obtain ⟨x, hx, hp⟩ := h
      cases hx with
      | head => exact Or.inl hp
      | tail _ ht => exact Or.inr ⟨x, ht, hp⟩

theorem edgeBool_iff (es : List (Node × Node)) (a b : Node) :
    edgeBool es a b = true ↔ (a, b) ∈ es := by
  rw [edgeBool, List.any_eq_true]
  constructor
  · intro h
    obtain ⟨e, he, hp⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    cases hp with
    | intro hl hr =>
      cases e with
      | mk e1 e2 =>
        cases hl
        cases hr
        exact he
  · intro h
    refine ⟨(a, b), h, ?_⟩
    simp

def closePairs (origin prev : Node) : List Node → List (Node × Node)
  | [] => [(prev, origin)]
  | y :: ys => (prev, y) :: closePairs origin y ys

def cyclePairs : List Node → List (Node × Node)
  | [] => []
  | n :: rest => closePairs n n rest

def isCycle (E : Node → Node → Bool) (c : List Node) : Bool :=
  match c with
  | [] => false
  | _ :: _ => (cyclePairs c).all fun p => E p.1 p.2

theorem closePairs_path (E : Node → Node → Bool) (origin prev : Node) (xs : List Node)
    (h : ∀ p ∈ closePairs origin prev xs, E p.1 p.2 = true) :
    Path E prev origin := by
  match xs with
  | [] =>
    exact Path.single (h (prev, origin) (by simp [closePairs]))
  | y :: ys =>
    refine Path.cons (h (prev, y) ?_) (closePairs_path E origin y ys ?_)
    · simp [closePairs]
    · intro p hp
      exact h p (by simp [closePairs, hp])

theorem isCycle_path (E : Node → Node → Bool) (c : List Node) (h : isCycle E c = true) :
    ∃ n, Path E n n := by
  match c with
  | [] => simp [isCycle] at h
  | n :: rest =>
    have hall : (cyclePairs (n :: rest)).all (fun p => E p.1 p.2) = true := by
      simpa [isCycle] using h
    have hmem : ∀ p ∈ closePairs n n rest, E p.1 p.2 = true := by
      intro p hp
      have := (List.all_eq_true (fun q => E q.1 q.2) (cyclePairs (n :: rest))).mp hall p
      exact this (by simpa [cyclePairs] using hp)
    exact ⟨n, closePairs_path E n n rest hmem⟩

theorem path_height_drop (E : Node → Node → Bool) (height : Node → Nat)
    (hok : ∀ a b, E a b = true → height b < height a)
    {a b : Node} (p : Path E a b) : height b < height a := by
  induction p with
  | single hE => exact hok _ _ hE
  | cons hE _ ih => exact Nat.lt_trans ih (hok _ _ hE)

theorem heights_acyclic (E : Node → Node → Bool) (height : Node → Nat)
    (hok : ∀ a b, E a b = true → height b < height a) : Acyclic E := by
  intro a p
  exact Nat.lt_irrefl _ (path_height_drop E height hok p)

def heightOf (hs : List (Node × Nat)) (n : Node) : Nat :=
  (alistGet hs n).getD 0

def heightStrict (hs : List (Node × Nat)) (e : Node × Node) : Bool :=
  match alistGet hs e.1, alistGet hs e.2 with
  | some ha, some hb => decide (hb < ha)
  | _, _ => false

def heightsOkB (es : List (Node × Node)) (hs : List (Node × Nat)) : Bool :=
  es.all (heightStrict hs)

theorem heightStrict_true (hs : List (Node × Nat)) (e : Node × Node)
    (h : heightStrict hs e = true) : heightOf hs e.2 < heightOf hs e.1 := by
  simp only [heightStrict] at h
  cases h1 : alistGet hs e.1 <;> cases h2 : alistGet hs e.2 <;>
    simp [h1, h2, heightOf, Option.getD, decide_eq_true_eq] at h ⊢
  exact h

theorem heightsOkB_mem (es : List (Node × Node)) (hs : List (Node × Nat))
    (hb : heightsOkB es hs = true) :
    ∀ e ∈ es, heightOf hs e.2 < heightOf hs e.1 := by
  induction es with
  | nil =>
    intro e he
    cases he
  | cons e es ih =>
    rw [heightsOkB, List.all_cons, Bool.and_eq_true] at hb
    intro e2 he2
    cases he2 with
    | head => exact heightStrict_true hs e hb.1
    | tail _ ht => exact ih hb.2 e2 ht

theorem heightsOkB_acyclic (es : List (Node × Node)) (hs : List (Node × Nat))
    (hb : heightsOkB es hs = true) : Acyclic (edgeBool es) := by
  refine heights_acyclic (edgeBool es) (heightOf hs) ?_
  intro a b he
  exact heightsOkB_mem es hs hb (a, b) ((edgeBool_iff es a b).mp he)

/-! Compatibility groups. The list is untrusted. A passing check means it contains
the initial tuple and is closed under every listed step and under restart
(and therefore under terminate-and-respawn). It is sufficient, not necessary:
failure means "not provable with this relation". -/

def compatGroups : CompatMode → List CompatGroup
  | .groups gs => gs
  | _ => []

def lookupRole (t : List RoleState) (role : String) : Option String :=
  t.findSome? fun rs => if rs.role = role then some rs.state else none

def tupleMem (allowed : List (List RoleState)) (t : List RoleState) : Bool :=
  allowed.any fun a =>
    t.all (fun rs => lookupRole a rs.role == some rs.state) &&
      a.all (fun rs => lookupRole t rs.role == some rs.state)

def substRole (t : List RoleState) (role state : String) : List RoleState :=
  t.map fun rs => if rs.role = role then { rs with state := state } else rs

def fmtTuple (t : List RoleState) : String :=
  "(" ++ String.intercalate ", " (t.map fun rs => s!"{rs.role}: {rs.state}") ++ ")"

def coStates (g : CompatGroup) (src ss dst : String) : List String :=
  dedup <| g.allowed.filterMap fun tup =>
    if lookupRole tup src == some ss then lookupRole tup dst else none

def listInter (xs ys : List String) : List String :=
  xs.filter fun x => ys.elem x

/-- Partner states that co-occur with `srcState` in every group containing both roles.
Extra groups only remove states, so a hand-written list cannot add a residual edge
the relation does not allow. -/
def groupTargets (gs : List CompatGroup) (src ss dst : String) : List String :=
  match gs.filter fun g => g.roles.elem src && g.roles.elem dst with
  | [] => []
  | g :: rest => rest.foldl (fun acc h => listInter acc (coStates h src ss dst)) (coStates g src ss dst)

/-! Discharge -/

/-- Partner states drawn while `e.src` waits in `e.srcState`. In group mode that is
the intersection of the stored rows. A nonempty outcome landing
(`toNotAdmitted`, `toTimedOut`, `toTimeout`, `toFull`, `toGone`) is not a
separate field of the description: `pairBreaks` requires every substitution
between those states to already be a stored row, and this function then draws
the partner that row names. -/
def targetStates (D : Description) (e : Edge) : List String :=
  match D.compatibility with
  | .all => statesOf D e.dst
  | .explicit ps =>
    dedup <| ps.filterMap fun a =>
      if a.src == e.src && a.srcState == e.srcState && a.dst == e.dst then some a.dstState
      else none
  | .groups gs => groupTargets gs e.src e.srcState e.dst

/-- A blocking send is deleted when Lemma 1 applies. Calls stay: admission may be
credited, but the reply wait is still a residual edge. Non-blocking effects are not waits. -/
def discharged (D : Description) (e : Edge) : Bool :=
  e.kind == .nonBlocking || (e.effect == .send && l1 D e.dst)

def residualEdges (D : Description) : List (Node × Node) :=
  D.edges.foldl (fun acc e =>
    if discharged D e then acc
    else
      let src : Node := { template := e.src, state := e.srcState }
      acc ++ (targetStates D e).map fun st =>
        (src, ({ template := e.dst, state := st } : Node))) []

def allNodes (D : Description) : List Node :=
  dedup <|
    (D.templates.foldl (fun acc t =>
      acc ++ t.states.map fun s => ({ template := t.name, state := s } : Node)) []) ++
    (residualEdges D).foldl (fun acc e => acc ++ [e.1, e.2]) []

/-! Kahn, heights, cycle extraction -/

def indegList (nodes : List Node) (es : List (Node × Node)) : List (Node × Nat) :=
  nodes.map fun n => (n, (es.filter fun e => decide (e.2 = n)).length)

def decAt (xs : List (Node × Nat)) (n : Node) : List (Node × Nat) :=
  xs.map fun (m, k) => if m == n && 0 < k then (m, k - 1) else (m, k)

def enqueueZero (indeg : List (Node × Nat)) (order queue : List Node) (n : Node) : List Node :=
  if alistGet indeg n == some 0 && !order.elem n && !queue.elem n then queue ++ [n] else queue

def kahn (fuel : Nat) (es : List (Node × Node)) (indeg : List (Node × Nat))
    (queue order : List Node) : List Node :=
  match fuel with
  | 0 => order
  | fuel + 1 =>
    match queue with
    | [] => order
    | n :: qs =>
      let outs := es.filter fun e => decide (e.1 = n)
      let indeg' := outs.foldl (fun acc e => decAt acc e.2) indeg
      let order' := order ++ [n]
      let queue' := outs.foldl (fun q e => enqueueZero indeg' order' q e.2) qs
      kahn fuel es indeg' queue' order'

def topo (nodes : List Node) (es : List (Node × Node)) : List Node :=
  let indeg := indegList nodes es
  let queue := nodes.filter fun n => alistGet indeg n == some 0
  kahn nodes.length es indeg queue []

def assignHeights (order : List Node) (es : List (Node × Node)) : List (Node × Nat) :=
  order.foldr (fun n acc =>
    let succs := es.filterMap fun e => if e.1 == n then some e.2 else none
    let hs := succs.filterMap fun b => alistGet acc b
    let mx := hs.foldl Nat.max 0
    let h := if succs.isEmpty then 0 else mx + 1
    (n, h) :: acc) []

def listSubset (xs ys : List Node) : Bool :=
  xs.all (fun n => ys.elem n)

def sameNodes (xs ys : List Node) : Bool :=
  listSubset xs ys && listSubset ys xs

def prefixBefore (cur : Node) : List Node → List Node
  | [] => []
  | x :: xs => if x == cur then [] else x :: prefixBefore cur xs

def predIn (es : List (Node × Node)) (remaining : List Node) (n : Node) : Option Node :=
  es.findSome? fun e => if decide (e.2 = n) && remaining.elem e.1 then some e.1 else none

def walkCycle (es : List (Node × Node)) (remaining : List Node) : Nat → Node → List Node → Option (List Node)
  | 0, _, _ => none
  | fuel + 1, cur, stack =>
    if stack.elem cur then
      some ((cur :: prefixBefore cur stack).reverse)
    else
      match predIn es remaining cur with
      | none => none
      | some p => walkCycle es remaining fuel p (cur :: stack)

def findCycle (nodes : List Node) (es : List (Node × Node)) : Option (List Node) :=
  let order := topo nodes es
  let remaining := nodes.filter fun n => !order.elem n
  remaining.findSome? fun start =>
    walkCycle es remaining (remaining.length + 1) start []

def verifiedCycle (nodes : List Node) (es : List (Node × Node)) : Option (List Node) :=
  match findCycle nodes es with
  | none => none
  | some c => if isCycle (edgeBool es) c then some c else none

inductive Cert where
  | ok (hs : List (Node × Nat))
  | cycle (c : List Node)
  | uncertified
  deriving Repr

def heightsGood (nodes : List Node) (es : List (Node × Node)) : Bool :=
  let order := topo nodes es
  sameNodes order nodes && heightsOkB es (assignHeights order es)

def certify (nodes : List Node) (es : List (Node × Node)) : Cert :=
  let order := topo nodes es
  let hs := assignHeights order es
  if heightsGood nodes es then
    .ok hs
  else
    match verifiedCycle nodes es with
    | some c => .cycle c
    | none => .uncertified

theorem verifiedCycle_isCycle (nodes : List Node) (es : List (Node × Node)) (c : List Node)
    (h : verifiedCycle nodes es = some c) : isCycle (edgeBool es) c = true := by
  simp only [verifiedCycle] at h
  cases hf : findCycle nodes es with
  | none => simp [hf] at h
  | some c0 =>
    simp only [hf] at h
    cases hic : isCycle (edgeBool es) c0
    · simp [hic] at h
    · simp [hic] at h
      cases h
      exact hic

theorem certify_ok_heights (nodes : List Node) (es : List (Node × Node)) (hs : List (Node × Nat))
    (h : certify nodes es = .ok hs) : heightsOkB es hs = true := by
  unfold certify at h
  cases hgb : heightsGood nodes es with
  | true =>
    simp only [hgb, ite_true] at h
    cases h
    have hg : heightsGood nodes es = true := hgb
    simp only [heightsGood, Bool.and_eq_true] at hg
    exact hg.2
  | false =>
    simp only [hgb, ite_false] at h
    cases hv : verifiedCycle nodes es <;> simp [hv] at h

theorem certify_cycle_real (nodes : List Node) (es : List (Node × Node)) (c : List Node)
    (h : certify nodes es = .cycle c) : isCycle (edgeBool es) c = true := by
  unfold certify at h
  cases hgb : heightsGood nodes es with
  | true =>
    simp only [hgb, ite_true] at h
    cases h
  | false =>
    simp only [hgb, ite_false] at h
    cases hv : verifiedCycle nodes es with
    | none => simp [hv] at h
    | some _ =>
      simp [hv] at h
      cases h
      exact verifiedCycle_isCycle nodes es c hv

/-! Boolean obligations -/

def nameFails (D : Description) : List String :=
  let names := D.templates.map (·.name)
  if names.length == (dedup names).length then [] else ["fail: duplicate template name"]

def stateFails (D : Description) : List String :=
  D.templates.filterMap fun t =>
    if t.states.isEmpty then some s!"fail: template {t.name} has no states"
    else if !(t.states.elem t.initial) then some s!"fail: template {t.name} initial state is not declared"
    else if t.states.length != (dedup t.states).length then some s!"fail: template {t.name} has a duplicate state"
    else none

def endpointFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if !(hasTemplate D e.src) then some s!"fail: edge {e.label} leaves unknown template {e.src}"
    else if !(stateMem D e.src e.srcState) then
      some s!"fail: edge {e.label} leaves unknown state {e.src}/{e.srcState}"
    else if !(hasTemplate D e.dst) then some s!"fail: edge {e.label} enters unknown template {e.dst}"
    else none

def kindOk (e : Edge) : Bool :=
  match e.effect, e.kind with
  | .send, .blocking => true
  | .call, .blocking => true
  | .trySend, .nonBlocking => true
  | .reply, .nonBlocking => true
  | .selfSchedule, .nonBlocking => true
  | .cell, .nonBlocking => true
  | .internal, .nonBlocking => true
  | .peer, .nonBlocking => true
  | _, _ => false

/-- A reliable `trySend` that is not ingress drops when the mailbox is full.
Only a superseding edge, or an ingress edge delivered by `Action.ingress`, may do that. -/
def reliableTryFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if e.ingress && !(e.src == e.dst) then
      some s!"fail: ingress edge {e.label} must be a self-edge; a program send is not ingress"
    else if e.effect == .trySend && e.reliability == .reliable && !e.ingress then
      some s!"fail: reliable trySend {e.label} may be dropped; mark a self-edge ingress or use superseding"
    else none

def kindFails (D : Description) : List String :=
  (D.edges.filterMap fun e =>
    if kindOk e then none
    else some s!"fail: edge {e.label} mixes {reprStr e.effect} with {reprStr e.kind}") ++
    reliableTryFails D

def scopeOk (D : Description) (e : Edge) : Bool :=
  match templateOf D e.src, templateOf D e.dst, e.scope with
  | some _, some _, .intra => true
  | some s, some t, .cross => decide (s.multiplicity = .perPeer) && decide (t.multiplicity = .perPeer)
  | some s, some t, .coreInst =>
      (decide (s.multiplicity = .one) && decide (t.multiplicity = .perPeer)) ||
        (decide (s.multiplicity = .perPeer) && decide (t.multiplicity = .one))
  | _, _, _ => false

def scopeFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if scopeOk D e then none
    else some s!"fail: edge {e.label} has scope inconsistent with template multiplicity"

def missingFlags (c : CellFlags) : List String :=
  (if c.singleWriter then [] else ["singleWriter"]) ++
  (if c.orderMonotone then [] else ["orderMonotone"]) ++
  (if c.noPerMessageObligation then [] else ["noPerMessageObligation"]) ++
  (if c.visibility then [] else ["visibility"]) ++
  (if c.readPoints then [] else ["readPoints"]) ++
  (if c.idempotent then [] else ["idempotent"]) ++
  (if c.dirtyBit then [] else ["dirtyBit"])

def cellFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if e.reliability != .superseding then none
    else if e.effect != .cell || e.kind != .nonBlocking then
      some s!"fail: superseding edge {e.src}/{e.srcState} -[{e.label}]-> {e.dst} must be a non-blocking cell write"
    else
      let missing := missingFlags e.cell
      if missing.isEmpty then none
      else some s!"fail: superseding edge {e.label} misses cell conditions {String.intercalate ", " missing}"

def ingressFails (D : Description) : List String :=
  (enum D.edges).filterMap fun (i, e) =>
    if !e.ingress then none
    else if e.effect != .trySend || e.kind != .nonBlocking then
      some s!"fail: ingress edge {e.label} must be a non-blocking try_send"
    else
      match e.ingressLegal, templateOf D e.dst with
      | none, _ => some s!"fail: ingress edge {e.label} has no legal outstanding bound"
      | _, none => some s!"fail: ingress edge {e.label} enters unknown template {e.dst}"
      | some legal, some t =>
        let used := legal.add (occExcept D e.dst i)
        if Affine.leB used t.capacity then none
        else some s!"fail: overflowing mailbox\n  ingress {e.dst}: legal+others {used.toString} > capacity {t.capacity.toString}"

def allowedFails (D : Description) : List String :=
  match D.compatibility with
  | .all => []
  | .explicit ps =>
    ps.filterMap fun a =>
      if stateMem D a.src a.srcState && stateMem D a.dst a.dstState then none
      else some s!"fail: compatibility pair {a.src}/{a.srcState} ~ {a.dst}/{a.dstState} mentions an unknown state"
  | .groups _ => []

def stepBreaks (g : CompatGroup) (step : CompatStep) (fromAny : Bool) : List String :=
  g.allowed.filterMap fun tup =>
    if !(g.roles.elem step.template) then none
    else
      match lookupRole tup step.template with
      | none => none
      | some s =>
        if !fromAny && s != step.fromState then none
        else
          let post := substRole tup step.template step.toState
          if tupleMem g.allowed post then none
          else
            some s!"fail: compatibility broken by transition {step.template} {s} -> {step.toState} [{step.label}]\n  pre: {fmtTuple tup}\n  post: {fmtTuple post}"

/-- Substituting `template` from any state in `states` to any other state in
`states` must stay inside the stored rows. The local check passes one
transition's landing set: `toState` together with every nonempty outcome field. -/
def pairBreaks (g : CompatGroup) (template : String) (states : List String) (label : String) : List String :=
  if g.roles.elem template then
    states.flatMap fun s0 =>
      states.flatMap fun s1 =>
        if s0 == s1 then []
        else stepBreaks g { template := template, fromState := s0, toState := s1, label := label } false
  else []

def groupWellformed (D : Description) (g : CompatGroup) : List String :=
  if g.roles.length < 2 then [s!"fail: compatibility group {g.name} needs at least two roles"]
  else if g.roles.length != (dedup g.roles).length then [s!"fail: compatibility group {g.name} repeats a role"]
  else
    let unknown := g.roles.filter fun r => !(hasTemplate D r)
    if !unknown.isEmpty then
      [s!"fail: compatibility group {g.name} mentions unknown template {unknown.head?.getD "?"}"]
    else
      let perPeer := g.roles.filter fun r =>
        match templateOf D r with
        | some t => t.multiplicity == .perPeer
        | none => false
      if !perPeer.isEmpty then
        [s!"fail: compatibility group {g.name} role {perPeer.head?.getD "?"} has multiplicity perPeer; this check does not certify every instance count N"]
      else
        let terminable := g.roles.filter fun r =>
          match templateOf D r with
          | some t => t.terminable
          | none => false
        if !terminable.isEmpty then
          [s!"fail: compatibility group {g.name} role {terminable.head?.getD "?"} is terminable; a dead role is not a state in the tuple"]
        else
        g.allowed.filterMap fun tup =>
          if tup.length != g.roles.length then
            some s!"fail: compatibility group {g.name} tuple {fmtTuple tup} does not cover every role"
          else if g.roles.any fun r => !(tup.any fun rs => rs.role == r) then
            some s!"fail: compatibility group {g.name} tuple {fmtTuple tup} does not cover every role"
          else if tup.any fun rs => !(stateMem D rs.role rs.state) then
            some s!"fail: compatibility group {g.name} tuple {fmtTuple tup} mentions an unknown state"
          else none

def initialTuple (D : Description) (g : CompatGroup) : List RoleState :=
  g.roles.filterMap fun r =>
    match templateOf D r with
    | some t => some { role := r, state := t.initial }
    | none => none

def restartSteps (D : Description) (g : CompatGroup) : List CompatStep :=
  g.roles.filterMap fun r =>
    match templateOf D r with
    | some t => some { template := r, fromState := t.initial, toState := t.initial, label := "restart" }
    | none => none

def groupClosure (D : Description) (g : CompatGroup) : List String :=
  if !(groupWellformed D g).isEmpty then []
  else
    let init := initialTuple D g
    let initFail :=
      if tupleMem g.allowed init then []
      else [s!"fail: compatibility group {g.name} rejects the initial tuple\n  tuple: {fmtTuple init}"]
    -- Only real typestate steps. In-place restart is not a step of this semantics;
    -- a dead role leaves the product instead of being read as `initial`.
    initFail ++ D.steps.flatMap (stepBreaks g · false)

def uncoveredEdges (D : Description) (gs : List CompatGroup) : List String :=
  D.edges.filterMap fun e =>
    if e.kind != .blocking then none
    else if gs.any fun g => g.roles.elem e.src && g.roles.elem e.dst then none
    else some s!"fail: blocking edge {e.label} from {e.src} to {e.dst} is not in any compatibility group"

def compatFails (D : Description) : List String :=
  match D.compatibility with
  | .all => []
  | .explicit _ =>
    ["fail: compatibility mode explicit is not an invariance check; use groups"]
  | .groups gs =>
    gs.flatMap (fun g => groupWellformed D g ++ groupClosure D g) ++ uncoveredEdges D gs

/-- A listed cell write is a non-blocking cell edge with the same endpoints and label. -/
def declaredCell (D : Description) (src ss dst label : String) : Bool :=
  D.edges.any fun e =>
    e.src == src && e.srcState == ss && e.dst == dst && e.effect == .cell &&
      e.kind == .nonBlocking && e.label == label

def cellEffectFails (D : Description) : List String :=
  D.cellEffects.filterMap fun w =>
    if declaredCell D w.src w.srcState w.dst w.label then none
    else some s!"fail: cell effect {w.src}/{w.srcState} -[{w.label}]-> {w.dst} is not a declared cell edge"

def structLines (D : Description) : List String :=
  nameFails D ++ stateFails D ++ endpointFails D ++ kindFails D ++ scopeFails D ++
    cellFails D ++ cellEffectFails D ++ ingressFails D ++ allowedFails D ++ compatFails D

def priorityFails (D : Description) : List String :=
  D.templates.filterMap fun t =>
    if Affine.leB t.priorityBound t.priorityCapacity then none
    else some s!"fail: priority lane {t.name}: bound {t.priorityBound.toString} > capacity {t.priorityCapacity.toString}"

def replyFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if e.effect == .call && !e.repliesInDequeue then
      some s!"fail: call {e.src} -[{e.label}]-> {e.dst} is not answered in the dequeue transition"
    else none

/-- Shared subtree name, or empty when `name` is a lone actor. -/
def templateSubtree (D : Description) (name : String) : String :=
  match templateOf D name with
  | some t => t.subtree
  | none => ""

/-- Both roles name the same nonempty subtree, so one kill ends both. -/
def sameSubtree (D : Description) (a b : String) : Bool :=
  let s := templateSubtree D a
  s != "" && s == templateSubtree D b

/-- `name` belongs to a subtree that has a timeout role. -/
def subtreeKillable (D : Description) (name : String) : Bool :=
  let s := templateSubtree D name
  s != "" && D.templates.any fun t => t.subtree == s && t.timeoutKills

/-- A pool child addressed by its core supervisor. The core may send to and
call that child: the child's shutdown refunds the message. -/
def coreSupervisedPool (D : Description) (src dst : String) : Bool :=
  match templateOf D dst, templateOf D src with
  | some child, some parent =>
    child.slots != 0 && child.multiplicity == .perPeer &&
      supNamed child.supervisor src && parent.multiplicity == .one
  | _, _ => false

def callTermFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if e.effect != .call then none
    else
      match templateOf D e.dst with
      | none => some s!"fail: call {e.label} targets unknown template {e.dst}"
      | some t =>
        -- A call may enter a terminable per-peer inside that peer's subtree, or a
        -- pool child of the calling core. A core is not a terminable target: the
        -- flag is rejected, and the core's terminate crashes the node.
        if t.terminable && t.multiplicity != .one && !sameSubtree D e.src e.dst &&
            !coreSupervisedPool D e.src e.dst then
          some s!"fail: call {e.label} targets terminable template {e.dst}"
        else none

/-- Templates that may interact with `name`. In group mode that is the shared
compat group. In explicit mode it is the templates named together in an allowed
pair. In `all` mode every template can co-occur, so the cohort is the roster. -/
def cohortOf (D : Description) (name : String) : List String :=
  match D.compatibility with
  | .all => D.templates.map (·.name)
  | .explicit ps =>
    dedup (name :: ps.foldl (fun acc a =>
      if a.src == name || a.dst == name then acc ++ [a.src, a.dst] else acc) [])
  | .groups gs =>
    dedup (name :: gs.foldl (fun acc g =>
      if g.roles.elem name then acc ++ g.roles else acc) [])

/-- A timed peer wait on `name`: the template is not `untimedPeer`, and some
edge is a `peer` effect. `finish` is the timeout. -/
def hasTimedPeer (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | none => false
  | some t => !t.untimedPeer && D.edges.any fun e => e.src == name && e.effect == .peer

/-- A timed peer in `name`'s subtree whose timeout kills that subtree. The kill,
not a sibling's `finish`, is what ends a chain parked on an untimed member. -/
def hasKillingPeer (D : Description) (name : String) : Bool :=
  let s := templateSubtree D name
  s != "" && D.templates.any fun t =>
    t.subtree == s && t.timeoutKills && hasTimedPeer D t.name

/-- An untimed peer ends a chain only when a timed peer in its subtree can end
that chain by killing it. A cohort timed peer that merely `finish`es does not. -/
def timedCohortEnds (D : Description) (name : String) : Bool :=
  hasKillingPeer D name

/-- An untimed peer with no timed cohort cut. `finish` stays disabled, so the
wait is a legitimate end of its own chain and must not sit inside another
actor's chain or on a permanent mailbox. -/
def templatePure (D : Description) (name : String) : Bool :=
  match templateOf D name with
  | none => false
  | some t => t.untimedPeer && !timedCohortEnds D name

def pureKillMsg (name : String) : String :=
  s!"fail: {name} is a pure untimed peer and its own timeout does not kill the subtree"

/-- A per-peer supervisor of the same subtree, or a multiplicity-one core. -/
def supervisorInSubtree (D : Description) (t : Template) : Bool :=
  match t.supervisor with
  | none => false
  | some name =>
    match templateOf D name with
    | none => false
    | some s =>
      (s.multiplicity == .one) ||
        (s.multiplicity == .perPeer && s.subtree == t.subtree && s.name != t.name)

/-- How many templates of `sub` name no supervisor. -/
def rootCount (D : Description) (sub : String) : Nat :=
  (D.templates.filter fun t => t.subtree == sub && t.supervisor.isNone).length

/-- The first template of `sub` that names no supervisor. The failure is
reported on that one, so a subtree is not listed twice. -/
def firstRoot (D : Description) (sub : String) : Option String :=
  (D.templates.find? fun t => t.subtree == sub && t.supervisor.isNone).map (·.name)

/-- A supervised child with an empty label. Terminating it while the parent is
alive crashes: there is no handler to deliver. -/
def missingTombstone (t : Template) : Option String :=
  if t.supervisor.isSome && t.tombstone == "" then
    some s!"fail: {t.name} has a supervisor and no tombstone"
  else none

/-- A nonempty subtree is a per-peer cohort with at most one unsupervised
template. That template is the scheduler root: it takes a fresh subtree key,
and a second root would not share it, so a send between them would not
resolve. A named supervisor is a multiplicity-one core or a per-peer stage of
the same subtree. A pool (`slots` > 0) may name a core supervisor and no
subtree: the core births it by slot. The step relation does not require every
member to be terminable, and it does not require a `timeoutKills` role: any
stage may `terminate`, and the tombstone goes to the immediate supervisor.
`timeoutKills` on a template with no subtree is still rejected: the flag names
a subtree kill the template does not belong to. -/
def subtreeEntry (D : Description) (t : Template) : Option String :=
  if t.slots != 0 && (t.multiplicity != .perPeer || t.supervisor.isNone) then
    some s!"fail: pool {t.name} is a per-peer template with a supervisor"
  else if t.slots != 0 then
    match t.supervisor with
    | some name =>
      match templateOf D name with
      | some s =>
        if s.multiplicity != .one then
          some s!"fail: slots must be 0 under a per-peer parent"
        else if t.subtree != "" && !(supervisorInSubtree D t) then
          some s!"fail: subtree {t.subtree} supervisor {name} is not in the subtree"
        else missingTombstone t
      | none => some s!"fail: pool {t.name} names unknown supervisor {name}"
    | none => some s!"fail: pool {t.name} names unknown supervisor none"
  else if t.subtree == "" then
    if t.supervisor.isSome then some s!"fail: {t.name} names a supervisor without a subtree"
    else if t.timeoutKills then some s!"fail: {t.name} sets timeoutKills without a subtree"
    else if templatePure D t.name then some (pureKillMsg t.name)
    else none
  else if t.multiplicity != .perPeer then
    some s!"fail: subtree {t.subtree} member {t.name} is not per-peer"
  else if t.supervisor.isSome && !supervisorInSubtree D t then
    some s!"fail: subtree {t.subtree} supervisor {supText t.supervisor} is not in the subtree"
  else if t.supervisor.isNone && decide (rootCount D t.subtree > 1) &&
      firstRoot D t.subtree == some t.name then
    some s!"fail: subtree {t.subtree} has more than one unsupervised root"
  else missingTombstone t

/-- A multiplicity-one template is not a subtree member. The entry is a pool
failure when it has slots, and a "not per-peer" failure when it does not. -/
theorem subtreeEntry_not_one (D : Description) (t : Template)
    (hne : t.subtree ≠ "") (hone : t.multiplicity = .one) :
    subtreeEntry D t ≠ none := by
  unfold subtreeEntry
  have hsub : (t.subtree == "") = false := by simpa using hne
  have hmult : (t.multiplicity != .perPeer) = true := by
    rw [hone]; decide
  by_cases hs : (t.slots != 0) = true
  · simp [hs, hmult]
  · simp [hs, hsub, hmult]

/-- A supervised template that passes `subtreeEntry` names a tombstone.
`missingTombstone` is the last check on every arm that allows a supervisor. -/
theorem missingTombstone_ne (t : Template) (name : String)
    (h : missingTombstone t = none) (hsup : t.supervisor = some name) :
    t.tombstone ≠ "" := by
  have hsome : t.supervisor.isSome = true := by simp [hsup]
  unfold missingTombstone at h
  by_cases hempty : (t.tombstone == "") = true
  · simp [hsome, hempty] at h
  · intro heq
    apply hempty
    simp [heq]

theorem subtreeEntry_tombstone (D : Description) (t : Template) (name : String)
    (h : subtreeEntry D t = none) (hsup : t.supervisor = some name) :
    t.tombstone ≠ "" := by
  unfold subtreeEntry at h
  simp only [hsup] at h
  split at h
  · simp at h
  · split at h
    · split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · exact missingTombstone_ne t name h hsup
      · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · exact missingTombstone_ne t name h hsup

/-- `terminable` names a per-peer shutdown. A multiplicity-one template that
sets it is rejected: every core may terminate, and that step crashes the node. -/
def coreFlagFails (D : Description) : List String :=
  D.templates.filterMap fun t =>
    if t.multiplicity == .one && t.terminable then
      some s!"fail: core {t.name} sets terminable; a core terminate crashes the node"
    else none

def subtreeFails (D : Description) : List String :=
  D.templates.filterMap (subtreeEntry D) ++ coreFlagFails D

def pureTermMsg (name : String) : String :=
  s!"fail: template {name} is an untimed peer end and is not terminable; a permanent mailbox would stall with the peer"

def cellPureMsg (dst label : String) : String :=
  s!"fail: cell {label} wakes {dst}, whose untimed peer has no timed cut in the cohort"

def interiorMsg (src dst : String) : String :=
  s!"fail: {src} depends on {dst}, whose untimed peer wait is interior and no timed peer in the cohort can end the chain"

/-- A pure untimed per-peer is terminable. Nothing forces it to leave the peer
wait, so reliable mail on it would never be received. A core is not this peer:
`subtreeEntry` rejects a pure core, and a core may not set `terminable`. -/
def pureTermFails (D : Description) : List String :=
  D.templates.filterMap fun t =>
    if t.multiplicity != .one && templatePure D t.name && !t.terminable then
      some (pureTermMsg t.name)
    else none

/-- A pure untimed template is not a cell reader. A wake would sit on the
priority lane for as long as the peer stays silent. -/
def cellPureFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if e.effect == .cell && templatePure D e.dst then some (cellPureMsg e.dst e.label) else none

/-- A blocking send or a call makes the source depend on the destination. An
untimed peer there is interior to the source's chain. It is allowed only when
`timedCohortEnds`: a timed peer in the same subtree kills that subtree, and the
kill is what ends the chain. -/
def interiorFails (D : Description) : List String :=
  D.edges.filterMap fun e =>
    if (e.kind == .blocking || e.effect == .call) = false then none
    else
      match templateOf D e.dst with
      | none => none
      | some t =>
        if t.untimedPeer && !timedCohortEnds D e.dst then some (interiorMsg e.src e.dst) else none

/-- Untimed peer waits are allowed. `peerFails` rejects three placements: a pure
untimed per-peer that is not terminable, a cell wake of a pure untimed template,
and a blocking send or call onto an untimed template that no subtree kill can
end. The last of those is the interior wait. A timed peer whose timeout kills
the subtree is the cut that makes the dependency legal. -/
def peerFails (D : Description) : List String :=
  pureTermFails D ++ cellPureFails D ++ interiorFails D

def overflowFails (D : Description) : List String :=
  D.templates.filterMap fun t =>
    if t.mustFit && !(Affine.leB (totalOcc D t.name) t.capacity) then
      some s!"  mailbox {t.name}: occupancy {(totalOcc D t.name).toString} > capacity {t.capacity.toString}"
    else none

def freshFails (D : Description) : List String :=
  if D.freshNames then [] else ["fail: freshNames is false (re-created actors must not reuse a mailbox name)"]

inductive Issue where
  | text (s : String)
  | cycle (c : List Node)
  deriving Repr

def certifyOf (D : Description) : Cert :=
  certify (allNodes D) (residualEdges D)

def acyclicB (D : Description) : Bool :=
  match certifyOf D with
  | .ok _ => true
  | _ => false

def optText (ok : Bool) (msg : String) : List Issue :=
  if ok then [] else [Issue.text msg]

def certHead (D : Description) : Issue :=
  match certifyOf D with
  | .cycle c => Issue.cycle c
  | .ok _ => Issue.text "fail: internal certificate"
  | .uncertified => Issue.text "fail: residual graph was not certified acyclic"

def certIssue (D : Description) : List Issue :=
  if acyclicB D then [] else [certHead D]

def issues (D : Description) : List Issue :=
  optText (structLines D).isEmpty (String.intercalate "\n" (structLines D)) ++
  optText (freshFails D).isEmpty (String.intercalate "\n" (freshFails D)) ++
  optText (priorityFails D).isEmpty (String.intercalate "\n" (priorityFails D)) ++
  optText (replyFails D).isEmpty (String.intercalate "\n" (replyFails D)) ++
  optText (callTermFails D).isEmpty (String.intercalate "\n" (callTermFails D)) ++
  optText (peerFails D).isEmpty (String.intercalate "\n" (peerFails D)) ++
  optText (subtreeFails D).isEmpty (String.intercalate "\n" (subtreeFails D)) ++
  certIssue D ++
  optText (overflowFails D).isEmpty ("fail: overflowing mailbox\n" ++ String.intercalate "\n" (overflowFails D))

def checkBool (D : Description) : Bool :=
  (structLines D).isEmpty && (freshFails D).isEmpty && (priorityFails D).isEmpty &&
    (replyFails D).isEmpty && (callTermFails D).isEmpty && (peerFails D).isEmpty &&
    (subtreeFails D).isEmpty && acyclicB D && (overflowFails D).isEmpty

def nodeStr (n : Node) : String := s!"({n.template}, {n.state})"

def cycleStr (c : List Node) : String :=
  String.intercalate " -> " <|
    (c.map nodeStr) ++ match c.head? with
      | some h => [nodeStr h]
      | none => []

def issueStr : Issue → String
  | .text s => s
  | .cycle c => "fail: residual cycle\n  " ++ cycleStr c

def render (D : Description) : String :=
  if checkBool D then
    "pass"
  else
    let msg := String.intercalate "\n" ((issues D).map issueStr)
    if msg == "pass" then "fail: uncertified" else msg

/-! What a passing check guarantees. -/

structure GraphOk (D : Description) : Prop where
  struct : structLines D = []
  fresh : freshFails D = []
  priority : priorityFails D = []
  replies : replyFails D = []
  lifecycle : callTermFails D = []
  peers : peerFails D = []
  subtrees : subtreeFails D = []
  acyclic : Acyclic (edgeBool (residualEdges D))
  /-- A concrete rank witnessing acyclicity: every residual edge drops the rank. -/
  ranked : ∃ hs : List (Node × Nat), heightsOkB (residualEdges D) hs = true
  credit : overflowFails D = []

theorem bool_and_parts (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem isEmpty_true {α : Type} (xs : List α) (h : xs.isEmpty = true) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => simp [List.isEmpty] at h

theorem acyclicB_heights (D : Description) (h : acyclicB D = true) :
    ∃ hs, certifyOf D = .ok hs ∧ heightsOkB (residualEdges D) hs = true := by
  unfold acyclicB at h
  cases hc : certifyOf D with
  | ok hs =>
    have hcert : certify (allNodes D) (residualEdges D) = Cert.ok hs := by
      simpa [certifyOf] using hc
    refine ⟨hs, ?_, certify_ok_heights _ _ _ hcert⟩
    simpa [certifyOf] using hcert
  | cycle _ => simp [hc] at h
  | uncertified => simp [hc] at h

theorem checkBool_sound (D : Description) (h : checkBool D = true) : GraphOk D := by
  simp only [checkBool] at h
  obtain ⟨h8, hO⟩ := bool_and_parts _ _ h
  obtain ⟨h7, hA⟩ := bool_and_parts _ _ h8
  obtain ⟨h6, hSub⟩ := bool_and_parts _ _ h7
  obtain ⟨h5, hE⟩ := bool_and_parts _ _ h6
  obtain ⟨h4, hL⟩ := bool_and_parts _ _ h5
  obtain ⟨h3, hR⟩ := bool_and_parts _ _ h4
  obtain ⟨h2, hP⟩ := bool_and_parts _ _ h3
  obtain ⟨hS, hF⟩ := bool_and_parts _ _ h2
  obtain ⟨hs, -, hHeights⟩ := acyclicB_heights D hA
  exact {
    struct := isEmpty_true _ hS
    fresh := isEmpty_true _ hF
    priority := isEmpty_true _ hP
    replies := isEmpty_true _ hR
    lifecycle := isEmpty_true _ hL
    peers := isEmpty_true _ hE
    subtrees := isEmpty_true _ hSub
    acyclic := heightsOkB_acyclic _ _ hHeights
    ranked := ⟨hs, hHeights⟩
    credit := isEmpty_true _ hO
  }

theorem render_pass_iff (D : Description) : render D = "pass" ↔ checkBool D = true := by
  cases hk : checkBool D with
  | true => simp [render, hk]
  | false =>
    simp only [render, hk, Bool.false_eq_true, ite_false]
    by_cases hm : (String.intercalate "\n" ((issues D).map issueStr)) == "pass"
    · simp [hm]
    · simp [hm]
      intro hEq
      apply hm
      simpa [beq_iff_eq] using hEq

theorem cycle_not_optText (ok : Bool) (msg : String) (c : List Node) :
    Issue.cycle c ∉ optText ok msg := by
  cases ok <;> simp [optText]

theorem certHead_cycle (D : Description) (c : List Node) (h : certHead D = Issue.cycle c) :
    certifyOf D = .cycle c := by
  unfold certHead at h
  cases hc : certifyOf D with
  | ok _ => simp [hc] at h
  | cycle c' =>
    simp [hc] at h ⊢
    cases h
    rfl
  | uncertified => simp [hc] at h

theorem mem_singleton_eq {α : Type} {a b : α} (h : a ∈ [b]) : a = b := by
  cases h with
  | head => rfl
  | tail _ ht => cases ht

theorem certify_of_cycle (D : Description) (c : List Node) (h : Issue.cycle c ∈ issues D) :
    certifyOf D = .cycle c := by
  simp only [issues] at h
  have peel : Issue.cycle c ∈ certIssue D := by
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · rcases List.mem_append.mp h with h | h
                · rcases List.mem_append.mp h with h | h
                  · exact absurd h (cycle_not_optText _ _ _)
                  · exact absurd h (cycle_not_optText _ _ _)
                · exact absurd h (cycle_not_optText _ _ _)
              · exact absurd h (cycle_not_optText _ _ _)
            · exact absurd h (cycle_not_optText _ _ _)
          · exact absurd h (cycle_not_optText _ _ _)
        · exact absurd h (cycle_not_optText _ _ _)
      · exact h
    · exact absurd h (cycle_not_optText _ _ _)
  cases hac : acyclicB D with
  | true =>
    simp [certIssue, hac] at peel
  | false =>
    have peel' : Issue.cycle c ∈ [certHead D] := by
      simpa [certIssue, hac] using peel
    exact certHead_cycle D c (mem_singleton_eq peel').symm

theorem listInter_elem (xs ys : List String) (x : String) :
    x ∈ listInter xs ys ↔ x ∈ xs ∧ ys.elem x = true := by
  simp [listInter, List.mem_filter, List.elem_iff]

theorem foldl_inter_spec (src ss dst : String) (rest : List CompatGroup) (acc : List String) (ds : String)
    (h : ds ∈ rest.foldl (fun acc h => listInter acc (coStates h src ss dst)) acc) :
    ds ∈ acc ∧ ∀ g ∈ rest, (coStates g src ss dst).elem ds = true := by
  induction rest generalizing acc with
  | nil =>
    simp at h
    exact ⟨h, fun _ hg => by cases hg⟩
  | cons g gs ih =>
    simp only [List.foldl_cons] at h
    have ih' := ih _ h
    refine ⟨?_, ?_⟩
    · exact (listInter_elem acc (coStates g src ss dst) ds).mp ih'.1 |>.1
    · intro g' hg
      cases hg with
      | head =>
        exact (listInter_elem acc (coStates g src ss dst) ds).mp ih'.1 |>.2
      | tail _ ht =>
        exact ih'.2 g' ht

/-- A residual target drawn from a group relation co-occurs with the source state
in every group that contains both roles. -/
theorem groupTargets_cooccur (gs : List CompatGroup) (src ss dst ds : String)
    (h : ds ∈ groupTargets gs src ss dst) (g : CompatGroup)
    (hg : g ∈ gs) (hs : g.roles.elem src = true) (hd : g.roles.elem dst = true) :
    (coStates g src ss dst).elem ds = true := by
  have hbool : (g.roles.elem src && g.roles.elem dst) = true := by
    rw [hs, hd]
    rfl
  have hg' : g ∈ gs.filter fun g => g.roles.elem src && g.roles.elem dst :=
    List.mem_filter.mpr ⟨hg, hbool⟩
  unfold groupTargets at h
  cases hh : gs.filter fun g => g.roles.elem src && g.roles.elem dst with
  | nil =>
    rw [hh] at hg'
    cases hg'
  | cons g0 rest =>
    rw [hh] at h
    have hmem := foldl_inter_spec src ss dst rest (coStates g0 src ss dst) ds h
    have hg'' : g = g0 ∨ g ∈ rest := by
      have : g ∈ g0 :: rest := by
        rw [hh] at hg'
        exact hg'
      simpa [List.mem_cons] using this
    cases hg'' with
    | inl heq =>
      subst heq
      exact List.elem_iff.mpr hmem.1
    | inr hrest =>
      exact hmem.2 g hrest

theorem issue_cycle_real (D : Description) (c : List Node) (h : Issue.cycle c ∈ issues D) :
    ∃ n, Path (edgeBool (residualEdges D)) n n := by
  have hc := certify_of_cycle D c h
  have his := certify_cycle_real (allNodes D) (residualEdges D) c (by simpa [certifyOf] using hc)
  exact isCycle_path _ c his

end Deadlock
