import Deadlock.Occupy

set_option autoImplicit false

namespace Deadlock

/-! Decidable local checks. These are what `LocalOk` hands to the invariant. -/

def pairAllowed (D : Description) (src ss dst ds : String) : Bool :=
  match D.compatibility with
  | .all => stateMem D src ss && stateMem D dst ds
  | .explicit ps =>
    ps.any fun a => a.src == src && a.srcState == ss && a.dst == dst && a.dstState == ds
  | .groups _ =>
    -- Group mode filters residual edges in `targetStates`, not here.
    true

def hasEdge (D : Description) (src ss dst : String) (effect : EffectKind) (kind : EdgeKind) (label : String) : Bool :=
  D.edges.any fun e =>
    e.src == src && e.srcState == ss && e.dst == dst && e.effect == effect && e.kind == kind && e.label == label

def selfLabels : List Eff → List String
  | [] => []
  | .selfSchedule l :: es => l :: selfLabels es
  | _ :: es => selfLabels es

/-- Labels a program can wake on `reader`'s priority lane by a `cell` write. -/
def cellWakeLabels (reader : String) : List Eff → List String
  | [] => []
  | .cell d l _ :: es => (if d == reader then [l] else []) ++ cellWakeLabels reader es
  | _ :: es => cellWakeLabels reader es

def sendsOk (D : Description) (template srcState dstState : String) (prog : List Eff) : Bool :=
  D.templates.all fun t =>
    sendsTo t.name prog + floorState D template dstState t.name ≤ floorState D template srcState t.name

def effectsOk (D : Description) (template toState : String) : List Eff → Bool
  | [] => true
  | .send d l _ :: es => hasEdge D template toState d .send .blocking l && effectsOk D template toState es
  | .trySend d l _ :: es =>
    hasEdge D template toState d .trySend .nonBlocking l &&
      !(D.edges.any fun e => e.ingress && e.src == template && e.dst == d && e.label == l) &&
      effectsOk D template toState es
  | .call d l _ :: es => hasEdge D template toState d .call .blocking l && effectsOk D template toState es
  | .cell d l _ :: es => hasEdge D template toState d .cell .nonBlocking l && effectsOk D template toState es
  | _ :: es => effectsOk D template toState es

def hasTerminate : List Eff → Bool
  | [] => false
  | .terminate :: _ => true
  | _ :: es => hasTerminate es

def noBulkSend : List Eff → Bool
  | [] => true
  | .send _ _ _ :: _ => false
  | .trySend _ _ _ :: _ => false
  | .call _ _ _ :: _ => false
  | _ :: es => noBulkSend es

def transitionOk (I : Impl) (tr : Transition) : Bool :=
  match templateOf I.desc tr.template with
  | none => false
  | some t =>
    (t.states.elem tr.fromState) && (t.states.elem tr.toState) && tr.release == 1 &&
      sendsOk I.desc tr.template tr.fromState tr.toState tr.program &&
      effectsOk I.desc tr.template tr.toState tr.program &&
      (if tr.acceptsCall then
        replyCount tr.program == 1 && !terminateBeforeReply tr.program
      else replyCount tr.program == 0) &&
      (if hasTerminate tr.program then t.terminable else true) &&
      (if t.terminable then noBulkSend tr.program else true)

def callSites : List Transition → List (String × String)
  | [] => []
  | tr :: ts =>
    let here := tr.program.filterMap fun e =>
      match e with
      | .call d l _ => some (d, l)
      | _ => none
    dedup (here ++ callSites ts)

def callTotal (I : Impl) : Bool :=
  (callSites I.transitions).all fun p =>
    match templateOf I.desc p.1 with
    | none => false
    | some t =>
      t.states.all fun st =>
        I.transitions.any fun tr =>
          tr.template == p.1 && tr.fromState == st && tr.label == p.2 && tr.acceptsCall

def targetsAll (D : Description) : Bool :=
  match D.compatibility with
  | .groups _ => true
  | _ =>
    D.edges.all fun e =>
      if e.kind == .blocking then
        (statesOf D e.dst).all fun ds => pairAllowed D e.src e.srcState e.dst ds
      else true

def occShape (D : Description) : Bool :=
  D.edges.all fun e =>
    match templateOf D e.src with
    | none => false
    | some t =>
      match t.multiplicity with
      | .one => e.occupancy.a == 0
      | .perPeer => e.occupancy.b == 0

def dstClosed (I : Impl) : Bool :=
  match I.desc.compatibility with
  | .all => true
  | .groups _ => true
  | .explicit ps =>
    I.transitions.all fun tr =>
      ps.all fun a =>
        if a.dst == tr.template && a.dstState == tr.fromState then
          pairAllowed I.desc a.src a.srcState tr.template tr.toState
        else true

def prioLabels (I : Impl) (template : String) : List String :=
  dedup <|
    (I.transitions.filterMap fun tr =>
      if tr.template == template then some (selfLabels tr.program) else none).flatten ++
      cellLabels I.desc template ++
      (I.transitions.map fun tr => cellWakeLabels template tr.program).flatten

def prioOk (I : Impl) : Bool :=
  I.desc.templates.all fun t =>
    let labels := prioLabels I t.name
    labels.length ≤ t.priorityBound.b && t.priorityBound.a == 0

/-- Every program the semantics can fire is one of the steps the relation was closed under. -/
def stepsCoverB (I : Impl) : Bool :=
  I.transitions.all fun tr =>
    I.desc.steps.any fun s =>
      s.template == tr.template && s.fromState == tr.fromState &&
        s.toState == tr.toState && s.label == tr.label

/-- `findTr` returns the first transition with this key. A second one is ignored,
so a call can be refused while `callTotal` still sees an accepting copy. -/
def trKey (tr : Transition) : String × String × String :=
  (tr.template, tr.fromState, tr.label)

def uniqueKeys (I : Impl) : Bool :=
  let keys := I.transitions.map trKey
  keys.length == (dedup keys).length

/-- Every bulk label on an edge is handled in every state the relation allows
the receiver to be in. A missing transition is what `deliver` consumes silently. -/
def labelHandled (I : Impl) : Bool :=
  I.desc.edges.all fun e =>
    if e.effect == .send || e.effect == .call || e.effect == .trySend then
      (targetStates I.desc e).all fun st =>
        I.transitions.any fun tr =>
          tr.template == e.dst && tr.fromState == st && tr.label == e.label &&
            (e.effect != .call || tr.acceptsCall)
    else true

/-- A reliable send or call may target only a non-terminable multiplicity-one
template. Those cores do not die, so the sender cannot proceed past a dead name. -/
def permanentTarget (I : Impl) : Bool :=
  I.desc.edges.all fun e =>
    if (e.effect == .send || e.effect == .call) && e.reliability == .reliable then
      match templateOf I.desc e.dst with
      | none => false
      | some t => t.multiplicity == .one && t.terminable == false
    else true

def localTail (I : Impl) : Bool :=
  stepsCoverB I && uniqueKeys I && labelHandled I && permanentTarget I

def localOkB (I : Impl) : Bool :=
  I.transitions.all (transitionOk I) && callTotal I && targetsAll I.desc &&
    occShape I.desc && dstClosed I && prioOk I &&
    (compatFails I.desc).isEmpty && localTail I

def LocalOk (I : Impl) : Prop := localOkB I = true

/-- Trust boundary. Nothing in here is a theorem about Rust.
`rust_refines` says the node's programs are `I.transitions`.
An internal effect completes as a `finish` step. A timed peer wait completes
the same way. An untimed peer wait does not, so the peer may stay silent.
Scheduler fairness is the separate `Fair` hypothesis and does not force ingress. -/
structure Assumptions (I : Impl) : Prop where
  rust_refines :
    ∀ tr ∈ I.transitions, ∃ tr' ∈ I.transitions,
      tr'.template = tr.template ∧ tr'.fromState = tr.fromState ∧
      tr'.label = tr.label ∧ tr'.program = tr.program ∧ tr'.toState = tr.toState ∧
      tr'.acceptsCall = tr.acceptsCall

/-- After a declared cell label strictly rises, every instance of that template
which is already alive and stays alive eventually records at least the written
value. A reader that is dead or never spawned has nothing to observe. -/
def CellFresh {I : Impl} {N : Nat} (ρ : Run I N) : Prop :=
  ∀ i dst label,
    label ∈ cellLabels I.desc dst →
    ((ρ.cfg i).cell dst label).value < ((ρ.cfg (i + 1)).cell dst label).value →
    ∀ r, tname r = dst →
      (∀ t, i ≤ t → ((ρ.cfg t).st r).life = .alive) →
      ∃ j, i < j ∧
        ((ρ.cfg (i + 1)).cell dst label).value ≤ ((ρ.cfg j).observed r label)

/-! Boolean checks imply the facts the invariant uses. -/

theorem local_parts (I : Impl) (h : LocalOk I) :
    I.transitions.all (transitionOk I) = true ∧ callTotal I = true ∧ targetsAll I.desc = true ∧
      occShape I.desc = true ∧ dstClosed I = true ∧ prioOk I = true ∧
      (compatFails I.desc).isEmpty = true ∧ stepsCoverB I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2,
    h.2.1.1.1⟩

theorem unique_keys_local (I : Impl) (h : LocalOk I) : uniqueKeys I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.1.2

theorem label_handled_local (I : Impl) (h : LocalOk I) : labelHandled I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.2

theorem permanent_target_local (I : Impl) (h : LocalOk I) : permanentTarget I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2

theorem transitionOk_of_mem (I : Impl) (h : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    transitionOk I tr = true := by
  have htr := (local_parts I h).1
  exact (List.all_eq_true _ _).mp htr tr hm

theorem targetsAll_edge (I : Impl) (h : LocalOk I) (e : Edge) (he : e ∈ I.desc.edges)
    (hk : e.kind = .blocking) (ds : String) (hs : ds ∈ statesOf I.desc e.dst) :
    pairAllowed I.desc e.src e.srcState e.dst ds = true := by
  have ht := (local_parts I h).2.2.1
  cases hc : I.desc.compatibility with
  | groups _ => simp [pairAllowed, hc]
  | all =>
    simp only [targetsAll, hc] at ht
    have he' := (List.all_eq_true _ _).mp ht e he
    rw [hk] at he'
    simp at he'
    cases he' with
    | inl hbad =>
      have ht : (EdgeKind.blocking == EdgeKind.blocking) = true := by decide
      simp [ht] at hbad
    | inr hok => exact hok ds hs
  | explicit _ =>
    simp only [targetsAll, hc] at ht
    have he' := (List.all_eq_true _ _).mp ht e he
    rw [hk] at he'
    simp at he'
    cases he' with
    | inl hbad =>
      have ht : (EdgeKind.blocking == EdgeKind.blocking) = true := by decide
      simp [ht] at hbad
    | inr hok => exact hok ds hs


end Deadlock
