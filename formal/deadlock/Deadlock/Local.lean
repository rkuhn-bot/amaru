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
  | .trySend d l _ onFull onGone :: es =>
    hasEdge D template toState d .trySend .nonBlocking l &&
      !(D.edges.any fun e => e.ingress && e.src == template && e.dst == d && e.label == l) &&
      effectsOk D template toState onFull && effectsOk D template toState onGone &&
      effectsOk D template toState es
  | .call d l _ onNotAdmitted onTimedOut :: es =>
    hasEdge D template toState d .call .blocking l &&
      effectsOk D template toState onNotAdmitted && effectsOk D template toState onTimedOut &&
      effectsOk D template toState es
  | .cell d l _ :: es => hasEdge D template toState d .cell .nonBlocking l && effectsOk D template toState es
  | .peer onTimeout :: es =>
    effectsOk D template toState onTimeout && effectsOk D template toState es
  | _ :: es => effectsOk D template toState es

def hasTerminate : List Eff → Bool
  | [] => false
  | .terminate :: _ => true
  | _ :: es => hasTerminate es

/-- A terminable program must not leave a reliable message behind. `send`,
`trySend`, and `call` are bulk; `selfSchedule` is a reliable priority message
that `terminate` would clear. -/
def noBulkSend : List Eff → Bool
  | [] => true
  | .send _ _ _ :: _ => false
  | .trySend _ _ _ _ _ :: _ => false
  | .call _ _ _ _ _ :: _ => false
  | .selfSchedule _ :: _ => false
  | .peer onTimeout :: es => noBulkSend onTimeout && noBulkSend es
  | _ :: es => noBulkSend es

/-- What a continuation may still do. A lone terminable stays mute. A subtree
member may send to a per-peer sibling and call one. Anything else is
unconstrained here. -/
def bulkScopeOf (D : Description) (name : String) (es : List Eff) : Bool :=
  match templateOf D name with
  | none => true
  | some t =>
    if !t.terminable then true
    else if t.subtree == "" then noBulkSend es
    else memberProgramOk D name es

/-- Every outcome continuation is a program `LocalOk` accepts. `Reply` is the
tail, `NotAdmitted` and `TimedOut` are the call's own lists, a peer wait has
data and timeout, and `trySend` has admitted, `Full`, and `Gone`. -/
def callOutcomesOk (D : Description) (template toState : String) : List Eff → Bool
  | [] => true
  | .call _ _ _ onNotAdmitted onTimedOut :: es =>
    effectsOk D template toState es && effectsOk D template toState onNotAdmitted &&
      effectsOk D template toState onTimedOut && callOutcomesOk D template toState es &&
      callOutcomesOk D template toState onNotAdmitted &&
      callOutcomesOk D template toState onTimedOut
  | .trySend _ _ _ onFull onGone :: es =>
    effectsOk D template toState onFull && effectsOk D template toState onGone &&
      callOutcomesOk D template toState es && callOutcomesOk D template toState onFull &&
      callOutcomesOk D template toState onGone
  | .peer onTimeout :: es =>
    effectsOk D template toState onTimeout && callOutcomesOk D template toState es &&
      callOutcomesOk D template toState onTimeout
  | _ :: es => callOutcomesOk D template toState es

def transitionOk (I : Impl) (tr : Transition) : Bool :=
  match templateOf I.desc tr.template with
  | none => false
  | some t =>
    (t.states.elem tr.fromState) && (t.states.elem tr.toState) && tr.release == 1 &&
      sendsOk I.desc tr.template tr.fromState tr.toState tr.program &&
      effectsOk I.desc tr.template tr.toState tr.program &&
      callOutcomesOk I.desc tr.template tr.toState tr.program &&
      (if tr.acceptsCall then
        replyCount tr.program == 1 && !terminateBeforeReply tr.program
      else replyCount tr.program == 0) &&
      (if hasTerminate tr.program then t.terminable else true) &&
      bulkScopeOf I.desc tr.template tr.program

def callSites : List Transition → List (String × String)
  | [] => []
  | tr :: ts =>
    let here := tr.program.filterMap fun e =>
      match e with
      | .call d l _ _ _ => some (d, l)
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

/-- A reliable send or call leaves the sender's subtree only toward a
non-terminable multiplicity-one core. Inside the subtree the target may be a
terminable member: the subtree kill credits or fails that message. -/
def permanentTarget (I : Impl) : Bool :=
  I.desc.edges.all fun e =>
    if (e.effect == .send || e.effect == .call) && e.reliability == .reliable then
      match templateOf I.desc e.dst with
      | none => false
      | some t =>
        (t.multiplicity == .one && t.terminable == false) || sameSubtree I.desc e.src e.dst
    else true

def noSelfSchedule : List Eff → Bool
  | [] => true
  | .selfSchedule _ :: _ => false
  | _ :: es => noSelfSchedule es

/-- A pure untimed template does not arm its own priority lane. The peer wait
is not finishable, so a self-scheduled label would never be received. -/
def pureSchedOk (I : Impl) : Bool :=
  I.transitions.all fun tr =>
    if templatePure I.desc tr.template then noSelfSchedule tr.program else true

/-- A supervised template names one tombstone label, and its supervisor has a
transition on that label. -/
def tombstoneHandled (I : Impl) : Bool :=
  I.desc.templates.all fun t =>
    if t.supervisor == "" then true
    else
      t.tombstone != "" &&
        I.transitions.any fun tr => tr.template == t.supervisor && tr.label == t.tombstone

def localTail (I : Impl) : Bool :=
  stepsCoverB I && uniqueKeys I && labelHandled I && permanentTarget I && pureSchedOk I &&
    tombstoneHandled I

def localOkB (I : Impl) : Bool :=
  I.transitions.all (transitionOk I) && callTotal I && targetsAll I.desc &&
    occShape I.desc && dstClosed I && prioOk I &&
    (compatFails I.desc).isEmpty && localTail I

def LocalOk (I : Impl) : Prop := localOkB I = true

/-- Trust boundary. Nothing in here is a theorem about Rust.
`rust_refines` says the node's programs are `I.transitions`.
An internal effect completes as a `finish` step. A timed peer wait completes
the same way. An untimed peer wait completes when a timed peer in its cohort
can end the chain. A pure untimed peer wait does not, so that peer may stay silent.
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
    h.2.1.1.1.1.1⟩

theorem unique_keys_local (I : Impl) (h : LocalOk I) : uniqueKeys I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.1.1.1.2

theorem label_handled_local (I : Impl) (h : LocalOk I) : labelHandled I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.1.1.2

theorem permanent_target_local (I : Impl) (h : LocalOk I) : permanentTarget I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.1.2

theorem pure_sched_local (I : Impl) (h : LocalOk I) : pureSchedOk I = true := by
  simp only [LocalOk, localOkB, localTail] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.2

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

/-! Reasons a wiring fails `localOkB`. The boolean stays the decision; these
lines are what `check` prints. Each line names the obligation that failed. -/

def floorGap (D : Description) (template srcState dstState label : String) (prog : List Eff) : List String :=
  D.templates.filterMap fun dst =>
    let sent := sendsTo dst.name prog
    let held := floorState D template srcState dst.name
    let need := sent + floorState D template dstState dst.name
    if need ≤ held then none
    else some s!"fail: transition {template} {srcState} -> {dstState} [{label}] needs {need} slot(s) toward {dst.name} and {srcState} holds {held}"

def programGap (D : Description) (template toState label : String) : List Eff → List String
  | [] => []
  | .send d l _ :: es =>
    if hasEdge D template toState d .send .blocking l then programGap D template toState label es
    else [s!"fail: transition {template} [{label}] sends {l} to {d} from {toState}, which is not a blocking send edge"]
  | .trySend d l _ onFull onGone :: es =>
    if hasEdge D template toState d .trySend .nonBlocking l then
      if D.edges.any fun e => e.ingress && e.src == template && e.dst == d && e.label == l then
        [s!"fail: transition {template} [{label}] try-sends {l}, which is an ingress label delivered by the environment"]
      else programGap D template toState label onFull ++ programGap D template toState label onGone ++
        programGap D template toState label es
    else [s!"fail: transition {template} [{label}] try-sends {l} to {d} from {toState}, which is not a non-blocking trySend edge"]
  | .call d l _ onNotAdmitted onTimedOut :: es =>
    if hasEdge D template toState d .call .blocking l then
      programGap D template toState label onNotAdmitted ++ programGap D template toState label onTimedOut ++
        programGap D template toState label es
    else [s!"fail: transition {template} [{label}] calls {l} on {d} from {toState}, which is not a blocking call edge"]
  | .cell d l _ :: es =>
    if hasEdge D template toState d .cell .nonBlocking l then programGap D template toState label es
    else [s!"fail: transition {template} [{label}] writes cell {l} on {d} from {toState}, which is not a non-blocking cell edge"]
  | _ :: es => programGap D template toState label es

def replyGap (tr : Transition) : List String :=
  if tr.acceptsCall then
    (if replyCount tr.program == 1 then []
     else [s!"fail: transition {tr.template} [{tr.label}] accepts a call but does not reply once"]) ++
    (if terminateBeforeReply tr.program then
      [s!"fail: transition {tr.template} [{tr.label}] terminates before its reply"]
     else [])
  else if replyCount tr.program == 0 then []
  else [s!"fail: transition {tr.template} [{tr.label}] replies without accepting a call"]

/-- Effects in a subtree member's program that leave the subtree. -/
def scopeGap (D : Description) (template label : String) : List Eff → List String
  | [] => []
  | .send dst _ _ :: es =>
    (if sameSubtree D template dst && perPeerB D dst then []
     else [s!"fail: transition {template} [{label}] sends to {dst} outside its subtree"]) ++
      scopeGap D template label es
  | .trySend dst _ _ onFull onGone :: es =>
    (if sameSubtree D template dst && perPeerB D dst then []
     else [s!"fail: transition {template} [{label}] try-sends to {dst} outside its subtree"]) ++
      scopeGap D template label onFull ++ scopeGap D template label onGone ++
      scopeGap D template label es
  | .call dst _ _ onNotAdmitted onTimedOut :: es =>
    (if sameSubtree D template dst && perPeerB D dst then []
     else [s!"fail: transition {template} [{label}] calls {dst} outside its subtree"]) ++
      scopeGap D template label onNotAdmitted ++ scopeGap D template label onTimedOut ++
      scopeGap D template label es
  | .peer onTimeout :: es =>
    scopeGap D template label onTimeout ++ scopeGap D template label es
  | _ :: es => scopeGap D template label es

/-- One transition's local failures. Empty when `transitionOk` holds. -/
def transitionIssues (I : Impl) (tr : Transition) : List String :=
  match templateOf I.desc tr.template with
  | none => [s!"fail: transition {tr.label} names unknown template {tr.template}"]
  | some t =>
    (if t.states.elem tr.fromState then []
     else [s!"fail: transition {tr.template} [{tr.label}] leaves undeclared state {tr.fromState}"]) ++
    (if t.states.elem tr.toState then []
     else [s!"fail: transition {tr.template} [{tr.label}] enters undeclared state {tr.toState}"]) ++
    (if tr.release == 1 then []
     else [s!"fail: transition {tr.template} [{tr.label}] releases {tr.release} slot(s); a bulk receive releases 1"]) ++
    floorGap I.desc tr.template tr.fromState tr.toState tr.label tr.program ++
    programGap I.desc tr.template tr.toState tr.label tr.program ++
    replyGap tr ++
    (if hasTerminate tr.program && !t.terminable then
      [s!"fail: transition {tr.template} [{tr.label}] terminates, and {tr.template} is not terminable"]
     else []) ++
    (if t.terminable && t.subtree == "" && !(noBulkSend tr.program) then
      [s!"fail: transition {tr.template} [{tr.label}] sends from terminable role {tr.template}"]
     else []) ++
    (if t.terminable && t.subtree != "" then scopeGap I.desc tr.template tr.label tr.program else [])

def callIssues (I : Impl) : List String :=
  (callSites I.transitions).filterMap fun p =>
    match templateOf I.desc p.1 with
    | none => some s!"fail: call {p.2} targets unknown template {p.1}"
    | some t =>
      let missing := t.states.filter fun st =>
        !(I.transitions.any fun tr =>
          tr.template == p.1 && tr.fromState == st && tr.label == p.2 && tr.acceptsCall)
      match missing.head? with
      | none => none
      | some st => some s!"fail: call {p.2} is not accepted by {p.1} in state {st}"

def targetIssues (D : Description) : List String :=
  match D.compatibility with
  | .groups _ => []
  | _ =>
    D.edges.flatMap fun e =>
      if e.kind == .blocking then
        (statesOf D e.dst).filterMap fun ds =>
          if pairAllowed D e.src e.srcState e.dst ds then none
          else some s!"fail: blocking edge {e.label} does not allow {e.dst} in {ds} while {e.src} is in {e.srcState}"
      else []

def shapeIssues (D : Description) : List String :=
  D.edges.filterMap fun e =>
    match templateOf D e.src with
    | none => some s!"fail: edge {e.label} leaves unknown template {e.src}"
    | some t =>
      match t.multiplicity with
      | .one =>
        if e.occupancy.a == 0 then none
        else some s!"fail: edge {e.label} from core {e.src} carries a per-peer occupancy coefficient"
      | .perPeer =>
        if e.occupancy.b == 0 then none
        else some s!"fail: edge {e.label} from per-peer {e.src} carries a constant occupancy term"

def coverIssues (I : Impl) : List String :=
  I.transitions.filterMap fun tr =>
    if I.desc.steps.any fun s =>
        s.template == tr.template && s.fromState == tr.fromState &&
          s.toState == tr.toState && s.label == tr.label then none
    else some s!"fail: transition {tr.template} {tr.fromState} -> {tr.toState} [{tr.label}] is not a compatibility step"

def keyIssues (I : Impl) : List String :=
  if uniqueKeys I then []
  else ["fail: two transitions share a template, a source state, and a label; only the first one runs"]

def handledIssues (I : Impl) : List String :=
  I.desc.edges.flatMap fun e =>
    if e.effect == .send || e.effect == .call || e.effect == .trySend then
      (targetStates I.desc e).filterMap fun st =>
        if I.transitions.any fun tr =>
            tr.template == e.dst && tr.fromState == st && tr.label == e.label &&
              (e.effect != .call || tr.acceptsCall) then none
        else some s!"fail: {e.label} into {e.dst} is not handled in state {st}"
    else []

def permanentIssues (I : Impl) : List String :=
  I.desc.edges.filterMap fun e =>
    if (e.effect == .send || e.effect == .call) && e.reliability == .reliable then
      match templateOf I.desc e.dst with
      | none => some s!"fail: reliable {e.label} targets unknown template {e.dst}"
      | some t =>
        if (t.multiplicity == .one && t.terminable == false) || sameSubtree I.desc e.src e.dst then none
        else some s!"fail: reliable {e.label} from {e.src} to {e.dst} is neither a permanent core nor inside the subtree"
    else none

def schedIssues (I : Impl) : List String :=
  I.transitions.filterMap fun tr =>
    if templatePure I.desc tr.template && !(noSelfSchedule tr.program) then
      some s!"fail: pure untimed template {tr.template} self-schedules in [{tr.label}], and that wait never finishes"
    else none

def prioIssues (I : Impl) : List String :=
  I.desc.templates.filterMap fun t =>
    let labels := prioLabels I t.name
    if labels.length ≤ t.priorityBound.b && t.priorityBound.a == 0 then none
    else some s!"fail: priority lane {t.name} lists {labels.length} label(s) and the bound is {t.priorityBound.a}*N+{t.priorityBound.b}"

def closedIssues (I : Impl) : List String :=
  match I.desc.compatibility with
  | .explicit ps =>
    I.transitions.flatMap fun tr =>
      ps.filterMap fun a =>
        if a.dst == tr.template && a.dstState == tr.fromState &&
            !(pairAllowed I.desc a.src a.srcState tr.template tr.toState) then
          some s!"fail: transition {tr.template} {tr.fromState} -> {tr.toState} [{tr.label}] leaves allowed pair {a.src}/{a.srcState}"
        else none
  | _ => []

def localIssues (I : Impl) : List String :=
  (I.transitions.flatMap (transitionIssues I)) ++ callIssues I ++ targetIssues I.desc ++
    shapeIssues I.desc ++ closedIssues I ++ prioIssues I ++ coverIssues I ++ keyIssues I ++
    handledIssues I ++ permanentIssues I ++ schedIssues I

end Deadlock
