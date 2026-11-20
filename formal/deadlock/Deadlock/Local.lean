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

mutual
def selfLabels : List Eff → List String
  | [] => []
  | e :: es => effSelf e ++ selfLabels es

def effSelf : Eff → List String
  | .selfSchedule l => [l]
  | .trySend _ _ _ onFull onGone => selfLabels onFull ++ selfLabels onGone
  | .call _ _ _ onNotAdmitted onTimedOut => selfLabels onNotAdmitted ++ selfLabels onTimedOut
  | .peer onTimeout => selfLabels onTimeout
  | _ => []
end

mutual
/-- Labels a program can wake on `reader`'s priority lane by a `cell` write. -/
def cellWakeLabels (reader : String) : List Eff → List String
  | [] => []
  | e :: es => effWake reader e ++ cellWakeLabels reader es

def effWake (reader : String) : Eff → List String
  | .cell d l _ => if d == reader then [l] else []
  | .trySend _ _ _ onFull onGone => cellWakeLabels reader onFull ++ cellWakeLabels reader onGone
  | .call _ _ _ onNotAdmitted onTimedOut =>
    cellWakeLabels reader onNotAdmitted ++ cellWakeLabels reader onTimedOut
  | .peer onTimeout => cellWakeLabels reader onTimeout
  | _ => []
end

def sendsOk (D : Description) (template : String) (tr : Transition) : Bool :=
  D.templates.all fun t =>
    pathReserve D template t.name (branchAt tr) tr.program ≤
      floorState D template tr.fromState t.name

mutual
def effectsOk (D : Description) (template : String) (at_ : BranchAt) : List Eff → Bool
  | [] => true
  | e :: es => effectOk D template at_ e && effectsOk D template at_ es

/-- One effect, at `at_.here`. A replacing branch is checked at its own typestate. -/
def effectOk (D : Description) (template : String) (at_ : BranchAt) : Eff → Bool
  | .send d l _ => hasEdge D template at_.here d .send .blocking l
  | .trySend d l _ onFull onGone =>
    hasEdge D template at_.here d .trySend .nonBlocking l &&
      !(D.edges.any fun e => e.ingress && e.src == template && e.dst == d && e.label == l) &&
      effectsOk D template (focus at_ at_.full) onFull &&
      effectsOk D template (focus at_ at_.gone) onGone
  | .call d l _ onNotAdmitted onTimedOut =>
    hasEdge D template at_.here d .call .blocking l &&
      effectsOk D template (focus at_ at_.notAdmitted) onNotAdmitted &&
      effectsOk D template (focus at_ at_.timedOut) onTimedOut
  | .cell d l _ => hasEdge D template at_.here d .cell .nonBlocking l
  | .peer onTimeout => effectsOk D template (focus at_ at_.timeout) onTimeout
  | _ => true
end

mutual
def hasTerminate : List Eff → Bool
  | [] => false
  | e :: es => effTerminates e || hasTerminate es

def effTerminates : Eff → Bool
  | .terminate => true
  | .trySend _ _ _ onFull onGone => hasTerminate onFull || hasTerminate onGone
  | .call _ _ _ onNotAdmitted onTimedOut => hasTerminate onNotAdmitted || hasTerminate onTimedOut
  | .peer onTimeout => hasTerminate onTimeout
  | _ => false
end

mutual
/-- A terminable program must not leave a reliable message behind. `send`,
`trySend`, and `call` are bulk; `selfSchedule` is a reliable priority message
that `terminate` would clear. -/
def noBulkSend : List Eff → Bool
  | [] => true
  | e :: es => effMute e && noBulkSend es

def effMute : Eff → Bool
  | .send _ _ _ => false
  | .trySend _ _ _ onFull onGone => noBulkSend onFull && noBulkSend onGone
  | .call _ _ _ onNotAdmitted onTimedOut => noBulkSend onNotAdmitted && noBulkSend onTimedOut
  | .selfSchedule _ => false
  | .peer onTimeout => noBulkSend onTimeout
  | _ => true
end

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

/-- `Reply` is the tail. `NotAdmitted`, `TimedOut`, peer timeout, `Full`, and
`Gone` are checked at their own typestate by `effectsOk`. -/
def callOutcomesOk (D : Description) (template : String) (at_ : BranchAt) (es : List Eff) : Bool :=
  effectsOk D template at_ es

/-- Empty names the transition's `toState`, which is checked on its own. -/
def stateNamed (t : Template) (s : String) : Bool :=
  s == "" || t.states.elem s

mutual
/-- `Eff.spawn` names a per-peer child this template supervises. -/
def spawnScope (D : Description) (src : String) : List Eff → Bool
  | [] => true
  | e :: es => spawnEffect D src e && spawnScope D src es

def spawnEffect (D : Description) (src : String) : Eff → Bool
  | .spawn child =>
    match templateOf D child, templateOf D src with
    | some ct, some p =>
      if p.multiplicity == .perPeer then
        ct.supervisor == src && ct.multiplicity == .perPeer && ct.slots == 0
      else
        ct.supervisor == src && ct.multiplicity == .perPeer && ct.slots != 0
    | _, _ => false
  | .trySend _ _ _ onFull onGone => spawnScope D src onFull && spawnScope D src onGone
  | .call _ _ _ onNotAdmitted onTimedOut =>
    spawnScope D src onNotAdmitted && spawnScope D src onTimedOut
  | .peer onTimeout => spawnScope D src onTimeout
  | _ => true
end

def transitionOk (I : Impl) (tr : Transition) : Bool :=
  match templateOf I.desc tr.template with
  | none => false
  | some t =>
    let at_ := branchAt tr
    (t.states.elem tr.fromState) && (t.states.elem tr.toState) && tr.release == 1 &&
      stateNamed t tr.toNotAdmitted && stateNamed t tr.toTimedOut &&
      stateNamed t tr.toTimeout && stateNamed t tr.toFull && stateNamed t tr.toGone &&
      sendsOk I.desc tr.template tr &&
      effectsOk I.desc tr.template at_ tr.program &&
      callOutcomesOk I.desc tr.template at_ tr.program &&
      spawnScope I.desc tr.template tr.program &&
      (if tr.acceptsCall then
        repliesMatch 1 tr.program && !terminateBeforeReply tr.program
      else repliesMatch 0 tr.program) &&
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

/-- The static size under which a priority lane does not overflow: capacity
covers every child that can tombstone at once plus the other priority senders.
Full-duplex sizing makes the tombstone term `population`, a product along the
supervision tree. Not part of `LocalOk`. The checker will report these lines
later. -/
def prioSizeFails (I : Impl) (N : Nat) : List String :=
  I.desc.templates.filterMap fun t =>
    if prioSized I.desc t.name N (prioLabels I t.name).length then none
    else some s!"fail: priority lane {t.name} holds fewer slots than the tombstones and other priority senders it can receive at once"

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

mutual
def noSelfSchedule : List Eff → Bool
  | [] => true
  | e :: es => effNoSched e && noSelfSchedule es

def effNoSched : Eff → Bool
  | .selfSchedule _ => false
  | .trySend _ _ _ onFull onGone => noSelfSchedule onFull && noSelfSchedule onGone
  | .call _ _ _ onNotAdmitted onTimedOut => noSelfSchedule onNotAdmitted && noSelfSchedule onTimedOut
  | .peer onTimeout => noSelfSchedule onTimeout
  | _ => true
end

/-- A pure untimed template does not arm its own priority lane. The peer wait
is not finishable, so a self-scheduled label would never be received. -/
def pureSchedOk (I : Impl) : Bool :=
  I.transitions.all fun tr =>
    if templatePure I.desc tr.template then noSelfSchedule tr.program else true

/-- A supervised template names one tombstone label, and its supervisor handles
that label in every state the template declares. A tombstone that arrives in
a state with no transition stays queued. -/
def tombstoneHandled (I : Impl) : Bool :=
  I.desc.templates.all fun t =>
    if t.supervisor == "" then true
    else
      t.tombstone != "" &&
        match templateOf I.desc t.supervisor with
        | none => false
        | some sup =>
          sup.states.all fun st =>
            I.transitions.any fun tr =>
              tr.template == t.supervisor && tr.fromState == st && tr.label == t.tombstone

def localTail (I : Impl) : Bool :=
  stepsCoverB I && uniqueKeys I && labelHandled I && permanentTarget I && pureSchedOk I &&
    tombstoneHandled I

def localOkB (I : Impl) : Bool :=
  I.transitions.all (transitionOk I) && callTotal I && targetsAll I.desc &&
    occShape I.desc && dstClosed I && prioOk I &&
    (compatFails I.desc).isEmpty && localTail I

def LocalOk (I : Impl) : Prop := localOkB I = true

instance (I : Impl) : Decidable (LocalOk I) :=
  inferInstanceAs (Decidable (localOkB I = true))

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

def floorGap (D : Description) (tr : Transition) : List String :=
  D.templates.filterMap fun dst =>
    let need := pathReserve D tr.template dst.name (branchAt tr) tr.program
    let held := floorState D tr.template tr.fromState dst.name
    if need ≤ held then none
    else some s!"fail: transition {tr.template} {tr.fromState} -> {tr.toState} [{tr.label}] needs {need} slot(s) toward {dst.name} and {tr.fromState} holds {held}"

def programGap (D : Description) (template label : String) (at_ : BranchAt) : List Eff → List String
  | [] => []
  | .send d l _ :: es =>
    if hasEdge D template at_.here d .send .blocking l then programGap D template label at_ es
    else [s!"fail: transition {template} [{label}] sends {l} to {d} from {at_.here}, which is not a blocking send edge"]
  | .trySend d l _ onFull onGone :: es =>
    if hasEdge D template at_.here d .trySend .nonBlocking l then
      if D.edges.any fun e => e.ingress && e.src == template && e.dst == d && e.label == l then
        [s!"fail: transition {template} [{label}] try-sends {l}, which is an ingress label delivered by the environment"]
      else programGap D template label (focus at_ at_.full) onFull ++
        programGap D template label (focus at_ at_.gone) onGone ++
        programGap D template label at_ es
    else [s!"fail: transition {template} [{label}] try-sends {l} to {d} from {at_.here}, which is not a non-blocking trySend edge"]
  | .call d l _ onNotAdmitted onTimedOut :: es =>
    if hasEdge D template at_.here d .call .blocking l then
      programGap D template label (focus at_ at_.notAdmitted) onNotAdmitted ++
        programGap D template label (focus at_ at_.timedOut) onTimedOut ++
        programGap D template label at_ es
    else [s!"fail: transition {template} [{label}] calls {l} on {d} from {at_.here}, which is not a blocking call edge"]
  | .cell d l _ :: es =>
    if hasEdge D template at_.here d .cell .nonBlocking l then programGap D template label at_ es
    else [s!"fail: transition {template} [{label}] writes cell {l} on {d} from {at_.here}, which is not a non-blocking cell edge"]
  | .peer onTimeout :: es =>
    programGap D template label (focus at_ at_.timeout) onTimeout ++ programGap D template label at_ es
  | _ :: es => programGap D template label at_ es

def replyGap (tr : Transition) : List String :=
  if tr.acceptsCall then
    (if repliesMatch 1 tr.program then []
     else [s!"fail: transition {tr.template} [{tr.label}] accepts a call but does not reply once on every path"]) ++
    (if terminateBeforeReply tr.program then
      [s!"fail: transition {tr.template} [{tr.label}] terminates before its reply"]
     else [])
  else if repliesMatch 0 tr.program then []
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
    floorGap I.desc tr ++
    programGap I.desc tr.template tr.label (branchAt tr) tr.program ++
    replyGap tr ++
    (if stateNamed t tr.toNotAdmitted && stateNamed t tr.toTimedOut &&
        stateNamed t tr.toTimeout && stateNamed t tr.toFull && stateNamed t tr.toGone then []
     else [s!"fail: transition {tr.template} [{tr.label}] names an outcome state the template does not declare"]) ++
    (if spawnScope I.desc tr.template tr.program then []
     else [s!"fail: transition {tr.template} [{tr.label}] spawns a stage it does not supervise"]) ++
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
