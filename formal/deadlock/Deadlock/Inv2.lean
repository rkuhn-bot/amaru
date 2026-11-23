import Deadlock.ChildBirth
import Deadlock.Lane
import Deadlock.Occ

set_option autoImplicit false

namespace Deadlock

/-- The program still to run, and the three outcome lists a later step may switch to.
`NotAdmitted` and `TimedOut` are the call's, `onTimeout` is the peer wait's.
`trySend`'s `Full` and `Gone` are installed as `rest` in the same step, so they
are not stored beside it. -/
def contArms (D : Description) (name : String) (k : Cont) : Bool :=
  bulkScopeOf D name k.rest && bulkScopeOf D name k.onNotAdmitted &&
    bulkScopeOf D name k.onTimedOut && bulkScopeOf D name k.onTimeout

/-- Bulk scope of whatever continuation this phase still holds. Idle and crashed
hold none. -/
def phaseScope (D : Description) (name : String) : Phase → Bool
  | .run k => contArms D name k
  | .parked _ _ k => contArms D name k
  | .awaitReply _ k => contArms D name k
  | .awaitEffect k => contArms D name k
  | .awaitPeer k => contArms D name k
  | .idle => true
  | .crashed => true

/-- A lone terminable's stored continuations do not send, call, or self-schedule.
A subtree member's stored continuations stay inside that subtree. The outcome
lists are part of the fact: a timeout runs one of them, and `contRest` alone
does not mention it. -/
def BulkFree (I : Impl) (w : World) : Prop :=
  ∀ id, phaseScope I.desc (tname id) (w.st id).phase = true

theorem scope_rest (D : Description) (name : String) (ph : Phase)
    (h : phaseScope D name ph = true) :
    bulkScopeOf D name (contRest ph) = true := by
  cases ph with
  | idle => simpa [contRest] using scope_empty D name
  | crashed => simpa [contRest] using scope_empty D name
  | run k =>
    simp only [phaseScope, contArms, contRest, Bool.and_eq_true] at h
    exact h.1.1.1
  | parked _ _ k =>
    simp only [phaseScope, contArms, contRest, Bool.and_eq_true] at h
    exact h.1.1.1
  | awaitReply _ k =>
    simp only [phaseScope, contArms, contRest, Bool.and_eq_true] at h
    exact h.1.1.1
  | awaitEffect k =>
    simp only [phaseScope, contArms, contRest, Bool.and_eq_true] at h
    exact h.1.1.1
  | awaitPeer k =>
    simp only [phaseScope, contArms, contRest, Bool.and_eq_true] at h
    exact h.1.1.1

theorem arms_rest (D : Description) (name : String) (k : Cont) (rest : List Eff)
    (h : contArms D name k = true) (hr : bulkScopeOf D name rest = true) :
    contArms D name { k with rest := rest } = true := by
  simp only [contArms, Bool.and_eq_true] at h
  simp [contArms, Bool.and_eq_true]
  exact ⟨⟨⟨hr, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem arms_skip (D : Description) (name : String) (k : Cont) (e : Eff) (es : List Eff)
    (h : contArms D name k = true) (hrest : k.rest = e :: es) :
    contArms D name (afterHead k) = true := by
  have htail : bulkScopeOf D name es = true := by
    have hr : bulkScopeOf D name k.rest = true := by
      simp only [contArms, Bool.and_eq_true] at h
      exact h.1.1.1
    have hrs : bulkScopeOf D name (e :: es) = true := by simpa [hrest] using hr
    exact scope_tail D name e es hrs
  have htailr : k.rest.tail = es := by simp [hrest, List.tail_cons]
  simpa [afterHead, htailr] using arms_rest D name k es h htail

theorem phase_proceed (D : Description) (name : String) (a : Actor) (k : Cont)
    (h : contArms D name k = true) : phaseScope D name (proceed a k).phase = true := by
  cases hk : k.rest with
  | nil => simp [proceed, hk, phaseScope]
  | cons _ _ => simpa [proceed, hk, phaseScope] using h

theorem phase_after (D : Description) (name : String) (a : Actor) (k : Cont) (e : Eff) (es : List Eff)
    (h : phaseScope D name (.run k) = true) (hrest : k.rest = e :: es) :
    phaseScope D name (proceed a (afterHead k)).phase = true := by
  have har : contArms D name k = true := by simpa [phaseScope] using h
  exact phase_proceed D name a (afterHead k) (arms_skip D name k e es har hrest)

/-- Replacing the two call outcomes keeps the rest and the peer timeout. -/
theorem arms_out (D : Description) (name : String) (k : Cont) (onNotAdmitted onTimedOut : List Eff)
    (h : contArms D name k = true) (hna : bulkScopeOf D name onNotAdmitted = true)
    (hto : bulkScopeOf D name onTimedOut = true) :
    contArms D name { k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } = true := by
  simp only [contArms, Bool.and_eq_true] at h
  simp [contArms, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1.1, hna⟩, hto⟩, h.2⟩

/-- Replacing a peer timeout keeps the rest and the call outcomes. -/
theorem arms_timeout (D : Description) (name : String) (k : Cont) (onTimeout : List Eff)
    (h : contArms D name k = true) (ht : bulkScopeOf D name onTimeout = true) :
    contArms D name { k with onTimeout := onTimeout } = true := by
  simp only [contArms, Bool.and_eq_true] at h
  simp [contArms, Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, ht⟩

/-- `NotAdmitted` runs `onNotAdmitted`. That list is already one arm of `k`. -/
theorem arms_notAdmitted (D : Description) (name : String) (k : Cont)
    (h : contArms D name k = true) :
    contArms D name (selectCall k .notAdmitted) = true := by
  simp only [contArms, selectCall, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- `TimedOut` runs `onTimedOut`. That list is already one arm of `k`. -/
theorem arms_timedOut (D : Description) (name : String) (k : Cont)
    (h : contArms D name k = true) :
    contArms D name (selectCall k .timedOut) = true := by
  simp only [contArms, selectCall, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- `Bool.and_eq_true` is an `Iff`, and this Lean build does not expose `.mp` on it.
The two directions used below are named here. -/
theorem and_left (a b : Bool) (h : (a && b) = true) : a = true := by
  rw [Bool.and_eq_true] at h
  exact h.1

theorem and_right (a b : Bool) (h : (a && b) = true) : b = true := by
  rw [Bool.and_eq_true] at h
  exact h.2

/-- `Full`, `Gone`, `NotAdmitted`, `TimedOut`, and a peer timeout are checked
with the program that contains them. -/
theorem scope_onFull (D : Description) (name dst label : String) (hint : Nat)
    (onFull onGone es : List Eff)
    (h : bulkScopeOf D name (.trySend dst label hint onFull onGone :: es) = true) :
    bulkScopeOf D name onFull = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : t.multiplicity == .one
        · rfl
        · exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp [hnot, hterm] at h ⊢
        by_cases hsub : t.subtree = ""
        · simp [hsub, noBulkSend, effMute] at h
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact h.1.1
        · have hm : memberProgramOk D name (.trySend dst label hint onFull onGone :: es) = true := by
            simpa [hsub] using h
          have hhead := memberProgram_head D name (.trySend dst label hint onFull onGone) es hm
          simp [memberEffectOk, Bool.and_eq_true] at hhead
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact hhead.1.2
      · simp [hnot, hterm]

theorem scope_onGone (D : Description) (name dst label : String) (hint : Nat)
    (onFull onGone es : List Eff)
    (h : bulkScopeOf D name (.trySend dst label hint onFull onGone :: es) = true) :
    bulkScopeOf D name onGone = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : t.multiplicity == .one
        · rfl
        · exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp [hnot, hterm] at h ⊢
        by_cases hsub : t.subtree = ""
        · simp [hsub, noBulkSend, effMute] at h
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact h.1.2
        · have hm : memberProgramOk D name (.trySend dst label hint onFull onGone :: es) = true := by
            simpa [hsub] using h
          have hhead := memberProgram_head D name (.trySend dst label hint onFull onGone) es hm
          simp [memberEffectOk, Bool.and_eq_true] at hhead
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact hhead.2
      · simp [hnot, hterm]

theorem scope_onNotAdmitted (D : Description) (name dst label : String) (hint : Nat)
    (onNotAdmitted onTimedOut es : List Eff)
    (h : bulkScopeOf D name (.call dst label hint onNotAdmitted onTimedOut :: es) = true) :
    bulkScopeOf D name onNotAdmitted = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : t.multiplicity == .one
        · rfl
        · exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp [hnot, hterm] at h ⊢
        by_cases hsub : t.subtree = ""
        · simp [hsub, noBulkSend, effMute] at h
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact h.1.1
        · have hm : memberProgramOk D name (.call dst label hint onNotAdmitted onTimedOut :: es) = true := by
            simpa [hsub] using h
          have hhead := memberProgram_head D name (.call dst label hint onNotAdmitted onTimedOut) es hm
          simp [memberEffectOk, Bool.and_eq_true] at hhead
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact hhead.1.2
      · simp [hnot, hterm]

theorem scope_onTimedOut (D : Description) (name dst label : String) (hint : Nat)
    (onNotAdmitted onTimedOut es : List Eff)
    (h : bulkScopeOf D name (.call dst label hint onNotAdmitted onTimedOut :: es) = true) :
    bulkScopeOf D name onTimedOut = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : t.multiplicity == .one
        · rfl
        · exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp [hnot, hterm] at h ⊢
        by_cases hsub : t.subtree = ""
        · simp [hsub, noBulkSend, effMute] at h
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact h.1.2
        · have hm : memberProgramOk D name (.call dst label hint onNotAdmitted onTimedOut :: es) = true := by
            simpa [hsub] using h
          have hhead := memberProgram_head D name (.call dst label hint onNotAdmitted onTimedOut) es hm
          simp [memberEffectOk, Bool.and_eq_true] at hhead
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact hhead.2
      · simp [hnot, hterm]

theorem scope_onTimeout (D : Description) (name : String) (onTimeout es : List Eff)
    (h : bulkScopeOf D name (.peer onTimeout :: es) = true) :
    bulkScopeOf D name onTimeout = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : t.multiplicity == .one
        · rfl
        · exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp [hnot, hterm] at h ⊢
        by_cases hsub : t.subtree = ""
        · simp [hsub, noBulkSend, effMute] at h
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact h.1
        · have hm : memberProgramOk D name (.peer onTimeout :: es) = true := by
            simpa [hsub] using h
          have hhead := memberProgram_head D name (.peer onTimeout) es hm
          simp [memberEffectOk] at hhead
          simp [bulkScopeOf, ht, hnot, hterm, hsub]
          exact hhead
      · simp [hnot, hterm]

def Inv2 (I : Impl) (w : World) : Prop :=
  Inv I w ∧ OccInv I w ∧ TyOk I.desc w ∧ BulkFree I w

theorem nobulk_empty : noBulkSend [] = true := rfl

theorem nobulk_idle (a : Actor) (h : a.phase = .idle ∨ a.phase = .crashed) :
    noBulkSend (contRest a.phase) = true := by
  rcases h with h | h <;> simp [contRest, h, nobulk_empty]

theorem terminable_program (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (t : Template) (ht : templateOf I.desc tr.template = some t) (hterm : t.terminable = true) :
    bulkScopeOf I.desc tr.template tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  simp only [transitionOk, ht] at hok
  repeat rw [Bool.and_eq_true] at hok
  exact hok.2

/-- Every checked transition's program is in bulk scope, terminable or not.
`transitionOk` requires `bulkScopeOf` on the program itself. -/
theorem program_scope (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    bulkScopeOf I.desc tr.template tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  cases ht : templateOf I.desc tr.template with
  | none => simp [transitionOk, ht] at hok
  | some _ =>
    simp only [transitionOk, ht] at hok
    repeat rw [Bool.and_eq_true] at hok
    exact hok.2

theorem bulk_init (I : Impl) (N : Nat) : BulkFree I (initWorld I N) := by
  intro id
  have hph := init_phase I N id
  simpa [phaseScope, hph]

theorem inv2_init (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) :
    Inv2 I (initWorld I N) :=
  ⟨inv_init I N hL, occ_init I hG N, ty_init I hG N, bulk_init I N⟩

theorem occ_apply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (a : Action) (w w' : World)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w)
    (hT : TyOk I.desc w) (hB : BulkFree I w) (hF : ParentForest w)
    (hBirth : BirthInv I.desc w) (hSeal : SealInv w) (h : apply I a w = some w') :
    OccInv I w' := by
  have ⟨hcr, hstep⟩ := apply_step I a w w' h
  cases a with
  | recvBulk id =>
    simpa [stepWorld] using occ_bulk I hL hG w id w' hO hS hM hstep
  | recvPrio id =>
    simpa [stepWorld] using occ_prio I hL hG w id w' hO hstep
  | exec id =>
    simpa [stepWorld] using occ_head I hL hG w w' id hO hT hS hM hSlots hstep
      (fun k hph => by
        simpa [contRest, hph] using scope_rest I.desc (tname id) (w.st id).phase (hB id)) hcr hSeal.childless
      hBirth.parented hBirth.singleGen hBirth.noTombLive hBirth.present hSeal.quiet
      hSeal.liveParked hBirth.plainBox hSeal.chain hBirth.noSelf hF
  | finish id =>
    simpa [stepWorld] using occ_finish I w w' id hO hS hstep
  | spawn template =>
    simpa [stepWorld] using occ_spawn I hG w w' template hO hstep
  | ingress dst label =>
    simpa [stepWorld] using occ_ingress I w w' dst label hO hstep
  | callTimeout id =>
    simpa [stepWorld] using occ_timeout I w w' id hO hS.cont hstep
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hO

theorem nobulk_drop (es : List Eff) (n : Nat) (h : noBulkSend es = true) : noBulkSend (es.drop n) = true := by
  induction n generalizing es with
  | zero => simpa using h
  | succ n ih =>
    cases es with
    | nil => exact nobulk_empty
    | cons e es => exact ih _ (noBulk_tail e es h)

/-- The continuation after one effect stays inside the scope the whole program had. -/
theorem after_scope (D : Description) (name : String) (a : Actor) (k : Cont)
    (h : bulkScopeOf D name k.rest = true) :
    bulkScopeOf D name (contRest (proceed a (afterHead k)).phase) = true := by
  cases hk : k.rest with
  | nil =>
    simp [proceed, afterHead, hk, contRest]
    exact scope_empty D name
  | cons e es =>
    have htail := scope_tail D name e es (by simpa [hk] using h)
    cases es with
    | nil =>
      simp [proceed, afterHead, hk, contRest]
      exact scope_empty D name
    | cons _ _ => simp [proceed, afterHead, hk, List.tail_cons, contRest, htail]

theorem cont_resumed (k : Cont) : contRest (resumed k) = k.rest := by
  cases hk : k.rest <;> simp [resumed, contRest, hk]

/-- A send keeps `k.rest`. A call keeps it when the target is alive, and runs
`onNotAdmitted` when the target is not. `awaitReply` and `parked` both store
`k.rest`. -/
theorem enqueue_sender_cont (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) :
    contRest ((enqueueOrPark w D sender dst msg isCall k).st sender).phase =
      (if isCall = true ∧ (w.st dst).life ≠ .alive then (selectCall k .notAdmitted).rest else k.rest) := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall with
      | true =>
        by_cases hsame : sender = dst
        · simp [hsame, setActor_self, contRest]
        · simp [hsame, setActor_self, contRest]
      | false =>
        by_cases hsame : sender = dst
        · simp [hsame, setActor_self, proceed_resumed]
          exact cont_resumed k
        · simp [hsame, setActor_self, proceed_resumed]
          exact cont_resumed k
    · simp [hroom]
      by_cases hsame : sender = dst
      · simp [hsame, setActor_self, contRest]
      · simp [hsame, setActor_self, contRest]
  · simp [hlive]
    cases isCall with
    | false =>
      simp [setActor_self]
      cases hk : k.rest <;> simp [proceed, hk, contRest]
    | true =>
      simp [setActor_self, finishCall, selectCall, contRest]
      cases hk : k.onNotAdmitted <;> simp [proceed, hk, contRest]

/-- `proceed` is idle when the rest is empty and running otherwise, and either way
the remaining program is still in scope. -/
theorem scope_proceed (D : Description) (name : String) (a : Actor) (k : Cont)
    (h : bulkScopeOf D name k.rest = true) :
    bulkScopeOf D name (contRest (proceed a k).phase) = true := by
  cases hk : k.rest with
  | nil =>
    simp [proceed, hk, contRest]
    exact scope_empty D name
  | cons _ _ => simpa [proceed, hk, contRest] using h

theorem after_nobulk (a : Actor) (k : Cont) (h : noBulkSend k.rest = true) :
    noBulkSend (contRest (proceed a (afterHead k)).phase) = true := by
  cases hk : k.rest with
  | nil =>
    simp [proceed, afterHead, hk, contRest]
    exact nobulk_empty
  | cons e es =>
    have htail := noBulk_tail e es (by simpa [hk] using h)
    cases es with
    | nil =>
      simp [proceed, afterHead, hk, contRest]
      exact nobulk_empty
    | cons _ _ => simp [proceed, afterHead, hk, List.tail_cons, contRest, htail]

theorem resume_nobulk (a : Actor) (b : Bool) (dst : InstId) (h : noBulkSend (contRest a.phase) = true) :
    noBulkSend (contRest (resumeSender a b dst).phase) = true := by
  cases hph : a.phase with
  | parked _ _ k =>
    have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using h
    cases b with
    | true => simpa [resumeSender, hph, contRest] using hrest
    | false =>
      cases hk : k.rest with
      | nil =>
        simp [resumeSender, hph, proceed, hk, contRest]
        exact nobulk_empty
      | cons _ _ => simpa [resumeSender, hph, proceed, hk, contRest] using hrest
  | idle =>
    simp [resumeSender, hph, contRest]
    exact nobulk_empty
  | run k => simpa [resumeSender, hph, contRest] using h
  | awaitReply _ k => simpa [resumeSender, hph, contRest] using h
  | awaitEffect k => simpa [resumeSender, hph, contRest] using h
  | awaitPeer k => simpa [resumeSender, hph, contRest] using h
  | crashed =>
    simp [resumeSender, hph, contRest]
    exact nobulk_empty

/-- Resuming a waiter keeps the continuation inside the scope it already had. -/
theorem resume_scope (D : Description) (name : String) (a : Actor) (b : Bool) (dst : InstId)
    (h : bulkScopeOf D name (contRest a.phase) = true) :
    bulkScopeOf D name (contRest (resumeSender a b dst).phase) = true := by
  cases hph : a.phase with
  | parked _ _ k =>
    have hrest : bulkScopeOf D name k.rest = true := by simpa [contRest, hph] using h
    cases b with
    | true => simpa [resumeSender, hph, contRest] using hrest
    | false =>
      cases hk : k.rest with
      | nil =>
        simp [resumeSender, hph, proceed, hk, contRest]
        exact scope_empty D name
      | cons _ _ => simpa [resumeSender, hph, proceed, hk, contRest] using hrest
  | idle =>
    simp [resumeSender, hph, contRest]
    exact scope_empty D name
  | run k => simpa [resumeSender, hph, contRest] using h
  | awaitReply _ k => simpa [resumeSender, hph, contRest] using h
  | awaitEffect k => simpa [resumeSender, hph, contRest] using h
  | awaitPeer k => simpa [resumeSender, hph, contRest] using h
  | crashed =>
    simp [resumeSender, hph, contRest]
    exact scope_empty D name

/-- Delivering a message installs that transition's program, which is in scope. -/
theorem deliver_scope (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    bulkScopeOf I.desc (tname id) (contRest a1.phase) = true := by
  -- Same splits as `deliver_life`. A tombstone for an older generation, and a
  -- message this state does not handle, install idle. A matching transition
  -- installs that transition's program, which `program_scope` accepts.
  simp only [deliver] at h
  revert h
  split
  · intro h; cases h
  · intro h
    split at h
    · cases h
      simp [contRest]
      exact scope_empty I.desc (tname id)
    · split at h
      · split at h
        · cases h
        · cases h
          simp [contRest]
          exact scope_empty I.desc (tname id)
      · next tr hfind =>
        split at h
        · cases h
        · cases h
          have hmem := findDeliver_mem I (tname id) a.typestate m tr hfind
          by_cases hempty : tr.program.isEmpty = true
          · simp [hempty, contRest]
            exact scope_empty I.desc (tname id)
          · have hemptyF : tr.program.isEmpty = false := by
              cases hbb : tr.program.isEmpty
              · rfl
              · exact absurd hbb hempty
            simp [hemptyF, contRest]
            simpa [hmem.2.1] using program_scope I hL tr hmem.1

/-- A delivered continuation stores the transition program and empty outcome lists.
`deliver_scope` is the program; the empty lists are in scope on their own. -/
theorem deliver_phase (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    phaseScope I.desc (tname id) a1.phase = true := by
  simp only [deliver] at h
  revert h
  split
  · intro h; cases h
  · intro h
    split at h
    · cases h
      simp [phaseScope]
    · split at h
      · split at h
        · cases h
        · cases h
          simp [phaseScope]
      · next tr hfind =>
        split at h
        · cases h
        · cases h
          have hmem := findDeliver_mem I (tname id) a.typestate m tr hfind
          by_cases hempty : tr.program.isEmpty = true
          · simp [hempty, phaseScope]
          · have hemptyF : tr.program.isEmpty = false := by
              cases hbb : tr.program.isEmpty
              · rfl
              · exact absurd hbb hempty
            simp [hemptyF, phaseScope, contArms, scope_empty]
            simpa [hmem.2.1] using program_scope I hL tr hmem.1

theorem bulk_or (I : Impl) (w w' : World) (hB : BulkFree I w)
    (h : ∀ id, phaseScope I.desc (tname id) (w'.st id).phase = true ∨
      (w'.st id).phase = (w.st id).phase) :
    BulkFree I w' := by
  intro id
  rcases h id with h | h
  · exact h
  · simpa [h] using hB id

theorem enqueue_phase_other (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hne : i ≠ sender) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).phase = (w.st i).phase := by
  cases isCall <;>
    (unfold enqueueOrPark
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive]
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom]
         by_cases hsame : sender = dst
         · have hdst : i ≠ dst := fun h => hne (h.trans hsame.symm)
           simp [hsame, setActor, hdst]
         · simp [hsame, setActor]
           by_cases hid : i = dst
           · have hflip : dst ≠ sender := fun h => hsame h.symm
             simp [setActor, hid, hflip]
           · simp [setActor, hid, hne]
       · simp [hroom]
         by_cases hsame : sender = dst
         · have hdst : i ≠ dst := fun h => hne (h.trans hsame.symm)
           simp [hsame, setActor, hdst]
         · simp [hsame, setActor]
           by_cases hid : i = dst
           · have hflip : dst ≠ sender := fun h => hsame h.symm
             simp [setActor, hid, hflip]
           · simp [setActor, hid, hne]
     · first
       | (simp [hlive, setActor, hne]; done)
       | (by_cases hdead : (w.st dst).life = .dead
          · simp [hlive, hdead, setActor, hne]
          · simp [hlive, hdead, setActor, hne]))

/-- The sender `enqueueOrPark` writes is either still on `k`, resumed by `proceed`,
or running `NotAdmitted`. Each of those is in scope when `k`'s arms are. -/
theorem scope_enqueue_sender (D : Description) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (h : contArms D (tname sender) k = true) :
    phaseScope D (tname sender) ((enqueueOrPark w D sender dst msg isCall k).st sender).phase = true := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall with
      | true =>
        by_cases hsame : sender = dst
        · subst hsame
          simp [setActor_self, phaseScope]
          exact h
        · simp [hsame, setActor_self, phaseScope]
          exact h
      | false =>
        by_cases hsame : sender = dst
        · subst hsame
          simpa [setActor_self] using phase_proceed D (tname sender) _ k h
        · simpa [hsame, setActor_self] using phase_proceed D (tname sender) _ k h
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        simp [setActor_self, phaseScope]
        exact h
      · simp [hsame, setActor_self, phaseScope]
        exact h
  · simp [hlive]
    cases isCall with
    | false =>
      simpa [setActor_self] using phase_proceed D (tname sender) _ k h
    | true =>
      simpa [setActor_self, finishCall, selectCall] using
        phase_proceed D (tname sender) _ (selectCall k .notAdmitted)
          (arms_notAdmitted D (tname sender) k h)

theorem phase_credit (w : World) (dst : String) (s i : InstId) :
    ((creditSender w dst s).st i).phase = (w.st i).phase :=
  (credit_life w dst s i).2.2.1

theorem phase_refund (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).phase = (w.st i).phase :=
  (refund_life w dst ms i).2.2.1

theorem phase_refundP (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).phase = (w.st i).phase :=
  (refundP_life w dst ps i).2.2.1

theorem bulk_finish (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : finishWait I w id = some w') : BulkFree I w' := by
  obtain ⟨k, hk, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  apply bulk_or I w _ hB
  intro i
  by_cases hi : i = id
  · rw [hi]
    simp [setActor_self]
    rcases hk with hk | hk
    · exact Or.inl (phase_proceed I.desc (tname id) (w.st id) k (by simpa [phaseScope, hk] using hB id))
    · exact Or.inl (phase_proceed I.desc (tname id) (w.st id) k (by simpa [phaseScope, hk] using hB id))
  · simp [setActor, hi]

/-- An ingress delivery leaves every phase where it was, so a bulk-free world stays bulk-free. -/
theorem bulk_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String) (hB : BulkFree I w)
    (h : receiveIngress I w dst label = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro id
  exact Or.inr (ingress_phase I w w' dst label id h).1

/-- `placePeer` writes one idle actor. `next` is a key bump and does not touch `st`. -/
theorem placePeer_phase (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World) (i : InstId) (hn : ∀ w, (next w).st = w.st) :
    ((placePeer I w template k initial parent next).st i).phase =
      if i = InstId.peer template k (maxGen w template k) then Phase.idle else (w.st i).phase := by
  unfold placePeer
  simp only [readCells_st]
  have hnext :
      (next { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] }).st i =
        w.st i := by
    rw [hn]
  by_cases hi : i = InstId.peer template k (maxGen w template k)
  · simp [setActor, hi, bornActor, withKeyTokens, hnext]
  · simp [setActor, hi, hnext]

theorem bulk_spawn (I : Impl) (w w' : World) (template : String) (hB : BulkFree I w)
    (h : spawn I w template = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro i
  simp only [spawn] at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some name =>
        simp only [hsup] at h
        let k := freshKey I.desc w t.subtree
        cases h
        have hph := placePeer_phase I w template k t.initial (some (.core name))
          (fun w1 => { w1 with nextKey := fun s => if s = t.subtree then k + 1 else w1.nextKey s })
          i (by intro _; rfl)
        by_cases hi : i = InstId.peer template k (maxGen w template k)
        · unfold k at hph hi
          exact Or.inl (by rw [hph, hi]; simp [phaseScope])
        · unfold k at hph hi
          exact Or.inr (by rw [hph]; simp [hi])
      | none =>
        simp only [hsup] at h
        by_cases hsub : (t.subtree == "") = true
        · simp only [hsub, ite_true] at h
          let k := w.nextIx template
          cases h
          have hph := placePeer_phase I w template k t.initial none
            (fun w1 => { w1 with nextIx := fun n => if n = template then k + 1 else w1.nextIx n })
            i (by intro _; rfl)
          by_cases hi : i = InstId.peer template k (maxGen w template k)
          · unfold k at hph hi
            exact Or.inl (by rw [hph, hi]; simp [phaseScope])
          · unfold k at hph hi
            exact Or.inr (by rw [hph]; simp [hi])
        · have hsubF : (t.subtree == "") = false := by
            cases hb : t.subtree == ""
            · rfl
            · exact absurd hb hsub
          simp only [hsubF, ite_false] at h
          let k := freshKey I.desc w t.subtree
          cases h
          have hph := placePeer_phase I w template k t.initial none
            (fun w1 => { w1 with nextKey := fun s => if s = t.subtree then k + 1 else w1.nextKey s })
            i (by intro _; rfl)
          by_cases hi : i = InstId.peer template k (maxGen w template k)
          · unfold k at hph hi
            exact Or.inl (by rw [hph, hi]; simp [phaseScope])
          · unfold k at hph hi
            exact Or.inr (by rw [hph]; simp [hi])
    · simp [hmay] at h

/-- Resuming a waiter keeps every stored list in scope. A non-call resumes by
`proceed`; a call moves to `awaitReply` on the same continuation. Any other
phase is left as it is. -/
theorem phase_resume (D : Description) (name : String) (a : Actor) (b : Bool) (dst : InstId)
    (h : phaseScope D name a.phase = true) :
    phaseScope D name (resumeSender a b dst).phase = true := by
  cases hph : a.phase with
  | parked _ _ k =>
    have har : contArms D name k = true := by simpa [phaseScope, hph] using h
    cases b with
    | true => simpa [resumeSender, hph, phaseScope] using har
    | false =>
      simpa [resumeSender, hph] using phase_proceed D name a k har
  | idle => simpa [resumeSender, hph] using h
  | run k => simpa [resumeSender, hph] using h
  | awaitReply _ k => simpa [resumeSender, hph] using h
  | awaitEffect k => simpa [resumeSender, hph] using h
  | awaitPeer k => simpa [resumeSender, hph] using h
  | crashed => simpa [resumeSender, hph] using h

theorem release_bulk (I : Impl) (w : World) (id : InstId) (ps : List Parked)
    (hB : BulkFree I w) : BulkFree I (releaseParked w id ps) := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hB
  | cons p ps ih =>
    unfold releaseParked
    simp only [List.foldl_cons]
    by_cases hskip : p.isCall = true ∨ p.sender = id
    · simp [hskip]
      simpa [releaseParked] using ih w hB
    · simp [hskip]
      have hB' : BulkFree I (setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
        apply bulk_or I w _ hB
        intro i
        by_cases hi : i = p.sender
        · rw [hi]
          simp [setActor]
          exact Or.inl (phase_resume I.desc (tname p.sender) (w.st p.sender) false id (hB p.sender))
        · simp [setActor, hi]
      simpa [releaseParked] using ih _ hB'

/-- A full priority lane crashes the roster. `tryWake` used to be stated as
keeping every phase; that is false when `offerPrio` crashes. What bulk scope
needs is the disjunction `crashWorld` already has: an actor who was alive
has an empty rest, and everyone else keeps the phase that was in scope. -/
theorem scope_crash (D : Description) (w : World) (s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((crashWorld w).st s).phase = true := by
  by_cases hmem : s ∈ w.roster
  · simp only [crashWorld, hmem, ite_true, crashActor]
    by_cases hla : ((w.st s).life == .alive) = true
    · simp [hla, phaseScope]
    · have hlaF : ((w.st s).life == .alive) = false := by
        cases hbb : (w.st s).life == .alive
        · rfl
        · exact absurd hbb hla
      simpa [hlaF] using h
  · simpa [crashWorld, hmem] using h

theorem scope_offer (D : Description) (w : World) (host : InstId) (msg : Msg) (s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((offerPrio D w host msg).st s).phase = true := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp only [hfull, ite_true]
    exact scope_crash D w s h
  · have hfullF : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = false := by
      cases hbb : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host)
      · rfl
      · exact absurd hbb hfull
    simp only [hfullF, ite_false]
    by_cases hs : s = host
    · subst hs
      simp [setActor_self]
      exact h
    · simpa [setActor, hs] using h

theorem scope_tryWake (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer s : InstId) (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((tryWake D w dstId label writer).st s).phase = true := by
  unfold tryWake
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp only [hskip, ite_true]
    exact h
  · have hskipF : ((w.st dstId).life != .alive ||
        (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      cases hbb : (w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)
      · rfl
      · exact absurd hbb hskip
    simp only [hskipF, ite_false]
    exact scope_offer D w dstId _ s h

theorem scope_wakeFold (ids : List InstId) (D : Description) (w : World) (dst label : String)
    (writer s : InstId) (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s)
      ((ids.foldl (fun w id => tryWake D w id label writer) w).st s).phase = true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact ih _ (scope_tryWake D w j label writer s h)

theorem scope_wakeReaders (D : Description) (w : World) (dst label : String) (writer s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((wakeReaders D w dst label writer).st s).phase = true := by
  simpa [wakeReaders] using scope_wakeFold (readersOf w dst) D w dst label writer s h

theorem scope_failWaiter (D : Description) (w : World) (dead i s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((failWaiter w dead i).st s).phase) = true := by
  by_cases hs : s = i
  · rw [hs] at h ⊢
    unfold failWaiter
    split
    · exact h
    · cases hph : (w.st i).phase with
      | parked d b k =>
        cases b with
        | false =>
          have hrest : bulkScopeOf D (tname i) k.rest = true := by simpa [contRest, hph] using h
          simp [hph]
          split
          · cases hk : k.rest with
            | nil =>
              simp [setActor_self, proceed, hk, contRest]
              exact scope_empty D (tname i)
            | cons _ _ => simpa [setActor_self, proceed, hk, contRest] using hrest
          · exact h
        | true => simpa [hph, contRest] using h
      | awaitReply _ _ => simpa [hph, contRest] using h
      | idle => simpa [hph, contRest] using h
      | run k => simpa [hph, contRest] using h
      | awaitEffect k => simpa [hph, contRest] using h
      | awaitPeer k => simpa [hph, contRest] using h
      | crashed => simpa [hph, contRest] using h
  · rw [failWaiter_other w dead i s hs]
    exact h

theorem scope_failFold (D : Description) (w : World) (dead s : InstId) (ids : List InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s)
      (contRest ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase) = true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (scope_failWaiter D w dead i s h)

/-- Killing one actor leaves every continuation in the scope it had. The victim
goes idle; a waiter resumes the tail it was already allowed to run. -/
theorem scope_killOne (D : Description) (w : World) (id s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((killOne w D id).st s).phase) = true := by
  by_cases hs : s = id
  · rw [hs, (killOne_self w D id).2.1]
    simp [contRest]
    exact scope_empty D (tname id)
  · let w1 := readCells D w id
    have hst1 : w1.st s = w.st s := cellsSt D w id s
    have h1 : bulkScopeOf D (tname s) (contRest (w1.st s).phase) = true := by simpa [hst1] using h
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have hph2 : (w2.st s).phase = (w1.st s).phase := by
      simpa [w2] using (refundMsgs_rest w1 (tname id) (w.st id).box s).1
    have h2 : bulkScopeOf D (tname s) (contRest (w2.st s).phase) = true := by simpa [hph2] using h1
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have hph3 : (w3.st s).phase = (w2.st s).phase := by
      simpa [w3] using (refundParked_rest w2 (tname id) (w.st id).parked s).1
    have h3 : bulkScopeOf D (tname s) (contRest (w3.st s).phase) = true := by simpa [hph3] using h2
    let w4 := failWaiters w3 id
    have h4 : bulkScopeOf D (tname s) (contRest (w4.st s).phase) = true := by
      simpa [w4, failWaiters] using scope_failFold D w3 id s w3.roster h3
    let w5 := forgetSender w4 id
    have hph5 : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using (forget_stable w4 id s).1
    have h5 : bulkScopeOf D (tname s) (contRest (w5.st s).phase) = true := by simpa [hph5] using h4
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hs]
    exact h5

theorem scope_killFold (D : Description) (w : World) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase) =
      true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (scope_killOne D w j s h)
    · simp only [hcond]
      exact ih w h

theorem release_victim_phase (w : World) (id : InstId) (ps : List Parked) :
    ((releaseParked w id ps).st id).phase = (w.st id).phase := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hne : p.sender ≠ id := by
        intro hs
        exact hskip (by simp [hs])
      have hst : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st id).phase =
          (w.st id).phase := by
        simp [setActor, Ne.symm hne]
      exact (ih _).trans hst

theorem scope_releaseParked (D : Description) (w : World) (id s : InstId) (ps : List Parked)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((releaseParked w id ps).st s).phase) = true := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using h
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w h
    · rw [if_neg hskip]
      by_cases hs : s = p.sender
      · have hsc := resume_scope D (tname p.sender) (w.st p.sender) false id (by simpa [hs] using h)
        exact ih _
          (by simpa [setActor_self, hs] using hsc)
      · have hph : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st s).phase =
            (w.st s).phase := by simp [setActor, hs]
        exact ih _ (by simpa [hph] using h)

/-- `releaseParked` skips the sealed actor, so that actor is written back unchanged. -/
theorem releaseParked_self (w : World) (id : InstId) (ps : List Parked) :
    (releaseParked w id ps).st id = w.st id := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hne : p.sender ≠ id := by
        intro hs
        exact hskip (by simp [hs])
      have hst : (setActor w p.sender (resumeSender (w.st p.sender) false id)).st id = w.st id := by
        simp [setActor, Ne.symm hne]
      exact (ih _).trans hst

theorem phase_releaseParked (D : Description) (w : World) (id s : InstId) (ps : List Parked)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((releaseParked w id ps).st s).phase = true := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using h
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w h
    · rw [if_neg hskip]
      by_cases hs : s = p.sender
      · exact ih _ (by
          simpa [setActor_self, hs] using
            phase_resume D (tname p.sender) (w.st p.sender) false id (by simpa [hs] using h))
      · have hph : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st s).phase =
            (w.st s).phase := by simp [setActor, hs]
        exact ih _ (by simpa [hph] using h)

theorem scope_releaseWorld (D : Description) (w : World) (id : InstId) (a : Actor) (s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((releaseWorld D w id a).st s).phase = true := by
  let base := refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked
  let cleared := releaseOutbound base id
  let dead : Actor :=
    { cleared.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hworld : releaseWorld D w id a = releaseParked (setActor cleared id dead) id a.parked := by
    simp [releaseWorld, base, cleared, dead]
  rw [hworld]
  by_cases hs : s = id
  · rw [hs]
    have hidle : ((setActor cleared id dead).st id).phase = .idle := by simp [setActor, dead]
    rw [release_victim_phase (setActor cleared id dead) id a.parked, hidle]
    simp [phaseScope]
  · have hph : ((setActor cleared id dead).st s).phase = (w.st s).phase := by
      have hclear : (cleared.st s).phase = (base.st s).phase := by
        simpa [cleared] using releaseOutbound_phase base id s
      simp [setActor, hs, hclear, base, phase_refundP, phase_refund, readCells_st]
    exact phase_releaseParked D (setActor cleared id dead) id s a.parked (by simpa [hph] using h)

/-- The actor `releaseWorld` seals is dead, idle, and has an empty mailbox.
`releaseParked` does not write that actor: a self-send is skipped. -/
theorem release_quiet (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).life = .dead ∧
      ((releaseWorld D w id a).st id).phase = .idle ∧
      ((releaseWorld D w id a).st id).box = [] ∧
      ((releaseWorld D w id a).st id).prio = [] ∧
      ((releaseWorld D w id a).st id).parked = [] := by
  let base := refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked
  let cleared := releaseOutbound base id
  let dead : Actor :=
    { cleared.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hr : releaseWorld D w id a = releaseParked (setActor cleared id dead) id a.parked := by
    simp [releaseWorld, base, cleared, dead]
  rw [hr, releaseParked_self]
  simp [setActor_self, dead]

/-- Queuing the tombstone does not put mail or a continuation back on the child.
The child is already dead, so a crash leaves it as `releaseWorld` wrote it, and
the offer is written on the parent. -/
theorem enqueue_quiet (D : Description) (w : World) (child : InstId)
    (hl : (w.st child).life = .dead) (hp : (w.st child).phase = .idle)
    (hb : (w.st child).box = []) (hpr : (w.st child).prio = []) (hpk : (w.st child).parked = []) :
    ((enqueueTombstone D w child).st child).life = .dead ∧
      ((enqueueTombstone D w child).st child).phase = .idle ∧
      ((enqueueTombstone D w child).st child).box = [] ∧
      ((enqueueTombstone D w child).st child).prio = [] ∧
      ((enqueueTombstone D w child).st child).parked = [] := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simp [hpar, hl, hp, hb, hpr, hpk]
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp [hlive, hl, hp, hb, hpr, hpk]
    · have hliveF : ((w.st parent).life != .alive) = false := by
        cases hbb : (w.st parent).life != .alive
        · rfl
        · exact absurd hbb hlive
      simp only [hliveF, ite_false]
      have hne : parent ≠ child := by
        intro hs
        have hdead : (w.st parent).life = .dead := by simpa [hs] using hl
        have hbit : ((w.st parent).life != .alive) = true := by simp [hdead]
        -- `hliveF` is `= false`, so `absurd` does not apply. Rewriting produces `true = false`.
        simp [hbit] at hliveF
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        have hdead : ((w.st child).life == .alive) = false := by simp [hl]
        simp [crashWorld, crashActor, hdead, hl, hp, hb, hpr, hpk]
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hbb : (tombstoneMsg D (w.st parent) child).label == ""
          · rfl
          · exact absurd hbb hlab
        simp only [hlabF, ite_false]
        unfold offerPrio
        by_cases hfull : decide (prioLoad (w.st parent).prio ≥ capPrio D w.N parent) = true
        · simp only [hfull, ite_true]
          have hdead : ((w.st child).life == .alive) = false := by simp [hl]
          simp [crashWorld, crashActor, hdead, hl, hp, hb, hpr, hpk]
        · have hfullF : decide (prioLoad (w.st parent).prio ≥ capPrio D w.N parent) = false := by
            cases hbb : decide (prioLoad (w.st parent).prio ≥ capPrio D w.N parent)
            · rfl
            · exact absurd hbb hfull
          have hc : child ≠ parent := Ne.symm hne
          simp [hfullF, setActor, hc, hl, hp, hb, hpr, hpk]

theorem seal_quiet (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((sealActor D w id a).st id).life = .dead ∧
      ((sealActor D w id a).st id).phase = .idle ∧
      ((sealActor D w id a).st id).box = [] ∧
      ((sealActor D w id a).st id).prio = [] ∧
      ((sealActor D w id a).st id).parked = [] := by
  unfold sealActor
  have hq := release_quiet D w id a
  exact enqueue_quiet D (releaseWorld D w id a) id hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2

theorem scope_enqueue (D : Description) (w : World) (child s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((enqueueTombstone D w child).st s).phase = true := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simpa [hpar] using h
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp only [hlive, ite_true]
      exact h
    · have hliveF : ((w.st parent).life != .alive) = false := by
        cases hbb : (w.st parent).life != .alive
        · rfl
        · exact absurd hbb hlive
      simp only [hliveF, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        exact scope_crash D w s h
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hbb : (tombstoneMsg D (w.st parent) child).label == ""
          · rfl
          · exact absurd hbb hlab
        simp only [hlabF, ite_false]
        exact scope_offer D w parent _ s h

theorem scope_shutdown (D : Description) (w : World) (id s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((shutdownActor D w id).st s).phase = true := by
  unfold shutdownActor
  by_cases hl : ((w.st id).life == .alive) = true
  · simp only [hl, ite_true]
    exact scope_enqueue D (releaseWorld D w id (w.st id)) id s
      (scope_releaseWorld D w id (w.st id) s h)
  · have hlf : ((w.st id).life == .alive) = false := by
      cases hbb : (w.st id).life == .alive
      · rfl
      · exact absurd hbb hl
    simp only [hlf, ite_false]
    exact h

theorem scope_sealFold (D : Description) (fuel : Nat) (id : InstId) (ids : List InstId)
    (w : World) (s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true)
    (ih : ∀ w' c, phaseScope D (tname s) (w'.st s).phase = true →
      phaseScope D (tname s) ((sealBranch fuel D w' c).st s).phase = true) :
    phaseScope D (tname s) ((ids.foldl (fun acc child =>
      if isChild acc id child then sealBranch fuel D acc child else acc) w).st s).phase = true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons c cs ihf =>
    simp only [List.foldl_cons]
    by_cases hc : isChild w id c = true
    · simp only [hc, ite_true]
      exact ihf _ (ih w c h)
    · have hcf : isChild w id c = false := by
        cases hbb : isChild w id c
        · rfl
        · exact absurd hbb hc
      simp only [hcf, ite_false]
      exact ihf _ h

theorem scope_sealBranch (D : Description) (fuel : Nat) (w : World) (id s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((sealBranch fuel D w id).st s).phase = true := by
  induction fuel generalizing w id with
  | zero => simpa [sealBranch] using h
  | succ fuel ih =>
    unfold sealBranch
    dsimp only
    have hfold := scope_sealFold D fuel id w.roster w s h ih
    generalize hse : w.roster.foldl (fun acc child =>
      if isChild acc id child then sealBranch fuel D acc child else acc) w = sealed at hfold ⊢
    by_cases hl : ((sealed.st id).life == .alive) = true
    · simp only [hl, ite_true]
      exact scope_releaseWorld D sealed id (sealed.st id) s hfold
    · have hlf : ((sealed.st id).life == .alive) = false := by
        cases hbb : (sealed.st id).life == .alive
        · rfl
        · exact absurd hbb hl
      simp only [hlf, ite_false]
      exact hfold

theorem scope_drop (D : Description) (w : World) (id s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((dropDescendants D w id).st s).phase = true := by
  unfold dropDescendants
  exact scope_sealFold D w.roster.length id w.roster w s h
    (fun w' c hw' => scope_sealBranch D _ w' c s hw')

/-- What an abort does to bulk scope.

`abortChildren` seals each live child by `dropDescendants` then `shutdownActor`.
`seal_quiet` is one such seal: the child is dead, idle, and its mailbox is empty,
so its rest is empty. A descendant sealed by `sealBranch` is `releaseWorld`'d the
same way, and its tombstone is not queued.

That is not "every other actor's rest is empty". `AbortRest` is the regression:
a core that is not a child keeps the program it was running. Two further writes
stay inside the scope this theorem carries:

* `refundMsgs` credits a sender's tokens. The sender's phase, and therefore its
  rest, stays. The whole `st` does not.
* `releaseParked` resumes a non-call waiter onto the continuation it already
  held (`resume_scope`). A crash from an empty tombstone label or a full lane
  (`scope_crash`) gives every actor who was still alive an empty rest.

`BulkFree` uses this theorem, not a frame that freezes `st`. -/
theorem scope_abortChildren (D : Description) (w : World) (parent s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((abortChildren D w parent).st s).phase = true := by
  unfold abortChildren
  suffices ∀ (ids : List InstId) (w0 : World), phaseScope D (tname s) (w0.st s).phase = true →
      phaseScope D (tname s) ((ids.foldl (fun w child =>
        if isChild w parent child && (w.st child).life == .alive then
          shutdownActor D (dropDescendants D w child) child
        else w) w0).st s).phase = true from
    this w.roster w h
  intro ids
  induction ids with
  | nil => intro w0 h0; simpa using h0
  | cons c cs ih =>
    intro w0 h0
    simp only [List.foldl_cons]
    by_cases hgo : (isChild w0 parent c && (w0.st c).life == .alive) = true
    · simp only [hgo, ite_true]
      exact ih _ (scope_shutdown D (dropDescendants D w0 c) c s (scope_drop D w0 c s h0))
    · have hcf : (isChild w0 parent c && (w0.st c).life == .alive) = false := by
        cases hbb : isChild w0 parent c && (w0.st c).life == .alive
        · rfl
        · exact absurd hbb hgo
      simp only [hcf, ite_false]
      exact ih _ h0

/-- A per-peer `terminate` seals descendants, then the actor itself.
A core `terminate` is `crashWorld` and does not use this theorem. `seal_quiet`
is the actor's own seal; `scope_drop` is the descendants. -/
theorem scope_terminateStage (D : Description) (w : World) (id s : InstId)
    (h : phaseScope D (tname s) (w.st s).phase = true) :
    phaseScope D (tname s) ((terminateStage D w id (w.st id)).st s).phase = true := by
  unfold terminateStage
  dsimp only
  exact scope_shutdown D (dropDescendants D w id) id s (scope_drop D w id s h)

theorem scope_killSubtree (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((killSubtree w D sub key).st s).phase) = true := by
  simpa [killSubtree, killMembers] using scope_killFold D w sub key w.roster s h

theorem bulk_exec (I : Impl) (w : World) (id : InstId) (k : Cont) (hB : BulkFree I w)
    (hlive : (w.st id).life = .alive) (hph : (w.st id).phase = .run k) :
    BulkFree I (execRun I w id (w.st id) k) := by
  have hgo : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  apply bulk_or I w _ hB
  intro i
  cases hrest : k.rest with
    | nil =>
      by_cases hi : i = id
      · rw [hi]
        simp [execRun, hgo, hrest, setActor_self, phaseScope]
      · simp [execRun, hgo, hrest, setActor, hi]
    | cons e es =>
      cases e with
      | send dst label hint =>
        simp only [execRun, hgo, hrest]
        have hhead : contArms I.desc (tname id) (afterHead k) = true :=
          arms_skip I.desc (tname id) k (.send dst label hint) es
            (by simpa [phaseScope, hph] using hB id) hrest
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr, noteStale_st]
          by_cases hi : i = id
          · rw [hi]
            simp [setActor_self]
            exact Or.inl (phase_after I.desc (tname id) (w.st id) k (.send dst label hint) es
              (by simpa [phaseScope, hph] using hB id) hrest)
          · simp [setActor, hi]
        | some dstId =>
          simp only [hr]
          by_cases hi : i = id
          · rw [hi]
            exact Or.inl (scope_enqueue_sender I.desc w id dstId
              { label := label, sender := id, callFrom := none } false (afterHead k) hhead)
          · exact Or.inr (enqueue_phase_other w I.desc id dstId
              { label := label, sender := id, callFrom := none } false (afterHead k) i hi)
      | call dst label hint onNotAdmitted onTimedOut =>
        simp only [execRun, hgo, hrest]
        have hprog : bulkScopeOf I.desc (tname id)
            (.call dst label hint onNotAdmitted onTimedOut :: es) = true := by
          simpa [contRest, hrest] using scope_rest I.desc (tname id) (.run k) (by simpa [phaseScope, hph] using hB id)
        have hwait : contArms I.desc (tname id)
            { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } = true :=
          arms_out I.desc (tname id) (afterHead k) onNotAdmitted onTimedOut
            (arms_skip I.desc (tname id) k (.call dst label hint onNotAdmitted onTimedOut) es
              (by simpa [phaseScope, hph] using hB id) hrest)
            (scope_onNotAdmitted I.desc (tname id) dst label hint onNotAdmitted onTimedOut es hprog)
            (scope_onTimedOut I.desc (tname id) dst label hint onNotAdmitted onTimedOut es hprog)
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp only [hr, noteStale_st]
          by_cases hi : i = id
          · rw [hi]
            simpa [setActor_self, finishCall, selectCall] using
              Or.inl (phase_proceed I.desc (tname id) (issueCall (w.st id))
                (selectCall { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
                  .notAdmitted)
                (arms_notAdmitted I.desc (tname id)
                  { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } hwait))
          · simp [setActor, hi]
        | some dstId =>
          simp only [hr]
          by_cases hi : i = id
          · rw [hi]
            exact Or.inl (scope_enqueue_sender I.desc w id dstId
              { label := label, sender := id, callFrom := some id } true
              { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } hwait)
          · exact Or.inr (enqueue_phase_other w I.desc id dstId
              { label := label, sender := id, callFrom := some id } true
              { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } i hi)
      | trySend dst label hint onFull onGone =>
        simp only [execRun, hgo, hrest]
        have hprog : bulkScopeOf I.desc (tname id)
            (.trySend dst label hint onFull onGone :: es) = true := by
          simpa [contRest, hrest] using scope_rest I.desc (tname id) (.run k) (by simpa [phaseScope, hph] using hB id)
        have hhead : contArms I.desc (tname id) (afterHead k) = true :=
          arms_skip I.desc (tname id) k (.trySend dst label hint onFull onGone) es
            (by simpa [phaseScope, hph] using hB id) hrest
        let kFull := { afterHead k with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull }
        let kGone := { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone }
        have hfull : contArms I.desc (tname id) kFull = true :=
          arms_rest I.desc (tname id) (afterHead k) onFull hhead
            (scope_onFull I.desc (tname id) dst label hint onFull onGone es hprog)
        have hgone : contArms I.desc (tname id) kGone = true :=
          arms_rest I.desc (tname id) (afterHead k) onGone hhead
            (scope_onGone I.desc (tname id) dst label hint onFull onGone es hprog)
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr, noteStale_st]
          by_cases hi : i = id
          · rw [hi]
            simpa [setActor_self, kGone] using Or.inl (phase_proceed I.desc (tname id) (w.st id) kGone hgone)
          · simp [setActor, hi]
        | some dstId =>
          simp only [hr]
          by_cases hadmit : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
          · simp only [hadmit, ite_true]
            by_cases hi : i = id
            · rw [hi]
              exact Or.inl (scope_enqueue_sender I.desc w id dstId
                { label := label, sender := id, callFrom := none, reliable := false } false
                (afterHead k) hhead)
            · exact Or.inr (enqueue_phase_other w I.desc id dstId
                { label := label, sender := id, callFrom := none, reliable := false } false
                (afterHead k) i hi)
          · rw [ite_eq_right hadmit]
            by_cases halive : ((w.st dstId).life == .alive) = true
            · simp only [halive, ite_true]
              by_cases hi : i = id
              · rw [hi]
                simpa [setActor_self, kFull] using Or.inl (phase_proceed I.desc (tname id) (w.st id) kFull hfull)
              · simp [setActor, hi]
            · rw [ite_eq_right halive]
              by_cases hi : i = id
              · rw [hi]
                simpa [setActor_self, kGone] using Or.inl (phase_proceed I.desc (tname id) (w.st id) kGone hgone)
              · simp [setActor, hi]
      | reply =>
        simp [execRun, hgo, hrest]
        unfold performReply
        cases hto : k.replyTo with
        | none =>
          simp [hto, setActor]
          by_cases hi : i = id
          · rw [hi]
            simp [setActor]
            exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
              (by simpa [phaseScope, hph] using hB id) hrest)
          · simp [hi]
        | some caller =>
          simp [hto]
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            simp [hcall]
            by_cases hd : dst = id
            · by_cases howe : (w.st id).oweId = some (w.st caller).waitId
              · simp [hd, howe, setActor]
                by_cases hi : i = id
                · rw [hi]
                  simp [setActor]
                  exact Or.inl (phase_after I.desc (tname id)
                    (if id = caller then finishCall (w.st caller) ck .reply else w.st id)
                    k .reply es
                    (by simpa [phaseScope, hph] using hB id) hrest)
                · by_cases hc : i = caller
                  · by_cases hself : caller = id
                    · exact absurd (hc.trans hself) hi
                    · rw [hc]
                      simpa [setActor, hi, hself, finishCall, selectCall] using
                        Or.inl (phase_proceed I.desc (tname caller) (w.st caller) ck
                          (by simpa [phaseScope, hcall] using hB caller))
                  · simp [setActor, hi, hc]
              · simp [hd, howe, setActor]
                by_cases hi : i = id
                · rw [hi]
                  simp [setActor]
                  exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                    (by simpa [phaseScope, hph] using hB id) hrest)
                · simp [hi]
            · simp [hd, setActor]
              by_cases hi : i = id
              · rw [hi]
                simp [setActor]
                exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                  (by simpa [phaseScope, hph] using hB id) hrest)
              · simp [hi]
          | idle =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
          | run ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
          | parked dst b ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
          | awaitEffect ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
          | awaitPeer ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
          | crashed =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (phase_after I.desc (tname id) (w.st id) k .reply es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [hi]
      | selfSchedule label =>
        simp only [execRun, hgo, hrest]
        by_cases hqueued : ((w.st id).prio.any (fun p => p.label == label)) = true
        · simp only [hqueued, ite_true]
          by_cases hi : i = id
          · rw [hi]
            simp [setActor_self]
            exact Or.inl (phase_after I.desc (tname id) (w.st id) k (.selfSchedule label) es
              (by simpa [phaseScope, hph] using hB id) hrest)
          · simp [setActor, hi]
        · have hqueuedF : ((w.st id).prio.any (fun p => p.label == label)) = false := by
            cases hbb : (w.st id).prio.any (fun p => p.label == label)
            · rfl
            · exact absurd hbb hqueued
          simp only [hqueuedF, ite_false]
          by_cases hroom : prioLoad (w.st id).prio < capPrio I.desc w.N id
          · simp only [hroom, ite_true]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor_self]
              exact Or.inl (phase_after I.desc (tname id) _ k (.selfSchedule label) es
                (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [setActor, hi]
          · simp only [hroom, ite_false]
            exact Or.inl (scope_crash I.desc w i (hB i))
      | cell dst label value =>
        simp only [execRun, hgo, hrest]
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp only [hdirty, ite_true]
          by_cases hi : i = id
          · rw [hi]
            simp [setCell, setActor_self]
            exact Or.inl (phase_after I.desc (tname id) (w.st id) k (.cell dst label value) es
              (by simpa [phaseScope, hph] using hB id) hrest)
          · simp [setCell, setActor, hi]
        · have hdirtyF : (w.cell dst label).dirty = false := by
            cases hbb : (w.cell dst label).dirty
            · rfl
            · exact absurd hbb hdirty
          simp only [hdirtyF, ite_false]
          refine Or.inl ?_
          apply scope_wakeReaders
          by_cases hi : i = id
          · rw [hi]
            simp [setCell, setActor_self]
            exact phase_after I.desc (tname id) ((setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }).st id) k (.cell dst label value) es
              (by simpa [phaseScope, hph] using hB id) hrest
          · simp [setCell, setActor, hi]
            exact hB i
      | internal =>
        simp only [execRun, hgo, hrest]
        by_cases hi : i = id
        · rw [hi]
          simpa [setActor_self, phaseScope] using Or.inl
            (arms_skip I.desc (tname id) k .internal es (by simpa [phaseScope, hph] using hB id) hrest)
        · simp [setActor, hi]
      | peer onTimeout =>
        simp only [execRun, hgo, hrest]
        by_cases hi : i = id
        · rw [hi]
          have hprog : bulkScopeOf I.desc (tname id) (.peer onTimeout :: es) = true := by
            simpa [contRest, hrest] using scope_rest I.desc (tname id) (.run k) (by simpa [phaseScope, hph] using hB id)
          simpa [setActor_self, phaseScope] using Or.inl
            (arms_timeout I.desc (tname id) (afterHead k) onTimeout
              (arms_skip I.desc (tname id) k (.peer onTimeout) es
                (by simpa [phaseScope, hph] using hB id) hrest)
              (scope_onTimeout I.desc (tname id) onTimeout es hprog))
        · simp [setActor, hi]
      | abort =>
        simp only [execRun, hgo, hrest]
        have hAb : phaseScope I.desc (tname i) ((abortChildren I.desc w id).st i).phase = true :=
          scope_abortChildren I.desc w id i (hB i)
        by_cases hcr : (abortChildren I.desc w id).crashed = true
        · simp only [commitCont, hcr, ite_true]
          exact Or.inl hAb
        · have hcrF : (abortChildren I.desc w id).crashed = false := by
            cases hbb : (abortChildren I.desc w id).crashed
            · rfl
            · exact absurd hbb hcr
          simp only [commitCont, hcrF, ite_false]
          by_cases hi : i = id
          · simp [setActor_self, hi]
            exact Or.inl (phase_after I.desc (tname id) ((abortChildren I.desc w id).st id) k .abort es
              (by simpa [phaseScope, hph] using hB id) hrest)
          · exact Or.inl (by simpa [setActor, hi] using hAb)
      | spawn child =>
        simp only [execRun, hgo, hrest]
        cases hs : spawnChild I w id child with
        | none =>
          simp only [hs]
          exact Or.inl (scope_crash I.desc w i (hB i))
        | some w' =>
          simp only [hs]
          by_cases hcr : w'.crashed = true
          · simp only [commitCont, hcr, ite_true]
            rcases spawnChild_phase I w w' id child i hs with hsame | hidle
            · exact Or.inr hsame
            · exact Or.inl (by simp [phaseScope, hidle])
          · have hcrF : w'.crashed = false := by
              cases hbb : w'.crashed
              · rfl
              · exact absurd hbb hcr
            simp only [commitCont, hcrF, ite_false]
            by_cases hi : i = id
            · rw [hi]
              simpa [setActor_self] using Or.inl (phase_after I.desc (tname id) (w'.st id) k
                (.spawn child) es (by simpa [phaseScope, hph] using hB id) hrest)
            · simp [setActor, hi]
              rcases spawnChild_phase I w w' id child i hs with hsame | hidle
              · exact Or.inr hsame
              · exact Or.inl (by simp [phaseScope, hidle])
      | terminate =>
        simp only [execRun, hgo, hrest]
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp only [ht]
          exact Or.inl (scope_crash I.desc w i (hB i))
        | some t =>
          simp only [ht]
          by_cases hcore : (t.multiplicity == .one) = true
          · simp only [hcore, ite_true]
            exact Or.inl (scope_crash I.desc w i (hB i))
          · rw [ite_eq_right hcore]
            by_cases htree : (t.multiplicity == .perPeer && t.subtree != "") = true
            · simp only [htree, ite_true]
              exact Or.inl (scope_terminateStage I.desc w id i (hB i))
            · rw [ite_eq_right htree]
              by_cases hlone : (t.terminable && t.subtree == "" && !hasParkedCall (w.st id).parked &&
                  !(hasChild I.desc w id)) = true
              · simp only [hlone, ite_true]
                exact Or.inl (scope_shutdown I.desc w id i (hB i))
              · rw [ite_eq_right hlone]
                by_cases hcascade : (t.terminable && t.subtree == "" && !hasParkedCall (w.st id).parked &&
                    hasChild I.desc w id) = true
                · simp only [hcascade, ite_true]
                  exact Or.inl (scope_terminateStage I.desc w id i (hB i))
                · rw [ite_eq_right hcascade]
                  exact Or.inl (scope_crash I.desc w i (hB i))

theorem bulk_head (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : execHead I w id = some w') : BulkFree I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact bulk_exec I w id k hB hlive hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem place_bulk (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor) (dst : String) (sender : InstId)
    (hn : phaseScope I.desc (tname id) a1.phase = true)
    (hst : ∀ i, w1.st i = w.st i) (hB : BulkFree I w) :
    BulkFree I (creditLive (setActor w1 id a1) dst sender) := by
  apply bulk_or I w _ hB
  intro i
  by_cases hi : i = id
  · rw [hi]
    simp [creditLive, phase_credit, setActor]
    exact Or.inl hn
  · simp [creditLive, phase_credit, setActor, hi, hst i]

theorem place_actor (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor)
    (hn : phaseScope I.desc (tname id) a1.phase = true)
    (hst : ∀ i, w1.st i = w.st i) (hB : BulkFree I w) :
    BulkFree I (setActor w1 id a1) := by
  apply bulk_or I w _ hB
  intro i
  by_cases hi : i = id
  · rw [hi]
    simp [setActor]
    exact Or.inl hn
  · simp [setActor, hi, hst i]

theorem resume_bulk (I : Impl) (w : World) (sender : InstId) (b : Bool) (dst : InstId)
    (hB : BulkFree I w) :
    BulkFree I (setActor w sender (resumeSender (w.st sender) b dst)) := by
  apply bulk_or I w _ hB
  intro i
  by_cases hi : i = sender
  · rw [hi]
    simp [setActor]
    exact Or.inl (phase_resume I.desc (tname sender) (w.st sender) b dst (hB sender))
  · simp [setActor, hi]

theorem bulk_recv (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : receiveBulk I w id = some w') : BulkFree I w' := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hplace := place_bulk I w w1 id a1 (tname id) p.msg.sender
            (deliver_phase I hL w id _ p.msg w1 a1 hdel)
            (fun i => deliver_st I w id _ p.msg w1 a1 i hdel) hB
          exact resume_bulk I _ p.sender p.isCall id hplace
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          exact place_bulk I w w1 id a1 (tname id) m.sender
            (deliver_phase I hL w id _ m w1 a1 hdel)
            (fun i => deliver_st I w id _ m w1 a1 i hdel) hB
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hph : admitted.phase = a1.phase := by simp [admitted]
          have hplace := place_bulk I w w1 id admitted (tname id) m.sender
            (by simpa [hph] using deliver_phase I hL w id _ m w1 a1 hdel)
            (fun i => deliver_st I w id _ m w1 a1 i hdel) hB
          simpa [admitted] using resume_bulk I _ p.sender p.isCall id hplace

theorem bulk_prio (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : receivePrio I w id = some w') : BulkFree I w' := by
  unfold receivePrio at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    obtain ⟨m, _, _, w1, a1, _, _, hdel, hw'⟩ :=
      receivePrioFrom_spec I w id [] (w.st id).prio w' h
    rw [hw']
    exact place_actor I w w1 id a1
      (deliver_phase I hL w id _ m w1 a1 hdel)
      (fun i => deliver_st I w id _ m w1 a1 i hdel) hB

/-- Failing a waiter either keeps its continuation or drops it. Either way a
terminable program stays free of bulk sends. -/
theorem nobulk_failWaiter (w : World) (dead i s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((failWaiter w dead i).st s).phase) = true := by
  by_cases hs : s = i
  · rw [hs] at h ⊢
    unfold failWaiter
    split
    · exact h
    · cases hph : (w.st i).phase with
      | parked d b k =>
        cases b with
        | false =>
          have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using h
          simp [hph]
          split
          · cases hk : k.rest with
            | nil =>
              simp [setActor_self, proceed, hk, contRest]
              exact nobulk_empty
            | cons _ _ => simpa [setActor_self, proceed, hk, contRest] using hrest
          · exact h
        | true => simpa [hph, contRest] using h
      | awaitReply _ _ => simpa [hph, contRest] using h
      | idle => simpa [hph, contRest] using h
      | run k => simpa [hph, contRest] using h
      | awaitEffect k => simpa [hph, contRest] using h
      | awaitPeer k => simpa [hph, contRest] using h
      | crashed => simpa [hph, contRest] using h
  · rw [failWaiter_other w dead i s hs]
    exact h

theorem nobulk_failFold (w : World) (dead s : InstId) (ids : List InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase) = true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (nobulk_failWaiter w dead i s h)

theorem nobulk_killOne (w : World) (D : Description) (id s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((killOne w D id).st s).phase) = true := by
  by_cases hs : s = id
  · rw [hs, (killOne_self w D id).2.1]
    simp [contRest]
    exact nobulk_empty
  · let w1 := readCells D w id
    have hst1 : w1.st s = w.st s := cellsSt D w id s
    have h1 : noBulkSend (contRest (w1.st s).phase) = true := by simpa [hst1] using h
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
    have hph2 : (w2.st s).phase = (w1.st s).phase := by simpa [w2] using h2.1
    have h2n : noBulkSend (contRest (w2.st s).phase) = true := by simpa [hph2] using h1
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
    have hph3 : (w3.st s).phase = (w2.st s).phase := by simpa [w3] using h3.1
    have h3n : noBulkSend (contRest (w3.st s).phase) = true := by simpa [hph3] using h2n
    let w4 := failWaiters w3 id
    have h4n : noBulkSend (contRest (w4.st s).phase) = true := by
      simpa [w4, failWaiters] using nobulk_failFold w3 id s w3.roster h3n
    let w5 := forgetSender w4 id
    have hph5 : (w5.st s).phase = (w4.st s).phase := by simpa [w5] using (forget_stable w4 id s).1
    have h5n : noBulkSend (contRest (w5.st s).phase) = true := by simpa [hph5] using h4n
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hs]
    exact h5n

theorem nobulk_killFold (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase) =
      true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (nobulk_killOne w D j s h)
    · simp only [hcond]
      exact ih w h

theorem nobulk_killSubtree (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((killSubtree w D sub key).st s).phase) = true := by
  simpa [killSubtree, killMembers] using nobulk_killFold w D sub key w.roster s h

/-- Clearing a reply obligation changes `replyTo` only, so every stored list stays. -/
theorem phase_detach (D : Description) (name : String) (caller : InstId) (cid : Nat) (a : Actor)
    (h : phaseScope D name a.phase = true) :
    phaseScope D name (detachReply (detachBox a caller) caller cid).phase = true := by
  unfold detachReply
  split
  · cases hph : a.phase with
    | idle => simp [detachBox, clearReplyPhase, hph, phaseScope]
    | crashed => simp [detachBox, clearReplyPhase, hph, phaseScope]
    | run k =>
      simp [detachBox, clearReplyPhase, hph, phaseScope, contArms, clearReplyCont, Bool.and_eq_true] at h ⊢
      split <;> exact h
    | parked d c k =>
      simp [detachBox, clearReplyPhase, hph, phaseScope, contArms, clearReplyCont, Bool.and_eq_true] at h ⊢
      split <;> exact h
    | awaitReply d k =>
      simp [detachBox, clearReplyPhase, hph, phaseScope, contArms, clearReplyCont, Bool.and_eq_true] at h ⊢
      split <;> exact h
    | awaitEffect k =>
      simp [detachBox, clearReplyPhase, hph, phaseScope, contArms, clearReplyCont, Bool.and_eq_true] at h ⊢
      split <;> exact h
    | awaitPeer k =>
      simp [detachBox, clearReplyPhase, hph, phaseScope, contArms, clearReplyCont, Bool.and_eq_true] at h ⊢
      split <;> exact h
  · simpa [detachBox] using h

theorem bulk_timeout (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : callTimeout w id = some w') : BulkFree I w' := by
  apply bulk_or I w _ hB
  intro i
  unfold callTimeout at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hgo : ((w.st id).life != .alive) = false := by
      cases hb : (w.st id).life != .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp only [hgo] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      cases h
      by_cases hi : i = id
      · rw [hi]
        simpa [setActor_self, finishCall, selectCall] using
          Or.inl (phase_proceed I.desc (tname id) _ (selectCall k .timedOut)
            (arms_timedOut I.desc (tname id) k (by simpa [phaseScope, hph] using hB id)))
      · by_cases hd : i = dst
        · rw [hd]
          rw [setActor_other _ id dst _ (fun h => hi (h ▸ hd))]
          rw [setActor_self]
          exact Or.inl (phase_detach I.desc (tname dst) id (w.st id).waitId (w.st dst) (hB dst))
        · rw [setActor_other _ id i _ hi, setActor_other _ dst i _ hd]
          exact Or.inr rfl
    | parked dst b k =>
      cases b with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        cases h
        by_cases hi : i = id
        · rw [hi]
          simpa [setActor_self, finishCall, selectCall] using
            Or.inl (phase_proceed I.desc (tname id) _ (selectCall k .notAdmitted)
              (arms_notAdmitted I.desc (tname id) k (by simpa [phaseScope, hph] using hB id)))
        · rw [setActor_other _ id i _ hi]
          exact Or.inr (refundCall_fields w id dst i).1
    | awaitPeer k =>
      simp only [hph] at h
      cases h
      by_cases hi : i = id
      · rw [hi]
        simpa [setActor_self] using Or.inl (phase_proceed I.desc (tname id) (w.st id)
          { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }
          (arms_rest I.desc (tname id) k k.onTimeout (by simpa [phaseScope, hph] using hB id)
            (by
              have har : contArms I.desc (tname id) k = true := by simpa [phaseScope, hph] using hB id
              simp only [contArms, Bool.and_eq_true] at har
              exact har.2)))
      · simp [setActor, hi]
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem bulk_apply (I : Impl) (hL : LocalOk I) (a : Action) (w w' : World) (hB : BulkFree I w)
    (h : apply I a w = some w') : BulkFree I w' := by
  have ⟨_, hstep⟩ := apply_step I a w w' h
  cases a with
  | recvBulk id => simpa [stepWorld] using bulk_recv I hL w w' id hB hstep
  | recvPrio id => simpa [stepWorld] using bulk_prio I hL w w' id hB hstep
  | exec id => simpa [stepWorld] using bulk_head I w w' id hB hstep
  | finish id => simpa [stepWorld] using bulk_finish I w w' id hB hstep
  | spawn template => simpa [stepWorld] using bulk_spawn I w w' template hB hstep
  | ingress dst label => simpa [stepWorld] using bulk_ingress I w w' dst label hB hstep
  | callTimeout id => simpa [stepWorld] using bulk_timeout I w w' id hB hstep
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hB

/-- Parent facts of every reachable world. `OpenSlots` is the reachable
invariant's, and a child birth uses `PeerRole` and `CoreRole`. -/
theorem birth_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : BirthInv I.desc w := by
  induction hR with
  | init => exact birth_init I hG N
  | step w w' a prev ha ih =>
    exact birth_apply I hG a w w' ih (inv_reachable I N w hL prev).2.2.1
      (peer_role_reachable I hG N w prev) (core_reachable I hG N w prev) ha

theorem inv2_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : Inv2 I w := by
  induction hR with
  | init => exact inv2_init I hL hG N
  | step w w' a hw happly ih =>
    rcases ih with ⟨hI, hO, hT, hB⟩
    exact ⟨step_inv I hL w w' ⟨a, happly⟩ hI,
      occ_apply I hL hG a w w' hO hI.1 hI.2.1 hI.2.2.1 hT hB hI.forest
        (birth_reachable I hL hG N w hw) hI.seal happly,
      ty_step I hL hG N w w' a hw happly hT,     bulk_apply I hL a w w' hB happly⟩

theorem residual_of_edge (D : Description) (e : Edge) (st : String) (he : e ∈ D.edges)
    (hd : discharged D e = false) (hs : st ∈ targetStates D e) :
    (({ template := e.src, state := e.srcState } : Node),
      ({ template := e.dst, state := st } : Node)) ∈ residualEdges D := by
  unfold residualEdges
  let step : List (Node × Node) → Edge → List (Node × Node) := fun acc e =>
    if discharged D e = true then acc
    else acc ++ (targetStates D e).map fun st =>
      (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := st } : Node))
  let pair : Node × Node :=
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := st } : Node))
  have hkeep : ∀ (es : List Edge) (acc : List (Node × Node)), pair ∈ acc → pair ∈ List.foldl step acc es := by
    intro es
    induction es with
    | nil =>
      intro acc hp
      exact hp
    | cons e0 es ih =>
      intro acc hp
      simp only [List.foldl_cons]
      by_cases hdis0 : discharged D e0 = true
      · simp [step, hdis0]
        exact ih _ hp
      · simp [step, hdis0]
        exact ih _ (List.mem_append_left _ hp)
  suffices ∀ (es : List Edge) (acc : List (Node × Node)), e ∈ es → pair ∈ List.foldl step acc es by
    simpa [residualEdges, step, pair] using this D.edges [] he
  intro es acc he
  induction es generalizing acc with
  | nil => cases he
  | cons e0 es ih =>
    simp only [List.foldl_cons]
    cases he with
    | head =>
      simp [step, hd]
      exact hkeep es _ (List.mem_append_right _ (List.mem_map.mpr ⟨st, hs, rfl⟩))
    | tail _ ht =>
      exact ih _ ht

/-- A Lemma-1 mailbox never carries a parked entry. Admission still has room
whenever a live sender holds the token for one more message, so `enqueueOrPark`
takes the box branch. `OccInv` does not store this: a full box of an earlier
generation is a different fact from a parked sender. -/
def l1Clear (D : Description) (w : World) : Prop :=
  ∀ id, l1 D (tname id) = true → (w.st id).parked = []

theorem l1Clear_sub (D : Description) (w w' : World) (h : l1Clear D w)
    (hsub : ∀ id p, p ∈ (w'.st id).parked → p ∈ (w.st id).parked) : l1Clear D w' := by
  intro id hl1
  cases hpark : (w'.st id).parked with
  | nil => rfl
  | cons p _ =>
    have hmem : p ∈ (w.st id).parked := hsub id p (by simp [hpark])
    simp [h id hl1] at hmem

theorem l1Clear_init (I : Impl) (N : Nat) : l1Clear I.desc (initWorld I N) := by
  intro id _
  exact (init_box I N id).2

theorem queued_succ_le (budget queued : Nat) (tokens : Int)
    (hsum : tokens + (queued : Int) = (budget : Int)) (htok : (1 : Int) ≤ tokens) :
    queued + 1 ≤ budget := by
  omega

theorem tokenHold_head_send (D : Description) (template dst : String) (a : Actor) (k : Cont)
    (label : String) (hint : Nat) (es : List Eff) (hph : a.phase = .run k)
    (hk : k.rest = .send dst label hint :: es) : 1 ≤ tokenHold D template dst a := by
  have hb : (dst == dst) = true := by simp
  simp [tokenHold, hph, hk, pathReserve, effReserve, hb]

/-- One more send from the live generation still fits in the key's budget.
The parked message is not this fact: the token is spent only when the send runs. -/
theorem peer_send_gap (I : Impl) (w : World) (hO : OccInv I w) (name : String) (key : Nat)
    (sender : InstId) (dst : String) (hlive : findLive w name key = some sender)
    (hlife : (w.st sender).life = .alive) (hhold : 1 ≤ tokenHold I.desc name dst (w.st sender)) :
    queuedFromKey w name key dst + 1 ≤ budget I.desc name dst := by
  have htn := (findLive_spec w name key sender hlive).1
  have hS := hO.slack sender dst hlife
  have hcast : ((1 : Nat) : Int) ≤ (tokenHold I.desc name dst (w.st sender) : Int) :=
    Int.ofNat_le.mpr hhold
  rw [htn] at hS
  exact queued_succ_le _ _ _ (hO.balance.1.1 name key sender dst hlive) (Int.le_trans hcast hS)

theorem l1_parked_empty (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id : InstId) (hl1 : l1 I.desc (tname id) = true) :
    (w.st id).parked = [] :=
  l1Clear_reachable I hL hG N w hR id hl1

theorem park_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (id dst : InstId) (k : Cont)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .parked dst false k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_park I hL hG N w hR id dst false k hph
  obtain ⟨p, hp, _, _⟩ := (inv_reachable I N w hL hR).2.1.bwdSend id dst k hph
  have hdis : discharged I.desc e = false := by
    by_cases hd : discharged I.desc e = true
    · have hl1 : l1 I.desc (tname dst) = true := by
        have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
        simp [discharged, hkind, heff, hdstn, hne] at hd
        exact hd.2
      have hempty : (w.st dst).parked = [] := l1_parked_empty I hL hG N w hR dst hl1
      simp [hempty] at hp
    · cases hbit : discharged I.desc e
      · rfl
      · exact absurd hbit hd
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

theorem park_height (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .parked dst false k) (hlive : (w.st dst).life = .alive) :
    ∃ hs : List (Node × Nat),
      heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
        heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨hs, hok⟩ := hG.ranked
  exact ⟨hs, park_below I hL hG N w hR hO id dst k hs hok hph hlive⟩

theorem reply_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hs : List (Node × Nat))
    (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .awaitReply dst k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_reply I hL hG N w hR id dst k hph
  have hdis : discharged I.desc e = false := by
    have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
    have hcall : (EffectKind.call == EffectKind.send) = false := by decide
    simp [discharged, hkind, heff, hne, hcall]
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

/-- A parked call waits on a live callee of strictly smaller height. -/
theorem call_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hs : List (Node × Nat))
    (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .parked dst true k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_park I hL hG N w hR id dst true k hph
  have heff' : e.effect = EffectKind.call := by simpa using heff
  have hdis : discharged I.desc e = false := by
    have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
    have hcall : (EffectKind.call == EffectKind.send) = false := by decide
    simp [discharged, hkind, heff', hne, hcall]
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

theorem reply_height (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .awaitReply dst k) (hlive : (w.st dst).life = .alive) :
    ∃ hs : List (Node × Nat),
      heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
        heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨hs, hok⟩ := hG.ranked
  exact ⟨hs, reply_below I hL hG N w hR id dst k hs hok hph hlive⟩

/-- A caller blocked on `callee` for this continuation. -/
def CallWait (ph : Phase) (callee : InstId) (k : Cont) : Prop :=
  ph = .parked callee true k ∨ ph = .awaitReply callee k

theorem proceed_not_callwait (a : Actor) (k : Cont) (callee : InstId) (k' : Cont) :
    ¬ CallWait (proceed a k).phase callee k' := by
  cases hk : k.rest <;> simp [proceed, hk, CallWait]

theorem template_subtree_of (D : Description) (name : String) (t : Template)
    (ht : templateOf D name = some t) : templateSubtree D name = t.subtree := by
  simp [templateSubtree, ht]

/-- Reachable mail stays inside the sender's subtree, and parked senders match the message. -/
theorem mail_pack_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : MailHere I.desc w ∧ ParkAlign w := by
  induction hR with
  | init => exact ⟨mail_here_init I N, align_init I N⟩
  | step w w' a hw h ih =>
    exact mail_pack_step I hG a w w' ih.1 ih.2
      (fun id => scope_rest I.desc (tname id) (w.st id).phase ((inv2_reachable I hL hG N w hw).2.2.2 id)) h

theorem mail_here_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : MailHere I.desc w :=
  (mail_pack_reachable I hL hG N w hR).1

end Deadlock
