import Deadlock.Occ

set_option autoImplicit false

namespace Deadlock

/-- A lone terminable's continuation does not send, call, or self-schedule.
A subtree member's continuation stays inside that subtree. -/
def BulkFree (I : Impl) (w : World) : Prop :=
  ∀ id, bulkScopeOf I.desc (tname id) (contRest (w.st id).phase) = true

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

theorem bulk_init (I : Impl) (N : Nat) : BulkFree I (initWorld I N) := by
  intro id
  have hph := init_phase I N id
  simpa [contRest, hph] using scope_empty I.desc (tname id)

theorem inv2_init (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) :
    Inv2 I (initWorld I N) :=
  ⟨inv_init I N hL, occ_init I hG N, ty_init I hG N, bulk_init I N⟩

theorem occ_apply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (a : Action) (w w' : World)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w)
    (hT : TyOk I.desc w) (hB : BulkFree I w)
    (h : apply I a w = some w') : OccInv I w' := by
  cases a with
  | recvBulk id =>
    simpa [apply] using occ_bulk I hL hG w id w' hO hS hM h
  | recvPrio id =>
    simpa [apply] using occ_prio I hL hG w id w' hO h
  | exec id =>
    simpa [apply] using occ_head I hL hG w w' id hO hT hS hM hSlots h
      (fun k hph => by simpa [contRest, hph] using hB id)
  | finish id =>
    simpa [apply] using occ_finish I w w' id hO hS h
  | spawn template =>
    simpa [apply] using occ_spawn I w w' template hO h
  | ingress dst label =>
    simpa [apply] using occ_ingress I w w' dst label hO h
  | callTimeout id =>
    simpa [apply] using occ_timeout I w w' id hO hS.cont h
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

/-- Parking, waiting, or proceeding all keep the same rest, so the scope carries. -/
theorem enqueue_sender_cont (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) :
    contRest ((enqueueOrPark w D sender dst msg isCall k).st sender).phase = k.rest := by
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
      by_cases hdead : ((w.st dst).life == .dead) = true
      · have hEq : (w.st dst).life = .dead := by simpa [beq_iff_eq] using hdead
        simp [hEq, setActor_self, contRest]
      · have hbit : ((w.st dst).life == .dead) = false := by
          cases hb : (w.st dst).life == .dead with
          | true => exact absurd hb hdead
          | false => rfl
        have hEq : (w.st dst).life ≠ .dead := by simpa [beq_iff_eq] using hbit
        simp [hEq, setActor_self, finishCall]
        cases hk : k.rest <;> simp [proceed, hk, contRest]

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
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · next heq =>
      split at h
      · cases h
      · cases h
        simp [contRest]
        exact scope_empty I.desc (tname id)
    · next tr heq =>
      split at h
      · cases h
      · cases h
        have hmem := findTr_mem I (tname id) a.typestate m.label tr heq
        by_cases hempty : tr.program.isEmpty = true
        · simp [hempty, contRest]
          exact scope_empty I.desc (tname id)
        · simp [hempty, contRest]
          cases ht : templateOf I.desc (tname id) with
          | none => simp [bulkScopeOf, ht]
          | some t =>
            cases hterm : t.terminable
            · simp [bulkScopeOf, ht, hterm]
            · simpa [hmem.2.1] using
                terminable_program I hL tr hmem.1 t (by simpa [hmem.2.1] using ht) hterm

theorem bulk_or (I : Impl) (w w' : World) (hB : BulkFree I w)
    (h : ∀ id, bulkScopeOf I.desc (tname id) (contRest (w'.st id).phase) = true ∨
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
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    apply bulk_or I w _ hB
    intro i
    by_cases hi : i = id
    · rw [hi]
      have hrest : bulkScopeOf I.desc (tname id) k.rest = true := by
        simpa [contRest, hph] using hB id
      cases hk : k.rest with
      | nil =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (scope_empty I.desc (tname id))
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    apply bulk_or I w _ hB
    intro i
    by_cases hi : i = id
    · rw [hi]
      have hrest : bulkScopeOf I.desc (tname id) k.rest = true := by
        simpa [contRest, hph] using hB id
      cases hk : k.rest with
      | nil =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (scope_empty I.desc (tname id))
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

/-- An ingress delivery leaves every phase where it was, so a bulk-free world stays bulk-free. -/
theorem bulk_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String) (hB : BulkFree I w)
    (h : receiveIngress I w dst label = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro id
  exact Or.inr (ingress_phase I w w' dst label id h).1

theorem bulk_spawn (I : Impl) (w w' : World) (template : String) (hB : BulkFree I w)
    (h : spawn I w template = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro i
  unfold spawn at h
  split at h
  · cases h
  · next t _ =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      by_cases hi : i = InstId.peer template (w.nextIx template)
      · simpa [readCells_st, setActor, hi, withTokens, contRest, tname] using
          Or.inl (scope_empty I.desc template)
      · simpa [readCells_st, setActor, hi] using Or.inr rfl
    · simp [hif] at h

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
          exact Or.inl (resume_scope I.desc (tname p.sender) (w.st p.sender) false id (hB p.sender))
        · simp [setActor, hi]
      simpa [releaseParked] using ih _ hB'

theorem try_wake_phase (D : Description) (w : World) (dstId : InstId) (label : String) (writer i : InstId) :
    ((tryWake D w dstId label writer).st i).phase = (w.st i).phase := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide (prioLoad (w.st dstId).prio < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_phase (ids : List InstId) (D : Description) (w : World) (dst label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).phase = (w.st i).phase := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, try_wake_phase]

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

theorem scope_releaseWorld (D : Description) (w : World) (id : InstId) (a : Actor) (s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((releaseWorld D w id a).st s).phase) = true := by
  let base := refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hworld : releaseWorld D w id a = releaseParked (setActor base id dead) id a.parked := by
    simp [releaseWorld, base, dead]
  rw [hworld]
  by_cases hs : s = id
  · rw [hs]
    have hidle : ((setActor base id dead).st id).phase = .idle := by simp [setActor, dead]
    rw [release_victim_phase (setActor base id dead) id a.parked, hidle]
    simp [contRest]
    exact scope_empty D (tname id)
  · have hph : ((setActor base id dead).st s).phase = (w.st s).phase := by
      simp [setActor, hs, base, phase_refundP, phase_refund, readCells_st]
    exact scope_releaseParked D (setActor base id dead) id s a.parked (by simpa [hph] using h)

theorem scope_abortActor (D : Description) (w : World) (id : InstId) (a : Actor) (s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((abortActor D w id a).st s).phase) = true := by
  have hrel := scope_releaseWorld D w id a s h
  let released := releaseWorld D w id a
  have hfail := scope_failFold D released id s released.roster hrel
  rw [abortActor]
  have hph := (admitDead_phase (failWaiters released id) id s).1
  rw [hph]
  simpa [released, failWaiters] using hfail

theorem scope_abortDesc (fuel : Nat) (D : Description) (w : World) (parent s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((abortDesc fuel D w parent).st s).phase) = true := by
  induction fuel generalizing w parent with
  | zero => simpa [abortDesc] using h
  | succ fuel ih =>
    simp only [abortDesc]
    suffices ∀ (ids : List InstId) (w0 : World),
        bulkScopeOf D (tname s) (contRest (w0.st s).phase) = true →
        bulkScopeOf D (tname s) (contRest ((ids.foldl (fun w child =>
          if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
            let w := abortDesc fuel D w child
            abortActor D w child (w.st child)
          else w) w0).st s).phase) = true by
      exact this w.roster w h
    intro ids
    induction ids with
    | nil =>
      intro w0 h0
      simpa using h0
    | cons c ids ihf =>
      intro w0 h0
      simp only [List.foldl_cons]
      by_cases hgo : (isChild D parent c && (w0.st c).life == .alive && childTerminable D c) = true
      · rw [if_pos hgo]
        have hdesc := ih w0 c h0
        exact ihf _ (scope_abortActor D (abortDesc fuel D w0 c) c ((abortDesc fuel D w0 c).st c) s hdesc)
      · rw [if_neg hgo]
        exact ihf w0 h0

theorem tombstone_phase (D : Description) (w : World) (child s : InstId) :
    ((enqueueTombstone D w child).st s).phase = (w.st s).phase := by
  cases hsup : supervisorOf D child with
  | none => simp [enqueueTombstone, hsup]
  | some parent =>
    simp [enqueueTombstone, hsup]
    by_cases hlive : (w.st parent).life = .alive
    · simp [hlive, setActor]
      by_cases hs : s = parent <;> simp [hs]
    · simp [hlive]

theorem scope_terminateStage (D : Description) (w : World) (id s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((terminateStage D w id (w.st id)).st s).phase) = true := by
  have hdesc := scope_abortDesc w.roster.length D w id s h
  have hab := scope_abortActor D (abortDesc w.roster.length D w id) id
    ((abortDesc w.roster.length D w id).st id) s hdesc
  have hph := tombstone_phase D
    (abortActor D (abortDesc w.roster.length D w id) id ((abortDesc w.roster.length D w id).st id)) id s
  simpa [terminateStage, hph] using hab

theorem scope_killSubtree (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : bulkScopeOf D (tname s) (contRest (w.st s).phase) = true) :
    bulkScopeOf D (tname s) (contRest ((killSubtree w D sub key).st s).phase) = true := by
  simpa [killSubtree, killMembers] using scope_killFold D w sub key w.roster s h

theorem bulk_exec (I : Impl) (w : World) (id : InstId) (k : Cont) (hB : BulkFree I w)
    (hph : (w.st id).phase = .run k) : BulkFree I (execRun I w id (w.st id) k) := by
  apply bulk_or I w _ hB
  intro i
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      by_cases hi : i = id
      · rw [hi]
        simp [execRun, hrest, setActor, contRest, scope_empty]
      · simp [execRun, hrest, setActor, hi]
    | cons e es =>
      cases e with
      | send dst label hint =>
        by_cases hi : i = id
        · have htail := scope_tail I.desc (tname id) (.send dst label hint) es
            (by simpa [contRest, hph, hrest] using hB id)
          rw [hi]
          simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none =>
            simp [hr, setActor_self]
            exact Or.inl (scope_proceed I.desc (tname id) (w.st id) ⟨es, toState, replyTo⟩ htail)
          | some dstId =>
            simp [hr]
            exact Or.inl (by simpa [enqueue_sender_cont, afterHead, List.tail_cons] using htail)
        · simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none => simp [hr, setActor, hi]
          | some dstId =>
            simp [hr]
            exact Or.inr (enqueue_phase_other w I.desc id dstId { label := label, sender := id, callFrom := none } false
              ⟨es, toState, replyTo⟩ i hi)
      | call dst label hint =>
        by_cases hi : i = id
        · have htail := scope_tail I.desc (tname id) (.call dst label hint) es
            (by simpa [contRest, hph, hrest] using hB id)
          rw [hi]
          simp [execRun, hrest]
          cases hr : resolveId I.desc id dst with
          | none =>
            simp [hr, setActor_self, noteStale_st]
            exact Or.inl (scope_proceed I.desc (tname id) (w.st id) ⟨es, toState, replyTo⟩ htail)
          | some dstId =>
            simp [hr]
            by_cases hlive : (w.st dstId).life = .alive
            · simp [hlive]
              exact Or.inl (by simpa [enqueue_sender_cont, afterHead, List.tail_cons] using htail)
            · simp [hlive]
              exact Or.inl (by simpa [enqueue_sender_cont, afterHead, List.tail_cons, noteStale_st] using htail)
        · simp [execRun, hrest]
          cases hr : resolveId I.desc id dst with
          | none => simp [hr, setActor, hi, noteStale_st]
          | some dstId =>
            simp [hr]
            by_cases hlive : (w.st dstId).life = .alive
            · simp [hlive]
              exact Or.inr (enqueue_phase_other w I.desc id dstId { label := label, sender := id, callFrom := some id } true
                ⟨es, toState, replyTo⟩ i hi)
            · simp [hlive]
              have hph' := enqueue_phase_other (noteStale w id dst) I.desc id dstId
                { label := label, sender := id, callFrom := some id } true
                (afterHead { rest := .call dst label hint :: es, toState := toState, replyTo := replyTo }) i hi
              rw [noteStale_st] at hph'
              exact Or.inr hph'
      | trySend dst label hint =>
        by_cases hi : i = id
        · have htail := scope_tail I.desc (tname id) (.trySend dst label hint) es
            (by simpa [contRest, hph, hrest] using hB id)
          rw [hi]
          simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none =>
            simp [hr, setActor_self]
            exact Or.inl (scope_proceed I.desc (tname id) (w.st id) ⟨es, toState, replyTo⟩ htail)
          | some dstId =>
            simp [hr]
            split
            · exact Or.inl (by simpa [enqueue_sender_cont, afterHead, List.tail_cons] using htail)
            · simp [setActor_self]
              exact Or.inl (scope_proceed I.desc (tname id) (w.st id) ⟨es, toState, replyTo⟩ htail)
        · simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none => simp [hr, setActor, hi]
          | some dstId =>
            simp [hr]
            split
            · exact Or.inr (enqueue_phase_other w I.desc id dstId
                { label := label, sender := id, callFrom := none, reliable := false } false
                ⟨es, toState, replyTo⟩ i hi)
            · simp [setActor, hi]
      | reply =>
        simp [execRun, hrest]
        unfold performReply
        cases hto : replyTo with
        | none =>
          simp [hto, setActor]
          by_cases hi : i = id
          · rw [hi]
            simp [setActor]
            exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, none⟩
              (by simpa [contRest, hph, hrest] using hB id))
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
                  exact Or.inl (after_scope I.desc (tname id)
                    (if id = caller then finishCall (w.st caller) ck .reply else w.st id)
                    ⟨.reply :: es, toState, some caller⟩
                    (by simpa [contRest, hph, hrest] using hB id))
                · by_cases hc : i = caller
                  · by_cases hself : caller = id
                    · exact absurd (hc.trans hself) hi
                    · rw [hc]
                      simp [setActor, hi, hself, finishCall]
                      have hold : bulkScopeOf I.desc (tname caller) ck.rest = true := by
                        simpa [contRest, hcall] using hB caller
                      cases hk : ck.rest with
                      | nil =>
                        simp [proceed, hk, contRest]
                        exact Or.inl (scope_empty I.desc (tname caller))
                      | cons _ _ =>
                        simp [proceed, hk, contRest]
                        exact Or.inl (by simpa [hk] using hold)
                  · simp [setActor, hi, hc]
              · simp [hd, howe, setActor]
                by_cases hi : i = id
                · rw [hi]
                  simp [setActor]
                  exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                    (by simpa [contRest, hph, hrest] using hB id))
                · simp [hi]
            · simp [hd, setActor]
              by_cases hi : i = id
              · rw [hi]
                simp [setActor]
                exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                  (by simpa [contRest, hph, hrest] using hB id))
              · simp [hi]
          | idle =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
          | run ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
          | parked dst b ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
          | awaitEffect ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
          | awaitPeer ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
          | crashed =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi]
              simp [setActor]
              exact Or.inl (after_scope I.desc (tname id) (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id))
            · simp [hi]
      | selfSchedule label =>
        simp only [execRun, hrest]
        split
        · by_cases hi : i = id
          · rw [hi]
            have htail := scope_tail I.desc (tname id) (.selfSchedule label) es
              (by simpa [contRest, hph, hrest] using hB id)
            cases hes : es with
            | nil => simp [setActor, proceed, afterHead, hes, contRest, scope_empty]
            | cons _ _ =>
              simp [setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setActor, hi]
        · split
          · by_cases hi : i = id
            · rw [hi]
              have htail := scope_tail I.desc (tname id) (.selfSchedule label) es
                (by simpa [contRest, hph, hrest] using hB id)
              cases hes : es with
              | nil => simp [setActor, proceed, afterHead, hes, contRest, scope_empty]
              | cons _ _ =>
                simp [setActor, proceed, afterHead, hes, contRest]
                exact Or.inl (by simpa [hes] using htail)
            · simp [setActor, hi]
          · by_cases hi : i = id
            · rw [hi]
              simp [setActor, contRest, scope_empty]
            · simp [setActor, hi]
      | cell dst label value =>
        simp only [execRun, hrest]
        split
        · by_cases hi : i = id
          · rw [hi]
            have htail := scope_tail I.desc (tname id) (.cell dst label value) es
              (by simpa [contRest, hph, hrest] using hB id)
            cases hes : es with
            | nil => simp [setCell, setActor, proceed, afterHead, hes, contRest, scope_empty]
            | cons _ _ =>
              simp [setCell, setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setCell, setActor, hi]
        · simp only [wakeReaders]
          rw [wakes_phase (readersOf _ dst) I.desc _ dst label id i]
          by_cases hi : i = id
          · rw [hi]
            have htail := scope_tail I.desc (tname id) (.cell dst label value) es
              (by simpa [contRest, hph, hrest] using hB id)
            cases hes : es with
            | nil => simp [setCell, setActor, proceed, afterHead, hes, contRest, scope_empty]
            | cons _ _ =>
              simp [setCell, setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setCell, setActor, hi]
      | internal =>
        by_cases hi : i = id
        · rw [hi]
          have htail := scope_tail I.desc (tname id) (.internal) es
            (by simpa [contRest, hph, hrest] using hB id)
          simp [execRun, hrest, setActor, contRest]
          exact Or.inl htail
        · simp [execRun, hrest, setActor, hi]
      | peer =>
        by_cases hi : i = id
        · rw [hi]
          have htail := scope_tail I.desc (tname id) (.peer) es
            (by simpa [contRest, hph, hrest] using hB id)
          simp [execRun, hrest, setActor, contRest]
          exact Or.inl htail
        · simp [execRun, hrest, setActor, hi]
      | terminate =>
        simp [execRun, hrest]
        cases htpl : templateOf I.desc (tname id) with
        | none => simp [htpl]
        | some t =>
          simp only [htpl]
          split
          · split
            · let wR := readCells I.desc w id
              let wM := refundMsgs wR (tname id) (w.st id).box
              let wP := refundParked wM (tname id) (w.st id).parked
              let dead : Actor :=
                { wP.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
              have hpre : BulkFree I (setActor wP id dead) := by
                apply bulk_or I w _ hB
                intro j
                by_cases hj : j = id
                · rw [hj]
                  simp [setActor, dead, contRest, scope_empty]
                · have hphj : (wP.st j).phase = (w.st j).phase := by
                    simp [wP, wM, wR, phase_refundP, phase_refund, readCells_st]
                  simp [setActor, hj, hphj]
              exact Or.inl ((release_bulk I (setActor wP id dead) id (w.st id).parked hpre) i)
            · exact Or.inl (scope_terminateStage I.desc w id i (hB i))
          · exact Or.inr rfl

theorem bulk_head (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : execHead I w id = some w') : BulkFree I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact bulk_exec I w id k hB hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem place_bulk (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor) (dst : String) (sender : InstId)
    (hn : bulkScopeOf I.desc (tname id) (contRest a1.phase) = true)
    (hst : ∀ i, w1.st i = w.st i) (hB : BulkFree I w) :
    BulkFree I (creditSender (setActor w1 id a1) dst sender) := by
  apply bulk_or I w _ hB
  intro i
  by_cases hi : i = id
  · rw [hi]
    simp [phase_credit, setActor]
    exact Or.inl hn
  · simp [phase_credit, setActor, hi, hst i]

theorem place_actor (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor)
    (hn : bulkScopeOf I.desc (tname id) (contRest a1.phase) = true)
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
    exact Or.inl (resume_scope I.desc (tname sender) (w.st sender) b dst (hB sender))
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
            (deliver_scope I hL w id _ p.msg w1 a1 hdel)
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
            (deliver_scope I hL w id _ m w1 a1 hdel)
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
            (by simpa [hph] using deliver_scope I hL w id _ m w1 a1 hdel)
            (fun i => deliver_st I w id _ m w1 a1 i hdel) hB
          simpa [admitted] using resume_bulk I _ p.sender p.isCall id hplace

theorem bulk_prio (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : receivePrio I w id = some w') : BulkFree I w' := by
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      exact place_actor I w w1 id a1
        (deliver_scope I hL w id _ m w1 a1 hdel)
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
        have hold : bulkScopeOf I.desc (tname id) k.rest = true := by
          simpa [contRest, hph] using hB id
        simp [setActor_self, finishCall]
        cases hk : k.rest with
        | nil =>
          simp [proceed, hk, contRest]
          exact Or.inl (scope_empty I.desc (tname id))
        | cons _ _ =>
          simp [proceed, hk, contRest]
          exact Or.inl (by simpa [hk] using hold)
      · by_cases hd : i = dst
        · rw [hd]
          rw [setActor_other _ id dst _ (fun h => hi (h ▸ hd))]
          rw [setActor_self]
          suffices hrest : contRest (detachReply (detachBox (w.st dst) id) id (w.st id).waitId).phase =
              contRest (w.st dst).phase by
            exact Or.inl (by simpa [hrest] using hB dst)
          unfold detachReply
          split <;> simp [detachBox, clearReplyPhase_rest]
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
          have hold : bulkScopeOf I.desc (tname id) k.rest = true := by
            simpa [contRest, hph] using hB id
          simp [setActor_self, finishCall]
          cases hk : k.rest with
          | nil =>
            simp [proceed, hk, contRest]
            exact Or.inl (scope_empty I.desc (tname id))
          | cons _ _ =>
            simp [proceed, hk, contRest]
            exact Or.inl (by simpa [hk] using hold)
        · rw [setActor_other _ id i _ hi]
          exact Or.inr ((refundCall_fields w id dst i).1)
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem bulk_apply (I : Impl) (hL : LocalOk I) (a : Action) (w w' : World) (hB : BulkFree I w)
    (h : apply I a w = some w') : BulkFree I w' := by
  cases a with
  | recvBulk id => simpa [apply] using bulk_recv I hL w w' id hB h
  | recvPrio id => simpa [apply] using bulk_prio I hL w w' id hB h
  | exec id => simpa [apply] using bulk_head I w w' id hB h
  | finish id => simpa [apply] using bulk_finish I w w' id hB h
  | spawn template => simpa [apply] using bulk_spawn I w w' template hB h
  | ingress dst label => simpa [apply] using bulk_ingress I w w' dst label hB h
  | callTimeout id => simpa [apply] using bulk_timeout I w w' id hB h
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hB

theorem inv2_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : Inv2 I w := by
  induction hR with
  | init => exact inv2_init I hL hG N
  | step w w' a hw happly ih =>
    rcases ih with ⟨hI, hO, hT, hB⟩
    exact ⟨step_inv I hL w w' ⟨a, happly⟩ hI, occ_apply I hL hG a w w' hO hI.1 hI.2.1 hI.2.2 hT hB happly,
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
      simp [hO.clear dst hl1] at hp
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

/-- A nonempty subtree member is terminable. `subtreeFails` is what the checker records. -/
theorem subtree_member_terminable (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hne : t.subtree ≠ "") : t.terminable = true := by
  have hmap := hG.subtrees
  simp [subtreeFails] at hmap
  have hf := hmap t (template_mem D name t ht)
  simp [hne] at hf
  cases hmul : t.multiplicity with
  | perPeer =>
    rw [hmul] at hf
    have hper : (Multiplicity.perPeer != Multiplicity.perPeer) = false := by decide
    rw [hper] at hf
    cases htm : t.terminable with
    | true => rfl
    | false => simp [htm] at hf
  | one =>
    rw [hmul] at hf
    have hper : (Multiplicity.one != Multiplicity.perPeer) = true := by decide
    rw [hper] at hf
    simp at hf

theorem same_src_terminable (D : Description) (hG : GraphOk D) (a b : String) (t : Template)
    (hsame : sameSubtree D a b = true) (ht : templateOf D a = some t) : t.terminable = true := by
  have hsub : templateSubtree D a ≠ "" := by
    simp [sameSubtree, Bool.and_eq_true] at hsame
    intro hempty
    simp [hempty] at hsame
  rw [template_subtree_of D a t ht] at hsub
  exact subtree_member_terminable D hG a t ht hsub

/-- Reachable mail stays inside the sender's subtree, and parked senders match the message. -/
theorem mail_pack_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : MailHere I.desc w ∧ ParkAlign w := by
  induction hR with
  | init => exact ⟨mail_here_init I N, align_init I N⟩
  | step w w' a hw h ih =>
    exact mail_pack_step I a w w' ih.1 ih.2 (inv2_reachable I hL hG N w hw).2.2.2 h

theorem mail_here_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : MailHere I.desc w :=
  (mail_pack_reachable I hL hG N w hR).1

end Deadlock
