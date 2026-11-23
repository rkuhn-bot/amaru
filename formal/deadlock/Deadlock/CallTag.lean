import Deadlock.Inv2

set_option autoImplicit false

namespace Deadlock

/-- A call leaves its subtree only toward a non-terminable template. Inside the
subtree the target may be terminable: the subtree kill fails that caller in the
same step. -/
theorem call_edge_unterminable (D : Description) (hG : GraphOk D) (e : Edge)
    (he : e ∈ D.edges) (hc : e.effect = .call) (t : Template)
    (ht : templateOf D e.dst = some t) :
    t.terminable = false ∨ sameSubtree D e.src e.dst = true := by
  have hall := by simpa [callTermFails] using hG.lifecycle
  have hnot : (e.effect != .call) = false := by
    rw [hc]
    decide
  have hbody := hall e he hnot
  simp [ht] at hbody
  cases hterm : t.terminable
  · exact Or.inl rfl
  · simp [hterm] at hbody
    exact Or.inr hbody

/-- A running `call` of a terminable target stays inside the caller's subtree.
The edge checker rejects a call that leaves the subtree toward a terminable role. -/
theorem running_call_same_subtree (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hS : SemInv I w) (id : InstId) (toState : String) (replyTo : Option InstId)
    (dst label : String) (hint : Nat) (tail : List Eff)
    (hph : (w.st id).phase = .run ⟨.call dst label hint :: tail, toState, replyTo⟩)
    (t : Template) (ht : templateOf I.desc dst = some t) (hterm : t.terminable = true) :
    sameSubtree I.desc (tname id) dst = true := by
  have hprog := hS.prog id
  simp [programOk, hph, effectsOk, Bool.and_eq_true] at hprog
  obtain ⟨e, he, hsrc, _, hdst, heff, _, _⟩ :=
    hasEdge_mem I.desc (tname id) (w.st id).typestate dst .call .blocking label hprog.1
  have hsplit := call_edge_unterminable I.desc hG e he heff t (by simpa [hdst] using ht)
  cases hsplit with
  | inl hnot => simp [hterm] at hnot
  | inr hsame => simpa [hsrc, hdst] using hsame

/-- A lone terminable never runs a `call` head. A subtree member may call a
per-peer sibling, so the empty subtree is essential. -/
theorem terminable_no_call_head (I : Impl) (w : World) (hB : BulkFree I w) (id : InstId)
    (t : Template) (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true)
    (hsub : t.subtree = "")
    (dst label : String) (hint : Nat) (tail : List Eff) (toState : String)
    (replyTo : Option InstId)
    (hph : (w.st id).phase = .run ⟨.call dst label hint :: tail, toState, replyTo⟩) : False := by
  have hbad := hB id
  simp [contRest, hph, bulkScopeOf, ht, hterm, hsub, noBulkSend] at hbad

theorem failWaiter_call (w : World) (dead i caller callee : InstId) (k : Cont)
    (h : CallWait ((failWaiter w dead i).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  by_cases hc : caller = i
  · rw [hc] at h ⊢
    unfold failWaiter at h
    split at h
    · exact h
    · cases hph : (w.st i).phase with
      | parked d b ck =>
        cases b with
        | false =>
          simp only [hph] at h
          by_cases hd : (d == dead) = true
          · simp only [hd, if_true, setActor_self] at h
            exact absurd h (proceed_not_callwait (w.st i) ck callee k)
          · have hbit : (d == dead) = false := by
              cases hb : d == dead with
              | true => exact absurd hb hd
              | false => rfl
            simp only [hbit] at h
            simpa [hph] using h
        | true =>
          simp only [hph] at h
          simpa [hph] using h
      | awaitReply _ _ =>
        simp only [hph] at h
        simpa [hph] using h
      | idle =>
        simp only [hph] at h
        simpa [hph] using h
      | run _ =>
        simp only [hph] at h
        simpa [hph] using h
      | awaitEffect _ =>
        simp only [hph] at h
        simpa [hph] using h
      | awaitPeer _ =>
        simp only [hph] at h
        simpa [hph] using h
      | crashed =>
        simp only [hph] at h
        simpa [hph] using h
  · rw [failWaiter_other w dead i caller hc] at h
    exact h

theorem failFold_call (w : World) (dead caller callee : InstId) (k : Cont) (ids : List InstId)
    (h : CallWait ((ids.foldl (fun w i => failWaiter w dead i) w).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons] at h
    exact failWaiter_call _ _ _ _ _ _ (ih _ h)

theorem credit_call (w : World) (name : String) (sender caller callee : InstId) (k : Cont)
    (h : CallWait ((creditSender w name sender).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  have hp := (credit_phase_life w name sender caller).1
  simpa [hp] using h

theorem refundMsgs_call (w : World) (name : String) (ms : List Msg) (caller callee : InstId) (k : Cont)
    (h : CallWait ((refundMsgs w name ms).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using h
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons] at h
    exact credit_call _ _ _ _ _ _ (ih _ h)

theorem refundParked_call (w : World) (name : String) (ps : List Parked) (caller callee : InstId)
    (k : Cont) (h : CallWait ((refundParked w name ps).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using h
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons] at h
    exact credit_call _ _ _ _ _ _ (ih _ h)

theorem forgetStep_call (w : World) (dead id caller callee : InstId) (k : Cont)
    (h : CallWait ((let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  dsimp only at h
  by_cases hcond : ((w.st id).parked.filter fun p => p.sender != dead) == (w.st id).parked
  · simp only [hcond, ite_true] at h
    exact h
  · simp only [hcond, ite_false, setActor] at h
    by_cases hc : caller = id
    · subst hc
      simpa [CallWait] using h
    · simpa [hc] using h

theorem forgetFold_call (w : World) (dead caller callee : InstId) (k : Cont) (ids : List InstId)
    (h : CallWait ((ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons id ids ih =>
    simp only [List.foldl_cons] at h
    exact forgetStep_call _ _ _ _ _ _ (ih _ h)

/-- Killing one member does not create a call wait. A waiter of that member is
failed, and everyone else's call wait was already there. -/
theorem killOne_call (w : World) (D : Description) (id caller callee : InstId) (k : Cont)
    (h : CallWait ((killOne w D id).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  let w3 := refundParked w2 (tname id) (w.st id).parked
  let w4 := failWaiters w3 id
  let w5 := forgetSender w4 id
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5]
  rw [hbody] at h
  have h5 : CallWait (w5.st caller).phase callee k := by
    by_cases hc : caller = id
    · subst hc
      simp [setActor, CallWait] at h
    · simpa [setActor, hc] using h
  have h4 : CallWait (w4.st caller).phase callee k := by
    have hph5 := (forget_stable w4 id caller).1
    simpa [w5, hph5] using h5
  have h3 : CallWait (w3.st caller).phase callee k := by
    simpa [w4, failWaiters] using failFold_call w3 id caller callee k w3.roster h4
  have h2 := refundParked_call w2 (tname id) (w.st id).parked caller callee k (by simpa [w3] using h3)
  have h1 := refundMsgs_call w1 (tname id) (w.st id).box caller callee k (by simpa [w2] using h2)
  simpa [w1, cellsSt] using h1

theorem killFold_call (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (caller callee : InstId) (k : Cont)
    (h : CallWait ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st caller).phase
        callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons id ids ih =>
    simp only [List.foldl_cons] at h
    split at h
    · exact killOne_call _ _ _ _ _ _ (ih _ h)
    · exact ih _ h

theorem killSubtree_call (w : World) (D : Description) (sub : String) (key : Nat)
    (caller callee : InstId) (k : Cont)
    (h : CallWait ((killSubtree w D sub key).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  simp [killSubtree] at h
  simpa [killMembers] using killFold_call w D sub key w.roster caller callee k h

theorem spawn_keeps_call (I : Impl) (w w' : World) (template : String) (caller callee : InstId) (k : Cont)
    (h : apply I (.spawn template) w = some w')
    (hc : CallWait (w'.st caller).phase callee k) : CallWait (w.st caller).phase callee k := by
  simp only [apply, spawn] at h
  split at h
  · cases h
  · next _ _ =>
    split at h
    · cases h
      simp [cellsSt] at hc
      by_cases hcaller : caller = InstId.peer template (w.nextIx template)
      · simp [hcaller, setActor, withTokens, CallWait] at hc
      · simpa [setActor, hcaller] using hc
    · cases h

theorem finish_keeps_call (I : Impl) (w w' : World) (id caller callee : InstId) (k : Cont)
    (h : apply I (.finish id) w = some w')
    (hc : CallWait (w'.st caller).phase callee k) : CallWait (w.st caller).phase callee k := by
  simp only [apply] at h
  unfold finishWait at h
  cases hph : (w.st id).phase with
  | awaitEffect kw =>
    simp [hph] at h
    cases h
    by_cases hcaller : caller = id
    · rw [hcaller] at hc
      simp [setActor] at hc
      exact absurd hc (proceed_not_callwait (w.st id) kw callee k)
    · simpa [setActor, hcaller] using hc
  | awaitPeer kw =>
    by_cases hf : peerFinishable I.desc id = true
    · simp [hph, hf] at h
      cases h
      by_cases hcaller : caller = id
      · rw [hcaller] at hc
        simp [setActor] at hc
        exact absurd hc (proceed_not_callwait (w.st id) kw callee k)
      · simpa [setActor, hcaller] using hc
    · simp [hph, hf] at h
  | idle => simp [hph] at h
  | run _ => simp [hph] at h
  | parked _ _ _ => simp [hph] at h
  | awaitReply _ _ => simp [hph] at h
  | crashed => simp [hph] at h

/-- The continuation a phase is blocked on, when it has one. -/
def carriedCont : Phase → Option Cont
  | .run k => some k
  | .parked _ _ k => some k
  | .awaitReply _ k => some k
  | .awaitEffect k => some k
  | .awaitPeer k => some k
  | .idle | .crashed => none

/-- `k` still owes `c` one reply, and does not terminate first. -/
def replyShape (c : InstId) (k : Cont) : Prop :=
  k.replyTo = some c ∧ replyCount k.rest = 1 ∧ terminateBeforeReply k.rest = false

def nextIsReply (k : Cont) : Prop :=
  match k.rest with
  | .reply :: _ => True
  | _ => False

/-- `d`'s bulk mailbox holds a call that names `c`. -/
def mailCall (w : World) (d c : InstId) : Prop :=
  (∃ m, m ∈ (w.st d).box ∧ m.callFrom = some c) ∨
  (∃ p, p ∈ (w.st d).parked ∧ p.msg.callFrom = some c)

/-- A queued call names the actor that sent it. -/
def BoxOwned (w : World) : Prop :=
  ∀ i m c, m ∈ (w.st i).box → m.callFrom = some c → m.sender = c

def countCall : List Msg → InstId → Nat
  | [], _ => 0
  | m :: ms, c => (if m.callFrom = some c then 1 else 0) + countCall ms c

def countParkedCall : List Parked → InstId → Nat
  | [], _ => 0
  | p :: ps, c => (if p.msg.callFrom = some c then 1 else 0) + countParkedCall ps c

/-- At most one bulk message names a given caller. Delivering it then leaves none. -/
def soleCall (w : World) (d c : InstId) : Prop :=
  countCall (w.st d).box c + countParkedCall (w.st d).parked c ≤ 1

/-- `d` is inside the handler for `c`, and the reply is not the next effect. -/
def handlerOwes (c : InstId) (ph : Phase) : Prop :=
  ∃ k, carriedCont ph = some k ∧ replyShape c k ∧ ¬nextIsReply k

/-- The next effect of `d`'s handler for `c` is the reply. It may still be behind
a wait: the reply runs when that continuation is next executed. -/
def replyPending (c : InstId) (ph : Phase) : Prop :=
  ∃ k, carriedCont ph = some k ∧ replyShape c k ∧ nextIsReply k

theorem handlerOwes_not_pending (c : InstId) (ph : Phase) : handlerOwes c ph → ¬replyPending c ph := by
  intro ⟨k, hk, _, hnot⟩ ⟨k', hk', _, hy⟩
  have : k = k' := by
    rw [hk] at hk'
    injection hk'
  exact hnot (this ▸ hy)

/-- While `c` is in `awaitReply d`, one of: the call is still in `d`'s mailbox,
`d` is in the handler and the reply is still ahead, that reply is the next
effect, or `d` has halted. In the last case `c` is
alive, so its deadline is enabled, and nobody owes or holds that call. A
parked entry carries `callFrom = some s` exactly when `s` is that entry's
sender and `s` is in `.parked d true`. Such a caller’s message is in the
parked list, not the box. No priority message carries a `callFrom`. -/
structure CallTagInv (w : World) : Prop where
  awaiting : ∀ c d k, (w.st c).phase = .awaitReply d k →
    (mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ replyPending c (w.st d).phase) ∨
    (Halted (w.st d).life ∧ (w.st c).life = .alive ∧ ¬mailCall w d c ∧
      ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase)
  /-- The callee is alive and holds the call, or it has halted and does not.
  A termination goes from alive to dead in one step and clears the parked list,
  so a halted callee does not keep the entry. The caller's deadline ends the
  wait, and the id is not reused. -/
  parkedCall : ∀ c d k, (w.st c).phase = .parked d true k →
    ((w.st d).life = .alive ∧ mailCall w d c ∧
        ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (Halted (w.st d).life ∧ ¬mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧
        ¬replyPending c (w.st d).phase)
  msgOwner : ∀ d c, mailCall w d c →
    (∃ k, (w.st c).phase = .awaitReply d k) ∨ (∃ k, (w.st c).phase = .parked d true k)
  oweOwner : ∀ d c, handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase →
    ∃ k, (w.st c).phase = .awaitReply d k
  prioPlain : ∀ id m, m ∈ (w.st id).prio → m.callFrom = none
  sole : ∀ d c, soleCall w d c
  parkFrom : ∀ d p, p ∈ (w.st d).parked → ∀ s,
    p.msg.callFrom = some s ↔ p.sender = s ∧ ∃ k, (w.st s).phase = .parked d true k
  parkedOnly : ∀ c d k, (w.st c).phase = .parked d true k →
    ((w.st d).life = .alive ∧
        (∃ p, p ∈ (w.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w.st d).box ∧ m.callFrom = some c) ∨
    (Halted (w.st d).life ∧
        (¬∃ p, p ∈ (w.st d).parked ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w.st d).box ∧ m.callFrom = some c)
  /-- A handler that still owes `c` a reply is stamped with `c`'s current wait id.
  A late reply for a retired id therefore cannot match a later call. -/
  owedId : ∀ d c, handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase →
    (w.st d).oweId = some (w.st c).waitId

/-- `CallTagInv` reads only actor state, so a world with the same actors satisfies it. -/
theorem callTag_st {w w' : World} (h : ∀ i, w'.st i = w.st i) (hT : CallTagInv w) : CallTagInv w' where
  awaiting c d k hk := by
    rw [h] at hk
    simpa [mailCall, h] using hT.awaiting c d k hk
  parkedCall c d k hk := by
    rw [h] at hk
    rcases hT.parkedCall c d k hk with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
    · exact Or.inl ⟨by simpa [h] using hl, by simpa [mailCall, h] using hm,
        by simpa [h] using ho, by simpa [h] using hp⟩
    · exact Or.inr ⟨by simpa [h] using hl, by simpa [mailCall, h] using hm,
        by simpa [h] using ho, by simpa [h] using hp⟩
  msgOwner d c hm := by
    have hm' : mailCall w d c := by simpa [mailCall, h] using hm
    simpa [h] using hT.msgOwner d c hm'
  oweOwner d c ho := by
    have ho' : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [h] using ho
    simpa [h] using hT.oweOwner d c ho'
  prioPlain id m hm := hT.prioPlain id m (by simpa [h] using hm)
  sole d c := by simpa [soleCall, h] using hT.sole d c
  parkFrom d p hp s := by
    have hp' : p ∈ (w.st d).parked := by simpa [h] using hp
    simpa [h] using hT.parkFrom d p hp' s
  parkedOnly c d k hk := by
    rw [h] at hk
    simpa [h] using hT.parkedOnly c d k hk
  owedId d c ho := by
    have ho' : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [h] using ho
    simpa [h] using hT.owedId d c ho'

/-- Recording a failed route does not change actors, so a call-tag invariant carries across. -/
theorem callTag_note (w0 : World) (sender id : InstId) (dst : String) (a : Actor)
    (hT : CallTagInv (setActor w0 id a)) :
    CallTagInv (setActor (noteStale w0 sender dst) id a) :=
  callTag_st (w := setActor w0 id a) (w' := setActor (noteStale w0 sender dst) id a)
    (fun _ => rfl) hT

theorem init_prio_empty (I : Impl) (N : Nat) (id : InstId) : ((initWorld I N).st id).prio = [] := by
  rw [init_base_st]
  split
  · unfold initActor
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem replyCount_ne_reply (e : Eff) (es : List Eff) (hne : e ≠ .reply) :
    replyCount (e :: es) = replyCount es := by
  cases e <;> simp [replyCount] at hne ⊢

theorem not_iff {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b :=
  ⟨fun hna hb => hna (h.mpr hb), fun hnb ha => hnb (h.mp ha)⟩

/-- The three live-callee cases. A caller waiting on a dead callee is not one of
them; that call ends by `TimedOut`. -/
def Awaiting3 (w : World) : Prop :=
  ∀ c d k, (w.st c).phase = .awaitReply d k →
    (mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ replyPending c (w.st d).phase)

theorem awaiting_dead_copy (w w' : World) (c d : InstId)
    (hlD : (w'.st d).life = (w.st d).life) (hlC : (w'.st c).life = (w.st c).life)
    (hmail : mailCall w' d c ↔ mailCall w d c)
    (howe : handlerOwes c (w'.st d).phase ↔ handlerOwes c (w.st d).phase)
    (hpend : replyPending c (w'.st d).phase ↔ replyPending c (w.st d).phase)
    (h : Halted (w.st d).life ∧ (w.st c).life = .alive ∧ ¬mailCall w d c ∧
        ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) :
    Halted (w'.st d).life ∧ (w'.st c).life = .alive ∧ ¬mailCall w' d c ∧
      ¬handlerOwes c (w'.st d).phase ∧ ¬replyPending c (w'.st d).phase :=
  ⟨hlD ▸ h.1, hlC.trans h.2.1, (not_iff hmail).mpr h.2.2.1,
    (not_iff howe).mpr h.2.2.2.1, (not_iff hpend).mpr h.2.2.2.2⟩

theorem terminateBefore_ne_reply (e : Eff) (es : List Eff)
    (h : terminateBeforeReply (e :: es) = false) (hne : e ≠ .reply) :
    e ≠ .terminate ∧ terminateBeforeReply es = false := by
  constructor
  · intro heq
    rw [heq] at h
    simp [terminateBeforeReply] at h
  · cases e <;> simp [terminateBeforeReply] at h hne <;> try exact h

theorem replyShape_nonempty (c : InstId) (k : Cont) (hs : replyShape c k) : k.rest ≠ [] := by
  intro hempty
  have hc := hs.2.1
  simp [replyCount, hempty] at hc

theorem replyShape_after (c : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hrest : k.rest = e :: es) (hs : replyShape c k) (hne : e ≠ .reply) :
    replyShape c (afterHead k) := by
  obtain ⟨hto, hcount, hterm⟩ := hs
  have hterm' := terminateBefore_ne_reply e es (by simpa [hrest] using hterm) hne
  refine ⟨?_, ?_, ?_⟩
  · simpa [afterHead, hrest] using hto
  · simpa [afterHead, hrest, replyCount_ne_reply e es hne] using hcount
  · simpa [afterHead, hrest] using hterm'.2

theorem proceed_carriedCont (a : Actor) (k : Cont) (hne : k.rest ≠ []) :
    carriedCont (proceed a k).phase = some k := by
  cases hk : k.rest <;> simp [proceed, carriedCont, hk] at hne ⊢

theorem credit_same (w : World) (name : String) (s i : InstId) :
    ((creditSender w name s).st i).box = (w.st i).box ∧
      ((creditSender w name s).st i).parked = (w.st i).parked ∧
      ((creditSender w name s).st i).phase = (w.st i).phase ∧
      ((creditSender w name s).st i).prio = (w.st i).prio := by
  by_cases hi : i = s <;> simp [creditSender, setActor, hi, bumpToken]

/-- Life is unchanged, except that spawning may turn an absent slot alive. -/
def LifeKeep (w w' : World) : Prop :=
  ∀ i, (w'.st i).life = (w.st i).life ∨
    ((w.st i).life = .absent ∧ (w'.st i).life = .alive)

theorem lifeKeep_of_eq {w w' : World} (h : ∀ i, (w'.st i).life = (w.st i).life) : LifeKeep w w' :=
  fun i => Or.inl (h i)

theorem lifeKeep_alive {w w' : World} {i : InstId} (h : LifeKeep w w')
    (hl : (w.st i).life = .alive) : (w'.st i).life = .alive := by
  rcases h i with heq | ⟨habs, _⟩
  · rw [heq, hl]
  · rw [habs] at hl
    cases hl

theorem lifeKeep_dead {w w' : World} {i : InstId} (h : LifeKeep w w')
    (hl : (w.st i).life = .dead) : (w'.st i).life = .dead := by
  rcases h i with heq | ⟨habs, _⟩
  · rw [heq, hl]
  · rw [habs] at hl
    cases hl

theorem lifeKeep_halted {w w' : World} {i : InstId} (h : LifeKeep w w')
    (hl : Halted (w.st i).life) : Halted (w'.st i).life := by
  unfold Halted at hl ⊢
  exact lifeKeep_dead h hl

theorem halted_cast {a b : Life} (h : a = b) (hh : Halted b) : Halted a := h ▸ hh

/-- The callee is alive, so it can still hold the call. A halted callee does not. -/
def Holding (l : Life) : Prop := l = .alive

theorem lifeKeep_holding {w w' : World} {i : InstId} (h : LifeKeep w w')
    (hl : Holding (w.st i).life) : Holding (w'.st i).life := by
  unfold Holding at hl ⊢
  exact lifeKeep_alive h hl

theorem awaiting_dead_keep (w w' : World) (c d : InstId) (hlife : LifeKeep w w')
    (hmail : mailCall w' d c ↔ mailCall w d c)
    (howe : handlerOwes c (w'.st d).phase ↔ handlerOwes c (w.st d).phase)
    (hpend : replyPending c (w'.st d).phase ↔ replyPending c (w.st d).phase)
    (h : Halted (w.st d).life ∧ (w.st c).life = .alive ∧ ¬mailCall w d c ∧
        ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) :
    Halted (w'.st d).life ∧ (w'.st c).life = .alive ∧ ¬mailCall w' d c ∧
      ¬handlerOwes c (w'.st d).phase ∧ ¬replyPending c (w'.st d).phase :=
  ⟨lifeKeep_halted hlife h.1, lifeKeep_alive hlife h.2.1, (not_iff hmail).mpr h.2.2.1,
    (not_iff howe).mpr h.2.2.2.1, (not_iff hpend).mpr h.2.2.2.2⟩

theorem life_setActor (w : World) (id : InstId) (a : Actor) (hl : a.life = (w.st id).life) :
    LifeKeep w (setActor w id a) :=
  lifeKeep_of_eq (fun i => by
    by_cases hi : i = id
    · simp [setActor, hi, hl]
    · simp [setActor, hi])

theorem life_set_st (w w1 : World) (id : InstId) (a : Actor)
    (hst : ∀ i, w1.st i = w.st i) (hl : a.life = (w.st id).life) :
    LifeKeep w (setActor w1 id a) :=
  lifeKeep_of_eq (fun i => by
    by_cases hi : i = id
    · simp [setActor, hi, hl]
    · simp [setActor, hi, hst])

/-- Same phases and mailboxes are the same call tags. -/
theorem call_tag_copy (w w' : World) (hT : CallTagInv w)
    (h : ∀ i, (w'.st i).phase = (w.st i).phase ∧ (w'.st i).box = (w.st i).box ∧
      (w'.st i).parked = (w.st i).parked ∧ (w'.st i).prio = (w.st i).prio)
    (hlife : LifeKeep w w')
    (howed : ∀ d c, handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase →
      (w'.st d).oweId = some (w'.st c).waitId) :
    CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, howed⟩
  · intro c d k hph
    have hpre := hT.awaiting c d k (by simpa [(h c).1] using hph)
    have hmail : mailCall w' d c ↔ mailCall w d c := by
      constructor
      · intro hm
        rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
        · exact Or.inl ⟨m, by simpa [(h d).2.1] using hmem, hc⟩
        · exact Or.inr ⟨p, by simpa [(h d).2.2.1] using hmem, hc⟩
      · intro hm
        rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
        · exact Or.inl ⟨m, by simpa [← (h d).2.1] using hmem, hc⟩
        · exact Or.inr ⟨p, by simpa [← (h d).2.2.1] using hmem, hc⟩
    have howe : handlerOwes c (w'.st d).phase ↔ handlerOwes c (w.st d).phase := by
      simp [(h d).1]
    have hpend : replyPending c (w'.st d).phase ↔ replyPending c (w.st d).phase := by
      simp [(h d).1]
    rcases hpre with h1 | h2 | h3 | h4
    · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
    · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
        hpend.mpr h3.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (awaiting_dead_keep w w' c d hlife hmail howe hpend h4)))
  · intro c d k hph
    have hpre := hT.parkedCall c d k (by simpa [(h c).1] using hph)
    have hmail : mailCall w d c → mailCall w' d c := by
      intro hm
      rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
      · exact Or.inl ⟨m, by simpa [← (h d).2.1] using hmem, hc⟩
      · exact Or.inr ⟨p, by simpa [← (h d).2.2.1] using hmem, hc⟩
    have hmail' : mailCall w' d c → mailCall w d c := by
      intro hm
      rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
      · exact Or.inl ⟨m, by simpa [(h d).2.1] using hmem, hc⟩
      · exact Or.inr ⟨p, by simpa [(h d).2.2.1] using hmem, hc⟩
    rcases hpre with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
    · exact Or.inl ⟨lifeKeep_holding hlife hl, hmail hm, by simpa [(h d).1] using ho,
        by simpa [(h d).1] using hp⟩
    · exact Or.inr ⟨lifeKeep_halted hlife hl, fun h => hm (hmail' h), by simpa [(h d).1] using ho,
        by simpa [(h d).1] using hp⟩
  · intro d c hm
    have hpre : mailCall w d c := by
      rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
      · exact Or.inl ⟨m, by simpa [(h d).2.1] using hmem, hc⟩
      · exact Or.inr ⟨p, by simpa [(h d).2.2.1] using hmem, hc⟩
    rcases hT.msgOwner d c hpre with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, by simpa [← (h c).1] using hk⟩
    · exact Or.inr ⟨k, by simpa [← (h c).1] using hk⟩
  · intro d c ho
    have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [(h d).1] using ho
    obtain ⟨k, hk⟩ := hT.oweOwner d c hpre
    exact ⟨k, by simpa [← (h c).1] using hk⟩
  · intro id m hm
    exact hT.prioPlain id m (by simpa [(h id).2.2.2] using hm)
  · intro d c
    simpa [soleCall, (h d).2.1, (h d).2.2.1] using hT.sole d c
  · intro d p hp s
    rw [(h d).2.2.1] at hp
    constructor
    · intro hc
      obtain ⟨hs, k, hk⟩ := (hT.parkFrom d p hp s).mp hc
      exact ⟨hs, k, by simpa [← (h s).1] using hk⟩
    · intro ⟨hs, k, hk⟩
      exact (hT.parkFrom d p hp s).mpr ⟨hs, k, by simpa [(h s).1] using hk⟩
  · intro c d k hph
    have hpre := hT.parkedOnly c d k (by simpa [(h c).1] using hph)
    rcases hpre with ⟨hl, ⟨p, hp, hs, hc⟩, hbox⟩ | ⟨hl, hno, hbox⟩
    · exact Or.inl ⟨lifeKeep_holding hlife hl, ⟨p, by simpa [← (h d).2.2.1] using hp, hs, hc⟩,
        fun ⟨m, hm, hc⟩ => hbox ⟨m, by simpa [(h d).2.1] using hm, hc⟩⟩
    · exact Or.inr ⟨lifeKeep_halted hlife hl,
        fun ⟨p, hp, hc⟩ => hno ⟨p, by simpa [(h d).2.2.1] using hp, hc⟩,
        fun ⟨m, hm, hc⟩ => hbox ⟨m, by simpa [(h d).2.1] using hm, hc⟩⟩

/-- Tags survive a step that keeps every await and parked call in place and does not
change who owes a reply or which call sits in a mailbox. -/
theorem call_tag_stable (w w' : World) (hT : CallTagInv w)
    (hmail : ∀ d c, mailCall w' d c ↔ mailCall w d c)
    (howe : ∀ i c, handlerOwes c (w'.st i).phase ↔ handlerOwes c (w.st i).phase)
    (hpend : ∀ i c, replyPending c (w'.st i).phase ↔ replyPending c (w.st i).phase)
    (hawait : ∀ c d k, (w'.st c).phase = .awaitReply d k → (w.st c).phase = .awaitReply d k)
    (hawait' : ∀ c d k, (w.st c).phase = .awaitReply d k → (w'.st c).phase = .awaitReply d k)
    (hpark : ∀ c d k, (w'.st c).phase = .parked d true k → (w.st c).phase = .parked d true k)
    (hpark' : ∀ c d k, (w.st c).phase = .parked d true k → (w'.st c).phase = .parked d true k)
    (hprio : ∀ id m, m ∈ (w'.st id).prio → m.callFrom = none)
    (hsole : ∀ d c, soleCall w' d c)
    (hfrom : ∀ d p, p ∈ (w'.st d).parked → ∀ s,
      p.msg.callFrom = some s ↔ p.sender = s ∧ ∃ k, (w'.st s).phase = .parked d true k)
    (honly : ∀ c d k, (w'.st c).phase = .parked d true k →
      (Holding (w'.st d).life ∧
          (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) ∨
      (Halted (w'.st d).life ∧
          (¬∃ p, p ∈ (w'.st d).parked ∧ p.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c))
    (hlife : LifeKeep w w')
    (howed : ∀ d c, handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase →
      (w'.st d).oweId = some (w'.st c).waitId) :
    CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio, hsole, hfrom, honly, howed⟩
  · intro c d k hph
    have hpre := hT.awaiting c d k (hawait c d k hph)
    rcases hpre with h1 | h2 | h3 | h4
    · exact Or.inl ⟨(hmail d c).mpr h1.1, (not_iff (howe d c)).mpr h1.2.1,
        (not_iff (hpend d c)).mpr h1.2.2⟩
    · exact Or.inr (Or.inl ⟨(not_iff (hmail d c)).mpr h2.1, (howe d c).mpr h2.2.1,
        (not_iff (hpend d c)).mpr h2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(not_iff (hmail d c)).mpr h3.1, (not_iff (howe d c)).mpr h3.2.1,
        (hpend d c).mpr h3.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (awaiting_dead_keep w w' c d hlife (hmail d c) (howe d c)
        (hpend d c) h4)))
  · intro c d k hph
    have hpre := hT.parkedCall c d k (hpark c d k hph)
    rcases hpre with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
    · exact Or.inl ⟨lifeKeep_holding hlife hl, (hmail d c).mpr hm,
        (not_iff (howe d c)).mpr ho, (not_iff (hpend d c)).mpr hp⟩
    · exact Or.inr ⟨lifeKeep_halted hlife hl, (not_iff (hmail d c)).mpr hm,
        (not_iff (howe d c)).mpr ho, (not_iff (hpend d c)).mpr hp⟩
  · intro d c hm
    rcases hT.msgOwner d c ((hmail d c).mp hm) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, hawait' c d k hk⟩
    · exact Or.inr ⟨k, hpark' c d k hk⟩
  · intro d c ho
    have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      rcases ho with h | h
      · exact Or.inl ((howe d c).mp h)
      · exact Or.inr ((hpend d c).mp h)
    obtain ⟨k, hk⟩ := hT.oweOwner d c hpre
    exact ⟨k, hawait' c d k hk⟩

/-- Mail and the existence of a handler obligation are what the three cases need.
Which of `handlerOwes` and `replyPending` holds may flip when the reply becomes next. -/
theorem call_tag_duty (w w' : World) (hT : CallTagInv w)
    (hmail : ∀ d c, mailCall w' d c ↔ mailCall w d c)
    (hduty : ∀ i c, (handlerOwes c (w'.st i).phase ∨ replyPending c (w'.st i).phase) ↔
      (handlerOwes c (w.st i).phase ∨ replyPending c (w.st i).phase))
    (hawait : ∀ c d k, (w'.st c).phase = .awaitReply d k → (w.st c).phase = .awaitReply d k)
    (hawait' : ∀ c d k, (w.st c).phase = .awaitReply d k → (w'.st c).phase = .awaitReply d k)
    (hpark : ∀ c d k, (w'.st c).phase = .parked d true k → (w.st c).phase = .parked d true k)
    (hpark' : ∀ c d k, (w.st c).phase = .parked d true k → (w'.st c).phase = .parked d true k)
    (hprio : ∀ id m, m ∈ (w'.st id).prio → m.callFrom = none)
    (hsole : ∀ d c, soleCall w' d c)
    (hfrom : ∀ d p, p ∈ (w'.st d).parked → ∀ s,
      p.msg.callFrom = some s ↔ p.sender = s ∧ ∃ k, (w'.st s).phase = .parked d true k)
    (honly : ∀ c d k, (w'.st c).phase = .parked d true k →
      (Holding (w'.st d).life ∧
          (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) ∨
      (Halted (w'.st d).life ∧
          (¬∃ p, p ∈ (w'.st d).parked ∧ p.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c))
    (hlife : LifeKeep w w')
    (howed : ∀ d c, handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase →
      (w'.st d).oweId = some (w'.st c).waitId) :
    CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio, hsole, hfrom, honly, howed⟩
  · intro c d k hph
    have hpre := hT.awaiting c d k (hawait c d k hph)
    have hxor := handlerOwes_not_pending c (w'.st d).phase
    rcases hpre with h1 | h2 | h3 | h4
    · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
        (not_iff (hduty d c)).mpr (fun h => h.elim (fun ho => h1.2.1 ho) (fun hp => h1.2.2 hp))
      exact Or.inl ⟨(hmail d c).mpr h1.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩
    · have hyes : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase :=
        (hduty d c).mpr (Or.inl h2.2.1)
      have hnom := (not_iff (hmail d c)).mpr h2.1
      rcases hyes with ho | hp
      · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hnom, fun ho => hxor ho hp, hp⟩))
    · have hyes : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase :=
        (hduty d c).mpr (Or.inr h3.2.2)
      have hnom := (not_iff (hmail d c)).mpr h3.1
      rcases hyes with ho | hp
      · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hnom, fun ho => hxor ho hp, hp⟩))
    · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
        (not_iff (hduty d c)).mpr (fun h => h.elim h4.2.2.2.1 h4.2.2.2.2)
      exact Or.inr (Or.inr (Or.inr ⟨lifeKeep_halted hlife h4.1, lifeKeep_alive hlife h4.2.1,
        (not_iff (hmail d c)).mpr h4.2.2.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩))
  · intro c d k hph
    have hpre := hT.parkedCall c d k (hpark c d k hph)
    rcases hpre with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
    · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
        (not_iff (hduty d c)).mpr (fun h => h.elim (fun howe => ho howe) (fun hpend => hp hpend))
      exact Or.inl ⟨lifeKeep_holding hlife hl, (hmail d c).mpr hm, fun howe => hno (Or.inl howe),
        fun hpend => hno (Or.inr hpend)⟩
    · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
        (not_iff (hduty d c)).mpr (fun h => h.elim (fun howe => ho howe) (fun hpend => hp hpend))
      exact Or.inr ⟨lifeKeep_halted hlife hl, (not_iff (hmail d c)).mpr hm, fun howe => hno (Or.inl howe),
        fun hpend => hno (Or.inr hpend)⟩
  · intro d c hm
    rcases hT.msgOwner d c ((hmail d c).mp hm) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, hawait' c d k hk⟩
    · exact Or.inr ⟨k, hpark' c d k hk⟩
  · intro d c ho
    have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase :=
      (hduty d c).mp ho
    obtain ⟨k, hk⟩ := hT.oweOwner d c hpre
    exact ⟨k, hawait' c d k hk⟩

theorem call_tag_init (I : Impl) (N : Nat) : CallTagInv (initWorld I N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d k hph
    simp [init_phase] at hph
  · intro c d k hph
    simp [init_phase] at hph
  · intro d c hmail
    rcases hmail with ⟨_, hm, _⟩ | ⟨_, hp, _⟩
    · simp [(init_box I N d).1] at hm
    · simp [(init_box I N d).2] at hp
  · intro d c h
    have hph := init_phase I N d
    rcases h with ⟨k, hk, _, _⟩ | ⟨k, hk, _, _⟩
    · simp [carriedCont, hph] at hk
    · simp [carriedCont, hph] at hk
  · intro id m hm
    simp [init_prio_empty] at hm
  · intro d c
    simp [soleCall, countCall, countParkedCall, (init_box I N d).1, (init_box I N d).2]
  · intro d p hp
    simp [(init_box I N d).2] at hp
  · intro c d k hph
    simp [init_phase] at hph
  · intro d c h
    have hph := init_phase I N d
    rcases h with ⟨k, hk, _, _⟩ | ⟨k, hk, _, _⟩
    · simp [carriedCont, hph] at hk
    · simp [carriedCont, hph] at hk

/-- Parked-entry facts survive when the parked lists agree, the new box is a
subset of the old one, and parked-call phases agree. -/
theorem parkFrom_transport (w w' : World) (hT : CallTagInv w)
    (hpark : ∀ i, (w'.st i).parked = (w.st i).parked)
    (hph : ∀ s d k, (w'.st s).phase = .parked d true k ↔ (w.st s).phase = .parked d true k)
    (d : InstId) (p : Parked) (hp : p ∈ (w'.st d).parked) (s : InstId) :
    p.msg.callFrom = some s ↔ p.sender = s ∧ ∃ k, (w'.st s).phase = .parked d true k := by
  rw [hpark d] at hp
  constructor
  · intro hc
    obtain ⟨hs, k, hk⟩ := (hT.parkFrom d p hp s).mp hc
    exact ⟨hs, k, (hph s d k).mpr hk⟩
  · intro ⟨hs, k, hk⟩
    exact (hT.parkFrom d p hp s).mpr ⟨hs, k, (hph s d k).mp hk⟩

theorem parkedOnly_transport (w w' : World) (hT : CallTagInv w)
    (hpark : ∀ i, (w'.st i).parked = (w.st i).parked)
    (hbox : ∀ i m, m ∈ (w'.st i).box → m ∈ (w.st i).box)
    (hph : ∀ c d k, (w'.st c).phase = .parked d true k → (w.st c).phase = .parked d true k)
    (c d : InstId) (k : Cont) (hk : (w'.st c).phase = .parked d true k)
    (hlife : LifeKeep w w') :
    (Holding (w'.st d).life ∧
        (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) ∨
    (Halted (w'.st d).life ∧
        (¬∃ p, p ∈ (w'.st d).parked ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) := by
  have hpre := hT.parkedOnly c d k (hph c d k hk)
  rcases hpre with ⟨hl, ⟨p, hp, hs, hc⟩, hnobox⟩ | ⟨hl, hno, hnobox⟩
  · exact Or.inl ⟨lifeKeep_holding hlife hl, ⟨p, by rw [hpark d]; exact hp, hs, hc⟩,
      fun ⟨m, hm, hc⟩ => hnobox ⟨m, hbox d m hm, hc⟩⟩
  · exact Or.inr ⟨lifeKeep_halted hlife hl,
      fun ⟨p, hp, hc⟩ => hno ⟨p, by simpa [hpark d] using hp, hc⟩,
      fun ⟨m, hm, hc⟩ => hnobox ⟨m, hbox d m hm, hc⟩⟩

/-- Move a parked-call fact across a step that keeps the callee's life and does not
invent a call message for that caller. -/
theorem parkedOnly_lift (w w' : World) (hT : CallTagInv w) (c d : InstId) (k : Cont)
    (hold : (w.st c).phase = .parked d true k) (hlife : (w'.st d).life = (w.st d).life)
    (hfwd : ∀ p, p ∈ (w.st d).parked → p.sender = c → p.msg.callFrom = some c →
      p ∈ (w'.st d).parked)
    (hback : ∀ p, p ∈ (w'.st d).parked → p.msg.callFrom = some c → p ∈ (w.st d).parked)
    (hboxBack : ∀ m, m ∈ (w'.st d).box → m.callFrom = some c → m ∈ (w.st d).box) :
    (Holding (w'.st d).life ∧
        (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) ∨
    (Halted (w'.st d).life ∧
        (¬∃ p, p ∈ (w'.st d).parked ∧ p.msg.callFrom = some c) ∧
        ¬∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) := by
  rcases hT.parkedOnly c d k hold with ⟨hl, ⟨p, hp, hs, hc⟩, hnobox⟩ | ⟨hl, hno, hnobox⟩
  · exact Or.inl ⟨by rw [hlife]; exact hl, ⟨p, hfwd p hp hs hc, hs, hc⟩,
      fun ⟨m, hm, hc⟩ => hnobox ⟨m, hboxBack m hm hc, hc⟩⟩
  · exact Or.inr ⟨by rw [hlife]; exact hl,
      fun ⟨p, hp, hc⟩ => hno ⟨p, hback p hp hc, hc⟩,
      fun ⟨m, hm, hc⟩ => hnobox ⟨m, hboxBack m hm hc, hc⟩⟩

/-- A call sitting in the box belongs to a caller already in `awaitReply`. -/
theorem box_awaits (w : World) (hT : CallTagInv w) (d : InstId) (m : Msg) (c : InstId)
    (hm : m ∈ (w.st d).box) (hc : m.callFrom = some c) :
    ∃ k, (w.st c).phase = .awaitReply d k := by
  rcases hT.msgOwner d c (Or.inl ⟨m, hm, hc⟩) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, hk⟩
  · rcases hT.parkedOnly c d k hk with ⟨_, _, hbox⟩ | ⟨_, _, hbox⟩
    · exact False.elim (hbox ⟨m, hm, hc⟩)
    · exact False.elim (hbox ⟨m, hm, hc⟩)

/-- A parked entry names its sender with `callFrom` exactly on a call. -/
theorem entry_align (w : World) (hT : CallTagInv w) (hM : MailInv w) (d : InstId)
    (p : Parked) (hp : p ∈ (w.st d).parked) :
    (p.isCall = true → p.msg.callFrom = some p.sender) ∧
      (p.isCall = false → p.msg.callFrom = none) := by
  obtain ⟨k, hph⟩ := hM.fwd d p hp
  constructor
  · intro hc
    have hph' : (w.st p.sender).phase = .parked d true k := by simpa [hc] using hph
    exact (hT.parkFrom d p hp p.sender).mpr ⟨rfl, k, hph'⟩
  · intro hc
    cases hcf : p.msg.callFrom with
    | none => rfl
    | some s =>
      obtain ⟨hs, k', hk'⟩ := (hT.parkFrom d p hp s).mp hcf
      have hph' : (w.st p.sender).phase = .parked d false k := by simpa [hc] using hph
      rw [hs] at hph'
      rw [hph'] at hk'
      cases hk'

theorem proceed_fields (a : Actor) (k : Cont) :
    (proceed a k).box = a.box ∧ (proceed a k).parked = a.parked ∧
      (proceed a k).prio = a.prio ∧ (proceed a k).life = a.life := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem proceed_stamps (a : Actor) (k : Cont) :
    (proceed a k).oweId = a.oweId ∧ (proceed a k).waitId = a.waitId := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem finishCall_phase (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).phase = (proceed a k).phase := by simp [finishCall]

theorem finishCall_box (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).box = a.box := by simp [finishCall, proceed_fields]

theorem finishCall_parked (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).parked = a.parked := by simp [finishCall, proceed_fields]

theorem finishCall_prio (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).prio = a.prio := by simp [finishCall, proceed_fields]

theorem finishCall_owe (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).oweId = a.oweId := by simp [finishCall, proceed_stamps]

theorem finishCall_wait (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).waitId = a.nextCall := by simp [finishCall]

theorem resume_stamps (a : Actor) (b : Bool) (dst : InstId) :
    (resumeSender a b dst).oweId = a.oweId ∧ (resumeSender a b dst).waitId = a.waitId := by
  unfold resumeSender
  split
  · split
    · simp
    · exact proceed_stamps _ _
  · exact ⟨rfl, rfl⟩

/-- Installing an actor that keeps the call id and the owed id leaves both stamps. -/
theorem stamp_set (w : World) (id : InstId) (a : Actor)
    (ho : a.oweId = (w.st id).oweId) (hw : a.waitId = (w.st id).waitId) :
    ∀ i, ((setActor w id a).st i).oweId = (w.st i).oweId ∧
      ((setActor w id a).st i).waitId = (w.st i).waitId := by
  intro i
  by_cases hi : i = id <;> simp [setActor, hi, ho, hw]

theorem credit_stamps_ow (w : World) (name : String) (s : InstId) :
    ∀ i, ((creditSender w name s).st i).oweId = (w.st i).oweId ∧
      ((creditSender w name s).st i).waitId = (w.st i).waitId := by
  intro i
  by_cases hi : i = s <;> simp [creditSender, setActor, bumpToken, hi]

/-- The agreement survives when every phase and both stamps are unchanged. -/
theorem owed_phase (w w' : World) (hT : CallTagInv w)
    (hph : ∀ i, (w'.st i).phase = (w.st i).phase)
    (hstamp : ∀ i, (w'.st i).oweId = (w.st i).oweId ∧ (w'.st i).waitId = (w.st i).waitId)
    (d c : InstId) (ho : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :
    (w'.st d).oweId = some (w'.st c).waitId := by
  have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
    simpa [hph d] using ho
  simpa [(hstamp d).1, (hstamp c).2] using hT.owedId d c hpre

/-- Installing an actor with the same phase and the same stamps keeps the agreement. -/
theorem owed_set_keep (w : World) (id : InstId) (a : Actor) (hT : CallTagInv w)
    (hph : a.phase = (w.st id).phase)
    (ho : a.oweId = (w.st id).oweId) (hw : a.waitId = (w.st id).waitId) :
    ∀ d c, handlerOwes c ((setActor w id a).st d).phase ∨
        replyPending c ((setActor w id a).st d).phase →
      ((setActor w id a).st d).oweId = some ((setActor w id a).st c).waitId :=
  fun d c h => owed_phase w (setActor w id a) hT
    (fun i => by by_cases hi : i = id <;> simp [setActor, hi, hph])
    (stamp_set w id a ho hw) d c h

/-- `proceed` either goes idle, carrying no reply, or keeps the same continuation.
Either way the owed id still names the caller's current wait id. -/
theorem owed_proceed (w : World) (id : InstId) (k : Cont) (hT : CallTagInv w)
    (hcar : carriedCont (w.st id).phase = some k) :
    ∀ d c, handlerOwes c ((setActor w id (proceed (w.st id) k)).st d).phase ∨
        replyPending c ((setActor w id (proceed (w.st id) k)).st d).phase →
      ((setActor w id (proceed (w.st id) k)).st d).oweId =
        some ((setActor w id (proceed (w.st id) k)).st c).waitId := by
  intro d c ho
  have hs := stamp_set w id (proceed (w.st id) k) (proceed_stamps _ _).1 (proceed_stamps _ _).2
  by_cases hd : d = id
  · rw [hd] at ho
    cases hk : k.rest with
    | nil =>
      rcases ho with ⟨_, hco, _⟩ | ⟨_, hco, _⟩ <;>
        simp [setActor, proceed, hk, carriedCont] at hco
    | cons _ _ =>
      have hcarry : carriedCont (proceed (w.st id) k).phase = some k := by
        simp [proceed, hk, carriedCont]
      have hback : handlerOwes c (w.st id).phase ∨ replyPending c (w.st id).phase := by
        rcases ho with ⟨k0, hk0, hs0, hn⟩ | ⟨k0, hk0, hs0, hn⟩
        · have hk0' : carriedCont (proceed (w.st id) k).phase = some k0 := by
            simpa [setActor] using hk0
          have heq : k0 = k := by injection hk0'.symm.trans hcarry
          exact Or.inl ⟨k0, heq ▸ hcar, hs0, hn⟩
        · have hk0' : carriedCont (proceed (w.st id) k).phase = some k0 := by
            simpa [setActor] using hk0
          have heq : k0 = k := by injection hk0'.symm.trans hcarry
          exact Or.inr ⟨k0, heq ▸ hcar, hs0, hn⟩
      rw [hd]
      simpa [(hs id).1, (hs c).2] using hT.owedId id c hback
  · have hback : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [setActor, hd] using ho
    simpa [(hs d).1, (hs c).2] using hT.owedId d c hback

/-- Installing an actor over an idle phase that still owes nobody keeps the agreement:
the new phase owes nobody, and nobody was waiting on the idle actor. -/
theorem owed_quiet_set (w w1 : World) (id : InstId) (a1 : Actor) (hT : CallTagInv w)
    (hst : ∀ i, w1.st i = w.st i) (hidle : (w.st id).phase = .idle)
    (hquiet : ∀ c, ¬handlerOwes c a1.phase ∧ ¬replyPending c a1.phase) :
    ∀ d c, handlerOwes c ((setActor w1 id a1).st d).phase ∨
        replyPending c ((setActor w1 id a1).st d).phase →
      ((setActor w1 id a1).st d).oweId = some ((setActor w1 id a1).st c).waitId := by
  intro d c ho
  by_cases hd : d = id
  · rw [hd] at ho
    rcases ho with h | h
    · exact absurd (by simpa [setActor] using h) (hquiet c).1
    · exact absurd (by simpa [setActor] using h) (hquiet c).2
  · by_cases hc : c = id
    · rw [hc] at ho
      have hpre : handlerOwes id (w.st d).phase ∨ replyPending id (w.st d).phase := by
        simpa [setActor, hd, hst] using ho
      obtain ⟨k, hk⟩ := hT.oweOwner d id hpre
      simp [hidle] at hk
    · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        simpa [setActor, hd, hst] using ho
      simpa [setActor, hd, hc, hst] using hT.owedId d c hpre

theorem mail_iff_lists (w w' : World)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box)
    (hpark : ∀ i, (w'.st i).parked = (w.st i).parked) (d c : InstId) :
    mailCall w' d c ↔ mailCall w d c := by
  constructor
  · intro hm
    rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
    · exact Or.inl ⟨m, by rw [hbox d] at hmem; exact hmem, hc⟩
    · exact Or.inr ⟨p, by rw [hpark d] at hmem; exact hmem, hc⟩
  · intro hm
    rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
    · exact Or.inl ⟨m, by rw [← hbox d] at hmem; exact hmem, hc⟩
    · exact Or.inr ⟨p, by rw [← hpark d] at hmem; exact hmem, hc⟩

theorem owes_iff_carried (ph ph' : Phase) (h : carriedCont ph' = carriedCont ph) (c : InstId) :
    handlerOwes c ph' ↔ handlerOwes c ph := by
  constructor
  · intro ⟨k, hk, hs, hn⟩
    exact ⟨k, h.symm.trans hk, hs, hn⟩
  · intro ⟨k, hk, hs, hn⟩
    exact ⟨k, h.trans hk, hs, hn⟩

theorem pending_iff_carried (ph ph' : Phase) (h : carriedCont ph' = carriedCont ph) (c : InstId) :
    replyPending c ph' ↔ replyPending c ph := by
  constructor
  · intro ⟨k, hk, hs, hn⟩
    exact ⟨k, h.symm.trans hk, hs, hn⟩
  · intro ⟨k, hk, hs, hn⟩
    exact ⟨k, h.trans hk, hs, hn⟩

theorem owes_empty (ph : Phase) (k : Cont) (h : carriedCont ph = some k) (hempty : k.rest = [])
    (c : InstId) : ¬handlerOwes c ph := by
  intro ⟨k', hk, hs, _⟩
  have hk' : k' = k := by
    rw [h] at hk
    injection hk with heq
    exact heq.symm
  have hc := hs.2.1
  simp [hk', hempty, replyCount] at hc

theorem pending_empty (ph : Phase) (k : Cont) (h : carriedCont ph = some k) (hempty : k.rest = [])
    (c : InstId) : ¬replyPending c ph := by
  intro ⟨k', hk, hs, _⟩
  have hk' : k' = k := by
    rw [h] at hk
    injection hk with heq
    exact heq.symm
  have hc := hs.2.1
  simp [hk', hempty, replyCount] at hc

/-- Resuming the continuation already carried by `id` does not move a call tag.
`id` itself is not in `awaitReply` or parked. -/
theorem resume_tag (w : World) (id : InstId) (k : Cont) (hT : CallTagInv w)
    (hph : carriedCont (w.st id).phase = some k)
    (hnotA : ∀ d kA, (w.st id).phase ≠ .awaitReply d kA)
    (hnotP : ∀ d (b : Bool) kA, (w.st id).phase ≠ .parked d b kA) :
    CallTagInv (setActor w id (proceed (w.st id) k)) := by
  let w' := setActor w id (proceed (w.st id) k)
  have hfields := proceed_fields (w.st id) k
  have hproc : ∀ d kA, (proceed (w.st id) k).phase ≠ .parked d true kA := by
    intro d kA
    cases hk : k.rest <;> simp [proceed, hk]
  apply call_tag_stable w w' hT
  · intro d c
    refine mail_iff_lists w w' ?_ ?_ d c
    · intro i
      by_cases hi : i = id <;> simp [w', setActor, hi, hfields.1]
    · intro i
      by_cases hi : i = id <;> simp [w', setActor, hi, hfields.2.1]
  · intro i c
    by_cases hi : i = id
    · rw [hi]
      by_cases hempty : k.rest = []
      · have hold := owes_empty (w.st id).phase k hph hempty c
        have hnew : ¬handlerOwes c (w'.st id).phase := by
          simp [w', setActor, proceed, hempty, handlerOwes, carriedCont]
        exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
      · have hnew : carriedCont (w'.st id).phase = some k := by
          simp [w', setActor, proceed_carriedCont (w.st id) k hempty]
        exact owes_iff_carried _ _ (hnew.trans hph.symm) c
    · have hst : (w'.st i).phase = (w.st i).phase := by simp [w', setActor, hi]
      exact owes_iff_carried _ _ (by simp [hst]) c
  · intro i c
    by_cases hi : i = id
    · rw [hi]
      by_cases hempty : k.rest = []
      · have hold := pending_empty (w.st id).phase k hph hempty c
        have hnew : ¬replyPending c (w'.st id).phase := by
          simp [w', setActor, proceed, hempty, replyPending, carriedCont]
        exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
      · have hnew : carriedCont (w'.st id).phase = some k := by
          simp [w', setActor, proceed_carriedCont (w.st id) k hempty]
        exact pending_iff_carried _ _ (hnew.trans hph.symm) c
    · have hst : (w'.st i).phase = (w.st i).phase := by simp [w', setActor, hi]
      exact pending_iff_carried _ _ (by simp [hst]) c
  · intro c d kA hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      simp [w', setActor, proceed] at hph'
      cases hk : k.rest <;> simp [hk] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      exact absurd hph' (hnotA d kA)
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      simp [w', setActor, proceed] at hph'
      cases hk : k.rest <;> simp [hk] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      exact absurd hph' (hnotP d true kA)
    · simpa [w', setActor, hc] using hph'
  · intro i m hm
    by_cases hi : i = id
    · exact hT.prioPlain id m (by simpa [w', setActor, hi, hfields.2.2.1] using hm)
    · exact hT.prioPlain i m (by simpa [w', setActor, hi] using hm)
  · intro d c
    have hbox : (w'.st d).box = (w.st d).box := by
      by_cases hd : d = id <;> simp [w', setActor, hd, hfields.1]
    have hpark : (w'.st d).parked = (w.st d).parked := by
      by_cases hd : d = id <;> simp [w', setActor, hd, hfields.2.1]
    simpa [soleCall, hbox, hpark] using hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi, hfields.2.1])
      (fun s d kP => ⟨
        fun h => by
          by_cases hs : s = id
          · rw [hs] at h
            simp [w', setActor] at h
            exact False.elim (hproc d kP h)
          · simpa [w', setActor, hs] using h,
        fun h => by
          by_cases hs : s = id
          · rw [hs] at h
            exact absurd h (hnotP d true kP)
          · simpa [w', setActor, hs] using h⟩)
      d p hp s
  · intro c d k hk
    refine parkedOnly_transport w w' hT
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi, hfields.2.1])
      (fun i m hm => by
        by_cases hi : i = id
        · simpa [w', setActor, hi, hfields.1] using hm
        · simpa [w', setActor, hi] using hm)
      (fun c d _ h => by
        by_cases hc : c = id
        · rw [hc] at h
          simp [w', setActor] at h
          exact False.elim (hproc d _ h)
        · simpa [w', setActor, hc] using h)
      c d k hk
      (lifeKeep_of_eq (fun i => by
        by_cases hi : i = id <;> simp [w', setActor, hi, proceed_life]))
  · exact lifeKeep_of_eq (fun i => by
      by_cases hi : i = id <;> simp [w', setActor, hi, proceed_life])
  · exact owed_proceed w id k hT hph

theorem finish_tag (I : Impl) (w : World) (id : InstId) (w' : World) (hT : CallTagInv w)
    (h : finishWait I w id = some w') : CallTagInv w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    exact resume_tag w id k hT (by simp [carriedCont, hph])
      (fun d kA hbad => by simp [hph] at hbad)
      (fun d b kA hbad => by simp [hph] at hbad)
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    exact resume_tag w id k hT (by simp [carriedCont, hph])
      (fun d kA hbad => by simp [hph] at hbad)
      (fun d b kA hbad => by simp [hph] at hbad)
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem countCall_snoc_none (ms : List Msg) (m : Msg) (c : InstId) (hc : m.callFrom = none) :
    countCall (ms ++ [m]) c = countCall ms c := by
  induction ms with
  | nil => simp [countCall, hc]
  | cons x xs ih => simp [countCall, ih]

/-- Appending an ingress message changes neither call id. -/
theorem ingress_stamps (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') (i : InstId) :
    (w'.st i).oweId = (w.st i).oweId ∧ (w'.st i).waitId = (w.st i).waitId := by
  dsimp [receiveIngress] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · cases h
            by_cases hi : i = dst <;> simp [setActor, hi, chargeSender, bumpToken]

/-- Environment ingress appends a non-call, so every call tag stays where it was. -/
theorem ingress_tag (I : Impl) (w : World) (dst : InstId) (label : String) (w' : World)
    (hT : CallTagInv w) (h : receiveIngress I w dst label = some w') : CallTagInv w' := by
  let msg : Msg :=
    { label := label, sender := dst, callFrom := none, reliable := true, mid := (w.st dst).nextMid }
  have hphase (i : InstId) : (w'.st i).phase = (w.st i).phase :=
    (ingress_phase I w w' dst label i h).1
  have hprio (i : InstId) : (w'.st i).prio = (w.st i).prio :=
    (ingress_phase I w w' dst label i h).2.2.1
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked :=
    (ingress_parked I w w' dst label i h).1
  apply call_tag_stable w w' hT
  · intro d c
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · rcases ingress_box I w w' dst label d h with ⟨_, hbox⟩ | ⟨_, hbox⟩
        · rw [hbox] at hm
          simp [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact Or.inl ⟨m, hm, hc⟩
          · simp [msg] at hc
        · exact Or.inl ⟨m, by simpa [hbox] using hm, hc⟩
      · exact Or.inr ⟨p, by simpa [hparked d] using hp, hc⟩
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · rcases ingress_box I w w' dst label d h with ⟨_, hbox⟩ | ⟨_, hbox⟩
        · exact Or.inl ⟨m, by simp [hbox, List.mem_append, hm], hc⟩
        · exact Or.inl ⟨m, by simpa [hbox] using hm, hc⟩
      · exact Or.inr ⟨p, by simpa [hparked d] using hp, hc⟩
  · intro i c
    constructor <;> simp [handlerOwes, hphase]
  · intro i c
    constructor <;> simp [replyPending, hphase]
  · intro c d k hph
    simpa [hphase c] using hph
  · intro c d k hph
    simpa [hphase c] using hph
  · intro c d k hph
    simpa [hphase c] using hph
  · intro c d k hph
    simpa [hphase c] using hph
  · intro id m hm
    rw [hprio id] at hm
    exact hT.prioPlain id m hm
  · intro d c
    rcases ingress_box I w w' dst label d h with ⟨_, hbox⟩ | ⟨_, hbox⟩
    · have hc := countCall_snoc_none (w.st d).box msg c rfl
      rw [soleCall, hbox, hc, hparked d]
      exact hT.sole d c
    · rw [soleCall, hbox, hparked d]
      exact hT.sole d c
  · intro d p hp s
    have hp0 : p ∈ (w.st d).parked := by simpa [hparked d] using hp
    constructor
    · intro hc
      rcases (hT.parkFrom d p hp0 s).mp hc with ⟨hs, k, hk⟩
      exact ⟨hs, k, by simpa [hphase s] using hk⟩
    · intro h
      rcases h with ⟨hs, k, hk⟩
      exact (hT.parkFrom d p hp0 s).mpr ⟨hs, k, by simpa [hphase s] using hk⟩
  · intro c d k hph
    exact parkedOnly_lift w w' hT c d k (by simpa [hphase c] using hph)
      ((ingress_phase I w w' dst label d h).2.1)
      (fun _ hp _ _ => by simpa [hparked d] using hp)
      (fun _ hp _ => by simpa [hparked d] using hp)
      (fun m hm hc => by
        rcases ingress_box I w w' dst label d h with ⟨_, hbox⟩ | ⟨_, hbox⟩
        · rw [hbox] at hm
          simp [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact hm
          · exact False.elim (by simp [msg] at hc)
        · exact by simpa [hbox] using hm)
  · exact lifeKeep_of_eq (fun i => (ingress_phase I w w' dst label i h).2.1)
  · exact fun d c ho => owed_phase w w' hT (fun i => (ingress_phase I w w' dst label i h).1)
      (fun i => ingress_stamps I w w' dst label h i) d c ho

/-- A freshly spawned actor is idle and empty, so it adds no call tag. -/
theorem spawn_tag (I : Impl) (w : World) (template : String) (w' : World)
    (hSlot : OpenSlots w) (hOcc : OccInv I w) (hT : CallTagInv w)
    (h : spawn I w template = some w') : CallTagInv w' := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp [ht] at h
    obtain ⟨_, heq⟩ := h
    let nid := InstId.peer template (w.nextIx template)
    have hnin : nid ∉ w.roster := by
      intro hmem
      have hix := hOcc.indexed template (w.nextIx template) hmem
      exact absurd hix (Nat.lt_irrefl _)
    have hopen : (w.st nid).life = .absent ∧ (w.st nid).phase = .idle ∧ (w.st nid).parked = [] := by
      simpa [nid] using hSlot template (w.nextIx template) (Nat.le_refl _)
    have hempty := hOcc.offEmpty nid hnin
    have hbox : ∀ i, (w'.st i).box = (w.st i).box := by
      rw [← heq]
      intro i
      by_cases hi : i = nid
      · simp [hi, nid, readCells_st, setActor, withTokens, hempty.1]
      · simp [readCells_st, setActor, hi, nid]
    have hparkL : ∀ i, (w'.st i).parked = (w.st i).parked := by
      rw [← heq]
      intro i
      by_cases hi : i = nid
      · simp [hi, nid, readCells_st, setActor, withTokens, hempty.2]
      · simp [readCells_st, setActor, hi, nid]
    have hlife : LifeKeep w w' := by
      intro i
      rw [← heq]
      by_cases hi : i = nid
      · rw [hi]
        exact Or.inr ⟨hopen.1, by simp [nid, readCells_st, setActor, withTokens]⟩
      · exact Or.inl (by simp [readCells_st, setActor, hi, nid])
    apply call_tag_stable w w' hT
    · intro d c
      exact mail_iff_lists w w' hbox hparkL d c
    · intro i c
      by_cases hi : i = nid
      · have hold : carriedCont (w.st nid).phase = none := by simp [carriedCont, hopen.2.1]
        have hnew : carriedCont (w'.st nid).phase = none := by
          rw [← heq]
          simp [nid, readCells_st, setActor, carriedCont, withTokens]
        exact owes_iff_carried _ _ (by rw [hi]; exact hnew.trans hold.symm) c
      · exact owes_iff_carried _ _ (by rw [← heq]; simp [nid, readCells_st, setActor, hi]) c
    · intro i c
      by_cases hi : i = nid
      · have hold : carriedCont (w.st nid).phase = none := by simp [carriedCont, hopen.2.1]
        have hnew : carriedCont (w'.st nid).phase = none := by
          rw [← heq]
          simp [nid, readCells_st, setActor, carriedCont, withTokens]
        exact pending_iff_carried _ _ (by rw [hi]; exact hnew.trans hold.symm) c
      · exact pending_iff_carried _ _ (by rw [← heq]; simp [nid, readCells_st, setActor, hi]) c
    · intro c d k hph
      rw [← heq] at hph
      by_cases hc : c = nid
      · simp [hc, nid, readCells_st, setActor, withTokens] at hph
      · simpa [nid, readCells_st, setActor, hc] using hph
    · intro c d k hph
      by_cases hc : c = nid
      · simp [hopen.2.1, hc] at hph
      · have hst : (w'.st c).phase = (w.st c).phase := by
          rw [← heq]
          simp [nid, readCells_st, setActor, hc]
        simpa [hst] using hph
    · intro c d k hph
      rw [← heq] at hph
      by_cases hc : c = nid
      · simp [hc, nid, readCells_st, setActor, withTokens] at hph
      · simpa [nid, readCells_st, setActor, hc] using hph
    · intro c d k hph
      by_cases hc : c = nid
      · simp [hopen.2.1, hc] at hph
      · have hst : (w'.st c).phase = (w.st c).phase := by
          rw [← heq]
          simp [nid, readCells_st, setActor, hc]
        simpa [hst] using hph
    · intro i m hm
      rw [← heq] at hm
      by_cases hi : i = nid
      · simp [hi, nid, readCells_st, setActor, withTokens] at hm
      · exact hT.prioPlain i m (by simpa [nid, readCells_st, setActor, hi] using hm)
    · intro d c
      simpa [soleCall, hbox d, hparkL d] using hT.sole d c
    · intro d p hp s
      exact parkFrom_transport w w' hT hparkL
        (fun s d k => ⟨
          fun h => by
            by_cases hs : s = nid
            · rw [← heq] at h
              simp [hs, nid, readCells_st, setActor, withTokens] at h
            · have hst : (w'.st s).phase = (w.st s).phase := by
                rw [← heq]
                simp [nid, readCells_st, setActor, hs]
              rwa [hst] at h,
          fun h => by
            by_cases hs : s = nid
            · simp [hopen.2.1, hs] at h
            · have hst : (w'.st s).phase = (w.st s).phase := by
                rw [← heq]
                simp [nid, readCells_st, setActor, hs]
              rwa [← hst] at h⟩)
        d p hp s
    · intro c d k hk
      exact parkedOnly_transport w w' hT hparkL
        (fun i m hm => by rw [hbox i] at hm; exact hm)
        (fun c d k h => by
          by_cases hc : c = nid
          · rw [← heq] at h
            simp [hc, nid, readCells_st, setActor, withTokens] at h
          · have hst : (w'.st c).phase = (w.st c).phase := by
              rw [← heq]
              simp [nid, readCells_st, setActor, hc]
            rwa [hst] at h)
        c d k hk
        hlife
    · exact hlife
    · intro d c ho
      by_cases hd : d = nid
      · have hquiet : carriedCont (w'.st nid).phase = none := by
          rw [← heq]
          simp [nid, readCells_st, setActor, carriedCont, withTokens]
        rcases ho with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> simp [hd, hquiet] at hk
      · by_cases hc0 : c = nid
        · have hphD : (w'.st d).phase = (w.st d).phase := by
            rw [← heq]
            simp [nid, readCells_st, setActor, hd]
          have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
            simpa [hphD] using ho
          obtain ⟨k, hk⟩ := hT.oweOwner d c hpre
          simp [hc0, hopen.2.1] at hk
        · have hphD : (w'.st d).phase = (w.st d).phase := by
            rw [← heq]
            simp [nid, readCells_st, setActor, hd]
          have howe : (w'.st d).oweId = (w.st d).oweId := by
            rw [← heq]
            simp [nid, readCells_st, setActor, hd, withTokens]
          have hwait : (w'.st c).waitId = (w.st c).waitId := by
            rw [← heq]
            simp [nid, readCells_st, setActor, hc0, withTokens]
          have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
            simpa [hphD] using ho
          simpa [howe, hwait] using hT.owedId d c hpre

theorem plain_no_owe (ph : Phase) (c : InstId)
    (h : carriedCont ph = none ∨ ∃ k, carriedCont ph = some k ∧ k.replyTo = none) :
    ¬handlerOwes c ph ∧ ¬replyPending c ph := by
  constructor
  · intro ⟨k, hk, hs, _⟩
    rcases h with hnone | ⟨k', hk', hto⟩
    · simp [hnone] at hk
    · rw [hk] at hk'
      cases hk'
      have hbad := hs.1
      simp [hto] at hbad
  · intro ⟨k, hk, hs, _⟩
    rcases h with hnone | ⟨k', hk', hto⟩
    · simp [hnone] at hk
    · rw [hk] at hk'
      cases hk'
      have hbad := hs.1
      simp [hto] at hbad

/-- A priority or ordinary message carries no caller, so delivering it starts no handler. -/
theorem deliver_plain (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) (hc : m.callFrom = none) :
    a1.box = a.box ∧ a1.parked = a.parked ∧ a1.prio = a.prio ∧
      (a1.phase = .idle ∨ ∃ k, a1.phase = .run k ∧ k.replyTo = none) := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · next hnot => simp [hc, Option.isSome] at hnot
      · simp [hc, Option.isSome] at h
        rcases h with ⟨_, ha⟩
        subst ha
        exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
    · next tr htr =>
      split at h
      · simp [hc] at h
      · cases h
        cases tr.program with
        | nil => exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
        | cons _ _ => exact ⟨rfl, rfl, rfl, Or.inr ⟨_, rfl, hc⟩⟩

theorem deliver_call (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (c : InstId) (h : deliver I w id a m = some (w1, a1))
    (hc : m.callFrom = some c) :
    a1.box = a.box ∧ a1.parked = a.parked ∧ a1.prio = a.prio ∧
      a1.waitId = a.waitId ∧
      a1.oweId = some (if c = id then a.waitId else (w.st c).waitId) ∧
      ∃ k, a1.phase = .run k ∧ replyShape c k ∧
        (nextIsReply k ∨ ¬nextIsReply k) ∧
        ∀ c', c' ≠ c → ¬handlerOwes c' a1.phase ∧ ¬replyPending c' a1.phase := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · simp [hc, Option.isSome] at *
      · simp [hc, Option.isSome] at *
    · next tr htr =>
      have hmem := (findTr_mem I (tname id) a.typestate m.label tr htr).1
      have hacc : tr.acceptsCall = true := by
        cases hb : tr.acceptsCall with
        | false => simp [hc, Option.isSome, hb] at h
        | true => rfl
      have hok := transitionOk_of_mem I hL tr hmem
      cases ht : templateOf I.desc tr.template with
      | none => simp [transitionOk, ht] at hok
      | some t =>
        simp only [transitionOk, ht, hacc, ite_true] at hok
        repeat rw [Bool.and_eq_true] at hok
        have hcount : replyCount tr.program = 1 := beq_iff_eq.mp hok.1.1.2.1
        have hterm : terminateBeforeReply tr.program = false := by
          cases hb : terminateBeforeReply tr.program
          · rfl
          · simp [hb] at hok
        have hne : tr.program ≠ [] := by
          intro hempty
          simp [hempty, replyCount] at hcount
        simp [hc, Option.isSome, hacc] at h
        rcases h with ⟨_, ha⟩
        subst ha
        cases hp : tr.program with
        | nil => exact absurd hp hne
        | cons e es =>
          refine ⟨rfl, rfl, rfl, rfl, by simp [cellsSt], ?_⟩
          refine ⟨{ rest := e :: es, toState := tr.toState, replyTo := some c }, rfl, ?_, ?_, ?_⟩
          · exact ⟨rfl, by simpa [hp] using hcount, by simpa [hp] using hterm⟩
          · by_cases hr : e = .reply
            · exact Or.inl (by simp [nextIsReply, hr])
            · exact Or.inr (by
                cases e <;> simp [nextIsReply] at hr ⊢)
          · intro c' hne'
            have hto : ¬({ rest := e :: es, toState := tr.toState, replyTo := some c } : Cont).replyTo = some c' := by
              intro hbad
              injection hbad with heq
              exact hne' heq.symm
            constructor
            · intro ⟨k, hk, hs, _⟩
              simp [carriedCont] at hk
              cases hk
              have hbad := hs.1
              simp [hto] at hbad
            · intro ⟨k, hk, hs, _⟩
              simp [carriedCont] at hk
              cases hk
              have hbad := hs.1
              simp [hto] at hbad

theorem prio_tag (I : Impl) (w : World) (id : InstId) (w' : World) (hT : CallTagInv w)
    (h : receivePrio I w id = some w') : CallTagInv w' := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp [hp] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      obtain ⟨⟨_, hidle⟩, heq⟩ := h
      injection heq with hw
      subst hw
      have hc : m.callFrom = none := hT.prioPlain id m (by simp [hp])
      have hplain := deliver_plain I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel hc
      have hst : ∀ i, w1.st i = w.st i := fun i =>
        deliver_st I w id ({ (w.st id) with prio := ms }) m w1 a1 i hdel
      apply call_tag_stable w (setActor w1 id a1) hT
      · intro d c
        refine mail_iff_lists w (setActor w1 id a1) ?_ ?_ d c
        · intro i
          by_cases hi : i = id
          · simp [setActor, hi, hst, hplain.1]
          · simp [setActor, hi, hst]
        · intro i
          by_cases hi : i = id
          · simp [setActor, hi, hst, hplain.2.1]
          · simp [setActor, hi, hst]
      · intro i c
        by_cases hi : i = id
        · rw [hi]
          have hold : ¬handlerOwes c (w.st id).phase := by
            simp [handlerOwes, carriedCont, hidle]
          have hnew : ¬handlerOwes c a1.phase := (plain_no_owe a1.phase c (by
            rcases hplain.2.2.2 with hI | ⟨k, hk, hto⟩
            · exact Or.inl (by simp [carriedCont, hI])
            · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩)).1
          simp [setActor]
          exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
        · have hph : ((setActor w1 id a1).st i).phase = (w.st i).phase := by simp [setActor, hi, hst]
          exact owes_iff_carried _ _ (by simp [hph]) c
      · intro i c
        by_cases hi : i = id
        · rw [hi]
          have hold : ¬replyPending c (w.st id).phase := by
            simp [replyPending, carriedCont, hidle]
          have hnew : ¬replyPending c a1.phase := (plain_no_owe a1.phase c (by
            rcases hplain.2.2.2 with hI | ⟨k, hk, hto⟩
            · exact Or.inl (by simp [carriedCont, hI])
            · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩)).2
          simp [setActor]
          exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
        · have hph : ((setActor w1 id a1).st i).phase = (w.st i).phase := by simp [setActor, hi, hst]
          exact pending_iff_carried _ _ (by simp [hph]) c
      · intro c d k hph
        by_cases hc : c = id
        · simp [setActor, hc, hst] at hph
          rcases hplain.2.2.2 with hI | ⟨_, hk, _⟩
          · simp [hI] at hph
          · simp [hk] at hph
        · simpa [setActor, hc, hst] using hph
      · intro c d k hph
        by_cases hc : c = id
        · simp [hidle, hc] at hph
        · simpa [setActor, hc, hst] using hph
      · intro c d k hph
        by_cases hc : c = id
        · simp [setActor, hc, hst] at hph
          rcases hplain.2.2.2 with hI | ⟨_, hk, _⟩
          · simp [hI] at hph
          · simp [hk] at hph
        · simpa [setActor, hc, hst] using hph
      · intro c d k hph
        by_cases hc : c = id
        · simp [hidle, hc] at hph
        · simpa [setActor, hc, hst] using hph
      · intro i msg hm
        by_cases hi : i = id
        · have hmem : msg ∈ ms := by simpa [setActor, hi, hst, hplain.2.2.1] using hm
          exact hT.prioPlain id msg (by simp [hp, hmem])
        · exact hT.prioPlain i msg (by simpa [setActor, hi, hst] using hm)
      · intro d c
        have hbox : ((setActor w1 id a1).st d).box = (w.st d).box := by
          by_cases hd : d = id
          · simp [setActor, hd, hst, hplain.1]
          · simp [setActor, hd, hst]
        have hpark : ((setActor w1 id a1).st d).parked = (w.st d).parked := by
          by_cases hd : d = id
          · simp [setActor, hd, hst, hplain.2.1]
          · simp [setActor, hd, hst]
        simpa [soleCall, hbox, hpark] using hT.sole d c
      · intro d p hp s
        exact parkFrom_transport w (setActor w1 id a1) hT
          (fun i => by
            by_cases hi : i = id
            · simp [setActor, hi, hst, hplain.2.1]
            · simp [setActor, hi, hst])
          (fun s d k => ⟨
            fun h => by
              by_cases hs : s = id
              · simp [setActor, hs, hst] at h
                rcases hplain.2.2.2 with hI | ⟨_, hk, _⟩ <;>
                first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
              · simpa [setActor, hs, hst] using h,
            fun h => by
              by_cases hs : s = id
              · simp [hidle, hs] at h
              · simpa [setActor, hs, hst] using h⟩)
          d p hp s
      · intro c d k hk
        exact parkedOnly_transport w (setActor w1 id a1) hT
          (fun i => by
            by_cases hi : i = id
            · simp [setActor, hi, hst, hplain.2.1]
            · simp [setActor, hi, hst])
          (fun i m hm => by
            by_cases hi : i = id
            · simpa [setActor, hi, hst, hplain.1] using hm
            · simpa [setActor, hi, hst] using hm)
          (fun c d k h => by
            by_cases hc : c = id
            · simp [setActor, hc, hst] at h
              rcases hplain.2.2.2 with hI | ⟨_, hk, _⟩ <;>
                first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
            · simpa [setActor, hc, hst] using h)
          c d k hk
          (life_set_st w w1 id a1 hst (by
            simpa using (deliver_life I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel).1))
      · exact life_set_st w w1 id a1 hst (by
          simpa using (deliver_life I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel).1)
      · exact owed_quiet_set w w1 id a1 hT hst hidle
          (fun c => plain_no_owe a1.phase c (by
            rcases hplain.2.2.2 with hI | ⟨k, hk, hto⟩
            · exact Or.inl (by simp [carriedCont, hI])
            · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩))

/-- Crediting a sender only changes a token. -/
theorem credit_tag (w : World) (name : String) (s : InstId) (hT : CallTagInv w) :
    CallTagInv (creditSender w name s) := by
  apply call_tag_stable w (creditSender w name s) hT
  · intro d c
    exact mail_iff_lists w _ (fun i => (credit_same w name s i).1)
      (fun i => (credit_same w name s i).2.1) d c
  · intro i c
    exact owes_iff_carried _ _ (by simp [(credit_same w name s i).2.2.1]) c
  · intro i c
    exact pending_iff_carried _ _ (by simp [(credit_same w name s i).2.2.1]) c
  · intro c d k hph
    simpa [(credit_same w name s c).2.2.1] using hph
  · intro c d k hph
    simpa [(credit_same w name s c).2.2.1] using hph
  · intro c d k hph
    simpa [(credit_same w name s c).2.2.1] using hph
  · intro c d k hph
    simpa [(credit_same w name s c).2.2.1] using hph
  · intro i m hm
    exact hT.prioPlain i m (by simpa [(credit_same w name s i).2.2.2] using hm)
  · intro d c
    simpa [soleCall, (credit_same w name s d).1, (credit_same w name s d).2.1] using hT.sole d c
  · intro d p hp s0
    exact parkFrom_transport w (creditSender w name s) hT
      (fun i => (credit_same w name s i).2.1)
      (fun s0 d k => ⟨
        fun h => by simpa [(credit_same w name s s0).2.2.1] using h,
        fun h => by simpa [← (credit_same w name s s0).2.2.1] using h⟩)
      d p hp s0
  · intro c d k hk
    exact parkedOnly_transport w (creditSender w name s) hT
      (fun i => (credit_same w name s i).2.1)
      (fun i m hm => by simpa [(credit_same w name s i).1] using hm)
      (fun c d k h => by simpa [(credit_same w name s c).2.2.1] using h)
      c d k hk
      (lifeKeep_of_eq (fun i => (credit_phase_life w name s i).2))
  · exact lifeKeep_of_eq (fun i => (credit_phase_life w name s i).2)
  · exact fun d c ho => owed_phase w (creditSender w name s) hT
      (fun i => (credit_same w name s i).2.2.1) (credit_stamps_ow w name s) d c ho

theorem count_none (m : Msg) (ms : List Msg) (c : InstId) (h : m.callFrom = none) :
    countCall (m :: ms) c = countCall ms c := by
  simp [countCall, h]

theorem mem_drop_none (m : Msg) (ms : List Msg) (c : InstId) (h : m.callFrom = none) :
    (∃ x, x ∈ ms ∧ x.callFrom = some c) ↔ (∃ x, x ∈ m :: ms ∧ x.callFrom = some c) := by
  constructor
  · intro ⟨x, hx, hc⟩
    exact ⟨x, List.mem_cons_of_mem _ hx, hc⟩
  · intro ⟨x, hx, hc⟩
    cases hx with
    | head => simp [h] at hc
    | tail _ ht => exact ⟨x, ht, hc⟩

/-- Dropping a non-call at the head of an idle mailbox does not move a tag. -/
theorem install_plain (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hpark0 : (w.st id).parked = [])
    (hbox1 : a1.box = ms) (hpark1 : a1.parked = []) (hprio1 : a1.prio = (w.st id).prio)
    (hlifeA : a1.life = (w.st id).life)
    (hph : a1.phase = .idle ∨ ∃ k, a1.phase = .run k ∧ k.replyTo = none)
    (hhead : (w.st id).box = m :: ms) (hc : m.callFrom = none) :
    CallTagInv (setActor w1 id a1) := by
  have hcarry : ∀ c : InstId, carriedCont a1.phase = none ∨
      ∃ k, carriedCont a1.phase = some k ∧ k.replyTo = none := by
    intro c
    rcases hph with hI | ⟨k, hk, hto⟩
    · exact Or.inl (by simp [carriedCont, hI])
    · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩
  apply call_tag_stable w (setActor w1 id a1) hT
  · intro d c
    constructor
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
        · have hx' : x ∈ ms := by
            simp only [setActor, hd, hst, if_true] at hx
            rw [hbox1] at hx
            exact hx
          exact Or.inl ⟨x, by rw [hd, hhead]; exact List.mem_cons_of_mem _ hx', hcf⟩
        · have hp' : p ∈ a1.parked := by
            simp only [setActor, hd, hst, if_true] at hp
            exact hp
          simp [hpark1] at hp'
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
        · exact Or.inl ⟨x, by simpa [setActor, hd, hst] using hx, hcf⟩
        · exact Or.inr ⟨p, by simpa [setActor, hd, hst] using hp, hcf⟩
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
        · have hx' : x ∈ ms := by
            rw [hd, hhead] at hx
            cases hx with
            | head => simp [hc] at hcf
            | tail _ ht => exact ht
          exact Or.inl ⟨x, by simp [setActor, hd, hst, hbox1, hx'], hcf⟩
        · simp [hpark0, hd] at hp
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
        · exact Or.inl ⟨x, by simp [setActor, hd, hst, hx], hcf⟩
        · exact Or.inr ⟨p, by simp [setActor, hd, hst, hp], hcf⟩
  · intro i c
    by_cases hi : i = id
    · have hold : ¬handlerOwes c (w.st id).phase := by simp [handlerOwes, carriedCont, hidle]
      have hnew : ¬handlerOwes c a1.phase := (plain_no_owe a1.phase c (hcarry c)).1
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact owes_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro i c
    by_cases hi : i = id
    · have hold : ¬replyPending c (w.st id).phase := by simp [replyPending, carriedCont, hidle]
      have hnew : ¬replyPending c a1.phase := (plain_no_owe a1.phase c (hcarry c)).2
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact pending_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro i msg hm
    by_cases hi : i = id
    · exact hT.prioPlain id msg (by simpa [setActor, hi, hst, hprio1] using hm)
    · exact hT.prioPlain i msg (by simpa [setActor, hi, hst] using hm)
  · intro d c
    by_cases hd : d = id
    · have hs := hT.sole id c
      unfold soleCall at hs
      rw [hhead, hpark0, count_none m ms c hc] at hs
      simpa [soleCall, setActor, hd, hst, hbox1, hpark1] using hs
    · simp [soleCall, setActor, hd, hst]
      exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w (setActor w1 id a1) hT
      (fun i => by
        by_cases hi : i = id
        · simp [setActor, hi, hst, hpark1, hpark0]
        · simp [setActor, hi, hst])
      (fun s d _ => ⟨
        fun h => by
          by_cases hs : s = id
          · simp [setActor, hs, hst] at h
            rcases hph with hI | ⟨_, hk, _⟩ <;>
            first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
          · simpa [setActor, hs, hst] using h,
        fun h => by
          by_cases hs : s = id
          · simp [hidle, hs] at h
          · simpa [setActor, hs, hst] using h⟩)
      d p hp s
  · intro c d k hk
    exact parkedOnly_transport w (setActor w1 id a1) hT
      (fun i => by
        by_cases hi : i = id
        · simp [setActor, hi, hst, hpark1, hpark0]
        · simp [setActor, hi, hst])
      (fun i msg hm => by
        by_cases hi : i = id
        · have hm' : msg ∈ ms := by
            simp only [setActor, hi, hst, ite_true] at hm
            rw [hbox1] at hm
            exact hm
          rw [hi, hhead]
          exact List.mem_cons_of_mem _ hm'
        · simpa [setActor, hi, hst] using hm)
      (fun c d _ h => by
        by_cases hc0 : c = id
        · simp [setActor, hc0, hst] at h
          rcases hph with hI | ⟨_, hk, _⟩ <;>
            first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
        · simpa [setActor, hc0, hst] using h)
      c d k hk
      (life_set_st w w1 id a1 hst hlifeA)
  · exact life_set_st w w1 id a1 hst hlifeA
  · exact owed_quiet_set w w1 id a1 hT hst hidle (fun c0 => plain_no_owe _ c0 (hcarry c0))

theorem count_some (m : Msg) (ms : List Msg) (c : InstId) (h : m.callFrom = some c) :
    countCall (m :: ms) c = countCall ms c + 1 := by
  simp [countCall, h, Nat.add_comm]

theorem countParked_zero_mem (ps : List Parked) (c : InstId) (h : countParkedCall ps c = 0) :
    ∀ p, p ∈ ps → p.msg.callFrom ≠ some c := by
  induction ps with
  | nil => intro _ hp; cases hp
  | cons q qs ih =>
    simp [countParkedCall] at h
    by_cases hq : q.msg.callFrom = some c
    · simp [hq] at h
    · simp [hq] at h
      intro p hp
      cases hp with
      | head => exact hq
      | tail _ ht => exact ih h p ht

theorem count_zero_mem (ms : List Msg) (c : InstId) (h : countCall ms c = 0) :
    ∀ m, m ∈ ms → m.callFrom ≠ some c := by
  induction ms with
  | nil => intro _ hm; cases hm
  | cons q qs ih =>
    simp [countCall] at h
    by_cases hq : q.callFrom = some c
    · simp [hq] at h
    · simp [hq] at h
      intro m hm
      cases hm with
      | head => exact hq
      | tail _ ht => exact ih h m ht

/-- Delivering the unique call at the head of an idle mailbox starts its handler.
The caller is already in `awaitReply`, because the parked list is empty. -/
theorem install_call (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (c : InstId) (k : Cont) (hM : MailInv w) (hT : CallTagInv w)
    (hidle : (w.st id).phase = .idle) (hlive : (w.st id).life = .alive)
    (hst : ∀ i, w1.st i = w.st i)
    (hpark0 : (w.st id).parked = []) (hbox1 : a1.box = ms) (hpark1 : a1.parked = [])
    (hprio1 : a1.prio = (w.st id).prio) (hlifeA : a1.life = (w.st id).life)
    (hhead : (w.st id).box = m :: ms)
    (hc : m.callFrom = some c) (hrun : a1.phase = .run k) (hshape : replyShape c k)
    (hother : ∀ c', c' ≠ c → ¬handlerOwes c' a1.phase ∧ ¬replyPending c' a1.phase)
    (howeA : a1.oweId = some (if c = id then (w.st id).waitId else (w.st c).waitId)) :
    CallTagInv (setActor w1 id a1) := by
  have hzero : countCall ms c = 0 := by
    have hs := hT.sole id c
    unfold soleCall at hs
    rw [hhead, hpark0, count_some m ms c hc] at hs
    omega
  have hne : c ≠ id := by
    intro heq
    rcases hT.msgOwner id c (Or.inl ⟨m, by simp [hhead], hc⟩) with ⟨_, hk⟩ | ⟨_, hk⟩
    · simp [heq, hidle] at hk
    · simp [heq, hidle] at hk
  have hkw : ∃ kw, (w.st c).phase = .awaitReply id kw := by
    rcases hT.msgOwner id c (Or.inl ⟨m, by simp [hhead], hc⟩) with ⟨kw, hk⟩ | ⟨kw, hk⟩
    · exact ⟨kw, hk⟩
    · rcases hT.parkedOnly c id kw hk with ⟨_, ⟨_, hp, _, _⟩, hbox⟩ | ⟨_, _, hbox⟩
      · exact False.elim (hbox ⟨m, by simp [hhead], hc⟩)
      · exact False.elim (hbox ⟨m, by simp [hhead], hc⟩)
  obtain ⟨kw, hkw⟩ := hkw
  have hduty : handlerOwes c a1.phase ∨ replyPending c a1.phase := by
    cases hrest : k.rest with
    | nil =>
      have hc1 := hshape.2.1
      simp [replyCount, hrest] at hc1
    | cons e es =>
      by_cases he : e = .reply
      · exact Or.inr ⟨k, by simp [carriedCont, hrun], hshape, by simp [nextIsReply, hrest, he]⟩
      · exact Or.inl ⟨k, by simp [carriedCont, hrun], hshape, by
          cases e <;> simp [nextIsReply, hrest] at he ⊢⟩
  let w' := setActor w1 id a1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold : (w.st c0).phase = .awaitReply d0 k0 := by
      simpa [w', setActor, hc0, hst] using hph
    by_cases hd : d0 = id
    · have hpre := hT.awaiting c0 id k0 (by simpa [hd] using hold)
      have holdD : ¬(handlerOwes c0 (w.st id).phase ∨ replyPending c0 (w.st id).phase) := by
        simp [handlerOwes, replyPending, carriedCont, hidle]
      have hmail0 : mailCall w id c0 := by
        rcases hpre with h1 | h2 | h3 | h4
        · exact h1.1
        · exact absurd (Or.inl h2.2.1) holdD
        · exact absurd (Or.inr h3.2.2) holdD
        · rw [hlive] at h4
          unfold Halted at h4
          cases h4.1
      by_cases hsame : c0 = c
      · rw [hsame, hd]
        have hnom : ¬mailCall w' id c := by
          intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, _⟩
          · have hx' : x ∈ ms := by
              simp only [w', setActor, if_true] at hx
              rw [hbox1] at hx
              exact hx
            exact count_zero_mem ms c hzero x hx' hcf
          · simp only [w', setActor, if_true] at hp
            simp [hpark1] at hp
        rcases hduty with ho | hp
        · exact Or.inr (Or.inl ⟨hnom,
            by simpa [w', setActor] using ho,
            by simpa [w', setActor] using handlerOwes_not_pending c a1.phase ho⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hnom,
            fun ho' => by
              have hnot := handlerOwes_not_pending c a1.phase (by simpa [w', setActor] using ho')
              exact hnot (by simpa [w', setActor] using hp),
            by simpa [w', setActor] using hp⟩))
      · have hmem : ∃ x, x ∈ ms ∧ x.callFrom = some c0 := by
          rcases hmail0 with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
          · rw [hhead] at hx
            cases hx with
            | head =>
              simp [hc] at hcf
              exact False.elim (hsame hcf.symm)
            | tail _ ht => exact ⟨x, ht, hcf⟩
          · simp [hpark0] at hp
        obtain ⟨x, hx, hcfx⟩ := hmem
        exact Or.inl ⟨Or.inl ⟨x, by simp [w', setActor, hd, hbox1, hx], hcfx⟩,
          by simpa [w', setActor, hd] using (hother c0 hsame).1,
          by simpa [w', setActor, hd] using (hother c0 hsame).2⟩
    · have hpre := hT.awaiting c0 d0 k0 hold
      have hmail : mailCall w' d0 c0 ↔ mailCall w d0 c0 := by
        constructor
        · intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
          · exact Or.inl ⟨x, by simpa [w', setActor, hd, hst] using hx, hcf⟩
          · exact Or.inr ⟨p, by simpa [w', setActor, hd, hst] using hp, hcf⟩
        · intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
          · exact Or.inl ⟨x, by simp [w', setActor, hd, hst, hx], hcf⟩
          · exact Or.inr ⟨p, by simp [w', setActor, hd, hst, hp], hcf⟩
      have howe : handlerOwes c0 (w'.st d0).phase ↔ handlerOwes c0 (w.st d0).phase :=
        owes_iff_carried _ _ (by simp [w', setActor, hd, hst]) c0
      have hpend : replyPending c0 (w'.st d0).phase ↔ replyPending c0 (w.st d0).phase :=
        pending_iff_carried _ _ (by simp [w', setActor, hd, hst]) c0
      rcases hpre with h1 | h2 | h3 | h4
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
          hpend.mpr h3.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w w' c0 d0
          (by simp [w', setActor, hd, hst]) (by simp [w', setActor, hc0, hst]) hmail howe hpend h4)))
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold := by simpa [w', setActor, hc0, hst] using hph
    have hpre := hT.parkedCall c0 d0 k0 hold
    have hd0 : d0 ≠ id := by
      intro heq
      rw [heq] at hpre
      rcases hpre with ⟨_, _, _, _⟩ | ⟨hl, _, _, _⟩
      · rcases hT.parkedOnly c0 id k0 (by simpa [heq] using hold) with ⟨_, ⟨_, hp, _, _⟩, _⟩ | ⟨hdead, _, _⟩
        · simp [hpark0] at hp
        · unfold Halted at hdead
          rw [hdead] at hlive
          cases hlive
      · unfold Halted at hl
        rw [hl] at hlive
        cases hlive
    exact (by
      rcases hpre with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
      · refine Or.inl ⟨by simpa [w', setActor, hd0, hst] using hl, ?_, ?_, ?_⟩
        · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp0, hcf⟩
          · exact Or.inl ⟨x, by simp [w', setActor, hd0, hst, hx], hcf⟩
          · exact Or.inr ⟨p, by simp [w', setActor, hd0, hst, hp0], hcf⟩
        · simpa [w', setActor, hd0, hst] using ho
        · simpa [w', setActor, hd0, hst] using hp
      · refine Or.inr ⟨by simpa [w', setActor, hd0, hst] using hl, ?_, ?_, ?_⟩
        · intro hm'
          apply hm
          rcases hm' with ⟨x, hx, hcf⟩ | ⟨p, hp0, hcf⟩
          · exact Or.inl ⟨x, by simpa [w', setActor, hd0, hst] using hx, hcf⟩
          · exact Or.inr ⟨p, by simpa [w', setActor, hd0, hst] using hp0, hcf⟩
        · simpa [w', setActor, hd0, hst] using ho
        · simpa [w', setActor, hd0, hst] using hp)
  · intro d0 c0 hm
    have hpreM : mailCall w d0 c0 := by
      by_cases hd : d0 = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, _⟩
        · have hx' : x ∈ ms := by
            simp only [w', setActor, hd, if_true] at hx
            rw [hbox1] at hx
            exact hx
          exact Or.inl ⟨x, by rw [hd, hhead]; exact List.mem_cons_of_mem _ hx', hcf⟩
        · simp only [w', setActor, hd, if_true] at hp
          simp [hpark1] at hp
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
        · exact Or.inl ⟨x, by simpa [w', setActor, hd, hst] using hx, hcf⟩
        · exact Or.inr ⟨p, by simpa [w', setActor, hd, hst] using hp, hcf⟩
    rcases hT.msgOwner d0 c0 hpreM with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
    · exact Or.inl ⟨k0, by
        have hc0 : c0 ≠ id := by
          intro heq
          simp [heq, hidle] at hk0
        simpa [w', setActor, hc0, hst] using hk0⟩
    · exact Or.inr ⟨k0, by
        have hc0 : c0 ≠ id := by
          intro heq
          simp [heq, hidle] at hk0
        simpa [w', setActor, hc0, hst] using hk0⟩
  · intro d0 c0 ho
    by_cases hd : d0 = id
    · have hc0 : c0 = c := by
        by_cases hbad : c0 = c
        · exact hbad
        · rcases ho with h | h
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).1
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).2
      exact ⟨kw, by
        rw [hc0, hd]
        simpa [w', setActor, hst, hne] using hkw⟩
    · have hpre : handlerOwes c0 (w.st d0).phase ∨ replyPending c0 (w.st d0).phase := by
        simpa [w', setActor, hd, hst] using ho
      obtain ⟨k0, hk0⟩ := hT.oweOwner d0 c0 hpre
      have hc0 : c0 ≠ id := by
        intro heq
        simp [heq, hidle] at hk0
      exact ⟨k0, by simpa [w', setActor, hc0, hst] using hk0⟩
  · intro i msg hm
    by_cases hi : i = id
    · exact hT.prioPlain id msg (by
        simp only [w', setActor, hi, if_true] at hm
        simpa [hprio1] using hm)
    · exact hT.prioPlain i msg (by simpa [w', setActor, hi, hst] using hm)
  · intro d0 c0
    by_cases hd : d0 = id
    · by_cases hsame : c0 = c
      · unfold soleCall
        simp [w', setActor, hd, hbox1, hpark1, countParkedCall, hsame, hzero]
      · have hs := hT.sole id c0
        unfold soleCall at hs
        rw [hhead, hpark0] at hs
        have hdrop : countCall (m :: ms) c0 = countCall ms c0 := by
          have hne0 : m.callFrom ≠ some c0 := by
            intro hbad
            simp [hc] at hbad
            exact hsame hbad.symm
          simp [countCall, hne0]
        rw [hdrop] at hs
        simpa [soleCall, w', setActor, hd, hbox1, hpark1] using hs
    · simpa [soleCall, w', setActor, hd, hst] using hT.sole d0 c0
  · intro d p hp s
    exact parkFrom_transport w w' hT
      (fun i => by
        by_cases hi : i = id
        · simp [w', setActor, hi, hpark1, hpark0]
        · simp [w', setActor, hi, hst])
      (fun s d _ => ⟨
        fun h => by
          by_cases hs : s = id
          · simp [w', setActor, hs, hrun] at h
          · simpa [w', setActor, hs, hst] using h,
        fun h => by
          by_cases hs : s = id
          · simp [hidle, hs] at h
          · simpa [w', setActor, hs, hst] using h⟩)
      d p hp s
  · intro c0 d kP hk
    exact parkedOnly_transport w w' hT
      (fun i => by
        by_cases hi : i = id
        · simp [w', setActor, hi, hpark1, hpark0]
        · simp [w', setActor, hi, hst])
      (fun i msg hm => by
        by_cases hi : i = id
        · have hm' : msg ∈ ms := by
            simp only [w', setActor, hi, if_true] at hm
            rw [hbox1] at hm
            exact hm
          rw [hi, hhead]
          exact List.mem_cons_of_mem _ hm'
        · simpa [w', setActor, hi, hst] using hm)
      (fun c0 d _ h => by
        by_cases hc0 : c0 = id
        · simp [w', setActor, hc0, hrun] at h
        · simpa [w', setActor, hc0, hst] using h)
      c0 d kP hk
      (life_set_st w w1 id a1 hst hlifeA)
  · intro d0 c0 ho
    by_cases hd : d0 = id
    · have hc0 : c0 = c := by
        by_cases hbad : c0 = c
        · exact hbad
        · rcases ho with h | h
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).1
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).2
      rw [hd, hc0]
      simp [w', setActor, howeA, hne, hst]
    · by_cases hc0 : c0 = id
      · rw [hc0] at ho
        have hpre : handlerOwes id (w.st d0).phase ∨ replyPending id (w.st d0).phase := by
          simpa [w', setActor, hd, hst] using ho
        obtain ⟨k0, hk0⟩ := hT.oweOwner d0 id hpre
        simp [hidle] at hk0
      · have hpre : handlerOwes c0 (w.st d0).phase ∨ replyPending c0 (w.st d0).phase := by
          simpa [w', setActor, hd, hst] using ho
        simpa [w', setActor, hd, hc0, hst] using hT.owedId d0 c0 hpre

/-- An idle actor whose parked list is empty dequeues one bulk head. -/
theorem bulk_box (I : Impl) (hL : LocalOk I) (w w1 : World) (id : InstId) (m : Msg)
    (ms : List Msg) (a1 : Actor) (hM : MailInv w) (hT : CallTagInv w)
    (hidle : (w.st id).phase = .idle) (hpark0 : (w.st id).parked = [])
    (hhead : (w.st id).box = m :: ms)
    (hdel : deliver I w id { (w.st id) with box := ms } m = some (w1, a1)) :
    CallTagInv (creditSender (setActor w1 id a1) (tname id) m.sender) := by
  have hst : ∀ i, w1.st i = w.st i := fun i =>
    deliver_st I w id ({ (w.st id) with box := ms }) m w1 a1 i hdel
  cases hc : m.callFrom with
  | none =>
    have hplain := deliver_plain I w id ({ (w.st id) with box := ms }) m w1 a1 hdel hc
    have hI := install_plain w w1 id a1 m ms hT hidle hst hpark0
      (by simpa using hplain.1) (by simpa [hpark0] using hplain.2.1) (by simpa using hplain.2.2.1)
      (by simpa using (deliver_life I w id ({ (w.st id) with box := ms }) m w1 a1 hdel).1)
      hplain.2.2.2 hhead hc
    exact credit_tag (setActor w1 id a1) (tname id) m.sender hI
  | some c =>
    have hcall := deliver_call I hL w id ({ (w.st id) with box := ms }) m w1 a1 c hdel hc
    obtain ⟨k, hrun, hshape, _, hother⟩ := hcall.2.2.2.2.2
    have hlive : (w.st id).life = .alive := by
      unfold deliver at hdel
      by_cases hl : (w.st id).life = .alive
      · exact hl
      · simp [hl] at hdel
    have hI := install_call w w1 id a1 m ms c k hM hT hidle hlive hst hpark0
      (by simpa using hcall.1) (by simpa [hpark0] using hcall.2.1) (by simpa using hcall.2.2.1)
      (by simpa using (deliver_life I w id ({ (w.st id) with box := ms }) m w1 a1 hdel).1)
      hhead hc hrun hshape hother (by simpa using hcall.2.2.2.2.1)
    exact credit_tag (setActor w1 id a1) (tname id) m.sender hI

theorem countParked_some (p : Parked) (ps : List Parked) (c : InstId)
    (h : p.msg.callFrom = some c) :
    countParkedCall (p :: ps) c = countParkedCall ps c + 1 := by
  simp [countParkedCall, h, Nat.add_comm]

/-- Drop a non-call parked head and install a plain delivery. The sender is not moved. -/
theorem install_parked_plain (w w1 : World) (id : InstId) (a1 : Actor) (p : Parked)
    (ps : List Parked) (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hbox0 : (w.st id).box = [])
    (hpark : (w.st id).parked = p :: ps) (hbox1 : a1.box = (w.st id).box)
    (hpark1 : a1.parked = ps) (hprio1 : a1.prio = (w.st id).prio)
    (hlifeA : a1.life = (w.st id).life)
    (hph : a1.phase = .idle ∨ ∃ k, a1.phase = .run k ∧ k.replyTo = none)
    (hc : p.msg.callFrom = none) : CallTagInv (setActor w1 id a1) := by
  have hcarry : ∀ c : InstId, carriedCont a1.phase = none ∨
      ∃ k, carriedCont a1.phase = some k ∧ k.replyTo = none := by
    intro _
    rcases hph with hI | ⟨k, hk, hto⟩
    · exact Or.inl (by simp [carriedCont, hI])
    · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩
  apply call_tag_stable w (setActor w1 id a1) hT
  · intro d c
    constructor
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · have hx' : x ∈ a1.box := by
            simp only [setActor, hd, hst, ite_true] at hx
            exact hx
          exact Or.inl ⟨x, by rw [hd]; rw [hbox1] at hx'; exact hx', hcf⟩
        · have hq' : q ∈ ps := by
            simp only [setActor, hd, hst, ite_true] at hq
            rw [hpark1] at hq
            exact hq
          exact Or.inr ⟨q, by rw [hd, hpark]; exact List.mem_cons_of_mem _ hq', hcf⟩
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simpa [setActor, hd, hst] using hx, hcf⟩
        · exact Or.inr ⟨q, by simpa [setActor, hd, hst] using hq, hcf⟩
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by
            simp only [setActor, hd, hst, ite_true]
            rw [hd, ← hbox1] at hx
            exact hx, hcf⟩
        · have hq' : q ∈ ps := by
            rw [hd, hpark] at hq
            cases hq with
            | head => simp [hc] at hcf
            | tail _ ht => exact ht
          exact Or.inr ⟨q, by
            simp only [setActor, hd, hst, ite_true]
            rw [hpark1]
            exact hq', hcf⟩
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [setActor, hd, hst, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [setActor, hd, hst, hq], hcf⟩
  · intro i c
    by_cases hi : i = id
    · have hold : ¬handlerOwes c (w.st id).phase := by simp [handlerOwes, carriedCont, hidle]
      have hnew : ¬handlerOwes c a1.phase := (plain_no_owe a1.phase c (hcarry c)).1
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact owes_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro i c
    by_cases hi : i = id
    · have hold : ¬replyPending c (w.st id).phase := by simp [replyPending, carriedCont, hidle]
      have hnew : ¬replyPending c a1.phase := (plain_no_owe a1.phase c (hcarry c)).2
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact pending_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro i msg hm
    by_cases hi : i = id
    · exact hT.prioPlain id msg (by
        simp only [setActor, hi, hst, ite_true] at hm
        simpa [hprio1] using hm)
    · exact hT.prioPlain i msg (by simpa [setActor, hi, hst] using hm)
  · intro d c
    by_cases hd : d = id
    · have hs := hT.sole id c
      unfold soleCall at hs
      rw [hbox0, hpark] at hs
      have hdrop : countParkedCall (p :: ps) c = countParkedCall ps c := by
        simp [countParkedCall, hc]
      rw [hdrop] at hs
      unfold soleCall
      simp [setActor, hd, hst, hbox1, hpark1, hbox0]
      simpa [countCall] using hs
    · simp [soleCall, setActor, hd, hst]
      exact hT.sole d c
  · intro d q hq s
    by_cases hd : d = id
    · have hq' : q ∈ p :: ps := by
        simp only [setActor, hd, hst, ite_true] at hq
        rw [hpark1] at hq
        exact List.mem_cons_of_mem _ hq
      have hiff := hT.parkFrom id q (by simpa [hpark] using hq') s
      constructor
      · intro hc
        obtain ⟨hs, k, hk⟩ := hiff.mp hc
        have hsnd : s ≠ id := by
          intro heq
          simp [heq, hidle] at hk
        exact ⟨hs, k, by rw [hd]; simpa [setActor, hsnd, hst] using hk⟩
      · intro ⟨hs, k, hk⟩
        have hsnd : s ≠ id := by
          intro heq
          simp [setActor, heq, hst] at hk
          rcases hph with hI | ⟨_, hr, _⟩ <;>
            first | (rw [hI] at hk; cases hk) | (rw [hr] at hk; cases hk)
        have hk0 : (w.st s).phase = .parked d true k := by
          simpa [hd, setActor, hsnd, hst] using hk
        rw [hd] at hk0
        exact hiff.mpr ⟨hs, k, hk0⟩
    · have hiff := hT.parkFrom d q (by simpa [setActor, hd, hst] using hq) s
      constructor
      · intro hc
        obtain ⟨hs, k, hk⟩ := hiff.mp hc
        have hsnd : s ≠ id := by intro heq; simp [heq, hidle] at hk
        exact ⟨hs, k, by simpa [setActor, hsnd, hst] using hk⟩
      · intro ⟨hs, k, hk⟩
        have hsnd : s ≠ id := by
          intro heq
          simp [setActor, heq, hst] at hk
          rcases hph with hI | ⟨_, hr, _⟩ <;>
            first | (rw [hI] at hk; cases hk) | (rw [hr] at hk; cases hk)
        exact hiff.mpr ⟨hs, k, by simpa [setActor, hsnd, hst] using hk⟩
  · intro c d k hk
    have hc0 : c ≠ id := by
      intro heq
      simp [setActor, heq, hst] at hk
      rcases hph with hI | ⟨_, hr, _⟩ <;>
        first | (rw [hI] at hk; cases hk) | (rw [hr] at hk; cases hk)
    have hold : (w.st c).phase = .parked d true k := by simpa [setActor, hc0, hst] using hk
    exact parkedOnly_lift w (setActor w1 id a1) hT c d k hold
      (by
        by_cases hd : d = id
        · rw [hd]
          simp [setActor, hlifeA]
        · simp [setActor, hd, hst])
      (fun p hp hs hcf => by
        by_cases hd : d = id
        · rw [hd] at hp ⊢
          rw [hpark] at hp
          cases hp with
          | head => simp [hc] at hcf
          | tail _ ht =>
            simp [setActor, hst, hpark1]
            exact ht
        · simpa [setActor, hd, hst] using hp)
      (fun p hp hcf => by
        by_cases hd : d = id
        · rw [hd] at hp ⊢
          simp [setActor, hst, hpark1] at hp
          rw [hpark]
          exact List.mem_cons_of_mem _ hp
        · simpa [setActor, hd, hst] using hp)
      (fun m hm hcf => by
        by_cases hd : d = id
        · rw [hd] at hm
          simp [setActor, hst] at hm
          rw [hbox1, hbox0] at hm
          cases hm
        · simpa [setActor, hd, hst] using hm)
  · exact life_set_st w w1 id a1 hst hlifeA
  · exact owed_quiet_set w w1 id a1 hT hst hidle (fun c0 => plain_no_owe _ c0 (hcarry c0))

/-- Resuming a parked send runs its continuation and does not move a call tag. -/
theorem resume_send_tag (w : World) (s id : InstId) (kS : Cont) (hT : CallTagInv w)
    (hph : (w.st s).phase = .parked id false kS) :
    CallTagInv (setActor w s (resumeSender (w.st s) false id)) := by
  have hres : resumeSender (w.st s) false id = proceed (w.st s) kS := by
    simp [resumeSender, hph]
  rw [hres]
  let w' := setActor w s (proceed (w.st s) kS)
  apply call_tag_stable w w' hT
  · intro d c
    exact mail_iff_lists w w' (fun i => by
      by_cases hi : i = s <;> simp [w', setActor, hi, proceed_fields])
      (fun i => by
        by_cases hi : i = s <;> simp [w', setActor, hi, (proceed_fields _ kS).2.1]) d c
  · intro i c
    by_cases hi : i = s
    · rw [hi]
      cases hk : kS.rest with
      | nil =>
        constructor
        · intro h
          simp [w', setActor, proceed, hk, handlerOwes, carriedCont, replyCount] at h
        · intro h
          simp [handlerOwes, replyShape, carriedCont, hph, hk, replyCount] at h
      | cons _ _ =>
        have hcar := proceed_carriedCont (w.st s) kS (by simp [hk])
        have hold : carriedCont (w.st s).phase = some kS := by simp [carriedCont, hph]
        exact owes_iff_carried _ _ (by simp [w', setActor, hcar, hold]) c
    · exact owes_iff_carried _ _ (by simp [w', setActor, hi]) c
  · intro i c
    by_cases hi : i = s
    · rw [hi]
      cases hk : kS.rest with
      | nil =>
        constructor
        · intro h
          simp [w', setActor, proceed, hk, replyPending, carriedCont] at h
        · intro h
          simp [replyPending, replyShape, carriedCont, hph, hk, replyCount] at h
      | cons _ _ =>
        have hcar := proceed_carriedCont (w.st s) kS (by simp [hk])
        have hold : carriedCont (w.st s).phase = some kS := by simp [carriedCont, hph]
        exact pending_iff_carried _ _ (by simp [w', setActor, hcar, hold]) c
    · exact pending_iff_carried _ _ (by simp [w', setActor, hi]) c
  · intro c d kA hph'
    by_cases hc : c = s
    · simp [w', setActor, hc, proceed] at hph'
      cases hk : kS.rest <;> simp [hk, hph] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = s
    · simp [hph, hc] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = s
    · simp [w', setActor, hc, proceed] at hph'
      cases hk : kS.rest <;> simp [hk] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = s
    · simp [hph, hc] at hph'
    · simpa [w', setActor, hc] using hph'
  · intro i m hm
    by_cases hi : i = s
    · have hmem : m ∈ (w.st s).prio := by
        have hp := (proceed_fields (w.st s) kS).2.2.1
        simp [w', setActor, hi] at hm
        rwa [hp] at hm
      exact hT.prioPlain s m hmem
    · exact hT.prioPlain i m (by simpa [w', setActor, hi] using hm)
  · intro d c
    by_cases hd : d = s
    · have hbox : (w'.st d).box = (w.st d).box := by
        simp [w', setActor, hd, proceed_fields]
      have hparkL : (w'.st d).parked = (w.st d).parked := by
        simp [w', setActor, hd, (proceed_fields _ kS).2.1]
      simpa [soleCall, hbox, hparkL] using hT.sole d c
    · simpa [soleCall, w', setActor, hd] using hT.sole d c
  · intro d p hp s0
    exact parkFrom_transport w w' hT
      (fun i => by
        by_cases hi : i = s <;> simp [w', setActor, hi, (proceed_fields _ kS).2.1])
      (fun s0 d kP => ⟨
        fun h => by
          by_cases hs0 : s0 = s
          · simp [w', setActor, hs0, proceed] at h
            cases hk : kS.rest <;> simp [hk] at h
          · simpa [w', setActor, hs0] using h,
        fun h => by
          by_cases hs0 : s0 = s
          · simp [hph, hs0] at h
          · simpa [w', setActor, hs0] using h⟩)
      d p hp s0
  · intro c d kP hk
    exact parkedOnly_transport w w' hT
      (fun i => by
        by_cases hi : i = s <;> simp [w', setActor, hi, (proceed_fields _ kS).2.1])
      (fun i msg hm => by
        by_cases hi : i = s
        · simpa [w', setActor, hi, (proceed_fields _ kS).1] using hm
        · simpa [w', setActor, hi] using hm)
      (fun c d _ h => by
        by_cases hc : c = s
        · simp [w', setActor, hc, proceed] at h
          cases hk : kS.rest <;> simp [hk] at h
        · simpa [w', setActor, hc] using h)
      c d kP hk
      (by simpa [w'] using life_setActor w s (proceed (w.st s) kS) (proceed_life _ _))
  · simpa [w'] using life_setActor w s (proceed (w.st s) kS) (proceed_life _ _)
  · exact owed_proceed w s kS hT (by simp [carriedCont, hph])

/-- A non-call parked head is delivered plainly and its sender is resumed. -/
theorem deliver_parked_send (I : Impl) (w w1 : World) (id : InstId) (p : Parked)
    (ps : List Parked) (a1 : Actor) (kS : Cont) (hM : MailInv w) (hT : CallTagInv w)
    (hidle : (w.st id).phase = .idle) (hbox0 : (w.st id).box = [])
    (hpark : (w.st id).parked = p :: ps) (hnc : p.isCall = false) (hc : p.msg.callFrom = none)
    (hphS : (w.st p.sender).phase = .parked id false kS)
    (hdel : deliver I w id { (w.st id) with parked := ps } p.msg = some (w1, a1)) :
    let wA := setActor w1 id a1
    let wC := creditSender wA (tname id) p.msg.sender
    CallTagInv (setActor wC p.sender (resumeSender (wC.st p.sender) false id)) := by
  have hst : ∀ i, w1.st i = w.st i := fun i =>
    deliver_st I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 i hdel
  have hplain := deliver_plain I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 hdel hc
  have hsnd : p.sender ≠ id := by
    intro heq
    simp [heq, hidle] at hphS
  have hI := install_parked_plain w w1 id a1 p ps hT hidle hst hbox0 hpark
    (by simpa [hbox0] using hplain.1) (by simpa using hplain.2.1) (by simpa using hplain.2.2.1)
    (by simpa using (deliver_life I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 hdel).1)
    hplain.2.2.2 hc
  have hC := credit_tag (setActor w1 id a1) (tname id) p.msg.sender hI
  have hphC : ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender).phase =
      .parked id false kS := by
    have hphA : ((setActor w1 id a1).st p.sender).phase = (w.st p.sender).phase := by
      simp [setActor, hsnd, hst]
    simpa [hphA, hphS] using (credit_same (setActor w1 id a1) (tname id) p.msg.sender p.sender).2.2.1
  simpa using resume_send_tag (creditSender (setActor w1 id a1) (tname id) p.msg.sender)
    p.sender id kS hC hphC

/-- Phases and mailboxes after an empty mailbox delivers a parked call head. -/
theorem deliver_parked_view (I : Impl) (w w1 : World) (id : InstId) (p : Parked)
    (ps : List Parked) (a1 : Actor) (kS : Cont)
    (hidle : (w.st id).phase = .idle)
    (hphS : (w.st p.sender).phase = .parked id true kS)
    (hdel : deliver I w id { (w.st id) with parked := ps } p.msg = some (w1, a1)) :
    let wA := setActor w1 id a1
    let wC := creditSender wA (tname id) p.msg.sender
    let w' := setActor wC p.sender (resumeSender (wC.st p.sender) true id)
    p.sender ≠ id ∧
      (w'.st id).phase = a1.phase ∧ (w'.st id).box = a1.box ∧
        (w'.st id).parked = a1.parked ∧ (w'.st id).prio = a1.prio ∧
          (w'.st p.sender).phase = .awaitReply id kS ∧
            (w'.st p.sender).box = (w.st p.sender).box ∧
              (w'.st p.sender).parked = (w.st p.sender).parked ∧
                (w'.st p.sender).prio = (w.st p.sender).prio ∧
                  ∀ i, i ≠ id → i ≠ p.sender →
                    (w'.st i).phase = (w.st i).phase ∧ (w'.st i).box = (w.st i).box ∧
                      (w'.st i).parked = (w.st i).parked ∧ (w'.st i).prio = (w.st i).prio := by
  have hst : ∀ i, w1.st i = w.st i := fun i =>
    deliver_st I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 i hdel
  have hsnd : p.sender ≠ id := by
    intro heq
    simp [heq, hidle] at hphS
  let wA := setActor w1 id a1
  let wC := creditSender wA (tname id) p.msg.sender
  let w' := setActor wC p.sender (resumeSender (wC.st p.sender) true id)
  have hcred := fun i => credit_same wA (tname id) p.msg.sender i
  have hphA : (wA.st p.sender).phase = (w.st p.sender).phase := by
    simp [wA, setActor, hsnd, hst]
  have hphC : (wC.st p.sender).phase = .parked id true kS := by
    simpa [wC, hphA, hphS] using (hcred p.sender).2.2.1
  have hres : resumeSender (wC.st p.sender) true id =
      { (wC.st p.sender) with phase := .awaitReply id kS } := by
    simp [resumeSender, hphC]
  have hidN : ¬ id = p.sender := fun h => hsnd h.symm
  refine ⟨hsnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (w'.st id).phase = (wC.st id).phase := by simp [w', setActor, hidN]
    have h2 : (wC.st id).phase = (wA.st id).phase := by simpa [wC] using (hcred id).2.2.1
    have h3 : (wA.st id).phase = a1.phase := by simp [wA, setActor]
    rw [h1, h2, h3]
  · have h1 : (w'.st id).box = (wC.st id).box := by simp [w', setActor, hidN]
    have h2 : (wC.st id).box = (wA.st id).box := by simpa [wC] using (hcred id).1
    have h3 : (wA.st id).box = a1.box := by simp [wA, setActor]
    rw [h1, h2, h3]
  · have h1 : (w'.st id).parked = (wC.st id).parked := by simp [w', setActor, hidN]
    have h2 : (wC.st id).parked = (wA.st id).parked := by simpa [wC] using (hcred id).2.1
    have h3 : (wA.st id).parked = a1.parked := by simp [wA, setActor]
    rw [h1, h2, h3]
  · have h1 : (w'.st id).prio = (wC.st id).prio := by simp [w', setActor, hidN]
    have h2 : (wC.st id).prio = (wA.st id).prio := by simpa [wC] using (hcred id).2.2.2
    have h3 : (wA.st id).prio = a1.prio := by simp [wA, setActor]
    rw [h1, h2, h3]
  · show (w'.st p.sender).phase = .awaitReply id kS
    simp [w', setActor, hres]
  · have hbR : (resumeSender (wC.st p.sender) true id).box = (wC.st p.sender).box := by
      simp [hres]
    have hbC : (wC.st p.sender).box = (wA.st p.sender).box := by simpa [wC] using (hcred p.sender).1
    have hbA : (wA.st p.sender).box = (w.st p.sender).box := by simp [wA, setActor, hsnd, hst]
    show (w'.st p.sender).box = (w.st p.sender).box
    simp [w', setActor, hbR, hbC, hbA]
  · have hpR : (resumeSender (wC.st p.sender) true id).parked = (wC.st p.sender).parked := by
      simp [hres]
    have hpC : (wC.st p.sender).parked = (wA.st p.sender).parked := by
      simpa [wC] using (hcred p.sender).2.1
    have hpA : (wA.st p.sender).parked = (w.st p.sender).parked := by simp [wA, setActor, hsnd, hst]
    show (w'.st p.sender).parked = (w.st p.sender).parked
    simp [w', setActor, hpR, hpC, hpA]
  · have hqR : (resumeSender (wC.st p.sender) true id).prio = (wC.st p.sender).prio := by
      simp [hres]
    have hqC : (wC.st p.sender).prio = (wA.st p.sender).prio := by
      simpa [wC] using (hcred p.sender).2.2.2
    have hqA : (wA.st p.sender).prio = (w.st p.sender).prio := by simp [wA, setActor, hsnd, hst]
    show (w'.st p.sender).prio = (w.st p.sender).prio
    simp [w', setActor, hqR, hqC, hqA]
  · intro i hi hs
    have h1p : (w'.st i).phase = (wC.st i).phase := by simp [w', setActor, hs]
    have h1b : (w'.st i).box = (wC.st i).box := by simp [w', setActor, hs]
    have h1k : (w'.st i).parked = (wC.st i).parked := by simp [w', setActor, hs]
    have h1q : (w'.st i).prio = (wC.st i).prio := by simp [w', setActor, hs]
    have h2p : (wC.st i).phase = (wA.st i).phase := by simpa [wC] using (hcred i).2.2.1
    have h2b : (wC.st i).box = (wA.st i).box := by simpa [wC] using (hcred i).1
    have h2k : (wC.st i).parked = (wA.st i).parked := by simpa [wC] using (hcred i).2.1
    have h2q : (wC.st i).prio = (wA.st i).prio := by simpa [wC] using (hcred i).2.2.2
    have h3p : (wA.st i).phase = (w.st i).phase := by simp [wA, setActor, hi, hst]
    have h3b : (wA.st i).box = (w.st i).box := by simp [wA, setActor, hi, hst]
    have h3k : (wA.st i).parked = (w.st i).parked := by simp [wA, setActor, hi, hst]
    have h3q : (wA.st i).prio = (w.st i).prio := by simp [wA, setActor, hi, hst]
    exact ⟨h1p.trans (h2p.trans h3p), h1b.trans (h2b.trans h3b),
      h1k.trans (h2k.trans h3k), h1q.trans (h2q.trans h3q)⟩

/-- The world after a parked call is delivered: the handler is installed, the
message sender is credited, and the parked caller is resumed into `awaitReply`. -/
def deliverPost (w1 : World) (id : InstId) (a1 : Actor) (credited resumed : InstId)
    (name : String) : World :=
  setActor (creditSender (setActor w1 id a1) name credited) resumed
    (resumeSender ((creditSender (setActor w1 id a1) name credited).st resumed) true id)

/-- Crediting and resuming leave the owed id where `deliver` put it. The resumed
caller's own owed id is unchanged, and so is everyone else's. -/
theorem deliverPost_oweId (w1 : World) (id : InstId) (a1 : Actor) (credited resumed : InstId)
    (name : String) (i : InstId) (hres : resumed ≠ id) :
    ((deliverPost w1 id a1 credited resumed name).st i).oweId =
      if i = resumed then (w1.st resumed).oweId
      else if i = id then a1.oweId
      else (w1.st i).oweId := by
  unfold deliverPost
  by_cases hs : i = resumed
  · rw [hs, setActor_self, (resume_stamps _ true id).1,
      (credit_stamps_ow (setActor w1 id a1) name credited resumed).1,
      setActor_other _ _ _ _ hres]
    simp
  · rw [setActor_other _ _ _ _ hs]
    by_cases hid : i = id
    · rw [hid, (credit_stamps_ow (setActor w1 id a1) name credited id).1, setActor_self]
      simp [hres.symm]
    · rw [(credit_stamps_ow (setActor w1 id a1) name credited i).1,
        setActor_other _ _ _ _ hid]
      simp [hs, hid]

/-- The same step leaves every wait id, except the handler's, which is the
wait id `deliver` wrote onto the installed actor. -/
theorem deliverPost_waitId (w1 : World) (id : InstId) (a1 : Actor) (credited resumed : InstId)
    (name : String) (i : InstId) (hres : resumed ≠ id) :
    ((deliverPost w1 id a1 credited resumed name).st i).waitId =
      if i = id then a1.waitId else (w1.st i).waitId := by
  unfold deliverPost
  by_cases hs : i = resumed
  · rw [hs, setActor_self, (resume_stamps _ true id).2,
      (credit_stamps_ow (setActor w1 id a1) name credited resumed).2,
      setActor_other _ _ _ _ hres]
    simp [hres]
  · rw [setActor_other _ _ _ _ hs]
    by_cases hid : i = id
    · rw [hid, (credit_stamps_ow (setActor w1 id a1) name credited id).2, setActor_self]
      simp
    · rw [(credit_stamps_ow (setActor w1 id a1) name credited i).2,
        setActor_other _ _ _ _ hid]
      simp [hid]

/-- An empty mailbox delivers a parked call: the handler is installed with
`replyTo` the sender, that sender moves to `awaitReply`, and the entry is gone.
The three are checked together. The world in which the message is already gone
and the sender is still parked is not a `CallTagInv` world. -/
theorem deliver_parked_tag (I : Impl) (hL : LocalOk I) (w w1 : World) (id : InstId)
    (p : Parked) (ps : List Parked) (a1 : Actor) (kS : Cont) (hM : MailInv w)
    (hT : CallTagInv w) (hidle : (w.st id).phase = .idle) (hbox0 : (w.st id).box = [])
    (hpark : (w.st id).parked = p :: ps) (hfrom : p.msg.callFrom = some p.sender)
    (hphS : (w.st p.sender).phase = .parked id true kS)
    (hdel : deliver I w id { (w.st id) with parked := ps } p.msg = some (w1, a1)) :
    let wA := setActor w1 id a1
    let wC := creditSender wA (tname id) p.msg.sender
    CallTagInv (setActor wC p.sender (resumeSender (wC.st p.sender) true id)) := by
  have hD := deliver_call I hL w id ({ (w.st id) with parked := ps }) p.msg w1 a1 p.sender hdel hfrom
  obtain ⟨kH, hrun, hshape, _, hother⟩ := hD.2.2.2.2.2
  have hbox1 : a1.box = [] := by simpa [hbox0] using hD.1
  have hpark1 : a1.parked = ps := by simpa using hD.2.1
  have hprio1 : a1.prio = (w.st id).prio := by simpa using hD.2.2.1
  obtain ⟨hsnd, hIdP, hIdB, hIdK, hIdQ, hSP, hSB, hSK, hSQ, hO⟩ :=
    deliver_parked_view I w w1 id p ps a1 kS hidle hphS hdel
  have hzero : countParkedCall ps p.sender = 0 := by
    have hs := hT.sole id p.sender
    unfold soleCall at hs
    rw [hbox0, hpark, countParked_some p ps p.sender hfrom] at hs
    omega
  have hduty : handlerOwes p.sender a1.phase ∨ replyPending p.sender a1.phase := by
    cases hrest : kH.rest with
    | nil =>
      have hc1 := hshape.2.1
      simp [replyCount, hrest] at hc1
    | cons e es =>
      by_cases he : e = .reply
      · exact Or.inr ⟨kH, by simp [carriedCont, hrun], hshape, by simp [nextIsReply, hrest, he]⟩
      · exact Or.inl ⟨kH, by simp [carriedCont, hrun], hshape, by
          cases e <;> simp [nextIsReply, hrest] at he ⊢⟩
  let post := setActor (creditSender (setActor w1 id a1) (tname id) p.msg.sender) p.sender
    (resumeSender ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender) true id)
  have hIdP' : (post.st id).phase = a1.phase := by simpa [post] using hIdP
  have hIdB' : (post.st id).box = a1.box := by simpa [post] using hIdB
  have hIdK' : (post.st id).parked = a1.parked := by simpa [post] using hIdK
  have hIdQ' : (post.st id).prio = a1.prio := by simpa [post] using hIdQ
  have hSP' : (post.st p.sender).phase = .awaitReply id kS := by simpa [post] using hSP
  have hSB' : (post.st p.sender).box = (w.st p.sender).box := by simpa [post] using hSB
  have hSK' : (post.st p.sender).parked = (w.st p.sender).parked := by simpa [post] using hSK
  have hSQ' : (post.st p.sender).prio = (w.st p.sender).prio := by simpa [post] using hSQ
  have hO' : ∀ i, i ≠ id → i ≠ p.sender →
      (post.st i).phase = (w.st i).phase ∧ (post.st i).box = (w.st i).box ∧
        (post.st i).parked = (w.st i).parked ∧ (post.st i).prio = (w.st i).prio := by
    intro i hi hs
    simpa [post] using hO i hi hs
  have hlifeP (i : InstId) : (post.st i).life = (w.st i).life := by
    have hL := deliver_life I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 hdel
    have hA : a1.life = (w.st id).life := by simpa using hL.1
    by_cases hs : i = p.sender
    · rw [hs]
      simp only [post]
      rw [set_resume_life]
      rw [(credit_phase_life (setActor w1 id a1) (tname id) p.msg.sender p.sender).2]
      have hsnd : p.sender ≠ id := by intro h; simp [h, hidle] at hphS
      simp [setActor, hsnd, hL.2]
    · simp only [post]
      rw [set_resume_life_other (creditSender (setActor w1 id a1) (tname id) p.msg.sender) p.sender i
        _ true id hs]
      rw [(credit_phase_life (setActor w1 id a1) (tname id) p.msg.sender i).2]
      by_cases hid : i = id
      · simp [setActor, hid, hA]
      · simp [setActor, hid, hL.2]
  have hnomS : ¬mailCall post id p.sender := by
    intro hm
    rcases hm with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
    · rw [hIdB'] at hx
      simp [hbox1] at hx
    · rw [hIdK', hpark1] at hq
      exact absurd hcf (countParked_zero_mem ps p.sender hzero q hq)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 d0 k0 hph
    by_cases hcS : c0 = p.sender
    · have hph' : (post.st p.sender).phase = .awaitReply d0 k0 := by simpa [post, hcS] using hph
      have hEq : Phase.awaitReply id kS = Phase.awaitReply d0 k0 := hSP'.symm.trans hph'
      injection hEq with hd0 hk0
      rw [hcS, ← hd0]
      rcases hduty with ho | hp
      · exact Or.inr (Or.inl ⟨hnomS, by simpa [post, ← hIdP'] using ho,
          fun hpend => handlerOwes_not_pending p.sender a1.phase ho
            (by simpa [post, hIdP'] using hpend)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hnomS,
          fun ho' => handlerOwes_not_pending p.sender a1.phase
            (by simpa [post, hIdP'] using ho') (by simpa [post] using hp),
          by simpa [post, ← hIdP'] using hp⟩))
    · by_cases hcId : c0 = id
      · have hbad : (post.st id).phase = .awaitReply d0 k0 := by simpa [post, hcId] using hph
        simp [hIdP', hrun] at hbad
      · have hold : (w.st c0).phase = .awaitReply d0 k0 := by
          have hpeq := (hO' c0 hcId hcS).1
          rw [← hpeq]
          simpa [post] using hph
        by_cases hd : d0 = id
        · have hpre := hT.awaiting c0 id k0 (by simpa [hd] using hold)
          have holdD : ¬(handlerOwes c0 (w.st id).phase ∨ replyPending c0 (w.st id).phase) := by
            simp [handlerOwes, replyPending, carriedCont, hidle]
          have hmail0 : mailCall w id c0 := by
            rcases hpre with h1 | h2 | h3 | h4
            · exact h1.1
            · exact absurd (Or.inl h2.2.1) holdD
            · exact absurd (Or.inr h3.2.2) holdD
            · have hne : (w.st id).life ≠ .alive := by
                unfold Halted at h4
                intro hl
                rw [h4.1] at hl
                cases hl
              simp [deliver, hne] at hdel
          have hmem : ∃ q, q ∈ ps ∧ q.msg.callFrom = some c0 := by
            rcases hmail0 with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
            · simp [hbox0] at hx
            · rw [hpark] at hq
              cases hq with
              | head =>
                simp [hfrom] at hcf
                exact False.elim (hcS hcf.symm)
              | tail _ ht => exact ⟨q, ht, hcf⟩
          obtain ⟨q, hq, hcf⟩ := hmem
          exact Or.inl ⟨Or.inr ⟨q, by rw [hd, hIdK', hpark1]; exact hq, hcf⟩,
            by rw [hd, hIdP']; exact (hother c0 hcS).1,
            by rw [hd, hIdP']; exact (hother c0 hcS).2⟩
        · by_cases hdS : d0 = p.sender
          · have hpre := hT.awaiting c0 p.sender k0 (by simpa [hdS] using hold)
            have hmail : mailCall post p.sender c0 ↔ mailCall w p.sender c0 := by
              constructor
              · intro hm
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [hSB'] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [hSK'] at hq; exact hq, hcf⟩
              · intro hm
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [← hSB'] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [← hSK'] at hq; exact hq, hcf⟩
            have hcar : carriedCont (post.st p.sender).phase = carriedCont (w.st p.sender).phase := by
              simp [carriedCont, hSP', hphS]
            have howe := owes_iff_carried (w.st p.sender).phase (post.st p.sender).phase hcar c0
            have hpend := pending_iff_carried (w.st p.sender).phase (post.st p.sender).phase hcar c0
            rw [hdS]
            rcases hpre with h1 | h2 | h3 | h4
            · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
            · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1,
                (not_iff hpend).mpr h2.2.2⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
                hpend.mpr h3.2.2⟩))
            · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w post c0 p.sender
                (hlifeP p.sender) (hlifeP c0) hmail howe hpend h4)))
          · have hpre := hT.awaiting c0 d0 k0 hold
            have hpeq := (hO' d0 hd hdS).1
            have hb := (hO' d0 hd hdS).2.1
            have hk := (hO' d0 hd hdS).2.2.1
            have hmail : mailCall post d0 c0 ↔ mailCall w d0 c0 := by
              constructor
              · intro hm
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [hb] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [hk] at hq; exact hq, hcf⟩
              · intro hm
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [← hb] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [← hk] at hq; exact hq, hcf⟩
            have howe := owes_iff_carried (w.st d0).phase (post.st d0).phase (by rw [hpeq]) c0
            have hpend := pending_iff_carried (w.st d0).phase (post.st d0).phase (by rw [hpeq]) c0
            rcases hpre with h1 | h2 | h3 | h4
            · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
            · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1,
                (not_iff hpend).mpr h2.2.2⟩)
            · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
                hpend.mpr h3.2.2⟩))
            · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w post c0 d0
                (hlifeP d0) (hlifeP c0) hmail howe hpend h4)))
  · intro c0 d0 k0 hph
    by_cases hcS : c0 = p.sender
    · have hbad : (post.st p.sender).phase = .parked d0 true k0 := by simpa [post, hcS] using hph
      simp [hSP'] at hbad
    · by_cases hcId : c0 = id
      · have hbad : (post.st id).phase = .parked d0 true k0 := by simpa [post, hcId] using hph
        simp [hIdP', hrun] at hbad
      · have hold : (w.st c0).phase = .parked d0 true k0 := by
          rw [← (hO' c0 hcId hcS).1]
          simpa [post] using hph
        rcases hT.parkedCall c0 d0 k0 hold with ⟨hl, hm, ho, hp⟩ | ⟨hl, hnm, ho, hp⟩
        · by_cases hd : d0 = id
          · have hmem : ∃ q, q ∈ ps ∧ q.msg.callFrom = some c0 := by
              rcases hm with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
              · rw [hd] at hx
                simp [hbox0] at hx
              · rw [hd, hpark] at hq
                cases hq with
                | head =>
                  simp [hfrom] at hcf
                  exact False.elim (hcS hcf.symm)
                | tail _ ht => exact ⟨q, ht, hcf⟩
            obtain ⟨q, hq, hcf⟩ := hmem
            exact Or.inl ⟨by rw [hlifeP]; exact hl,
              Or.inr ⟨q, by rw [hd, hIdK', hpark1]; exact hq, hcf⟩,
              by rw [hd, hIdP']; exact (hother c0 hcS).1,
              by rw [hd, hIdP']; exact (hother c0 hcS).2⟩
          · by_cases hdS : d0 = p.sender
            · subst hdS
              have hmail : mailCall post p.sender c0 := by
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [← hSB'] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [← hSK'] at hq; exact hq, hcf⟩
              have hcar : carriedCont (post.st p.sender).phase =
                  carriedCont (w.st p.sender).phase := by simp [carriedCont, hSP', hphS]
              exact Or.inl ⟨by rw [hlifeP]; exact hl, hmail,
                (not_iff (owes_iff_carried _ _ hcar c0)).mpr ho,
                (not_iff (pending_iff_carried _ _ hcar c0)).mpr hp⟩
            · have hmail : mailCall post d0 c0 := by
                rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · exact Or.inl ⟨x, by rw [← (hO' d0 hd hdS).2.1] at hx; exact hx, hcf⟩
                · exact Or.inr ⟨q, by rw [← (hO' d0 hd hdS).2.2.1] at hq; exact hq, hcf⟩
              have hpeq := (hO' d0 hd hdS).1
              exact Or.inl ⟨by rw [hlifeP]; exact hl, hmail,
                (not_iff (owes_iff_carried _ _ (by rw [hpeq]) c0)).mpr ho,
                (not_iff (pending_iff_carried _ _ (by rw [hpeq]) c0)).mpr hp⟩
        · by_cases hd : d0 = id
          · exact Or.inr ⟨by rw [hlifeP]; exact hl,
              fun hm' => by
                rcases hm' with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                · rw [hd, hIdB'] at hx
                  simp [hbox1] at hx
                · rw [hd, hIdK', hpark1] at hq
                  exact hnm (Or.inr ⟨q, by rw [hd, hpark]; exact List.mem_cons_of_mem _ hq, hcf⟩),
              by rw [hd, hIdP']; exact (hother c0 hcS).1,
              by rw [hd, hIdP']; exact (hother c0 hcS).2⟩
          · by_cases hdS : d0 = p.sender
            · subst hdS
              have hcar : carriedCont (post.st p.sender).phase =
                  carriedCont (w.st p.sender).phase := by simp [carriedCont, hSP', hphS]
              exact Or.inr ⟨by rw [hlifeP]; exact hl,
                fun hm' => hnm (by
                  rcases hm' with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                  · exact Or.inl ⟨x, by rw [hSB'] at hx; exact hx, hcf⟩
                  · exact Or.inr ⟨q, by rw [hSK'] at hq; exact hq, hcf⟩),
                (not_iff (owes_iff_carried _ _ hcar c0)).mpr ho,
                (not_iff (pending_iff_carried _ _ hcar c0)).mpr hp⟩
            · have hpeq := (hO' d0 hd hdS).1
              exact Or.inr ⟨by rw [hlifeP]; exact hl,
                fun hm' => hnm (by
                  rcases hm' with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
                  · exact Or.inl ⟨x, by rw [(hO' d0 hd hdS).2.1] at hx; exact hx, hcf⟩
                  · exact Or.inr ⟨q, by rw [(hO' d0 hd hdS).2.2.1] at hq; exact hq, hcf⟩),
                (not_iff (owes_iff_carried _ _ (by rw [hpeq]) c0)).mpr ho,
                (not_iff (pending_iff_carried _ _ (by rw [hpeq]) c0)).mpr hp⟩
  · intro d0 c0 hm
    by_cases hd : d0 = id
    · rcases hm with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
      · rw [hd, hIdB'] at hx
        simp [hbox1] at hx
      · rw [hd, hIdK', hpark1] at hq
        have hpreM : mailCall w id c0 := Or.inr ⟨q, by rw [hpark]; exact List.mem_cons_of_mem _ hq, hcf⟩
        have hc0 : c0 ≠ p.sender := by
          intro heq
          exact absurd (by simpa [heq] using hcf) (countParked_zero_mem ps p.sender hzero q hq)
        rcases hT.msgOwner id c0 hpreM with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
        · have hc0id : c0 ≠ id := by
            intro heq
            simp [heq, hidle] at hk0
          exact Or.inl ⟨k0, by rw [(hO' c0 hc0id hc0).1]; simpa [hd] using hk0⟩
        · have hc0id : c0 ≠ id := by
            intro heq
            simp [heq, hidle] at hk0
          exact Or.inr ⟨k0, by rw [(hO' c0 hc0id hc0).1]; simpa [hd] using hk0⟩
    · by_cases hdS : d0 = p.sender
      · have hpreM : mailCall w p.sender c0 := by
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨x, by rw [hdS] at hx; rw [hSB'] at hx; exact hx, hcf⟩
          · exact Or.inr ⟨q, by rw [hdS] at hq; rw [hSK'] at hq; exact hq, hcf⟩
        rcases hT.msgOwner p.sender c0 hpreM with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
        · have hc0 : c0 ≠ p.sender := by
            intro heq
            rw [heq, hphS] at hk0
            cases hk0
          have hc0id : c0 ≠ id := by
            intro heq
            simp [heq, hidle] at hk0
          rw [hdS]
          exact Or.inl ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
        · have hc0 : c0 ≠ p.sender := by
            intro heq
            rw [heq, hphS] at hk0
            injection hk0 with hdid _ _
            exact hsnd (by first | exact (hdid.trans hdS).symm | exact (hdid.symm.trans hdS) | exact hdid.symm)
          have hc0id : c0 ≠ id := by
            intro heq
            simp [heq, hidle] at hk0
          rw [hdS]
          exact Or.inr ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
      · have hpreM : mailCall w d0 c0 := by
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨x, by rw [(hO' d0 hd hdS).2.1] at hx; exact hx, hcf⟩
          · exact Or.inr ⟨q, by rw [(hO' d0 hd hdS).2.2.1] at hq; exact hq, hcf⟩
        rcases hT.msgOwner d0 c0 hpreM with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
        · by_cases hc0 : c0 = p.sender
          · rw [hc0, hphS] at hk0
            cases hk0
          · by_cases hc0id : c0 = id
            · simp [hc0id, hidle] at hk0
            · exact Or.inl ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
        · by_cases hc0 : c0 = p.sender
          · rw [hc0, hphS] at hk0
            injection hk0 with hdid _ _
            exact False.elim (hd hdid.symm)
          · by_cases hc0id : c0 = id
            · simp [hc0id, hidle] at hk0
            · exact Or.inr ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
  · intro d0 c0 ho
    by_cases hd : d0 = id
    · have hc0 : c0 = p.sender := by
        by_cases hbad : c0 = p.sender
        · exact hbad
        · rcases ho with h | h
          · exact absurd (by rw [hd] at h; rw [hIdP'] at h; exact h) (hother c0 hbad).1
          · exact absurd (by rw [hd] at h; rw [hIdP'] at h; exact h) (hother c0 hbad).2
      exact ⟨kS, by rw [hc0]; simpa [hd] using hSP'⟩
    · by_cases hdS : d0 = p.sender
      · have hcar : carriedCont (post.st p.sender).phase = carriedCont (w.st p.sender).phase := by
          simp [carriedCont, hSP', hphS]
        obtain ⟨k0, hk0⟩ := hT.oweOwner p.sender c0 (by
          rcases ho with h | h
          · exact Or.inl ((owes_iff_carried _ _ hcar c0).mp (by simpa [hdS] using h))
          · exact Or.inr ((pending_iff_carried _ _ hcar c0).mp (by simpa [hdS] using h)))
        have hc0 : c0 ≠ p.sender := by
          intro heq
          simp [heq, hphS] at hk0
        have hc0id : c0 ≠ id := by
          intro heq
          simp [heq, hidle] at hk0
        rw [hdS]
        exact ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
      · obtain ⟨k0, hk0⟩ := hT.oweOwner d0 c0 (by
          have hpeq := (hO' d0 hd hdS).1
          rcases ho with h | h
          · exact Or.inl ((owes_iff_carried _ _ (by rw [hpeq]) c0).mp h)
          · exact Or.inr ((pending_iff_carried _ _ (by rw [hpeq]) c0).mp h))
        by_cases hc0 : c0 = p.sender
        · simp [hc0, hphS] at hk0
        · by_cases hc0id : c0 = id
          · simp [hc0id, hidle] at hk0
          · exact ⟨k0, by rw [(hO' c0 hc0id hc0).1]; exact hk0⟩
  · intro i m hm
    by_cases hi : i = id
    · rw [hi, hIdQ'] at hm
      exact hT.prioPlain id m (by simpa [hprio1] using hm)
    · by_cases hs : i = p.sender
      · rw [hs, hSQ'] at hm
        exact hT.prioPlain p.sender m hm
      · rw [(hO' i hi hs).2.2.2] at hm
        exact hT.prioPlain i m hm
  · intro d0 c0
    by_cases hd : d0 = id
    · by_cases hs : c0 = p.sender
      · unfold soleCall
        rw [hd, hIdB', hIdK', hbox1, hpark1, hs, hzero]
        simp [countCall, countParkedCall]
      · have hold := hT.sole id c0
        unfold soleCall at hold ⊢
        rw [hd, hIdB', hIdK', hbox1, hpark1]
        rw [hbox0, hpark] at hold
        have hdrop : countParkedCall (p :: ps) c0 = countParkedCall ps c0 := by
          have hne : p.msg.callFrom ≠ some c0 := by
            intro hbad
            simp [hfrom] at hbad
            exact hs hbad.symm
          simp [countParkedCall, hne]
        rw [hdrop] at hold
        simpa [countCall] using hold
    · by_cases hs : d0 = p.sender
      · unfold soleCall
        rw [hs, hSB', hSK']
        exact hT.sole p.sender c0
      · unfold soleCall
        rw [(hO' d0 hd hs).2.1, (hO' d0 hd hs).2.2.1]
        exact hT.sole d0 c0
  · intro d q hq s
    by_cases hsid : s = id
    · constructor
      · intro hc
        have hq0 : q ∈ (w.st d).parked := by
          by_cases hd : d = id
          · have hq' : q ∈ ps := by
              have hmem : q ∈ (post.st id).parked := by simpa [post, hd] using hq
              rw [hIdK', hpark1] at hmem
              exact hmem
            rw [hd, hpark]
            exact List.mem_cons_of_mem _ hq'
          · by_cases hdS : d = p.sender
            · have hmem : q ∈ (post.st p.sender).parked := by simpa [post, hdS] using hq
              rw [hSK'] at hmem
              rw [hdS]
              exact hmem
            · have hmem : q ∈ (post.st d).parked := by simpa [post] using hq
              rw [(hO' d hd hdS).2.2.1] at hmem
              exact hmem
        obtain ⟨_, _, hk⟩ := (hT.parkFrom d q hq0 s).mp hc
        simp [hsid, hidle] at hk
      · intro ⟨_, _, hk⟩
        rw [hsid, hIdP', hrun] at hk
        cases hk
    · by_cases hsS : s = p.sender
      · constructor
        · intro hc
          have hq0 : q ∈ (w.st d).parked := by
            by_cases hd : d = id
            · have hq' : q ∈ ps := by
                have hmem : q ∈ (post.st id).parked := by simpa [post, hd] using hq
                rw [hIdK', hpark1] at hmem
                exact hmem
              rw [hd, hpark]
              exact List.mem_cons_of_mem _ hq'
            · by_cases hdS : d = p.sender
              · have hmem : q ∈ (post.st p.sender).parked := by simpa [post, hdS] using hq
                rw [hSK'] at hmem
                rw [hdS]
                exact hmem
              · have hmem : q ∈ (post.st d).parked := by simpa [post] using hq
                rw [(hO' d hd hdS).2.2.1] at hmem
                exact hmem
          obtain ⟨hseq, _, _⟩ := (hT.parkFrom d q hq0 s).mp hc
          have hsame := hM.uniq d id q p hq0 (by rw [hpark]; exact List.Mem.head _)
            (hseq.trans hsS)
          have hqP : q ∈ ps := by
            have hmem : q ∈ (post.st id).parked := by
              rw [← hsame.1]
              simpa [post] using hq
            rw [hIdK', hpark1] at hmem
            exact hmem
          have hnd := hM.once id
          rw [hpark] at hnd
          exact False.elim ((List.nodup_cons.mp hnd).1 (by simpa [hsame.2] using hqP))
        · intro ⟨_, _, hk⟩
          rw [hsS, hSP'] at hk
          cases hk
      · have hphEq : (post.st s).phase = (w.st s).phase := (hO' s hsid hsS).1
        have hq0 : q ∈ (w.st d).parked := by
          by_cases hd : d = id
          · have hq' : q ∈ ps := by
              have hmem : q ∈ (post.st id).parked := by simpa [post, hd] using hq
              rw [hIdK', hpark1] at hmem
              exact hmem
            rw [hd, hpark]
            exact List.mem_cons_of_mem _ hq'
          · by_cases hdS : d = p.sender
            · have hmem : q ∈ (post.st p.sender).parked := by simpa [post, hdS] using hq
              rw [hSK'] at hmem
              rw [hdS]
              exact hmem
            · have hmem : q ∈ (post.st d).parked := by simpa [post] using hq
              rw [(hO' d hd hdS).2.2.1] at hmem
              exact hmem
        have hiff := hT.parkFrom d q hq0 s
        constructor
        · intro hc
          obtain ⟨hs, k, hk⟩ := hiff.mp hc
          exact ⟨hs, k, by rw [hphEq]; exact hk⟩
        · intro ⟨hs, k, hk⟩
          exact hiff.mpr ⟨hs, k, by rw [← hphEq]; exact hk⟩
  · intro c d k hk
    have hcS : c ≠ p.sender := by
      intro heq
      rw [heq, hSP'] at hk
      cases hk
    have hcId : c ≠ id := by
      intro heq
      rw [heq, hIdP', hrun] at hk
      cases hk
    have hold : (w.st c).phase = .parked d true k := by
      rw [(hO' c hcId hcS).1] at hk
      exact hk
    rcases hT.parkedOnly c d k hold with ⟨hl, ⟨q, hq, hsend, hcf⟩, hboxN⟩ | ⟨hl, hnoP, hboxN⟩
    · refine Or.inl ⟨by rw [hlifeP]; exact hl, ?_, ?_⟩
      · by_cases hd : d = id
        · rw [hd, hpark] at hq
          cases hq with
          | head => exact False.elim (hcS hsend.symm)
          | tail _ ht =>
            have heq : (post.st d).parked = ps := by rw [hd, hIdK', hpark1]
            exact ⟨q, heq ▸ ht, hsend, hcf⟩
        · by_cases hdS : d = p.sender
          · exact ⟨q, by simpa [post, hdS, hSK'] using hq, hsend, hcf⟩
          · exact ⟨q, by simpa [post, (hO' d hd hdS).2.2.1] using hq, hsend, hcf⟩
      · intro ⟨msg, hm, hcfM⟩
        exact hboxN ⟨msg, by
          by_cases hd : d = id
          · have hm' : msg ∈ (post.st id).box := by simpa [post, hd] using hm
            rw [hIdB', hbox1] at hm'
            cases hm'
          · by_cases hdS : d = p.sender
            · have hm' : msg ∈ (post.st p.sender).box := by simpa [post, hdS] using hm
              rw [hSB'] at hm'
              rw [hdS]
              exact hm'
            · have hm' : msg ∈ (post.st d).box := by simpa [post] using hm
              rw [(hO' d hd hdS).2.1] at hm'
              exact hm', hcfM⟩
    · refine Or.inr ⟨by rw [hlifeP]; exact hl, ?_, ?_⟩
      · intro ⟨q, hq, hcf⟩
        by_cases hd : d = id
        · have hq' : q ∈ ps := by
            have hmem : q ∈ (post.st id).parked := by simpa [post, hd] using hq
            rw [hIdK', hpark1] at hmem
            exact hmem
          exact hnoP ⟨q, by rw [hd, hpark]; exact List.mem_cons_of_mem _ hq', hcf⟩
        · by_cases hdS : d = p.sender
          · exact hnoP ⟨q, by
              have hmem : q ∈ (post.st p.sender).parked := by simpa [post, hdS] using hq
              rw [hSK'] at hmem
              rw [hdS]
              exact hmem, hcf⟩
          · exact hnoP ⟨q, by
              have hmem : q ∈ (post.st d).parked := by simpa [post] using hq
              rw [(hO' d hd hdS).2.2.1] at hmem
              exact hmem, hcf⟩
      · intro ⟨msg, hm, hcfM⟩
        exact hboxN ⟨msg, by
          by_cases hd : d = id
          · have hm' : msg ∈ (post.st id).box := by simpa [post, hd] using hm
            rw [hIdB', hbox1] at hm'
            cases hm'
          · by_cases hdS : d = p.sender
            · have hm' : msg ∈ (post.st p.sender).box := by simpa [post, hdS] using hm
              rw [hSB'] at hm'
              rw [hdS]
              exact hm'
            · have hm' : msg ∈ (post.st d).box := by simpa [post] using hm
              rw [(hO' d hd hdS).2.1] at hm'
              exact hm', hcfM⟩
  · intro d c ho
    have hsnd : p.sender ≠ id := by intro h; simp [h, hidle] at hphS
    have howeA : a1.oweId = some (w.st p.sender).waitId := by
      simpa [show ¬p.sender = id from hsnd] using hD.2.2.2.2.1
    have hwaitA : a1.waitId = (w.st id).waitId := by simpa using hD.2.2.2.1
    have hst1 (i : InstId) : w1.st i = w.st i :=
      deliver_st I w id ({ (w.st id) with parked := ps }) p.msg w1 a1 i hdel
    have howeI := deliverPost_oweId w1 id a1 p.msg.sender p.sender (tname id)
    have hwaitI := deliverPost_waitId w1 id a1 p.msg.sender p.sender (tname id)
    unfold deliverPost at howeI hwaitI
    by_cases hd : d = id
    · have hc : c = p.sender := by
        by_cases hbad : c = p.sender
        · exact hbad
        · rcases ho with h | h
          · have hh : handlerOwes c (post.st id).phase := by simpa [post, hd] using h
            rw [hIdP'] at hh
            exact False.elim ((hother c hbad).1 hh)
          · have hh : replyPending c (post.st id).phase := by simpa [post, hd] using h
            rw [hIdP'] at hh
            exact False.elim ((hother c hbad).2 hh)
      rw [hd, hc, howeI id hsnd, hwaitI p.sender hsnd]
      simp [hsnd, hsnd.symm, howeA, hst1 p.sender]
    · by_cases hdS : d = p.sender
      · rw [hdS] at ho ⊢
        have hcarN : carriedCont (post.st p.sender).phase = some kS := by simp [carriedCont, hSP']
        have hcarO : carriedCont (w.st p.sender).phase = some kS := by simp [carriedCont, hphS]
        have hpre : handlerOwes c (w.st p.sender).phase ∨ replyPending c (w.st p.sender).phase := by
          rcases ho with h | h
          · exact Or.inl ((owes_iff_carried _ _ (hcarN.trans hcarO.symm) c).mp h)
          · exact Or.inr ((pending_iff_carried _ _ (hcarN.trans hcarO.symm) c).mp h)
        rw [howeI p.sender hsnd, hwaitI c hsnd]
        by_cases hc : c = id
        · simp [hsnd, hc, hst1 p.sender, hwaitA, hT.owedId p.sender c hpre]
        · simp [hsnd, hc, hst1 p.sender, hst1 c, hT.owedId p.sender c hpre]
      · have hdS' : d ≠ p.sender := fun h => hdS h
        have hd' : d ≠ id := fun h => hd h
        have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          have hphD : (post.st d).phase = (w.st d).phase := (hO' d hd hdS).1
          rcases ho with h | h
          · exact Or.inl (by
              have hh : handlerOwes c (post.st d).phase := by simpa [post, hd, hdS] using h
              rwa [hphD] at hh)
          · exact Or.inr (by
              have hh : replyPending c (post.st d).phase := by simpa [post, hd, hdS] using h
              rwa [hphD] at hh)
        rw [howeI d hsnd, hwaitI c hsnd]
        by_cases hc : c = id
        · simp [hdS', hd', hc, hst1 d, hwaitA, hT.owedId d c hpre]
        · simp [hdS', hd', hc, hst1 d, hst1 c, hT.owedId d c hpre]

/-- Deliver a non-call box head and leave the parked list where it is. -/
theorem install_plain_kept (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hbox1 : a1.box = ms)
    (hpark1 : a1.parked = (w.st id).parked) (hprio1 : a1.prio = (w.st id).prio)
    (hlifeA : a1.life = (w.st id).life)
    (hph : a1.phase = .idle ∨ ∃ k, a1.phase = .run k ∧ k.replyTo = none)
    (hhead : (w.st id).box = m :: ms) (hc : m.callFrom = none) :
    CallTagInv (setActor w1 id a1) := by
  have hcarry : ∀ c : InstId, carriedCont a1.phase = none ∨
      ∃ k, carriedCont a1.phase = some k ∧ k.replyTo = none := by
    intro _
    rcases hph with hI | ⟨k, hk, hto⟩
    · exact Or.inl (by simp [carriedCont, hI])
    · exact Or.inr ⟨k, by simp [carriedCont, hk], hto⟩
  apply call_tag_stable w (setActor w1 id a1) hT
  · intro d c
    constructor
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · have hx' : x ∈ ms := by
            simp only [setActor, hd, hst, if_true] at hx
            rw [hbox1] at hx
            exact hx
          exact Or.inl ⟨x, by rw [hd, hhead]; exact List.mem_cons_of_mem _ hx', hcf⟩
        · have hq' : q ∈ a1.parked := by
            simp only [setActor, hd, hst, if_true] at hq
            exact hq
          exact Or.inr ⟨q, by rw [hd, ← hpark1]; exact hq', hcf⟩
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simpa [setActor, hd, hst] using hx, hcf⟩
        · exact Or.inr ⟨q, by simpa [setActor, hd, hst] using hq, hcf⟩
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · have hx' : x ∈ ms := by
            rw [hd, hhead] at hx
            cases hx with
            | head => simp [hc] at hcf
            | tail _ ht => exact ht
          exact Or.inl ⟨x, by
            simp only [setActor, hd, hst, if_true]
            rw [← hbox1] at hx'
            exact hx', hcf⟩
        · exact Or.inr ⟨q, by
            simp only [setActor, hd, hst, if_true]
            rw [hd] at hq
            rwa [← hpark1] at hq, hcf⟩
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [setActor, hd, hst, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [setActor, hd, hst, hq], hcf⟩
  · intro i c
    by_cases hi : i = id
    · have hold : ¬handlerOwes c (w.st id).phase := by simp [handlerOwes, carriedCont, hidle]
      have hnew : ¬handlerOwes c a1.phase := (plain_no_owe a1.phase c (hcarry c)).1
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact owes_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro i c
    by_cases hi : i = id
    · have hold : ¬replyPending c (w.st id).phase := by simp [replyPending, carriedCont, hidle]
      have hnew : ¬replyPending c a1.phase := (plain_no_owe a1.phase c (hcarry c)).2
      simp [setActor, hi]
      exact ⟨fun h => absurd h hnew, fun h => absurd h hold⟩
    · exact pending_iff_carried _ _ (by simp [setActor, hi, hst]) c
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [setActor, hc', hst] at hph'
      rcases hph with hI | ⟨_, hk, _⟩
      · simp [hI] at hph'
      · simp [hk] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro c d k hph'
    by_cases hc' : c = id
    · simp [hidle, hc'] at hph'
    · simpa [setActor, hc', hst] using hph'
  · intro i msg hm
    by_cases hi : i = id
    · exact hT.prioPlain id msg (by
        simp only [setActor, hi, hst, if_true] at hm
        simpa [hprio1] using hm)
    · exact hT.prioPlain i msg (by simpa [setActor, hi, hst] using hm)
  · intro d c
    by_cases hd : d = id
    · have hs := hT.sole id c
      unfold soleCall at hs ⊢
      rw [hhead, count_none m ms c hc] at hs
      simp [setActor, hd, hst, hbox1, hpark1]
      simpa [countCall] using hs
    · simp [soleCall, setActor, hd, hst]
      exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w (setActor w1 id a1) hT
      (fun i => by
        by_cases hi : i = id
        · simp [setActor, hi, hst, hpark1]
        · simp [setActor, hi, hst])
      (fun s d _ => ⟨
        fun h => by
          by_cases hs : s = id
          · simp [setActor, hs, hst] at h
            rcases hph with hI | ⟨_, hk, _⟩ <;>
            first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
          · simpa [setActor, hs, hst] using h,
        fun h => by
          by_cases hs : s = id
          · simp [hidle, hs] at h
          · simpa [setActor, hs, hst] using h⟩)
      d p hp s
  · intro c d k hk
    exact parkedOnly_transport w (setActor w1 id a1) hT
      (fun i => by
        by_cases hi : i = id
        · simp [setActor, hi, hst, hpark1]
        · simp [setActor, hi, hst])
      (fun i msg hm => by
        by_cases hi : i = id
        · have hm' : msg ∈ ms := by
            simp only [setActor, hi, hst, ite_true] at hm
            rw [hbox1] at hm
            exact hm
          rw [hi, hhead]
          exact List.mem_cons_of_mem _ hm'
        · simpa [setActor, hi, hst] using hm)
      (fun c d _ h => by
        by_cases hc0 : c = id
        · simp [setActor, hc0, hst] at h
          rcases hph with hI | ⟨_, hk, _⟩ <;>
            first | (rw [hI] at h; cases h) | (rw [hk] at h; cases h)
        · simpa [setActor, hc0, hst] using h)
      c d k hk
      (life_set_st w w1 id a1 hst hlifeA)
  · exact life_set_st w w1 id a1 hst hlifeA
  · exact owed_quiet_set w w1 id a1 hT hst hidle (fun c0 => plain_no_owe _ c0 (hcarry c0))

/-- Deliver a call at the box head and leave the parked list where it is.
The caller is already in `awaitReply`: a parked phase does not own a box message. -/
theorem install_call_kept (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (c : InstId) (k kw : Cont) (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hbox1 : a1.box = ms)
    (hpark1 : a1.parked = (w.st id).parked) (hprio1 : a1.prio = (w.st id).prio)
    (hlifeA : a1.life = (w.st id).life)
    (hhead : (w.st id).box = m :: ms) (hc : m.callFrom = some c)
    (hrun : a1.phase = .run k) (hshape : replyShape c k)
    (hother : ∀ c', c' ≠ c → ¬handlerOwes c' a1.phase ∧ ¬replyPending c' a1.phase)
    (hown : (w.st c).phase = .awaitReply id kw)
    (howeA : a1.oweId = some (if c = id then (w.st id).waitId else (w.st c).waitId)) :
    CallTagInv (setActor w1 id a1) := by
  have hzeroB : countCall ms c = 0 := by
    have hs := hT.sole id c
    unfold soleCall at hs
    rw [hhead, count_some m ms c hc] at hs
    omega
  have hzeroP : countParkedCall (w.st id).parked c = 0 := by
    have hs := hT.sole id c
    unfold soleCall at hs
    rw [hhead, count_some m ms c hc] at hs
    omega
  have hne : c ≠ id := by
    intro heq
    simp [heq, hidle] at hown
  have hduty : handlerOwes c a1.phase ∨ replyPending c a1.phase := by
    cases hrest : k.rest with
    | nil =>
      have hc1 := hshape.2.1
      simp [replyCount, hrest] at hc1
    | cons e es =>
      by_cases he : e = .reply
      · exact Or.inr ⟨k, by simp [carriedCont, hrun], hshape, by simp [nextIsReply, hrest, he]⟩
      · exact Or.inl ⟨k, by simp [carriedCont, hrun], hshape, by
          cases e <;> simp [nextIsReply, hrest] at he ⊢⟩
  let w' := setActor w1 id a1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold : (w.st c0).phase = .awaitReply d0 k0 := by
      simpa [w', setActor, hc0, hst] using hph
    by_cases hd : d0 = id
    · by_cases hsame : c0 = c
      · rw [hsame, hd]
        have hnom : ¬mailCall w' id c := by
          intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · have hx' : x ∈ ms := by
              simp only [w', setActor, if_true] at hx
              rw [hbox1] at hx
              exact hx
            exact count_zero_mem ms c hzeroB x hx' hcf
          · have hq' : q ∈ (w.st id).parked := by
              simp only [w', setActor, if_true] at hq
              rw [hpark1] at hq
              exact hq
            exact countParked_zero_mem _ c hzeroP q hq' hcf
        rcases hduty with ho | hp
        · exact Or.inr (Or.inl ⟨hnom, by simpa [w', setActor] using ho,
            by simpa [w', setActor] using handlerOwes_not_pending c a1.phase ho⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hnom,
            fun ho' => handlerOwes_not_pending c a1.phase (by simpa [w', setActor] using ho')
              (by simpa [w', setActor] using hp),
            by simpa [w', setActor] using hp⟩))
      · have hpre := hT.awaiting c0 id k0 (by simpa [hd] using hold)
        have holdD : ¬(handlerOwes c0 (w.st id).phase ∨ replyPending c0 (w.st id).phase) := by
          simp [handlerOwes, replyPending, carriedCont, hidle]
        rcases hpre with h1 | h2 | h3 | h4
        · have hmail0 : mailCall w id c0 := h1.1
          have hmem : (∃ x, x ∈ ms ∧ x.callFrom = some c0) ∨
              (∃ q, q ∈ (w.st id).parked ∧ q.msg.callFrom = some c0) := by
            rcases hmail0 with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
            · rw [hhead] at hx
              cases hx with
              | head =>
                simp [hc] at hcf
                exact False.elim (hsame hcf.symm)
              | tail _ ht => exact Or.inl ⟨x, ht, hcf⟩
            · exact Or.inr ⟨q, hq, hcf⟩
          rcases hmem with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨Or.inl ⟨x, by simp [w', setActor, hd, hbox1, hx], hcf⟩,
              by simpa [w', setActor, hd] using (hother c0 hsame).1,
              by simpa [w', setActor, hd] using (hother c0 hsame).2⟩
          · exact Or.inl ⟨Or.inr ⟨q, by simp [w', setActor, hd, hpark1, hq], hcf⟩,
              by simpa [w', setActor, hd] using (hother c0 hsame).1,
              by simpa [w', setActor, hd] using (hother c0 hsame).2⟩
        · exact absurd (Or.inl h2.2.1) holdD
        · exact absurd (Or.inr h3.2.2) holdD
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩))
          · exact halted_cast (by simp [w', setActor, hd, hlifeA]) h4.1
          · simpa [w', setActor, hc0, hst] using h4.2.1
          · intro hm
            apply h4.2.2.1
            rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
            · have hx' : x ∈ ms := by
                simp only [w', setActor, hd, if_true] at hx
                rw [hbox1] at hx
                exact hx
              exact Or.inl ⟨x, by rw [hhead]; exact List.mem_cons_of_mem _ hx', hcf⟩
            · exact Or.inr ⟨q, by
                simp only [w', setActor, hd, if_true] at hq
                rw [hpark1] at hq
                exact hq, hcf⟩
          · simpa [w', setActor, hd] using (hother c0 hsame).1
          · simpa [w', setActor, hd] using (hother c0 hsame).2
    · have hpre := hT.awaiting c0 d0 k0 hold
      have hmail : mailCall w' d0 c0 ↔ mailCall w d0 c0 := by
        constructor
        · intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨x, by simpa [w', setActor, hd, hst] using hx, hcf⟩
          · exact Or.inr ⟨q, by simpa [w', setActor, hd, hst] using hq, hcf⟩
        · intro hm
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨x, by simp [w', setActor, hd, hst, hx], hcf⟩
          · exact Or.inr ⟨q, by simp [w', setActor, hd, hst, hq], hcf⟩
      have hphEq : (w'.st d0).phase = (w.st d0).phase := by
        simp [w', setActor, ite_eq_right hd, hst]
      have howe := owes_iff_carried (w.st d0).phase (w'.st d0).phase (by rw [hphEq]) c0
      have hpend := pending_iff_carried (w.st d0).phase (w'.st d0).phase (by rw [hphEq]) c0
      have hlD : (w'.st d0).life = (w.st d0).life := by simp [w', setActor, hd, hst, hlifeA]
      have hlC : (w'.st c0).life = (w.st c0).life := by simp [w', setActor, hc0, hst]
      rcases hpre with h1 | h2 | h3 | h4
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
          hpend.mpr h3.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w w' c0 d0 hlD hlC hmail howe hpend h4)))
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold : (w.st c0).phase = .parked d0 true k0 := by
      simpa [w', setActor, hc0, hst] using hph
    have hlifeI (i : InstId) : (w'.st i).life = (w.st i).life := by
      by_cases hi : i = id
      · simp [w', setActor, hi, hlifeA]
      · simp [w', setActor, hi, hst]
    rcases hT.parkedCall c0 d0 k0 hold with ⟨hl, hm, ho, hp⟩ | ⟨hl, hnm, ho, hp⟩
    · by_cases hd : d0 = id
      · have hnotC : c0 ≠ c := by
          intro heq
          simp [heq, hown, hd] at hold
        have hmem : (∃ x, x ∈ ms ∧ x.callFrom = some c0) ∨
            (∃ q, q ∈ (w.st id).parked ∧ q.msg.callFrom = some c0) := by
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · rw [hd, hhead] at hx
            cases hx with
            | head =>
              simp [hc] at hcf
              exact False.elim (hnotC hcf.symm)
            | tail _ ht => exact Or.inl ⟨x, ht, hcf⟩
          · exact Or.inr ⟨q, by simpa [hd] using hq, hcf⟩
        refine Or.inl ⟨by rw [hlifeI]; exact hl, ?_,
          by simpa [w', setActor, hd] using (hother c0 hnotC).1,
          by simpa [w', setActor, hd] using (hother c0 hnotC).2⟩
        rcases hmem with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [w', setActor, hd, hbox1, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [w', setActor, hd, hpark1, hq], hcf⟩
      · exact Or.inl ⟨by rw [hlifeI]; exact hl, by
          rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
          · exact Or.inl ⟨x, by simp [w', setActor, hd, hst, hx], hcf⟩
          · exact Or.inr ⟨q, by simp [w', setActor, hd, hst, hq], hcf⟩,
          by simpa [w', setActor, hd, hst] using ho,
          by simpa [w', setActor, hd, hst] using hp⟩
    · by_cases hd : d0 = id
      · have hnotC : c0 ≠ c := by
          intro heq
          simp [heq, hown, hd] at hold
        refine Or.inr ⟨by rw [hlifeI]; exact hl, ?_,
          by simpa [w', setActor, hd] using (hother c0 hnotC).1,
          by simpa [w', setActor, hd] using (hother c0 hnotC).2⟩
        intro hm'
        rcases hm' with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · have hx0 : x ∈ m :: ms := by
            simp [w', setActor, hd, hbox1] at hx
            exact List.mem_cons_of_mem _ hx
          exact hnm (Or.inl ⟨x, by rw [hd, hhead]; exact hx0, hcf⟩)
        · exact hnm (Or.inr ⟨q, by
            simpa [w', setActor, hd, hpark1] using hq, hcf⟩)
      · exact Or.inr ⟨by rw [hlifeI]; exact hl,
          fun hm' => hnm (by
            rcases hm' with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
            · exact Or.inl ⟨x, by simpa [w', setActor, hd, hst] using hx, hcf⟩
            · exact Or.inr ⟨q, by simpa [w', setActor, hd, hst] using hq, hcf⟩),
          by simpa [w', setActor, hd, hst] using ho,
          by simpa [w', setActor, hd, hst] using hp⟩
  · intro d0 c0 hm
    have hpreM : mailCall w d0 c0 := by
      by_cases hd : d0 = id
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · have hx' : x ∈ ms := by
            simp only [w', setActor, hd, if_true] at hx
            rw [hbox1] at hx
            exact hx
          exact Or.inl ⟨x, by rw [hd, hhead]; exact List.mem_cons_of_mem _ hx', hcf⟩
        · have hq' : q ∈ (w.st id).parked := by
            simp only [w', setActor, hd, if_true] at hq
            rw [hpark1] at hq
            exact hq
          exact Or.inr ⟨q, by rw [hd]; exact hq', hcf⟩
      · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simpa [w', setActor, hd, hst] using hx, hcf⟩
        · exact Or.inr ⟨q, by simpa [w', setActor, hd, hst] using hq, hcf⟩
    rcases hT.msgOwner d0 c0 hpreM with ⟨k0, hk0⟩ | ⟨k0, hk0⟩
    · exact Or.inl ⟨k0, by
        have hc0 : c0 ≠ id := by
          intro heq
          simp [heq, hidle] at hk0
        simpa [w', setActor, hc0, hst] using hk0⟩
    · exact Or.inr ⟨k0, by
        have hc0 : c0 ≠ id := by
          intro heq
          simp [heq, hidle] at hk0
        simpa [w', setActor, hc0, hst] using hk0⟩
  · intro d0 c0 ho
    by_cases hd : d0 = id
    · have hc0 : c0 = c := by
        by_cases hbad : c0 = c
        · exact hbad
        · rcases ho with h | h
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).1
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).2
      exact ⟨kw, by rw [hc0, hd]; simpa [w', setActor, hst, hne] using hown⟩
    · have hpre : handlerOwes c0 (w.st d0).phase ∨ replyPending c0 (w.st d0).phase := by
        simpa [w', setActor, hd, hst] using ho
      obtain ⟨k0, hk0⟩ := hT.oweOwner d0 c0 hpre
      have hc0 : c0 ≠ id := by
        intro heq
        simp [heq, hidle] at hk0
      exact ⟨k0, by simpa [w', setActor, hc0, hst] using hk0⟩
  · intro i msg hm
    by_cases hi : i = id
    · exact hT.prioPlain id msg (by
        simp only [w', setActor, hi, if_true] at hm
        simpa [hprio1] using hm)
    · exact hT.prioPlain i msg (by simpa [w', setActor, hi, hst] using hm)
  · intro d0 c0
    by_cases hd : d0 = id
    · by_cases hsame : c0 = c
      · unfold soleCall
        have hz : countParkedCall a1.parked c = 0 := by rw [hpark1]; exact hzeroP
        simp [w', setActor, hd, hbox1, hsame, hzeroB, hz, countParkedCall]
      · have hs := hT.sole id c0
        unfold soleCall at hs
        rw [hhead] at hs
        have hdrop : countCall (m :: ms) c0 = countCall ms c0 := by
          have hne0 : m.callFrom ≠ some c0 := by
            intro hbad
            simp [hc] at hbad
            exact hsame hbad.symm
          simp [countCall, hne0]
        rw [hdrop] at hs
        simpa [soleCall, w', setActor, hd, hbox1, hpark1] using hs
    · simpa [soleCall, w', setActor, hd, hst] using hT.sole d0 c0
  · intro d p hp s
    exact parkFrom_transport w w' hT
      (fun i => by
        by_cases hi : i = id
        · simp [w', setActor, hi, hpark1]
        · simp [w', setActor, hi, hst])
      (fun s d _ => ⟨
        fun h => by
          by_cases hs : s = id
          · simp [w', setActor, hs, hrun] at h
          · simpa [w', setActor, hs, hst] using h,
        fun h => by
          by_cases hs : s = id
          · simp [hidle, hs] at h
          · simpa [w', setActor, hs, hst] using h⟩)
      d p hp s
  · intro c0 d kP hk
    exact parkedOnly_transport w w' hT
      (fun i => by
        by_cases hi : i = id
        · simp [w', setActor, hi, hpark1]
        · simp [w', setActor, hi, hst])
      (fun i msg hm => by
        by_cases hi : i = id
        · have hm' : msg ∈ ms := by
            simp only [w', setActor, hi, if_true] at hm
            rw [hbox1] at hm
            exact hm
          rw [hi, hhead]
          exact List.mem_cons_of_mem _ hm'
        · simpa [w', setActor, hi, hst] using hm)
      (fun c0 d _ h => by
        by_cases hc0 : c0 = id
        · simp [w', setActor, hc0, hrun] at h
        · simpa [w', setActor, hc0, hst] using h)
      c0 d kP hk
      (life_set_st w w1 id a1 hst hlifeA)
  · intro d0 c0 ho
    by_cases hd : d0 = id
    · have hc0 : c0 = c := by
        by_cases hbad : c0 = c
        · exact hbad
        · rcases ho with h | h
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).1
          · exact absurd (by simpa [w', setActor, hd] using h) (hother c0 hbad).2
      rw [hd, hc0]
      simp [w', setActor, howeA, hne, hst]
    · by_cases hc0 : c0 = id
      · rw [hc0] at ho
        have hpre : handlerOwes id (w.st d0).phase ∨ replyPending id (w.st d0).phase := by
          simpa [w', setActor, hd, hst] using ho
        obtain ⟨k0, hk0⟩ := hT.oweOwner d0 id hpre
        simp [hidle] at hk0
      · have hpre : handlerOwes c0 (w.st d0).phase ∨ replyPending c0 (w.st d0).phase := by
          simpa [w', setActor, hd, hst] using ho
        simpa [w', setActor, hd, hc0, hst] using hT.owedId d0 c0 hpre

theorem count_append (ms : List Msg) (m : Msg) (c : InstId) :
    countCall (ms ++ [m]) c = countCall ms c + countCall [m] c := by
  induction ms with
  | nil => simp [countCall]
  | cons x xs ih =>
    simp [countCall, ih, Nat.add_assoc]

/-- Move a parked head onto the tail of the box. Phases stay put, so a call tag
moves from one list to the other and the count is unchanged. -/
theorem move_parked_msg (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hplain : p.msg.callFrom = none) :
    CallTagInv (setActor w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }) := by
  let w' := setActor w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }
  apply call_tag_stable w w' hT
  · intro d c
    by_cases hd : d = id
    · constructor
      · intro hm
        rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · simp only [w', setActor, hd, if_true] at hx
          rw [hd]
          have hx' : x ∈ (w.st id).box ∨ x = p.msg := by
            rw [List.mem_append] at hx
            simpa using hx
          rcases hx' with hin | heq
          · exact Or.inl ⟨x, hin, hcf⟩
          · rw [heq] at hcf
            exact Or.inr ⟨p, by simp [hpark], hcf⟩
        · simp only [w', setActor, hd, if_true] at hq
          exact Or.inr ⟨q, by rw [hd, hpark]; exact List.mem_cons_of_mem _ hq, hcf⟩
      · intro hm
        rw [hd] at hm
        rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by
            simp [w', setActor, hd]
            exact Or.inl hx, hcf⟩
        · rw [hpark] at hq
          cases hq with
          | head =>
            exact Or.inl ⟨p.msg, by
              simp [w', setActor, hd], hcf⟩
          | tail _ ht =>
            exact Or.inr ⟨q, by
              simp [w', setActor, hd]
              exact ht, hcf⟩
    · constructor
      · intro hm
        rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simpa [w', setActor, ite_eq_right hd] using hx, hcf⟩
        · exact Or.inr ⟨q, by simpa [w', setActor, ite_eq_right hd] using hq, hcf⟩
      · intro hm
        rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [w', setActor, ite_eq_right hd, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [w', setActor, ite_eq_right hd, hq], hcf⟩
  · intro i c
    exact owes_iff_carried _ _ (by
      by_cases hi : i = id <;> simp [w', setActor, hi, carriedCont]) c
  · intro i c
    exact pending_iff_carried _ _ (by
      by_cases hi : i = id <;> simp [w', setActor, hi, carriedCont]) c
  · intro c0 d0 k0 hph
    by_cases hc : c0 = id
    · simp [w', setActor, hc] at hph
      rw [hc]
      exact hph
    · simpa [w', setActor, hc] using hph
  · intro c0 d0 k0 hph
    by_cases hc : c0 = id
    · simpa [w', setActor, hc] using hph
    · simpa [w', setActor, hc] using hph
  · intro c0 d0 k0 hph
    by_cases hc : c0 = id
    · simp [w', setActor, hc] at hph
      rw [hc]
      exact hph
    · simpa [w', setActor, hc] using hph
  · intro c0 d0 k0 hph
    by_cases hc : c0 = id
    · simpa [w', setActor, hc] using hph
    · simpa [w', setActor, hc] using hph
  · intro i m hm
    by_cases hi : i = id
    · exact hT.prioPlain id m (by simpa [w', setActor, hi] using hm)
    · exact hT.prioPlain i m (by simpa [w', setActor, hi] using hm)
  · intro d c
    by_cases hd : d = id
    · have hs := hT.sole id c
      unfold soleCall at hs ⊢
      rw [hd]
      simp [w', setActor, hpark, count_append, countCall, countParkedCall] at hs ⊢
      omega
    · simpa [soleCall, w', setActor, hd] using hT.sole d c
  · intro d q hq s
    have hphEq : (w'.st s).phase = (w.st s).phase := by
      by_cases hs : s = id <;> simp [w', setActor, hs]
    have hq0 : q ∈ (w.st d).parked := by
      by_cases hd : d = id
      · have ht : q ∈ ps := by
          simp only [w', setActor, hd, if_true] at hq
          exact hq
        rw [hd, hpark]
        exact List.mem_cons_of_mem _ ht
      · simpa [w', setActor, hd] using hq
    have hiff := hT.parkFrom d q hq0 s
    constructor
    · intro hc
      obtain ⟨hs, k, hk⟩ := hiff.mp hc
      exact ⟨hs, k, by rw [hphEq]; exact hk⟩
    · intro ⟨hs, k, hk⟩
      exact hiff.mpr ⟨hs, k, by rw [← hphEq]; exact hk⟩
  · intro c d k hk
    have hphEq : (w'.st c).phase = (w.st c).phase := by
      by_cases hc : c = id <;> simp [w', setActor, hc]
    exact parkedOnly_lift w w' hT c d k (by rw [hphEq] at hk; exact hk)
      (by
        by_cases hd : d = id
        · rw [hd]
          simp [w', setActor]
        · simp [w', setActor, hd])
      (fun p hp hs hcf => by
        by_cases hd : d = id
        · rw [hd] at hp ⊢
          rw [hpark] at hp
          cases hp with
          | head => simp [hplain] at hcf
          | tail _ ht =>
            simp [w', setActor]
            exact ht
        · simpa [w', setActor, hd] using hp)
      (fun p hp hcf => by
        by_cases hd : d = id
        · rw [hd] at hp ⊢
          simp [w', setActor] at hp
          rw [hpark]
          exact List.mem_cons_of_mem _ hp
        · simpa [w', setActor, hd] using hp)
      (fun m hm hcf => by
        by_cases hd : d = id
        · rw [hd] at hm ⊢
          simp [w', setActor] at hm
          rcases hm with hmem | hmem
          · exact hmem
          · subst hmem
            rw [hplain] at hcf
            cases hcf
        · simpa [w', setActor, hd] using hm)
  · simpa [w'] using life_setActor w id
      ({ (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }) (by simp)
  · exact fun d c ho => owed_phase w w' hT
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi])
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi]) d c ho

/-- Mailbox after a parked head has been appended to the box. -/
def shiftBase (w : World) (id : InstId) (p : Parked) (ps : List Parked) : World :=
  setActor w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }

/-- That mailbox, with the parked caller now in `awaitReply`. -/
def shiftWorld (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont) : World :=
  setActor (shiftBase w id p ps) p.sender
    { ((shiftBase w id p ps).st p.sender) with phase := .awaitReply id kS }

theorem shift_phF (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st p.sender).phase = .awaitReply id kS := by
  simp [shiftWorld, shiftBase, setActor]

theorem shift_phId (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st id).phase = (w.st id).phase := by
  have hne : ¬ id = p.sender := fun h => hsnd h.symm
  simp [shiftWorld, shiftBase, setActor, hne]

theorem shift_boxId (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st id).box = (w.st id).box ++ [p.msg] := by
  have hne : ¬ id = p.sender := fun h => hsnd h.symm
  simp [shiftWorld, shiftBase, setActor, hne]

theorem shift_parkId (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st id).parked = ps := by
  have hne : ¬ id = p.sender := fun h => hsnd h.symm
  simp [shiftWorld, shiftBase, setActor, hne]

theorem shift_prioId (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st id).prio = (w.st id).prio := by
  have hne : ¬ id = p.sender := fun h => hsnd h.symm
  simp [shiftWorld, shiftBase, setActor, hne]

theorem shift_boxS (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st p.sender).box = (w.st p.sender).box := by
  simp [shiftWorld, shiftBase, setActor, hsnd]

theorem shift_parkS (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st p.sender).parked = (w.st p.sender).parked := by
  simp [shiftWorld, shiftBase, setActor, hsnd]

theorem shift_prioS (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) :
    ((shiftWorld w id p ps kS).st p.sender).prio = (w.st p.sender).prio := by
  simp [shiftWorld, shiftBase, setActor, hsnd]

theorem shift_other (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (i : InstId) (hi : i ≠ id) (hs : i ≠ p.sender) :
    ((shiftWorld w id p ps kS).st i).phase = (w.st i).phase ∧
      ((shiftWorld w id p ps kS).st i).box = (w.st i).box ∧
      ((shiftWorld w id p ps kS).st i).parked = (w.st i).parked ∧
      ((shiftWorld w id p ps kS).st i).prio = (w.st i).prio := by
  simp [shiftWorld, shiftBase, setActor, hi, hs]

/-- Installing a delivered actor keeps the parked relation when that actor is not parked. -/
theorem mail_install (w w1 : World) (id : InstId) (a1 : Actor) (hM : MailInv w)
    (hst : ∀ i, w1.st i = w.st i) (hidle : (w.st id).phase = .idle)
    (hlive : (w.st id).life = .alive) (hpark1 : a1.parked = (w.st id).parked)
    (hnot : ∀ d (b : Bool) k, a1.phase ≠ .parked d b k) :
    MailInv (setActor w1 id a1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb q hp
    by_cases hd : mb = id
    · have hp0 : q ∈ (w.st id).parked := by
        simp only [setActor, hd, hst, ite_true] at hp
        rwa [hpark1] at hp
      obtain ⟨k, hk⟩ := hM.fwd id q hp0
      have hsnd : q.sender ≠ id := by
        intro heq
        simp [heq, hidle] at hk
      exact ⟨k, by rw [hd]; simpa [setActor, hsnd, hst] using hk⟩
    · have hp0 : q ∈ (w.st mb).parked := by simpa [setActor, hd, hst] using hp
      obtain ⟨k, hk⟩ := hM.fwd mb q hp0
      by_cases hs : q.sender = id
      · simp [hs, hidle] at hk
      · exact ⟨k, by simpa [setActor, hs, hst] using hk⟩
  · intro i dst b k hk
    have hi : i ≠ id := by
      intro heq
      simp [setActor, heq, hst] at hk
      exact hnot dst b k hk
    have hold : (w.st i).phase = .parked dst b k := by simpa [setActor, hi, hst] using hk
    rcases hM.bwd i dst b k hold with ⟨q, hq, hs, hc⟩ | ⟨hb, hdead⟩
    · by_cases hd : dst = id
      · exact Or.inl ⟨q, by
          rw [hd]
          simp only [setActor, hst, ite_true]
          rw [hd] at hq
          rw [hpark1]
          exact hq, hs, hc⟩
      · exact Or.inl ⟨q, by simpa [setActor, hd, hst] using hq, hs, hc⟩
    · by_cases hd : dst = id
      · rw [hd] at hdead
        rw [hdead] at hlive
        cases hlive
      · exact Or.inr ⟨hb, by simpa [setActor, hd, hst] using hdead⟩
  · intro mb1 mb2 q1 q2 h1 h2 hseq
    have back (mb : InstId) (q : Parked) (hq : q ∈ ((setActor w1 id a1).st mb).parked) :
        q ∈ (w.st mb).parked := by
      by_cases hd : mb = id
      · rw [hd] at hq
        simp only [setActor, hst, ite_true] at hq
        rw [hd]
        rwa [hpark1] at hq
      · simpa [setActor, hd, hst] using hq
    exact hM.uniq mb1 mb2 q1 q2 (back mb1 q1 h1) (back mb2 q2 h2) hseq
  · intro mb
    by_cases hd : mb = id
    · simpa [setActor, hd, hst, hpark1] using hM.once id
    · simpa [setActor, hd, hst] using hM.once mb

theorem shift_prio (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hsnd : p.sender ≠ id) :
    ∀ i m, m ∈ ((shiftWorld w id p ps kS).st i).prio → m.callFrom = none := by
  intro i m hm
  by_cases hi : i = id
  · exact hT.prioPlain id m (by
      rw [hi, shift_prioId w id p ps kS hsnd] at hm
      exact hm)
  · by_cases hs : i = p.sender
    · exact hT.prioPlain p.sender m (by
        rw [hs, shift_prioS w id p ps kS hsnd] at hm
        exact hm)
    · exact hT.prioPlain i m (by
        rw [(shift_other w id p ps kS i hi hs).2.2.2] at hm
        exact hm)

theorem shift_sole (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hfrom : p.msg.callFrom = some p.sender) (hsnd : p.sender ≠ id) :
    ∀ d c, soleCall (shiftWorld w id p ps kS) d c := by
  intro d c
  by_cases hd : d = id
  · by_cases hc : c = p.sender
    · have hold := hT.sole id p.sender
      unfold soleCall at hold ⊢
      rw [hpark, countParked_some p ps p.sender hfrom] at hold
      rw [hd, hc, shift_boxId w id p ps kS hsnd, shift_parkId w id p ps kS hsnd, count_append]
      simp [countCall, hfrom]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hold
    · have hold := hT.sole id c
      unfold soleCall at hold ⊢
      rw [hd, shift_boxId w id p ps kS hsnd, shift_parkId w id p ps kS hsnd]
      rw [hpark] at hold
      have hdropP : countParkedCall (p :: ps) c = countParkedCall ps c := by
        have hne : p.msg.callFrom ≠ some c := by
          intro hbad
          simp [hfrom] at hbad
          exact hc hbad.symm
        simp [countParkedCall, hne]
      have hdropB : countCall ((w.st id).box ++ [p.msg]) c = countCall (w.st id).box c := by
        have hne : p.msg.callFrom ≠ some c := by
          intro hbad
          simp [hfrom] at hbad
          exact hc hbad.symm
        rw [count_append]
        simp [countCall, hne]
      rw [hdropP] at hold
      rw [hdropB]
      exact hold
  · by_cases hdS : d = p.sender
    · unfold soleCall
      rw [hdS, shift_boxS w id p ps kS hsnd, shift_parkS w id p ps kS hsnd]
      exact hT.sole p.sender c
    · unfold soleCall
      rw [(shift_other w id p ps kS d hd hdS).2.1, (shift_other w id p ps kS d hd hdS).2.2.1]
      exact hT.sole d c

/-- A parked call moves onto the box and its sender enters `awaitReply` together.
Either half alone breaks `parkFrom` or `parkedOnly`. -/
theorem shift_old_park (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hpark : (w.st id).parked = p :: ps) (hsnd : p.sender ≠ id) (d : InstId) (q : Parked)
    (hq : q ∈ ((shiftWorld w id p ps kS).st d).parked) : q ∈ (w.st d).parked := by
  by_cases hd : d = id
  · rw [hd] at hq
    rw [shift_parkId w id p ps kS hsnd] at hq
    rw [hd, hpark]
    exact List.mem_cons_of_mem _ hq
  · by_cases hdS : d = p.sender
    · rw [hdS] at hq
      rw [shift_parkS w id p ps kS hsnd] at hq
      rw [hdS]
      exact hq
    · rw [(shift_other w id p ps kS d hd hdS).2.2.1] at hq
      exact hq

theorem shift_owes (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) (d c : InstId) :
    handlerOwes c ((shiftWorld w id p ps kS).st d).phase ↔
      handlerOwes c (w.st d).phase := by
  by_cases hd : d = p.sender
  · have hcar : carriedCont ((shiftWorld w id p ps kS).st p.sender).phase =
        carriedCont (w.st p.sender).phase := by
      simp [carriedCont, shift_phF w id p ps kS hsnd, hph]
    exact owes_iff_carried _ _ (by rw [hd]; exact hcar) c
  · by_cases hdI : d = id
    · exact owes_iff_carried _ _ (by rw [hdI, shift_phId w id p ps kS hsnd]) c
    · exact owes_iff_carried _ _ (by rw [(shift_other w id p ps kS d hdI hd).1]) c

theorem shift_pending (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) (d c : InstId) :
    replyPending c ((shiftWorld w id p ps kS).st d).phase ↔
      replyPending c (w.st d).phase := by
  by_cases hd : d = p.sender
  · have hcar : carriedCont ((shiftWorld w id p ps kS).st p.sender).phase =
        carriedCont (w.st p.sender).phase := by
      simp [carriedCont, shift_phF w id p ps kS hsnd, hph]
    exact pending_iff_carried _ _ (by rw [hd]; exact hcar) c
  · by_cases hdI : d = id
    · exact pending_iff_carried _ _ (by rw [hdI, shift_phId w id p ps kS hsnd]) c
    · exact pending_iff_carried _ _ (by rw [(shift_other w id p ps kS d hdI hd).1]) c

theorem shift_mail_ne (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hpark : (w.st id).parked = p :: ps) (hfrom : p.msg.callFrom = some p.sender)
    (hsnd : p.sender ≠ id) (d c : InstId) (hc : c ≠ p.sender) :
    mailCall (shiftWorld w id p ps kS) d c ↔ mailCall w d c := by
  constructor
  · intro hm
    rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
    · by_cases hd : d = id
      · rw [hd, shift_boxId w id p ps kS hsnd] at hx
        rw [List.mem_append] at hx
        rcases hx with hin | heq
        · exact Or.inl ⟨x, by rw [hd]; exact hin, hcf⟩
        · simp at heq
          rw [heq, hfrom] at hcf
          injection hcf with heqc
          exact False.elim (hc heqc.symm)
      · by_cases hdS : d = p.sender
        · rw [hdS, shift_boxS w id p ps kS hsnd] at hx
          exact Or.inl ⟨x, by rw [hdS]; exact hx, hcf⟩
        · rw [(shift_other w id p ps kS d hd hdS).2.1] at hx
          exact Or.inl ⟨x, hx, hcf⟩
    · exact Or.inr ⟨q, shift_old_park w id p ps kS hpark hsnd d q hq, hcf⟩
  · intro hm
    rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
    · by_cases hd : d = id
      · exact Or.inl ⟨x, by
          rw [hd] at hx
          rw [hd]
          rw [shift_boxId w id p ps kS hsnd]
          exact List.mem_append_left _ hx, hcf⟩
      · by_cases hdS : d = p.sender
        · exact Or.inl ⟨x, by
            rw [hdS] at hx
            rw [hdS, shift_boxS w id p ps kS hsnd]
            exact hx, hcf⟩
        · exact Or.inl ⟨x, by
            rw [(shift_other w id p ps kS d hd hdS).2.1]
            exact hx, hcf⟩
    · by_cases hd : d = id
      · rw [hd, hpark] at hq
        cases hq with
        | head =>
          rw [hfrom] at hcf
          injection hcf with heqc
          exact False.elim (hc heqc.symm)
        | tail _ ht =>
          exact Or.inr ⟨q, by rw [hd, shift_parkId w id p ps kS hsnd]; exact ht, hcf⟩
      · by_cases hdS : d = p.sender
        · exact Or.inr ⟨q, by
            rw [hdS] at hq
            rw [hdS, shift_parkS w id p ps kS hsnd]
            exact hq, hcf⟩
        · exact Or.inr ⟨q, by
            rw [(shift_other w id p ps kS d hd hdS).2.2.1]
            exact hq, hcf⟩

theorem shift_life (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (i : InstId) : ((shiftWorld w id p ps kS).st i).life = (w.st i).life := by
  by_cases hs : i = p.sender
  · rw [hs, shiftWorld, setActor_self]
    change ((shiftBase w id p ps).st p.sender).life = (w.st p.sender).life
    by_cases hsi : p.sender = id
    · simp [shiftBase, setActor, hsi]
    · simp [shiftBase, setActor, hsi]
  · by_cases hid : i = id
    · have hne : ¬ id = p.sender := fun h => hs (hid ▸ h)
      simp [shiftWorld, shiftBase, setActor, hid, hne]
    · simp [shiftWorld, shiftBase, setActor, hs, hid]

theorem shift_awaiting (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS)
    (hfrom : p.msg.callFrom = some p.sender) (hsnd : p.sender ≠ id) :
    ∀ c d k, ((shiftWorld w id p ps kS).st c).phase = .awaitReply d k →
      (mailCall (shiftWorld w id p ps kS) d c ∧
          ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          ¬replyPending c ((shiftWorld w id p ps kS).st d).phase) ∨
      (¬mailCall (shiftWorld w id p ps kS) d c ∧
          handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          ¬replyPending c ((shiftWorld w id p ps kS).st d).phase) ∨
      (¬mailCall (shiftWorld w id p ps kS) d c ∧
          ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          replyPending c ((shiftWorld w id p ps kS).st d).phase) ∨
      (Halted ((shiftWorld w id p ps kS).st d).life ∧
          ((shiftWorld w id p ps kS).st c).life = .alive ∧
          ¬mailCall (shiftWorld w id p ps kS) d c ∧
          ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          ¬replyPending c ((shiftWorld w id p ps kS).st d).phase) := by
  intro c d k hph'
  by_cases hc : c = p.sender
  · have hEq : Phase.awaitReply id kS = Phase.awaitReply d k := by
      rw [← shift_phF w id p ps kS hsnd, ← hc]; exact hph'
    injection hEq with hd0 hk0
    have hmail : mailCall (shiftWorld w id p ps kS) id p.sender :=
      Or.inl ⟨p.msg, by
        rw [shift_boxId w id p ps kS hsnd]
        exact List.mem_append_right _ (by simp), hfrom⟩
    rcases hT.parkedCall p.sender id kS hph with ⟨_, _, ho, hp⟩ | ⟨_, _, ho, hp⟩
    all_goals
      have howe := shift_owes w id p ps kS hph hsnd id p.sender
      have hpend := shift_pending w id p ps kS hph hsnd id p.sender
      rw [← hd0, hc]
      exact Or.inl ⟨hmail, (not_iff howe).mpr ho, (not_iff hpend).mpr hp⟩
  · by_cases hcId : c = id
    · have hph0 : (w.st c).phase = .awaitReply d k := by
        have h := hph'
        rw [hcId, shift_phId w id p ps kS hsnd] at h
        rwa [← hcId] at h
      have hpre := hT.awaiting c d k hph0
      have hmail := shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc
      have howe := shift_owes w id p ps kS hph hsnd d c
      have hpend := shift_pending w id p ps kS hph hsnd d c
      rcases hpre with h1 | h2 | h3 | h4
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
          hpend.mpr h3.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w (shiftWorld w id p ps kS) c d
          (shift_life w id p ps kS d) (shift_life w id p ps kS c) hmail howe hpend h4)))
    · have hph0 : (w.st c).phase = .awaitReply d k := by
        rw [← (shift_other w id p ps kS c hcId hc).1]; exact hph'
      have hpre := hT.awaiting c d k hph0
      have hmail := shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc
      have howe := shift_owes w id p ps kS hph hsnd d c
      have hpend := shift_pending w id p ps kS hph hsnd d c
      rcases hpre with h1 | h2 | h3 | h4
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
          hpend.mpr h3.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w (shiftWorld w id p ps kS) c d
          (shift_life w id p ps kS d) (shift_life w id p ps kS c) hmail howe hpend h4)))

theorem shift_parkedCall (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) :
    ∀ c d k, ((shiftWorld w id p ps kS).st c).phase = .parked d true k →
      (Holding ((shiftWorld w id p ps kS).st d).life ∧
          mailCall (shiftWorld w id p ps kS) d c ∧
          ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          ¬replyPending c ((shiftWorld w id p ps kS).st d).phase) ∨
      (Halted ((shiftWorld w id p ps kS).st d).life ∧
          ¬mailCall (shiftWorld w id p ps kS) d c ∧
          ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
          ¬replyPending c ((shiftWorld w id p ps kS).st d).phase) := by
  intro c d k hph'
  by_cases hc : c = p.sender
  · rw [hc, shift_phF w id p ps kS hsnd] at hph'
    cases hph'
  · have hph0 : (w.st c).phase = .parked d true k := by
      by_cases hcId : c = id
      · have h := hph'
        rw [hcId, shift_phId w id p ps kS hsnd] at h
        rwa [← hcId] at h
      · rw [(shift_other w id p ps kS c hcId hc).1] at hph'
        exact hph'
    have hfrom : p.msg.callFrom = some p.sender :=
      (hT.parkFrom id p (by simp [hpark]) p.sender).mpr ⟨rfl, kS, hph⟩
    have hmail := shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc
    rcases hT.parkedCall c d k hph0 with ⟨hl, hm, ho, hp⟩ | ⟨hl, hm, ho, hp⟩
    · exact Or.inl ⟨by rw [shift_life w id p ps kS d]; exact hl, hmail.mpr hm,
        (not_iff (shift_owes w id p ps kS hph hsnd d c)).mpr ho,
        (not_iff (shift_pending w id p ps kS hph hsnd d c)).mpr hp⟩
    · exact Or.inr ⟨by rw [shift_life w id p ps kS d]; exact hl, fun h => hm (hmail.mp h),
        (not_iff (shift_owes w id p ps kS hph hsnd d c)).mpr ho,
        (not_iff (shift_pending w id p ps kS hph hsnd d c)).mpr hp⟩

theorem shift_parkFrom (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hM : MailInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) :
    ∀ d q, q ∈ ((shiftWorld w id p ps kS).st d).parked → ∀ s,
      q.msg.callFrom = some s ↔ q.sender = s ∧
        ∃ k, ((shiftWorld w id p ps kS).st s).phase = .parked d true k := by
  intro d q hq s
  by_cases hsS : s = p.sender
  · constructor
    · intro hc
      have hq0 := shift_old_park w id p ps kS hpark hsnd d q hq
      obtain ⟨hseq, _, hk⟩ := (hT.parkFrom d q hq0 s).mp hc
      have hsame := hM.uniq d id q p hq0 (by rw [hpark]; exact List.Mem.head _) (hseq.trans hsS)
      have hqP : p ∈ ps := by
        have hq' := hq
        rw [hsame.1] at hq'
        rw [shift_parkId w id p ps kS hsnd] at hq'
        simpa [hsame.2] using hq'
      have hnd := hM.once id
      rw [hpark] at hnd
      exact False.elim ((List.nodup_cons.mp hnd).1 hqP)
    · intro ⟨_, _, hk⟩
      rw [hsS, shift_phF w id p ps kS hsnd] at hk
      cases hk
  · have hphEq : ((shiftWorld w id p ps kS).st s).phase = (w.st s).phase := by
      by_cases hsid : s = id
      · rw [hsid]; exact shift_phId w id p ps kS hsnd
      · exact (shift_other w id p ps kS s hsid hsS).1
    have hq0 := shift_old_park w id p ps kS hpark hsnd d q hq
    have hiff := hT.parkFrom d q hq0 s
    constructor
    · intro hc
      obtain ⟨hseq, k, hk⟩ := hiff.mp hc
      exact ⟨hseq, k, by rw [hphEq]; exact hk⟩
    · intro ⟨hseq, k, hk⟩
      exact hiff.mpr ⟨hseq, k, by rw [← hphEq]; exact hk⟩

theorem shift_parkedOnly (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS)
    (hfrom : p.msg.callFrom = some p.sender) (hsnd : p.sender ≠ id) :
    ∀ c d k, ((shiftWorld w id p ps kS).st c).phase = .parked d true k →
      (Holding ((shiftWorld w id p ps kS).st d).life ∧
          (∃ q, q ∈ ((shiftWorld w id p ps kS).st d).parked ∧ q.sender = c ∧
            q.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ ((shiftWorld w id p ps kS).st d).box ∧ m.callFrom = some c) ∨
      (Halted ((shiftWorld w id p ps kS).st d).life ∧
          (¬∃ q, q ∈ ((shiftWorld w id p ps kS).st d).parked ∧ q.msg.callFrom = some c) ∧
          ¬∃ m, m ∈ ((shiftWorld w id p ps kS).st d).box ∧ m.callFrom = some c) := by
  intro c d k hph'
  by_cases hc : c = p.sender
  · rw [hc, shift_phF w id p ps kS hsnd] at hph'
    cases hph'
  · have hph0 : (w.st c).phase = .parked d true k := by
      by_cases hcId : c = id
      · have h := hph'
        rw [hcId, shift_phId w id p ps kS hsnd] at h
        rwa [← hcId] at h
      · rw [(shift_other w id p ps kS c hcId hc).1] at hph'
        exact hph'
    exact parkedOnly_lift w (shiftWorld w id p ps kS) hT c d k hph0
      (shift_life w id p ps kS d)
      (fun q hq hsend _ => by
        by_cases hd : d = id
        · rw [hd, hpark] at hq
          cases hq with
          | head => exact False.elim (hc hsend.symm)
          | tail _ ht =>
            rw [hd, shift_parkId w id p ps kS hsnd]
            exact ht
        · by_cases hdS : d = p.sender
          · rw [hdS] at hq
            rw [hdS, shift_parkS w id p ps kS hsnd]
            exact hq
          · rw [(shift_other w id p ps kS d hd hdS).2.2.1]
            exact hq)
      (fun q hq _ => shift_old_park w id p ps kS hpark hsnd d q hq)
      (fun m hm hcf => by
        by_cases hd : d = id
        · rw [hd, shift_boxId w id p ps kS hsnd] at hm
          rw [List.mem_append] at hm
          rcases hm with hin | heq
          · rw [hd]
            exact hin
          · simp at heq
            rw [heq, hfrom] at hcf
            injection hcf with heqc
            exact False.elim (hc heqc.symm)
        · by_cases hdS : d = p.sender
          · rw [hdS, shift_boxS w id p ps kS hsnd] at hm
            rw [hdS]
            exact hm
          · rw [(shift_other w id p ps kS d hd hdS).2.1] at hm
            exact hm)

theorem shift_msgOwner (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hM : MailInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS)
    (hfrom : p.msg.callFrom = some p.sender) (hsnd : p.sender ≠ id) :
    ∀ d c, mailCall (shiftWorld w id p ps kS) d c →
      (∃ k, ((shiftWorld w id p ps kS).st c).phase = .awaitReply d k) ∨
        (∃ k, ((shiftWorld w id p ps kS).st c).phase = .parked d true k) := by
  intro d c hm
  by_cases hc : c = p.sender
  · rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
    · by_cases hd : d = id
      · rw [hd, shift_boxId w id p ps kS hsnd] at hx
        rw [List.mem_append] at hx
        rcases hx with hin | heq
        · have hph' : (w.st p.sender).phase = .parked id true kS := by simpa [hd] using hph
          have hcf' : x.callFrom = some p.sender := hc ▸ hcf
          rcases hT.parkedOnly p.sender id kS hph' with ⟨_, _, hbox⟩ | ⟨_, _, hbox⟩
          · exact False.elim (hbox ⟨x, hin, hcf'⟩)
          · exact False.elim (hbox ⟨x, hin, hcf'⟩)
        · exact Or.inl ⟨kS, by rw [hc, hd, shift_phF w id p ps kS hsnd]⟩
      · have hx0 : x ∈ (w.st d).box := by
          by_cases hdS : d = p.sender
          · have hx' := hx
            rw [hdS, shift_boxS w id p ps kS hsnd] at hx'
            rwa [← hdS] at hx'
          · rw [(shift_other w id p ps kS d hd hdS).2.1] at hx
            exact hx
        rcases hT.msgOwner d p.sender
            (Or.inl ⟨x, hx0, by rw [hc] at hcf; exact hcf⟩) with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hph] at hk
          cases hk
        · have hk' := hk
          rw [hph] at hk'
          injection hk' with hd0
          exact False.elim (hd hd0.symm)
    · have hq0 := shift_old_park w id p ps kS hpark hsnd d q hq
      obtain ⟨hseq, k, hk⟩ := (hT.parkFrom d q hq0 p.sender).mp (by rw [hc] at hcf; exact hcf)
      have hk' := hk
      rw [hph] at hk'
      injection hk' with hd0
      have hqN : q ∈ ps := by
        have hq' := hq
        rw [← hd0] at hq'
        rw [shift_parkId w id p ps kS hsnd] at hq'
        exact hq'
      have hsame := hM.uniq id id q p
        (by rw [← hd0] at hq0; exact hq0) (by rw [hpark]; exact List.Mem.head _) hseq
      rw [hsame.2] at hqN
      have hnd := hM.once id
      rw [hpark] at hnd
      exact False.elim ((List.nodup_cons.mp hnd).1 hqN)
  · have hmail0 := (shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc).mp hm
    rcases hT.msgOwner d c hmail0 with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, by
        by_cases hi : c = id
        · have h := hk
          rw [hi] at h
          rw [hi, shift_phId w id p ps kS hsnd]
          exact h
        · rw [(shift_other w id p ps kS c hi hc).1]
          exact hk⟩
    · exact Or.inr ⟨k, by
        by_cases hi : c = id
        · have h := hk
          rw [hi] at h
          rw [hi, shift_phId w id p ps kS hsnd]
          exact h
        · rw [(shift_other w id p ps kS c hi hc).1]
          exact hk⟩

theorem shift_oweOwner (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) :
    ∀ d c, handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∨
        replyPending c ((shiftWorld w id p ps kS).st d).phase →
      ∃ k, ((shiftWorld w id p ps kS).st c).phase = .awaitReply d k := by
  intro d c ho
  have hold : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
    rcases ho with h | h
    · exact Or.inl ((shift_owes w id p ps kS hph hsnd d c).mp h)
    · exact Or.inr ((shift_pending w id p ps kS hph hsnd d c).mp h)
  obtain ⟨k, hk⟩ := hT.oweOwner d c hold
  have hc : c ≠ p.sender := by
    intro heq
    simp [heq, hph] at hk
  by_cases hi : c = id
  · exact ⟨k, by rw [hi, shift_phId w id p ps kS hsnd, ← hi]; exact hk⟩
  · exact ⟨k, by rw [(shift_other w id p ps kS c hi hc).1]; exact hk⟩

theorem shift_stamps (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hsnd : p.sender ≠ id) (i : InstId) :
    ((shiftWorld w id p ps kS).st i).oweId = (w.st i).oweId ∧
      ((shiftWorld w id p ps kS).st i).waitId = (w.st i).waitId := by
  by_cases hs : i = p.sender
  · simp only [shiftWorld, shiftBase, setActor, hs]
    split <;> simp
  · by_cases hid : i = id
    · have hne : ¬ id = p.sender := fun h => hs (hid ▸ h)
      simp [shiftWorld, shiftBase, setActor, hid, hne]
    · simp [shiftWorld, shiftBase, setActor, hs, hid]

theorem shift_owedId (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) :
    ∀ d c, handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∨
        replyPending c ((shiftWorld w id p ps kS).st d).phase →
      ((shiftWorld w id p ps kS).st d).oweId = some ((shiftWorld w id p ps kS).st c).waitId := by
  intro d c ho
  have hold : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
    rcases ho with h | h
    · exact Or.inl ((shift_owes w id p ps kS hph hsnd d c).mp h)
    · exact Or.inr ((shift_pending w id p ps kS hph hsnd d c).mp h)
  simpa [(shift_stamps w id p ps kS hsnd d).1, (shift_stamps w id p ps kS hsnd c).2] using
    hT.owedId d c hold

/-- A parked call moves onto the box and its sender enters `awaitReply` together. -/
theorem parked_tail_call (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (kS : Cont) (name : String) (s : InstId) (hT : CallTagInv w) (hM : MailInv w)
    (hpark : (w.st id).parked = p :: ps) (hph : (w.st p.sender).phase = .parked id true kS)
    (hsnd : p.sender ≠ id) :
    CallTagInv (setActor (creditSender (shiftBase w id p ps) name s) p.sender
      (resumeSender ((creditSender (shiftBase w id p ps) name s).st p.sender) true id)) := by
  have hmem : p ∈ (w.st id).parked := by simp [hpark]
  have hfrom : p.msg.callFrom = some p.sender :=
    (hT.parkFrom id p hmem p.sender).mpr ⟨rfl, kS, hph⟩
  have hF : CallTagInv (shiftWorld w id p ps kS) :=
    ⟨shift_awaiting w id p ps kS hT hpark hph hfrom hsnd,
     shift_parkedCall w id p ps kS hT hpark hph hsnd,
     shift_msgOwner w id p ps kS hT hM hpark hph hfrom hsnd,
     shift_oweOwner w id p ps kS hT hph hsnd,
     shift_prio w id p ps kS hT hsnd,
     shift_sole w id p ps kS hT hpark hfrom hsnd,
     shift_parkFrom w id p ps kS hT hM hpark hph hsnd,
     shift_parkedOnly w id p ps kS hT hpark hph hfrom hsnd,
     shift_owedId w id p ps kS hT hph hsnd⟩
  have hC := credit_tag (shiftWorld w id p ps kS) name s hF
  apply call_tag_copy (creditSender (shiftWorld w id p ps kS) name s) _ hC
  intro i
  by_cases hi : i = p.sender
  · have hphC : ((creditSender (shiftBase w id p ps) name s).st p.sender).phase =
        .parked id true kS := by
      have hbase : ((shiftBase w id p ps).st p.sender).phase = (w.st p.sender).phase := by
        simp [shiftBase, setActor, hsnd]
      simpa [hbase, hph] using (credit_same (shiftBase w id p ps) name s p.sender).2.2.1
    have hres : resumeSender ((creditSender (shiftBase w id p ps) name s).st p.sender) true id =
        { ((creditSender (shiftBase w id p ps) name s).st p.sender) with phase := .awaitReply id kS } := by
      simp [resumeSender, hphC]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hi]
      simp [setActor, hres]
      rw [(credit_same (shiftWorld w id p ps kS) name s p.sender).2.2.1]
      exact (shift_phF w id p ps kS hsnd).symm
    · rw [hi]
      have hb := (credit_same (shiftBase w id p ps) name s p.sender).1
      simp [setActor, hres, hb, shift_boxS w id p ps kS hsnd,
        (credit_same (shiftWorld w id p ps kS) name s p.sender).1]
      simp [shiftBase, setActor, hsnd]
    · rw [hi]
      have hp := (credit_same (shiftBase w id p ps) name s p.sender).2.1
      simp [setActor, hres, hp, shift_parkS w id p ps kS hsnd,
        (credit_same (shiftWorld w id p ps kS) name s p.sender).2.1]
      simp [shiftBase, setActor, hsnd]
    · rw [hi]
      have hq := (credit_same (shiftBase w id p ps) name s p.sender).2.2.2
      simp [setActor, hres, hq, shift_prioS w id p ps kS hsnd,
        (credit_same (shiftWorld w id p ps kS) name s p.sender).2.2.2]
      simp [shiftBase, setActor, hsnd]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [setActor, hi, (credit_same (shiftBase w id p ps) name s i).2.2.1,
        (credit_same (shiftWorld w id p ps kS) name s i).2.2.1]
      by_cases hid : i = id
      · simp [setActor, hid, shiftBase, shift_phId w id p ps kS hsnd]
      · simp [setActor, hid, shiftBase, (shift_other w id p ps kS i hid hi).1]
    · simp [setActor, hi, (credit_same (shiftBase w id p ps) name s i).1,
        (credit_same (shiftWorld w id p ps kS) name s i).1]
      by_cases hid : i = id
      · simp [setActor, hid, shiftBase, shift_boxId w id p ps kS hsnd]
      · simp [setActor, hid, shiftBase, (shift_other w id p ps kS i hid hi).2.1]
    · simp [setActor, hi, (credit_same (shiftBase w id p ps) name s i).2.1,
        (credit_same (shiftWorld w id p ps kS) name s i).2.1]
      by_cases hid : i = id
      · simp [setActor, hid, shiftBase, shift_parkId w id p ps kS hsnd]
      · simp [setActor, hid, shiftBase, (shift_other w id p ps kS i hid hi).2.2.1]
    · simp [setActor, hi, (credit_same (shiftBase w id p ps) name s i).2.2.2,
        (credit_same (shiftWorld w id p ps kS) name s i).2.2.2]
      by_cases hid : i = id
      · simp [setActor, hid, shiftBase, shift_prioId w id p ps kS hsnd]
      · simp [setActor, hid, shiftBase, (shift_other w id p ps kS i hid hi).2.2.2]
  exact lifeKeep_of_eq (fun j => by
    by_cases hj : j = p.sender
    · rw [hj, set_resume_life,
        (credit_phase_life (shiftBase w id p ps) name s p.sender).2,
        (credit_phase_life (shiftWorld w id p ps kS) name s p.sender).2]
      simp [shiftWorld, shiftBase, setActor, hsnd]
    · rw [set_resume_life_other (creditSender (shiftBase w id p ps) name s) p.sender j _ true id hj,
        (credit_phase_life (shiftBase w id p ps) name s j).2,
        (credit_phase_life (shiftWorld w id p ps kS) name s j).2]
      by_cases hid : j = id
      · have hne : id ≠ p.sender := hsnd.symm
        simp [shiftWorld, shiftBase, setActor, hid, hne]
      · simp [shiftWorld, shiftBase, setActor, hid, hj])
  · let wF := setActor (creditSender (shiftBase w id p ps) name s) p.sender
      (resumeSender ((creditSender (shiftBase w id p ps) name s).st p.sender) true id)
    let base := shiftBase w id p ps
    intro d c ho
    have hphC : ((creditSender base name s).st p.sender).phase = .parked id true kS := by
      have hbasePh : (base.st p.sender).phase = (w.st p.sender).phase := by
        simp [base, shiftBase, setActor, hsnd]
      simpa [hbasePh, hph] using (credit_same base name s p.sender).2.2.1
    have hres : resumeSender ((creditSender base name s).st p.sender) true id =
        { ((creditSender base name s).st p.sender) with phase := .awaitReply id kS } := by
      simp [resumeSender, hphC]
    have hs : ∀ i, (wF.st i).oweId = (w.st i).oweId ∧ (wF.st i).waitId = (w.st i).waitId := by
      intro i
      have hbaseS := stamp_set w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }
        (by simp) (by simp)
      by_cases hi : i = p.sender
      · rw [hi]
        have hr := resume_stamps ((creditSender base name s).st p.sender) true id
        have hc := credit_stamps_ow base name s p.sender
        refine ⟨?_, ?_⟩
        · simp only [wF, setActor_self]
          rw [hr.1, hc.1]
          simpa [base, shiftBase, setActor] using (hbaseS p.sender).1
        · simp only [wF, setActor_self]
          rw [hr.2, hc.2]
          simpa [base, shiftBase, setActor] using (hbaseS p.sender).2
      · have hc := credit_stamps_ow base name s i
        have hfi : (wF.st i).oweId = ((creditSender base name s).st i).oweId ∧
            (wF.st i).waitId = ((creditSender base name s).st i).waitId := by
          simp [wF, base, setActor, hi]
        refine ⟨?_, ?_⟩
        · rw [hfi.1, hc.1]
          simpa [base, shiftBase, setActor] using (hbaseS i).1
        · rw [hfi.2, hc.2]
          simpa [base, shiftBase, setActor] using (hbaseS i).2
    have hcred := credit_stamps_ow (shiftWorld w id p ps kS) name s
    have hshift := fun i => shift_stamps w id p ps kS hsnd i
    by_cases hd : d = p.sender
    · have hphF : (wF.st p.sender).phase = .awaitReply id kS := by
        simp [wF, base, setActor, hres]
      have hphW : ((creditSender (shiftWorld w id p ps kS) name s).st p.sender).phase =
          .awaitReply id kS := by
        rw [(credit_same (shiftWorld w id p ps kS) name s p.sender).2.2.1]
        exact shift_phF w id p ps kS hsnd
      have hback : handlerOwes c ((creditSender (shiftWorld w id p ps kS) name s).st d).phase ∨
          replyPending c ((creditSender (shiftWorld w id p ps kS) name s).st d).phase := by
        rw [hd]
        rcases ho with ⟨k0, hk0, hs0, hn⟩ | ⟨k0, hk0, hs0, hn⟩
        · have hkF : carriedCont (wF.st p.sender).phase = some k0 := by
            simpa [wF, hd] using hk0
          rw [hphF, carriedCont] at hkF
          injection hkF with hkF
          exact Or.inl ⟨k0, by simp [hphW, carriedCont, hkF.symm], hs0, hn⟩
        · have hkF : carriedCont (wF.st p.sender).phase = some k0 := by
            simpa [wF, hd] using hk0
          rw [hphF, carriedCont] at hkF
          injection hkF with hkF
          exact Or.inr ⟨k0, by simp [hphW, carriedCont, hkF.symm], hs0, hn⟩
      rw [(hs d).1, (hs c).2]
      exact (by simpa [(hcred d).1, (hcred c).2, (hshift d).1, (hshift c).2] using
        hC.owedId d c hback)
    · have hphEq : (wF.st d).phase =
          ((creditSender (shiftWorld w id p ps kS) name s).st d).phase := by
        simp only [wF]
        rw [setActor_other _ _ _ _ hd]
        rw [(credit_same (shiftBase w id p ps) name s d).2.2.1]
        rw [(credit_same (shiftWorld w id p ps kS) name s d).2.2.1]
        by_cases hid : d = id <;> simp [shiftBase, shiftWorld, setActor, hid, hd, hsnd.symm]
      have hback : handlerOwes c ((creditSender (shiftWorld w id p ps kS) name s).st d).phase ∨
          replyPending c ((creditSender (shiftWorld w id p ps kS) name s).st d).phase := by
        simpa [← hphEq] using ho
      rw [(hs d).1, (hs c).2]
      exact (by simpa [(hcred d).1, (hcred c).2, (hshift d).1, (hshift c).2] using
        hC.owedId d c hback)

/-- After the parked head has been appended to the box, resume a non-call sender. -/
theorem parked_tail_send (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (kS : Cont) (name : String) (s : InstId) (hT : CallTagInv w)
    (hpark : (w.st id).parked = p :: ps) (hph : (w.st p.sender).phase = .parked id false kS)
    (hsnd : p.sender ≠ id) :
    let wM := setActor w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }
    let wC := creditSender wM name s
    CallTagInv (setActor wC p.sender (resumeSender (wC.st p.sender) false id)) := by
  have hplain : p.msg.callFrom = none := by
    cases hcf : p.msg.callFrom with
    | none => rfl
    | some s0 =>
      obtain ⟨hs, _, hk⟩ := (hT.parkFrom id p (by simp [hpark]) s0).mp hcf
      rw [← hs, hph] at hk
      cases hk
  have hM := move_parked_msg w id p ps hT hpark hplain
  let wM := setActor w id { (w.st id) with box := (w.st id).box ++ [p.msg], parked := ps }
  have hC := credit_tag wM name s hM
  let wC := creditSender wM name s
  have hphC : (wC.st p.sender).phase = .parked id false kS := by
    have hphM : (wM.st p.sender).phase = (w.st p.sender).phase := by
      simp [wM, setActor, hsnd]
    simpa [wC, hphM, hph] using (credit_same wM name s p.sender).2.2.1
  simpa using resume_send_tag wC p.sender id kS hC hphC

theorem ite_shadow {α : Type} (p : Prop) [Decidable p] (a b d : α) :
    (if p then a else if p then b else d) = if p then a else d := by
  by_cases h : p <;> simp [h]

theorem setActor_same (w : World) (id : InstId) (a b : Actor) :
    setActor (setActor w id a) id b = setActor w id b := by
  simp [setActor]
  funext i
  by_cases hi : i = id <;> simp [hi]

/-- A successful bulk receive preserves call tags. -/
theorem recvBulk_tag (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (hM : MailInv w) (hT : CallTagInv w) (h : receiveBulk I w id = some w') :
    CallTagInv w' := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    have hidle : (w.st id).phase = .idle := by
      by_cases hp : (w.st id).phase = .idle
      · exact hp
      · exact absurd (Or.inr hp) hready
    have hlive : (w.st id).life = .alive := by
      by_cases hl : (w.st id).life = .alive
      · exact hl
      · exact absurd (Or.inl hl) hready
    cases hbox : (w.st id).box with
    | nil =>
      cases hp : (w.st id).parked with
      | nil => simp [hbox, hp] at h
      | cons p ps =>
        simp [hbox, hp] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          obtain ⟨kS, hph⟩ := hM.fwd id p (by simp [hp])
          have hsnd : p.sender ≠ id := by
            intro heq
            simp [heq, hidle] at hph
          have hdel' : deliver I w id ({ (w.st id) with parked := ps }) p.msg = some (w1, a1) := by
            simp [hbox]
            exact hdel
          cases hc : p.isCall with
          | false =>
            have hfrom := (entry_align w hT hM id p (by simp [hp])).2 hc
            rw [hc] at hph
            simpa [hc] using deliver_parked_send I w w1 id p ps a1 kS hM hT hidle hbox hp hc
              hfrom hph hdel'
          | true =>
            have hfrom := (entry_align w hT hM id p (by simp [hp])).1 hc
            rw [hc] at hph
            simpa [hc] using deliver_parked_tag I hL w w1 id p ps a1 kS hM hT hidle hbox hp
              hfrom hph hdel'
    | cons m ms =>
      cases hp : (w.st id).parked with
      | nil =>
        simp [hbox, hp] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hdel' : deliver I w id ({ (w.st id) with box := ms }) m = some (w1, a1) := by
            simp [hp]
            exact hdel
          exact bulk_box I hL w w1 id m ms a1 hM hT hidle hp hbox hdel'
      | cons p ps =>
        simp [hbox, hp] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hdel' : deliver I w id ({ (w.st id) with box := ms }) m = some (w1, a1) := by
            simp [hp]
            exact hdel
          have hst : ∀ i, w1.st i = w.st i := fun i =>
            deliver_st I w id ({ (w.st id) with box := ms }) m w1 a1 i hdel'
          obtain ⟨kS, hph⟩ := hM.fwd id p (by simp [hp])
          have hsnd : p.sender ≠ id := by
            intro heq
            simp [heq, hidle] at hph
          have hparkA : ((setActor w1 id a1).st id).parked = p :: ps := by
            cases hcm : m.callFrom with
            | none =>
              have hplain := deliver_plain I w id ({ (w.st id) with box := ms }) m w1 a1 hdel' hcm
              simp [setActor, hplain.2.1, hp]
            | some c =>
              have hcall := deliver_call I hL w id ({ (w.st id) with box := ms }) m w1 a1 c hdel' hcm
              simp [setActor, hcall.2.1, hp]
          have hphA : ((setActor w1 id a1).st p.sender).phase = (w.st p.sender).phase := by
            simp [setActor, hsnd, hst]
          cases hcm : m.callFrom with
          | none =>
            have hplain := deliver_plain I w id ({ (w.st id) with box := ms }) m w1 a1 hdel' hcm
            have hI := install_plain_kept w w1 id a1 m ms hT hidle hst
              (by simpa using hplain.1) (by simpa [hp] using hplain.2.1)
              (by simpa using hplain.2.2.1)
              (by simpa using (deliver_life I w id ({ (w.st id) with box := ms }) m w1 a1 hdel').1)
              hplain.2.2.2 hbox hcm
            cases hc : p.isCall with
            | false =>
              rw [hc] at hph
              have hphS : ((setActor w1 id a1).st p.sender).phase = .parked id false kS := by
                rw [hphA]; exact hph
              have := parked_tail_send (setActor w1 id a1) id p ps kS (tname id) m.sender hI
                hparkA hphS hsnd
              simpa [setActor_same, setActor, ite_shadow, hc] using this
            | true =>
              rw [hc] at hph
              have hphS : ((setActor w1 id a1).st p.sender).phase = .parked id true kS := by
                rw [hphA]; exact hph
              have hnot : ∀ d (b : Bool) k, a1.phase ≠ .parked d b k := by
                intro d b k hk
                rcases hplain.2.2.2 with hIph | ⟨_, hk', _⟩
                · rw [hIph] at hk
                  cases hk
                · rw [hk'] at hk
                  cases hk
              have hMail := mail_install w w1 id a1 hM hst hidle hlive
                (by simpa [hp] using hplain.2.1) hnot
              have := parked_tail_call (setActor w1 id a1) id p ps kS (tname id) m.sender hI
                hMail hparkA hphS hsnd
              simpa [setActor_same, setActor, ite_shadow, shiftBase, hc] using this
          | some c =>
            have hcall := deliver_call I hL w id ({ (w.st id) with box := ms }) m w1 a1 c hdel' hcm
            obtain ⟨kH, hrun, hshape, _, hother⟩ := hcall.2.2.2.2.2
            obtain ⟨kw, hownc⟩ := box_awaits w hT id m c (by simp [hbox]) hcm
            have hI := install_call_kept w w1 id a1 m ms c kH kw hT hidle hst
              (by simpa using hcall.1) (by simpa [hp] using hcall.2.1)
              (by simpa using hcall.2.2.1)
              (by simpa using (deliver_life I w id ({ (w.st id) with box := ms }) m w1 a1 hdel').1)
              hbox hcm hrun hshape hother hownc (by simpa using hcall.2.2.2.2.1)
            cases hc : p.isCall with
            | false =>
              rw [hc] at hph
              have hphS : ((setActor w1 id a1).st p.sender).phase = .parked id false kS := by
                rw [hphA]; exact hph
              have := parked_tail_send (setActor w1 id a1) id p ps kS (tname id) m.sender hI
                hparkA hphS hsnd
              simpa [setActor_same, setActor, ite_shadow, hc] using this
            | true =>
              rw [hc] at hph
              have hphS : ((setActor w1 id a1).st p.sender).phase = .parked id true kS := by
                rw [hphA]; exact hph
              have hnot : ∀ d (b : Bool) k, a1.phase ≠ .parked d b k := by
                intro d b k hk
                rw [hrun] at hk
                cases hk
              have hMail := mail_install w w1 id a1 hM hst hidle hlive
                (by simpa [hp] using hcall.2.1) hnot
              have := parked_tail_call (setActor w1 id a1) id p ps kS (tname id) m.sender hI
                hMail hparkA hphS hsnd
              simpa [setActor_same, setActor, ite_shadow, shiftBase, hc] using this

/-- A running handler owes a caller exactly when its continuation still has that reply. -/
theorem shape_split (c : InstId) (k : Cont) :
    handlerOwes c (.run k) ∨ replyPending c (.run k) ↔ replyShape c k := by
  constructor
  · intro h
    rcases h with ⟨k0, hk, hs, _⟩ | ⟨k0, hk, hs, _⟩
    · simp [carriedCont] at hk
      cases hk
      exact hs
    · simp [carriedCont] at hk
      cases hk
      exact hs
  · intro hs
    cases hhead : k.rest with
    | nil => exact absurd hhead (replyShape_nonempty c k hs)
    | cons e es =>
      by_cases he : e = .reply
      · rw [he] at hhead
        exact Or.inr ⟨k, by simp [carriedCont], hs, by simp [nextIsReply, hhead]⟩
      · exact Or.inl ⟨k, by simp [carriedCont], hs, by
          intro hn
          cases e with
          | reply => exact absurd rfl he
          | _ => simp [nextIsReply, hhead] at hn⟩

/-- Dropping a head that is neither the reply nor `terminate` keeps the reply shape. -/
theorem replyShape_tail (c : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hrest : k.rest = e :: es) (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    replyShape c k ↔ replyShape c (afterHead k) := by
  constructor
  · intro hs
    exact replyShape_after c k e es hrest hs hne
  · intro hs
    obtain ⟨hto, hcount, hterm0⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · simpa [afterHead, hrest] using hto
    · simpa [afterHead, hrest, replyCount_ne_reply e es hne] using hcount
    · cases e with
      | reply => exact absurd rfl hne
      | terminate => exact absurd rfl hterm
      | _ =>
        have hterm0' : terminateBeforeReply es = false := by
          simpa [afterHead, hrest] using hterm0
        simpa [terminateBeforeReply, hrest] using hterm0'

/-- The reply obligation is unchanged when a non-reply, non-terminate head is consumed. -/
theorem tail_duty (a : Actor) (k : Cont) (e : Eff) (es : List Eff) (c : InstId)
    (hrest : k.rest = e :: es) (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    handlerOwes c (proceed a (afterHead k)).phase ∨ replyPending c (proceed a (afterHead k)).phase ↔
      handlerOwes c (.run k) ∨ replyPending c (.run k) := by
  have hshape := replyShape_tail c k e es hrest hne hterm
  have hsplit := shape_split c k
  cases hes : es with
  | nil =>
    have hidle : (proceed a (afterHead k)).phase = .idle := by
      simp [proceed, afterHead, hrest, hes]
    constructor
    · intro h
      simp [hidle, handlerOwes, replyPending, carriedCont] at h
    · intro h
      have hc := (hsplit.mp h).2.1
      cases e with
      | reply => exact absurd rfl hne
      | _ => simp [replyCount, hrest, hes] at hc
  | cons e2 es2 =>
    have hrun : (proceed a (afterHead k)).phase = .run (afterHead k) := by
      simp [proceed, afterHead, hrest, hes]
    have hsplit' : handlerOwes c (.run (afterHead k)) ∨ replyPending c (.run (afterHead k)) ↔
        replyShape c (afterHead k) := shape_split c (afterHead k)
    constructor
    · intro h
      exact hsplit.mpr (hshape.mpr (hsplit'.mp (by simpa [hrun] using h)))
    · intro h
      exact (by simpa [hrun] using hsplit'.mpr (hshape.mp (hsplit.mp h)))

/-- Consuming a non-reply keeps the owed id: the tail owes the same caller, or nobody. -/
theorem owed_tail (w : World) (id : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st id).phase = .run k) (hrest : k.rest = e :: es)
    (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    ∀ d c, handlerOwes c ((setActor w id (proceed (w.st id) (afterHead k))).st d).phase ∨
        replyPending c ((setActor w id (proceed (w.st id) (afterHead k))).st d).phase →
      ((setActor w id (proceed (w.st id) (afterHead k))).st d).oweId =
        some ((setActor w id (proceed (w.st id) (afterHead k))).st c).waitId := by
  intro d c ho
  have hs := stamp_set w id (proceed (w.st id) (afterHead k))
    (proceed_stamps _ _).1 (proceed_stamps _ _).2
  by_cases hd : d = id
  · rw [hd] at ho
    have hback : handlerOwes c (w.st id).phase ∨ replyPending c (w.st id).phase := by
      have hdu := (tail_duty (w.st id) k e es c hrest hne hterm).mp (by simpa [setActor] using ho)
      rwa [hph]
    rw [hd]
    simpa [(hs id).1, (hs c).2] using hT.owedId id c hback
  · have hback : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [setActor, hd] using ho
    simpa [(hs d).1, (hs c).2] using hT.owedId d c hback

/-- A finished handler is idle, so it owes nobody, and it was not itself awaiting. -/
theorem owed_idle (w : World) (id : InstId) (k : Cont) (hT : CallTagInv w)
    (hph : (w.st id).phase = .run k) (hrest : k.rest = []) :
    ∀ d c, handlerOwes c ((setActor w id
        ({ (w.st id) with phase := .idle, typestate := k.toState })).st d).phase ∨
        replyPending c ((setActor w id
        ({ (w.st id) with phase := .idle, typestate := k.toState })).st d).phase →
      ((setActor w id ({ (w.st id) with phase := .idle, typestate := k.toState })).st d).oweId =
        some ((setActor w id
          ({ (w.st id) with phase := .idle, typestate := k.toState })).st c).waitId := by
  intro d c ho
  by_cases hd : d = id
  · rw [hd] at ho
    rcases ho with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> simp [setActor, carriedCont] at hk
  · by_cases hc : c = id
    · rw [hc] at ho
      have hpre : handlerOwes id (w.st d).phase ∨ replyPending id (w.st d).phase := by
        simpa [setActor, hd] using ho
      obtain ⟨k', hk⟩ := hT.oweOwner d id hpre
      simp [hph] at hk
    · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        simpa [setActor, hd] using ho
      simpa [setActor, hd, hc] using hT.owedId d c hpre

/-- Consuming a head that is neither the reply nor `terminate` preserves call tags.
The runner stays in `.run` or becomes idle; nobody's mail moves. -/
theorem run_tail_tag (w : World) (id : InstId) (k : Cont) (e : Eff) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st id).phase = .run k) (hrest : k.rest = e :: es)
    (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    CallTagInv (setActor w id (proceed (w.st id) (afterHead k))) := by
  let w' := setActor w id (proceed (w.st id) (afterHead k))
  have hst (i : InstId) (hi : i ≠ id) : w'.st i = w.st i := by simp [w', setActor, hi]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hi : i = id
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hi : i = id
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  have hprioL (i : InstId) : (w'.st i).prio = (w.st i).prio := by
    by_cases hi : i = id
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  apply call_tag_duty w w' hT
  · intro d c
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · exact Or.inl ⟨m, by rw [← hbox d]; exact hm, hc⟩
      · exact Or.inr ⟨p, by rw [← hparked d]; exact hp, hc⟩
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · exact Or.inl ⟨m, by rw [hbox d]; exact hm, hc⟩
      · exact Or.inr ⟨p, by rw [hparked d]; exact hp, hc⟩
  · intro i c
    by_cases hi : i = id
    · rw [hi]
      have hnew : (w'.st id).phase = (proceed (w.st id) (afterHead k)).phase := by
        simp [w', setActor]
      have hold : (w.st id).phase = .run k := hph
      constructor
      · intro h
        have h' := (tail_duty (w.st id) k e es c hrest hne hterm).mp (by simpa [hnew] using h)
        rwa [hph]
      · intro h
        have h' := (tail_duty (w.st id) k e es c hrest hne hterm).mpr (by simpa [hold] using h)
        simpa [hnew] using h'
    · have hpe : (w'.st i).phase = (w.st i).phase := by rw [hst i hi]
      constructor
      · intro h
        rcases h with ho | hp
        · exact Or.inl (by simpa [← hpe] using ho)
        · exact Or.inr (by simpa [← hpe] using hp)
      · intro h
        rcases h with ho | hp
        · exact Or.inl (by simpa [hpe] using ho)
        · exact Or.inr (by simpa [hpe] using hp)
  · intro c d kA hph'
    by_cases hc : c = id
    · cases hes : es with
      | nil => simp [w', hc, setActor, proceed, afterHead, hrest, hes] at hph'
      | cons _ _ => simp [w', hc, setActor, proceed, afterHead, hrest, hes] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · cases hes : es with
      | nil => simp [w', hc, setActor, proceed, afterHead, hrest, hes] at hph'
      | cons _ _ => simp [w', hc, setActor, proceed, afterHead, hrest, hes] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprioL i] at hm; exact hm)
  · intro d c
    unfold soleCall
    rw [hbox d, hparked d]
    exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT hparked
      (by
        intro s0 d0 k0
        constructor
        · intro hk
          by_cases hs0 : s0 = id
          · cases hes : es with
            | nil => simp [w', hs0, setActor, proceed, afterHead, hrest, hes] at hk
            | cons _ _ => simp [w', hs0, setActor, proceed, afterHead, hrest, hes] at hk
          · simpa [hst s0 hs0] using hk
        · intro hk
          by_cases hs0 : s0 = id
          · simp [hs0, hph] at hk
          · simpa [← hst s0 hs0] using hk)
      d p hp s
  · intro c d kA hk
    exact parkedOnly_transport w w' hT hparked
      (by intro i m hm; rw [hbox i] at hm; exact hm)
      (by
        intro c0 d0 k0 hk0
        by_cases hc0 : c0 = id
        · cases hes : es with
          | nil => simp [w', hc0, setActor, proceed, afterHead, hrest, hes] at hk0
          | cons _ _ => simp [w', hc0, setActor, proceed, afterHead, hrest, hes] at hk0
        · simpa [hst c0 hc0] using hk0)
      c d kA hk
      (by simpa [w'] using life_setActor w id (proceed (w.st id) (afterHead k)) (proceed_life _ _))
  · simpa [w'] using life_setActor w id (proceed (w.st id) (afterHead k)) (proceed_life _ _)
  · exact fun d c ho => owed_tail w id k e es hT hph hrest hne hterm d c ho

/-- An empty continuation goes idle and was not still holding a reply. -/
theorem run_done_tag (w : World) (id : InstId) (k : Cont) (hT : CallTagInv w)
    (hph : (w.st id).phase = .run k) (hrest : k.rest = []) :
    CallTagInv (setActor w id { (w.st id) with phase := .idle, typestate := k.toState }) := by
  let w' := setActor w id { (w.st id) with phase := .idle, typestate := k.toState }
  have hst (i : InstId) (hi : i ≠ id) : w'.st i = w.st i := by simp [w', setActor, hi]
  have hsame (i : InstId) : (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked ∧
      (w'.st i).prio = (w.st i).prio := by
    by_cases hi : i = id
    · simp [w', hi, setActor]
    · simp [hst i hi]
  apply call_tag_stable w w' hT
  · intro d c
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · exact Or.inl ⟨m, by rw [← (hsame d).1]; exact hm, hc⟩
      · exact Or.inr ⟨p, by rw [← (hsame d).2.1]; exact hp, hc⟩
    · intro hm
      rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · exact Or.inl ⟨m, by rw [(hsame d).1]; exact hm, hc⟩
      · exact Or.inr ⟨p, by rw [(hsame d).2.1]; exact hp, hc⟩
  · intro i c
    by_cases hi : i = id
    · constructor
      · intro h
        simp [w', hi, setActor, handlerOwes, carriedCont] at h
      · intro ⟨k0, hk, hs, _⟩
        simp [hi, carriedCont, hph] at hk
        cases hk
        exact False.elim (replyShape_nonempty c k hs hrest)
    · simp [hst i hi]
  · intro i c
    by_cases hi : i = id
    · constructor
      · intro h
        simp [w', hi, setActor, replyPending, carriedCont] at h
      · intro ⟨k0, hk, hs, _⟩
        simp [hi, carriedCont, hph] at hk
        cases hk
        exact False.elim (replyShape_nonempty c k hs hrest)
    · simp [hst i hi]
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [w', hc, setActor] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [w', hc, setActor] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro i m hm
    exact hT.prioPlain i m (by rw [(hsame i).2.2] at hm; exact hm)
  · intro d c
    unfold soleCall
    rw [(hsame d).1, (hsame d).2.1]
    exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT (fun i => (hsame i).2.1)
      (by
        intro s0 d0 k0
        constructor
        · intro hk
          by_cases hs0 : s0 = id
          · simp [w', hs0, setActor] at hk
          · simpa [hst s0 hs0] using hk
        · intro hk
          by_cases hs0 : s0 = id
          · simp [hs0, hph] at hk
          · simpa [← hst s0 hs0] using hk)
      d p hp s
  · intro c d kA hk
    exact parkedOnly_transport w w' hT (fun i => (hsame i).2.1)
      (by intro i m hm; rw [(hsame i).1] at hm; exact hm)
      (by
        intro c0 _ _ hk0
        by_cases hc0 : c0 = id
        · simp [w', hc0, setActor] at hk0
        · simpa [hst c0 hc0] using hk0)
      c d kA hk
      (by simpa [w'] using life_setActor w id ({ (w.st id) with phase := .idle, typestate := k.toState }) (by simp))
  · simpa [w'] using life_setActor w id ({ (w.st id) with phase := .idle, typestate := k.toState }) (by simp)
  · exact fun d c ho => owed_idle w id k hT hph hrest d c ho

/-- An obligation is exactly the reply shape of the continuation the phase carries. -/
theorem carried_duty (c : InstId) (ph : Phase) (k : Cont) (hcar : carriedCont ph = some k) :
    handlerOwes c ph ∨ replyPending c ph ↔ replyShape c k := by
  constructor
  · intro h
    rcases h with ⟨k0, hk, hs, _⟩ | ⟨k0, hk, hs, _⟩
    · rw [hcar] at hk
      cases hk
      exact hs
    · rw [hcar] at hk
      cases hk
      exact hs
  · intro hs
    cases hhead : k.rest with
    | nil => exact absurd hhead (replyShape_nonempty c k hs)
    | cons e es =>
      by_cases he : e = .reply
      · exact Or.inr ⟨k, hcar, hs, by simp [nextIsReply, hhead, he]⟩
      · exact Or.inl ⟨k, hcar, hs, by
          intro hn
          cases e with
          | reply => exact absurd rfl he
          | _ => simp [nextIsReply, hhead] at hn⟩

theorem countCall_pos (ms : List Msg) (c : InstId) (h : countCall ms c ≠ 0) :
    ∃ m, m ∈ ms ∧ m.callFrom = some c := by
  induction ms with
  | nil => simp [countCall] at h
  | cons m ms ih =>
    by_cases hc : m.callFrom = some c
    · exact ⟨m, List.Mem.head _, hc⟩
    · simp [countCall, hc] at h
      obtain ⟨m', hm, hcf⟩ := ih h
      exact ⟨m', List.mem_cons_of_mem _ hm, hcf⟩

theorem countParked_pos (ps : List Parked) (c : InstId) (h : countParkedCall ps c ≠ 0) :
    ∃ p, p ∈ ps ∧ p.msg.callFrom = some c := by
  induction ps with
  | nil => simp [countParkedCall] at h
  | cons p ps ih =>
    by_cases hc : p.msg.callFrom = some c
    · exact ⟨p, List.Mem.head _, hc⟩
    · simp [countParkedCall, hc] at h
      obtain ⟨p', hp, hcf⟩ := ih h
      exact ⟨p', List.mem_cons_of_mem _ hp, hcf⟩

theorem countParkedCall_append (ps : List Parked) (p : Parked) (c : InstId) :
    countParkedCall (ps ++ [p]) c = countParkedCall ps c + countParkedCall [p] c := by
  induction ps with
  | nil => simp [countParkedCall]
  | cons x xs ih => simp [countParkedCall, ih, Nat.add_assoc]

/-- A running actor is not the owner of a call message. -/
theorem run_unnamed (w : World) (hT : CallTagInv w) (s : InstId) (k : Cont)
    (hph : (w.st s).phase = .run k) (d : InstId) : ¬mailCall w d s := by
  intro hm
  rcases hT.msgOwner d s hm with ⟨_, hk⟩ | ⟨_, hk⟩ <;>
    (rw [hph] at hk; cases hk)

theorem run_unnamed_count (w : World) (hT : CallTagInv w) (s : InstId) (k : Cont)
    (hph : (w.st s).phase = .run k) (d : InstId) :
    countCall (w.st d).box s + countParkedCall (w.st d).parked s = 0 := by
  have hm := run_unnamed w hT s k hph d
  have hb : countCall (w.st d).box s = 0 := by
    by_cases hz : countCall (w.st d).box s = 0
    · exact hz
    · exact False.elim (hm (Or.inl (countCall_pos _ _ hz)))
  have hp : countParkedCall (w.st d).parked s = 0 := by
    by_cases hz : countParkedCall (w.st d).parked s = 0
    · exact hz
    · exact False.elim (hm (Or.inr (countParked_pos _ _ hz)))
  simp [hb, hp]

/-- Enqueueing a call from a running sender. The target is alive, so the sender moves
to `awaitReply` with the message in the box, or to `.parked _ true` with a parked
entry. Mail anywhere else is unchanged, and a running sender was not already named. -/
theorem fresh_call_tag (w w' : World) (sender dst : InstId) (msg : Msg) (k kRun : Cont)
    (hT : CallTagInv w) (hM : MailInv w) (hph : (w.st sender).phase = .run kRun)
    (e : Eff) (es : List Eff) (hrest : kRun.rest = e :: es) (hne : e ≠ .reply)
    (hterm : e ≠ .terminate) (hk : k = afterHead kRun) (hfrom : msg.callFrom = some sender)
    (hother : ∀ i, i ≠ sender → (w'.st i).phase = (w.st i).phase)
    (hboxI : ∀ i, i ≠ dst → (w'.st i).box = (w.st i).box)
    (hparkI : ∀ i, i ≠ dst → (w'.st i).parked = (w.st i).parked)
    (hmode :
      ((w'.st sender).phase = .awaitReply dst k ∧ (w'.st dst).box = (w.st dst).box ++ [msg] ∧
          (w'.st dst).parked = (w.st dst).parked) ∨
        ((w'.st sender).phase = .parked dst true k ∧
          (w'.st dst).parked =
            (w.st dst).parked ++ [{ sender := sender, msg := msg, isCall := true }] ∧
          (w'.st dst).box = (w.st dst).box))
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hlive : (w.st dst).life = .alive) (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (howed : ∀ i, (w'.st i).oweId = (w.st i).oweId)
    (hwait : ∀ i, i ≠ sender → (w'.st i).waitId = (w.st i).waitId) :
    CallTagInv w' := by
  have hphS : (w'.st sender).phase = .awaitReply dst k ∨ (w'.st sender).phase = .parked dst true k := by
    rcases hmode with ⟨h, _, _⟩ | ⟨h, _, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hdutyS (c : InstId) :
      handlerOwes c (w'.st sender).phase ∨ replyPending c (w'.st sender).phase ↔
        handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase := by
    have hshape := replyShape_tail c kRun e es hrest hne hterm
    have hold := (shape_split c kRun).trans hshape
    rcases hphS with hawait | hparked
    · have hcar : carriedCont (w'.st sender).phase = some k := by simp [carriedCont, hawait]
      have hnew := carried_duty c (w'.st sender).phase k hcar
      constructor
      · intro h
        have h' := hold.mpr (by rw [← hk]; exact hnew.mp h)
        rwa [hph]
      · intro h
        have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
          rw [hph] at h
          exact h
        exact hnew.mpr (by rw [hk]; exact hold.mp h0)
    · have hcar : carriedCont (w'.st sender).phase = some k := by simp [carriedCont, hparked]
      have hnew := carried_duty c (w'.st sender).phase k hcar
      constructor
      · intro h
        have h' := hold.mpr (by rw [← hk]; exact hnew.mp h)
        rwa [hph]
      · intro h
        have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
          rw [hph] at h
          exact h
        exact hnew.mpr (by rw [hk]; exact hold.mp h0)
  have hmailNe (d c : InstId) (hc : c ≠ sender) : mailCall w' d c ↔ mailCall w d c := by
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨q, hq, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · rw [hd, hboxA, List.mem_append] at hm
            rcases hm with hold | heq
            · exact Or.inl ⟨m, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              injection hcf with heqc
              exact False.elim (hc heqc.symm)
          · rw [hd, hboxP] at hm
            exact Or.inl ⟨m, by rw [hd]; exact hm, hcf⟩
        · rw [hboxI d hd] at hm
          exact Or.inl ⟨m, hm, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · rw [hd, hparkA] at hq
            exact Or.inr ⟨q, by rw [hd]; exact hq, hcf⟩
          · rw [hd, hparkP, List.mem_append] at hq
            rcases hq with hold | heq
            · exact Or.inr ⟨q, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              injection hcf with heqc
              exact False.elim (hc heqc.symm)
        · rw [hparkI d hd] at hq
          exact Or.inr ⟨q, hq, hcf⟩
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨q, hq, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · exact Or.inl ⟨m, by
              rw [hd] at hm
              rw [hd, hboxA]
              exact List.mem_append_left _ hm, hcf⟩
          · exact Or.inl ⟨m, by rw [hd] at hm; rw [hd, hboxP]; exact hm, hcf⟩
        · exact Or.inl ⟨m, by rw [hboxI d hd]; exact hm, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · exact Or.inr ⟨q, by rw [hd] at hq; rw [hd, hparkA]; exact hq, hcf⟩
          · exact Or.inr ⟨q, by
              rw [hd] at hq
              rw [hd, hparkP]
              exact List.mem_append_left _ hq, hcf⟩
        · exact Or.inr ⟨q, by rw [hparkI d hd]; exact hq, hcf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hphA, hboxA, _⟩ | ⟨hphP, _, _⟩
      · rw [hc, hphA] at hph'
        injection hph' with hd _
        refine Or.inl ⟨?_, ?_, ?_⟩
        · exact Or.inl ⟨msg, by
            rw [← hd, hboxA]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl), by rw [← hc] at hfrom; exact hfrom⟩
        · intro ho
          by_cases hdS : d = sender
          · obtain ⟨_, hkO⟩ := hT.oweOwner sender c ((hdutyS c).mp (Or.inl (by rw [hdS] at ho; exact ho)))
            rw [hc, hph] at hkO
            cases hkO
          · have ho0 : handlerOwes c (w.st d).phase := by rw [hother d hdS] at ho; exact ho
            obtain ⟨_, hkO⟩ := hT.oweOwner d c (Or.inl ho0)
            rw [hc, hph] at hkO
            cases hkO
        · intro hp
          by_cases hdS : d = sender
          · obtain ⟨_, hkO⟩ := hT.oweOwner sender c
              ((hdutyS c).mp (Or.inr (by rw [hdS] at hp; exact hp)))
            rw [hc, hph] at hkO
            cases hkO
          · have hp0 : replyPending c (w.st d).phase := by rw [hother d hdS] at hp; exact hp
            obtain ⟨_, hkO⟩ := hT.oweOwner d c (Or.inr hp0)
            rw [hc, hph] at hkO
            cases hkO
      · rw [hc, hphP] at hph'
        cases hph'
    · have hph0 : (w.st c).phase = .awaitReply d kA := by rw [hother c hc] at hph'; exact hph'
      have hpre := hT.awaiting c d kA hph0
      have hmail := hmailNe d c hc
      have hduty : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase ↔
          handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        by_cases hdS : d = sender
        · rw [hdS]
          exact hdutyS c
        · have hpe : (w'.st d).phase = (w.st d).phase := hother d hdS
          constructor
          · intro h
            rcases h with ho | hp
            · exact Or.inl (by simpa [← hpe] using ho)
            · exact Or.inr (by simpa [← hpe] using hp)
          · intro h
            rcases h with ho | hp
            · exact Or.inl (by simpa [hpe] using ho)
            · exact Or.inr (by simpa [hpe] using hp)
      have hxor := handlerOwes_not_pending c (w'.st d).phase
      rcases hpre with h1 | h2 | h3 | h4
      · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
          (not_iff hduty).mpr (fun h => h.elim h1.2.1 h1.2.2)
        exact Or.inl ⟨hmail.mpr h1.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩
      · have hyes := hduty.mpr (Or.inl h2.2.1)
        have hnom := (not_iff hmail).mpr h2.1
        rcases hyes with ho | hp
        · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hnom, fun ho => hxor ho hp, hp⟩))
      · have hyes := hduty.mpr (Or.inr h3.2.2)
        have hnom := (not_iff hmail).mpr h3.1
        rcases hyes with ho | hp
        · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hnom, fun ho => hxor ho hp, hp⟩))
      · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
          (not_iff hduty).mpr (fun h => h.elim h4.2.2.2.1 h4.2.2.2.2)
        exact Or.inr (Or.inr (Or.inr ⟨halted_cast (hlife d) h4.1, (hlife c).trans h4.2.1,
          (not_iff hmail).mpr h4.2.2.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩))
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hphA, _, _⟩ | ⟨hphP, hparkP, hboxP⟩
      · rw [hc, hphA] at hph'
        cases hph'
      · rw [hc, hphP] at hph'
        injection hph' with hd _
        refine Or.inl ⟨?_, ?_, ?_, ?_⟩
        · rw [hlife d, ← hd]
          exact hlive
        · exact Or.inr ⟨{ sender := sender, msg := msg, isCall := true }, by
            rw [← hd, hparkP]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl), by
            rw [← hc] at hfrom
            exact hfrom⟩
        · intro ho
          by_cases hdS : d = sender
          · obtain ⟨_, hkO⟩ := hT.oweOwner sender c ((hdutyS c).mp (Or.inl (by rw [hdS] at ho; exact ho)))
            rw [hc, hph] at hkO
            cases hkO
          · have ho0 : handlerOwes c (w.st d).phase := by rw [hother d hdS] at ho; exact ho
            obtain ⟨_, hkO⟩ := hT.oweOwner d c (Or.inl ho0)
            rw [hc, hph] at hkO
            cases hkO
        · intro hp
          by_cases hdS : d = sender
          · obtain ⟨_, hkO⟩ := hT.oweOwner sender c
              ((hdutyS c).mp (Or.inr (by rw [hdS] at hp; exact hp)))
            rw [hc, hph] at hkO
            cases hkO
          · have hp0 : replyPending c (w.st d).phase := by rw [hother d hdS] at hp; exact hp
            obtain ⟨_, hkO⟩ := hT.oweOwner d c (Or.inr hp0)
            rw [hc, hph] at hkO
            cases hkO
    · have hph0 : (w.st c).phase = .parked d true kA := by rw [hother c hc] at hph'; exact hph'
      rcases hT.parkedCall c d kA hph0 with ⟨hl, hm, ho, hp⟩ | ⟨hl, hnm, ho, hp⟩
      · refine Or.inl ⟨by rw [hlife d]; exact hl, (hmailNe d c hc).mpr hm, ?_, ?_⟩
        · intro hnew
          have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
            fun h => h.elim ho hp
          by_cases hdS : d = sender
          · have hback := (hdutyS c).mp (by rw [hdS] at hnew; exact Or.inl hnew)
            rw [← hdS] at hback
            exact hno hback
          · have ho0 : handlerOwes c (w.st d).phase := by rw [hother d hdS] at hnew; exact hnew
            exact ho ho0
        · intro hnew
          have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
            fun h => h.elim ho hp
          by_cases hdS : d = sender
          · have hback := (hdutyS c).mp (by rw [hdS] at hnew; exact Or.inr hnew)
            rw [← hdS] at hback
            exact hno hback
          · have hp0 : replyPending c (w.st d).phase := by rw [hother d hdS] at hnew; exact hnew
            exact hp hp0
      · refine Or.inr ⟨by rw [hlife d]; exact hl, (not_iff (hmailNe d c hc)).mpr hnm, ?_, ?_⟩
        · intro hnew
          have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
            fun h => h.elim ho hp
          by_cases hdS : d = sender
          · have hback := (hdutyS c).mp (by rw [hdS] at hnew; exact Or.inl hnew)
            rw [← hdS] at hback
            exact hno hback
          · have ho0 : handlerOwes c (w.st d).phase := by rw [hother d hdS] at hnew; exact hnew
            exact ho ho0
        · intro hnew
          have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
            fun h => h.elim ho hp
          by_cases hdS : d = sender
          · have hback := (hdutyS c).mp (by rw [hdS] at hnew; exact Or.inr hnew)
            rw [← hdS] at hback
            exact hno hback
          · have hp0 : replyPending c (w.st d).phase := by rw [hother d hdS] at hnew; exact hnew
            exact hp hp0
  · intro d c hm
    by_cases hc : c = sender
    · rcases hm with ⟨m, hm, hcf⟩ | ⟨q, hq, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨hphA, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · rw [hd, hboxA, List.mem_append] at hm
            rcases hm with hold | heq
            · exact False.elim (run_unnamed w hT sender kRun hph d (Or.inl ⟨m, by rw [hd]; exact hold, by
                rw [hc] at hcf; exact hcf⟩))
            · exact Or.inl ⟨k, by
                rw [hc]
                have h := hphA
                rw [← hd] at h
                exact h⟩
          · rw [hd, hboxP] at hm
            exact False.elim (run_unnamed w hT sender kRun hph d (Or.inl ⟨m, by rw [hd]; exact hm, by
              rw [hc] at hcf; exact hcf⟩))
        · rw [hboxI d hd] at hm
          exact False.elim (run_unnamed w hT sender kRun hph d (Or.inl ⟨m, hm, by rw [hc] at hcf; exact hcf⟩))
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨hphP, hparkP, _⟩
          · rw [hd, hparkA] at hq
            exact False.elim (run_unnamed w hT sender kRun hph d (Or.inr ⟨q, by rw [hd]; exact hq, by
              rw [hc] at hcf; exact hcf⟩))
          · rw [hd, hparkP, List.mem_append] at hq
            rcases hq with hold | heq
            · exact False.elim (run_unnamed w hT sender kRun hph d (Or.inr ⟨q, by rw [hd]; exact hold, by
                rw [hc] at hcf; exact hcf⟩))
            · exact Or.inr ⟨k, by
                rw [hc]
                have h := hphP
                rw [← hd] at h
                exact h⟩
        · rw [hparkI d hd] at hq
          exact False.elim (run_unnamed w hT sender kRun hph d (Or.inr ⟨q, hq, by rw [hc] at hcf; exact hcf⟩))
    · have hm0 : mailCall w d c := (hmailNe d c hc).mp hm
      rcases hT.msgOwner d c hm0 with ⟨kA, hkA⟩ | ⟨kA, hkA⟩
      · exact Or.inl ⟨kA, by
          by_cases hi : c = sender
          · exact absurd hi hc
          · rw [hother c hi]
            exact hkA⟩
      · exact Or.inr ⟨kA, by
          by_cases hi : c = sender
          · exact absurd hi hc
          · rw [hother c hi]
            exact hkA⟩
  · intro d c ho
    by_cases hdS : d = sender
    · have hold := (hdutyS c).mp (by rw [hdS] at ho; exact ho)
      obtain ⟨kA, hkA⟩ := hT.oweOwner sender c hold
      have hc : c ≠ sender := by
        intro heq
        rw [heq, hph] at hkA
        cases hkA
      exact ⟨kA, by
        rw [hother c hc, hdS]
        exact hkA⟩
    · have hold : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        rcases ho with h | h
        · exact Or.inl (by rw [hother d hdS] at h; exact h)
        · exact Or.inr (by rw [hother d hdS] at h; exact h)
      obtain ⟨kA, hkA⟩ := hT.oweOwner d c hold
      by_cases hc : c = sender
      · rw [hc, hph] at hkA
        cases hkA
      · exact ⟨kA, by rw [hother c hc]; exact hkA⟩
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprio i] at hm; exact hm)
  · intro d c
    unfold soleCall
    by_cases hd : d = dst
    · rcases hmode with ⟨_, hboxA, hparkA⟩ | ⟨_, hparkP, hboxP⟩
      · rw [hd, hboxA, hparkA, count_append]
        by_cases hc : c = sender
        · rw [hc]
          have h0 := run_unnamed_count w hT sender kRun hph dst
          have hone : countCall [msg] sender = 1 := by
            simp [countCall, hfrom]
          rw [hone]
          omega
        · have hneC : msg.callFrom ≠ some c := by
            intro h
            rw [hfrom] at h
            injection h with he
            exact hc he.symm
          have hzero : countCall [msg] c = 0 := by simp [countCall, hneC]
          rw [hzero, Nat.add_zero]
          simpa [soleCall] using hT.sole dst c
      · rw [hd, hboxP, hparkP, countParkedCall_append]
        by_cases hc : c = sender
        · rw [hc]
          have h0 := run_unnamed_count w hT sender kRun hph dst
          have hone : countParkedCall [{ sender := sender, msg := msg, isCall := true }] sender = 1 := by
            simp [countParkedCall, hfrom]
          rw [hone]
          omega
        · have hneC : msg.callFrom ≠ some c := by
            intro h
            rw [hfrom] at h
            injection h with he
            exact hc he.symm
          have hzero : countParkedCall [{ sender := sender, msg := msg, isCall := true }] c = 0 := by
            simp [countParkedCall, hneC]
          rw [hzero, Nat.add_zero]
          simpa [soleCall] using hT.sole dst c
    · rw [hboxI d hd, hparkI d hd]
      exact hT.sole d c
  · intro d q hq s0
    rcases hmode with ⟨hphA, _, hparkA⟩ | ⟨hphP, hparkP, _⟩
    · have hq0 : q ∈ (w.st d).parked := by
        by_cases hd : d = dst
        · rw [hd, hparkA] at hq
          rw [hd]
          exact hq
        · rw [hparkI d hd] at hq
          exact hq
      by_cases hs0 : s0 = sender
      · constructor
        · intro hc
          obtain ⟨_, _, hkP⟩ := (hT.parkFrom d q hq0 s0).mp hc
          rw [hs0, hph] at hkP
          cases hkP
        · intro ⟨_, _, hkP⟩
          rw [hs0, hphA] at hkP
          cases hkP
      · have hiff := hT.parkFrom d q hq0 s0
        have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
        constructor
        · intro hc
          obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
          exact ⟨hseq, kP, by rw [hpe]; exact hkP⟩
        · intro ⟨hseq, kP, hkP⟩
          exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; exact hkP⟩
    · by_cases hd : d = dst
      · rw [hd, hparkP, List.mem_append] at hq
        rcases hq with hold | hnew
        · have hq0 : q ∈ (w.st dst).parked := hold
          have hsnd : q.sender ≠ sender := by
            intro hs
            obtain ⟨_, hkOld⟩ := hM.fwd dst q hq0
            rw [hs, hph] at hkOld
            cases hkOld
          by_cases hs0 : s0 = sender
          · constructor
            · intro hc
              obtain ⟨hseq, _, hkP⟩ := (hT.parkFrom dst q hq0 s0).mp hc
              rw [hs0, hph] at hkP
              cases hkP
            · intro ⟨hseq, _, _⟩
              exact absurd hseq (by rw [hs0]; exact hsnd)
          · have hiff := hT.parkFrom dst q hq0 s0
            have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
            constructor
            · intro hc
              obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
              exact ⟨hseq, kP, by rw [hd, hpe]; exact hkP⟩
            · intro ⟨hseq, kP, hkP⟩
              exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; rw [hd] at hkP; exact hkP⟩
        · simp [List.mem_singleton] at hnew
          rw [hnew]
          constructor
          · intro hc
            have hc' : msg.callFrom = some s0 := hc
            rw [hfrom] at hc'
            injection hc' with hs
            refine ⟨hs, k, ?_⟩
            rw [← hs, hphP, ← hd]
          · intro ⟨hseq, _, _⟩
            have hs : sender = s0 := hseq
            rw [← hs, hfrom]
      · rw [hparkI d hd] at hq
        have hsnd : q.sender ≠ sender := by
          intro hs
          obtain ⟨_, hkOld⟩ := hM.fwd d q hq
          rw [hs, hph] at hkOld
          cases hkOld
        by_cases hs0 : s0 = sender
        · constructor
          · intro hc
            obtain ⟨_, _, hkP⟩ := (hT.parkFrom d q hq s0).mp hc
            rw [hs0, hph] at hkP
            cases hkP
          · intro ⟨hseq, _, _⟩
            exact absurd hseq (by rw [hs0]; exact hsnd)
        · have hiff := hT.parkFrom d q hq s0
          have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
          constructor
          · intro hc
            obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
            exact ⟨hseq, kP, by rw [hpe]; exact hkP⟩
          · intro ⟨hseq, kP, hkP⟩
            exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; exact hkP⟩
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hphA, _, _⟩ | ⟨hphP, hparkP, hboxP⟩
      · rw [hc, hphA] at hph'
        cases hph'
      · rw [hc, hphP] at hph'
        injection hph' with hd _
        refine Or.inl ⟨?_, ?_, ?_⟩
        · rw [hlife d, ← hd]
          exact hlive
        · exact ⟨{ sender := sender, msg := msg, isCall := true }, by
            rw [← hd, hparkP]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl), hc.symm, by
            rw [← hc] at hfrom
            exact hfrom⟩
        · intro ⟨m, hm, hcf⟩
          rw [← hd, hboxP] at hm
          exact run_unnamed w hT sender kRun hph dst (Or.inl ⟨m, hm, by rw [hc] at hcf; exact hcf⟩)
    · have hph0 : (w.st c).phase = .parked d true kA := by rw [hother c hc] at hph'; exact hph'
      exact parkedOnly_lift w w' hT c d kA hph0 (hlife d)
        (fun q hq _ _ => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
            · rw [hd] at hq
              rw [hd, hparkA]
              exact hq
            · rw [hd] at hq
              rw [hd, hparkP]
              exact List.mem_append_left _ hq
          · rw [hparkI d hd]
            exact hq)
        (fun q hq hcf => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
            · rw [hd, hparkA] at hq
              rw [hd]
              exact hq
            · rw [hd, hparkP, List.mem_append] at hq
              rcases hq with hold | heq
              · rw [hd]
                exact hold
              · simp [List.mem_singleton] at heq
                rw [heq, hfrom] at hcf
                injection hcf with heqc
                exact False.elim (hc heqc.symm)
          · rw [← hparkI d hd]
            exact hq)
        (fun m hm hcf => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
            · rw [hd, hboxA, List.mem_append] at hm
              rcases hm with hold | heq
              · rw [hd]
                exact hold
              · simp [List.mem_singleton] at heq
                rw [heq, hfrom] at hcf
                injection hcf with heqc
                exact False.elim (hc heqc.symm)
            · rw [hd, hboxP] at hm
              rw [hd]
              exact hm
          · rw [← hboxI d hd]
            exact hm)
  · intro d c ho
    by_cases hd : d = sender
    · rw [hd] at ho
      have hpre : handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase :=
        (hdutyS c).mp ho
      have hc : c ≠ sender := by
        intro heq
        obtain ⟨k0, hk0⟩ := hT.oweOwner sender c hpre
        rw [heq, hph] at hk0
        cases hk0
      rw [hd, howed sender, hT.owedId sender c hpre, hwait c hc]
    · by_cases hc : c = sender
      · rw [hc] at ho
        have hpre : handlerOwes sender (w.st d).phase ∨ replyPending sender (w.st d).phase := by
          simpa [hother d hd] using ho
        obtain ⟨k0, hk0⟩ := hT.oweOwner d sender hpre
        rw [hph] at hk0
        cases hk0
      · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          simpa [hother d hd] using ho
        rw [howed d, hT.owedId d c hpre, hwait c hc]

/-- The duty of a continuation is unchanged when its head is parked instead of run. -/
theorem parked_duty (dst : InstId) (k : Cont) (e : Eff) (es : List Eff) (c : InstId)
    (hrest : k.rest = e :: es) (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    handlerOwes c (.parked dst true (afterHead k)) ∨ replyPending c (.parked dst true (afterHead k)) ↔
      handlerOwes c (.run k) ∨ replyPending c (.run k) := by
  have hshape := replyShape_tail c k e es hrest hne hterm
  have hsplit := shape_split c k
  have hnew := carried_duty c (.parked dst true (afterHead k)) (afterHead k) (by simp [carriedCont])
  constructor
  · intro h
    exact hsplit.mpr (hshape.mpr (hnew.mp h))
  · intro h
    exact hnew.mpr (hshape.mp (hsplit.mp h))

/-- Retiring a call id changes that actor's `waitId` only. Nobody was awaiting them,
and their own `oweId` is untouched, so the agreement still holds. -/
theorem owed_retire (w : World) (id : InstId) (a : Actor) (hT : CallTagInv w)
    (hph : ∀ i, ((setActor w id a).st i).phase = (w.st i).phase)
    (howe : a.oweId = (w.st id).oweId)
    (hnot : ∀ d k, (w.st id).phase ≠ .awaitReply d k) :
    ∀ d c, handlerOwes c ((setActor w id a).st d).phase ∨
        replyPending c ((setActor w id a).st d).phase →
      ((setActor w id a).st d).oweId = some ((setActor w id a).st c).waitId := by
  intro d c ho
  have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
    simpa [hph d] using ho
  have hold := hT.owedId d c hpre
  by_cases hc : c = id
  · rw [hc] at hpre
    obtain ⟨k, hk⟩ := hT.oweOwner d id hpre
    exact absurd hk (hnot d k)
  · by_cases hd : d = id
    · rw [hd] at hold ⊢
      simp [setActor, hc, howe]
      exact hold
    · simp [setActor, hd, hc, hold]

/-- An absent callee takes `NotAdmitted` at once. The caller proceeds, and the
call id is retired, so no tag moves. -/
theorem absent_call_tag (w : World) (sender : InstId) (kRun : Cont) (e : Eff) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st sender).phase = .run kRun) (hrest : kRun.rest = e :: es)
    (hne : e ≠ .reply) (hterm : e ≠ .terminate) :
    CallTagInv (setActor w sender (finishCall (issueCall (w.st sender)) (afterHead kRun) .notAdmitted)) := by
  have htail := run_tail_tag w sender kRun e es hT hph hrest hne hterm
  apply call_tag_copy (setActor w sender (proceed (w.st sender) (afterHead kRun)))
      (setActor w sender (finishCall (issueCall (w.st sender)) (afterHead kRun) .notAdmitted)) htail
  · intro i
    by_cases hi : i = sender
    · cases hr : (afterHead kRun).rest <;>
        simp [setActor, hi, hr, finishCall, issueCall, proceed]
    · simp [setActor, hi]
  · exact lifeKeep_of_eq (fun i => by
      by_cases hi : i = sender
      · simp [setActor, hi, finishCall, issueCall, proceed_life]
      · simp [setActor, hi])
  · rw [← setActor_same w sender (proceed (w.st sender) (afterHead kRun))
      (finishCall (issueCall (w.st sender)) (afterHead kRun) .notAdmitted)]
    exact owed_retire (setActor w sender (proceed (w.st sender) (afterHead kRun))) sender
      (finishCall (issueCall (w.st sender)) (afterHead kRun) .notAdmitted) htail
      (fun i => by
        by_cases hi : i = sender
        · rw [hi, setActor_self, setActor_self, finishCall, proceed_resumed, proceed_resumed]
        · simp [setActor, hi])
      (by
        rw [setActor_self]
        simp [finishCall, issueCall, proceed_stamps])
      (fun d k hk => by
        rw [setActor_self] at hk
        cases hr : (afterHead kRun).rest <;> simp [proceed, hr] at hk)

/-- A call parked on a dead name has no mailbox entry. Death has already cleared
that mailbox, and the caller was not in a call, so the dead disjunct holds. -/
theorem dead_park_tag (w : World) (sender dst : InstId) (kRun : Cont) (e : Eff) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st sender).phase = .run kRun) (hrest : kRun.rest = e :: es)
    (hne : e ≠ .reply) (hterm : e ≠ .terminate) (hdead : (w.st dst).life = .dead)
    (hbox0 : (w.st dst).box = []) (hpark0 : (w.st dst).parked = []) :
    CallTagInv (setActor w sender
      { issueCall (w.st sender) with phase := .parked dst true (afterHead kRun) }) := by
  let w' := setActor w sender
    { issueCall (w.st sender) with phase := .parked dst true (afterHead kRun) }
  change CallTagInv w'
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hi : i = sender <;> simp [w', setActor, hi, issueCall]
  have hpark (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hi : i = sender <;> simp [w', setActor, hi, issueCall]
  have hlife (i : InstId) : (w'.st i).life = (w.st i).life := by
    by_cases hi : i = sender <;> simp [w', setActor, hi, issueCall]
  have hmail (d c : InstId) : mailCall w' d c ↔ mailCall w d c := by
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨p, hp, hcf⟩
      · exact Or.inl ⟨m, by rw [← hbox d]; exact hm, hcf⟩
      · exact Or.inr ⟨p, by rw [← hpark d]; exact hp, hcf⟩
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨p, hp, hcf⟩
      · exact Or.inl ⟨m, by rw [hbox d]; exact hm, hcf⟩
      · exact Or.inr ⟨p, by rw [hpark d]; exact hp, hcf⟩
  have hquiet : ¬handlerOwes sender (w.st dst).phase ∧ ¬replyPending sender (w.st dst).phase := by
    constructor
    · intro ho
      obtain ⟨k, hk⟩ := hT.oweOwner dst sender (Or.inl ho)
      rw [hph] at hk
      cases hk
    · intro hp
      obtain ⟨k, hk⟩ := hT.oweOwner dst sender (Or.inr hp)
      rw [hph] at hk
      cases hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d kA hph'
    by_cases hc : c = sender
    · rw [hc] at hph'
      simp [w', setActor, issueCall] at hph'
    · have hph0 : (w.st c).phase = .awaitReply d kA := by simpa [w', setActor, hc] using hph'
      by_cases hd : d = sender
      · rw [hd]
        have hiff := parked_duty dst kRun e es c hrest hne hterm
        have hnew : handlerOwes c (w'.st sender).phase ∨ replyPending c (w'.st sender).phase ↔
            handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase := by
          simpa [w', setActor, issueCall, hph] using hiff
        rcases hT.awaiting c sender kA (by rw [← hd]; exact hph0) with h1 | h2 | h3 | h4
        · exact Or.inl ⟨(hmail sender c).mpr h1.1,
            fun ho => (hnew.mp (Or.inl ho)).elim h1.2.1 h1.2.2,
            fun hp => (hnew.mp (Or.inr hp)).elim h1.2.1 h1.2.2⟩
        · have hyes := hnew.mpr (Or.inl h2.2.1)
          rcases hyes with ho | hp
          · exact Or.inr (Or.inl ⟨(not_iff (hmail sender c)).mpr h2.1, ho,
              handlerOwes_not_pending c _ ho⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨(not_iff (hmail sender c)).mpr h2.1,
              fun ho => handlerOwes_not_pending c _ ho hp, hp⟩))
        · have hyes := hnew.mpr (Or.inr h3.2.2)
          rcases hyes with ho | hp
          · exact Or.inr (Or.inl ⟨(not_iff (hmail sender c)).mpr h3.1, ho,
              handlerOwes_not_pending c _ ho⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨(not_iff (hmail sender c)).mpr h3.1,
              fun ho => handlerOwes_not_pending c _ ho hp, hp⟩))
        · have hno : ¬(handlerOwes c (w'.st sender).phase ∨ replyPending c (w'.st sender).phase) :=
            (not_iff hnew).mpr (fun h => h.elim h4.2.2.2.1 h4.2.2.2.2)
          exact Or.inr (Or.inr (Or.inr ⟨halted_cast (hlife sender) h4.1, (hlife c).trans h4.2.1,
            (not_iff (hmail sender c)).mpr h4.2.2.1,
            fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩))
      · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', setActor, hd]
        have howe : handlerOwes c (w'.st d).phase ↔ handlerOwes c (w.st d).phase := by simp [hpe]
        have hpend : replyPending c (w'.st d).phase ↔ replyPending c (w.st d).phase := by simp [hpe]
        rcases hT.awaiting c d kA hph0 with h1 | h2 | h3 | h4
        · exact Or.inl ⟨(hmail d c).mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
        · exact Or.inr (Or.inl ⟨(not_iff (hmail d c)).mpr h2.1, howe.mpr h2.2.1,
            (not_iff hpend).mpr h2.2.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨(not_iff (hmail d c)).mpr h3.1, (not_iff howe).mpr h3.2.1,
            hpend.mpr h3.2.2⟩))
        · exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w w' c d (hlife d) (hlife c)
            (hmail d c) howe hpend h4)))
  · intro c d kA hph'
    by_cases hc : c = sender
    · subst hc
      have hhere : (w'.st c).phase = .parked dst true (afterHead kRun) := by
        simp [w', setActor, issueCall]
      rw [hhere] at hph'
      injection hph' with hd _ _
      rw [← hd]
      refine Or.inr ⟨by rw [hlife dst]; exact hdead, ?_, ?_, ?_⟩
      · intro hm
        have hm0 := (hmail dst c).mp hm
        rcases hT.msgOwner dst c hm0 with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hph] at hk
          cases hk
        · rw [hph] at hk
          cases hk
      · intro ho
        by_cases hs : c = dst
        · rw [hs] at ho hph hquiet
          simp [w', setActor, issueCall, hs] at ho
          have hback := (parked_duty dst kRun e es dst hrest hne hterm).mp (Or.inl ho)
          rw [← hph] at hback
          exact hback.elim hquiet.1 hquiet.2
        · have hne : dst ≠ c := fun h => hs h.symm
          simp [w', setActor, hne] at ho
          exact hquiet.1 ho
      · intro hp
        by_cases hs : c = dst
        · rw [hs] at hp hph hquiet
          simp [w', setActor, issueCall, hs] at hp
          have hback := (parked_duty dst kRun e es dst hrest hne hterm).mp (Or.inr hp)
          rw [← hph] at hback
          exact hback.elim hquiet.1 hquiet.2
        · have hne : dst ≠ c := fun h => hs h.symm
          simp [w', setActor, hne] at hp
          exact hquiet.2 hp
    · have hph0 : (w.st c).phase = .parked d true kA := by simpa [w', setActor, hc] using hph'
      rcases hT.parkedCall c d kA hph0 with ⟨hl, hm, ho, hp⟩ | ⟨hl, hnm, ho, hp⟩
      · refine Or.inl ⟨by rw [hlife d]; exact hl, (hmail d c).mpr hm, ?_, ?_⟩
        · intro hnew
          by_cases hd : d = sender
          · have hback := (parked_duty dst kRun e es c hrest hne hterm).mp
              (Or.inl (by rw [hd] at hnew; simpa [w', setActor, issueCall] using hnew))
            have hback' : handlerOwes c (w.st sender).phase ∨
                replyPending c (w.st sender).phase := by rwa [← hph] at hback
            exact hback'.elim (by rw [← hd]; exact ho) (by rw [← hd]; exact hp)
          · exact ho (by simpa [w', setActor, hd] using hnew)
        · intro hnew
          by_cases hd : d = sender
          · have hback := (parked_duty dst kRun e es c hrest hne hterm).mp
              (Or.inr (by rw [hd] at hnew; simpa [w', setActor, issueCall] using hnew))
            have hback' : handlerOwes c (w.st sender).phase ∨
                replyPending c (w.st sender).phase := by rwa [← hph] at hback
            exact hback'.elim (by rw [← hd]; exact ho) (by rw [← hd]; exact hp)
          · exact hp (by simpa [w', setActor, hd] using hnew)
      · refine Or.inr ⟨by rw [hlife d]; exact hl, (not_iff (hmail d c)).mpr hnm, ?_, ?_⟩
        · intro hnew
          by_cases hd : d = sender
          · have hback := (parked_duty dst kRun e es c hrest hne hterm).mp
              (Or.inl (by rw [hd] at hnew; simpa [w', setActor, issueCall] using hnew))
            have hback' : handlerOwes c (w.st sender).phase ∨
                replyPending c (w.st sender).phase := by rwa [← hph] at hback
            exact hback'.elim (by rw [← hd]; exact ho) (by rw [← hd]; exact hp)
          · exact ho (by simpa [w', setActor, hd] using hnew)
        · intro hnew
          by_cases hd : d = sender
          · have hback := (parked_duty dst kRun e es c hrest hne hterm).mp
              (Or.inr (by rw [hd] at hnew; simpa [w', setActor, issueCall] using hnew))
            have hback' : handlerOwes c (w.st sender).phase ∨
                replyPending c (w.st sender).phase := by rwa [← hph] at hback
            exact hback'.elim (by rw [← hd]; exact ho) (by rw [← hd]; exact hp)
          · exact hp (by simpa [w', setActor, hd] using hnew)
  · intro d c hm
    have hm0 := (hmail d c).mp hm
    rcases hT.msgOwner d c hm0 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hc : c ≠ sender := by
        intro heq
        rw [heq, hph] at hk
        cases hk
      exact Or.inl ⟨k, by simpa [w', setActor, hc] using hk⟩
    · have hc : c ≠ sender := by
        intro heq
        rw [heq, hph] at hk
        cases hk
      exact Or.inr ⟨k, by simpa [w', setActor, hc] using hk⟩
  · intro d c h
    by_cases hd : d = sender
    · have hlit := (parked_duty dst kRun e es c hrest hne hterm).mp (by
        rw [hd] at h
        simpa [w', setActor, issueCall] using h)
      have h0 : handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase := by
        rwa [← hph] at hlit
      obtain ⟨k, hk⟩ := hT.oweOwner sender c h0
      have hc : c ≠ sender := by
        intro heq
        rw [heq, hph] at hk
        cases hk
      exact ⟨k, by rw [hd]; simpa [w', setActor, hc] using hk⟩
    · have h0 : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        simpa [w', setActor, hd] using h
      obtain ⟨k, hk⟩ := hT.oweOwner d c h0
      have hc : c ≠ sender := by
        intro heq
        rw [heq, hph] at hk
        cases hk
      exact ⟨k, by simpa [w', setActor, hc] using hk⟩
  · intro i m hm
    exact hT.prioPlain i m (by
      by_cases hi : i = sender
      · simpa [w', setActor, hi, issueCall] using hm
      · simpa [w', setActor, hi] using hm)
  · intro d c
    simpa [soleCall, hbox d, hpark d] using hT.sole d c
  · intro d q hq s
    by_cases hd : d = dst
    · have hq0 : q ∈ (w.st dst).parked := by
        rw [← hpark dst]
        simpa [hd] using hq
      simp [hpark0] at hq0
    · have hq0 : q ∈ (w.st d).parked := by rw [← hpark d]; exact hq
      have hiff := hT.parkFrom d q hq0 s
      by_cases hs : s = sender
      · constructor
        · intro hc
          obtain ⟨_, _, hk⟩ := hiff.mp hc
          rw [hs, hph] at hk
          cases hk
        · intro ⟨_, _, hk⟩
          simp [w', setActor, hs, issueCall] at hk
          exact False.elim (hd hk.1.symm)
      · constructor
        · intro hc
          obtain ⟨hseq, k, hk⟩ := hiff.mp hc
          exact ⟨hseq, k, by simpa [w', setActor, hs] using hk⟩
        · intro ⟨hseq, k, hk⟩
          exact hiff.mpr ⟨hseq, k, by simpa [w', setActor, hs] using hk⟩
  · intro c d kA hph'
    by_cases hc : c = sender
    · rw [hc] at hph'
      have hhere : (w'.st sender).phase = .parked dst true (afterHead kRun) := by
        simp [w', setActor, issueCall]
      rw [hhere] at hph'
      injection hph' with heq _ _
      refine Or.inr ⟨by rw [hlife d, ← heq]; exact hdead, ?_, ?_⟩
      · intro ⟨p, hp, _⟩
        have hp0 : p ∈ (w.st d).parked := by rw [← hpark d]; exact hp
        rw [← heq] at hp0
        simp [hpark0] at hp0
      · intro ⟨m, hm, _⟩
        have hm0 : m ∈ (w.st d).box := by rw [← hbox d]; exact hm
        rw [← heq] at hm0
        simp [hbox0] at hm0
    · have hph0 : (w.st c).phase = .parked d true kA := by simpa [w', setActor, hc] using hph'
      exact parkedOnly_lift w w' hT c d kA hph0 (by rw [hlife d])
        (fun p hp _ _ => by rw [hpark d]; exact hp)
        (fun p hp _ => by rw [← hpark d]; exact hp)
        (fun m hm _ => by rw [← hbox d]; exact hm)
  · intro d c ho
    by_cases hd : d = sender
    · rw [hd] at ho
      have hlit := (parked_duty dst kRun e es c hrest hne hterm).mp (by
        simpa [w', setActor, issueCall] using ho)
      have h0 : handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase := by
        rwa [← hph] at hlit
      have hc : c ≠ sender := by
        intro heq
        obtain ⟨k, hk⟩ := hT.oweOwner sender c h0
        rw [heq, hph] at hk
        cases hk
      rw [hd]
      have hold := hT.owedId sender c h0
      simp only [w', setActor, hc, issueCall] at hold ⊢
      exact hold
    · by_cases hc : c = sender
      · rw [hc] at ho
        have hpre : handlerOwes sender (w.st d).phase ∨ replyPending sender (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        obtain ⟨k, hk⟩ := hT.oweOwner d sender hpre
        rw [hph] at hk
        cases hk
      · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        simpa [w', setActor, hd, hc, issueCall] using hT.owedId d c hpre

/-- A call effect enqueues a fresh tag, or misses when the target is not alive. -/
theorem enqueue_call_tag (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (kRun : Cont) (e : Eff) (es : List Eff) (hT : CallTagInv w) (hM : MailInv w)
    (hph : (w.st sender).phase = .run kRun) (hrest : kRun.rest = e :: es) (hne : e ≠ .reply)
    (hterm : e ≠ .terminate) (hfrom : msg.callFrom = some sender)
    (_hempty : (w.st dst).life ≠ .alive → (w.st dst).box = [] ∧ (w.st dst).parked = []) :
    CallTagInv (enqueueOrPark w D sender dst msg true (afterHead kRun)) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hparkS : (w.st sender).parked = [] := by
          have h := hroom.1
          rwa [← hsame] at h
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by
          have h := hroom.2
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_room_self_call w D sender msg (afterHead kRun) hliveS hparkS hcapS]
        apply fresh_call_tag w _ sender sender { msg with mid := (w.st sender).nextMid } (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inl ⟨by simp [setActor], ?_, ?_⟩
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
        · exact hliveS
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, issueCall, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, issueCall, chargeSender, bumpToken]
        · intro i hi
          simp [setActor, hi, issueCall, chargeSender, bumpToken]
      · rw [enqueue_room_other_call w D sender dst msg (afterHead kRun) hlive hsame hroom.1 hroom.2]
        apply fresh_call_tag w _ sender dst { msg with mid := (w.st dst).nextMid } (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          by_cases hid : i = dst
          · have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, hi, hid, hflip]
          · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · have hflip : ¬ dst = sender := fun h => hsame h.symm
          refine Or.inl ⟨by simp [setActor], ?_, ?_⟩
          · simp [setActor, hflip, issueCall, ite_true]
          · simp [setActor, hflip, issueCall, ite_true]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · exact hlive
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, issueCall, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip, issueCall]
            · simp [setActor, hi, hid]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, issueCall, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · exact absurd hs hi
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid, issueCall, chargeSender, bumpToken]
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          have h := hroom
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_park_self w D sender msg true (afterHead kRun) hliveS hroomS]
        apply fresh_call_tag w _ sender sender { msg with mid := (w.st sender).nextMid } (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inr ⟨by simp [setActor], ?_, ?_⟩
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
        · exact hliveS
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, issueCall, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, issueCall, chargeSender, bumpToken]
        · intro i hi
          simp [setActor, hi, issueCall, chargeSender, bumpToken]
      · rw [enqueue_park_other w D sender dst msg true (afterHead kRun) hlive hsame hroom]
        apply fresh_call_tag w _ sender dst { msg with mid := (w.st dst).nextMid } (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          by_cases hid : i = dst
          · have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, hi, hid, hflip]
          · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · have hflip : ¬ dst = sender := fun h => hsame h.symm
          refine Or.inr ⟨by simp [setActor, issueCall, ite_true, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, hflip, issueCall, ite_true]
          · simp [setActor, hflip, issueCall, ite_true]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · exact hlive
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, issueCall, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip, issueCall]
            · simp [setActor, hi, hid]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, issueCall, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · exact absurd hs hi
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid, issueCall, chargeSender, bumpToken]
  · rw [enqueue_miss w D sender dst msg (afterHead kRun) hlive]
    exact absent_call_tag w sender kRun e es hT hph hrest hne hterm

theorem not_shape_zero (c : InstId) (k : Cont) (h : replyCount k.rest = 0) : ¬replyShape c k := by
  intro hs
  have hc := hs.2.1
  rw [h] at hc
  omega

/-- Advancing a continuation whose `replyTo` is empty owes nobody, and the runner
was not itself awaiting, so the owed-id agreement is untouched. -/
theorem owed_noreply (w : World) (id : InstId) (k : Cont) (hT : CallTagInv w)
    (hph : (w.st id).phase = .run k) (hto : k.replyTo = none) :
    ∀ d c, handlerOwes c ((setActor w id (proceed (w.st id) (afterHead k))).st d).phase ∨
        replyPending c ((setActor w id (proceed (w.st id) (afterHead k))).st d).phase →
      ((setActor w id (proceed (w.st id) (afterHead k))).st d).oweId =
        some ((setActor w id (proceed (w.st id) (afterHead k))).st c).waitId := by
  intro d c ho
  have hs := stamp_set w id (proceed (w.st id) (afterHead k))
    (proceed_stamps _ _).1 (proceed_stamps _ _).2
  by_cases hd : d = id
  · rw [hd] at ho
    rcases ho with ⟨k0, hk0, hs0, _⟩ | ⟨k0, hk0, hs0, _⟩
    · simp [setActor] at hk0
      cases hr : (afterHead k).rest <;> simp [proceed, hr, carriedCont] at hk0
      cases hk0
      simp [replyShape, afterHead, hto] at hs0
    · simp [setActor] at hk0
      cases hr : (afterHead k).rest <;> simp [proceed, hr, carriedCont] at hk0
      cases hk0
      simp [replyShape, afterHead, hto] at hs0
  · by_cases hc : c = id
    · rw [hc] at ho
      have hpre : handlerOwes id (w.st d).phase ∨ replyPending id (w.st d).phase := by
        simpa [setActor, hd] using ho
      obtain ⟨k0, hk0⟩ := hT.oweOwner d id hpre
      simp [hph] at hk0
    · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
        simpa [setActor, hd] using ho
      simpa [setActor, hd, hc, (hs d).1, (hs c).2] using hT.owedId d c hpre

/-- A reply whose `replyTo` is empty only advances the handler. The tail has no
reply left, and the handler was not holding one. -/
theorem reply_advance_tag (w : World) (sender : InstId) (k : Cont) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st sender).phase = .run k) (hrest : k.rest = .reply :: es)
    (hcount : replyCount k.rest = 1) (hto : k.replyTo = none) :
    CallTagInv (setActor w sender (proceed (w.st sender) (afterHead k))) := by
  have htail : replyCount es = 0 := by
    simp [replyCount, hrest] at hcount
    omega
  let k' := afterHead k
  have hkrest : k'.rest = es := by simp [k', afterHead, hrest]
  let w' := setActor w sender (proceed (w.st sender) k')
  have hst (i : InstId) (hi : i ≠ sender) : w'.st i = w.st i := by simp [w', setActor, hi]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hi : i = sender
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hi : i = sender
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  have hprioL (i : InstId) : (w'.st i).prio = (w.st i).prio := by
    by_cases hi : i = sender
    · simp [w', hi, setActor, proceed_fields]
    · simp [hst i hi]
  have hquiet (c : InstId) : ¬handlerOwes c (w.st sender).phase ∧ ¬replyPending c (w.st sender).phase := by
    constructor
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hph] at hk0
      cases hk0
      simp only [replyShape] at hs
      rw [hto] at hs
      cases hs.1
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hph] at hk0
      cases hk0
      simp only [replyShape] at hs
      rw [hto] at hs
      cases hs.1
  have hquiet' (c : InstId) :
      ¬handlerOwes c (w'.st sender).phase ∧ ¬replyPending c (w'.st sender).phase := by
    constructor
    · intro ⟨k0, hk0, hs, _⟩
      cases hes : es with
      | nil => simp [w', setActor, proceed, k', hkrest, hes, carriedCont] at hk0
      | cons _ _ =>
        simp [w', setActor, proceed, k', hkrest, hes, carriedCont] at hk0
        cases hk0
        exact not_shape_zero c k' (by simp [hkrest, htail]) hs
    · intro ⟨k0, hk0, hs, _⟩
      cases hes : es with
      | nil => simp [w', setActor, proceed, k', hkrest, hes, carriedCont] at hk0
      | cons _ _ =>
        simp [w', setActor, proceed, k', hkrest, hes, carriedCont] at hk0
        cases hk0
        exact not_shape_zero c k' (by simp [hkrest, htail]) hs
  apply call_tag_stable w w' hT
  · intro d c
    exact mail_iff_lists w w' hbox hparked d c
  · intro i c
    by_cases hi : i = sender
    · constructor
      · intro h
        rw [hi] at h
        exact False.elim ((hquiet' c).1 h)
      · intro h
        rw [hi] at h
        exact False.elim ((hquiet c).1 h)
    · exact owes_iff_carried _ _ (by simp [hst i hi, carriedCont]) c
  · intro i c
    by_cases hi : i = sender
    · constructor
      · intro h
        rw [hi] at h
        exact False.elim ((hquiet' c).2 h)
      · intro h
        rw [hi] at h
        exact False.elim ((hquiet c).2 h)
    · exact pending_iff_carried _ _ (by simp [hst i hi, carriedCont]) c
  · intro c d kA hph'
    by_cases hc : c = sender
    · cases hes : es with
      | nil => simp [w', hc, setActor, proceed, k', hkrest, hes] at hph'
      | cons _ _ => simp [w', hc, setActor, proceed, k', hkrest, hes] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · cases hes : es with
      | nil => simp [w', hc, setActor, proceed, k', hkrest, hes] at hph'
      | cons _ _ => simp [w', hc, setActor, proceed, k', hkrest, hes] at hph'
    · simpa [hst c hc] using hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprioL i] at hm; exact hm)
  · intro d c
    unfold soleCall
    rw [hbox d, hparked d]
    exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT hparked
      (by
        intro s0 d0 k0
        constructor
        · intro hk
          by_cases hs0 : s0 = sender
          · cases hes : es with
            | nil => simp [w', hs0, setActor, proceed, k', hkrest, hes] at hk
            | cons _ _ => simp [w', hs0, setActor, proceed, k', hkrest, hes] at hk
          · simpa [hst s0 hs0] using hk
        · intro hk
          by_cases hs0 : s0 = sender
          · simp [hs0, hph] at hk
          · simpa [← hst s0 hs0] using hk)
      d p hp s
  · intro c d kA hk
    exact parkedOnly_transport w w' hT hparked (by intro i m hm; rw [hbox i] at hm; exact hm)
      (by
        intro c0 _ _ hk0
        by_cases hc0 : c0 = sender
        · cases hes : es with
          | nil => simp [w', hc0, setActor, proceed, k', hkrest, hes] at hk0
          | cons _ _ => simp [w', hc0, setActor, proceed, k', hkrest, hes] at hk0
        · simpa [hst c0 hc0] using hk0)
      c d kA hk
      (by simpa [w'] using life_setActor w sender (proceed (w.st sender) k') (proceed_life _ _))
  · simpa [w'] using life_setActor w sender (proceed (w.st sender) k') (proceed_life _ _)
  · exact owed_noreply w sender k hT hph hto

/-- A reply and the resumption of its caller, checked on the combined post-state.
`oweOwner` names that caller, so every other `awaitReply` is left in place. -/
theorem reply_resume_tag (w : World) (sender c : InstId) (k ck : Cont) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st sender).phase = .run k) (hrest : k.rest = .reply :: es)
    (hcount : replyCount k.rest = 1) (hto : k.replyTo = some c)
    (hwait : (w.st c).phase = .awaitReply sender ck) (hcne : c ≠ sender) :
    let w1 := setActor w c (finishCall (w.st c) ck .reply)
    CallTagInv (setActor w1 sender (proceed (w1.st sender) (afterHead k))) := by
  have htail : replyCount es = 0 := by
    simp [replyCount, hrest] at hcount
    omega
  let k' := afterHead k
  have hkrest : k'.rest = es := by simp [k', afterHead, hrest]
  let w1 := setActor w c (finishCall (w.st c) ck .reply)
  let w' := setActor w1 sender (proceed (w1.st sender) k')
  have hflip : ¬ sender = c := fun h => hcne h.symm
  have hS : w1.st sender = w.st sender := by simp [w1, setActor, hflip]
  have hpend : replyPending c (w.st sender).phase :=
    ⟨k, by simp [carriedCont, hph], ⟨hto, hcount, by simp [terminateBeforeReply, hrest]⟩,
      by simp [nextIsReply, hrest]⟩
  have hnom : ¬mailCall w sender c := by
    have hpre := hT.awaiting c sender ck hwait
    rcases hpre with h1 | h2 | h3 | h4
    · exact False.elim (h1.2.2 hpend)
    · exact False.elim (h2.2.2 hpend)
    · exact h3.1
    · exact False.elim (h4.2.2.2.2 hpend)
  have hst (i : InstId) (hc0 : i ≠ c) (hs0 : i ≠ sender) : w'.st i = w.st i := by
    simp [w', w1, setActor, hc0, hs0]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, finishCall_box, finishCall_parked, finishCall_prio, hcne]
      · simp [hst i hc0 hs0]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, finishCall_box, finishCall_parked, finishCall_prio, hcne]
      · simp [hst i hc0 hs0]
  have hprioL (i : InstId) : (w'.st i).prio = (w.st i).prio := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, finishCall_box, finishCall_parked, finishCall_prio, hcne]
      · simp [hst i hc0 hs0]
  have hquietS (c0 : InstId) :
      ¬handlerOwes c0 (w'.st sender).phase ∧ ¬replyPending c0 (w'.st sender).phase := by
    constructor
    · intro ⟨k0, hk0, hs, _⟩
      cases hes : es with
      | nil => simp [w', setActor, proceed, hS, k', hkrest, hes, carriedCont] at hk0
      | cons _ _ =>
        simp [w', setActor, proceed, hS, k', hkrest, hes, carriedCont] at hk0
        cases hk0
        exact not_shape_zero c0 k' (by simp [hkrest, htail]) hs
    · intro ⟨k0, hk0, hs, _⟩
      cases hes : es with
      | nil => simp [w', setActor, proceed, hS, k', hkrest, hes, carriedCont] at hk0
      | cons _ _ =>
        simp [w', setActor, proceed, hS, k', hkrest, hes, carriedCont] at hk0
        cases hk0
        exact not_shape_zero c0 k' (by simp [hkrest, htail]) hs
  have hquietOld (c0 : InstId) (hc0 : c0 ≠ c) :
      ¬handlerOwes c0 (w.st sender).phase ∧ ¬replyPending c0 (w.st sender).phase := by
    constructor
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hph] at hk0
      cases hk0
      simp only [replyShape] at hs
      rw [hto] at hs
      injection hs.1 with heq
      exact hc0 heq.symm
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hph] at hk0
      cases hk0
      simp only [replyShape] at hs
      rw [hto] at hs
      injection hs.1 with heq
      exact hc0 heq.symm
  have howeC (c0 : InstId) : handlerOwes c0 (w'.st c).phase ↔ handlerOwes c0 (w.st c).phase := by
    cases hk : ck.rest with
    | nil =>
      constructor
      · intro h
        simp [w', w1, setActor, hcne, finishCall, proceed, hk, handlerOwes, carriedCont] at h
      · intro h
        have hcar : carriedCont (w.st c).phase = some ck := by
          rw [hwait]
          simp [carriedCont]
        exact False.elim (owes_empty _ _ hcar hk c0 h)
    | cons _ _ =>
      have hcarN : carriedCont (w'.st c).phase = some ck := by
        simp [w', w1, setActor, hcne, finishCall, proceed, carriedCont, hk]
      have hcarO : carriedCont (w.st c).phase = some ck := by simp [carriedCont, hwait]
      exact owes_iff_carried _ _ (hcarN.trans hcarO.symm) c0
  have hpendC (c0 : InstId) : replyPending c0 (w'.st c).phase ↔ replyPending c0 (w.st c).phase := by
    cases hk : ck.rest with
    | nil =>
      constructor
      · intro h
        simp [w', w1, setActor, hcne, finishCall, proceed, hk, replyPending, carriedCont] at h
      · intro h
        have hcar : carriedCont (w.st c).phase = some ck := by
          rw [hwait]
          simp [carriedCont]
        exact False.elim (pending_empty _ _ hcar hk c0 h)
    | cons _ _ =>
      have hcarN : carriedCont (w'.st c).phase = some ck := by
        simp [w', w1, setActor, hcne, finishCall, proceed, carriedCont, hk]
      have hcarO : carriedCont (w.st c).phase = some ck := by simp [carriedCont, hwait]
      exact pending_iff_carried _ _ (hcarN.trans hcarO.symm) c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 d kA hph'
    by_cases hc0 : c0 = c
    · cases hk : ck.rest <;> simp [w', w1, setActor, hcne, finishCall, proceed, hk, hc0] at hph'
    · by_cases hs0 : c0 = sender
      · cases hes : es <;> simp [w', setActor, proceed, hS, k', hkrest, hes, hs0] at hph'
      · have hph0 : (w.st c0).phase = .awaitReply d kA := by
          simp [w', w1, setActor, hc0, hs0] at hph'
          exact hph'
        have hpre := hT.awaiting c0 d kA hph0
        have hmail := mail_iff_lists w w' hbox hparked d c0
        have howe : handlerOwes c0 (w'.st d).phase ↔ handlerOwes c0 (w.st d).phase := by
          by_cases hd : d = sender
          · constructor
            · intro h
              exact False.elim ((hquietS c0).1 (by rw [hd] at h; exact h))
            · intro h
              exact False.elim ((hquietOld c0 hc0).1 (by rw [hd] at h; exact h))
          · by_cases hdc : d = c
            · rw [hdc]
              exact howeC c0
            · exact owes_iff_carried _ _ (by simp [w', w1, setActor, hd, hdc, carriedCont]) c0
        have hpendI : replyPending c0 (w'.st d).phase ↔ replyPending c0 (w.st d).phase := by
          by_cases hd : d = sender
          · constructor
            · intro h
              exact False.elim ((hquietS c0).2 (by rw [hd] at h; exact h))
            · intro h
              exact False.elim ((hquietOld c0 hc0).2 (by rw [hd] at h; exact h))
          · by_cases hdc : d = c
            · rw [hdc]
              exact hpendC c0
            · exact pending_iff_carried _ _ (by simp [w', w1, setActor, hd, hdc, carriedCont]) c0
        rcases hpre with h1 | h2 | h3 | h4
        · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpendI).mpr h1.2.2⟩
        · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpendI).mpr h2.2.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
            hpendI.mpr h3.2.2⟩))
        · have hlD : (w'.st d).life = (w.st d).life := by
            by_cases hd : d = sender
            · simp [w', hd, setActor, hS, proceed_keeps_life]
            · by_cases hdc : d = c
              · simp [w', w1, hd, hdc, setActor, hcne, finishCall_life]
              · simp [w', w1, setActor, hd, hdc]
          have hlC : (w'.st c0).life = (w.st c0).life := by
            simp [w', w1, setActor, hc0, hs0]
          exact Or.inr (Or.inr (Or.inr (awaiting_dead_copy w w' c0 d hlD hlC hmail howe hpendI h4)))
  · intro c0 d kA hph'
    by_cases hc0 : c0 = c
    · cases hk : ck.rest <;> simp [w', w1, setActor, hcne, finishCall, proceed, hk, hc0] at hph'
    · by_cases hs0 : c0 = sender
      · cases hes : es <;> simp [w', setActor, proceed, hS, k', hkrest, hes, hs0] at hph'
      · have hph0 : (w.st c0).phase = .parked d true kA := by
          simp [w', w1, setActor, hc0, hs0] at hph'
          exact hph'
        have hmail := mail_iff_lists w w' hbox hparked d c0
        have hlifeR : (w'.st d).life = (w.st d).life := by
          by_cases hd : d = sender
          · rw [hd]
            simp only [w']
            rw [setActor_self, proceed_life, hS]
          · by_cases hdc : d = c
            · rw [hdc]
              simp only [w']
              rw [setActor_other _ _ _ _ hcne]
              simp only [w1, setActor]
              exact finishCall_life _ _ _
            · simp [w', w1, setActor, hd, hdc]
        rcases hT.parkedCall c0 d kA hph0 with ⟨hl, hm, ho0, hp0⟩ | ⟨hl, hnm, ho0, hp0⟩
        · refine Or.inl ⟨by rw [hlifeR]; exact hl, hmail.mpr hm, ?_, ?_⟩
          · intro ho
            by_cases hd : d = sender
            · exact False.elim ((hquietS c0).1 (by rw [hd] at ho; exact ho))
            · by_cases hdc : d = c
              · rw [hdc] at ho ho0
                exact ho0 ((howeC c0).mp ho)
              · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
                exact ho0 (by simpa [← hpe] using ho)
          · intro hp
            by_cases hd : d = sender
            · exact False.elim ((hquietS c0).2 (by rw [hd] at hp; exact hp))
            · by_cases hdc : d = c
              · rw [hdc] at hp hp0
                exact hp0 ((hpendC c0).mp hp)
              · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
                exact hp0 (by simpa [← hpe] using hp)
        · refine Or.inr ⟨by rw [hlifeR]; exact hl, (not_iff hmail).mpr hnm, ?_, ?_⟩
          · intro ho
            by_cases hd : d = sender
            · exact False.elim ((hquietS c0).1 (by rw [hd] at ho; exact ho))
            · by_cases hdc : d = c
              · rw [hdc] at ho ho0
                exact ho0 ((howeC c0).mp ho)
              · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
                exact ho0 (by simpa [← hpe] using ho)
          · intro hp
            by_cases hd : d = sender
            · exact False.elim ((hquietS c0).2 (by rw [hd] at hp; exact hp))
            · by_cases hdc : d = c
              · rw [hdc] at hp hp0
                exact hp0 ((hpendC c0).mp hp)
              · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
                exact hp0 (by simpa [← hpe] using hp)
  · intro d c0 hm
    have hm0 := (mail_iff_lists w w' hbox hparked d c0).mp hm
    rcases hT.msgOwner d c0 hm0 with ⟨kA, hkA⟩ | ⟨kA, hkA⟩
    · have hc0 : c0 ≠ c := by
        intro heq
        rw [heq, hwait] at hkA
        injection hkA with hd0
        exact hnom (by rw [← hd0, heq] at hm0; exact hm0)
      have hs0 : c0 ≠ sender := by
        intro heq
        rw [heq, hph] at hkA
        cases hkA
      exact Or.inl ⟨kA, by
        simp [w', w1, setActor, hc0, hs0]
        exact hkA⟩
    · have hc0 : c0 ≠ c := by
        intro heq
        rw [heq, hwait] at hkA
        cases hkA
      have hs0 : c0 ≠ sender := by
        intro heq
        rw [heq, hph] at hkA
        cases hkA
      exact Or.inr ⟨kA, by
        simp [w', w1, setActor, hc0, hs0]
        exact hkA⟩
  · intro d c0 ho
    by_cases hd : d = sender
    · rcases ho with h | h
      · exact False.elim ((hquietS c0).1 (by rw [hd] at h; exact h))
      · exact False.elim ((hquietS c0).2 (by rw [hd] at h; exact h))
    · by_cases hdc : d = c
      · have hold : handlerOwes c0 (w.st c).phase ∨ replyPending c0 (w.st c).phase := by
          rcases ho with h | h
          · exact Or.inl ((howeC c0).mp (by rw [hdc] at h; exact h))
          · exact Or.inr ((hpendC c0).mp (by rw [hdc] at h; exact h))
        obtain ⟨kA, hkA⟩ := hT.oweOwner c c0 hold
        have hc0 : c0 ≠ c := by
          intro heq
          rw [heq, hwait] at hkA
          injection hkA with heqs
          exact hcne heqs.symm
        have hs0 : c0 ≠ sender := by
          intro heq
          rw [heq, hph] at hkA
          cases hkA
        exact ⟨kA, by
          simp [w', w1, setActor, hc0, hs0, hdc]
          exact hkA⟩
      · have hold : handlerOwes c0 (w.st d).phase ∨ replyPending c0 (w.st d).phase := by
          have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
          rcases ho with h | h
          · exact Or.inl (by simpa [← hpe] using h)
          · exact Or.inr (by simpa [← hpe] using h)
        obtain ⟨kA, hkA⟩ := hT.oweOwner d c0 hold
        have hc0 : c0 ≠ c := by
          intro heq
          rw [heq, hwait] at hkA
          injection hkA with hd0
          exact hd hd0.symm
        have hs0 : c0 ≠ sender := by
          intro heq
          rw [heq, hph] at hkA
          cases hkA
        exact ⟨kA, by
          simp [w', w1, setActor, hc0, hs0]
          exact hkA⟩
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprioL i] at hm; exact hm)
  · intro d c0
    unfold soleCall
    rw [hbox d, hparked d]
    exact hT.sole d c0
  · intro d0 p hp s0
    exact parkFrom_transport w w' hT hparked
      (by
        intro s1 d1 k1
        constructor
        · intro hk
          by_cases hs1 : s1 = sender
          · cases hes : es <;> simp [w', hs1, setActor, proceed, hS, k', hkrest, hes] at hk
          · by_cases hc1 : s1 = c
            · cases hck : ck.rest <;> simp [w', w1, setActor, hcne, finishCall, proceed, hck, hc1] at hk
            · simpa [hst s1 hc1 hs1] using hk
        · intro hk
          by_cases hs1 : s1 = sender
          · simp [hs1, hph] at hk
          · by_cases hc1 : s1 = c
            · rw [hc1, hwait] at hk
              cases hk
            · simpa [← hst s1 hc1 hs1] using hk)
      d0 p hp s0
  · intro c0 d0 k0 hk0
    exact parkedOnly_transport w w' hT hparked (by intro i m hm; rw [hbox i] at hm; exact hm)
      (by
        intro c1 _ _ hk1
        by_cases hs1 : c1 = sender
        · cases hes : es <;> simp [w', hs1, setActor, proceed, hS, k', hkrest, hes] at hk1
        · by_cases hc1 : c1 = c
          · cases hck : ck.rest <;> simp [w', w1, setActor, hcne, finishCall, proceed, hck, hc1] at hk1
          · simpa [hst c1 hc1 hs1] using hk1)
      c0 d0 k0 hk0
      (lifeKeep_of_eq (fun i => by
        by_cases hs0 : i = sender
        · rw [hs0]
          simp only [w']
          rw [setActor_self, proceed_life, hS]
        · by_cases hc0 : i = c
          · rw [hc0]
            simp only [w']
            rw [setActor_other _ _ _ _ hcne]
            simp only [w1, setActor]
            exact finishCall_life _ _ _
          · exact congrArg Actor.life (hst i hc0 hs0)))
  · intro d c0 ho
    by_cases hd : d = sender
    · rw [hd] at ho
      rcases ho with h | h
      · exact False.elim ((hquietS c0).1 h)
      · exact False.elim ((hquietS c0).2 h)
    · by_cases hdc : d = c
      · rw [hdc] at ho
        cases hck : ck.rest with
        | nil =>
          rcases ho with ⟨_, hk0, _⟩ | ⟨_, hk0, _⟩ <;>
            simp [w', w1, setActor, hd, hcne, finishCall, proceed, hck, carriedCont] at hk0
        | cons _ _ =>
          have hcarN : carriedCont (w'.st c).phase = some ck := by
            simp [w', w1, setActor, hd, hcne, finishCall, proceed, hck, carriedCont]
          have hcarO : carriedCont (w.st c).phase = some ck := by simp [carriedCont, hwait]
          have hpre : handlerOwes c0 (w.st c).phase ∨ replyPending c0 (w.st c).phase := by
            rcases ho with h | h
            · exact Or.inl ((owes_iff_carried _ _ (hcarN.trans hcarO.symm) c0).mp h)
            · exact Or.inr ((pending_iff_carried _ _ (hcarN.trans hcarO.symm) c0).mp h)
          have hc0ne : c0 ≠ c := by
            intro heq
            obtain ⟨kA, hkA⟩ := hT.oweOwner c c0 hpre
            rw [heq, hwait] at hkA
            injection hkA with hdS _
            exact hcne hdS.symm
          have howeEq : (w'.st c).oweId = (w.st c).oweId := by
            simp only [w']
            rw [setActor_other _ _ _ _ hcne]
            simp only [w1, setActor]
            exact finishCall_owe _ _ _
          have hwaitEq : (w'.st c0).waitId = (w.st c0).waitId := by
            by_cases hs0 : c0 = sender
            · simp only [w', hs0]
              rw [setActor_self, (proceed_stamps _ _).2, hS]
            · rw [hst c0 hc0ne hs0]
          rw [hdc] at ⊢
          rw [howeEq, hwaitEq]
          exact hT.owedId c c0 hpre
      · by_cases hc0 : c0 = c
        · rw [hc0] at ho
          have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
            simpa [w', w1, setActor, hd, hdc] using ho
          obtain ⟨kA, hkA⟩ := hT.oweOwner d c hpre
          rw [hwait] at hkA
          injection hkA with hdS _
          exact False.elim (hd hdS.symm)
        · have hpre : handlerOwes c0 (w.st d).phase ∨ replyPending c0 (w.st d).phase := by
            simpa [w', w1, setActor, hd, hdc] using ho
          have howeEq : (w'.st d).oweId = (w.st d).oweId := by
            rw [hst d hdc hd]
          have hwaitEq : (w'.st c0).waitId = (w.st c0).waitId := by
            by_cases hs0 : c0 = sender
            · simp only [w', hs0]
              rw [setActor_self, (proceed_stamps _ _).2, hS]
            · rw [hst c0 hc0 hs0]
          rw [howeEq, hwaitEq]
          exact hT.owedId d c0 hpre

/-- One reply step. An empty `replyTo` only advances the handler. A `replyTo`
resumes that caller in the same step; `oweOwner` says the caller is waiting on
this handler, so no other `awaitReply` moves. -/
theorem reply_tag (w : World) (sender : InstId) (k : Cont) (es : List Eff) (hT : CallTagInv w)
    (hph : (w.st sender).phase = .run k) (hrest : k.rest = .reply :: es)
    (hcount : replyCount k.rest = 1) : CallTagInv (performReply w sender k) := by
  cases hto : k.replyTo with
  | none =>
    simp [performReply, hto]
    exact reply_advance_tag w sender k es hT hph hrest hcount hto
  | some c =>
    have hpend : replyPending c (w.st sender).phase :=
      ⟨k, by simp [carriedCont, hph], ⟨hto, hcount, by simp [terminateBeforeReply, hrest]⟩,
        by simp [nextIsReply, hrest]⟩
    obtain ⟨ck, hwait⟩ := hT.oweOwner sender c (Or.inr hpend)
    have hcne : c ≠ sender := by
      intro heq
      rw [heq, hph] at hwait
      cases hwait
    have hflip : ¬ sender = c := fun h => hcne h.symm
    have howe : (w.st sender).oweId = some (w.st c).waitId :=
      hT.owedId sender c (Or.inr hpend)
    unfold performReply
    rw [hto]
    simp [hwait, hflip, howe]
    exact reply_resume_tag w sender c k ck es hT hph hrest hcount hto hwait hcne

/-- Replacing one actor's priority lane with plain messages keeps call tags. -/
theorem prio_keep_tag (w : World) (id : InstId) (prio : List Msg) (n : Nat) (hT : CallTagInv w)
    (hplain : ∀ m, m ∈ prio → m.callFrom = none) :
    CallTagInv (setActor w id { (w.st id) with prio := prio, nextMid := n }) := by
  let w' := setActor w id { (w.st id) with prio := prio, nextMid := n }
  have hst (i : InstId) (hi : i ≠ id) : w'.st i = w.st i := by simp [w', setActor, hi]
  have hph (i : InstId) : (w'.st i).phase = (w.st i).phase := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  apply call_tag_stable w w' hT
  · intro d c
    exact mail_iff_lists w w' hbox hparked d c
  · intro i c
    exact owes_iff_carried _ _ (by simp [hph i]) c
  · intro i c
    exact pending_iff_carried _ _ (by simp [hph i]) c
  · intro c d k hph'
    rw [hph c] at hph'
    exact hph'
  · intro c d k hph'
    rw [← hph c] at hph'
    exact hph'
  · intro c d k hph'
    rw [hph c] at hph'
    exact hph'
  · intro c d k hph'
    rw [← hph c] at hph'
    exact hph'
  · intro i m hm
    by_cases hi : i = id
    · exact hplain m (by simp [w', hi, setActor] at hm; exact hm)
    · exact hT.prioPlain i m (by rw [hst i hi] at hm; exact hm)
  · intro d c
    unfold soleCall
    rw [hbox d, hparked d]
    exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT hparked
      (by
        intro s0 d0 k0
        constructor
        · intro hk
          rw [hph s0] at hk
          exact hk
        · intro hk
          rw [← hph s0] at hk
          exact hk)
      d p hp s
  · intro c d k hk
    exact parkedOnly_transport w w' hT hparked (by intro i m hm; rw [hbox i] at hm; exact hm)
      (by
        intro c0 d0 k0 hk0
        rw [hph c0] at hk0
        exact hk0)
      c d k hk
      (by simpa [w'] using life_setActor w id ({ (w.st id) with prio := prio, nextMid := n }) (by simp))
  · simpa [w'] using life_setActor w id ({ (w.st id) with prio := prio, nextMid := n }) (by simp)
  · exact fun d c ho => owed_phase w w' hT
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi])
      (fun i => by by_cases hi : i = id <;> simp [w', setActor, hi]) d c ho

/-- A wake is a plain priority message, or no change. -/
theorem try_wake_tag (D : Description) (w : World) (dst : InstId) (label : String) (writer : InstId)
    (hT : CallTagInv w) : CallTagInv (tryWake D w dst label writer) := by
  by_cases hif : ((w.st dst).life == .alive &&
      decide (prioLoad (w.st dst).prio < capPrio D w.N dst) &&
      !((w.st dst).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif]
    let wake : Msg :=
      { label := label, sender := writer, callFrom := none, reliable := false,
        mid := (w.st dst).nextMid }
    have hmiss : ((w.st dst).prio.any fun p => p.label == wake.label) = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true] at hif
      simpa [wake] using hif.2
    have hup : upsertPrio (w.st dst).prio wake = (w.st dst).prio ++ [wake] := by
      simp [upsertPrio, hmiss]
    apply prio_keep_tag w dst (upsertPrio (w.st dst).prio wake) ((w.st dst).nextMid + 1) hT
    intro m hm
    rw [hup] at hm
    simp [List.mem_append, List.mem_singleton] at hm
    rcases hm with hold | heq
    · exact hT.prioPlain dst m hold
    · simp [heq, wake]
  · simp [tryWake, hif]
    exact hT

theorem wake_readers_tag (D : Description) (w : World) (dst label : String) (writer : InstId)
    (ids : List InstId) (hT : CallTagInv w) :
    CallTagInv (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => simpa
  | cons i ids ih =>
    simp
    exact ih _ (try_wake_tag D w i label writer hT)

/-- Moving a running handler into `awaitEffect` or `awaitPeer` keeps its reply. -/
theorem carry_step_tag (w : World) (id : InstId) (kRun : Cont) (e : Eff) (es : List Eff) (ph : Phase)
    (hT : CallTagInv w) (hph : (w.st id).phase = .run kRun) (hrest : kRun.rest = e :: es)
    (hne : e ≠ .reply) (hterm : e ≠ .terminate) (hcar : carriedCont ph = some (afterHead kRun))
    (hnotA : ∀ d k, ph ≠ .awaitReply d k) (hnotP : ∀ d k, ph ≠ .parked d true k) :
    CallTagInv (setActor w id { (w.st id) with phase := ph }) := by
  let w' := setActor w id { (w.st id) with phase := ph }
  have hst (i : InstId) (hi : i ≠ id) : w'.st i = w.st i := by simp [w', setActor, hi]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hprioL (i : InstId) : (w'.st i).prio = (w.st i).prio := by
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hduty (c : InstId) :
      handlerOwes c (w'.st id).phase ∨ replyPending c (w'.st id).phase ↔
        handlerOwes c (w.st id).phase ∨ replyPending c (w.st id).phase := by
    have hshape := replyShape_tail c kRun e es hrest hne hterm
    have hold := (shape_split c kRun).trans hshape
    have hnew := carried_duty c ph (afterHead kRun) (by simp [w', setActor, hcar])
    constructor
    · intro h
      have hphW : (w'.st id).phase = ph := by simp [w', setActor]
      rw [hphW] at h
      have h' := hold.mpr (hnew.mp h)
      rwa [hph]
    · intro h
      have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
        rw [hph] at h
        exact h
      simpa [w', setActor] using hnew.mpr (hold.mp h0)
  apply call_tag_duty w w' hT
  · intro d c
    exact mail_iff_lists w w' hbox hparked d c
  · intro i c
    by_cases hi : i = id
    · rw [hi]
      exact hduty c
    · exact (by
        have hpe : (w'.st i).phase = (w.st i).phase := by simp [hst i hi]
        constructor
        · intro h
          rcases h with ho | hp
          · exact Or.inl (by simpa [← hpe] using ho)
          · exact Or.inr (by simpa [← hpe] using hp)
        · intro h
          rcases h with ho | hp
          · exact Or.inl (by simpa [hpe] using ho)
          · exact Or.inr (by simpa [hpe] using hp))
  · intro c d k hph'
    by_cases hc : c = id
    · exact absurd hph' (by
        have hbad := hph'
        rw [hc, show (w'.st id).phase = ph from by simp [w', setActor]] at hbad
        exact False.elim (hnotA d k hbad))
    · simpa [hst c hc] using hph'
  · intro c d k hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro c d k hph'
    by_cases hc : c = id
    · exact absurd hph' (by
        have hbad := hph'
        rw [hc, show (w'.st id).phase = ph from by simp [w', setActor]] at hbad
        exact False.elim (hnotP d k hbad))
    · simpa [hst c hc] using hph'
  · intro c d k hph'
    by_cases hc : c = id
    · simp [hc, hph] at hph'
    · simpa [← hst c hc] using hph'
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprioL i] at hm; exact hm)
  · intro d c
    unfold soleCall
    rw [hbox d, hparked d]
    exact hT.sole d c
  · intro d p hp s
    exact parkFrom_transport w w' hT hparked
      (by
        intro s0 d0 k0
        constructor
        · intro hk
          by_cases hs0 : s0 = id
          · rw [hs0, show (w'.st id).phase = ph from by simp [w', setActor]] at hk
            exact absurd hk (hnotP d0 k0)
          · simpa [hst s0 hs0] using hk
        · intro hk
          by_cases hs0 : s0 = id
          · simp [hs0, hph] at hk
          · simpa [← hst s0 hs0] using hk)
      d p hp s
  · intro c d k hk
    exact parkedOnly_transport w w' hT hparked (by intro i m hm; rw [hbox i] at hm; exact hm)
      (by
        intro c0 d0 k0 hk0
        by_cases hc0 : c0 = id
        · rw [hc0, show (w'.st id).phase = ph from by simp [w', setActor]] at hk0
          exact absurd hk0 (hnotP d0 k0)
        · simpa [hst c0 hc0] using hk0)
      c d k hk
      (by simpa [w'] using life_setActor w id ({ (w.st id) with phase := ph }) (by simp))
  · simpa [w'] using life_setActor w id ({ (w.st id) with phase := ph }) (by simp)
  · intro d c ho
    have hs := stamp_set w id ({ (w.st id) with phase := ph }) (by simp) (by simp)
    by_cases hd : d = id
    · have hback := (hduty c).mp (by simpa [w', hd] using ho)
      rw [hd]
      change ((setActor w id ({ (w.st id) with phase := ph })).st id).oweId =
        some ((setActor w id ({ (w.st id) with phase := ph })).st c).waitId
      rw [(hs id).1, (hs c).2]
      exact hT.owedId id c hback
    · by_cases hc : c = id
      · rw [hc] at ho
        have hpre : handlerOwes id (w.st d).phase ∨ replyPending id (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        obtain ⟨k0, hk0⟩ := hT.oweOwner d id hpre
        simp [hph] at hk0
      · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        simpa [w', setActor, hd, hc, (hs d).1, (hs c).2] using hT.owedId d c hpre

/-- A plain send. The new message has `callFrom` empty, so it is not a call tag.
The sender proceeds when the mailbox has room, and otherwise parks with the call bit clear. -/
theorem plain_move_tag (w w' : World) (sender dst : InstId) (msg : Msg) (k kRun : Cont)
    (e : Eff) (es : List Eff) (hT : CallTagInv w) (hph : (w.st sender).phase = .run kRun)
    (hrest : kRun.rest = e :: es) (hne : e ≠ .reply) (hterm : e ≠ .terminate)
    (hk : k = afterHead kRun) (hfrom : msg.callFrom = none)
    (hother : ∀ i, i ≠ sender → (w'.st i).phase = (w.st i).phase)
    (hboxI : ∀ i, i ≠ dst → (w'.st i).box = (w.st i).box)
    (hparkI : ∀ i, i ≠ dst → (w'.st i).parked = (w.st i).parked)
    (hmode :
      ((w'.st sender).phase = (proceed (w.st sender) k).phase ∧
          (w'.st dst).box = (w.st dst).box ++ [msg] ∧
          (w'.st dst).parked = (w.st dst).parked) ∨
        ((w'.st sender).phase = .parked dst false k ∧
          (w'.st dst).parked =
            (w.st dst).parked ++ [{ sender := sender, msg := msg, isCall := false }] ∧
          (w'.st dst).box = (w.st dst).box))
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (howed : ∀ i, (w'.st i).oweId = (w.st i).oweId)
    (hwait : ∀ i, (w'.st i).waitId = (w.st i).waitId) : CallTagInv w' := by
  have hmail (d c : InstId) : mailCall w' d c ↔ mailCall w d c := by
    constructor
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨q, hq, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · rw [hd, hboxA, List.mem_append] at hm
            rcases hm with hold | heq
            · exact Or.inl ⟨m, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              cases hcf
          · rw [hd, hboxP] at hm
            exact Or.inl ⟨m, by rw [hd]; exact hm, hcf⟩
        · rw [hboxI d hd] at hm
          exact Or.inl ⟨m, hm, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · rw [hd, hparkA] at hq
            exact Or.inr ⟨q, by rw [hd]; exact hq, hcf⟩
          · rw [hd, hparkP, List.mem_append] at hq
            rcases hq with hold | heq
            · exact Or.inr ⟨q, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              cases hcf
        · rw [hparkI d hd] at hq
          exact Or.inr ⟨q, hq, hcf⟩
    · intro hm
      rcases hm with ⟨m, hm, hcf⟩ | ⟨q, hq, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · exact Or.inl ⟨m, by rw [hd] at hm; rw [hd, hboxA]; exact List.mem_append_left _ hm, hcf⟩
          · exact Or.inl ⟨m, by rw [hd] at hm; rw [hd, hboxP]; exact hm, hcf⟩
        · exact Or.inl ⟨m, by rw [hboxI d hd]; exact hm, hcf⟩
      · by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · exact Or.inr ⟨q, by rw [hd] at hq; rw [hd, hparkA]; exact hq, hcf⟩
          · exact Or.inr ⟨q, by rw [hd] at hq; rw [hd, hparkP]; exact List.mem_append_left _ hq, hcf⟩
        · exact Or.inr ⟨q, by rw [hparkI d hd]; exact hq, hcf⟩
  have hduty (c : InstId) :
      handlerOwes c (w'.st sender).phase ∨ replyPending c (w'.st sender).phase ↔
        handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase := by
    have hshape := replyShape_tail c kRun e es hrest hne hterm
    have hold := (shape_split c kRun).trans hshape
    rcases hmode with ⟨hproc, _, _⟩ | ⟨hparked, _, _⟩
    · cases hes : es with
      | nil =>
        have hidle : (w'.st sender).phase = .idle := by
          rw [hproc]
          simp [proceed, hk, afterHead, hrest, hes]
        constructor
        · intro h
          simp [hidle, handlerOwes, replyPending, carriedCont] at h
        · intro h
          have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
            rw [hph] at h
            exact h
          have hzero : replyCount (afterHead kRun).rest = 0 := by
            simp [afterHead, hrest, hes, replyCount]
          exact False.elim (not_shape_zero c (afterHead kRun) hzero (hold.mp h0))
      | cons _ _ =>
        have hrun : (w'.st sender).phase = .run k := by
          rw [hproc]
          simp [proceed, hk, afterHead, hrest, hes]
        have hcar : carriedCont (w'.st sender).phase = some k := by simp [carriedCont, hrun]
        have hnew := carried_duty c _ k hcar
        constructor
        · intro h
          have h' := hold.mpr (by rw [← hk]; exact hnew.mp h)
          rwa [hph]
        · intro h
          have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
            rw [hph] at h
            exact h
          exact hnew.mpr (by rw [hk]; exact hold.mp h0)
    · have hcar : carriedCont (w'.st sender).phase = some k := by simp [carriedCont, hparked]
      have hnew := carried_duty c _ k hcar
      constructor
      · intro h
        have h' := hold.mpr (by rw [← hk]; exact hnew.mp h)
        rwa [hph]
      · intro h
        have h0 : handlerOwes c (.run kRun) ∨ replyPending c (.run kRun) := by
          rw [hph] at h
          exact h
        exact hnew.mpr (by rw [hk]; exact hold.mp h0)
  apply call_tag_duty w w' hT
  · exact hmail
  · intro i c
    by_cases hi : i = sender
    · rw [hi]
      exact hduty c
    · have hpe : (w'.st i).phase = (w.st i).phase := hother i hi
      constructor
      · intro h
        rcases h with ho | hp
        · exact Or.inl (by simpa [← hpe] using ho)
        · exact Or.inr (by simpa [← hpe] using hp)
      · intro h
        rcases h with ho | hp
        · exact Or.inl (by simpa [hpe] using ho)
        · exact Or.inr (by simpa [hpe] using hp)
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hproc, _, _⟩ | ⟨hparked, _, _⟩
      · rw [hc, hproc] at hph'
        cases hes : es <;> simp [proceed, hk, afterHead, hrest, hes] at hph'
      · rw [hc, hparked] at hph'
        cases hph'
    · rw [hother c hc] at hph'
      exact hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · simp [hc, hph] at hph'
    · rw [← hother c hc] at hph'
      exact hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hproc, _, _⟩ | ⟨hparked, _, _⟩
      · rw [hc, hproc] at hph'
        cases hes : es <;> simp [proceed, hk, afterHead, hrest, hes] at hph'
      · rw [hc, hparked] at hph'
        cases hph'
    · rw [hother c hc] at hph'
      exact hph'
  · intro c d kA hph'
    by_cases hc : c = sender
    · simp [hc, hph] at hph'
    · rw [← hother c hc] at hph'
      exact hph'
  · intro i m hm
    exact hT.prioPlain i m (by rw [hprio i] at hm; exact hm)
  · intro d c
    unfold soleCall
    by_cases hd : d = dst
    · rcases hmode with ⟨_, hboxA, hparkA⟩ | ⟨_, hparkP, hboxP⟩
      · rw [hd, hboxA, hparkA, count_append]
        have hzero : countCall [msg] c = 0 := by simp [countCall, hfrom]
        rw [hzero, Nat.add_zero]
        simpa [soleCall] using hT.sole dst c
      · rw [hd, hboxP, hparkP, countParkedCall_append]
        have hzero : countParkedCall [{ sender := sender, msg := msg, isCall := false }] c = 0 := by
          simp [countParkedCall, hfrom]
        rw [hzero, Nat.add_zero]
        simpa [soleCall] using hT.sole dst c
    · rw [hboxI d hd, hparkI d hd]
      simpa [soleCall] using hT.sole d c
  · intro d q hq s0
    rcases hmode with ⟨hproc, _, hparkA⟩ | ⟨hparked, hparkP, _⟩
    · have hq0 : q ∈ (w.st d).parked := by
        by_cases hd : d = dst
        · rw [hd, hparkA] at hq
          rw [hd]
          exact hq
        · rw [hparkI d hd] at hq
          exact hq
      by_cases hs0 : s0 = sender
      · constructor
        · intro hc
          obtain ⟨_, _, hkP⟩ := (hT.parkFrom d q hq0 s0).mp hc
          rw [hs0, hph] at hkP
          cases hkP
        · intro ⟨_, _, hkP⟩
          rw [hs0, hproc] at hkP
          cases hes : es <;> simp [proceed, hk, afterHead, hrest, hes] at hkP
      · have hiff := hT.parkFrom d q hq0 s0
        have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
        constructor
        · intro hc
          obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
          exact ⟨hseq, kP, by rw [hpe]; exact hkP⟩
        · intro ⟨hseq, kP, hkP⟩
          exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; exact hkP⟩
    · by_cases hd : d = dst
      · rw [hd, hparkP, List.mem_append] at hq
        rcases hq with hold | hnew
        · have hq0 : q ∈ (w.st dst).parked := hold
          by_cases hs0 : s0 = sender
          · constructor
            · intro hc
              obtain ⟨_, _, hkP⟩ := (hT.parkFrom dst q hq0 s0).mp hc
              rw [hs0, hph] at hkP
              cases hkP
            · intro ⟨_, _, hkP⟩
              rw [hs0, hparked] at hkP
              cases hkP
          · have hiff := hT.parkFrom dst q hq0 s0
            have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
            constructor
            · intro hc
              obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
              exact ⟨hseq, kP, by rw [hd, hpe]; exact hkP⟩
            · intro ⟨hseq, kP, hkP⟩
              exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; rw [hd] at hkP; exact hkP⟩
        · simp [List.mem_singleton] at hnew
          rw [hnew]
          constructor
          · intro hc
            rw [hfrom] at hc
            cases hc
          · intro ⟨hseq, _, hkP⟩
            rw [← hseq, hparked] at hkP
            cases hkP
      · rw [hparkI d hd] at hq
        by_cases hs0 : s0 = sender
        · constructor
          · intro hc
            obtain ⟨_, _, hkP⟩ := (hT.parkFrom d q hq s0).mp hc
            rw [hs0, hph] at hkP
            cases hkP
          · intro ⟨_, _, hkP⟩
            rw [hs0, hparked] at hkP
            cases hkP
        · have hiff := hT.parkFrom d q hq s0
          have hpe : (w'.st s0).phase = (w.st s0).phase := hother s0 hs0
          constructor
          · intro hc
            obtain ⟨hseq, kP, hkP⟩ := hiff.mp hc
            exact ⟨hseq, kP, by rw [hpe]; exact hkP⟩
          · intro ⟨hseq, kP, hkP⟩
            exact hiff.mpr ⟨hseq, kP, by rw [← hpe]; exact hkP⟩
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hproc, _, _⟩ | ⟨hparked, _, _⟩
      · rw [hc, hproc] at hph'
        cases hes : es <;> simp [proceed, hk, afterHead, hrest, hes] at hph'
      · rw [hc, hparked] at hph'
        cases hph'
    · have hph0 : (w.st c).phase = .parked d true kA := by
        rw [hother c hc] at hph'
        exact hph'
      exact parkedOnly_lift w w' hT c d kA hph0 (hlife d)
        (fun q hq _ _ => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
            · rw [hd] at hq
              rw [hd, hparkA]
              exact hq
            · rw [hd] at hq
              rw [hd, hparkP]
              exact List.mem_append_left _ hq
          · rw [hparkI d hd]
            exact hq)
        (fun q hq hcf => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
            · rw [hd, hparkA] at hq
              rw [hd]
              exact hq
            · rw [hd, hparkP, List.mem_append] at hq
              rcases hq with hold | heq
              · rw [hd]
                exact hold
              · simp [List.mem_singleton] at heq
                rw [heq, hfrom] at hcf
                cases hcf
          · rw [← hparkI d hd]
            exact hq)
        (fun m hm hcf => by
          by_cases hd : d = dst
          · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
            · rw [hd, hboxA, List.mem_append] at hm
              rcases hm with hold | heq
              · rw [hd]
                exact hold
              · simp [List.mem_singleton] at heq
                rw [heq, hfrom] at hcf
                cases hcf
            · rw [hd, hboxP] at hm
              rw [hd]
              exact hm
          · rw [← hboxI d hd]
            exact hm)
  · exact lifeKeep_of_eq hlife
  · intro d c ho
    by_cases hd : d = sender
    · have hback : handlerOwes c (w.st sender).phase ∨ replyPending c (w.st sender).phase :=
        (hduty c).mp (by simpa [hd] using ho)
      have hc : c ≠ sender := by
        intro heq
        obtain ⟨k0, hk0⟩ := hT.oweOwner sender c hback
        rw [heq, hph] at hk0
        cases hk0
      rw [hd, howed sender, hT.owedId sender c hback, hwait c]
    · by_cases hc : c = sender
      · rw [hc] at ho
        have hpre : handlerOwes sender (w.st d).phase ∨ replyPending sender (w.st d).phase := by
          simpa [hother d hd] using ho
        obtain ⟨k0, hk0⟩ := hT.oweOwner d sender hpre
        rw [hph] at hk0
        cases hk0
      · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          simpa [hother d hd] using ho
        rw [howed d, hT.owedId d c hpre, hwait c]

/-- Enqueueing a non-call keeps every call tag. A dead target just proceeds. -/
theorem enqueue_send_tag (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (kRun : Cont) (e : Eff) (es : List Eff) (hT : CallTagInv w)
    (hph : (w.st sender).phase = .run kRun) (hrest : kRun.rest = e :: es) (hne : e ≠ .reply)
    (hterm : e ≠ .terminate) (hfrom : msg.callFrom = none) :
    CallTagInv (enqueueOrPark w D sender dst msg false (afterHead kRun)) := by
  have hphase (a : Actor) :
      (proceed a (afterHead kRun)).phase = (proceed (w.st sender) (afterHead kRun)).phase := by
    cases hr : (afterHead kRun).rest <;> simp [proceed, hr]
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hparkS : (w.st sender).parked = [] := by
          have h := hroom.1
          rwa [← hsame] at h
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by
          have h := hroom.2
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_room_self_send w D sender msg (afterHead kRun) hliveS hparkS hcapS]
        apply plain_move_tag w _ sender sender { msg with mid := (w.st sender).nextMid } (afterHead kRun) kRun e es hT hph hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inl ⟨?_, ?_, ?_⟩
          · simp [setActor, hphase]
          · simp [setActor, proceed_fields, chargeSender, bumpToken]
          · simp [setActor, proceed_fields, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_fields, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_life, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_stamps, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_stamps, chargeSender, bumpToken]
      · rw [enqueue_room_other_send w D sender dst msg (afterHead kRun) hlive hsame hroom.1 hroom.2]
        apply plain_move_tag w _ sender dst { msg with mid := (w.st dst).nextMid } (afterHead kRun) kRun e es hT hph hrest hne
          hterm rfl hfrom
        · intro i hi
          by_cases hid : i = dst
          · have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, hi, hid, hflip, proceed]
          · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, proceed_fields, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, proceed_fields, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · have hflip : ¬ dst = sender := fun h => hsame h.symm
          refine Or.inl ⟨by simp [setActor, hphase, proceed_fields, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, hflip, issueCall, ite_true]
          · simp [setActor, hflip, issueCall, ite_true]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, proceed_fields, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : ¬ i = dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, hflip, show ¬(i = dst) from hne, proceed_life, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_life, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_life, chargeSender, bumpToken]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : i ≠ dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, proceed_stamps, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_stamps, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_stamps, chargeSender, bumpToken]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : i ≠ dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, proceed_stamps, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_stamps, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_stamps, chargeSender, bumpToken]
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          have h := hroom
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_park_self w D sender msg false (afterHead kRun) hliveS hroomS]
        apply plain_move_tag w _ sender sender { msg with mid := (w.st sender).nextMid } (afterHead kRun) kRun e es hT hph hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inr ⟨by simp [setActor, issueCall, ite_true, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
          · simp [setActor, issueCall, ite_true, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_life, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_stamps, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, proceed_stamps, chargeSender, bumpToken]
      · rw [enqueue_park_other w D sender dst msg false (afterHead kRun) hlive hsame hroom]
        apply plain_move_tag w _ sender dst { msg with mid := (w.st dst).nextMid } (afterHead kRun) kRun e es hT hph hrest hne
          hterm rfl hfrom
        · intro i hi
          by_cases hid : i = dst
          · have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, hi, hid, hflip]
          · simp [setActor, hi, hid]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · intro i hi
          by_cases hs : i = sender
          · simp [setActor, hs, chargeSender, bumpToken]
          · simp [setActor, hs, hi]
        · have hflip : ¬ dst = sender := fun h => hsame h.symm
          refine Or.inr ⟨by simp [setActor, issueCall, ite_true, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, hflip, issueCall, ite_true]
          · simp [setActor, hflip, issueCall, ite_true]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : ¬ i = dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, hflip, show ¬(i = dst) from hne, proceed_life, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_life, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_life, chargeSender, bumpToken]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : i ≠ dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, proceed_stamps, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_stamps, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_stamps, chargeSender, bumpToken]
        · intro i
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · have hne : i ≠ dst := fun h => hsame (hi.symm.trans h)
            simp [setActor, hi, hne, proceed_stamps, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · simp [setActor, hi, hid, hflip, proceed_stamps, chargeSender, bumpToken]
            · simp [setActor, hi, hid, proceed_stamps, chargeSender, bumpToken]
  · rw [enqueue_dead w D sender dst msg (afterHead kRun) hlive]
    exact run_tail_tag w sender kRun e es hT hph hrest hne hterm

/-- A self-schedule either proceeds or arms one plain priority label. The overflow
branch is the one `lane_has_room` rules out for a declared label. -/
theorem schedule_tag (I : Impl) (w : World) (hT : CallTagInv w) (id : InstId) (k : Cont)
    (label : String) (es : List Eff) (hph : (w.st id).phase = .run k)
    (hrest : k.rest = .selfSchedule label :: es)
    (hroom : ((w.st id).prio.any fun p => p.label == label) = false →
      prioLoad (w.st id).prio < capPrio I.desc w.N id) :
    CallTagInv (execRun I w id (w.st id) k) := by
  simp [execRun, hrest]
  cases hany : ((w.st id).prio.any fun p => p.label == label)
  · have hlt : prioLoad (w.st id).prio < capPrio I.desc w.N id := hroom hany
    rw [List.any_eq_false] at hany
    have hno : ¬ ∃ x, x ∈ (w.st id).prio ∧ x.label = label := by
      intro ⟨x, hx, hl⟩
      have hf := hany x hx
      rw [(beq_iff_eq).mpr hl] at hf
      simp at hf
    simp [hno, hlt]
    let msg : Msg :=
      { label := label, sender := id, callFrom := none, reliable := true, mid := (w.st id).nextMid }
    let grown := upsertPrio (w.st id).prio msg
    let armed : Actor := { (w.st id) with prio := grown, nextMid := (w.st id).nextMid + 1 }
    have hplain : ∀ m, m ∈ grown → m.callFrom = none := by
      intro m hm
      simp [upsertPrio, grown, msg, hno, List.mem_append, List.mem_singleton] at hm
      rcases hm with hold | heq
      · exact hT.prioPlain id m hold
      · rw [heq]
    have hP := prio_keep_tag w id grown ((w.st id).nextMid + 1) hT hplain
    have hphP : ((setActor w id armed).st id).phase = .run k := by
      simp [setActor, armed, hph]
    have hrun := run_tail_tag (setActor w id armed) id k
      (.selfSchedule label) es hP hphP hrest (by intro h; cases h) (by intro h; cases h)
    have hself : (setActor w id armed).st id = armed := by simp [setActor]
    rw [setActor_same, hself] at hrun
    simpa [grown, msg, armed] using hrun
  · rw [List.any_eq_true] at hany
    obtain ⟨x, hx, hb⟩ := hany
    have hyes : ∃ x, x ∈ (w.st id).prio ∧ x.label = label := ⟨x, hx, (beq_iff_eq).mp hb⟩
    simp [hyes]
    exact run_tail_tag w id k (.selfSchedule label) es hT hph hrest
      (by intro h; cases h) (by intro h; cases h)

/-- Going idle and dropping a mailbox that holds no call tag. -/
theorem idle_clear_tag (w : World) (id : InstId) (hT : CallTagInv w)
    (hnotA : ∀ d k, (w.st id).phase ≠ .awaitReply d k)
    (hnotP : ∀ d k, (w.st id).phase ≠ .parked d true k)
    (hquiet : ∀ c, ¬handlerOwes c (w.st id).phase ∧ ¬replyPending c (w.st id).phase)
    (hcallB : ∀ m, m ∈ (w.st id).box → m.callFrom = none)
    (hcallP : ∀ p, p ∈ (w.st id).parked → p.msg.callFrom = none) :
    CallTagInv (setActor w id { (w.st id) with phase := .idle, box := [], prio := [], parked := [] }) := by
  let w' := setActor w id { (w.st id) with phase := .idle, box := [], prio := [], parked := [] }
  have hst (i : InstId) (hi : i ≠ id) : w'.st i = w.st i := by simp [w', setActor, hi]
  apply call_tag_stable w w' hT
  · intro d c
    constructor
    · intro hm
      by_cases hd : d = id
      · simp [w', setActor, hd, mailCall] at hm
      · rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
        · exact Or.inl ⟨m, by rw [hst d hd] at hm; exact hm, hc⟩
        · exact Or.inr ⟨p, by rw [hst d hd] at hp; exact hp, hc⟩
    · intro hm
      by_cases hd : d = id
      · rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
        · exact False.elim (by rw [hcallB m (by rw [hd] at hm; exact hm)] at hc; cases hc)
        · exact False.elim (by rw [hcallP p (by rw [hd] at hp; exact hp)] at hc; cases hc)
      · rcases hm with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
        · exact Or.inl ⟨m, by rw [← hst d hd] at hm; exact hm, hc⟩
        · exact Or.inr ⟨p, by rw [← hst d hd] at hp; exact hp, hc⟩
  · intro i c
    by_cases hi : i = id
    · constructor
      · intro h
        simp [w', hi, setActor, handlerOwes, carriedCont] at h
      · intro h
        exact False.elim ((hquiet c).1 (by rw [hi] at h; exact h))
    · exact owes_iff_carried _ _ (by simp [hst i hi]) c
  · intro i c
    by_cases hi : i = id
    · constructor
      · intro h
        simp [w', hi, setActor, replyPending, carriedCont] at h
      · intro h
        exact False.elim ((hquiet c).2 (by rw [hi] at h; exact h))
    · exact pending_iff_carried _ _ (by simp [hst i hi]) c
  · intro c d k hph'
    by_cases hc : c = id
    · simp [w', hc, setActor] at hph'
    · rw [hst c hc] at hph'
      exact hph'
  · intro c d k hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      exact absurd hph' (hnotA d k)
    · rw [← hst c hc] at hph'
      exact hph'
  · intro c d k hph'
    by_cases hc : c = id
    · simp [w', hc, setActor] at hph'
    · rw [hst c hc] at hph'
      exact hph'
  · intro c d k hph'
    by_cases hc : c = id
    · rw [hc] at hph'
      exact absurd hph' (hnotP d k)
    · rw [← hst c hc] at hph'
      exact hph'
  · intro i m hm
    by_cases hi : i = id
    · simp [w', hi, setActor, List.mem_nil_iff] at hm
    · exact hT.prioPlain i m (by rw [hst i hi] at hm; exact hm)
  · intro d c
    by_cases hd : d = id
    · unfold soleCall
      simp [w', setActor, hd, countCall, countParkedCall]
    · unfold soleCall
      rw [show (w'.st d).box = (w.st d).box from by rw [hst d hd]]
      rw [show (w'.st d).parked = (w.st d).parked from by rw [hst d hd]]
      exact hT.sole d c
  · intro d p hp s
    have hp0 : p ∈ (w.st d).parked := by
      by_cases hd : d = id
      · simp [w', setActor, hd, List.mem_nil_iff] at hp
      · rw [hst d hd] at hp
        exact hp
    by_cases hs : s = id
    · constructor
      · intro hc
        obtain ⟨_, _, hk⟩ := (hT.parkFrom d p hp0 s).mp hc
        rw [hs] at hk
        exact absurd hk (hnotP d _)
      · intro ⟨_, _, hk⟩
        simp [w', setActor, hs] at hk
    · have hpe : (w'.st s).phase = (w.st s).phase := by rw [hst s hs]
      constructor
      · intro hc
        obtain ⟨hseq, k, hk⟩ := (hT.parkFrom d p hp0 s).mp hc
        exact ⟨hseq, k, by rw [hpe]; exact hk⟩
      · intro ⟨hseq, k, hk⟩
        exact (hT.parkFrom d p hp0 s).mpr ⟨hseq, k, by rw [← hpe]; exact hk⟩
  · intro c d k hk
    by_cases hc : c = id
    · simp [w', setActor, hc] at hk
    · have hph0 : (w.st c).phase = .parked d true k := by
        rw [hst c hc] at hk
        exact hk
      by_cases hd : d = id
      · rw [hd]
        rcases hT.parkedOnly c id k (by rw [hd] at hph0; exact hph0) with
          ⟨_, ⟨p, hp, _, hcf⟩, _⟩ | ⟨hl, _, _⟩
        · exact False.elim (by rw [hcallP p hp] at hcf; cases hcf)
        · exact Or.inr ⟨by simpa [w', setActor] using hl,
            fun ⟨p, hp, _⟩ => by simp [w', setActor] at hp,
            fun ⟨m, hm, _⟩ => by simp [w', setActor] at hm⟩
      · exact parkedOnly_lift w w' hT c d k hph0 (by rw [hst d hd])
          (fun p hp _ _ => by rw [← hst d hd] at hp; exact hp)
          (fun p hp _ => by rw [hst d hd] at hp; exact hp)
          (fun m hm _ => by rw [hst d hd] at hm; exact hm)
  · simpa [w'] using life_setActor w id
      ({ (w.st id) with phase := .idle, box := [], prio := [], parked := [] }) (by simp)
  · intro d c ho
    have hs := stamp_set w id
      ({ (w.st id) with phase := .idle, box := [], prio := [], parked := [] }) (by simp) (by simp)
    by_cases hd : d = id
    · rw [hd] at ho
      rcases ho with ⟨_, hk0, _⟩ | ⟨_, hk0, _⟩ <;>
        simp [w', setActor, carriedCont] at hk0
    · by_cases hc : c = id
      · rw [hc] at ho
        have hpre : handlerOwes id (w.st d).phase ∨ replyPending id (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        obtain ⟨k, hk⟩ := hT.oweOwner d id hpre
        exact absurd hk (hnotA d k)
      · have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
          simpa [w', setActor, hd] using ho
        rw [(hs d).1, (hs c).2]
        exact hT.owedId d c hpre

/-- Releasing a list of non-call parked senders. Each sender other than the owner
is resumed from `.parked _ false`. -/
theorem release_plain_tag (w : World) (id : InstId) (ps : List Parked) (hT : CallTagInv w)
    (hsenders : ∀ p1 p2, p1 ∈ ps → p2 ∈ ps → p1.sender = p2.sender → p1 = p2)
    (hnodup : ps.Nodup)
    (hstep : ∀ p, p ∈ ps → p.isCall = false ∧
      (p.sender = id ∨ ∃ k, (w.st p.sender).phase = .parked id false k)) :
    CallTagInv (releaseParked w id ps) := by
  induction ps generalizing w with
  | nil =>
    simp [releaseParked]
    exact hT
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    have hp := hstep p (by simp)
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [ite_eq_left hskip]
      exact ih w hT
        (fun q1 q2 h1 h2 => hsenders q1 q2 (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2))
        (List.nodup_cons.mp hnodup).2
        (fun q hq => hstep q (List.mem_cons_of_mem _ hq))
    · rw [ite_eq_right hskip]
      have hne : p.sender ≠ id := by
        intro hs
        simp [hp.1, hs] at hskip
      rcases hp.2 with hsid | ⟨kS, hph⟩
      · exact absurd hsid hne
      · have h1 := resume_send_tag w p.sender id kS hT hph
        exact ih _ h1
          (fun q1 q2 h1m h2m heq => by
            have hsame := hsenders q1 q2 (List.mem_cons_of_mem _ h1m) (List.mem_cons_of_mem _ h2m) heq
            exact hsame)
          (List.nodup_cons.mp hnodup).2
          (fun q hq => by
            have hold := hstep q (List.mem_cons_of_mem _ hq)
            refine ⟨hold.1, ?_⟩
            rcases hold.2 with hsid | ⟨k, hk⟩
            · exact Or.inl hsid
            · have hqs : q.sender ≠ p.sender := by
                intro heq
                have hqP : q = p := hsenders q p (List.mem_cons_of_mem _ hq) (by simp) heq
                exact (List.nodup_cons.mp hnodup).1 (by rw [← hqP]; exact hq)
              exact Or.inr ⟨k, by simp [setActor, hqs, hk]⟩)

theorem deliver_running (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    a1.phase = .idle ∨ ∃ k, a1.phase = .run k := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact Or.inl rfl
    · next tr _ =>
      split at h
      · cases h
      · cases h
        cases tr.program with
        | nil => exact Or.inl rfl
        | cons _ _ => exact Or.inr ⟨_, rfl⟩

theorem recvPrio_keeps_call (I : Impl) (w w' : World) (id caller callee : InstId) (k : Cont)
    (h : apply I (.recvPrio id) w = some w')
    (hc : CallWait (w'.st caller).phase callee k) : CallWait (w.st caller).phase callee k := by
  simp only [apply] at h
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    by_cases hlive : (w.st id).life = .alive
    · by_cases hidle : (w.st id).phase = .idle
      · simp only [hp, hlive, hidle] at h
        split at h
        · cases h
        · split at h
          · cases h
          · next w1 a1 hd =>
            cases h
            have hst := deliver_st I w id _ m w1 a1 caller hd
            by_cases hcaller : caller = id
            · rw [hcaller] at hc
              simp [setActor] at hc
              rcases deliver_running I w id _ m w1 a1 hd with hidlePh | ⟨_, hr⟩
              · simp [hidlePh, CallWait] at hc
              · simp [hr, CallWait] at hc
            · simpa [setActor, hcaller, hst] using hc
      · simp [hp, hlive, hidle] at h
    · simp [hp, hlive] at h

theorem bulk_credit_call (I : Impl) (w w1 : World) (id : InstId) (a a1 : Actor) (m : Msg)
    (caller callee : InstId) (k : Cont) (hd : deliver I w id a m = some (w1, a1))
    (hc : CallWait ((creditSender (setActor w1 id a1) (tname id) m.sender).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  have hcred := (credit_phase_life (setActor w1 id a1) (tname id) m.sender caller).1
  rw [hcred] at hc
  by_cases hcaller : caller = id
  · rw [hcaller] at hc
    simp [setActor] at hc
    rcases deliver_running I w id _ m w1 a1 hd with hidle | ⟨_, hr⟩
    · simp [hidle, CallWait] at hc
    · simp [hr, CallWait] at hc
  · have hst := deliver_st I w id _ m w1 a1 caller hd
    simpa [setActor, hcaller, hst] using hc

theorem resume_bit_call (a : Actor) (dst callee : InstId) (c : Bool) (ck k : Cont)
    (hph : a.phase = .parked dst c ck)
    (h : CallWait (resumeSender a c dst).phase callee k) : CallWait a.phase callee k := by
  cases c with
  | false =>
    cases hk : ck.rest <;> simp [resumeSender, hph, hk, proceed, CallWait] at h
  | true =>
    simp [resumeSender, hph, CallWait] at h
    rcases h with ⟨rfl, rfl⟩
    exact Or.inl hph

theorem not_call_runner (w : World) (id : InstId) (a : Actor) (caller callee : InstId) (k : Cont)
    (hnot : ¬ CallWait a.phase callee k)
    (hc : CallWait ((setActor w id a).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  by_cases hcaller : caller = id
  · rw [hcaller] at hc
    simp [setActor] at hc
    exact absurd hc hnot
  · simpa [setActor, hcaller] using hc

theorem deliver_not_call (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (callee : InstId) (k : Cont) (hd : deliver I w id a m = some (w1, a1)) :
    ¬ CallWait a1.phase callee k := by
  intro h
  rcases deliver_running I w id a m w1 a1 hd with hidle | ⟨_, hr⟩
  · simp [hidle, CallWait] at h
  · simp [hr, CallWait] at h

/-- Resuming the parked sender of a delivered message does not create a call wait.
The sender was already parked on this mailbox, and every other phase is unchanged
or is the idle-or-running phase `deliver` just installed. -/
theorem installed_resume_call (I : Impl) (w w1 : World) (id : InstId) (a : Actor) (dm : Msg)
    (installed a1 : Actor) (p : Parked) (credited : InstId) (hM : MailInv w)
    (caller callee : InstId) (k : Cont) (hp : p ∈ (w.st id).parked)
    (hd : deliver I w id a dm = some (w1, a1)) (hphase : installed.phase = a1.phase)
    (hc : CallWait ((setActor (creditSender (setActor w1 id installed) (tname id) credited) p.sender
      (resumeSender ((creditSender (setActor w1 id installed) (tname id) credited).st p.sender)
        p.isCall id)).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  let wA := setActor w1 id installed
  let wB := creditSender wA (tname id) credited
  let resumed := resumeSender (wB.st p.sender) p.isCall id
  have hc0 : CallWait ((setActor wB p.sender resumed).st caller).phase callee k := by
    simpa [wA, wB, resumed] using hc
  have hcred (i : InstId) : (wB.st i).phase = (wA.st i).phase :=
    (credit_phase_life wA (tname id) credited i).1
  by_cases hself : p.sender = id
  · have hseen : (wB.st id).phase = a1.phase := by rw [hcred id]; simp [wA, setActor, hphase]
    have hres : resumed.phase = a1.phase := by
      rcases deliver_running I w id a dm w1 a1 hd with hidle | ⟨_, hr⟩
      · simp [resumed, resumeSender, hself, hseen, hidle]
      · simp [resumed, resumeSender, hself, hseen, hr]
    by_cases hcaller : caller = id
    · rw [hcaller, hself] at hc0
      simp [setActor] at hc0
      rw [hres] at hc0
      exact absurd hc0 (deliver_not_call I w id a dm w1 a1 callee k hd)
    · have hstep : ((setActor wB p.sender resumed).st caller).phase = (wB.st caller).phase := by
        simp [setActor, hcaller, hself]
      rw [hstep] at hc0
      rw [hcred caller] at hc0
      have hA : (wA.st caller).phase = (w.st caller).phase := by
        have hset := setActor_other w1 id caller installed hcaller
        simpa [wA, hset] using (congrArg (·.phase) (deliver_st I w id a dm w1 a1 caller hd))
      simpa [hA] using hc0
  · have hseen : (wB.st p.sender).phase = (w.st p.sender).phase := by
      rw [hcred p.sender]
      have hset := setActor_other w1 id p.sender installed hself
      simpa [wA, hset] using (congrArg (·.phase) (deliver_st I w id a dm w1 a1 p.sender hd))
    by_cases hcaller : caller = p.sender
    · obtain ⟨k0, hparked⟩ := hM.fwd id p hp
      rw [hcaller] at hc0
      simp [setActor] at hc0
      have hbit := resume_bit_call (wB.st p.sender) id callee p.isCall k0 k
        (by rw [hseen]; exact hparked) hc0
      rw [hseen] at hbit
      rw [hcaller]
      exact hbit
    · have hstep : ((setActor wB p.sender resumed).st caller).phase = (wB.st caller).phase := by
        simp [setActor, hcaller]
      rw [hstep, hcred caller] at hc0
      by_cases hid : caller = id
      · rw [hid] at hc0
        simp [wA, setActor] at hc0
        rw [hphase] at hc0
        exact absurd hc0 (deliver_not_call I w id a dm w1 a1 callee k hd)
      · have hA : (wA.st caller).phase = (w.st caller).phase := by
          have hset := setActor_other w1 id caller installed hid
          simpa [wA, hset] using (congrArg (·.phase) (deliver_st I w id a dm w1 a1 caller hd))
        simpa [hA] using hc0

theorem bulk_resume_call (I : Impl) (w w1 : World) (id : InstId) (a a1 : Actor) (p : Parked)
    (ps : List Parked) (hM : MailInv w) (caller callee : InstId) (k : Cont)
    (hpark : (w.st id).parked = p :: ps) (hd : deliver I w id a p.msg = some (w1, a1))
    (hc : CallWait ((setActor (creditSender (setActor w1 id a1) (tname id) p.msg.sender) p.sender
      (resumeSender ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender) p.isCall id)).st
        caller).phase callee k) :
    CallWait (w.st caller).phase callee k :=
  installed_resume_call I w w1 id a p.msg a1 a1 p p.msg.sender hM caller callee k
    (by simpa [hpark] using List.mem_cons_self p ps) hd rfl hc

theorem bulk_admit_call (I : Impl) (w w1 : World) (id : InstId) (a a1 : Actor) (m : Msg)
    (p : Parked) (ps : List Parked) (hM : MailInv w) (caller callee : InstId) (k : Cont)
    (hpark : (w.st id).parked = p :: ps) (hd : deliver I w id a m = some (w1, a1))
    (hc : CallWait ((setActor (creditSender (setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps })
      (tname id) m.sender) p.sender
      (resumeSender ((creditSender (setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps })
        (tname id) m.sender).st p.sender) p.isCall id)).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k :=
  installed_resume_call I w w1 id a m { a1 with box := a1.box ++ [p.msg], parked := ps } a1 p
    m.sender hM caller callee k (by simpa [hpark] using List.mem_cons_self p ps) hd (by simp) hc

theorem recvBulk_keeps_call (I : Impl) (w w' : World) (id : InstId) (hM : MailInv w)
    (caller callee : InstId) (k : Cont) (h : apply I (.recvBulk id) w = some w')
    (hc : CallWait (w'.st caller).phase callee k) : CallWait (w.st caller).phase callee k := by
  simp only [apply] at h
  unfold receiveBulk at h
  by_cases hlive : (w.st id).life = .alive
  · by_cases hidle : (w.st id).phase = .idle
    · simp [hlive, hidle] at h
      cases hbox : (w.st id).box with
      | nil =>
        cases hpark : (w.st id).parked with
        | nil => simp [hbox, hpark] at h
        | cons p ps =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hd =>
            cases h
            exact bulk_resume_call I w w1 id _ a1 p ps hM caller callee k hpark hd hc
      | cons m ms =>
        cases hpark : (w.st id).parked with
        | nil =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hd =>
            cases h
            exact bulk_credit_call I w w1 id _ a1 m caller callee k hd hc
        | cons p ps =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hd =>
            cases h
            exact bulk_admit_call I w w1 id _ a1 m p ps hM caller callee k hpark hd hc
    · simp [hlive, hidle] at h
  · simp [hlive] at h

theorem parked_false_not_call (dst callee : InstId) (k ck : Cont) :
    ¬ CallWait (Phase.parked dst false k) callee ck := by
  intro h
  rcases h with h | h <;> cases h

theorem await_not_call (kw : Cont) (callee : InstId) (k : Cont) :
    ¬ CallWait (Phase.awaitEffect kw) callee k := by
  intro h
  rcases h with h | h <;> cases h

theorem peer_not_call (kw : Cont) (callee : InstId) (k : Cont) :
    ¬ CallWait (Phase.awaitPeer kw) callee k := by
  intro h
  rcases h with h | h <;> cases h

theorem crash_not_call (callee : InstId) (k : Cont) : ¬ CallWait Phase.crashed callee k := by
  intro h
  rcases h with h | h <;> cases h

theorem idle_not_call (callee : InstId) (k : Cont) : ¬ CallWait Phase.idle callee k := by
  intro h
  rcases h with h | h <;> cases h

/-- A resolved route names the template that was asked for. -/
theorem route_name (w : World) (D : Description) (sender : InstId) (dst : String) (id : InstId)
    (h : route w D sender dst = some id) : tname id = dst := by
  simp only [route] at h
  cases ht : templateOf D dst with
  | none => simp [ht] at h
  | some t =>
    simp [ht] at h
    cases hm : t.multiplicity with
    | one =>
      simp [hm] at h
      rcases h with ⟨_, rfl⟩
      rfl
    | perPeer =>
      simp [hm] at h
      cases hk : memberKey sender with
      | none => simp [hk] at h
      | some k =>
        simp [hk] at h
        rcases h with ⟨_, rfl⟩
        rfl

theorem enqueue_plain_call (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (caller callee : InstId) (ck : Cont)
    (hc : CallWait ((enqueueOrPark w D sender dst msg false k).st caller).phase callee ck) :
    CallWait (w.st caller).phase callee ck := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · subst hsame
        rw [enqueue_room_self_send w D sender msg k hlive hroom.1 hroom.2] at hc
        exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
      · rw [enqueue_room_other_send w D sender dst msg k hlive hsame hroom.1 hroom.2] at hc
        have hprev := not_call_runner
          (setActor w dst { (w.st dst) with
            box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
            nextMid := (w.st dst).nextMid + 1 })
          sender (proceed (chargeSender (w.st sender) (tname dst)) k) caller callee ck
          (proceed_not_callwait _ _ _ _) hc
        by_cases hdst : caller = dst
        · subst hdst
          simp [setActor] at hprev
          exact hprev
        · simpa [setActor, hdst] using hprev
    · by_cases hsame : sender = dst
      · subst hsame
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := hroom
        rw [enqueue_park_self w D sender msg false k hlive hroomS] at hc
        exact not_call_runner w sender _ caller callee ck (parked_false_not_call sender callee k ck) hc
      · have hroomO : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst) := hroom
        rw [enqueue_park_other w D sender dst msg false k hlive hsame hroomO] at hc
        have hprev := not_call_runner
          (setActor w dst { (w.st dst) with
            parked := (w.st dst).parked ++
              [{ sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := false }],
            nextMid := (w.st dst).nextMid + 1 })
          sender { chargeSender (w.st sender) (tname dst) with phase := .parked dst false k }
          caller callee ck (parked_false_not_call dst callee k ck) hc
        by_cases hdst : caller = dst
        · subst hdst
          simp [setActor] at hprev
          exact hprev
        · simpa [setActor, hdst] using hprev
  · rw [enqueue_dead w D sender dst msg k hlive] at hc
    exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc

/-- A blocking enqueue either parks the sender on `dst`, or leaves every other actor. -/
theorem enqueue_true_sender (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (caller callee : InstId) (ck : Cont)
    (hc : CallWait ((enqueueOrPark w D sender dst msg true k).st caller).phase callee ck) :
    (caller = sender ∧ callee = dst ∧ ck = k) ∨
      (caller ≠ sender ∧ CallWait (w.st caller).phase callee ck) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by simpa [hsame] using hlive
        have hparkS : (w.st sender).parked = [] := by simpa [hsame] using hroom.1
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by simpa [hsame] using hroom.2
        subst hsame
        rw [enqueue_room_self_call w D sender msg k hliveS hparkS hcapS] at hc
        by_cases hcaller : caller = sender
        · subst hcaller
          simp only [setActor, CallWait] at hc
          rcases hc with hc | hc
          · cases hc
          · cases hc
            left
            exact ⟨rfl, rfl, rfl⟩
        · right
          refine ⟨hcaller, ?_⟩
          simpa [setActor, hcaller] using hc
      · rw [enqueue_room_other_call w D sender dst msg k hlive hsame hroom.1 hroom.2] at hc
        by_cases hcaller : caller = sender
        · subst hcaller
          simp only [setActor, CallWait] at hc
          rcases hc with hc | hc
          · cases hc
          · cases hc
            left
            exact ⟨rfl, rfl, rfl⟩
        · right
          have hprev : CallWait ((setActor w dst { (w.st dst) with
              box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
              nextMid := (w.st dst).nextMid + 1 }).st caller).phase callee ck := by
            simpa [setActor, hcaller] using hc
          refine ⟨hcaller, ?_⟩
          by_cases hdst : caller = dst
          · subst hdst
            simp [setActor] at hprev
            exact hprev
          · simpa [setActor, hdst] using hprev
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by simpa [hsame] using hlive
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          simpa [hsame] using hroom
        subst hsame
        rw [enqueue_park_self w D sender msg true k hliveS hroomS] at hc
        by_cases hcaller : caller = sender
        · subst hcaller
          simp only [setActor, CallWait] at hc
          rcases hc with hc | hc
          · cases hc
            left
            exact ⟨rfl, rfl, rfl⟩
          · cases hc
        · right
          refine ⟨hcaller, ?_⟩
          simpa [setActor, hcaller] using hc
      · rw [enqueue_park_other w D sender dst msg true k hlive hsame hroom] at hc
        by_cases hcaller : caller = sender
        · subst hcaller
          simp only [setActor, CallWait] at hc
          rcases hc with hc | hc
          · cases hc
            left
            exact ⟨rfl, rfl, rfl⟩
          · cases hc
        · right
          have hprev : CallWait ((setActor w dst { (w.st dst) with
              parked := (w.st dst).parked ++
                [{ sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := true }],
              nextMid := (w.st dst).nextMid + 1 }).st caller).phase callee ck := by
            simpa [setActor, hcaller] using hc
          refine ⟨hcaller, ?_⟩
          by_cases hdst : caller = dst
          · subst hdst
            simp [setActor] at hprev
            exact hprev
          · simpa [setActor, hdst] using hprev
  · rw [enqueue_miss w D sender dst msg k hlive] at hc
    by_cases hcaller : caller = sender
    · subst hcaller
      simp only [setActor_self, finishCall] at hc
      exact absurd hc (proceed_not_callwait (issueCall (w.st caller)) k callee ck)
    · right
      exact ⟨hcaller, by simpa [setActor, hcaller] using hc⟩

theorem reply_keeps_call (w : World) (sender caller callee : InstId) (ck k : Cont)
    (hc : CallWait ((performReply w sender k).st caller).phase callee ck) :
    CallWait (w.st caller).phase callee ck := by
  unfold performReply at hc
  cases hto : k.replyTo with
  | none =>
    simp [hto] at hc
    exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
  | some c =>
    simp [hto] at hc
    cases hph : (w.st c).phase with
    | awaitReply dst ck0 =>
      simp [hph] at hc
      by_cases hd : dst = sender
      · by_cases ho : (w.st sender).oweId = some (w.st c).waitId
        · simp [hd, ho, finishCall] at hc
          have hprev := not_call_runner
            (setActor w c (finishCall (w.st c) ck0 .reply)) sender _ caller callee ck
            (by simpa [finishCall] using proceed_not_callwait _ _ callee ck) hc
          by_cases hcc : caller = c
          · subst hcc
            simp [setActor, finishCall] at hprev
            exact absurd hprev (by simpa [finishCall] using proceed_not_callwait _ _ callee ck)
          · simpa [setActor, hcc] using hprev
        · simp [hd, ho] at hc
          exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
      · simp [hd] at hc
        exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | idle =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | run _ =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | parked _ _ _ =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | awaitEffect _ =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | awaitPeer _ =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc
    | crashed =>
      simp [hph] at hc
      exact not_call_runner w sender _ caller callee ck (proceed_not_callwait _ _ _ _) hc

theorem release_keeps_call (w : World) (id caller callee : InstId) (k : Cont) (ps : List Parked)
    (hc : CallWait ((releaseParked w id ps).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hc
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons] at hc
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [ite_eq_left hskip] at hc
      exact ih w hc
    · rw [ite_eq_right hskip] at hc
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id)) hc
      by_cases hcaller : caller = p.sender
      · rw [hcaller] at hmid
        simp [setActor] at hmid
        cases hph : (w.st p.sender).phase with
        | parked _ _ ck =>
          simp [resumeSender, hph] at hmid
          exact absurd hmid (proceed_not_callwait (w.st p.sender) ck callee k)
        | awaitReply _ _ =>
          simp [resumeSender, hph] at hmid
          rw [hcaller, hph]
          exact hmid
        | idle => simp [resumeSender, hph, CallWait] at hmid
        | run _ => simp [resumeSender, hph, CallWait] at hmid
        | awaitEffect _ => simp [resumeSender, hph, CallWait] at hmid
        | awaitPeer _ => simp [resumeSender, hph, CallWait] at hmid
        | crashed => simp [resumeSender, hph, CallWait] at hmid
      · simpa [setActor, hcaller] using hmid

theorem releaseWorld_call (D : Description) (w : World) (id : InstId) (a : Actor)
    (caller callee : InstId) (k : Cont)
    (hc : CallWait ((releaseWorld D w id a).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  let base := refundParked (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hworld : releaseWorld D w id a = releaseParked (setActor base id dead) id a.parked := by
    simp [releaseWorld, base, dead]
  rw [hworld] at hc
  have hrel := release_keeps_call (setActor base id dead) id caller callee k a.parked hc
  by_cases hcaller : caller = id
  · rw [hcaller] at hrel
    simp [setActor, dead, CallWait] at hrel
  · rw [setActor_other base id caller dead hcaller] at hrel
    have hpark := (refundParked_phase_life
      (refundMsgs (readCells D w id) (tname id) a.box) (tname id) a.parked caller).1
    have hmsg := (refundMsgs_phase_life (readCells D w id) (tname id) a.box caller).1
    have hcell := congrArg (·.phase) (cellsSt D w id caller)
    simp only [base] at hrel
    rw [hpark, hmsg, hcell] at hrel
    exact hrel

theorem admitDead_call (w : World) (dead caller callee : InstId) (k : Cont)
    (h : CallWait ((admitDead w dead).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  simpa [(admitDead_phase w dead caller).1] using h

theorem abortActor_call (D : Description) (w : World) (id : InstId) (a : Actor)
    (caller callee : InstId) (k : Cont)
    (h : CallWait ((abortActor D w id a).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  rw [abortActor] at h
  exact releaseWorld_call D w id a caller callee k
    (failFold_call (releaseWorld D w id a) id caller callee k (releaseWorld D w id a).roster
      (by simpa [failWaiters] using admitDead_call _ id caller callee k h))

theorem abortDesc_call (fuel : Nat) (D : Description) (w : World) (parent caller callee : InstId)
    (k : Cont) (h : CallWait ((abortDesc fuel D w parent).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  induction fuel generalizing w parent with
  | zero => simpa [abortDesc] using h
  | succ fuel ih =>
    simp only [abortDesc] at h
    suffices ∀ (ids : List InstId) (w0 : World),
        CallWait ((ids.foldl (fun w child =>
          if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
            let w := abortDesc fuel D w child
            abortActor D w child (w.st child)
          else w) w0).st caller).phase callee k →
        CallWait (w0.st caller).phase callee k by
      exact this w.roster w h
    intro ids
    induction ids with
    | nil =>
      intro w0 h0
      simpa using h0
    | cons c ids ihf =>
      intro w0 h0
      simp only [List.foldl_cons] at h0
      by_cases hgo : (isChild D parent c && (w0.st c).life == .alive && childTerminable D c) = true
      · rw [ite_eq_left hgo] at h0
        exact ih w0 c (abortActor_call D (abortDesc fuel D w0 c) c
          ((abortDesc fuel D w0 c).st c) caller callee k (ihf _ h0))
      · rw [ite_eq_right hgo] at h0
        exact ihf w0 h0

theorem tombstone_call (D : Description) (w : World) (child caller callee : InstId) (k : Cont)
    (h : CallWait ((enqueueTombstone D w child).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  simpa [tombstone_phase D w child caller] using h

/-- A tombstone is a plain priority message. Phases, bulk mail, lives, and call
stamps stay, so the call-tag invariant carries across the enqueue. -/
theorem tombstone_tag (D : Description) (w : World) (child : InstId) (hT : CallTagInv w) :
    CallTagInv (enqueueTombstone D w child) := by
  let w' := enqueueTombstone D w child
  have hph (i : InstId) : (w'.st i).phase = (w.st i).phase :=
    tombstone_phase D w child i
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box :=
    (enqueueTombstone_lists D w child i).1
  have hpark (i : InstId) : (w'.st i).parked = (w.st i).parked :=
    (enqueueTombstone_lists D w child i).2
  have hlifeEq (i : InstId) : (w'.st i).life = (w.st i).life := by
    cases hsup : supervisorOf D child with
    | none => simp [w', enqueueTombstone, hsup]
    | some parent =>
      simp only [w', enqueueTombstone, hsup]
      by_cases hlive : (w.st parent).life = .alive
      · by_cases hi : i = parent <;> simp [w', enqueueTombstone, hsup, hlive, setActor, hi]
      · simp [w', enqueueTombstone, hsup, hlive]
  have hstamp (i : InstId) :
      (w'.st i).oweId = (w.st i).oweId ∧ (w'.st i).waitId = (w.st i).waitId := by
    cases hsup : supervisorOf D child with
    | none => simp [w', enqueueTombstone, hsup]
    | some parent =>
      by_cases hlive : (w.st parent).life = .alive
      · by_cases hi : i = parent <;> simp [w', enqueueTombstone, hsup, hlive, setActor, hi]
      · simp [w', enqueueTombstone, hsup, hlive]
  apply call_tag_stable w w' hT
  · intro d c
    simp [mailCall, hbox d, hpark d]
  · intro i c
    exact owes_iff_carried _ _ (by simp [carriedCont, hph i]) c
  · intro i c
    exact pending_iff_carried _ _ (by simp [carriedCont, hph i]) c
  · intro c d k hph'
    simpa [hph c] using hph'
  · intro c d k hph'
    simpa [hph c] using hph'
  · intro c d k hph'
    simpa [hph c] using hph'
  · intro c d k hph'
    simpa [hph c] using hph'
  · intro i m hm
    cases hsup : supervisorOf D child with
    | none =>
      simp [w', enqueueTombstone, hsup] at hm
      exact hT.prioPlain i m hm
    | some parent =>
      by_cases hlive : (w.st parent).life = .alive
      · by_cases hi : i = parent
        · simp [w', enqueueTombstone, hsup, hlive, hi, setActor] at hm
          rcases hm with hold | hnew
          · exact hT.prioPlain parent m hold
          · rw [hnew]
            simp [tombstoneMsg]
        · simp [w', enqueueTombstone, hsup, hlive, hi, setActor] at hm
          exact hT.prioPlain i m hm
      · simp [w', enqueueTombstone, hsup, hlive] at hm
        exact hT.prioPlain i m hm
  · intro d c
    simpa [soleCall, hbox d, hpark d] using hT.sole d c
  · intro d p hp s
    have hp0 : p ∈ (w.st d).parked := by simpa [hpark d] using hp
    constructor
    · intro hc
      obtain ⟨hs, k, hk⟩ := (hT.parkFrom d p hp0 s).mp hc
      exact ⟨hs, k, by simpa [hph s] using hk⟩
    · intro ⟨hs, k, hk⟩
      exact (hT.parkFrom d p hp0 s).mpr ⟨hs, k, by simpa [hph s] using hk⟩
  · intro c d k hph'
    have hph0 : (w.st c).phase = .parked d true k := by simpa [hph c] using hph'
    rcases hT.parkedOnly c d k hph0 with ⟨hl, ⟨p, hp, hs, hc⟩, hbox0⟩ | ⟨hl, hno, hbox0⟩
    · exact Or.inl ⟨by simpa [hlifeEq d] using hl,
        ⟨p, by simpa [hpark d] using hp, hs, hc⟩,
        fun ⟨m, hm, hc⟩ => hbox0 ⟨m, by simpa [hbox d] using hm, hc⟩⟩
    · exact Or.inr ⟨by simpa [hlifeEq d] using hl,
        fun ⟨p, hp, hc⟩ => hno ⟨p, by simpa [hpark d] using hp, hc⟩,
        fun ⟨m, hm, hc⟩ => hbox0 ⟨m, by simpa [hbox d] using hm, hc⟩⟩
  · exact lifeKeep_of_eq hlifeEq
  · intro d c ho
    have hpre : handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase := by
      simpa [hph d] using ho
    simpa [(hstamp d).1, (hstamp c).2] using hT.owedId d c hpre

/-- A call wait that survives a committing `terminate` was already there. The
step aborts descendants and the actor itself, and a tombstone does not move a phase. -/
theorem terminateStage_call (D : Description) (w : World) (id caller callee : InstId) (k : Cont)
    (h : CallWait ((terminateStage D w id (w.st id)).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  simp only [terminateStage] at h
  exact abortDesc_call w.roster.length D w id caller callee k
    (abortActor_call D (abortDesc w.roster.length D w id) id
      ((abortDesc w.roster.length D w id).st id) caller callee k
      (tombstone_call D
        (abortActor D (abortDesc w.roster.length D w id) id
          ((abortDesc w.roster.length D w id).st id))
        id caller callee k h))

/-- A call wait after one head was already there, or this head is the `call` that
opened it and the route selected the callee. -/
theorem exec_call_origin (I : Impl) (w : World) (id : InstId) (krun : Cont)
    (hph : (w.st id).phase = .run krun) (caller callee : InstId) (k : Cont)
    (hc : CallWait ((execRun I w id (w.st id) krun).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k ∨
      (caller = id ∧ ∃ dst label hint tail, krun.rest = .call dst label hint :: tail ∧
        resolveId I.desc id dst = some callee) := by
  cases hrest : krun.rest with
  | nil =>
    simp [execRun, hrest] at hc
    exact Or.inl (not_call_runner w id _ caller callee k (idle_not_call callee k) hc)
  | cons e tail =>
    cases e with
    | send dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
      | some dstId =>
        simp [hr] at hc
        exact Or.inl (enqueue_plain_call w I.desc id dstId { label := label, sender := id, callFrom := none }
          (afterHead krun) caller callee k hc)
    | trySend dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
      | some dstId =>
        simp [hr] at hc
        split at hc
        · exact Or.inl (enqueue_plain_call w I.desc id dstId
            { label := label, sender := id, callFrom := none, reliable := false }
            (afterHead krun) caller callee k hc)
        · exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
    | call dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : resolveId I.desc id dst with
      | none =>
        have hc' : CallWait ((setActor w id (proceed (w.st id) (afterHead krun))).st caller).phase
            callee k := by simpa [hr, setActor, noteStale_st] using hc
        exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc')
      | some dstId =>
        simp [hr] at hc
        rcases enqueue_true_sender w I.desc id dstId { label := label, sender := id, callFrom := some id }
            (afterHead krun) caller callee k hc with ⟨hcaller, hcal, _⟩ | ⟨_, hprev⟩
        · exact Or.inr ⟨hcaller, ⟨dst, label, hint, tail, rfl, by rw [hcal]; exact hr⟩⟩
        · exact Or.inl hprev
    | reply =>
      simp [execRun, hrest] at hc
      exact Or.inl (reply_keeps_call w id caller callee k krun hc)
    | selfSchedule label =>
      simp [execRun, hrest] at hc
      split at hc
      · exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
      · split at hc
        · exact Or.inl (not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
        · exact Or.inl (not_call_runner w id _ caller callee k (crash_not_call callee k) hc)
    | cell dst label value =>
      simp only [execRun, hrest] at hc
      cases hdirty : (w.cell dst label).dirty with
      | false =>
        rw [ite_eq_right (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at hc
        rw [wakeReaders, wakes_phase (readersOf _ dst) I.desc _ dst label id caller] at hc
        exact Or.inl (not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
      | true =>
        simp [hdirty] at hc
        exact Or.inl (not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc)
    | internal =>
      simp [execRun, hrest] at hc
      exact Or.inl (not_call_runner w id _ caller callee k (await_not_call (afterHead krun) callee k) hc)
    | peer =>
      simp [execRun, hrest] at hc
      exact Or.inl (not_call_runner w id _ caller callee k (peer_not_call (afterHead krun) callee k) hc)
    | terminate =>
      simp only [execRun, hrest] at hc
      cases htpl : templateOf I.desc (tname id) with
      | none =>
        simp [htpl] at hc
        exact Or.inl (hc)
      | some ts =>
        simp only [htpl] at hc
        by_cases hkill : (ts.terminable && (ts.subtree != "" || !hasParkedCall (w.st id).parked)) = true
        · rw [ite_eq_left hkill] at hc
          by_cases hsub : ts.subtree = ""
          · by_cases hchild : hasChild I.desc w id = true
            · simp [hsub, hchild] at hc
              exact Or.inl (terminateStage_call I.desc w id caller callee k hc)
            · have hcf : hasChild I.desc w id = false := by
                cases h : hasChild I.desc w id
                · rfl
                · exact absurd h hchild
              simp [hsub, hcf] at hc
              exact Or.inl (releaseWorld_call I.desc w id (w.st id) caller callee k hc)
          · simp [hsub] at hc
            exact Or.inl (terminateStage_call I.desc w id caller callee k hc)
        · rw [ite_eq_right hkill] at hc
          exact Or.inl (hc)



/-- Failing one waiter of `dead` keeps call tags when nobody is in a call wait on
`dead`. A blocking send is resumed; a call wait on `dead` cannot be there. -/
theorem failWaiter_plain_tag (w : World) (dead i : InstId) (hT : CallTagInv w)
    (hno : ∀ c k, ¬ CallWait (w.st c).phase dead k) : CallTagInv (failWaiter w dead i) := by
  unfold failWaiter
  split
  · exact hT
  · cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        by_cases hd : (d == dead) = true
        · have hd' : d = dead := by simpa [beq_iff_eq] using hd
          have hph' : (w.st i).phase = .parked dead false k := by simp [hph, hd']
          have htag := resume_send_tag w i dead k hT hph'
          simp only [hph, hd, ite_true]
          rw [show resumeSender (w.st i) false dead = proceed (w.st i) k by
            simp [resumeSender, hph']] at htag
          exact htag
        · have hbit : (d == dead) = false := by
            cases hb : d == dead with
            | true => exact absurd hb hd
            | false => rfl
          simp only [hph, hbit, ite_false]
          exact hT
      | true =>
        simp [hph]
        exact hT
    | awaitReply _ _ =>
      simp [hph]
      exact hT
    | idle =>
      simp [hph]
      exact hT
    | run _ =>
      simp [hph]
      exact hT
    | awaitEffect _ =>
      simp [hph]
      exact hT
    | awaitPeer _ =>
      simp [hph]
      exact hT
    | crashed =>
      simp [hph]
      exact hT

theorem fail_plain_tag (w : World) (dead : InstId) (ids : List InstId) (hT : CallTagInv w)
    (hno : ∀ c k, ¬ CallWait (w.st c).phase dead k) :
    CallTagInv (ids.foldl (fun w i => failWaiter w dead i) w) := by
  induction ids generalizing w with
  | nil => simpa using hT
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep := failWaiter_plain_tag w dead i hT hno
    have hno' : ∀ c k, ¬ CallWait ((failWaiter w dead i).st c).phase dead k := by
      intro c k hc
      exact hno c k (failWaiter_call w dead i c dead k hc)
    exact ih _ hstep hno'

theorem execRun_keeps_call (I : Impl) (hG : GraphOk I.desc) (w : World) (id : InstId) (krun : Cont)
    (hS : SemInv I w) (hB : BulkFree I w) (hph : (w.st id).phase = .run krun)
    (caller callee : InstId) (k : Cont) (t : Template) (ht : templateOf I.desc (tname callee) = some t)
    (hterm : t.terminable = true)
    (hdiff : sameSubtree I.desc (tname caller) (tname callee) = false)
    (hc : CallWait ((execRun I w id (w.st id) krun).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  cases hrest : krun.rest with
  | nil =>
    simp [execRun, hrest] at hc
    exact not_call_runner w id _ caller callee k (idle_not_call callee k) hc
  | cons e tail =>
    cases e with
    | send dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | some dstId =>
        simp [hr] at hc
        exact enqueue_plain_call w I.desc id dstId { label := label, sender := id, callFrom := none }
          (afterHead krun) caller callee k hc
    | trySend dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | some dstId =>
        simp [hr] at hc
        split at hc
        · exact enqueue_plain_call w I.desc id dstId
            { label := label, sender := id, callFrom := none, reliable := false }
            (afterHead krun) caller callee k hc
        · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
    | call dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : resolveId I.desc id dst with
      | none =>
        have hc' : CallWait ((setActor w id (proceed (w.st id) (afterHead krun))).st caller).phase
            callee k := by simpa [hr, setActor, noteStale_st] using hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc'
      | some dstId =>
        simp [hr] at hc
        rcases enqueue_true_sender w I.desc id dstId { label := label, sender := id, callFrom := some id }
            (afterHead krun) caller callee k hc with ⟨hcaller, hcal, _⟩ | ⟨_, hprev⟩
        · have hrun : (w.st id).phase =
              .run ⟨.call dst label hint :: tail, krun.toState, krun.replyTo⟩ := by
            cases krun with
            | mk rest toState replyTo =>
              have hrest' : rest = .call dst label hint :: tail := hrest
              rw [hrest'] at hph
              exact hph
          have hsame := running_call_same_subtree I hG w hS id krun.toState krun.replyTo dst label
            hint tail hrun t (by simpa [hcal, resolve_tname I.desc id dst dstId hr] using ht) hterm
          have hjoin : sameSubtree I.desc (tname caller) (tname callee) = true := by
            simpa [hcaller, hcal, resolve_tname I.desc id dst dstId hr] using hsame
          simp [hjoin] at hdiff
        · exact hprev
    | reply =>
      simp [execRun, hrest] at hc
      exact reply_keeps_call w id caller callee k krun hc
    | selfSchedule label =>
      simp [execRun, hrest] at hc
      split at hc
      · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      · split at hc
        · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
        · exact not_call_runner w id _ caller callee k (crash_not_call callee k) hc
    | cell dst label value =>
      simp only [execRun, hrest] at hc
      cases hdirty : (w.cell dst label).dirty with
      | false =>
        rw [ite_eq_right (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at hc
        rw [wakeReaders, wakes_phase (readersOf _ dst) I.desc _ dst label id caller] at hc
        exact not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | true =>
        simp [hdirty] at hc
        exact not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc
    | internal =>
      simp [execRun, hrest] at hc
      exact not_call_runner w id _ caller callee k (await_not_call (afterHead krun) callee k) hc
    | peer =>
      simp [execRun, hrest] at hc
      exact not_call_runner w id _ caller callee k (peer_not_call (afterHead krun) callee k) hc
    | terminate =>
      simp only [execRun, hrest] at hc
      cases htpl : templateOf I.desc (tname id) with
      | none =>
        simp [htpl] at hc
        exact hc
      | some ts =>
        simp only [htpl] at hc
        by_cases hkill : (ts.terminable && (ts.subtree != "" || !hasParkedCall (w.st id).parked)) = true
        · rw [ite_eq_left hkill] at hc
          by_cases hsub : ts.subtree = ""
          · by_cases hchild : hasChild I.desc w id = true
            · simp [hsub, hchild] at hc
              exact terminateStage_call I.desc w id caller callee k hc
            · have hcf : hasChild I.desc w id = false := by
                cases h : hasChild I.desc w id
                · rfl
                · exact absurd h hchild
              simp [hsub, hcf] at hc
              exact releaseWorld_call I.desc w id (w.st id) caller callee k hc
          · simp [hsub] at hc
            exact terminateStage_call I.desc w id caller callee k hc
        · rw [ite_eq_right hkill] at hc
          exact hc

/-- Executing one head does not put a terminable actor into a call wait. The only
head that creates one is `call`, and a terminable continuation cannot start with it. -/
theorem execRun_keeps_terminable_caller (I : Impl) (w : World) (hB : BulkFree I w) (id : InstId)
    (krun : Cont) (hph : (w.st id).phase = .run krun) (caller callee : InstId) (k : Cont)
    (t : Template) (ht : templateOf I.desc (tname caller) = some t) (hterm : t.terminable = true)
    (hsub0 : t.subtree = "")
    (hc : CallWait ((execRun I w id (w.st id) krun).st caller).phase callee k) :
    CallWait (w.st caller).phase callee k := by
  cases hrest : krun.rest with
  | nil =>
    simp [execRun, hrest] at hc
    exact not_call_runner w id _ caller callee k (idle_not_call callee k) hc
  | cons e tail =>
    cases e with
    | send dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | some dstId =>
        simp [hr] at hc
        exact enqueue_plain_call w I.desc id dstId { label := label, sender := id, callFrom := none }
          (afterHead krun) caller callee k hc
    | trySend dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : route w I.desc id dst with
      | none =>
        simp [hr] at hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | some dstId =>
        simp [hr] at hc
        split at hc
        · exact enqueue_plain_call w I.desc id dstId
            { label := label, sender := id, callFrom := none, reliable := false }
            (afterHead krun) caller callee k hc
        · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
    | call dst label hint =>
      simp [execRun, hrest] at hc
      cases hr : resolveId I.desc id dst with
      | none =>
        have hc' : CallWait ((setActor w id (proceed (w.st id) (afterHead krun))).st caller).phase
            callee k := by simpa [hr, setActor, noteStale_st] using hc
        exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc'
      | some dstId =>
        simp [hr] at hc
        rcases enqueue_true_sender w I.desc id dstId
            { label := label, sender := id, callFrom := some id } (afterHead krun) caller callee k hc
            with ⟨hcaller, _, _⟩ | ⟨_, hprev⟩
        · have hrun : (w.st id).phase =
              .run ⟨.call dst label hint :: tail, krun.toState, krun.replyTo⟩ := by
            cases krun with
            | mk rest toState replyTo =>
              have hrest' : rest = .call dst label hint :: tail := hrest
              rw [hrest'] at hph
              exact hph
          have htId : templateOf I.desc (tname id) = some t := by simpa [hcaller] using ht
          exact False.elim (terminable_no_call_head I w hB id t htId hterm
            (by simpa [hcaller] using hsub0) dst label hint tail krun.toState krun.replyTo hrun)
        · exact hprev
    | reply =>
      simp [execRun, hrest] at hc
      exact reply_keeps_call w id caller callee k krun hc
    | selfSchedule label =>
      simp [execRun, hrest] at hc
      split at hc
      · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      · split at hc
        · exact not_call_runner w id _ caller callee k (proceed_not_callwait _ _ _ _) hc
        · exact not_call_runner w id _ caller callee k (crash_not_call callee k) hc
    | cell dst label value =>
      simp only [execRun, hrest] at hc
      cases hdirty : (w.cell dst label).dirty with
      | false =>
        rw [ite_eq_right (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at hc
        rw [wakeReaders, wakes_phase (readersOf _ dst) I.desc _ dst label id caller] at hc
        exact not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc
      | true =>
        simp [hdirty] at hc
        exact not_call_runner _ id _ caller callee k (proceed_not_callwait _ _ _ _) hc
    | internal =>
      simp [execRun, hrest] at hc
      exact not_call_runner w id _ caller callee k (await_not_call (afterHead krun) callee k) hc
    | peer =>
      simp [execRun, hrest] at hc
      exact not_call_runner w id _ caller callee k (peer_not_call (afterHead krun) callee k) hc
    | terminate =>
      simp only [execRun, hrest] at hc
      cases htpl : templateOf I.desc (tname id) with
      | none =>
        simp [htpl] at hc
        exact hc
      | some ts =>
        simp only [htpl] at hc
        by_cases hkill : (ts.terminable && (ts.subtree != "" || !hasParkedCall (w.st id).parked)) = true
        · rw [ite_eq_left hkill] at hc
          by_cases htree : ts.subtree = ""
          · by_cases hchild : hasChild I.desc w id = true
            · simp [htree, hchild] at hc
              exact terminateStage_call I.desc w id caller callee k hc
            · have hcf : hasChild I.desc w id = false := by
                cases h : hasChild I.desc w id
                · rfl
                · exact absurd h hchild
              simp [htree, hcf] at hc
              exact releaseWorld_call I.desc w id (w.st id) caller callee k hc
          · simp [htree] at hc
            exact terminateStage_call I.desc w id caller callee k hc
        · rw [ite_eq_right (by simpa using hkill)] at hc
          exact hc

theorem exec_keeps_call (I : Impl) (hG : GraphOk I.desc) (w w' : World) (id : InstId)
    (hS : SemInv I w) (hB : BulkFree I w) (caller callee : InstId) (k : Cont) (t : Template)
    (ht : templateOf I.desc (tname callee) = some t) (hterm : t.terminable = true)
    (hdiff : sameSubtree I.desc (tname caller) (tname callee) = false)
    (hc : CallWait (w'.st caller).phase callee k) (h : apply I (.exec id) w = some w') :
    CallWait (w.st caller).phase callee k := by
  simp only [apply] at h
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run krun =>
      simp [hph] at h
      cases h
      exact execRun_keeps_call I hG w id krun hS hB hph caller callee k t ht hterm hdiff hc
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem exec_keeps_terminable_caller (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (caller callee : InstId) (k : Cont) (t : Template)
    (ht : templateOf I.desc (tname caller) = some t) (hterm : t.terminable = true)
    (hsub0 : t.subtree = "")
    (hc : CallWait (w'.st caller).phase callee k) (h : apply I (.exec id) w = some w') :
    CallWait (w.st caller).phase callee k := by
  simp only [apply] at h
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run krun =>
      simp [hph] at h
      cases h
      exact execRun_keeps_terminable_caller I w hB id krun hph caller callee k t ht hterm hsub0 hc
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

/-- A reachable call wait names a terminable callee only inside the caller's subtree.
The wait edge is a `call`, and the checker rejects one that leaves the subtree. -/
theorem no_terminable_call_target (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (caller callee : InstId) (k : Cont)
    (hph : CallWait (w.st caller).phase callee k) (t : Template)
    (ht : templateOf I.desc (tname callee) = some t) :
    t.terminable = false ∨ sameSubtree I.desc (tname caller) (tname callee) = true := by
  have hI := inv_reachable I N w hL hR
  rcases hph with hpark | hawait
  · obtain ⟨_, e, he, hsrc, _, hdst, _, heff, _⟩ :=
      described_park I w hI caller callee true k hpark
    simpa [hsrc, hdst] using
      call_edge_unterminable I.desc hG e he heff t (by simpa [hdst] using ht)
  · obtain ⟨_, e, he, hsrc, _, hdst, _, heff, _⟩ :=
      described_reply I w hI caller callee k hawait
    simpa [hsrc, hdst] using
      call_edge_unterminable I.desc hG e he heff t (by simpa [hdst] using ht)

theorem clearPhase_wait (c callee : InstId) (k : Cont) (ph : Phase)
    (hc : CallWait (clearReplyPhase c ph) callee k) : ∃ k', CallWait ph callee k' := by
  cases ph with
  | parked d b k0 =>
    rcases hc with h | h
    · unfold clearReplyPhase at h
      injection h with hd hb _
      subst hb
      exact ⟨k0, Or.inl (by rw [hd])⟩
    · unfold clearReplyPhase at h
      cases h
  | awaitReply d k0 =>
    rcases hc with h | h
    · unfold clearReplyPhase at h
      cases h
    · unfold clearReplyPhase at h
      injection h with hd _
      exact ⟨k0, Or.inr (by rw [hd])⟩
  | run _ => simp [clearReplyPhase, CallWait] at hc
  | idle => simp [clearReplyPhase, CallWait] at hc
  | awaitEffect _ => simp [clearReplyPhase, CallWait] at hc
  | awaitPeer _ => simp [clearReplyPhase, CallWait] at hc
  | crashed => simp [clearReplyPhase, CallWait] at hc

theorem detach_wait (a : Actor) (c callee : InstId) (cid : Nat) (k : Cont)
    (hc : CallWait (detachReply a c cid).phase callee k) : ∃ k', CallWait a.phase callee k' := by
  unfold detachReply at hc
  split at hc
  · exact clearPhase_wait c callee k a.phase hc
  · exact ⟨k, hc⟩

theorem credit_fold_phase (ps : List Parked) (w : World) (name : String) (sender i : InstId) :
    ((ps.foldl (fun w _ => creditSender w name sender) w).st i).phase = (w.st i).phase := by
  induction ps generalizing w with
  | nil => rfl
  | cons _ tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact (credit_phase_life w name sender i).1

theorem refund_phase (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).phase = (w.st i).phase :=
  (refundCall_fields w caller dst i).1

/-- A call wait after a timeout was already a call wait. Timing out leaves the
wait, and scrubbing a reply keeps the phase constructor. -/
theorem callTimeout_prev (w w' : World) (id caller callee : InstId) (k : Cont)
    (h : callTimeout w id = some w') (hc : CallWait (w'.st caller).phase callee k) :
    ∃ k', CallWait (w.st caller).phase callee k' := by
  unfold callTimeout at h
  dsimp only at h
  split at h
  · cases h
  · cases hph : (w.st id).phase with
    | awaitReply dst ck =>
      simp [hph] at h
      cases h
      by_cases hcaller : caller = id
      · rw [hcaller] at hc
        simp [setActor, finishCall] at hc
        exact absurd hc (proceed_not_callwait _ ck callee k)
      · by_cases hd : caller = dst
        · rw [hd] at hc
          have hne : ¬ dst = id := fun h => hcaller (by rw [hd]; exact h)
          have hc0 : CallWait (detachReply (detachBox (w.st dst) id) id (w.st id).waitId).phase
              callee k := by simpa [setActor, hne] using hc
          have hprev := detach_wait (detachBox (w.st dst) id) id callee (w.st id).waitId k hc0
          rw [hd]
          simpa [detachBox] using hprev
        · exact ⟨k, by simpa [setActor, hcaller, hd] using hc⟩
    | parked dst b ck =>
      cases b with
      | false => simp [hph] at h
      | true =>
        simp [hph] at h
        cases h
        by_cases hcaller : caller = id
        · rw [hcaller] at hc
          have hc0 : CallWait (finishCall ((refundParkedCall w id dst).st id) ck .notAdmitted).phase
              callee k := by simp [setActor] at hc; exact hc
          simp [finishCall] at hc0
          exact absurd hc0 (proceed_not_callwait _ ck callee k)
        · have hc0 : CallWait ((refundParkedCall w id dst).st caller).phase callee k := by
            simpa [setActor, hcaller] using hc
          exact ⟨k, by rwa [refund_phase] at hc0⟩
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

/-- A reachable lone terminable is not blocked on a call. A subtree member may be:
its call stays inside the subtree and dies with it. -/
theorem terminable_not_caller (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (caller callee : InstId) (k : Cont)
    (hph : CallWait (w.st caller).phase callee k) (t : Template)
    (ht : templateOf I.desc (tname caller) = some t) (hsub0 : t.subtree = "") :
    t.terminable = false := by
  induction hR generalizing caller callee k with
  | init => simp [init_phase, CallWait] at hph
  | step w w' a prev happ ih =>
    have hInv := inv2_reachable I hL hG N w prev
    have hM : MailInv w := hInv.1.2.1
    have hB : BulkFree I w := hInv.2.2.2
    cases a with
    | stutter =>
      cases stutter_unchanged I w w' happ
      exact ih caller callee k hph ht
    | ingress dst label =>
      have hkeep := (ingress_phase I w w' dst label caller (by simpa [apply] using happ)).1
      exact ih caller callee k (by simpa [hkeep] using hph) ht
    | spawn template =>
      exact ih caller callee k (spawn_keeps_call I w w' template caller callee k happ hph) ht
    | finish id =>
      exact ih caller callee k (finish_keeps_call I w w' id caller callee k happ hph) ht
    | recvPrio id =>
      exact ih caller callee k (recvPrio_keeps_call I w w' id caller callee k happ hph) ht
    | recvBulk id =>
      exact ih caller callee k (recvBulk_keeps_call I w w' id hM caller callee k happ hph) ht
    | callTimeout s =>
      simp only [apply] at happ
      obtain ⟨k', hprev⟩ := callTimeout_prev w w' s caller callee k happ hph
      exact ih caller callee k' hprev ht
    | exec id =>
      cases hterm : t.terminable with
      | false => rfl
      | true =>
        have hprev :=
          exec_keeps_terminable_caller I w w' id hB caller callee k t ht hterm hsub0 hph happ
        have hnot := ih caller callee k hprev ht
        rwa [hterm] at hnot

/-- Call-relevant phase facts. A plain parked send may resume without touching them:
the continuation is the same, and an empty continuation owes no reply. -/
def TagView (ph ph' : Phase) : Prop :=
  (∀ d k, ph = .awaitReply d k ↔ ph' = .awaitReply d k) ∧
  (∀ d k, ph = .parked d true k ↔ ph' = .parked d true k) ∧
  (∀ c, handlerOwes c ph ↔ handlerOwes c ph') ∧
  (∀ c, replyPending c ph ↔ replyPending c ph')

theorem tagView_refl (ph : Phase) : TagView ph ph := by
  exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem tagView_trans (a b c : Phase) (hab : TagView a b) (hbc : TagView b c) : TagView a c :=
  ⟨fun d k => (hab.1 d k).trans (hbc.1 d k),
   fun d k => (hab.2.1 d k).trans (hbc.2.1 d k),
   fun x => (hab.2.2.1 x).trans (hbc.2.2.1 x),
   fun x => (hab.2.2.2 x).trans (hbc.2.2.2 x)⟩

theorem replyShape_nil (c : InstId) (k : Cont) (h : k.rest = []) : ¬ replyShape c k := by
  intro ⟨_, hcount, _⟩
  simp [replyCount, h] at hcount

theorem nextIsReply_nil (k : Cont) (h : k.rest = []) : ¬ nextIsReply k := by
  simp [nextIsReply, h]

theorem owes_of_cont (ph ph' : Phase) (c : InstId) (h : carriedCont ph = carriedCont ph') :
    handlerOwes c ph ↔ handlerOwes c ph' := by
  simp [handlerOwes, h]

theorem pending_of_cont (ph ph' : Phase) (c : InstId) (h : carriedCont ph = carriedCont ph') :
    replyPending c ph ↔ replyPending c ph' := by
  simp [replyPending, h]

/-- Resuming a plain parked send keeps every call-relevant phase fact. -/
theorem tagView_plain_resume (d : InstId) (k : Cont) :
    TagView (.parked d false k) (resumed k) := by
  cases hk : k.rest with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro dst ck
      constructor
      · intro h
        cases h
      · intro h
        simp [resumed, hk] at h
    · intro dst ck
      constructor
      · intro h
        cases h
      · intro h
        simp [resumed, hk] at h
    · intro c
      constructor
      · intro ⟨ck, hcar, hshape, _⟩
        simp [carriedCont] at hcar
        cases hcar
        exact absurd hshape (replyShape_nil c k hk)
      · intro ⟨ck, hcar, hshape, _⟩
        simp [resumed, hk, carriedCont] at hcar
    · intro c
      constructor
      · intro ⟨ck, hcar, _, hnext⟩
        simp [carriedCont] at hcar
        cases hcar
        exact absurd hnext (nextIsReply_nil k hk)
      · intro ⟨ck, hcar, _, hnext⟩
        simp [resumed, hk, carriedCont] at hcar
  | cons _ _ =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro dst ck
      constructor
      · intro h
        cases h
      · intro h
        simp [resumed, hk] at h
    · intro dst ck
      constructor
      · intro h
        cases h
      · intro h
        simp [resumed, hk] at h
    · intro c
      exact owes_of_cont _ _ c (by simp [carriedCont, resumed, hk])
    · intro c
      exact pending_of_cont _ _ c (by simp [carriedCont, resumed, hk])

/-- Failing `dead`'s waiters does not disturb call facts of an actor that is not
in a call on `dead`. A plain parked send may resume. -/
theorem failWaiter_tag (w : World) (dead i s : InstId)
    (hno : ∀ k, ¬ CallWait (w.st s).phase dead k) :
    TagView (w.st s).phase ((failWaiter w dead i).st s).phase ∧
      ((failWaiter w dead i).st s).box = (w.st s).box ∧
      ((failWaiter w dead i).st s).parked = (w.st s).parked ∧
      ((failWaiter w dead i).st s).prio = (w.st s).prio := by
  by_cases hs : s = i
  · rw [hs] at hno ⊢
    unfold failWaiter
    split
    · exact And.intro (tagView_refl _) (And.intro rfl (And.intro rfl rfl))
    · cases hph : (w.st i).phase with
      | parked d b k =>
        by_cases hd : (d == dead) = true
        · cases b with
          | true =>
            simp [hph]
            exact tagView_refl _
          | false =>
            simp only [hph, hd, setActor]
            cases hk : k.rest with
            | nil =>
              refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
              · simpa [proceed, hk, resumed] using tagView_plain_resume d k
              · simp [proceed, hk]
              · simp [proceed, hk]
              · simp [proceed, hk]
            | cons _ _ =>
              refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
              · simpa [proceed, hk, resumed] using tagView_plain_resume d k
              · simp [proceed, hk]
              · simp [proceed, hk]
              · simp [proceed, hk]
        · cases b with
          | true =>
            simp [hph]
            exact tagView_refl _
          | false =>
            have hneD : d ≠ dead := by
              intro heq
              exact hd (by simpa [beq_iff_eq] using heq)
            simp [hph, hneD]
            exact tagView_refl _
      | awaitReply _ _ =>
        simp [hph]
        exact tagView_refl _
      | idle =>
        simp [hph]
        exact tagView_refl _
      | run _ =>
        simp [hph]
        exact tagView_refl _
      | awaitEffect _ =>
        simp [hph]
        exact tagView_refl _
      | awaitPeer _ =>
        simp [hph]
        exact tagView_refl _
      | crashed =>
        simp [hph]
        exact tagView_refl _
  · have heq : (failWaiter w dead i).st s = w.st s := by
      unfold failWaiter
      split
      · rfl
      · cases hph : (w.st i).phase with
        | parked d b k =>
          have hne : i ≠ s := fun h => hs h.symm
          cases b with
          | true => simp [hph, setActor, hne]
          | false =>
            by_cases hd : (d == dead) = true
            · simp only [hph, hd]
              exact setActor_other w i s (proceed (w.st i) k) hne.symm
            · have hf : (d == dead) = false := by simpa [Bool.not_eq_true] using hd
              simp [hph, hf]
        | awaitReply d k =>
          have hne : i ≠ s := fun h => hs h.symm
          simp [hph, setActor, hne]
        | idle => simp [hph]
        | run _ => simp [hph]
        | awaitEffect _ => simp [hph]
        | awaitPeer _ => simp [hph]
        | crashed => simp [hph]
    simp [heq]
    exact tagView_refl _

/-- An actor outside every subtree is not a member of one. -/
theorem not_subtree_not_member (D : Description) (hG : GraphOk D) (id : InstId)
    (sub : String) (key : Nat) (hnot : ¬ subtreeMemberName D (tname id)) :
    isMember D id sub key = false := by
  by_cases hm : isMember D id sub key = true
  · have hname : subtreeMemberName D (tname id) := by
      have hB := member_terminable D hG.subtrees id sub key hm
      cases id with
      | core _ => simp [isMember] at hm
      | peer role ix =>
        simp only [isMember, Bool.and_eq_true] at hm
        obtain ⟨⟨_, hsubb⟩, htreeb⟩ := hm
        have htree : templateSubtree D role = sub := by simpa [beq_iff_eq] using htreeb
        have hsubne : sub ≠ "" := by
          have hfalse : (sub == "") = false := by simpa [bne] using hsubb
          simpa [beq_iff_eq] using hfalse
        cases ht : templateOf D role with
        | none =>
          simp [templateSubtree, ht] at htree
          exact absurd htree hsubne
        | some t =>
          have hterm : t.terminable = true := by simpa [terminableB, tname, ht] using hB
          have hts : sub = t.subtree := by simpa [templateSubtree, ht] using htree.symm
          exact ⟨t, by simpa [tname] using ht, hterm, hts ▸ hsubne⟩
    exact absurd hname hnot
  · simpa [Bool.not_eq_true] using hm

/-- A same-subtree route hits a per-peer role at the sender's key, so membership agrees. -/
theorem fresh_resolve_member (D : Description) (hG : GraphOk D)
    (sender callee : InstId) (dst : String) (hr : resolveId D sender dst = some callee)
    (hsame : sameSubtree D (tname sender) dst = true) (sub : String) (key : Nat) :
    isMember D callee sub key = isMember D sender sub key := by
  have hboth : templateSubtree D (tname sender) ≠ "" ∧
      templateSubtree D (tname sender) = templateSubtree D dst := by
    simp [sameSubtree, Bool.and_eq_true] at hsame
    constructor
    · intro hempty
      simp [hempty] at hsame
    · simpa [beq_iff_eq] using hsame.2
  cases ht : templateOf D dst with
  | none => simp [resolveId, ht] at hr
  | some t =>
    have htree : t.subtree ≠ "" := by
      rw [← template_subtree_of D dst t ht, ← hboth.2]
      exact hboth.1
    cases hmul : t.multiplicity with
    | one => exact False.elim (one_not_subtree D hG dst t ht htree hmul)
    | perPeer =>
      cases hk : memberKey sender with
      | none => simp [resolveId, ht, hmul, hk] at hr
      | some k =>
        simp only [resolveId, ht, hmul, hk] at hr
        cases hr
        cases sender with
        | core _ => simp [memberKey] at hk
        | peer role ix =>
          simp [memberKey] at hk
          subst hk
          have hrole : templateSubtree D role = t.subtree := by
            simpa [tname, templateSubtree, ht] using hboth.2
          simp [templateSubtree] at hrole
          simp [isMember, templateSubtree, ht, hrole]

theorem fresh_call_member (D : Description) (hG : GraphOk D) (w : World)
    (sender callee : InstId) (dst : String) (hr : route w D sender dst = some callee)
    (hsame : sameSubtree D (tname sender) dst = true) (sub : String) (key : Nat) :
    isMember D callee sub key = isMember D sender sub key := by
  have hboth : templateSubtree D (tname sender) ≠ "" ∧
      templateSubtree D (tname sender) = templateSubtree D dst := by
    simp [sameSubtree, Bool.and_eq_true] at hsame
    constructor
    · intro hempty
      simp [hempty] at hsame
    · simpa [beq_iff_eq] using hsame.2
  cases ht : templateOf D dst with
  | none => simp [route, ht] at hr
  | some t =>
    have htree : t.subtree ≠ "" := by
      rw [← template_subtree_of D dst t ht, ← hboth.2]
      exact hboth.1
    cases hmul : t.multiplicity with
    | one => exact False.elim (one_not_subtree D hG dst t ht htree hmul)
    | perPeer =>
      cases hk : memberKey sender with
      | none => simp [route, ht, hmul, hk] at hr
      | some k =>
        simp only [route, ht, hmul, hk] at hr
        split at hr
        · cases hr
          cases sender with
          | core _ => simp [memberKey] at hk
          | peer role ix =>
            simp [memberKey] at hk
            subst hk
            have hrole : templateSubtree D role = t.subtree := by
              simpa [tname, templateSubtree, ht] using hboth.2
            have hmatch : templateSubtree D role = t.subtree := hrole
            simp [templateSubtree] at hmatch
            simp [isMember, templateSubtree, ht, hmatch]
        · simp at hr

/-- Ingress does not open a call wait. -/
theorem ingress_keeps_call (I : Impl) (w w' : World) (dst caller callee : InstId)
    (label : String) (k : Cont) (h : apply I (.ingress dst label) w = some w')
    (hc : CallWait (w'.st caller).phase callee k) : CallWait (w.st caller).phase callee k := by
  have hph := (ingress_phase I w w' dst label caller (by simpa [apply] using h)).1
  simpa [hph] using hc

/-- The two ends of a reachable call are members of the same subtree key, or of none. -/
theorem call_member_iff (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (caller callee : InstId) (k : Cont)
    (hc : CallWait (w.st caller).phase callee k) (sub : String) (key : Nat) :
    isMember I.desc callee sub key = isMember I.desc caller sub key := by
  induction hR generalizing caller callee k with
  | init => simp [init_phase, CallWait] at hc
  | step w w' a prev happ ih =>
    have hInv := inv2_reachable I hL hG N w prev
    cases a with
    | stutter =>
      cases stutter_unchanged I w w' happ
      exact ih caller callee k hc
    | ingress dst label =>
      exact ih caller callee k (ingress_keeps_call I w w' dst caller callee label k happ hc)
    | finish who =>
      exact ih caller callee k (finish_keeps_call I w w' who caller callee k happ hc)
    | spawn template =>
      exact ih caller callee k (spawn_keeps_call I w w' template caller callee k happ hc)
    | recvPrio who =>
      exact ih caller callee k (recvPrio_keeps_call I w w' who caller callee k happ hc)
    | recvBulk who =>
      exact ih caller callee k
        (recvBulk_keeps_call I w w' who hInv.1.2.1 caller callee k happ hc)
    | callTimeout s =>
      simp only [apply] at happ
      obtain ⟨k', hprev⟩ := callTimeout_prev w w' s caller callee k happ hc
      exact ih caller callee k' hprev
    | exec who =>
      simp only [apply] at happ
      unfold execHead at happ
      by_cases hlive : (w.st who).life = .alive
      · simp [hlive] at happ
        cases hph : (w.st who).phase with
        | run krun =>
          simp [hph] at happ
          cases happ
          rcases exec_call_origin I w who krun hph caller callee k hc with
            hold | ⟨hcaller, dst, label, hint, tail, hrest, hr⟩
          · exact ih caller callee k hold
          · by_cases hname : subtreeMemberName I.desc (tname who)
            · have hbulk : bulkScopeOf I.desc (tname who) (.call dst label hint :: tail) = true := by
                simpa [contRest, hph, hrest] using hInv.2.2.2 who
              have hok := member_effect_of_scope I.desc hG (tname who)
                (.call dst label hint) tail hname hbulk
              have hscope : (sameSubtree I.desc (tname who) dst && perPeerB I.desc dst) = true := by
                simpa [memberEffectOk] using hok
              simp [Bool.and_eq_true] at hscope
              simpa [hcaller] using
                fresh_resolve_member I.desc hG who callee dst hr hscope.1 sub key
            · have hleft := not_subtree_not_member I.desc hG who sub key hname
              have hright : isMember I.desc callee sub key = false := by
                have hdst : tname callee = dst := resolve_tname I.desc who dst callee hr
                cases ht : templateOf I.desc dst with
                | none => simp [resolveId, ht] at hr
                | some t =>
                  by_cases hterm : t.terminable = true
                  · have hrun : (w.st who).phase =
                        .run ⟨.call dst label hint :: tail, krun.toState, krun.replyTo⟩ := by
                      cases krun with
                      | mk rest toState replyTo =>
                        cases hrest
                        exact hph
                    have hsame := running_call_same_subtree I hG w hInv.1.1 who
                      krun.toState krun.replyTo dst label hint tail hrun t ht hterm
                    have hsubS : templateSubtree I.desc (tname who) ≠ "" := by
                      simp [sameSubtree, Bool.and_eq_true] at hsame
                      intro hempty
                      simp [hempty] at hsame
                    cases htid : templateOf I.desc (tname who) with
                    | none => simp [templateSubtree, htid] at hsubS
                    | some ts =>
                      have hne : ts.subtree ≠ "" := by simpa [templateSubtree, htid] using hsubS
                      exact absurd
                        ⟨ts, htid, subtree_member_terminable I.desc hG (tname who) ts htid hne, hne⟩
                        hname
                  · by_cases hmem : isMember I.desc callee sub key = true
                    · have hB := member_terminable I.desc hG.subtrees callee sub key hmem
                      simp [terminableB, hdst, ht, hterm] at hB
                    · simpa [Bool.not_eq_true] using hmem
              rw [← hcaller] at hleft
              rw [hleft, hright]
        | idle => simp [hph] at happ
        | parked _ _ _ => simp [hph] at happ
        | awaitReply _ _ => simp [hph] at happ
        | awaitEffect _ => simp [hph] at happ
        | awaitPeer _ => simp [hph] at happ
        | crashed => simp [hph] at happ
      · simp [hlive] at happ

/-- Dropping messages that are not calls leaves the call count alone. -/
theorem countCall_filter_plain (dead : InstId) (ms : List Msg) (c : InstId)
    (h : ∀ m ∈ ms, m.sender = dead → m.callFrom = none) :
    countCall (ms.filter fun m => m.sender != dead) c = countCall ms c := by
  induction ms with
  | nil => simp [countCall]
  | cons m ms ih =>
    have htail : ∀ x ∈ ms, x.sender = dead → x.callFrom = none :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hs : m.sender = dead
    · have hnone : m.callFrom = none := h m List.mem_cons_self hs
      have hb : (m.sender == dead) = true := by simpa [beq_iff_eq] using hs
      simp [countCall, List.filter, hb, bne, hnone]
      exact ih htail
    · have hb : (m.sender == dead) = false := by simpa [beq_iff_eq] using hs
      have hkeep : (m.sender != dead) = true := by simp [bne, hb]
      simp [countCall, List.filter, hkeep]
      rw [ih htail]

theorem countParkedCall_filter_plain (dead : InstId) (ps : List Parked) (c : InstId)
    (h : ∀ p ∈ ps, p.sender = dead → p.msg.callFrom = none) :
    countParkedCall (ps.filter fun p => p.sender != dead) c = countParkedCall ps c := by
  induction ps with
  | nil => simp [countParkedCall]
  | cons p ps ih =>
    have htail : ∀ x ∈ ps, x.sender = dead → x.msg.callFrom = none :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hs : p.sender = dead
    · have hnone : p.msg.callFrom = none := h p List.mem_cons_self hs
      have hb : (p.sender == dead) = true := by simpa [beq_iff_eq] using hs
      simp [countParkedCall, List.filter, hb, bne, hnone]
      exact ih htail
    · have hb : (p.sender == dead) = false := by simpa [beq_iff_eq] using hs
      have hkeep : (p.sender != dead) = true := by simp [bne, hb]
      simp [countParkedCall, List.filter, hkeep]
      rw [ih htail]

/-- Forgetting a sender's plain mail does not change call tags. A call message is
not one of theirs: its `callFrom` would name them, and they are not in a call. -/
theorem forget_plain_tag (w : World) (dead : InstId) (hT : CallTagInv w)
    (hbox : ∀ i m, m ∈ (w.st i).box → m.sender = dead → m.callFrom = none)
    (hpark : ∀ i p, p ∈ (w.st i).parked → p.sender = dead → p.msg.callFrom = none) :
    CallTagInv (forgetSender w dead) := by
  let w' := forgetSender w dead
  have hph (i : InstId) : (w'.st i).phase = (w.st i).phase := (forget_stable w dead i).1
  have hprio (i : InstId) : (w'.st i).prio = (w.st i).prio := (forget_stable w dead i).2.2.2
  have hboxC (s c : InstId) : countCall (w'.st s).box c = countCall (w.st s).box c := by
    rcases forget_box_fate w dead s with heq | hfilt
    · simpa [w', heq]
    · simpa [w', hfilt] using countCall_filter_plain dead (w.st s).box c (hbox s)
  have hparkC (s c : InstId) : countParkedCall (w'.st s).parked c = countParkedCall (w.st s).parked c := by
    rcases forget_parked_fate w dead s with heq | hfilt
    · simpa [w', heq]
    · simpa [w', hfilt] using countParkedCall_filter_plain dead (w.st s).parked c (hpark s)
  apply call_tag_stable w w' hT
  · intro d c
    constructor
    · intro hmc
      rcases hmc with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · rcases forget_box_fate w dead d with heq | hfilt
        · exact Or.inl ⟨m, by simpa [w', heq] using hm, hc⟩
        · have hm0 : m ∈ (w.st d).box := (List.mem_filter.mp (hfilt ▸ hm)).1
          exact Or.inl ⟨m, hm0, hc⟩
      · rcases forget_parked_fate w dead d with heq | hfilt
        · exact Or.inr ⟨p, by simpa [w', heq] using hp, hc⟩
        · have hp0 : p ∈ (w.st d).parked := (List.mem_filter.mp (hfilt ▸ hp)).1
          exact Or.inr ⟨p, hp0, hc⟩
    · intro hmc
      rcases hmc with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
      · rcases forget_box_fate w dead d with heq | hfilt
        · exact Or.inl ⟨m, by simpa [w', heq] using hm, hc⟩
        · have hkeep : m.sender ≠ dead := by
            intro hs
            have hnone := hbox d m hm hs
            simp [hnone] at hc
          have hin : m ∈ (w.st d).box.filter fun x => x.sender != dead := by
            refine List.mem_filter.mpr ⟨hm, ?_⟩
            simpa [bne, beq_iff_eq] using hkeep
          exact Or.inl ⟨m, by simpa [w', hfilt] using hin, hc⟩
      · rcases forget_parked_fate w dead d with heq | hfilt
        · exact Or.inr ⟨p, by simpa [w', heq] using hp, hc⟩
        · have hkeep : p.sender ≠ dead := by
            intro hs
            have hnone := hpark d p hp hs
            simp [hnone] at hc
          have hin : p ∈ (w.st d).parked.filter fun x => x.sender != dead := by
            refine List.mem_filter.mpr ⟨hp, ?_⟩
            simpa [bne, beq_iff_eq] using hkeep
          exact Or.inr ⟨p, by simpa [w', hfilt] using hin, hc⟩
  · intro i c
    simp [handlerOwes, hph i]
  · intro i c
    simp [replyPending, hph i]
  · intro c d k h
    simpa [hph c] using h
  · intro c d k h
    simpa [hph c] using h
  · intro c d k h
    simpa [hph c] using h
  · intro c d k h
    simpa [hph c] using h
  · intro i m hm
    exact hT.prioPlain i m (by simpa [w', hprio i] using hm)
  · intro d c
    have hsum : countCall (w'.st d).box c + countParkedCall (w'.st d).parked c =
        countCall (w.st d).box c + countParkedCall (w.st d).parked c := by
      rw [hboxC d c, hparkC d c]
    simpa [soleCall, w', hsum] using hT.sole d c
  · intro d p hp s
    constructor
    · intro hc
      rcases forget_parked_fate w dead d with heq | hfilt
      · have hp0 : p ∈ (w.st d).parked := by simpa [w', heq] using hp
        rcases (hT.parkFrom d p hp0 s).mp hc with ⟨hs, k, hk⟩
        exact ⟨hs, k, by simpa [hph s] using hk⟩
      · have hp0 : p ∈ (w.st d).parked := (List.mem_filter.mp (hfilt ▸ hp)).1
        rcases (hT.parkFrom d p hp0 s).mp hc with ⟨hs, k, hk⟩
        exact ⟨hs, k, by simpa [hph s] using hk⟩
    · intro ⟨hs, k, hk⟩
      rcases forget_parked_fate w dead d with heq | hfilt
      · have hp0 : p ∈ (w.st d).parked := by simpa [w', heq] using hp
        exact (hT.parkFrom d p hp0 s).mpr ⟨hs, k, by simpa [hph s] using hk⟩
      · have hp0 : p ∈ (w.st d).parked := (List.mem_filter.mp (hfilt ▸ hp)).1
        exact (hT.parkFrom d p hp0 s).mpr ⟨hs, k, by simpa [hph s] using hk⟩
  · intro c d k h
    have hold : (w.st c).phase = .parked d true k := by simpa [hph c] using h
    exact parkedOnly_lift w w' hT c d k hold (forget_stable w dead d).2.1
      (fun p hp hs hc => by
        rcases forget_parked_fate w dead d with heq | hfilt
        · simpa [w', heq] using hp
        · have hkeep : p.sender ≠ dead := by
            intro hsd
            have hnone := hpark d p hp hsd
            simp [hnone] at hc
          have hin : p ∈ (w.st d).parked.filter fun x => x.sender != dead := by
            refine List.mem_filter.mpr ⟨hp, ?_⟩
            simpa [bne, beq_iff_eq] using hkeep
          simpa [w', hfilt] using hin)
      (fun p hp _ => by
        rcases forget_parked_fate w dead d with heq | hfilt
        · simpa [w', heq] using hp
        · exact (List.mem_filter.mp (hfilt ▸ hp)).1)
      (fun m hm _ => by
        rcases forget_box_fate w dead d with heq | hfilt
        · simpa [w', heq] using hm
        · exact (List.mem_filter.mp (hfilt ▸ hm)).1)
  · exact lifeKeep_of_eq (fun i => (forget_stable w dead i).2.1)
  · intro d c ho
    exact owed_phase w w' hT (fun i => (forget_stable w dead i).1)
      (fun i => by
        have hs := forget_stamps w dead i
        simpa [w'] using (And.intro hs.2.2.1 hs.1)) d c ho

end Deadlock
