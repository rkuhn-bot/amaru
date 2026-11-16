import Deadlock.Inv2

set_option autoImplicit false

namespace Deadlock

/-- A call edge does not land on a terminable template. The only transition that
sets `life` to dead is a killing `terminate`, so a callee of a call cannot die
while a caller is in `awaitReply`. -/
theorem call_edge_unterminable (D : Description) (hG : GraphOk D) (e : Edge)
    (he : e ∈ D.edges) (hc : e.effect = .call) (t : Template)
    (ht : templateOf D e.dst = some t) : t.terminable = false := by
  have hall := by simpa [callTermFails] using hG.lifecycle
  have hnot : (e.effect != .call) = false := by
    rw [hc]
    decide
  have hbody := hall e he hnot
  simp [ht] at hbody
  cases hterm : t.terminable
  · rfl
  · simp [hterm] at hbody

/-- A fresh enqueue adds at most the parked entry it was given. -/
theorem enqueue_parked_mem (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (mb : InstId) (p : Parked)
    (hp : p ∈ ((enqueueOrPark w D sender dst msg isCall k).st mb).parked) :
    p ∈ (w.st mb).parked ∨
      (mb = dst ∧ p.sender = sender ∧ p.msg = msg ∧ p.isCall = isCall ∧ (w.st dst).life = .alive) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hparkS : (w.st sender).parked = [] := by rw [hsame]; exact hroom.1
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by rw [hsame]; exact hroom.2
        cases isCall
        · rw [← hsame] at hp
          rw [enqueue_room_self_send w D sender msg k hliveS hparkS hcapS] at hp
          by_cases hmb : mb = sender
          · simp [setActor, hmb, proceed_parked, charge_parked] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · simp [setActor, hmb] at hp
            exact Or.inl hp
        · rw [← hsame] at hp
          rw [enqueue_room_self_call w D sender msg k hliveS hparkS hcapS] at hp
          by_cases hmb : mb = sender
          · simp [setActor, hmb, charge_parked] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · simp [setActor, hmb] at hp
            exact Or.inl hp
      · have hflip : ¬ dst = sender := fun h => hsame h.symm
        cases isCall
        · rw [enqueue_room_other_send w D sender dst msg k hlive hsame hroom.1 hroom.2] at hp
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp only [setActor] at hp
            rw [if_neg hne] at hp
            rw [if_pos hmb] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, proceed_parked, charge_parked] at hp
              exact Or.inl (by rw [← hsender] at hp; exact hp)
            · simp [setActor, hmb, hsender, hflip] at hp
              exact Or.inl hp
        · rw [enqueue_room_other_call w D sender dst msg k hlive hsame hroom.1 hroom.2] at hp
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp only [setActor] at hp
            rw [if_neg hne] at hp
            rw [if_pos hmb] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, charge_parked] at hp
              exact Or.inl (by rw [← hsender] at hp; exact hp)
            · simp [setActor, hmb, hsender, hflip] at hp
              exact Or.inl hp
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          rw [hsame]; exact hroom
        rw [← hsame] at hp
        rw [enqueue_park_self w D sender msg isCall k hliveS hroomS] at hp
        by_cases hmb : mb = sender
        · simp [setActor, hmb, charge_parked] at hp
          cases hp with
          | inl h => exact Or.inl (by rw [← hmb] at h; exact h)
          | inr h =>
            cases h
            exact Or.inr ⟨hmb.trans hsame, rfl, rfl, rfl, hlive⟩
        · simp [setActor, hmb] at hp
          exact Or.inl hp
      · have hflip : ¬ dst = sender := fun h => hsame h.symm
        rw [enqueue_park_other w D sender dst msg isCall k hlive hsame hroom] at hp
        by_cases hmb : mb = dst
        · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
          simp [setActor, hmb, hne, hflip] at hp
          cases hp with
          | inl h => exact Or.inl (by rw [← hmb] at h; exact h)
          | inr h =>
            cases h
            exact Or.inr ⟨hmb, rfl, rfl, rfl, hlive⟩
        · by_cases hsender : mb = sender
          · simp [setActor, hmb, hsender, hflip, charge_parked] at hp
            exact Or.inl (by rw [← hsender] at hp; exact hp)
          · simp [setActor, hmb, hsender, hflip] at hp
            exact Or.inl hp
  · rw [enqueue_dead w D sender dst msg isCall k hlive] at hp
    by_cases hmb : mb = sender
    · simp [setActor, hmb, proceed_parked] at hp
      exact Or.inl (by rw [← hmb] at hp; exact hp)
    · simp [setActor, hmb] at hp
      exact Or.inl hp

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

/-- While `c` is in `awaitReply d`, exactly one of: the call is still in `d`'s
mailbox, `d` is in the handler and the reply is still ahead, or that reply is
the next effect. A parked entry carries `callFrom = some s` exactly when `s`
is that entry's sender and `s` is in `.parked d true`. Such a caller’s message
is in the parked list, not the box. No priority message carries a `callFrom`. -/
structure CallTagInv (w : World) : Prop where
  awaiting : ∀ c d k, (w.st c).phase = .awaitReply d k →
    (mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase) ∨
    (¬mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ replyPending c (w.st d).phase)
  parkedCall : ∀ c d k, (w.st c).phase = .parked d true k →
    mailCall w d c ∧ ¬handlerOwes c (w.st d).phase ∧ ¬replyPending c (w.st d).phase
  msgOwner : ∀ d c, mailCall w d c →
    (∃ k, (w.st c).phase = .awaitReply d k) ∨ (∃ k, (w.st c).phase = .parked d true k)
  oweOwner : ∀ d c, handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase →
    ∃ k, (w.st c).phase = .awaitReply d k
  prioPlain : ∀ id m, m ∈ (w.st id).prio → m.callFrom = none
  sole : ∀ d c, soleCall w d c
  parkFrom : ∀ d p, p ∈ (w.st d).parked → ∀ s,
    p.msg.callFrom = some s ↔ p.sender = s ∧ ∃ k, (w.st s).phase = .parked d true k
  parkedOnly : ∀ c d k, (w.st c).phase = .parked d true k →
    (∃ p, p ∈ (w.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
    ¬ ∃ m, m ∈ (w.st d).box ∧ m.callFrom = some c

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

/-- Same phases and mailboxes are the same call tags. -/
theorem call_tag_copy (w w' : World) (hT : CallTagInv w)
    (h : ∀ i, (w'.st i).phase = (w.st i).phase ∧ (w'.st i).box = (w.st i).box ∧
      (w'.st i).parked = (w.st i).parked ∧ (w'.st i).prio = (w.st i).prio) :
    CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rcases hpre with h1 | h2 | h3
    · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
    · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
    · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)
  · intro c d k hph
    have hpre := hT.parkedCall c d k (by simpa [(h c).1] using hph)
    have hmail : mailCall w d c → mailCall w' d c := by
      intro hm
      rcases hm with ⟨m, hmem, hc⟩ | ⟨p, hmem, hc⟩
      · exact Or.inl ⟨m, by simpa [← (h d).2.1] using hmem, hc⟩
      · exact Or.inr ⟨p, by simpa [← (h d).2.2.1] using hmem, hc⟩
    exact ⟨hmail hpre.1, by simpa [(h d).1] using hpre.2.1, by simpa [(h d).1] using hpre.2.2⟩
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
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp, hs, hc⟩ := hpre.1
      exact ⟨p, by simpa [← (h d).2.2.1] using hp, hs, hc⟩
    · intro ⟨m, hm, hc⟩
      exact hpre.2 ⟨m, by simpa [(h d).2.1] using hm, hc⟩

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
      (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
      ¬ ∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) : CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio, hsole, hfrom, honly⟩
  · intro c d k hph
    have hpre := hT.awaiting c d k (hawait c d k hph)
    rcases hpre with h1 | h2 | h3
    · exact Or.inl ⟨(hmail d c).mpr h1.1, (not_iff (howe d c)).mpr h1.2.1,
        (not_iff (hpend d c)).mpr h1.2.2⟩
    · exact Or.inr (Or.inl ⟨(not_iff (hmail d c)).mpr h2.1, (howe d c).mpr h2.2.1,
        (not_iff (hpend d c)).mpr h2.2.2⟩)
    · exact Or.inr (Or.inr ⟨(not_iff (hmail d c)).mpr h3.1, (not_iff (howe d c)).mpr h3.2.1,
        (hpend d c).mpr h3.2.2⟩)
  · intro c d k hph
    have hpre := hT.parkedCall c d k (hpark c d k hph)
    exact ⟨(hmail d c).mpr hpre.1, (not_iff (howe d c)).mpr hpre.2.1,
      (not_iff (hpend d c)).mpr hpre.2.2⟩
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
      (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
      ¬ ∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c) : CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio, hsole, hfrom, honly⟩
  · intro c d k hph
    have hpre := hT.awaiting c d k (hawait c d k hph)
    have hxor := handlerOwes_not_pending c (w'.st d).phase
    rcases hpre with h1 | h2 | h3
    · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
        (not_iff (hduty d c)).mpr (fun h => h.elim (fun ho => h1.2.1 ho) (fun hp => h1.2.2 hp))
      exact Or.inl ⟨(hmail d c).mpr h1.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩
    · have hyes : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase :=
        (hduty d c).mpr (Or.inl h2.2.1)
      have hnom := (not_iff (hmail d c)).mpr h2.1
      rcases hyes with ho | hp
      · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
      · exact Or.inr (Or.inr ⟨hnom, fun ho => hxor ho hp, hp⟩)
    · have hyes : handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase :=
        (hduty d c).mpr (Or.inr h3.2.2)
      have hnom := (not_iff (hmail d c)).mpr h3.1
      rcases hyes with ho | hp
      · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
      · exact Or.inr (Or.inr ⟨hnom, fun ho => hxor ho hp, hp⟩)
  · intro c d k hph
    have hpre := hT.parkedCall c d k (hpark c d k hph)
    have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
      (not_iff (hduty d c)).mpr (fun h => h.elim (fun ho => hpre.2.1 ho) (fun hp => hpre.2.2 hp))
    exact ⟨(hmail d c).mpr hpre.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (c d : InstId) (k : Cont) (hk : (w'.st c).phase = .parked d true k) :
    (∃ p, p ∈ (w'.st d).parked ∧ p.sender = c ∧ p.msg.callFrom = some c) ∧
      ¬ ∃ m, m ∈ (w'.st d).box ∧ m.callFrom = some c := by
  have hpre := hT.parkedOnly c d k (hph c d k hk)
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hs, hc⟩ := hpre.1
    exact ⟨p, by rw [hpark d]; exact hp, hs, hc⟩
  · intro ⟨m, hm, hc⟩
    exact hpre.2 ⟨m, hbox d m hm, hc⟩

/-- A call sitting in the box belongs to a caller already in `awaitReply`. -/
theorem box_awaits (w : World) (hT : CallTagInv w) (d : InstId) (m : Msg) (c : InstId)
    (hm : m ∈ (w.st d).box) (hc : m.callFrom = some c) :
    ∃ k, (w.st c).phase = .awaitReply d k := by
  rcases hT.msgOwner d c (Or.inl ⟨m, hm, hc⟩) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, hk⟩
  · exact absurd ⟨m, hm, hc⟩ (hT.parkedOnly c d k hk).2

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

theorem finish_tag (w : World) (id : InstId) (w' : World) (hT : CallTagInv w)
    (h : finishWait w id = some w') : CallTagInv w' := by
  unfold finishWait at h
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [hph] at h
    cases h
    exact resume_tag w id k hT (by simp [carriedCont, hph])
      (fun d kA hbad => by simp [hph] at hbad)
      (fun d b kA hbad => by simp [hph] at hbad)
  | awaitPeer k =>
    simp [hph] at h
    cases h
    exact resume_tag w id k hT (by simp [carriedCont, hph])
      (fun d kA hbad => by simp [hph] at hbad)
      (fun d b kA hbad => by simp [hph] at hbad)
  | idle => simp [hph] at h
  | run _ => simp [hph] at h
  | parked _ _ _ => simp [hph] at h
  | awaitReply _ _ => simp [hph] at h
  | crashed => simp [hph] at h

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
          refine ⟨rfl, rfl, rfl, ?_⟩
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
    (hidle : (w.st id).phase = .idle) (hst : ∀ i, w1.st i = w.st i)
    (hpark0 : (w.st id).parked = []) (hbox1 : a1.box = ms) (hpark1 : a1.parked = [])
    (hprio1 : a1.prio = (w.st id).prio) (hhead : (w.st id).box = m :: ms)
    (hc : m.callFrom = some c) (hrun : a1.phase = .run k) (hshape : replyShape c k)
    (hother : ∀ c', c' ≠ c → ¬handlerOwes c' a1.phase ∧ ¬replyPending c' a1.phase) :
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
    · obtain ⟨_, hp, _, _⟩ := hM.bwd c id true kw hk
      simp [hpark0] at hp
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        rcases hpre with h1 | h2 | h3
        · exact h1.1
        · exact absurd (Or.inl h2.2.1) holdD
        · exact absurd (Or.inr h3.2.2) holdD
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
        · exact Or.inr (Or.inr ⟨hnom,
            fun ho' => by
              have hnot := handlerOwes_not_pending c a1.phase (by simpa [w', setActor] using ho')
              exact hnot (by simpa [w', setActor] using hp),
            by simpa [w', setActor] using hp⟩)
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
      rcases hpre with h1 | h2 | h3
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold := by simpa [w', setActor, hc0, hst] using hph
    have hpre := hT.parkedCall c0 d0 k0 hold
    have hd0 : d0 ≠ id := by
      intro heq
      obtain ⟨_, hp, _, _⟩ := hM.bwd c0 id true k0 (by simpa [heq] using hold)
      simp [hpark0] at hp
    have hmail : mailCall w' d0 c0 := by
      rcases hpre.1 with ⟨x, hx, hcf⟩ | ⟨p, hp, hcf⟩
      · exact Or.inl ⟨x, by simp [w', setActor, hd0, hst, hx], hcf⟩
      · exact Or.inr ⟨p, by simp [w', setActor, hd0, hst, hp], hcf⟩
    exact ⟨hmail,
      by simpa [w', setActor, hd0, hst] using hpre.2.1,
      by simpa [w', setActor, hd0, hst] using hpre.2.2⟩
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
      hplain.2.2.2 hhead hc
    exact credit_tag (setActor w1 id a1) (tname id) m.sender hI
  | some c =>
    have hcall := deliver_call I hL w id ({ (w.st id) with box := ms }) m w1 a1 c hdel hc
    obtain ⟨k, hrun, hshape, _, hother⟩ := hcall.2.2.2
    have hI := install_call w w1 id a1 m ms c k hM hT hidle hst hpark0
      (by simpa using hcall.1) (by simpa [hpark0] using hcall.2.1) (by simpa using hcall.2.2.1)
      hhead hc hrun hshape hother
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
    have hpre := hT.parkedOnly c d k hold
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq, hs, hcf⟩ := hpre.1
      by_cases hd : d = id
      · have hq' : q ∈ ps := by
          rw [hd, hpark] at hq
          cases hq with
          | head => simp [hc] at hcf
          | tail _ ht => exact ht
        exact ⟨q, by
          simp only [setActor, hd, hst, ite_true]
          rw [hpark1]
          exact hq', hs, hcf⟩
      · exact ⟨q, by simpa [setActor, hd, hst] using hq, hs, hcf⟩
    · intro ⟨msg, hm, hcf⟩
      by_cases hd : d = id
      · simp only [setActor, hd, hst, ite_true] at hm
        rw [hbox1, hbox0] at hm
        cases hm
      · exact hpre.2 ⟨msg, by simpa [setActor, hd, hst] using hm, hcf⟩

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
  obtain ⟨kH, hrun, hshape, _, hother⟩ := hD.2.2.2
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
  have hnomS : ¬mailCall post id p.sender := by
    intro hm
    rcases hm with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
    · rw [hIdB'] at hx
      simp [hbox1] at hx
    · rw [hIdK', hpark1] at hq
      exact absurd hcf (countParked_zero_mem ps p.sender hzero q hq)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · exact Or.inr (Or.inr ⟨hnomS,
          fun ho' => handlerOwes_not_pending p.sender a1.phase
            (by simpa [post, hIdP'] using ho') (by simpa [post] using hp),
          by simpa [post, ← hIdP'] using hp⟩)
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
            rcases hpre with h1 | h2 | h3
            · exact h1.1
            · exact absurd (Or.inl h2.2.1) holdD
            · exact absurd (Or.inr h3.2.2) holdD
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
            rcases hpre with h1 | h2 | h3
            · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
            · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1,
                (not_iff hpend).mpr h2.2.2⟩)
            · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
                hpend.mpr h3.2.2⟩)
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
            rcases hpre with h1 | h2 | h3
            · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
            · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1,
                (not_iff hpend).mpr h2.2.2⟩)
            · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1,
                hpend.mpr h3.2.2⟩)
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
        have hpre := hT.parkedCall c0 d0 k0 hold
        by_cases hd : d0 = id
        · have hmem : ∃ q, q ∈ ps ∧ q.msg.callFrom = some c0 := by
            rcases hpre.1 with ⟨x, hx, _⟩ | ⟨q, hq, hcf⟩
            · rw [hd] at hx
              simp [hbox0] at hx
            · rw [hd, hpark] at hq
              cases hq with
              | head =>
                simp [hfrom] at hcf
                exact False.elim (hcS hcf.symm)
              | tail _ ht => exact ⟨q, ht, hcf⟩
          obtain ⟨q, hq, hcf⟩ := hmem
          exact ⟨Or.inr ⟨q, by rw [hd, hIdK', hpark1]; exact hq, hcf⟩,
            by rw [hd, hIdP']; exact (hother c0 hcS).1,
            by rw [hd, hIdP']; exact (hother c0 hcS).2⟩
        · by_cases hdS : d0 = p.sender
          · rw [hdS] at hpre
            have hmail : mailCall post p.sender c0 := by
              rcases hpre.1 with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
              · exact Or.inl ⟨x, by rw [← hSB'] at hx; exact hx, hcf⟩
              · exact Or.inr ⟨q, by rw [← hSK'] at hq; exact hq, hcf⟩
            have hcar : carriedCont (post.st p.sender).phase =
                carriedCont (w.st p.sender).phase := by simp [carriedCont, hSP', hphS]
            rw [hdS]
            exact ⟨hmail,
              (not_iff (owes_iff_carried _ _ hcar c0)).mpr hpre.2.1,
              (not_iff (pending_iff_carried _ _ hcar c0)).mpr hpre.2.2⟩
          · have hmail : mailCall post d0 c0 := by
              rcases hpre.1 with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
              · exact Or.inl ⟨x, by rw [← (hO' d0 hd hdS).2.1] at hx; exact hx, hcf⟩
              · exact Or.inr ⟨q, by rw [← (hO' d0 hd hdS).2.2.1] at hq; exact hq, hcf⟩
            have hpeq := (hO' d0 hd hdS).1
            exact ⟨hmail,
              (not_iff (owes_iff_carried _ _ (by rw [hpeq]) c0)).mpr hpre.2.1,
              (not_iff (pending_iff_carried _ _ (by rw [hpeq]) c0)).mpr hpre.2.2⟩
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
    have hpre := hT.parkedOnly c d k hold
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq, hsend, hcf⟩ := hpre.1
      by_cases hd : d = id
      · rw [hd, hpark] at hq
        cases hq with
        | head => exact False.elim (hcS hsend.symm)
        | tail _ ht =>
          have heq : (post.st d).parked = ps := by rw [hd, hIdK', hpark1]
          exact ⟨q, heq ▸ ht, hsend, hcf⟩
      · by_cases hdS : d = p.sender
        · exact ⟨q, by simpa [post, hdS, hSK'] using hq, hsend, hcf⟩
        · exact ⟨q, by simpa [post, (hO' d hd hdS).2.2.1] using hq, hsend, hcf⟩
    · intro ⟨msg, hm, hcf⟩
      exact hpre.2 ⟨msg, by
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
            exact hm', hcf⟩

/-- Deliver a non-call box head and leave the parked list where it is. -/
theorem install_plain_kept (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hbox1 : a1.box = ms)
    (hpark1 : a1.parked = (w.st id).parked) (hprio1 : a1.prio = (w.st id).prio)
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

/-- Deliver a call at the box head and leave the parked list where it is.
The caller is already in `awaitReply`: a parked phase does not own a box message. -/
theorem install_call_kept (w w1 : World) (id : InstId) (a1 : Actor) (m : Msg) (ms : List Msg)
    (c : InstId) (k kw : Cont) (hT : CallTagInv w) (hidle : (w.st id).phase = .idle)
    (hst : ∀ i, w1.st i = w.st i) (hbox1 : a1.box = ms)
    (hpark1 : a1.parked = (w.st id).parked) (hprio1 : a1.prio = (w.st id).prio)
    (hhead : (w.st id).box = m :: ms) (hc : m.callFrom = some c)
    (hrun : a1.phase = .run k) (hshape : replyShape c k)
    (hother : ∀ c', c' ≠ c → ¬handlerOwes c' a1.phase ∧ ¬replyPending c' a1.phase)
    (hown : (w.st c).phase = .awaitReply id kw) : CallTagInv (setActor w1 id a1) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · exact Or.inr (Or.inr ⟨hnom,
            fun ho' => handlerOwes_not_pending c a1.phase (by simpa [w', setActor] using ho')
              (by simpa [w', setActor] using hp),
            by simpa [w', setActor] using hp⟩)
      · have hpre := hT.awaiting c0 id k0 (by simpa [hd] using hold)
        have holdD : ¬(handlerOwes c0 (w.st id).phase ∨ replyPending c0 (w.st id).phase) := by
          simp [handlerOwes, replyPending, carriedCont, hidle]
        have hmail0 : mailCall w id c0 := by
          rcases hpre with h1 | h2 | h3
          · exact h1.1
          · exact absurd (Or.inl h2.2.1) holdD
          · exact absurd (Or.inr h3.2.2) holdD
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
        simp [w', setActor, if_neg hd, hst]
      have howe := owes_iff_carried (w.st d0).phase (w'.st d0).phase (by rw [hphEq]) c0
      have hpend := pending_iff_carried (w.st d0).phase (w'.st d0).phase (by rw [hphEq]) c0
      rcases hpre with h1 | h2 | h3
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)
  · intro c0 d0 k0 hph
    have hc0 : c0 ≠ id := by
      intro heq
      simp [w', setActor, heq, hrun] at hph
    have hold : (w.st c0).phase = .parked d0 true k0 := by
      simpa [w', setActor, hc0, hst] using hph
    have hpre := hT.parkedCall c0 d0 k0 hold
    by_cases hd : d0 = id
    · have hnotC : c0 ≠ c := by
        intro heq
        simp [heq, hown, hd] at hold
      have hmem : (∃ x, x ∈ ms ∧ x.callFrom = some c0) ∨
          (∃ q, q ∈ (w.st id).parked ∧ q.msg.callFrom = some c0) := by
        rcases hpre.1 with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · rw [hd, hhead] at hx
          cases hx with
          | head =>
            simp [hc] at hcf
            exact False.elim (hnotC hcf.symm)
          | tail _ ht => exact Or.inl ⟨x, ht, hcf⟩
        · exact Or.inr ⟨q, by simpa [hd] using hq, hcf⟩
      rcases hmem with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
      · exact ⟨Or.inl ⟨x, by simp [w', setActor, hd, hbox1, hx], hcf⟩,
          by simpa [w', setActor, hd] using (hother c0 hnotC).1,
          by simpa [w', setActor, hd] using (hother c0 hnotC).2⟩
      · exact ⟨Or.inr ⟨q, by simp [w', setActor, hd, hpark1, hq], hcf⟩,
          by simpa [w', setActor, hd] using (hother c0 hnotC).1,
          by simpa [w', setActor, hd] using (hother c0 hnotC).2⟩
    · exact ⟨by
        rcases hpre.1 with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [w', setActor, hd, hst, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [w', setActor, hd, hst, hq], hcf⟩,
        by simpa [w', setActor, hd, hst] using hpre.2.1,
        by simpa [w', setActor, hd, hst] using hpre.2.2⟩
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
        · exact Or.inl ⟨x, by simpa [w', setActor, if_neg hd] using hx, hcf⟩
        · exact Or.inr ⟨q, by simpa [w', setActor, if_neg hd] using hq, hcf⟩
      · intro hm
        rcases hm with ⟨x, hx, hcf⟩ | ⟨q, hq, hcf⟩
        · exact Or.inl ⟨x, by simp [w', setActor, if_neg hd, hx], hcf⟩
        · exact Or.inr ⟨q, by simp [w', setActor, if_neg hd, hq], hcf⟩
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
    have hpre := hT.parkedOnly c d k (by rw [hphEq] at hk; exact hk)
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq, hs, hcf⟩ := hpre.1
      by_cases hd : d = id
      · rw [hd, hpark] at hq
        cases hq with
        | head => simp [hplain] at hcf
        | tail _ ht =>
          exact ⟨q, by
            simp only [w', setActor, hd, if_true]
            exact ht, hs, hcf⟩
      · exact ⟨q, by simpa [w', setActor, hd] using hq, hs, hcf⟩
    · intro ⟨msg, hm, hcf⟩
      by_cases hd : d = id
      · simp only [w', setActor, hd, if_true] at hm
        rw [List.mem_append] at hm
        rcases hm with hmem | hmem
        · exact hpre.2 ⟨msg, by rw [hd]; exact hmem, hcf⟩
        · simp at hmem
          rw [hmem, hplain] at hcf
          cases hcf
      · exact hpre.2 ⟨msg, by simpa [w', setActor, hd] using hm, hcf⟩

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
    (hpark1 : a1.parked = (w.st id).parked)
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
    obtain ⟨q, hq, hs, hc⟩ := hM.bwd i dst b k hold
    by_cases hd : dst = id
    · exact ⟨q, by
        rw [hd]
        simp only [setActor, hst, ite_true]
        rw [hd] at hq
        rw [hpark1]
        exact hq, hs, hc⟩
    · exact ⟨q, by simpa [setActor, hd, hst] using hq, hs, hc⟩
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
          replyPending c ((shiftWorld w id p ps kS).st d).phase) := by
  intro c d k hph'
  by_cases hc : c = p.sender
  · have hEq : Phase.awaitReply id kS = Phase.awaitReply d k := by
      rw [← shift_phF w id p ps kS hsnd, ← hc]; exact hph'
    injection hEq with hd0 hk0
    have hmail : mailCall (shiftWorld w id p ps kS) id p.sender :=
      Or.inl ⟨p.msg, by
        rw [shift_boxId w id p ps kS hsnd]
        exact List.mem_append_right _ (by simp), hfrom⟩
    have hpre := hT.parkedCall p.sender id kS hph
    have howe := shift_owes w id p ps kS hph hsnd id p.sender
    have hpend := shift_pending w id p ps kS hph hsnd id p.sender
    rw [← hd0, hc]
    exact Or.inl ⟨hmail, (not_iff howe).mpr hpre.2.1, (not_iff hpend).mpr hpre.2.2⟩
  · by_cases hcId : c = id
    · have hph0 : (w.st c).phase = .awaitReply d k := by
        have h := hph'
        rw [hcId, shift_phId w id p ps kS hsnd] at h
        rwa [← hcId] at h
      have hpre := hT.awaiting c d k hph0
      have hmail := shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc
      have howe := shift_owes w id p ps kS hph hsnd d c
      have hpend := shift_pending w id p ps kS hph hsnd d c
      rcases hpre with h1 | h2 | h3
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)
    · have hph0 : (w.st c).phase = .awaitReply d k := by
        rw [← (shift_other w id p ps kS c hcId hc).1]; exact hph'
      have hpre := hT.awaiting c d k hph0
      have hmail := shift_mail_ne w id p ps kS hpark hfrom hsnd d c hc
      have howe := shift_owes w id p ps kS hph hsnd d c
      have hpend := shift_pending w id p ps kS hph hsnd d c
      rcases hpre with h1 | h2 | h3
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)

theorem shift_parkedCall (w : World) (id : InstId) (p : Parked) (ps : List Parked) (kS : Cont)
    (hT : CallTagInv w) (hpark : (w.st id).parked = p :: ps)
    (hph : (w.st p.sender).phase = .parked id true kS) (hsnd : p.sender ≠ id) :
    ∀ c d k, ((shiftWorld w id p ps kS).st c).phase = .parked d true k →
      mailCall (shiftWorld w id p ps kS) d c ∧
        ¬handlerOwes c ((shiftWorld w id p ps kS).st d).phase ∧
        ¬replyPending c ((shiftWorld w id p ps kS).st d).phase := by
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
    have hpre := hT.parkedCall c d k hph0
    obtain ⟨q, hq, hsend, hcf⟩ := (hT.parkedOnly c d k hph0).1
    refine ⟨?_, (not_iff (shift_owes w id p ps kS hph hsnd d c)).mpr hpre.2.1,
      (not_iff (shift_pending w id p ps kS hph hsnd d c)).mpr hpre.2.2⟩
    by_cases hd : d = id
    · rw [hd, hpark] at hq
      cases hq with
      | head => exact False.elim (hc hsend.symm)
      | tail _ ht =>
        exact Or.inr ⟨q, by
          rw [hd, shift_parkId w id p ps kS hsnd]
          exact ht, hcf⟩
    · by_cases hdS : d = p.sender
      · exact Or.inr ⟨q, by
          rw [hdS] at hq
          rw [hdS, shift_parkS w id p ps kS hsnd]
          exact hq, hcf⟩
      · exact Or.inr ⟨q, by
          rw [(shift_other w id p ps kS d hd hdS).2.2.1]
          exact hq, hcf⟩

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
      (∃ q, q ∈ ((shiftWorld w id p ps kS).st d).parked ∧ q.sender = c ∧
          q.msg.callFrom = some c) ∧
        ¬ ∃ m, m ∈ ((shiftWorld w id p ps kS).st d).box ∧ m.callFrom = some c := by
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
    have hpre := hT.parkedOnly c d k hph0
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq, hsend, hcf⟩ := hpre.1
      by_cases hd : d = id
      · rw [hd, hpark] at hq
        cases hq with
        | head => exact False.elim (hc hsend.symm)
        | tail _ ht =>
          exact ⟨q, by
            rw [hd, shift_parkId w id p ps kS hsnd]
            exact ht, hsend, hcf⟩
      · by_cases hdS : d = p.sender
        · exact ⟨q, by
            rw [hdS] at hq
            rw [hdS, shift_parkS w id p ps kS hsnd]
            exact hq, hsend, hcf⟩
        · exact ⟨q, by
            rw [(shift_other w id p ps kS d hd hdS).2.2.1]
            exact hq, hsend, hcf⟩
    · intro ⟨m, hm, hcf⟩
      by_cases hd : d = id
      · rw [hd, shift_boxId w id p ps kS hsnd] at hm
        rw [List.mem_append] at hm
        rcases hm with hin | heq
        · exact hpre.2 ⟨m, by
            rw [← hd] at hin
            exact hin, hcf⟩
        · simp at heq
          rw [heq, hfrom] at hcf
          injection hcf with heqc
          exact False.elim (hc heqc.symm)
      · by_cases hdS : d = p.sender
        · rw [hdS, shift_boxS w id p ps kS hsnd] at hm
          exact hpre.2 ⟨m, by
            rw [← hdS] at hm
            exact hm, hcf⟩
        · rw [(shift_other w id p ps kS d hd hdS).2.1] at hm
          exact hpre.2 ⟨m, hm, hcf⟩

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
        · exact False.elim ((hT.parkedOnly p.sender id kS hph).2
            ⟨x, hin, by rw [hc] at hcf; exact hcf⟩)
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
     shift_parkedOnly w id p ps kS hT hpark hph hfrom hsnd⟩
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
              (by simpa using hplain.2.2.1) hplain.2.2.2 hbox hcm
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
              have hMail := mail_install w w1 id a1 hM hst hidle
                (by simpa [hp] using hplain.2.1) hnot
              have := parked_tail_call (setActor w1 id a1) id p ps kS (tname id) m.sender hI
                hMail hparkA hphS hsnd
              simpa [setActor_same, setActor, ite_shadow, shiftBase, hc] using this
          | some c =>
            have hcall := deliver_call I hL w id ({ (w.st id) with box := ms }) m w1 a1 c hdel' hcm
            obtain ⟨kH, hrun, hshape, _, hother⟩ := hcall.2.2.2
            obtain ⟨kw, hownc⟩ := box_awaits w hT id m c (by simp [hbox]) hcm
            have hI := install_call_kept w w1 id a1 m ms c kH kw hT hidle hst
              (by simpa using hcall.1) (by simpa [hp] using hcall.2.1)
              (by simpa using hcall.2.2.1) hbox hcm hrun hshape hother hownc
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
              have hMail := mail_install w w1 id a1 hM hst hidle
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
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio) : CallTagInv w' := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      rcases hpre with h1 | h2 | h3
      · have hno : ¬(handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase) :=
          (not_iff hduty).mpr (fun h => h.elim h1.2.1 h1.2.2)
        exact Or.inl ⟨hmail.mpr h1.1, fun ho => hno (Or.inl ho), fun hp => hno (Or.inr hp)⟩
      · have hyes := hduty.mpr (Or.inl h2.2.1)
        have hnom := (not_iff hmail).mpr h2.1
        rcases hyes with ho | hp
        · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
        · exact Or.inr (Or.inr ⟨hnom, fun ho => hxor ho hp, hp⟩)
      · have hyes := hduty.mpr (Or.inr h3.2.2)
        have hnom := (not_iff hmail).mpr h3.1
        rcases hyes with ho | hp
        · exact Or.inr (Or.inl ⟨hnom, ho, hxor ho⟩)
        · exact Or.inr (Or.inr ⟨hnom, fun ho => hxor ho hp, hp⟩)
  · intro c d kA hph'
    by_cases hc : c = sender
    · rcases hmode with ⟨hphA, _, _⟩ | ⟨hphP, hparkP, hboxP⟩
      · rw [hc, hphA] at hph'
        cases hph'
      · rw [hc, hphP] at hph'
        injection hph' with hd _
        refine ⟨?_, ?_, ?_⟩
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
      have hpre := hT.parkedCall c d kA hph0
      refine ⟨(hmailNe d c hc).mpr hpre.1, ?_, ?_⟩
      · intro ho
        have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
          fun h => h.elim hpre.2.1 hpre.2.2
        by_cases hdS : d = sender
        · have hback := (hdutyS c).mp (by rw [hdS] at ho; exact Or.inl ho)
          rw [← hdS] at hback
          exact hno hback
        · have ho0 : handlerOwes c (w.st d).phase := by rw [hother d hdS] at ho; exact ho
          exact hpre.2.1 ho0
      · intro hp
        have hno : ¬(handlerOwes c (w.st d).phase ∨ replyPending c (w.st d).phase) :=
          fun h => h.elim hpre.2.1 hpre.2.2
        by_cases hdS : d = sender
        · have hback := (hdutyS c).mp (by rw [hdS] at hp; exact Or.inr hp)
          rw [← hdS] at hback
          exact hno hback
        · have hp0 : replyPending c (w.st d).phase := by rw [hother d hdS] at hp; exact hp
          exact hpre.2.2 hp0
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
        refine ⟨?_, ?_⟩
        · exact ⟨{ sender := sender, msg := msg, isCall := true }, by
            rw [← hd, hparkP]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl), hc.symm, by
            rw [← hc] at hfrom
            exact hfrom⟩
        · intro ⟨m, hm, hcf⟩
          rw [← hd, hboxP] at hm
          exact run_unnamed w hT sender kRun hph dst (Or.inl ⟨m, hm, by rw [hc] at hcf; exact hcf⟩)
    · have hph0 : (w.st c).phase = .parked d true kA := by rw [hother c hc] at hph'; exact hph'
      have hpre := hT.parkedOnly c d kA hph0
      refine ⟨?_, ?_⟩
      · obtain ⟨q, hq, hsend, hcf⟩ := hpre.1
        by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · exact ⟨q, by rw [hd] at hq; rw [hd, hparkA]; exact hq, hsend, hcf⟩
          · exact ⟨q, by
              rw [hd] at hq
              rw [hd, hparkP]
              exact List.mem_append_left _ hq, hsend, hcf⟩
        · exact ⟨q, by rw [hparkI d hd]; exact hq, hsend, hcf⟩
      · intro ⟨m, hm, hcf⟩
        by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · rw [hd, hboxA, List.mem_append] at hm
            rcases hm with hold | heq
            · exact hpre.2 ⟨m, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              injection hcf with heqc
              exact False.elim (hc heqc.symm)
          · rw [hd, hboxP] at hm
            exact hpre.2 ⟨m, by rw [hd]; exact hm, hcf⟩
        · rw [hboxI d hd] at hm
          exact hpre.2 ⟨m, hm, hcf⟩

/-- A call effect enqueues a fresh tag, or proceeds when the target is not alive. -/
theorem enqueue_call_tag (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (kRun : Cont) (e : Eff) (es : List Eff) (hT : CallTagInv w) (hM : MailInv w)
    (hph : (w.st sender).phase = .run kRun) (hrest : kRun.rest = e :: es) (hne : e ≠ .reply)
    (hterm : e ≠ .terminate) (hfrom : msg.callFrom = some sender) :
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
        apply fresh_call_tag w _ sender sender msg (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inl ⟨by simp [setActor], ?_, ?_⟩
          · simp [setActor, chargeSender, bumpToken]
          · simp [setActor, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
      · rw [enqueue_room_other_call w D sender dst msg (afterHead kRun) hlive hsame hroom.1 hroom.2]
        apply fresh_call_tag w _ sender dst msg (afterHead kRun) kRun hT hM hph e es hrest hne
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
          · simp [setActor, hflip]
          · simp [setActor, hflip]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          have h := hroom
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_park_self w D sender msg true (afterHead kRun) hliveS hroomS]
        apply fresh_call_tag w _ sender sender msg (afterHead kRun) kRun hT hM hph e es hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inr ⟨by simp [setActor], ?_, ?_⟩
          · simp [setActor, chargeSender, bumpToken]
          · simp [setActor, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
      · rw [enqueue_park_other w D sender dst msg true (afterHead kRun) hlive hsame hroom]
        apply fresh_call_tag w _ sender dst msg (afterHead kRun) kRun hT hM hph e es hrest hne
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
          refine Or.inr ⟨by simp [setActor, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, hflip]
          · simp [setActor, hflip]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
  · rw [enqueue_dead w D sender dst msg true (afterHead kRun) hlive]
    exact run_tail_tag w sender kRun e es hT hph hrest hne hterm

theorem not_shape_zero (c : InstId) (k : Cont) (h : replyCount k.rest = 0) : ¬replyShape c k := by
  intro hs
  have hc := hs.2.1
  rw [h] at hc
  omega

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

/-- A reply and the resumption of its caller, checked on the combined post-state.
`oweOwner` names that caller, so every other `awaitReply` is left in place. -/
theorem reply_resume_tag (w : World) (sender c : InstId) (k ck : Cont) (es : List Eff)
    (hT : CallTagInv w) (hph : (w.st sender).phase = .run k) (hrest : k.rest = .reply :: es)
    (hcount : replyCount k.rest = 1) (hto : k.replyTo = some c)
    (hwait : (w.st c).phase = .awaitReply sender ck) (hcne : c ≠ sender) :
    let w1 := setActor w c (proceed (w.st c) ck)
    CallTagInv (setActor w1 sender (proceed (w1.st sender) (afterHead k))) := by
  have htail : replyCount es = 0 := by
    simp [replyCount, hrest] at hcount
    omega
  let k' := afterHead k
  have hkrest : k'.rest = es := by simp [k', afterHead, hrest]
  let w1 := setActor w c (proceed (w.st c) ck)
  let w' := setActor w1 sender (proceed (w1.st sender) k')
  have hflip : ¬ sender = c := fun h => hcne h.symm
  have hS : w1.st sender = w.st sender := by simp [w1, setActor, hflip]
  have hpend : replyPending c (w.st sender).phase :=
    ⟨k, by simp [carriedCont, hph], ⟨hto, hcount, by simp [terminateBeforeReply, hrest]⟩,
      by simp [nextIsReply, hrest]⟩
  have hnom : ¬mailCall w sender c := by
    have hpre := hT.awaiting c sender ck hwait
    rcases hpre with h1 | h2 | h3
    · exact False.elim (h1.2.2 hpend)
    · exact False.elim (h2.2.2 hpend)
    · exact h3.1
  have hst (i : InstId) (hc0 : i ≠ c) (hs0 : i ≠ sender) : w'.st i = w.st i := by
    simp [w', w1, setActor, hc0, hs0]
  have hbox (i : InstId) : (w'.st i).box = (w.st i).box := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, proceed_fields, hcne]
      · simp [hst i hc0 hs0]
  have hparked (i : InstId) : (w'.st i).parked = (w.st i).parked := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, proceed_fields, hcne]
      · simp [hst i hc0 hs0]
  have hprioL (i : InstId) : (w'.st i).prio = (w.st i).prio := by
    by_cases hs0 : i = sender
    · simp [w', w1, hs0, setActor, hflip, proceed_fields]
    · by_cases hc0 : i = c
      · simp [w', w1, hs0, hc0, setActor, proceed_fields, hcne]
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
        simp [w', w1, setActor, hcne, proceed, hk, handlerOwes, carriedCont] at h
      · intro h
        have hcar : carriedCont (w.st c).phase = some ck := by
          rw [hwait]
          simp [carriedCont]
        exact False.elim (owes_empty _ _ hcar hk c0 h)
    | cons _ _ =>
      have hcarN : carriedCont (w'.st c).phase = some ck := by
        simp [w', w1, setActor, hcne, proceed, carriedCont, hk]
      have hcarO : carriedCont (w.st c).phase = some ck := by simp [carriedCont, hwait]
      exact owes_iff_carried _ _ (hcarN.trans hcarO.symm) c0
  have hpendC (c0 : InstId) : replyPending c0 (w'.st c).phase ↔ replyPending c0 (w.st c).phase := by
    cases hk : ck.rest with
    | nil =>
      constructor
      · intro h
        simp [w', w1, setActor, hcne, proceed, hk, replyPending, carriedCont] at h
      · intro h
        have hcar : carriedCont (w.st c).phase = some ck := by
          rw [hwait]
          simp [carriedCont]
        exact False.elim (pending_empty _ _ hcar hk c0 h)
    | cons _ _ =>
      have hcarN : carriedCont (w'.st c).phase = some ck := by
        simp [w', w1, setActor, hcne, proceed, carriedCont, hk]
      have hcarO : carriedCont (w.st c).phase = some ck := by simp [carriedCont, hwait]
      exact pending_iff_carried _ _ (hcarN.trans hcarO.symm) c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c0 d kA hph'
    by_cases hc0 : c0 = c
    · cases hk : ck.rest <;> simp [w', w1, setActor, hcne, proceed, hk, hc0] at hph'
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
        rcases hpre with h1 | h2 | h3
        · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpendI).mpr h1.2.2⟩
        · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpendI).mpr h2.2.2⟩)
        · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpendI.mpr h3.2.2⟩)
  · intro c0 d kA hph'
    by_cases hc0 : c0 = c
    · cases hk : ck.rest <;> simp [w', w1, setActor, hcne, proceed, hk, hc0] at hph'
    · by_cases hs0 : c0 = sender
      · cases hes : es <;> simp [w', setActor, proceed, hS, k', hkrest, hes, hs0] at hph'
      · have hph0 : (w.st c0).phase = .parked d true kA := by
          simp [w', w1, setActor, hc0, hs0] at hph'
          exact hph'
        have hpre := hT.parkedCall c0 d kA hph0
        have hmail := mail_iff_lists w w' hbox hparked d c0
        refine ⟨hmail.mpr hpre.1, ?_, ?_⟩
        · intro ho
          by_cases hd : d = sender
          · exact False.elim ((hquietS c0).1 (by rw [hd] at ho; exact ho))
          · by_cases hdc : d = c
            · rw [hdc] at ho hpre
              exact hpre.2.1 ((howeC c0).mp ho)
            · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
              exact hpre.2.1 (by simpa [← hpe] using ho)
        · intro hp
          by_cases hd : d = sender
          · exact False.elim ((hquietS c0).2 (by rw [hd] at hp; exact hp))
          · by_cases hdc : d = c
            · rw [hdc] at hp hpre
              exact hpre.2.2 ((hpendC c0).mp hp)
            · have hpe : (w'.st d).phase = (w.st d).phase := by simp [w', w1, setActor, hd, hdc]
              exact hpre.2.2 (by simpa [← hpe] using hp)
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
            · cases hck : ck.rest <;> simp [w', w1, setActor, hcne, proceed, hck, hc1] at hk
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
          · cases hck : ck.rest <;> simp [w', w1, setActor, hcne, proceed, hck, hc1] at hk1
          · simpa [hst c1 hc1 hs1] using hk1)
      c0 d0 k0 hk0

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
    unfold performReply
    rw [hto]
    simp [hwait, hflip]
    exact reply_resume_tag w sender c k ck es hT hph hrest hcount hto hwait hcne

/-- Replacing one actor's priority lane with plain messages keeps call tags. -/
theorem prio_keep_tag (w : World) (id : InstId) (prio : List Msg) (hT : CallTagInv w)
    (hplain : ∀ m, m ∈ prio → m.callFrom = none) :
    CallTagInv (setActor w id { (w.st id) with prio := prio }) := by
  let w' := setActor w id { (w.st id) with prio := prio }
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

/-- A wake is a plain priority message, or no change. -/
theorem try_wake_tag (D : Description) (w : World) (dst : InstId) (label : String) (writer : InstId)
    (hT : CallTagInv w) : CallTagInv (tryWake D w dst label writer) := by
  by_cases hif : ((w.st dst).life == .alive &&
      decide ((w.st dst).prio.length < capPrio D w.N dst) &&
      !((w.st dst).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif]
    apply prio_keep_tag w dst (upsertPrio (w.st dst).prio { label := label, sender := writer, callFrom := none }) hT
    intro m hm
    unfold upsertPrio at hm
    by_cases hany : (w.st dst).prio.any (fun p => p.label == label) = true
    · simp [hany] at hm
      exact hT.prioPlain dst m hm
    · simp [hany, List.mem_append, List.mem_singleton] at hm
      rcases hm with hold | heq
      · exact hT.prioPlain dst m hold
      · simp [heq]
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
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio) : CallTagInv w' := by
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
      have hpre := hT.parkedOnly c d kA hph0
      refine ⟨?_, ?_⟩
      · obtain ⟨q, hq, hs, hcf⟩ := hpre.1
        by_cases hd : d = dst
        · rcases hmode with ⟨_, _, hparkA⟩ | ⟨_, hparkP, _⟩
          · exact ⟨q, by rw [hd] at hq; rw [hd, hparkA]; exact hq, hs, hcf⟩
          · exact ⟨q, by rw [hd] at hq; rw [hd, hparkP]; exact List.mem_append_left _ hq, hs, hcf⟩
        · exact ⟨q, by rw [hparkI d hd]; exact hq, hs, hcf⟩
      · intro ⟨m, hm, hcf⟩
        by_cases hd : d = dst
        · rcases hmode with ⟨_, hboxA, _⟩ | ⟨_, _, hboxP⟩
          · rw [hd, hboxA, List.mem_append] at hm
            rcases hm with hold | heq
            · exact hpre.2 ⟨m, by rw [hd]; exact hold, hcf⟩
            · simp [List.mem_singleton] at heq
              rw [heq, hfrom] at hcf
              cases hcf
          · rw [hd, hboxP] at hm
            exact hpre.2 ⟨m, by rw [hd]; exact hm, hcf⟩
        · rw [hboxI d hd] at hm
          exact hpre.2 ⟨m, hm, hcf⟩

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
        apply plain_move_tag w _ sender sender msg (afterHead kRun) kRun e es hT hph hrest hne
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
      · rw [enqueue_room_other_send w D sender dst msg (afterHead kRun) hlive hsame hroom.1 hroom.2]
        apply plain_move_tag w _ sender dst msg (afterHead kRun) kRun e es hT hph hrest hne
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
          · simp [setActor, hflip]
          · simp [setActor, hflip]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, proceed_fields, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by
          have h := hlive
          rwa [← hsame] at h
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          have h := hroom
          rwa [← hsame] at h
        rw [← hsame]
        rw [enqueue_park_self w D sender msg false (afterHead kRun) hliveS hroomS]
        apply plain_move_tag w _ sender sender msg (afterHead kRun) kRun e es hT hph hrest hne
          hterm rfl hfrom
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · intro i hi
          simp [setActor, hi]
        · refine Or.inr ⟨by simp [setActor, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, chargeSender, bumpToken]
          · simp [setActor, chargeSender, bumpToken]
        · intro i
          by_cases hi : i = sender <;> simp [setActor, hi, chargeSender, bumpToken]
      · rw [enqueue_park_other w D sender dst msg false (afterHead kRun) hlive hsame hroom]
        apply plain_move_tag w _ sender dst msg (afterHead kRun) kRun e es hT hph hrest hne
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
          refine Or.inr ⟨by simp [setActor, chargeSender, bumpToken], ?_, ?_⟩
          · simp [setActor, hflip]
          · simp [setActor, hflip]
        · intro i
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst
            · have hflip : ¬ dst = sender := fun h => hsame h.symm
              simp [setActor, hi, hid, hflip]
            · simp [setActor, hi, hid]
  · rw [enqueue_dead w D sender dst msg false (afterHead kRun) hlive]
    exact run_tail_tag w sender kRun e es hT hph hrest hne hterm

/-- A self-schedule either proceeds or arms one plain priority label. The overflow
branch is the one `lane_has_room` rules out for a declared label. -/
theorem schedule_tag (I : Impl) (w : World) (hT : CallTagInv w) (id : InstId) (k : Cont)
    (label : String) (es : List Eff) (hph : (w.st id).phase = .run k)
    (hrest : k.rest = .selfSchedule label :: es)
    (hroom : ((w.st id).prio.any fun p => p.label == label) = false →
      (w.st id).prio.length < capPrio I.desc w.N id) :
    CallTagInv (execRun I w id (w.st id) k) := by
  simp [execRun, hrest]
  cases hany : ((w.st id).prio.any fun p => p.label == label)
  · have hlt := hroom hany
    rw [List.any_eq_false] at hany
    have hno : ¬ ∃ x, x ∈ (w.st id).prio ∧ x.label = label := by
      intro ⟨x, hx, hl⟩
      have hf := hany x hx
      rw [(beq_iff_eq).mpr hl] at hf
      simp at hf
    simp [hno, hlt]
    let grown := upsertPrio (w.st id).prio { label := label, sender := id, callFrom := none }
    have hplain : ∀ m, m ∈ grown → m.callFrom = none := by
      intro m hm
      simp [upsertPrio, grown, hno, List.mem_append, List.mem_singleton] at hm
      rcases hm with hold | heq
      · exact hT.prioPlain id m hold
      · rw [heq]
    have hP := prio_keep_tag w id grown hT hplain
    have hphP : ((setActor w id { (w.st id) with prio := grown }).st id).phase = .run k := by
      simp [setActor, hph]
    have hrun := run_tail_tag (setActor w id { (w.st id) with prio := grown }) id k
      (.selfSchedule label) es hP hphP hrest (by intro h; cases h) (by intro h; cases h)
    have hself : (setActor w id { (w.st id) with prio := grown }).st id =
        { (w.st id) with prio := grown } := by simp [setActor]
    rw [setActor_same, hself] at hrun
    simpa [grown] using hrun
  · rw [List.any_eq_true] at hany
    obtain ⟨x, hx, hb⟩ := hany
    have hyes : ∃ x, x ∈ (w.st id).prio ∧ x.label = label := ⟨x, hx, (beq_iff_eq).mp hb⟩
    simp [hyes]
    exact run_tail_tag w id k (.selfSchedule label) es hT hph hrest
      (by intro h; cases h) (by intro h; cases h)

end Deadlock
