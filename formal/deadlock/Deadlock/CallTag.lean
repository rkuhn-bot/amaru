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
the next effect. A parked call is the same obligation before admission, so a
`callFrom` may also belong to a caller whose phase is `.parked d true`. No
priority message carries a `callFrom`. -/
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    (hprio : ∀ id m, m ∈ (w'.st id).prio → m.callFrom = none) : CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio⟩
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

theorem call_tag_init (I : Impl) (N : Nat) : CallTagInv (initWorld I N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

end Deadlock
