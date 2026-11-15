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
  sole : ∀ d c, soleCall w d c

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (hsole : ∀ d c, soleCall w' d c) : CallTagInv w' := by
  refine ⟨?_, ?_, ?_, ?_, hprio, hsole⟩
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Admitting a parked call rewrites the phase to `awaitReply` and keeps the message. -/
theorem admit_phase (w : World) (s d : InstId) (k : Cont) (hT : CallTagInv w)
    (hph : (w.st s).phase = .parked d true k) :
    CallTagInv (setActor w s { (w.st s) with phase := .awaitReply d k }) := by
  let w' := setActor w s { (w.st s) with phase := .awaitReply d k }
  have hcar : carriedCont (w'.st s).phase = carriedCont (w.st s).phase := by
    simp [w', setActor, carriedCont, hph]
  have hbox : ∀ i, (w'.st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = s <;> simp [w', setActor, hi]
  have hparkL : ∀ i, (w'.st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = s <;> simp [w', setActor, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c dst kA hph'
    by_cases hc : c = s
    · have hpre := hT.parkedCall s d k hph
      have hmail : mailCall w' d c := by
        rw [hc]
        rcases hpre.1 with ⟨m, hm, hcf⟩ | ⟨p, hp, hcf⟩
        · exact Or.inl ⟨m, by simpa [← hbox d] using hm, hcf⟩
        · exact Or.inr ⟨p, by simpa [← hparkL d] using hp, hcf⟩
      have howe : ¬handlerOwes c (w'.st d).phase := by
        by_cases hd : d = s
        · rw [hd] at hpre ⊢
          have hiff := owes_iff_carried (w.st s).phase (w'.st s).phase hcar c
          exact (not_iff hiff).mpr (by simpa [hc] using hpre.2.1)
        · simpa [w', setActor, hd, hc] using hpre.2.1
      have hpend : ¬replyPending c (w'.st d).phase := by
        by_cases hd : d = s
        · rw [hd] at hpre ⊢
          have hiff := pending_iff_carried (w.st s).phase (w'.st s).phase hcar c
          exact (not_iff hiff).mpr (by simpa [hc] using hpre.2.2)
        · simpa [w', setActor, hd, hc] using hpre.2.2
      have hdst : dst = d ∧ kA = k := by
        simp [w', setActor, hc, hph] at hph'
        exact ⟨hph'.1.symm, hph'.2.symm⟩
      simp [hdst.1, hdst.2]
      exact Or.inl ⟨hmail, howe, hpend⟩
    · have hold : (w.st c).phase = .awaitReply dst kA := by simpa [w', setActor, hc] using hph'
      have hpre := hT.awaiting c dst kA hold
      have hmail : mailCall w' dst c ↔ mailCall w dst c :=
        mail_iff_lists w w' hbox hparkL dst c
      have howe : handlerOwes c (w'.st dst).phase ↔ handlerOwes c (w.st dst).phase := by
        by_cases hd : dst = s
        · exact owes_iff_carried _ _ (by simp [hd, hcar]) c
        · exact owes_iff_carried _ _ (by simp [w', setActor, hd]) c
      have hpend : replyPending c (w'.st dst).phase ↔ replyPending c (w.st dst).phase := by
        by_cases hd : dst = s
        · exact pending_iff_carried _ _ (by simp [hd, hcar]) c
        · exact pending_iff_carried _ _ (by simp [w', setActor, hd]) c
      rcases hpre with h1 | h2 | h3
      · exact Or.inl ⟨hmail.mpr h1.1, (not_iff howe).mpr h1.2.1, (not_iff hpend).mpr h1.2.2⟩
      · exact Or.inr (Or.inl ⟨(not_iff hmail).mpr h2.1, howe.mpr h2.2.1, (not_iff hpend).mpr h2.2.2⟩)
      · exact Or.inr (Or.inr ⟨(not_iff hmail).mpr h3.1, (not_iff howe).mpr h3.2.1, hpend.mpr h3.2.2⟩)
  · intro c dst kA hph'
    by_cases hc : c = s
    · simp [w', setActor, hc] at hph'
    · have hold := by simpa [w', setActor, hc] using hph'
      have hpre := hT.parkedCall c dst kA hold
      have hmail : mailCall w' dst c := by
        rcases hpre.1 with ⟨m, hm, hcf⟩ | ⟨p, hp, hcf⟩
        · exact Or.inl ⟨m, by simpa [← hbox dst] using hm, hcf⟩
        · exact Or.inr ⟨p, by simpa [← hparkL dst] using hp, hcf⟩
      have howe : ¬handlerOwes c (w'.st dst).phase := by
        by_cases hd : dst = s
        · rw [hd] at hpre ⊢
          have hiff := owes_iff_carried (w.st s).phase (w'.st s).phase hcar c
          exact (not_iff hiff).mpr hpre.2.1
        · simpa [w', setActor, hd] using hpre.2.1
      have hpend : ¬replyPending c (w'.st dst).phase := by
        by_cases hd : dst = s
        · rw [hd] at hpre ⊢
          have hiff := pending_iff_carried (w.st s).phase (w'.st s).phase hcar c
          exact (not_iff hiff).mpr hpre.2.2
        · simpa [w', setActor, hd] using hpre.2.2
      exact ⟨hmail, howe, hpend⟩
  · intro dst c hm
    have hpreM : mailCall w dst c := by
      rcases hm with ⟨m, hmem, hcf⟩ | ⟨p, hmem, hcf⟩
      · exact Or.inl ⟨m, by rw [hbox dst] at hmem; exact hmem, hcf⟩
      · exact Or.inr ⟨p, by rw [hparkL dst] at hmem; exact hmem, hcf⟩
    rcases hT.msgOwner dst c hpreM with ⟨kA, hkA⟩ | ⟨kA, hkA⟩
    · exact Or.inl ⟨kA, by
        by_cases hc : c = s
        · rw [hc] at hkA
          simp [hph] at hkA
        · simpa [w', setActor, hc] using hkA⟩
    · by_cases hc : c = s
      · rw [hc] at hkA
        have hdd : d = dst ∧ k = kA := by simpa [hph] using hkA
        exact Or.inl ⟨k, by simp [w', setActor, hc, hdd.1]⟩
      · exact Or.inr ⟨kA, by simpa [w', setActor, hc] using hkA⟩
  · intro dst c ho
    have hpreO : handlerOwes c (w.st dst).phase ∨ replyPending c (w.st dst).phase := by
      by_cases hd : dst = s
      · rw [hd] at ho ⊢
        have hiff := owes_iff_carried (w'.st s).phase (w.st s).phase hcar.symm c
        have hiffP := pending_iff_carried (w'.st s).phase (w.st s).phase hcar.symm c
        rcases ho with h | h
        · exact Or.inl (hiff.mpr h)
        · exact Or.inr (hiffP.mpr h)
      · simpa [w', setActor, hd] using ho
    obtain ⟨kA, hkA⟩ := hT.oweOwner dst c hpreO
    by_cases hc : c = s
    · simp [hph, hc] at hkA
    · exact ⟨kA, by simpa [w', setActor, hc] using hkA⟩
  · intro i m hm
    by_cases hi : i = s
    · exact hT.prioPlain s m (by simpa [w', setActor, hi] using hm)
    · exact hT.prioPlain i m (by simpa [w', setActor, hi] using hm)
  · intro dst c
    unfold soleCall
    rw [hbox dst, hparkL dst]
    exact hT.sole dst c

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

end Deadlock
