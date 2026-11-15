import Deadlock.Pres

set_option autoImplicit false

namespace Deadlock

/-- A phase that is not blocked on a mailbox. -/
def notParked (ph : Phase) : Prop :=
  match ph with
  | .parked _ _ _ => False
  | _ => True

/-- Parked entries and parked phases name each other, with one entry per sender.
Kept separate from `SemInv`: a mailbox update and the sender's phase update are
one step, and the intermediate state is not in the relation. -/
structure MailInv (w : World) : Prop where
  fwd : ∀ (mb : InstId) (p : Parked), p ∈ (w.st mb).parked →
    ∃ k, (w.st p.sender).phase = .parked mb p.isCall k
  bwd : ∀ (id dst : InstId) (isCall : Bool) (k : Cont),
    (w.st id).phase = .parked dst isCall k →
    ∃ p, p ∈ (w.st dst).parked ∧ p.sender = id ∧ p.isCall = isCall
  uniq : ∀ mb1 mb2 p1 p2, p1 ∈ (w.st mb1).parked → p2 ∈ (w.st mb2).parked →
    p1.sender = p2.sender → mb1 = mb2 ∧ p1 = p2

theorem not_queued (w : World) (id : InstId) (hM : MailInv w) (hf : notParked (w.st id).phase) :
    ∀ mb p, p ∈ (w.st mb).parked → p.sender ≠ id := by
  intro mb p hp heq
  obtain ⟨k, hk⟩ := hM.fwd mb p hp
  rw [heq] at hk
  simp [notParked, hk] at hf

theorem mail_copy (w w' : World) (hM : MailInv w) (h : ∀ i, w'.st i = w.st i) : MailInv w' := by
  refine ⟨?_, ?_, ?_⟩
  · intro mb p hp
    rw [h] at hp
    obtain ⟨k, hk⟩ := hM.fwd mb p hp
    exact ⟨k, by simpa [h] using hk⟩
  · intro id dst c k hk
    rw [h] at hk
    obtain ⟨p, hp, hs, hc⟩ := hM.bwd id dst c k hk
    exact ⟨p, by simpa [h] using hp, hs, hc⟩
  · intro mb1 mb2 p1 p2 h1 h2 hs
    rw [h] at h1
    rw [h] at h2
    exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs

theorem init_parked (I : Impl) (N : Nat) (id : InstId) : ((initWorld I N).st id).parked = [] := by
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem mail_init (I : Impl) (N : Nat) : MailInv (initWorld I N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mb p hp
    simp [init_parked] at hp
  · intro id dst c k hk
    simp [init_phase] at hk
  · intro mb1 mb2 p1 p2 h1 h2 _
    simp [init_parked] at h1

/-- Replace an actor that is not parked, without making it parked or changing its queue. -/
theorem mail_set_free (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hold : notParked (w.st id).phase) (hnew : notParked a.phase)
    (hlist : a.parked = (w.st id).parked) : MailInv (setActor w id a) := by
  have hnq := not_queued w id hM hold
  refine ⟨?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hmb : mb = id
    · rw [hmb, setActor_self, hlist] at hp
      have hne := hnq id p hp
      obtain ⟨k, hk⟩ := hM.fwd id p hp
      rw [setActor_other w id p.sender a hne, hmb]
      exact ⟨k, hk⟩
    · rw [setActor_other w id mb a hmb] at hp
      have hne := hnq mb p hp
      obtain ⟨k, hk⟩ := hM.fwd mb p hp
      rw [setActor_other w id p.sender a hne]
      exact ⟨k, hk⟩
  · intro sid dst c k hk
    by_cases hs : sid = id
    · rw [hs, setActor_self] at hk
      cases hpa : a.phase <;> simp [hpa, notParked] at hnew hk
    · rw [setActor_other w id sid a hs] at hk
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwd sid dst c k hk
      by_cases hd : dst = id
      · rw [hd, setActor_self, hlist]
        exact ⟨p, by simpa [hd] using hp, hsender, hc⟩
      · rw [setActor_other w id dst a hd]
        exact ⟨p, hp, hsender, hc⟩
  · intro mb1 mb2 p1 p2 h1 h2 hs
    by_cases hm1 : mb1 = id
    · rw [hm1, setActor_self, hlist] at h1
      by_cases hm2 : mb2 = id
      · rw [hm2, setActor_self, hlist] at h2
        have huniq := hM.uniq id id p1 p2 h1 h2 hs
        exact ⟨by rw [hm1, hm2], huniq.2⟩
      · rw [setActor_other w id mb2 a hm2] at h2
        have hu := hM.uniq id mb2 p1 p2 h1 h2 hs
        exact ⟨hm1.trans hu.1, hu.2⟩
    · rw [setActor_other w id mb1 a hm1] at h1
      by_cases hm2 : mb2 = id
      · rw [hm2, setActor_self, hlist] at h2
        have hu := hM.uniq mb1 id p1 p2 h1 h2 hs
        exact ⟨hu.1.trans hm2.symm, hu.2⟩
      · rw [setActor_other w id mb2 a hm2] at h2
        exact hM.uniq mb1 mb2 p1 p2 h1 h2 hs

/-- Same phase and the same queue: tokens, the bulk box, and priority do not affect mail. -/
theorem mail_set_same (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hphase : a.phase = (w.st id).phase) (hlist : a.parked = (w.st id).parked) :
    MailInv (setActor w id a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hmb : mb = id
    · rw [hmb, setActor_self, hlist] at hp
      obtain ⟨k, hk⟩ := hM.fwd id p hp
      by_cases hs : p.sender = id
      · rw [hs, setActor_self, hphase, hmb]
        rw [hs] at hk
        exact ⟨k, hk⟩
      · rw [setActor_other w id p.sender a hs]
        exact ⟨k, by simpa [hmb] using hk⟩
    · rw [setActor_other w id mb a hmb] at hp
      obtain ⟨k, hk⟩ := hM.fwd mb p hp
      by_cases hs : p.sender = id
      · rw [hs, setActor_self, hphase]
        rw [hs] at hk
        exact ⟨k, hk⟩
      · rw [setActor_other w id p.sender a hs]
        exact ⟨k, hk⟩
  · intro sid dst c k hk
    by_cases hs : sid = id
    · rw [hs, setActor_self, hphase] at hk
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwd id dst c k (by simpa [hs] using hk)
      by_cases hd : dst = id
      · exact ⟨p, by rw [hd, setActor_self, hlist]; simpa [hd] using hp, by simpa [hs] using hsender, hc⟩
      · exact ⟨p, by rw [setActor_other w id dst a hd]; exact hp, by simpa [hs] using hsender, hc⟩
    · rw [setActor_other w id sid a hs] at hk
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwd sid dst c k hk
      by_cases hd : dst = id
      · exact ⟨p, by rw [hd, setActor_self, hlist]; simpa [hd] using hp, hsender, hc⟩
      · exact ⟨p, by rw [setActor_other w id dst a hd]; exact hp, hsender, hc⟩
  · intro mb1 mb2 p1 p2 h1 h2 hsnd
    by_cases hm1 : mb1 = id
    · rw [hm1, setActor_self, hlist] at h1
      by_cases hm2 : mb2 = id
      · rw [hm2, setActor_self, hlist] at h2
        have hu := hM.uniq id id p1 p2 h1 h2 hsnd
        exact ⟨by rw [hm1, hm2], hu.2⟩
      · rw [setActor_other w id mb2 a hm2] at h2
        have hu := hM.uniq id mb2 p1 p2 h1 h2 hsnd
        exact ⟨hm1.trans hu.1, hu.2⟩
    · rw [setActor_other w id mb1 a hm1] at h1
      by_cases hm2 : mb2 = id
      · rw [hm2, setActor_self, hlist] at h2
        have hu := hM.uniq mb1 id p1 p2 h1 h2 hsnd
        exact ⟨hu.1.trans hm2.symm, hu.2⟩
      · rw [setActor_other w id mb2 a hm2] at h2
        exact hM.uniq mb1 mb2 p1 p2 h1 h2 hsnd

theorem charge_parked (a : Actor) (d : String) : (chargeSender a d).parked = a.parked := by
  simp [chargeSender, bumpToken]

theorem charge_phase (a : Actor) (d : String) : (chargeSender a d).phase = a.phase := by
  simp [chargeSender, bumpToken]

theorem proceed_parked (a : Actor) (k : Cont) : (proceed a k).parked = a.parked := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem proceed_not_parked (a : Actor) (k : Cont) : notParked (proceed a k).phase := by
  cases hk : k.rest <;> simp [proceed, notParked, hk]

end Deadlock
