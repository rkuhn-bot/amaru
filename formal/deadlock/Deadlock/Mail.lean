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
  /-- A sender occupies one slot: the parked list has no duplicate entries. -/
  once : ∀ mb, (w.st mb).parked.Nodup

theorem not_queued (w : World) (id : InstId) (hM : MailInv w) (hf : notParked (w.st id).phase) :
    ∀ mb p, p ∈ (w.st mb).parked → p.sender ≠ id := by
  intro mb p hp heq
  obtain ⟨k, hk⟩ := hM.fwd mb p hp
  rw [heq] at hk
  simp [notParked, hk] at hf

theorem mail_copy (w w' : World) (hM : MailInv w) (h : ∀ i, w'.st i = w.st i) : MailInv w' := by
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro mb
    simpa [h mb] using hM.once mb

theorem init_parked (I : Impl) (N : Nat) (id : InstId) : ((initWorld I N).st id).parked = [] := by
  rw [init_base_st]
  split
  · simp [initActor, absentActor, withTokens]
    split <;> simp [withTokens, absentActor]
  · simp [absentActor]

theorem mail_init (I : Impl) (N : Nat) : MailInv (initWorld I N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    simp [init_parked] at hp
  · intro id dst c k hk
    simp [init_phase] at hk
  · intro mb1 mb2 p1 p2 h1 h2 _
    simp [init_parked] at h1
  · intro mb
    simp [init_parked]

/-- Replace an actor that is not parked, without making it parked or changing its queue. -/
theorem mail_set_free (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hold : notParked (w.st id).phase) (hnew : notParked a.phase)
    (hlist : a.parked = (w.st id).parked) : MailInv (setActor w id a) := by
  have hnq := not_queued w id hM hold
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro mb
    by_cases hmb : mb = id
    · rw [hmb, setActor_self, hlist]
      exact hM.once id
    · rw [setActor_other w id mb a hmb]
      exact hM.once mb

/-- Same phase and the same queue: tokens, the bulk box, and priority do not affect mail. -/
theorem mail_set_same (w : World) (id : InstId) (a : Actor) (hM : MailInv w)
    (hphase : a.phase = (w.st id).phase) (hlist : a.parked = (w.st id).parked) :
    MailInv (setActor w id a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro mb
    by_cases hmb : mb = id
    · rw [hmb, setActor_self, hlist]
      exact hM.once id
    · rw [setActor_other w id mb a hmb]
      exact hM.once mb

theorem nodup_snoc {α : Type} {l : List α} {a : α} (hl : l.Nodup) (ha : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    have htail := ih hl.2 (fun h => ha (List.mem_cons_of_mem _ h))
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, htail⟩
    intro hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    cases hmem with
    | inl h => exact hl.1 h
    | inr h =>
      cases h
      exact ha List.mem_cons_self

theorem charge_parked (a : Actor) (d : String) : (chargeSender a d).parked = a.parked := by
  simp [chargeSender, bumpToken]

theorem charge_phase (a : Actor) (d : String) : (chargeSender a d).phase = a.phase := by
  simp [chargeSender, bumpToken]

theorem proceed_parked (a : Actor) (k : Cont) : (proceed a k).parked = a.parked := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem proceed_not_parked (a : Actor) (k : Cont) : notParked (proceed a k).phase := by
  cases hk : k.rest <;> simp [proceed, notParked, hk]

/-- Park the sender on its own mailbox: one actor carries both the entry and the phase. -/
theorem mail_park_self (w : World) (sender : InstId) (a : Actor) (entry : Parked)
    (c : Bool) (k : Cont) (hM : MailInv w) (hfree : notParked (w.st sender).phase)
    (hphase : a.phase = .parked sender c k)
    (hlist : a.parked = (w.st sender).parked ++ [entry])
    (hentry : entry.sender = sender ∧ entry.isCall = c) :
    MailInv (setActor w sender a) := by
  have hnq := not_queued w sender hM hfree
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hmb : mb = sender
    · rw [hmb, setActor_self, hlist] at hp
      simp [List.mem_append, List.mem_singleton] at hp
      cases hp with
      | inl hold =>
        have hne := hnq sender p hold
        obtain ⟨ck, hck⟩ := hM.fwd sender p hold
        rw [setActor_other w sender p.sender a hne, hmb]
        exact ⟨ck, hck⟩
      | inr hnew =>
        rw [hnew, hentry.1, hentry.2, hmb, setActor_self, hphase]
        exact ⟨k, rfl⟩
    · rw [setActor_other w sender mb a hmb] at hp
      have hne := hnq mb p hp
      obtain ⟨ck, hck⟩ := hM.fwd mb p hp
      rw [setActor_other w sender p.sender a hne]
      exact ⟨ck, hck⟩
  · intro sid dst c' k' hk
    by_cases hs : sid = sender
    · rw [hs, setActor_self, hphase] at hk
      cases hk
      refine ⟨entry, ?_, by simpa [hs] using hentry.1, hentry.2⟩
      rw [setActor_self, hlist]
      simp [List.mem_append]
    · rw [setActor_other w sender sid a hs] at hk
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwd sid dst c' k' hk
      by_cases hd : dst = sender
      · refine ⟨p, ?_, hsender, hc⟩
        rw [hd, setActor_self, hlist, List.mem_append]
        exact Or.inl (by simpa [hd] using hp)
      · exact ⟨p, by rw [setActor_other w sender dst a hd]; exact hp, hsender, hc⟩
  · intro mb1 mb2 p1 p2 h1 h2 hsnd
    have fresh : ∀ {mb p}, p ∈ ((setActor w sender a).st mb).parked → p.sender = sender →
        mb = sender ∧ p = entry := by
      intro mb p hp hsend
      by_cases hmb : mb = sender
      · rw [hmb, setActor_self, hlist] at hp
        simp [List.mem_append, List.mem_singleton] at hp
        cases hp with
        | inl hold => exact absurd hsend (hnq sender p hold)
        | inr hnew => exact ⟨hmb, hnew⟩
      · rw [setActor_other w sender mb a hmb] at hp
        exact absurd hsend (hnq mb p hp)
    by_cases h1s : p1.sender = sender
    · have hm1 := fresh h1 h1s
      have hm2 := fresh h2 (hsnd.symm.trans h1s)
      exact ⟨hm1.1.trans hm2.1.symm, hm1.2.trans hm2.2.symm⟩
    · have hold1 : p1 ∈ (w.st mb1).parked := by
        by_cases hmb : mb1 = sender
        · rw [hmb, setActor_self, hlist] at h1
          simp [List.mem_append, List.mem_singleton] at h1
          cases h1 with
          | inl h => simpa [hmb] using h
          | inr h => exact absurd (by rw [h]; exact hentry.1) h1s
        · rw [setActor_other w sender mb1 a hmb] at h1
          exact h1
      have h2s : p2.sender ≠ sender := fun h => h1s (hsnd.trans h)
      have hold2 : p2 ∈ (w.st mb2).parked := by
        by_cases hmb : mb2 = sender
        · rw [hmb, setActor_self, hlist] at h2
          simp [List.mem_append, List.mem_singleton] at h2
          cases h2 with
          | inl h => simpa [hmb] using h
          | inr h => exact absurd (by rw [h]; exact hentry.1) h2s
        · rw [setActor_other w sender mb2 a hmb] at h2
          exact h2
      exact hM.uniq _ _ _ _ hold1 hold2 hsnd
  · intro mb
    by_cases hmb : mb = sender
    · rw [hmb, setActor_self, hlist]
      refine nodup_snoc (hM.once sender) ?_
      intro hin
      exact hnq sender entry hin hentry.1
    · rw [setActor_other w sender mb a hmb]
      exact hM.once mb

/-- Park `sender` on a different mailbox. The entry and the phase are the final state. -/
theorem mail_park_other (w : World) (dst sender : InstId) (a stored : Actor) (entry : Parked)
    (c : Bool) (k : Cont) (hM : MailInv w) (hdiff : sender ≠ dst)
    (hfree : notParked (w.st sender).phase) (hdstPh : stored.phase = (w.st dst).phase)
    (hdstPk : stored.parked = (w.st dst).parked ++ [entry])
    (hentry : entry.sender = sender ∧ entry.isCall = c)
    (hsPh : a.phase = .parked dst c k) (hsPk : a.parked = (w.st sender).parked) :
    MailInv (setActor (setActor w dst stored) sender a) := by
  have hnq := not_queued w sender hM hfree
  let final := setActor (setActor w dst stored) sender a
  have stS : final.st sender = a := by simp [final, setActor]
  have stD : final.st dst = stored := by
    rw [setActor_other _ sender dst a hdiff.symm, setActor_self]
  have stO : ∀ i, i ≠ sender → i ≠ dst → final.st i = w.st i := by
    intro i hs hd
    rw [setActor_other _ sender i a hs, setActor_other _ dst i stored hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hms : mb = sender
    · rw [hms, stS, hsPk] at hp
      have hne := hnq sender p hp
      obtain ⟨ck, hck⟩ := hM.fwd sender p hp
      by_cases hd : p.sender = dst
      · rw [hd, stD, hdstPh]
        rw [hd] at hck
        exact ⟨ck, by simpa [hms] using hck⟩
      · rw [stO p.sender hne hd]
        exact ⟨ck, by simpa [hms] using hck⟩
    · by_cases hmd : mb = dst
      · rw [hmd, stD, hdstPk] at hp
        simp [List.mem_append, List.mem_singleton] at hp
        cases hp with
        | inl hold =>
          have hne := hnq dst p hold
          obtain ⟨ck, hck⟩ := hM.fwd dst p hold
          by_cases hsnd : p.sender = sender
          · exact absurd hsnd hne
          · by_cases hd : p.sender = dst
            · rw [hd, stD, hdstPh]
              rw [hd] at hck
              exact ⟨ck, by simpa [hmd] using hck⟩
            · rw [stO p.sender hsnd hd]
              exact ⟨ck, by simpa [hmd] using hck⟩
        | inr hnew =>
          rw [hnew, hentry.1, hentry.2, hmd, stS, hsPh]
          exact ⟨k, rfl⟩
      · rw [stO mb hms hmd] at hp
        have hne := hnq mb p hp
        obtain ⟨ck, hck⟩ := hM.fwd mb p hp
        by_cases hsnd : p.sender = sender
        · exact absurd hsnd hne
        · by_cases hd : p.sender = dst
          · rw [hd, stD, hdstPh]
            rw [hd] at hck
            exact ⟨ck, hck⟩
          · rw [stO p.sender hsnd hd]
            exact ⟨ck, hck⟩
  · intro sid dbox isC ck hk
    by_cases hs : sid = sender
    · rw [hs, stS, hsPh] at hk
      cases hk
      refine ⟨entry, ?_, by simpa [hs] using hentry.1, hentry.2⟩
      rw [stD, hdstPk]
      simp [List.mem_append]
    · have hk0 : (w.st sid).phase = .parked dbox isC ck := by
        by_cases hd : sid = dst
        · rw [hd, stD, hdstPh] at hk
          simpa [hd] using hk
        · rw [stO sid hs hd] at hk
          exact hk
      obtain ⟨p, hp, hsender, hc⟩ := hM.bwd sid dbox isC ck hk0
      by_cases hd : dbox = dst
      · refine ⟨p, ?_, hsender, hc⟩
        rw [hd, stD, hdstPk, List.mem_append]
        exact Or.inl (by simpa [hd] using hp)
      · by_cases hbox : dbox = sender
        · refine ⟨p, ?_, hsender, hc⟩
          rw [hbox, stS, hsPk]
          simpa [hbox] using hp
        · refine ⟨p, ?_, hsender, hc⟩
          rw [stO dbox hbox hd]
          exact hp
  · intro mb1 mb2 p1 p2 h1 h2 hsnd
    have fresh : ∀ {mb p}, p ∈ (final.st mb).parked → p.sender = sender → mb = dst ∧ p = entry := by
      intro mb p hp hsend
      by_cases hms : mb = sender
      · rw [hms, stS, hsPk] at hp
        exact absurd hsend (hnq sender p hp)
      · by_cases hmd : mb = dst
        · rw [hmd, stD, hdstPk] at hp
          simp [List.mem_append, List.mem_singleton] at hp
          cases hp with
          | inl hold => exact absurd hsend (hnq dst p hold)
          | inr hnew => exact ⟨hmd, hnew⟩
        · rw [stO mb hms hmd] at hp
          exact absurd hsend (hnq mb p hp)
    by_cases h1s : p1.sender = sender
    · have hm1 := fresh h1 h1s
      have hm2 := fresh h2 (hsnd.symm.trans h1s)
      exact ⟨hm1.1.trans hm2.1.symm, hm1.2.trans hm2.2.symm⟩
    · have h2s : p2.sender ≠ sender := fun h => h1s (hsnd.trans h)
      have oldOf : ∀ {mb p}, p ∈ (final.st mb).parked → p.sender ≠ sender → p ∈ (w.st mb).parked := by
        intro mb p hp hsend
        by_cases hms : mb = sender
        · rw [hms, stS, hsPk] at hp
          simpa [hms] using hp
        · by_cases hmd : mb = dst
          · rw [hmd, stD, hdstPk] at hp
            simp [List.mem_append, List.mem_singleton] at hp
            cases hp with
            | inl h => simpa [hmd] using h
            | inr h => exact absurd (by rw [h]; exact hentry.1) hsend
          · rw [stO mb hms hmd] at hp
            exact hp
      exact hM.uniq _ _ _ _ (oldOf h1 h1s) (oldOf h2 h2s) hsnd
  · intro mb
    by_cases hms : mb = sender
    · rw [hms, stS, hsPk]
      exact hM.once sender
    · by_cases hmd : mb = dst
      · rw [hmd, stD, hdstPk]
        refine nodup_snoc (hM.once dst) ?_
        intro hin
        exact hnq dst entry hin hentry.1
      · rw [stO mb hms hmd]
        exact hM.once mb

theorem await_not_parked (a : Actor) (dst : InstId) (k : Cont) :
    notParked ({ a with phase := Phase.awaitReply dst k }).phase := by
  simp [notParked]

/-- A blocking enqueue, including the branch that parks, preserves `MailInv`.
The parked entry and the sender's phase are the final state together. -/
theorem enqueue_mail (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hM : MailInv w) (hfree : notParked (w.st sender).phase) :
    MailInv (enqueueOrPark w D sender dst msg isCall k) := by
  unfold enqueueOrPark
  dsimp only
  by_cases halive : (w.st dst).life = .alive
  · simp [halive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        if hcall : isCall = true then
          simp [hcall]
          apply mail_set_free w sender _ hM hfree
          · simp [notParked, chargeSender, bumpToken]
          · simp [chargeSender, bumpToken]
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          apply mail_set_free w sender _ hM hfree
          · exact proceed_not_parked _ _
          · simp [proceed_parked, chargeSender, bumpToken]
      · simp [hsame]
        rw [← halive, ← hroom.1]
        have hM1 := mail_set_same w dst { (w.st dst) with
            box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
            nextMid := (w.st dst).nextMid + 1 } hM rfl rfl
        if hcall : isCall = true then
          simp [hcall]
          apply mail_set_free (setActor w dst { (w.st dst) with
              box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
              nextMid := (w.st dst).nextMid + 1 }) sender _ hM1
          · rw [setActor_other _ dst sender _ hsame]
            exact hfree
          · simp [notParked, chargeSender, bumpToken]
          · rw [setActor_other _ dst sender _ hsame]
            simp [chargeSender, bumpToken]
        else
          have hcf : isCall = false := by cases hbb : isCall <;> simp_all
          simp [hcf]
          apply mail_set_free (setActor w dst { (w.st dst) with
              box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
              nextMid := (w.st dst).nextMid + 1 }) sender _ hM1
          · rw [setActor_other _ dst sender _ hsame]
            exact hfree
          · exact proceed_not_parked _ _
          · rw [setActor_other _ dst sender _ hsame]
            simp [proceed_parked, chargeSender, bumpToken]
    · simp [hroom]
      by_cases hsame : sender = dst
      · subst hsame
        simp
        apply mail_park_self w sender _
          { sender := sender,
            msg := { msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid },
            isCall := isCall } isCall k hM hfree
        · simp [chargeSender, bumpToken]
        · simp [chargeSender, bumpToken]
        · simp
      · simp [hsame]
        rw [← halive]
        apply mail_park_other w dst sender
          { chargeSender (w.st sender) (tname dst) with phase := .parked dst isCall k }
          { (w.st dst) with
            parked := (w.st dst).parked ++
              [{ sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := isCall }],
            nextMid := (w.st dst).nextMid + 1 }
          { sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := isCall }
          isCall k hM hsame hfree
        · rfl
        · rfl
        · simp
        · simp [chargeSender, bumpToken]
        · simp [chargeSender, bumpToken]
  · simp [halive]
    apply mail_set_free w sender _ hM hfree
    · exact proceed_not_parked _ _
    · exact proceed_parked _ _

/-- After the queue is cleared and every former sender has left `.parked`, mail holds again. -/
theorem mail_of_clear (w0 w : World) (id : InstId) (ps : List Parked) (hM : MailInv w0)
    (hfree : notParked (w0.st id).phase) (hnocall : ∀ p ∈ ps, p.isCall = false)
    (hqueue : ∀ p, p ∈ ps ↔ p ∈ (w0.st id).parked) (hidPh : (w.st id).phase = .idle)
    (hidPk : (w.st id).parked = []) (hpk : ∀ i, i ≠ id → (w.st i).parked = (w0.st i).parked)
    (hresume : ∀ p ∈ ps, notParked (w.st p.sender).phase)
    (hother : ∀ i, i ≠ id → (∀ p ∈ ps, p.sender ≠ i) → (w.st i).phase = (w0.st i).phase) :
    MailInv w := by
  have hnq := not_queued w0 id hM hfree
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    have hmb : mb ≠ id := by
      intro h
      rw [h, hidPk] at hp
      cases hp
    have hp0 : p ∈ (w0.st mb).parked := by simpa [hpk mb hmb] using hp
    obtain ⟨k, hk⟩ := hM.fwd mb p hp0
    have hsnd : p.sender ≠ id := hnq mb p hp0
    have hnot : ∀ q ∈ ps, q.sender ≠ p.sender := by
      intro q hq heq
      have hq0 : q ∈ (w0.st id).parked := (hqueue q).mp hq
      have huniq := hM.uniq id mb q p hq0 hp0 (by rw [heq])
      exact hmb huniq.1.symm
    rw [hother p.sender hsnd hnot]
    exact ⟨k, hk⟩
  · intro sid dst c k hk
    have hsid : sid ≠ id := by
      intro h
      rw [h, hidPh] at hk
      cases hk
    have hnot : ∀ q ∈ ps, q.sender ≠ sid := by
      intro q hq heq
      have hbad := hresume q hq
      rw [heq] at hbad
      simp [notParked, hk] at hbad
    have hk0 : (w0.st sid).phase = .parked dst c k := by
      rw [← hother sid hsid (fun q hq he => hnot q hq he)]
      exact hk
    obtain ⟨p, hp, hsender, hc⟩ := hM.bwd sid dst c k hk0
    have hdst : dst ≠ id := by
      intro h
      have hpq : p ∈ ps := (hqueue p).mpr (by simpa [h] using hp)
      exact hnot p hpq hsender
    exact ⟨p, by simpa [hpk dst hdst] using hp, hsender, hc⟩
  · intro mb1 mb2 p1 p2 h1 h2 hs
    have h1n : mb1 ≠ id := by intro h; rw [h, hidPk] at h1; cases h1
    have h2n : mb2 ≠ id := by intro h; rw [h, hidPk] at h2; cases h2
    exact hM.uniq mb1 mb2 p1 p2 (by simpa [hpk mb1 h1n] using h1) (by simpa [hpk mb2 h2n] using h2) hs
  · intro mb
    by_cases hmb : mb = id
    · rw [hmb, hidPk]
      simp
    · simpa [hpk mb hmb] using hM.once mb

/-- Drop the head of one parked queue and leave that sender's phase. The tail stays. -/
theorem mail_drop (w0 w : World) (id : InstId) (p : Parked) (ps : List Parked) (hM : MailInv w0)
    (hfree : notParked (w0.st id).phase) (hqueue : (w0.st id).parked = p :: ps)
    (hidPh : notParked (w.st id).phase) (hidPk : (w.st id).parked = ps)
    (hpk : ∀ i, i ≠ id → (w.st i).parked = (w0.st i).parked)
    (hresume : notParked (w.st p.sender).phase)
    (hother : ∀ i, i ≠ id → i ≠ p.sender → (w.st i).phase = (w0.st i).phase) : MailInv w := by
  have hnq := not_queued w0 id hM hfree
  have hhead : p ∈ (w0.st id).parked := by rw [hqueue]; exact List.mem_cons_self
  have hsnd : p.sender ≠ id := hnq id p hhead
  have hnodup : p ∉ ps := by
    have hnd := hM.once id
    rw [hqueue, List.nodup_cons] at hnd
    exact hnd.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb q hq
    by_cases hmb : mb = id
    · rw [hmb, hidPk] at hq
      have hq0 : q ∈ (w0.st id).parked := by rw [hqueue]; exact List.mem_cons_of_mem _ hq
      obtain ⟨k, hk⟩ := hM.fwd id q hq0
      have hne : q.sender ≠ p.sender := by
        intro heq
        have hqeq := (hM.uniq id id q p hq0 hhead heq).2
        rw [hqeq] at hq
        exact hnodup hq
      rw [hmb, hother q.sender (hnq id q hq0) hne]
      exact ⟨k, hk⟩
    · have hq0 : q ∈ (w0.st mb).parked := by simpa [hpk mb hmb] using hq
      obtain ⟨k, hk⟩ := hM.fwd mb q hq0
      have hwho : q.sender ≠ p.sender := by
        intro heq
        exact hmb (hM.uniq id mb p q hhead hq0 heq.symm).1.symm
      rw [hother q.sender (hnq mb q hq0) hwho]
      exact ⟨k, hk⟩
  · intro sid dst c k hk
    have hsid : sid ≠ id := by
      intro h
      rw [h] at hk
      simp [notParked, hk] at hidPh
    by_cases hwho : sid = p.sender
    · rw [hwho] at hk
      simp [notParked, hk] at hresume
    · have hk0 : (w0.st sid).phase = .parked dst c k := by
        rw [← hother sid hsid hwho]
        exact hk
      obtain ⟨q, hq, hsender, hc⟩ := hM.bwd sid dst c k hk0
      by_cases hd : dst = id
      · have hqlist : q ∈ p :: ps := by simpa [hd, hqueue] using hq
        rcases List.mem_cons.mp hqlist with rfl | htail
        · exact False.elim (hwho hsender.symm)
        · exact ⟨q, by simpa [hd, hidPk] using htail, hsender, hc⟩
      · exact ⟨q, by simpa [hpk dst hd] using hq, hsender, hc⟩
  · intro mb1 mb2 q1 q2 h1 h2 hs
    have old : ∀ {mb q}, q ∈ (w.st mb).parked → q ∈ (w0.st mb).parked := by
      intro mb q hq
      by_cases hmb : mb = id
      · rw [hmb] at hq ⊢
        rw [hidPk] at hq
        rw [hqueue]
        exact List.mem_cons_of_mem _ hq
      · simpa [hpk mb hmb] using hq
    exact hM.uniq mb1 mb2 q1 q2 (old h1) (old h2) hs
  · intro mb
    by_cases hmb : mb = id
    · have hnd := hM.once id
      rw [hqueue, List.nodup_cons] at hnd
      simpa [hmb, hidPk] using hnd.2
    · simpa [hpk mb hmb] using hM.once mb

end Deadlock
