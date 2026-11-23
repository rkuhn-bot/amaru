/-
Parent, generation, tombstone, and mailbox facts every reachable world has.
`occ_head` reads them off the world it steps. They are not extra hypotheses of
a headline.

Three facts are carried only so the seal and the admit stay inside the six:
`plainParked` (an admit copies a parked message into the box), `oneLive`
(a seal's tombstone meets every generation of that key), and `tombOnParent`
(a tombstone sits on the dead sender's parent, so a respawn looks at one lane).
-/

import Deadlock.Tomb

set_option autoImplicit false

namespace Deadlock

theorem life_dead_ne_alive (h : Life.dead = Life.alive) : False := by
  cases h

theorem life_dead_ne_absent (h : Life.dead = Life.absent) : False := by
  cases h

theorem life_was_alive {old new : Life} (h : new = old ∨ new = .dead) (ha : new = .alive) :
    old = .alive := by
  cases h with
  | inl heq => exact heq.symm.trans ha
  | inr hd =>
    exact False.elim (life_dead_ne_alive (hd.symm.trans ha))

/-- A roster actor was wired by the supervisor its template names, a root key
holds one generation, a live key has no queued tombstone, a roster actor is
not absent, bulk mail is not a tombstone, and a parent is not itself. -/
structure BirthInv (D : Description) (w : World) : Prop where
  parented : Parented D w
  singleGen : SingleGen D w
  noTombLive : NoTombWhileLive w
  present : Present w
  plainBox : PlainBox w
  noSelf : NoSelfParent w
  /-- Workaround `plainParked`: an admit moves a parked message into the box,
  so the box stays plain only when parked mail is plain too. -/
  plainParked : ∀ host p, p ∈ (w.st host).parked → p.msg.tombstone = false
  /-- Workaround `oneLive`: sealing one generation queues a tombstone for that
  name and key. A second live generation would be looking at it. -/
  oneLive : ∀ (n : String) (k g1 g2 : Nat),
    (w.st (InstId.peer n k g1)).life = .alive →
    (w.st (InstId.peer n k g2)).life = .alive → g1 = g2
  /-- Workaround `tombOnParent`: a tombstone is offered to the dead sender's
  recorded parent and is not moved. A respawn reads that one lane. -/
  tombOnParent : ∀ host m, m ∈ (w.st host).prio → m.tombstone = true →
    match m.sender with
    | .peer n k g =>
        InstId.peer n k g ∈ w.roster ∧
        (w.st (InstId.peer n k g)).parent = some host ∧
        (w.st (InstId.peer n k g)).life = .dead
    | .core _ => True
  /-- Workaround `ixPast`: an unsupervised lone root takes its key from `nextIx`,
  so a key already on the roster sits strictly below the counter. -/
  ixPast : ∀ (n : String) (k g : Nat), InstId.peer n k g ∈ w.roster →
    ∀ t, templateOf D n = some t → t.supervisor = none → t.subtree = "" →
      k < w.nextIx n
  /-- Workaround `keyPast`: a nonempty subtree takes its key from `nextKey`,
  so a key already on the roster sits strictly below that counter. -/
  keyPast : ∀ (n : String) (k g : Nat), InstId.peer n k g ∈ w.roster →
    ∀ t, templateOf D n = some t → t.subtree ≠ "" →
      k < w.nextKey (templateSubtree D n)

/-- Where a priority message in the next world came from. -/
inductive PrioFrom (w : World) (host : InstId) (m : Msg) : Prop where
  | old : m ∈ (w.st host).prio → PrioFrom w host m
  | plain : m.tombstone = false → PrioFrom w host m
  | tomb (n : String) (k g : Nat) :
      m.sender = InstId.peer n k g →
      m.tombstone = true →
      InstId.peer n k g ∈ w.roster →
      (w.st (InstId.peer n k g)).parent = some host →
      (w.st (InstId.peer n k g)).life = .dead →
      (∀ g', (w.st (InstId.peer n k g')).life ≠ .alive) →
      PrioFrom w host m
  | coreTomb (n : String) :
      m.sender = InstId.core n →
      m.tombstone = true →
      PrioFrom w host m

theorem birth_extend (D : Description) (w w' : World) (h : BirthInv D w)
    (hr : w'.roster = w.roster)
    (hix : ∀ n, w'.nextIx n = w.nextIx n)
    (hkey : ∀ s, w'.nextKey s = w.nextKey s)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life ∨ (w'.st i).life = .dead)
    (hbox : ∀ host m, m ∈ (w'.st host).box → m.tombstone = false)
    (hpark : ∀ host p, p ∈ (w'.st host).parked → p.msg.tombstone = false)
    (hprio : ∀ host m, m ∈ (w'.st host).prio → PrioFrom w host m) :
    BirthInv D w' := by
  refine ⟨?parented, ?single, ?tomb, ?present, ?box, ?self, ?park, ?live, ?onParent, ?ix, ?key⟩
  · intro id t hid ht
    have hid0 : id ∈ w.roster := by simpa [hr] using hid
    have hold := h.parented id t hid0 ht
    cases hsup : t.supervisor with
    | none =>
      simp only [hsup] at hold ⊢
      rw [hpar id]
      exact hold
    | some name =>
      simp only [hsup] at hold ⊢
      rcases hold with ⟨p, hparent, hname, hkeym⟩
      refine ⟨p, ?_, hname, hkeym⟩
      rw [hpar id]
      exact hparent
  · intro name k g1 g2 t ht hroot h1 h2
    exact h.singleGen name k g1 g2 t ht hroot (by simpa [hr] using h1) (by simpa [hr] using h2)
  · intro name k g host m hlivePeer hliveHost hm htomb
    cases hprio host m hm with
    | old hmem =>
      exact h.noTombLive name k g host m
        (life_was_alive (hlife _) hlivePeer) (life_was_alive (hlife _) hliveHost) hmem htomb
    | plain hplain =>
      rw [hplain] at htomb
      cases htomb
    | tomb n0 k0 g0 hs _ _ _ _ hclear =>
      rw [hs]
      intro hn hk
      subst hn
      subst hk
      exact hclear g (life_was_alive (hlife _) hlivePeer)
    | coreTomb n hs _ =>
      simp [hs]
  · intro id hid
    have hid0 : id ∈ w.roster := by simpa [hr] using hid
    cases hlife id with
    | inl heq =>
      rw [heq]
      exact h.present id hid0
    | inr hd =>
      rw [hd]
      intro hbad
      exact life_dead_ne_absent hbad
  · exact hbox
  · intro id
    rw [hpar id]
    exact h.noSelf id
  · exact hpark
  · intro n k g1 g2 h1 h2
    exact h.oneLive n k g1 g2 (life_was_alive (hlife _) h1) (life_was_alive (hlife _) h2)
  · intro host m hm htomb
    cases hprio host m hm with
    | old hmem =>
      have hold := h.tombOnParent host m hmem htomb
      cases hs : m.sender with
      | core _ =>
        simp [hs]
      | peer n k g =>
        simp only [hs] at hold
        rcases hold with ⟨hmemR, hp, hd⟩
        refine ⟨?_, ?_, ?_⟩
        · simpa [hr] using hmemR
        · rw [hpar]
          exact hp
        · cases hlife (InstId.peer n k g) with
          | inl heq =>
            rw [heq]
            exact hd
          | inr hdead => exact hdead
    | plain hplain =>
      rw [hplain] at htomb
      cases htomb
    | tomb n k g hs ht hmemR hp hd _ =>
      have ht' : m.tombstone = true := ht
      clear ht
      rw [hs]
      refine ⟨?_, ?_, ?_⟩
      · simpa [hr] using hmemR
      · rw [hpar]
        exact hp
      · cases hlife (InstId.peer n k g) with
        | inl heq =>
          rw [heq]
          exact hd
        | inr hdead => exact hdead
    | coreTomb n hs _ =>
      simp [hs]
  · intro n k g hmem t ht hsup hsub
    have hmem0 : InstId.peer n k g ∈ w.roster := by simpa [hr] using hmem
    simpa [hix n] using h.ixPast n k g hmem0 t ht hsup hsub
  · intro n k g hmem t ht hne
    have hmem0 : InstId.peer n k g ∈ w.roster := by simpa [hr] using hmem
    simpa [hkey (templateSubtree D n)] using h.keyPast n k g hmem0 t ht hne

theorem birth_quiet (D : Description) (w w' : World) (h : BirthInv D w)
    (hr : w'.roster = w.roster) (hix : ∀ n, w'.nextIx n = w.nextIx n)
    (hkey : ∀ s, w'.nextKey s = w.nextKey s)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life ∨ (w'.st i).life = .dead)
    (hbox : ∀ host m, m ∈ (w'.st host).box → m.tombstone = false)
    (hpark : ∀ host p, p ∈ (w'.st host).parked → p.msg.tombstone = false)
    (hprio : ∀ host m, m ∈ (w'.st host).prio →
      m ∈ (w.st host).prio ∨ m.tombstone = false) :
    BirthInv D w' := by
  refine birth_extend D w w' h hr hix hkey hpar hlife hbox hpark ?_
  intro host m hm
  rcases hprio host m hm with hmem | hplain
  · exact PrioFrom.old hmem
  · exact PrioFrom.plain hplain

theorem crashActor_parent (a : Actor) : (crashActor a).parent = a.parent := by
  unfold crashActor
  split <;> simp

theorem crashActor_box (a : Actor) : (crashActor a).box = a.box := by
  unfold crashActor
  split <;> simp

theorem crashActor_prio (a : Actor) : (crashActor a).prio = a.prio := by
  unfold crashActor
  split <;> simp

theorem crashActor_parked (a : Actor) : (crashActor a).parked = a.parked := by
  unfold crashActor
  split <;> simp

theorem crashActor_life (a : Actor) :
    (crashActor a).life = a.life ∨ (crashActor a).life = .dead := by
  unfold crashActor
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem birth_crash (D : Description) (w : World) (h : BirthInv D w) :
    BirthInv D (crashWorld w) := by
  refine birth_quiet D w (crashWorld w) h rfl (fun _ => rfl) (fun _ => rfl) ?par ?life ?box ?park ?prio
  · intro i
    by_cases hmem : i ∈ w.roster
    · simp [crashWorld, hmem, crashActor_parent]
    · simp [crashWorld, hmem]
  · intro i
    by_cases hmem : i ∈ w.roster
    · simp [crashWorld, hmem]
      exact crashActor_life (w.st i)
    · simp [crashWorld, hmem]
  · intro host m hm
    by_cases hmem : host ∈ w.roster
    · simp [crashWorld, hmem, crashActor_box] at hm
      exact h.plainBox host m hm
    · simp [crashWorld, hmem] at hm
      exact h.plainBox host m hm
  · intro host p hp
    by_cases hmem : host ∈ w.roster
    · simp [crashWorld, hmem, crashActor_parked] at hp
      exact h.plainParked host p hp
    · simp [crashWorld, hmem] at hp
      exact h.plainParked host p hp
  · intro host m hm
    by_cases hmem : host ∈ w.roster
    · simp [crashWorld, hmem, crashActor_prio] at hm
      exact Or.inl hm
    · simp [crashWorld, hmem] at hm
      exact Or.inl hm

theorem birth_set (D : Description) (w : World) (id : InstId) (a : Actor) (h : BirthInv D w)
    (hpar : a.parent = (w.st id).parent)
    (hlife : a.life = (w.st id).life ∨ a.life = .dead)
    (hbox : ∀ m, m ∈ a.box → m.tombstone = false)
    (hpark : ∀ p, p ∈ a.parked → p.msg.tombstone = false)
    (hprio : ∀ m, m ∈ a.prio → m ∈ (w.st id).prio ∨ m.tombstone = false) :
    BirthInv D (setActor w id a) := by
  refine birth_quiet D w (setActor w id a) h rfl (fun _ => rfl) (fun _ => rfl) ?par ?life ?box ?park ?prio
  · intro i
    by_cases hi : i = id
    · simp [setActor, hi, hpar]
    · simp [setActor, hi]
  · intro i
    by_cases hi : i = id
    · simp [setActor, hi]
      exact hlife
    · simp [setActor, hi]
  · intro host m hm
    by_cases hi : host = id
    · simp [setActor, hi] at hm
      exact hbox m hm
    · simp [setActor, hi] at hm
      exact h.plainBox host m hm
  · intro host p hp
    by_cases hi : host = id
    · simp [setActor, hi] at hp
      exact hpark p hp
    · simp [setActor, hi] at hp
      exact h.plainParked host p hp
  · intro host m hm
    by_cases hi : host = id
    · subst hi
      simp only [setActor_self] at hm
      exact hprio m hm
    · simp [setActor, hi] at hm
      exact Or.inl hm

theorem birth_keep (D : Description) (w : World) (id : InstId) (a : Actor) (h : BirthInv D w)
    (hpar : a.parent = (w.st id).parent) (hlife : a.life = (w.st id).life)
    (hbox : a.box = (w.st id).box) (hprio : a.prio = (w.st id).prio)
    (hpark : a.parked = (w.st id).parked) :
    BirthInv D (setActor w id a) := by
  refine birth_set D w id a h hpar (Or.inl hlife) ?box ?park ?prio
  · intro m hm
    rw [hbox] at hm
    exact h.plainBox id m hm
  · intro p hp
    rw [hpark] at hp
    exact h.plainParked id p hp
  · intro m hm
    exact Or.inl (by rwa [hprio] at hm)

theorem proceed_lineage (a : Actor) (k : Cont) :
    (proceed a k).life = a.life ∧ (proceed a k).parent = a.parent ∧
      (proceed a k).box = a.box ∧ (proceed a k).prio = a.prio ∧
      (proceed a k).parked = a.parked := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem finish_lineage (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).life = a.life ∧ (finishCall a k r).parent = a.parent ∧
      (finishCall a k r).box = a.box ∧ (finishCall a k r).prio = a.prio ∧
      (finishCall a k r).parked = a.parked := by
  rcases proceed_lineage a (selectCall k r) with ⟨hl, hp, hb, hpr, hk⟩
  simp [finishCall, hl, hp, hb, hpr, hk]

theorem issue_lineage (a : Actor) :
    (issueCall a).life = a.life ∧ (issueCall a).parent = a.parent ∧
      (issueCall a).box = a.box ∧ (issueCall a).prio = a.prio ∧
      (issueCall a).parked = a.parked := by
  simp [issueCall]

theorem bump_lineage (a : Actor) (dst : String) (d : Int) :
    (bumpToken a dst d).life = a.life ∧ (bumpToken a dst d).parent = a.parent ∧
      (bumpToken a dst d).box = a.box ∧ (bumpToken a dst d).prio = a.prio ∧
      (bumpToken a dst d).parked = a.parked := by
  simp [bumpToken]

theorem charge_lineage (a : Actor) (dst : String) :
    (chargeSender a dst).life = a.life ∧ (chargeSender a dst).parent = a.parent ∧
      (chargeSender a dst).box = a.box ∧ (chargeSender a dst).prio = a.prio ∧
      (chargeSender a dst).parked = a.parked := by
  simpa [chargeSender] using bump_lineage a dst (.negSucc 0)

theorem add_lineage (a : Actor) (name : String) (n : Nat) :
    (addTokens a name n).life = a.life ∧ (addTokens a name n).parent = a.parent ∧
      (addTokens a name n).box = a.box ∧ (addTokens a name n).prio = a.prio ∧
      (addTokens a name n).parked = a.parked := by
  simp [addTokens]

theorem resume_lineage (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).life = a.life ∧ (resumeSender a isCall dst).parent = a.parent ∧
      (resumeSender a isCall dst).box = a.box ∧ (resumeSender a isCall dst).prio = a.prio ∧
      (resumeSender a isCall dst).parked = a.parked := by
  cases hph : a.phase with
  | parked _ _ k =>
    simp only [resumeSender, hph]
    split
    · simp
    · simpa using proceed_lineage a k
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem detachMsg_tomb (caller : InstId) (m : Msg) :
    (detachMsg caller m).tombstone = m.tombstone := by
  unfold detachMsg
  split <;> simp

theorem birth_note (D : Description) (w : World) (sender : InstId) (dst : String)
    (h : BirthInv D w) : BirthInv D (noteStale w sender dst) := by
  refine birth_quiet D w (noteStale w sender dst) h rfl (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => Or.inl rfl) ?box ?park ?prio
  · intro host m hm
    exact h.plainBox host m hm
  · intro host p hp
    exact h.plainParked host p hp
  · intro host m hm
    exact Or.inl hm

theorem birth_cells (D : Description) (w : World) (id : InstId) (h : BirthInv D w) :
    BirthInv D (readCells D w id) := by
  refine birth_quiet D w (readCells D w id) h (cellsRoster D w id)
    (fun n => readCells_nextIx D w id n) (fun s => readCells_nextKey D w id s) ?par ?life ?box ?park ?prio
  · intro i
    exact congrArg Actor.parent (cellsSt D w id i)
  · intro i
    exact Or.inl (congrArg Actor.life (cellsSt D w id i))
  · intro host m hm
    rw [show (readCells D w id).st host = w.st host from cellsSt D w id host] at hm
    exact h.plainBox host m hm
  · intro host p hp
    rw [show (readCells D w id).st host = w.st host from cellsSt D w id host] at hp
    exact h.plainParked host p hp
  · intro host m hm
    rw [show (readCells D w id).st host = w.st host from cellsSt D w id host] at hm
    exact Or.inl hm

theorem birth_credit (D : Description) (w : World) (name : String) (s : InstId)
    (h : BirthInv D w) : BirthInv D (creditSender w name s) := by
  rcases bump_lineage (w.st s) name (.ofNat 1) with ⟨hl, hp, hb, hpr, hk⟩
  simpa [creditSender] using birth_keep D w s (bumpToken (w.st s) name (.ofNat 1)) h hp hl hb hpr hk

theorem birth_live (D : Description) (w : World) (name : String) (s : InstId)
    (h : BirthInv D w) : BirthInv D (creditLive w name s) := by
  simpa [creditLive] using birth_credit D w name (budgetHolder w s) h

theorem birth_refundMsgs (D : Description) (w : World) (name : String) (ms : List Msg)
    (h : BirthInv D w) : BirthInv D (refundMsgs w name ms) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using h
  | cons m ms ih =>
    have hfold : refundMsgs w name (m :: ms) = refundMsgs (creditLive w name m.sender) name ms := by
      simp [refundMsgs, List.foldl_cons]
    exact hfold ▸ ih _ (birth_live D w name m.sender h)

theorem birth_refundParked (D : Description) (w : World) (name : String) (ps : List Parked)
    (h : BirthInv D w) : BirthInv D (refundParked w name ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using h
  | cons p ps ih =>
    have hfold : refundParked w name (p :: ps) =
        refundParked (creditLive w name p.msg.sender) name ps := by
      simp [refundParked, List.foldl_cons]
    exact hfold ▸ ih _ (birth_live D w name p.msg.sender h)

theorem plain_mem_filter {p : Parked → Bool} {ps : List Parked}
    (h : ∀ q, q ∈ ps → q.msg.tombstone = false) :
    ∀ q, q ∈ ps.filter p → q.msg.tombstone = false := by
  intro q hq
  exact h q (List.mem_filter.mp hq).1

theorem birth_credits (D : Description) (w : World) (name : String) (caller : InstId)
    (ps : List Parked) (h : BirthInv D w) :
    BirthInv D (ps.foldl (fun w _ => creditSender w name caller) w) := by
  induction ps generalizing w with
  | nil => simpa using h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih _ (birth_credit D w name caller h)

/-- One host of `releaseOutbound`. A host that is the dead actor, or that holds
nothing of it, is skipped. -/
theorem birth_outbound_step (D : Description) (w : World) (dead host : InstId)
    (h : BirthInv D w) :
    BirthInv D (if host == dead then w else
      let dropped := (w.st host).parked.filter fun p => p.sender == dead
      if dropped.isEmpty then w else
        let w := setActor w host
          { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
        setActor w dead (addTokens (w.st dead) (tname host) dropped.length)) := by
  by_cases hsame : (host == dead) = true
  · simp [hsame]
    exact h
  · have hf : (host == dead) = false := by
      cases hbit : host == dead <;> simp_all
    simp only [hf, ite_false]
    let dropped := (w.st host).parked.filter fun p => p.sender == dead
    by_cases hempty : dropped.isEmpty = true
    · simp [dropped, hempty]
      exact h
    · have hne : dropped.isEmpty = false := by
        cases hbit : dropped.isEmpty <;> simp_all
      simp only [hne, ite_false, dropped]
      have hhost : host ≠ dead := by
        intro heq
        have : (host == dead) = true := by simpa [heq] using (beq_self_eq_true host)
        rw [this] at hf
        cases hf
      have hfilt : BirthInv D (setActor w host
          { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }) := by
        refine birth_set D w host _ h rfl (Or.inl rfl) ?box ?park ?prio
        · intro m hm
          exact h.plainBox host m hm
        · intro p hp
          exact plain_mem_filter (h.plainParked host) p hp
        · intro m hm
          exact Or.inl hm
      let w1 := setActor w host
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      rcases add_lineage (w1.st dead) (tname host) dropped.length with ⟨hl, hp, hb, hpr, hk⟩
      simpa [w1] using birth_keep D w1 dead _ hfilt hp hl hb hpr hk

theorem birth_outbound (D : Description) (w : World) (dead : InstId) (h : BirthInv D w) :
    BirthInv D (releaseOutbound w dead) := by
  unfold releaseOutbound
  suffices ∀ (ids : List InstId) (w0 : World), BirthInv D w0 →
      BirthInv D (ids.foldl (fun acc host =>
        if host == dead then acc else
          let dropped := (acc.st host).parked.filter fun p => p.sender == dead
          if dropped.isEmpty then acc else
            let acc := setActor acc host
              { (acc.st host) with parked := (acc.st host).parked.filter fun p => p.sender != dead }
            setActor acc dead (addTokens (acc.st dead) (tname host) dropped.length)) w0) by
    exact this w.roster w h
  intro ids
  induction ids with
  | nil => intro w0 h0; simpa using h0
  | cons host hosts ih =>
    intro w0 h0
    simp only [List.foldl_cons]
    exact ih _ (birth_outbound_step D w0 dead host h0)

theorem birth_die (D : Description) (w : World) (id : InstId) (h : BirthInv D w) :
    BirthInv D (setActor w id
      { (w.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }) := by
  refine birth_set D w id _ h rfl (Or.inr rfl) ?box ?park ?prio
  · intro m hm
    simp at hm
  · intro p hp
    simp at hp
  · intro m hm
    simp at hm

theorem birth_release_one (D : Description) (w : World) (id : InstId) (p : Parked)
    (h : BirthInv D w) :
    BirthInv D (if p.isCall = true ∨ p.sender = id then w else
      setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
  by_cases hskip : p.isCall = true ∨ p.sender = id
  · simp [hskip]
    exact h
  · simp [hskip]
    rcases resume_lineage (w.st p.sender) false id with ⟨hl, hp, hb, hpr, hk⟩
    exact birth_keep D w p.sender _ h hp hl hb hpr hk

theorem birth_releaseParked (D : Description) (w : World) (id : InstId) (ps : List Parked)
    (h : BirthInv D w) : BirthInv D (releaseParked w id ps) := by
  unfold releaseParked
  induction ps generalizing w with
  | nil => simpa using h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hstep : BirthInv D (if p.isCall || p.sender = id then w else
        setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
      simpa using birth_release_one D w id p h
    exact ih _ hstep

theorem birth_release (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : BirthInv D w) : BirthInv D (releaseWorld D w id a) := by
  unfold releaseWorld
  dsimp only
  have h1 := birth_cells D w id h
  have h2 := birth_refundMsgs D (readCells D w id) (tname id) a.box h1
  have h3 := birth_refundParked D _ (tname id) a.parked h2
  have h4 := birth_outbound D _ id h3
  have h5 := birth_die D _ id h4
  exact birth_releaseParked D _ id a.parked h5

/-- Releasing the live generation of a key leaves no generation of that key alive. -/
theorem release_slot (D : Description) (w : World) (n : String) (k g : Nat) (h : BirthInv D w)
    (hl : (w.st (InstId.peer n k g)).life = .alive) (g' : Nat) :
    ((releaseWorld D w (InstId.peer n k g) (w.st (InstId.peer n k g))).st
      (InstId.peer n k g')).life ≠ .alive := by
  intro ha
  by_cases heq : g' = g
  · subst heq
    simp [releaseWorld_self_dead] at ha
  · have hne : InstId.peer n k g' ≠ InstId.peer n k g := by
      intro hsame
      cases hsame
      exact heq rfl
    have hold := releaseWorld_other_life D w (InstId.peer n k g)
      (w.st (InstId.peer n k g)) (InstId.peer n k g') hne
    have halive0 : (w.st (InstId.peer n k g')).life = .alive := by
      rw [← hold]
      exact ha
    exact heq (h.oneLive n k g' g halive0 hl)

theorem upsert_from (prio : List Msg) (m x : Msg) (hm : m.tombstone = false)
    (hx : x ∈ upsertPrio prio m) : x ∈ prio ∨ x.tombstone = false := by
  unfold upsertPrio at hx
  split at hx
  · exact Or.inl hx
  · rcases List.mem_append.mp hx with h | h
    · exact Or.inl h
    · simp at h
      rw [h]
      exact Or.inr hm

theorem plain_append {box : List Msg} {m : Msg}
    (h : ∀ x, x ∈ box → x.tombstone = false) (hm : m.tombstone = false) :
    ∀ x, x ∈ box ++ [m] → x.tombstone = false := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · simp at hx
    rw [hx]
    exact hm

theorem plain_tail {m : Msg} {ms : List Msg}
    (h : ∀ x, x ∈ m :: ms → x.tombstone = false) :
    ∀ x, x ∈ ms → x.tombstone = false := by
  intro x hx
  exact h x (List.mem_cons_of_mem _ hx)

theorem park_tail {p : Parked} {ps : List Parked}
    (h : ∀ q, q ∈ p :: ps → q.msg.tombstone = false) :
    ∀ q, q ∈ ps → q.msg.tombstone = false := by
  intro q hq
  exact h q (List.mem_cons_of_mem _ hq)

theorem birth_snoc (D : Description) (w : World) (host : InstId) (msg : Msg)
    (h : BirthInv D w) (hfrom : PrioFrom w host msg) :
    BirthInv D (setActor w host
      { (w.st host) with prio := (w.st host).prio ++ [msg], nextMid := (w.st host).nextMid + 1 }) := by
  refine birth_extend D w _ h rfl (fun _ => rfl) (fun _ => rfl) ?par ?life ?box ?park ?prio
  · intro i
    by_cases hi : i = host
    · simp [setActor, hi]
    · simp [setActor, hi]
  · intro i
    by_cases hi : i = host
    · simp [setActor, hi]
    · simp [setActor, hi]
  · intro i m hm
    by_cases hi : i = host
    · simp [setActor, hi] at hm
      exact h.plainBox host m hm
    · simp [setActor, hi] at hm
      exact h.plainBox i m hm
  · intro i p hp
    by_cases hi : i = host
    · simp [setActor, hi] at hp
      exact h.plainParked host p hp
    · simp [setActor, hi] at hp
      exact h.plainParked i p hp
  · intro i m hm
    by_cases hi : i = host
    · rw [hi] at hm ⊢
      have hm' : m ∈ (w.st host).prio ++ [msg] := by
        simpa [setActor_self] using hm
      rcases List.mem_append.mp hm' with hmem | hnew
      · exact PrioFrom.old hmem
      · simp at hnew
        rw [hnew]
        exact hfrom
    · simp [setActor, hi] at hm
      exact PrioFrom.old hm

theorem birth_offer (D : Description) (w : World) (host : InstId) (msg : Msg)
    (h : BirthInv D w) (hfrom : PrioFrom w host msg) :
    BirthInv D (offerPrio D w host msg) := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp [hfull]
    exact birth_crash D w h
  · have hf : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = false := by
      cases hbit : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) <;> simp_all
    simp [hf]
    exact birth_snoc D w host msg h hfrom

theorem tomb_msg_sender (D : Description) (parent : Actor) (child : InstId) :
    (tombstoneMsg D parent child).sender = child ∧
      (tombstoneMsg D parent child).tombstone = true := by
  simp [tombstoneMsg]

/-- No generation of a peer's key is alive. A core has no key. -/
def slotClear (w : World) (id : InstId) : Prop :=
  match id with
  | .peer n k _ => ∀ g', (w.st (InstId.peer n k g')).life ≠ .alive
  | .core _ => True

theorem birth_enqueue (D : Description) (w : World) (child : InstId) (h : BirthInv D w)
    (hdead : (w.st child).life = .dead) (hmem : child ∈ w.roster)
    (hslot : slotClear w child) :
    BirthInv D (enqueueTombstone D w child) := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none =>
    simp [hpar]
    exact h
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp [hlive]
      exact h
    · have hliveF : ((w.st parent).life != .alive) = false := by
        cases hbit : (w.st parent).life != .alive <;> simp_all
      simp only [hliveF, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp [hlab]
        exact birth_crash D w h
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hbit : (tombstoneMsg D (w.st parent) child).label == "" <;> simp_all
        simp only [hlabF, ite_false]
        have ⟨hsend, htomb⟩ := tomb_msg_sender D (w.st parent) child
        have hfrom : PrioFrom w parent (tombstoneMsg D (w.st parent) child) := by
          cases child with
          | core n =>
            exact PrioFrom.coreTomb n (by simpa using hsend) htomb
          | peer n k g =>
            exact PrioFrom.tomb n k g (by simpa using hsend) htomb hmem hpar hdead
              (by simpa [slotClear] using hslot)
        exact birth_offer D w parent _ h hfrom

/-- Releasing `id` leaves no live generation of its key. A core has no key. -/
theorem release_slot_of (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : BirthInv D w) (hl : (w.st id).life = .alive) :
    slotClear (releaseWorld D w id a) id := by
  unfold slotClear
  cases id with
  | core _ => trivial
  | peer n k g =>
    intro g' ha
    by_cases heq : g' = g
    · subst heq
      simp [releaseWorld_self_dead] at ha
    · have hne : InstId.peer n k g' ≠ InstId.peer n k g := by
        intro hsame
        cases hsame
        exact heq rfl
      have hold := releaseWorld_other_life D w (InstId.peer n k g) a (InstId.peer n k g') hne
      have halive0 : (w.st (InstId.peer n k g')).life = .alive := by
        rw [← hold]
        exact ha
      exact heq (h.oneLive n k g' g halive0 hl)

theorem birth_seal (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : BirthInv D w) (hmem : id ∈ w.roster) (hlive : (w.st id).life = .alive) :
    BirthInv D (sealActor D w id a) := by
  unfold sealActor
  have hrel := birth_release D w id a h
  have hdead := releaseWorld_self_dead D w id a
  have hmem' : id ∈ (releaseWorld D w id a).roster := by
    simpa [release_roster] using hmem
  exact birth_enqueue D (releaseWorld D w id a) id hrel hdead hmem'
    (release_slot_of D w id a h hlive)

theorem birth_fold_cells (D : Description) (ids : List InstId) (w : World) (h : BirthInv D w) :
    BirthInv D (ids.foldl (fun acc id => readCells D acc id) w) := by
  induction ids generalizing w with
  | nil => exact h
  | cons id ids ih =>
    simp only [List.foldl_cons]
    exact ih (readCells D w id) (birth_cells D w id h)

/-- A multiplicity-one template that passes the subtree check names no supervisor
and belongs to no subtree. `subtreeEntry_not_one` rejects a core inside a subtree,
and an empty subtree rejects a named supervisor. -/
theorem one_rootless (D : Description) (hG : GraphOk D) (t : Template)
    (ht : t ∈ D.templates) (hone : t.multiplicity = .one) :
    t.supervisor = none ∧ t.subtree = "" := by
  have hmap : D.templates.filterMap (subtreeEntry D) = [] :=
    (List.append_eq_nil_iff.mp (by simpa only [subtreeFails_entry] using hG.subtrees)).1
  have hent := filterMap_none (subtreeEntry D) D.templates hmap t ht
  by_cases hsub : t.subtree = ""
  · cases hsup : t.supervisor with
    | none => exact ⟨rfl, hsub⟩
    | some _ =>
      have hb : (t.subtree == "") = true := by simpa [beq_iff_eq] using hsub
      simp [subtreeEntry, hb, hsup] at hent
  · exact False.elim ((subtreeEntry_not_one D t hsub hone) hent)

theorem birth_fold_dedup {α : Type} [DecidableEq α] (acc xs : List α) :
    (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length
      ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases hx : acc.elem x
    · simp only [hx, List.length_cons]
      have ih' := ih (acc ++ [x])
      simp [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_left_comm] at ih' ⊢
      rw [show acc.length + (1 + xs.length) = xs.length + (acc.length + 1) from by omega] at ih'
      exact ih'
    · simp only [hx, List.length_cons]
      exact Nat.le_trans (ih acc) (Nat.add_le_add_left (Nat.le_succ xs.length) acc.length)

theorem birth_name_len (D : Description) (h : nameFails D = []) :
    (dedup (D.templates.map (·.name))).length = (D.templates.map (·.name)).length := by
  unfold nameFails at h
  by_cases hq : (D.templates.map (·.name)).length == (dedup (D.templates.map (·.name))).length
  · simp only [hq, ite_true] at h
    exact ((beq_iff_eq).mp hq).symm
  · simp only [hq, ite_false] at h
    simp at h

theorem birth_nodup_snoc {α : Type} {l : List α} {a : α} (hl : l.Nodup) (ha : a ∉ l) :
    (l ++ [a]).Nodup := by
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

theorem birth_accum {α : Type} [DecidableEq α] (acc xs : List α) (hacc : acc.Nodup)
    (h : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length =
      acc.length + xs.length) : xs.Nodup ∧ ∀ x ∈ xs, x ∉ acc := by
  induction xs generalizing acc with
  | nil =>
    simp at h
    exact ⟨List.nodup_nil, fun _ hmem => by cases hmem⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons] at h
    cases hx : acc.elem x
    · simp only [hx, Bool.false_eq_true, ite_false] at h
      have hacc' : (acc ++ [x]).Nodup := birth_nodup_snoc hacc (by
        intro hin
        have := List.elem_iff.mpr hin
        rw [hx] at this
        cases this)
      have hlen : (acc ++ [x]).length = acc.length + 1 := by simp [List.length_append]
      have h' : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) (acc ++ [x])).length =
          (acc ++ [x]).length + xs.length := by
        rw [hlen]
        omega
      obtain ⟨hxs, hfresh⟩ := ih (acc ++ [x]) hacc' h'
      refine ⟨?_, ?_⟩
      · refine (List.nodup_cons).mpr ⟨?_, hxs⟩
        intro hin
        exact hfresh x hin (List.mem_append_right _ (List.Mem.head _))
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · intro hin
          have := List.elem_iff.mpr hin
          rw [hx] at this
          cases this
        · intro hin
          exact hfresh y hy (List.mem_append_left _ hin)
    · simp only [hx, ite_true] at h
      have hle := birth_fold_dedup acc xs
      omega

theorem birth_nodup_len {α : Type} [DecidableEq α] (xs : List α) (h : (dedup xs).length = xs.length) :
    xs.Nodup := by
  have h0 : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) ([] : List α)).length =
      ([] : List α).length + xs.length := by simpa [dedup, Nat.zero_add] using h
  exact (birth_accum [] xs List.nodup_nil h0).1

theorem birth_names (D : Description) (hG : GraphOk D) : (D.templates.map (·.name)).Nodup := by
  have h := hG.struct
  simp only [structLines, List.append_eq_nil_iff] at h
  repeat obtain ⟨h, _⟩ := h
  exact birth_nodup_len _ (birth_name_len D h)

theorem birth_find_named (xs : List Template) (t : Template) (ht : t ∈ xs)
    (h : (xs.map (·.name)).Nodup) :
    xs.findSome? (fun u => if u.name == t.name then some u else none) = some t := by
  induction xs with
  | nil => cases ht
  | cons u us ih =>
    have hcons := (List.nodup_cons).mp h
    rw [List.findSome?_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · simp
    · have hdiff : (u.name == t.name) = false := by
        by_cases hn : u.name = t.name
        · exact absurd (by
            have : t.name ∈ us.map (·.name) := List.mem_map.mpr ⟨t, ht, rfl⟩
            simpa [hn] using this) hcons.1
        · cases hbb : u.name == t.name <;> simp_all [beq_iff_eq]
      simp only [hdiff, ite_false]
      exact ih ht hcons.2

theorem birth_core_template (D : Description) (id : InstId) (hG : GraphOk D) (h : id ∈ coreRoster D) :
    ∃ t, templateOf D (tname id) = some t ∧ t.multiplicity = .one ∧ id = InstId.core t.name := by
  rw [coreRoster, List.mem_filterMap] at h
  obtain ⟨t, hmem, hif⟩ := h
  cases hb : t.multiplicity == .one <;> simp [hb] at hif
  cases hif
  have hone : t.multiplicity = .one := by
    cases hm : t.multiplicity with
    | one => rfl
    | perPeer =>
      rw [hm] at hb
      have hfalse : (Multiplicity.perPeer == Multiplicity.one) = false := by decide
      rw [hfalse] at hb
      cases hb
  refine ⟨t, ?_, hone, rfl⟩
  simpa [templateOf, tname] using birth_find_named D.templates t hmem (birth_names D hG)

theorem init_queues (D : Description) (id : InstId) :
    (initActor D id).box = [] ∧ (initActor D id).prio = [] ∧ (initActor D id).parked = [] := by
  cases h : templateOf D (tname id) <;> simp [initActor, h, withTokens, absentActor]

theorem birth_cores (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hros : w.roster = coreRoster I.desc) (_hix : ∀ n, w.nextIx n = 0)
    (_hkey : ∀ s, w.nextKey s = 0)
    (hst : ∀ id, w.st id =
      if w.roster.contains id then initActor I.desc id else absentActor) :
    BirthInv I.desc w := by
  have honly : ∀ id, id ∈ w.roster → ∃ name, id = InstId.core name := by
    intro id hid
    obtain ⟨_, _, _, hidc⟩ := birth_core_template I.desc id hG (by simpa [hros] using hid)
    exact ⟨_, hidc⟩
  refine ⟨?parented, ?single, ?tomb, ?present, ?box, ?self, ?park, ?live, ?onParent, ?ix, ?key⟩
  · intro id t hid ht
    obtain ⟨t0, ht0, hone, hidc⟩ := birth_core_template I.desc id hG (by simpa [hros] using hid)
    have ht' : t = t0 := by
      have hsame : some t = some t0 := by rw [← ht, ht0]
      cases hsame
      rfl
    have ⟨hmem, _⟩ := templateOf_mem I.desc (tname id) t0 ht0
    obtain ⟨hsup, _⟩ := one_rootless I.desc hG t0 hmem hone
    have hpar : (w.st id).parent = none := by
      have hc : w.roster.contains id = true := by simpa [List.elem_iff] using hid
      rw [hst id, hc]
      exact init_actor_parent I.desc id
    simpa [ht', hsup] using hpar
  · intro name k g1 g2 t ht hroot h1 h2
    obtain ⟨_, hidc⟩ := honly _ h1
    cases hidc
  · intro name k g host m _ _ hm _
    have hm' : m ∈ (if w.roster.contains host then initActor I.desc host else absentActor).prio := by
      simpa [hst] using hm
    split at hm'
    · rw [(init_queues I.desc host).2.1] at hm'
      cases hm'
    · simp [absentActor] at hm'
  · intro id hid
    obtain ⟨t, ht, _, _⟩ := birth_core_template I.desc id hG (by simpa [hros] using hid)
    have hc : w.roster.contains id = true := by simpa [List.elem_iff] using hid
    rw [hst id, hc, initActor, ht]
    intro hbad
    cases hbad
  · intro host m hm
    have hm' : m ∈ (if w.roster.contains host then initActor I.desc host else absentActor).box := by
      simpa [hst] using hm
    split at hm'
    · rw [(init_queues I.desc host).1] at hm'
      cases hm'
    · simp [absentActor] at hm'
  · intro id
    have hpar : (w.st id).parent = none := by
      rw [hst id]
      split
      · exact init_actor_parent I.desc id
      · simp [absentActor]
    rw [hpar]
    intro hbad
    cases hbad
  · intro host p hp
    have hp' : p ∈ (if w.roster.contains host then initActor I.desc host else absentActor).parked := by
      simpa [hst] using hp
    split at hp'
    · rw [(init_queues I.desc host).2.2] at hp'
      cases hp'
    · simp [absentActor] at hp'
  · intro n k g1 g2 h1 _
    have hnot : w.roster.contains (InstId.peer n k g1) = false := by
      by_cases hc : w.roster.contains (InstId.peer n k g1) = true
      · have hmem : InstId.peer n k g1 ∈ w.roster := by simpa [List.elem_iff] using hc
        obtain ⟨_, hidc⟩ := honly _ hmem
        cases hidc
      · cases hbb : w.roster.contains (InstId.peer n k g1) <;> simp_all
    rw [hst, hnot, absentActor] at h1
    cases h1
  · intro host m hm htomb
    have hm' : m ∈ (if w.roster.contains host then initActor I.desc host else absentActor).prio := by
      simpa [hst] using hm
    split at hm'
    · rw [(init_queues I.desc host).2.1] at hm'
      cases hm'
    · simp [absentActor] at hm'
  · intro n k g hmem _ _ _ _
    obtain ⟨_, hidc⟩ := honly _ hmem
    cases hidc
  · intro n k g hmem _ _ _
    obtain ⟨_, hidc⟩ := honly _ hmem
    cases hidc

theorem birth_init (I : Impl) (hG : GraphOk I.desc) (N : Nat) : BirthInv I.desc (initWorld I N) := by
  unfold initWorld
  dsimp only
  refine birth_fold_cells I.desc (coreRoster I.desc) _ ?_
  refine birth_cores I hG _ rfl (fun _ => rfl) (fun _ => rfl) ?_
  intro id
  rfl
