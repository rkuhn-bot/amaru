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

theorem birth_keep_line (D : Description) (w : World) (id : InstId) (a : Actor) (h : BirthInv D w)
    (hl : a.life = (w.st id).life ∧ a.parent = (w.st id).parent ∧ a.box = (w.st id).box ∧
      a.prio = (w.st id).prio ∧ a.parked = (w.st id).parked) :
    BirthInv D (setActor w id a) := by
  rcases hl with ⟨hl, hp, hb, hpr, hk⟩
  exact birth_keep D w id a h hp hl hb hpr hk

theorem detach_plain (a : Actor) (caller : InstId)
    (h : ∀ m, m ∈ a.box → m.tombstone = false) :
    ∀ m, m ∈ (detachBox a caller).box → m.tombstone = false := by
  intro m hm
  rw [detachBox] at hm
  obtain ⟨m0, hm0, heq⟩ := List.mem_map.mp hm
  rw [← heq, detachMsg_tomb]
  exact h _ hm0

theorem detach_host_line (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).life = a.life ∧
      (detachReply (detachBox a caller) caller cid).parent = a.parent ∧
      (detachReply (detachBox a caller) caller cid).prio = a.prio ∧
      (detachReply (detachBox a caller) caller cid).parked = a.parked := by
  unfold detachReply
  split
  · simp [detachBox, clearReplyPhase]
  · simp [detachBox]

theorem birth_detach (D : Description) (w : World) (dst caller : InstId) (cid : Nat)
    (h : BirthInv D w) :
    BirthInv D (setActor w dst (detachReply (detachBox (w.st dst) caller) caller cid)) := by
  rcases detach_host_line (w.st dst) caller cid with ⟨hl, hp, hpr, hk⟩
  have hbox : (detachReply (detachBox (w.st dst) caller) caller cid).box =
      (detachBox (w.st dst) caller).box := by
    unfold detachReply
    split <;> rfl
  refine birth_set D w dst _ h hp (Or.inl hl) ?box ?park ?prio
  · intro m hm
    rw [hbox] at hm
    exact detach_plain (w.st dst) caller (h.plainBox dst) m hm
  · intro p hp'
    rw [hk] at hp'
    exact h.plainParked dst p hp'
  · intro m hm
    rw [hpr] at hm
    exact Or.inl hm

theorem birth_refund_call (D : Description) (w : World) (caller dst : InstId) (h : BirthInv D w) :
    BirthInv D (refundParkedCall w caller dst) := by
  unfold refundParkedCall
  dsimp only
  by_cases hempty : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty = true
  · simp [hempty]
    exact h
  · have hf : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty = false := by
      cases hbit : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty <;> simp_all
    simp only [hf, ite_false]
    let keep := List.filter (fun p => !((p.sender == caller) && p.isCall)) (w.st dst).parked
    refine birth_credits D _ (tname dst) caller _ ?_
    refine birth_set D w dst { (w.st dst) with parked := keep } h rfl (Or.inl rfl)
      ?box ?park ?prio
    · intro m hm
      exact h.plainBox dst m hm
    · intro p hp
      exact h.plainParked dst p (List.mem_filter.mp hp).1
    · intro m hm
      exact Or.inl hm

theorem birth_finish (I : Impl) (w w' : World) (id : InstId) (h : BirthInv I.desc w)
    (hf : finishWait I w id = some w') : BirthInv I.desc w' := by
  unfold finishWait at hf
  by_cases hl : (w.st id).life = .alive
  · simp only [hl, ne_eq] at hf
    cases hph : (w.st id).phase <;> simp [hph] at hf
    case awaitEffect k =>
      cases hf
      exact birth_keep_line I.desc w id (proceed (w.st id) k) h (proceed_lineage (w.st id) k)
    case awaitPeer k =>
      cases hf
      exact birth_keep_line I.desc w id (proceed (w.st id) k) h (proceed_lineage (w.st id) k)
  · have hne : (w.st id).life ≠ .alive := by
      intro heq
      exact hl heq
    simp [hne] at hf

theorem birth_timeout (D : Description) (w w' : World) (id : InstId) (h : BirthInv D w)
    (ht : callTimeout w id = some w') : BirthInv D w' := by
  unfold callTimeout at ht
  by_cases hl : ((w.st id).life != .alive) = true
  · simp [hl] at ht
  · have hf : ((w.st id).life != .alive) = false := by
      cases hbit : (w.st id).life != .alive <;> simp_all
    simp only [hf, ite_false] at ht
    cases hph : (w.st id).phase <;> simp [hph] at ht
    case awaitReply dst k =>
      rw [← ht]
      exact birth_keep_line D (setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)) id
        (finishCall
          ((setActor w dst (detachReply (detachBox (w.st dst) id) id (w.st id).waitId)).st id) k .timedOut)
        (birth_detach D w dst id (w.st id).waitId h)
        (finish_lineage _ k .timedOut)
    case parked dst c k =>
      cases hc : c
      · simp [hph, hc] at ht
      · simp [hph, hc] at ht
        rw [← ht]
        exact birth_keep_line D (refundParkedCall w id dst) id
          (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted)
          (birth_refund_call D w id dst h)
          (finish_lineage _ k .notAdmitted)
    case awaitPeer k =>
      rw [← ht]
      exact birth_keep_line D w id (proceed (w.st id)
        { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }) h
        (proceed_lineage _ _)

theorem ingress_msg_tomb (dst : InstId) (label : String) (mid : Nat) :
    ({ label := label, sender := dst, callFrom := none, reliable := true, mid := mid } : Msg).tombstone =
      false := rfl

theorem birth_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : BirthInv I.desc w) (hi : receiveIngress I w dst label = some w') :
    BirthInv I.desc w' := by
  dsimp [receiveIngress] at hi
  split at hi
  · simp at hi
  · split at hi
    · simp at hi
    · split at hi
      · simp at hi
      · split at hi
        · simp at hi
        · split at hi
          · simp at hi
          · cases hi
            let a := w.st dst
            let msg : Msg :=
              { label := label, sender := dst, callFrom := none, reliable := true, mid := a.nextMid }
            let charged := chargeSender a (tname dst)
            rcases charge_lineage a (tname dst) with ⟨hl, hp, hb, hpr, hk⟩
            refine birth_set I.desc w dst { charged with box := a.box ++ [msg], nextMid := a.nextMid + 1 }
              h hp (Or.inl hl) ?box ?park ?prio
            · intro m hm
              exact plain_append (h.plainBox dst) (ingress_msg_tomb dst label a.nextMid) m hm
            · intro p hp'
              rw [hk] at hp'
              exact h.plainParked dst p hp'
            · intro m hm
              rw [hpr] at hm
              exact Or.inl hm

theorem born_shape (D : Description) (w : World) (template : String) (k : Nat)
    (initial : String) (parent : Option InstId) :
    let a := { bornActor D w template k initial with parent := parent }
    a.life = .alive ∧ a.box = [] ∧ a.prio = [] ∧ a.parked = [] ∧ a.parent = parent := by
  simp [bornActor, withKeyTokens, withTokens]

/-- Installing one peer whose key is not on the roster. `next` may bump one
counter and does not touch the roster or an actor. -/
theorem place_roster (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnros : ∀ u, (next u).roster = u.roster) :
    let id := InstId.peer template k (maxGen w template k)
    (placePeer I w template k initial parent next).roster = w.roster ++ [id] := by
  unfold placePeer
  dsimp
  rw [cellsRoster, setActor, hnros]

theorem place_st_self (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnst : ∀ u i, (next u).st i = u.st i) :
    let id := InstId.peer template k (maxGen w template k)
    (placePeer I w template k initial parent next).st id =
      { bornActor I.desc w template k initial with parent := parent } := by
  intro id
  have hset : (setActor (next { w with roster := w.roster ++ [id] }) id
      { bornActor I.desc w template k initial with parent := parent }).st id =
      { bornActor I.desc w template k initial with parent := parent } := setActor_self _ _ _
  simpa [placePeer, cellsSt, hnst] using hset

theorem place_st_other (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World) (i : InstId)
    (hnst : ∀ u j, (next u).st j = u.st j)
    (hne : i ≠ InstId.peer template k (maxGen w template k)) :
    (placePeer I w template k initial parent next).st i = w.st i := by
  have hset : (setActor (next { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] })
      (InstId.peer template k (maxGen w template k))
      { bornActor I.desc w template k initial with parent := parent }).st i = w.st i := by
    rw [setActor_other _ _ _ _ hne, hnst]
  simpa [placePeer, cellsSt] using hset

theorem place_nextIx (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (n : String) :
    (placePeer I w template k initial none
      (fun u => { u with nextIx := fun m => if m = template then k + 1 else u.nextIx m })).nextIx n =
      if n = template then k + 1 else w.nextIx n := by
  unfold placePeer
  dsimp
  rw [readCells_nextIx, setActor]

theorem place_nextKey (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (s : String) :
    (placePeer I w template k initial none
      (fun u => { u with nextIx := fun m => if m = template then k + 1 else u.nextIx m })).nextKey s =
      w.nextKey s := by
  unfold placePeer
  dsimp
  rw [readCells_nextKey, setActor]

/-- The counter step of an unsupervised lone root. -/
abbrev ixBump (template : String) (k : Nat) (u : World) : World :=
  { u with nextIx := fun m => if m = template then k + 1 else u.nextIx m }

theorem ixBump_st (template : String) (k : Nat) (u : World) (i : InstId) :
    (ixBump template k u).st i = u.st i := rfl

theorem ixBump_roster (template : String) (k : Nat) (u : World) :
    (ixBump template k u).roster = u.roster := rfl

theorem alive_on_roster (w : World) (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster)
    (id : InstId) (hl : (w.st id).life = .alive) : id ∈ w.roster :=
  hO id (by rw [hl]; intro hbad; cases hbad)

/-- An unsupervised lone root born at `nextIx`. The key is past every earlier
birth of that template (`ixPast`), the parent is `none`, and a non-absent
actor is already on the roster, so the new generation is the only live one. -/
theorem birth_lone (I : Impl) (w : World) (h : BirthInv I.desc w)
    (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster)
    (template : String) (t : Template) (k : Nat)
    (ht : templateOf I.desc template = some t) (hsup : t.supervisor = none)
    (hsub : t.subtree = "") (hk : k = w.nextIx template) :
    BirthInv I.desc (placePeer I w template k t.initial none (ixBump template k)) := by
  let id := InstId.peer template k (maxGen w template k)
  have hfresh : ∀ g, InstId.peer template k g ∉ w.roster := by
    intro g hmem
    have hlt := h.ixPast template k g hmem t ht hsup hsub
    omega
  have hros := place_roster I w template k t.initial none (ixBump template k) (ixBump_roster template k)
  have hself := place_st_self I w template k t.initial none (ixBump template k) (ixBump_st template k)
  have hother (i : InstId) (hne : i ≠ id) :
      (placePeer I w template k t.initial none (ixBump template k)).st i = w.st i :=
    place_st_other I w template k t.initial none (ixBump template k) i (ixBump_st template k) hne
  have hborn := born_shape I.desc w template k t.initial (none : Option InstId)
  refine ⟨?parented, ?single, ?tomb, ?present, ?box, ?self, ?park, ?live, ?onParent, ?ix, ?key⟩
  · intro i t' hi ht'
    rw [hros] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · have hne : i ≠ id := by
        intro heq
        exact hfresh _ (heq ▸ hold)
      rw [hother i hne]
      exact h.parented i t' hold ht'
    · have hiEq : i = id := List.mem_singleton.mp hnew
      unfold id at hiEq
      cases hiEq
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname] using ht'.symm.trans ht
        cases hsame
        rfl
      rw [hself]
      simp [htEq, hsup]
  · intro name key g1 g2 t' ht' hroot h1 h2
    rw [hros] at h1
    rw [hros] at h2
    rcases List.mem_append.mp h1 with h1o | h1n
    · rcases List.mem_append.mp h2 with h2o | h2n
      · exact h.singleGen name key g1 g2 t' ht' hroot h1o h2o
      · have h2eq := List.mem_singleton.mp h2n
        unfold id at h2eq
        cases h2eq
        exact absurd h1o (hfresh g1)
    · have h1eq := List.mem_singleton.mp h1n
      unfold id at h1eq
      cases h1eq
      rcases List.mem_append.mp h2 with h2o | h2n
      · exact absurd h2o (hfresh g2)
      · have h2eq := List.mem_singleton.mp h2n
        unfold id at h2eq
        cases h2eq
        rfl
  · intro name key g host m hliveP hliveH hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · have hm0 : m ∈ (w.st host).prio := by
        rw [hother host hh] at hm
        exact hm
      by_cases hp : InstId.peer name key g = id
      · unfold id at hp
        cases hp
        have hold := h.tombOnParent host m hm0 htomb
        cases hs : m.sender with
        | core _ => simp [hs]
        | peer n0 k0 g0 =>
          simp only [hs] at hold
          intro hn hk0
          rcases hold with ⟨hmem, _, _⟩
          exact hfresh g0 (by simpa [hn, hk0] using hmem)
      · have hlive0 : (w.st (InstId.peer name key g)).life = .alive := by
          rw [← hother _ hp]
          exact hliveP
        have hhost0 : (w.st host).life = .alive := by
          rw [← hother host hh]
          exact hliveH
        exact h.noTombLive name key g host m hlive0 hhost0 hm0 htomb
  · intro i hi
    rw [hros] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · have hne : i ≠ id := by
        intro heq
        exact hfresh _ (heq ▸ hold)
      rw [hother i hne]
      exact h.present i hold
    · have hiEq : i = id := List.mem_singleton.mp hnew
      unfold id at hiEq
      cases hiEq
      rw [hself]
      intro hbad
      rw [hborn.1] at hbad
      cases hbad
  · intro host m hm
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · rw [hother host hh] at hm
      exact h.plainBox host m hm
  · intro i
    by_cases hh : i = id
    · rw [hh, hself]
      intro hbad
      rw [hborn.2.2.2.2] at hbad
      cases hbad
    · rw [hother i hh]
      exact h.noSelf i
  · intro host p hp
    by_cases hh : host = id
    · rw [hh, hself] at hp
      simp [bornActor, withKeyTokens, withTokens] at hp
    · rw [hother host hh] at hp
      exact h.plainParked host p hp
  · intro n key g1 g2 h1 h2
    by_cases h1n : InstId.peer n key g1 = id
    · by_cases h2n : InstId.peer n key g2 = id
      · unfold id at h1n
        unfold id at h2n
        cases h1n
        cases h2n
        rfl
      · have h2old : (w.st (InstId.peer n key g2)).life = .alive := by
          rw [← hother _ h2n]
          exact h2
        unfold id at h1n
        cases h1n
        exact absurd (alive_on_roster w hO _ h2old) (hfresh g2)
    · by_cases h2n : InstId.peer n key g2 = id
      · have h1old : (w.st (InstId.peer n key g1)).life = .alive := by
          rw [← hother _ h1n]
          exact h1
        unfold id at h2n
        cases h2n
        exact absurd (alive_on_roster w hO _ h1old) (hfresh g1)
      · exact h.oneLive n key g1 g2 (by rw [← hother _ h1n]; exact h1)
          (by rw [← hother _ h2n]; exact h2)
  · intro host m hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · have hm0 : m ∈ (w.st host).prio := by
        rw [hother host hh] at hm
        exact hm
      have hold := h.tombOnParent host m hm0 htomb
      cases hs : m.sender with
      | core _ => simp [hs]
      | peer n key g =>
        simp only [hs] at hold
        rcases hold with ⟨hmem, hp, hd⟩
        have hne : InstId.peer n key g ≠ id := by
          intro heq
          unfold id at heq
          cases heq
          exact hfresh _ hmem
        refine ⟨?_, ?_, ?_⟩
        · rw [hros]
          exact List.mem_append_left _ hmem
        · rw [hother _ hne]
          exact hp
        · rw [hother _ hne]
          exact hd
  · intro n key g hmem t' ht' hsup' hsub'
    rw [hros] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · have hlt := h.ixPast n key g hold t' ht' hsup' hsub'
      have hix := place_nextIx I w template k t.initial n
      by_cases hn : n = template
      · rw [hix, ite_eq_left hn]
        have hlt' : key < k := by simpa [hn, hk] using hlt
        omega
      · rw [hix, ite_eq_right hn]
        exact hlt
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      rw [place_nextIx I w template k t.initial template, ite_eq_left rfl]
      omega
  · intro n key g hmem t' ht' hne
    rw [hros] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · have hlt := h.keyPast n key g hold t' ht' hne
      simpa [place_nextKey I w template k t.initial (templateSubtree I.desc n)] using hlt
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      have hsub' : t'.subtree = "" := by
        have hsame : some t' = some t := by rw [← ht', ht]
        cases hsame
        exact hsub
      exact absurd hsub' hne

/-- The counter step of a subtree key. Every member of `sub` shares it. -/
abbrev keyBump (sub : String) (k : Nat) (u : World) : World :=
  { u with nextKey := fun s => if s = sub then k + 1 else u.nextKey s }

theorem keyBump_st (sub : String) (k : Nat) (u : World) (i : InstId) :
    (keyBump sub k u).st i = u.st i := rfl

theorem keyBump_roster (sub : String) (k : Nat) (u : World) :
    (keyBump sub k u).roster = u.roster := rfl

theorem freshKey_ge (D : Description) (w : World) (sub : String) :
    w.nextKey sub ≤ freshKey D w sub := by
  unfold freshKey
  suffices ∀ (ids : List InstId) (start : Nat), start ≤ ids.foldl (fun m id =>
      match id with
      | .peer n k _ => if sub != "" && templateSubtree D n == sub then max m (k + 1) else m
      | .core _ => m) start by
    exact this w.roster (w.nextKey sub)
  intro ids
  induction ids with
  | nil => intro start; simp
  | cons id ids ih =>
    intro start
    simp only [List.foldl_cons]
    cases id with
    | core _ => exact ih start
    | peer n k _ =>
      by_cases hc : (sub != "" && templateSubtree D n == sub) = true
      · simp only [hc, ite_true]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih (max start (k + 1)))
      · have hf : (sub != "" && templateSubtree D n == sub) = false := by
          cases hbb : sub != "" && templateSubtree D n == sub <;> simp_all
        simp only [hf, ite_false]
        exact ih start

theorem place_key_nextIx (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (sub : String) (n : String) :
    (placePeer I w template k initial parent (keyBump sub k)).nextIx n = w.nextIx n := by
  unfold placePeer
  dsimp
  rw [readCells_nextIx, setActor]

theorem place_key_nextKey (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (sub s : String) :
    (placePeer I w template k initial parent (keyBump sub k)).nextKey s =
      if s = sub then k + 1 else w.nextKey s := by
  unfold placePeer
  dsimp
  rw [readCells_nextKey, setActor]

/-- A root born at `freshKey`. The key is past every earlier key of the subtree,
and the parent is the core the template names, or `none` when it names nobody. -/
theorem birth_fresh (I : Impl) (w : World) (h : BirthInv I.desc w)
    (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster)
    (template : String) (t : Template) (k : Nat) (parent : Option InstId)
    (hpar : match t.supervisor with
      | none => parent = none
      | some name => parent = some (InstId.core name))
    (ht : templateOf I.desc template = some t) (hsub : t.subtree ≠ "")
    (hk : k = freshKey I.desc w t.subtree) :
    BirthInv I.desc (placePeer I w template k t.initial parent (keyBump t.subtree k)) := by
  let id := InstId.peer template k (maxGen w template k)
  have htree : templateSubtree I.desc template = t.subtree := by simp [templateSubtree, ht]
  have hfresh : ∀ g, InstId.peer template k g ∉ w.roster := by
    intro g hmem
    have hlt := freshKey_gt I.desc w t.subtree template k g hsub htree hmem
    omega
  have hros := place_roster I w template k t.initial parent (keyBump t.subtree k)
    (keyBump_roster t.subtree k)
  have hself := place_st_self I w template k t.initial parent (keyBump t.subtree k)
    (keyBump_st t.subtree k)
  have hother (i : InstId) (hne : i ≠ id) :
      (placePeer I w template k t.initial parent (keyBump t.subtree k)).st i = w.st i :=
    place_st_other I w template k t.initial parent (keyBump t.subtree k) i (keyBump_st t.subtree k) hne
  have hborn := born_shape I.desc w template k t.initial parent
  refine ⟨?parented, ?single, ?tomb, ?present, ?box, ?self, ?park, ?live, ?onParent, ?ix, ?key⟩
  · intro i t' hi ht'
    rw [hros] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · have hne : i ≠ id := by
        intro heq
        exact hfresh _ (heq ▸ hold)
      rw [hother i hne]
      exact h.parented i t' hold ht'
    · have hiEq : i = id := List.mem_singleton.mp hnew
      unfold id at hiEq
      cases hiEq
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname] using ht'.symm.trans ht
        cases hsame
        rfl
      rw [htEq, hself]
      cases hsupv : t.supervisor with
      | none =>
        have hpnone : parent = none := by simpa [hsupv] using hpar
        simpa [hsupv, hpnone, bornActor, withKeyTokens, withTokens]
      | some name =>
        have hpcore : parent = some (InstId.core name) := by simpa [hsupv] using hpar
        simp [hsupv, hpcore, tname, bornActor, withKeyTokens, withTokens]
  · intro name key g1 g2 t' ht' hroot h1 h2
    rw [hros] at h1
    rw [hros] at h2
    rcases List.mem_append.mp h1 with h1o | h1n
    · rcases List.mem_append.mp h2 with h2o | h2n
      · exact h.singleGen name key g1 g2 t' ht' hroot h1o h2o
      · have h2eq := List.mem_singleton.mp h2n
        unfold id at h2eq
        cases h2eq
        exact absurd h1o (hfresh g1)
    · have h1eq := List.mem_singleton.mp h1n
      unfold id at h1eq
      cases h1eq
      rcases List.mem_append.mp h2 with h2o | h2n
      · exact absurd h2o (hfresh g2)
      · have h2eq := List.mem_singleton.mp h2n
        unfold id at h2eq
        cases h2eq
        rfl
  · intro name key g host m hliveP hliveH hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · have hm0 : m ∈ (w.st host).prio := by
        rw [hother host hh] at hm
        exact hm
      by_cases hp : InstId.peer name key g = id
      · unfold id at hp
        cases hp
        have hold := h.tombOnParent host m hm0 htomb
        cases hs : m.sender with
        | core _ => simp [hs]
        | peer n0 k0 g0 =>
          simp only [hs] at hold
          intro hn hk0
          rcases hold with ⟨hmem, _, _⟩
          exact hfresh g0 (by simpa [hn, hk0] using hmem)
      · have hlive0 : (w.st (InstId.peer name key g)).life = .alive := by
          rw [← hother _ hp]
          exact hliveP
        have hhost0 : (w.st host).life = .alive := by
          rw [← hother host hh]
          exact hliveH
        exact h.noTombLive name key g host m hlive0 hhost0 hm0 htomb
  · intro i hi
    rw [hros] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · have hne : i ≠ id := by
        intro heq
        exact hfresh _ (heq ▸ hold)
      rw [hother i hne]
      exact h.present i hold
    · have hiEq : i = id := List.mem_singleton.mp hnew
      unfold id at hiEq
      cases hiEq
      rw [hself]
      intro hbad
      rw [hborn.1] at hbad
      cases hbad
  · intro host m hm
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · rw [hother host hh] at hm
      exact h.plainBox host m hm
  · intro i
    by_cases hh : i = id
    · cases hsupv : t.supervisor with
      | none =>
        have hpnone : parent = none := by simpa [hsupv] using hpar
        rw [hh, hself, hpnone]
        intro hbad
        simp [bornActor, withKeyTokens, withTokens] at hbad
      | some name =>
        have hpcore : parent = some (InstId.core name) := by simpa [hsupv] using hpar
        rw [hh, hself, hpcore]
        intro hbad
        simp at hbad
    · rw [hother i hh]
      exact h.noSelf i
  · intro host p hp
    by_cases hh : host = id
    · rw [hh, hself] at hp
      simp [bornActor, withKeyTokens, withTokens] at hp
    · rw [hother host hh] at hp
      exact h.plainParked host p hp
  · intro n key g1 g2 h1 h2
    by_cases h1n : InstId.peer n key g1 = id
    · by_cases h2n : InstId.peer n key g2 = id
      · unfold id at h1n
        unfold id at h2n
        cases h1n
        cases h2n
        rfl
      · have h2old : (w.st (InstId.peer n key g2)).life = .alive := by
          rw [← hother _ h2n]
          exact h2
        unfold id at h1n
        cases h1n
        exact absurd (alive_on_roster w hO _ h2old) (hfresh g2)
    · by_cases h2n : InstId.peer n key g2 = id
      · have h1old : (w.st (InstId.peer n key g1)).life = .alive := by
          rw [← hother _ h1n]
          exact h1
        unfold id at h2n
        cases h2n
        exact absurd (alive_on_roster w hO _ h1old) (hfresh g1)
      · exact h.oneLive n key g1 g2 (by rw [← hother _ h1n]; exact h1)
          (by rw [← hother _ h2n]; exact h2)
  · intro host m hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [bornActor, withKeyTokens, withTokens] at hm
    · have hm0 : m ∈ (w.st host).prio := by
        rw [hother host hh] at hm
        exact hm
      have hold := h.tombOnParent host m hm0 htomb
      cases hs : m.sender with
      | core _ => simp [hs]
      | peer n key g =>
        simp only [hs] at hold
        rcases hold with ⟨hmem, hp, hd⟩
        have hne : InstId.peer n key g ≠ id := by
          intro heq
          unfold id at heq
          cases heq
          exact hfresh _ hmem
        refine ⟨?_, ?_, ?_⟩
        · rw [hros]
          exact List.mem_append_left _ hmem
        · rw [hother _ hne]
          exact hp
        · rw [hother _ hne]
          exact hd
  · intro n key g hmem t' ht' hsup' hsub'
    rw [hros] at hmem
    have hix := place_key_nextIx I w template k t.initial parent t.subtree n
    rw [hix]
    rcases List.mem_append.mp hmem with hold | hnew
    · exact h.ixPast n key g hold t' ht' hsup' hsub'
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      have hne' : t'.subtree ≠ "" := by
        have hsame : some t' = some t := by simpa [tname] using ht'.symm.trans ht
        cases hsame
        exact hsub
      exact absurd hsub' hne'
  · intro n key g hmem t' ht' hne
    rw [hros] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · have hlt := h.keyPast n key g hold t' ht' hne
      have hkey := place_key_nextKey I w template k t.initial parent t.subtree
        (templateSubtree I.desc n)
      by_cases hs : templateSubtree I.desc n = t.subtree
      · rw [hkey, ite_eq_left hs]
        have hlt0 : key < w.nextKey t.subtree := by simpa [hs] using hlt
        have hge := freshKey_ge I.desc w t.subtree
        omega
      · rw [hkey, ite_eq_right hs]
        exact hlt
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      have hkey := place_key_nextKey I w template k t.initial parent t.subtree
        (templateSubtree I.desc template)
      have hhere : templateSubtree I.desc template = t.subtree := htree
      rw [hkey, hhere, ite_eq_left rfl]
      omega

/-- A named supervisor sits in a nonempty subtree. The empty-subtree arm of
`subtreeEntry` rejects that template, and `GraphOk` has no such failures.
`supervised_subtree` states the same fact; this copy stays here because Birth
does not import Occ (Tomb and Step both export `detach_phase`). -/
theorem birth_supervised (D : Description) (hG : GraphOk D) (template : String) (t : Template)
    (ht : templateOf D template = some t) (name : String)
    (hsup : t.supervisor = some name) : t.subtree ≠ "" := by
  have hmap : D.templates.filterMap (subtreeEntry D) = [] :=
    (List.append_eq_nil_iff.mp (by simpa only [subtreeFails_entry] using hG.subtrees)).1
  have hent := filterMap_none (subtreeEntry D) D.templates hmap t (templateOf_mem D template t ht).1
  intro heq
  have hsubB : (t.subtree == "") = true := by simpa [beq_iff_eq] using heq
  have hsome : t.supervisor.isSome = true := by simp [hsup]
  unfold subtreeEntry at hent
  simp [hsubB, hsome] at hent

/-- Scheduler birth of a subtree root. A core supervisor takes `freshKey`; an
unsupervised empty subtree takes `nextIx`; an unsupervised nonempty subtree
takes `freshKey` with parent `none`. -/
theorem birth_spawn (I : Impl) (hG : GraphOk I.desc) (w w' : World) (template : String)
    (h : BirthInv I.desc w)
    (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster)
    (hsp : spawn I w template = some w') : BirthInv I.desc w' := by
  unfold spawn at hsp
  cases ht : templateOf I.desc template with
  | none => simp [ht] at hsp
  | some t =>
    simp only [ht] at hsp
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · rw [hmay] at hsp
      rw [ite_eq_left (by decide : true = true)] at hsp
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at hsp
        dsimp at hsp
        let k := freshKey I.desc w t.subtree
        have hsub := birth_supervised I.desc hG template t ht name hsup
        injection hsp with hw
        subst hw
        exact birth_fresh I w h hO template t k (some (InstId.core name))
          (by simp [hsup]) ht hsub rfl
      | none =>
        rw [hsup] at hsp
        dsimp at hsp
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at hsp
          rw [ite_eq_left (by decide : true = true)] at hsp
          let k := w.nextIx template
          have hsub : t.subtree = "" := by simpa [beq_iff_eq] using hempty
          injection hsp with hw
          subst hw
          exact birth_lone I w h hO template t k ht hsup hsub rfl
        · have hf : (t.subtree == "") = false := by
            cases hbb : t.subtree == ""
            · rfl
            · exact absurd hbb hempty
          rw [hf] at hsp
          rw [ite_eq_right (by decide : ¬ false = true)] at hsp
          let k := freshKey I.desc w t.subtree
          have hsub : t.subtree ≠ "" := by
            intro heq
            simp [beq_iff_eq, heq] at hf
          injection hsp with hw
          subst hw
          exact birth_fresh I w h hO template t k none (by simp [hsup]) ht hsub rfl
    · have hf : maySpawnRoot I.desc w template t = false := by
        cases hbb : maySpawnRoot I.desc w template t
        · rfl
        · exact absurd hbb hmay
      simp [hf] at hsp
