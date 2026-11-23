/-
A per-peer parent births its child at its own key.

`keyPast` says that key is already below `nextKey`. The parent is a per-peer
member of the same subtree, which is `PeerRole` together with `GraphOk`. A
live peer of a multiplicity-one name is the world where the child would land
on a key `nextKey` has not passed; `spawnChild` from a core admits nobody,
and no birth step makes that peer. `CoreRole` keeps a tombstone's host from
being a core of a per-peer name, so the lane `spawnChild` consults is the
parent's.
-/

import Deadlock.Birth

set_option autoImplicit false

namespace Deadlock

/-- Workaround `peerRole`: a live peer belongs to a per-peer template.
`spawn` and `spawnChild` both require `perPeer` before they admit anyone,
and no other step makes an actor alive. -/
def PeerRole (D : Description) (w : World) : Prop :=
  ∀ n k g, (w.st (InstId.peer n k g)).life = .alive →
    ∃ t, templateOf D n = some t ∧ t.multiplicity = .perPeer

/-- Workaround `coreRole`: a live core belongs to a multiplicity-one template.
`initWorld` places those templates as cores, and no step admits a core. -/
def CoreRole (D : Description) (w : World) : Prop :=
  ∀ n, (w.st (InstId.core n)).life = .alive →
    ∃ t, templateOf D n = some t ∧ t.multiplicity = .one

theorem admit_roster (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).roster = w.roster ++ [id] := by
  simp [admitBorn, cellsRoster, setActor]

theorem admit_nextKey (I : Impl) (w : World) (id : InstId) (a : Actor) (s : String) :
    (admitBorn I w id a).nextKey s = w.nextKey s := by
  simp [admitBorn, readCells_nextKey, setActor]

theorem admit_nextIx (I : Impl) (w : World) (id : InstId) (a : Actor) (n : String) :
    (admitBorn I w id a).nextIx n = w.nextIx n := by
  simp [admitBorn, readCells_nextIx, setActor]

theorem admit_st_self (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).st id = a := by
  simp [admitBorn, cellsSt, setActor]

theorem admit_st_other (I : Impl) (w : World) (id i : InstId) (a : Actor) (hne : i ≠ id) :
    (admitBorn I w id a).st i = w.st i := by
  simp [admitBorn, cellsSt, setActor, hne]

theorem sup_is (name : String) (s : Option String) (h : supNamed s name = true) : s = some name := by
  cases s with
  | none => simp [supNamed] at h
  | some n =>
    simp [supNamed, beq_iff_eq] at h
    simp [h]

theorem mul_per (t : Template) (h : (t.multiplicity == .perPeer) = true) : t.multiplicity = .perPeer := by
  cases hm : t.multiplicity with
  | one =>
    rw [hm] at h
    rw [show (Multiplicity.one == Multiplicity.perPeer) = false by decide] at h
    cases h
  | perPeer => rfl

theorem occupied_of_live (w : World) (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster)
    (n : String) (k g : Nat) (hl : (w.st (InstId.peer n k g)).life = .alive) :
    slotOccupied w n k = true := by
  have hmem := alive_on_roster w hO _ hl
  unfold slotOccupied
  apply _root_.List.any_eq_true.mpr
  refine ⟨InstId.peer n k g, hmem, ?_⟩
  simp [hl]

theorem slot_sees_tomb (w : World) (parent : InstId) (child : String) (k g : Nat) (m : Msg)
    (hm : m ∈ (w.st parent).prio) (ht : m.tombstone = true)
    (hs : m.sender = InstId.peer child k g) : slotTombstoneQueued w parent child k = true := by
  unfold slotTombstoneQueued
  apply _root_.List.any_eq_true.mpr
  refine ⟨m, hm, ?_⟩
  simp [hs, ht]

/-- A passing subtree entry with a per-peer body and a named supervisor has
that supervisor in the subtree. -/
theorem entry_sup_in (D : Description) (t : Template) (h : subtreeEntry D t = none)
    (hsub : t.subtree ≠ "") (hmul : t.multiplicity = .perPeer)
    (hsome : t.supervisor.isSome = true) : supervisorInSubtree D t = true := by
  unfold subtreeEntry at h
  have hsubB : (t.subtree == "") = false := by simpa [beq_iff_eq] using hsub
  have hmulB : (t.multiplicity != .perPeer) = false := by
    rw [hmul]
    decide
  simp only [hsubB, Bool.false_eq_true, ite_false, hmulB] at h
  cases hsi : supervisorInSubtree D t with
  | true => rfl
  | false =>
    have hbad : (t.supervisor.isSome && !supervisorInSubtree D t) = true := by simp [hsome, hsi]
    simp [hbad] at h

/-- A per-peer supervisor of a checked template shares its subtree and is not
the template itself. -/
theorem per_sup_same (D : Description) (hG : GraphOk D) (template : String) (t : Template)
    (ht : templateOf D template = some t) (hmulC : t.multiplicity = .perPeer) (supName : String)
    (hsup : t.supervisor = some supName) (ts : Template) (hts : templateOf D supName = some ts)
    (hmul : ts.multiplicity = .perPeer) : ts.subtree = t.subtree ∧ ts.name ≠ t.name := by
  have hsub := birth_supervised D hG template t ht supName hsup
  have hmap : D.templates.filterMap (subtreeEntry D) = [] :=
    (List.append_eq_nil_iff.mp (by simpa only [subtreeFails_entry] using hG.subtrees)).1
  have hent := filterMap_none (subtreeEntry D) D.templates hmap t (templateOf_mem D template t ht).1
  have hsi := entry_sup_in D t hent hsub hmulC (by simp [hsup])
  unfold supervisorInSubtree at hsi
  simp only [hsup, hts] at hsi
  have hone : (ts.multiplicity == .one) = false := by
    rw [hmul]
    decide
  rw [hone, hmul] at hsi
  simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsi
  exact ⟨hsi.1.2, hsi.2⟩

theorem root_of_per (D : Description) (t ts : Template) (name : String)
    (hsup : t.supervisor = some name) (hts : templateOf D name = some ts)
    (hmul : ts.multiplicity = .perPeer) : rootOf D t = false := by
  unfold rootOf
  simp only [hsup, hts]
  have hf : (ts.multiplicity == .one) = false := by
    rw [hmul]
    decide
  simp [hf]

/-- Admit one child at its parent's key. The parent is a live per-peer of the
supervisor's name, the slot is clear, and both role facts hold, so the new
key is the parent's and that key is already below `nextKey`. -/
theorem birth_child_at (I : Impl) (hG : GraphOk I.desc) (w : World) (h : BirthInv I.desc w)
    (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster) (hP : PeerRole I.desc w)
    (hC : CoreRole I.desc w) (pname child : String) (pk pg : Nat) (t : Template)
    (ht : templateOf I.desc child = some t) (hmul : t.multiplicity = .perPeer)
    (hsup : t.supervisor = some pname) (hlive : (w.st (InstId.peer pname pk pg)).life = .alive)
    (hslot : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = false) :
    BirthInv I.desc (admitBorn I w (InstId.peer child pk (maxGen w child pk))
      { bornActor I.desc w child pk t.initial with parent := some (InstId.peer pname pk pg) }) := by
  let parent := InstId.peer pname pk pg
  let id := InstId.peer child pk (maxGen w child pk)
  let born := { bornActor I.desc w child pk t.initial with parent := some parent }
  obtain ⟨ts, hts, hmulS⟩ := hP pname pk pg hlive
  obtain ⟨hshare, hdiff⟩ := per_sup_same I.desc hG child t ht hmul pname hsup ts hts hmulS
  have hsub := birth_supervised I.desc hG child t ht pname hsup
  have hnameP : ts.name = pname := (templateOf_mem I.desc pname ts hts).2
  have hnameC : t.name = child := (templateOf_mem I.desc child t ht).2
  have hneName : pname ≠ child := by
    intro heq
    exact hdiff (by simpa [hnameP, hnameC] using heq)
  have hrootF := root_of_per I.desc t ts pname hsup hts hmulS
  obtain ⟨hoccF, htombF⟩ := slotRespawnBlocked_clear I.desc w parent child pk hslot
  have hmemP := alive_on_roster w hO parent hlive
  have htree : templateSubtree I.desc child = t.subtree := by simp [templateSubtree, ht]
  have htreeP : templateSubtree I.desc pname = ts.subtree := by simp [templateSubtree, hts]
  have hfresh : id ∉ w.roster := by
    simpa [id] using maxGen_notin w child pk
  have hros := admit_roster I w id born
  have hself := admit_st_self I w id born
  have hother (i : InstId) (hne : i ≠ id) : (admitBorn I w id born).st i = w.st i :=
    admit_st_other I w id i born hne
  have hborn := born_shape I.desc w child pk t.initial (some parent)
  refine ⟨?parented, ?single, ?tomb, ?present, ?box, ?self, ?park, ?live, ?onParent, ?ix, ?key⟩
  · intro i t' hi ht'
    rw [hros] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · have hne : i ≠ id := by
        intro heq
        exact hfresh (heq ▸ hold)
      rw [hother i hne]
      exact h.parented i t' hold ht'
    · have hiEq : i = id := List.mem_singleton.mp hnew
      cases hiEq
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname, id] using ht'.symm.trans ht
        cases hsame
        rfl
      rw [htEq, hself, hsup]
      refine ⟨parent, ?_, ?_, ?_⟩
      · simpa [born, bornActor, withKeyTokens, withTokens]
      · rfl
      · simp [parent, id, memberKey]
  · intro name key g1 g2 t' ht' hroot h1 h2
    rw [hros] at h1
    rw [hros] at h2
    rcases List.mem_append.mp h1 with h1o | h1n
    · rcases List.mem_append.mp h2 with h2o | h2n
      · exact h.singleGen name key g1 g2 t' ht' hroot h1o h2o
      · have h2eq := List.mem_singleton.mp h2n
        unfold id at h2eq
        cases h2eq
        have htEq : t' = t := by
          have hsame : some t' = some t := by simpa [tname, id] using ht'.symm.trans ht
          cases hsame
          rfl
        simp [htEq, hrootF] at hroot
    · have h1eq := List.mem_singleton.mp h1n
      unfold id at h1eq
      cases h1eq
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname, id] using ht'.symm.trans ht
        cases hsame
        rfl
      simp [htEq, hrootF] at hroot
  · intro name key g host m hliveP hliveH hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [born, bornActor, withKeyTokens, withTokens] at hm
    · have hm0 : m ∈ (w.st host).prio := by
        rw [hother host hh] at hm
        exact hm
      by_cases hp : InstId.peer name key g = id
      · unfold id at hp
        cases hp
        cases hs : m.sender with
        | core _ => simp [hs]
        | peer n0 k0 g0 =>
          simp only [hs]
          intro hn hk0
          have hold := h.tombOnParent host m hm0 htomb
          simp only [hs] at hold
          rcases hold with ⟨hmemS, hpS, _⟩
          have hmemS' : InstId.peer child pk g0 ∈ w.roster := by simpa [hn, hk0] using hmemS
          have hPar := h.parented (InstId.peer child pk g0) t hmemS' ht
          simp only [hsup] at hPar
          rcases hPar with ⟨p, hparent, hpn, hkeym⟩
          have hpS' : (w.st (InstId.peer child pk g0)).parent = some host := by
            simpa [hn, hk0] using hpS
          have hpe : p = host := by
            have hsames : some p = some host := hparent.symm.trans hpS'
            cases hsames
            rfl
          have hliveH0 : (w.st host).life = .alive := by
            rw [← hother host hh]
            exact hliveH
          cases host with
          | core cn =>
            have hcn : cn = pname := by simpa [hpe, tname] using hpn
            obtain ⟨tc, htc, hmc⟩ := hC cn hliveH0
            have hts' : templateOf I.desc cn = some ts := by
              simpa [hcn] using hts
            have hsameT : ts = tc := by
              cases hts'.symm.trans htc
              rfl
            have hone : ts.multiplicity = .one := by simpa [hsameT] using hmc
            rw [hmulS] at hone
            cases hone
          | peer pn pk2 pg2 =>
            have hpn' : pn = pname := by simpa [hpe, tname] using hpn
            have hpk2 : pk2 = pk := by
              have hk' : memberKey (InstId.peer child pk g0) = some pk2 := by
                simpa [hpe] using hkeym
              simp [memberKey] at hk'
              exact hk'.symm
            have hlivePeer : (w.st (InstId.peer pname pk pg2)).life = .alive := by
              simpa [hpe, hpn', hpk2] using hliveH0
            have hgen := h.oneLive pname pk pg2 pg hlivePeer hlive
            have hhost : InstId.peer pn pk2 pg2 = parent := by
              rw [hpn', hpk2, hgen]
            have hmP : m ∈ (w.st parent).prio := by
              simpa [hhost] using hm0
            have hsee := slot_sees_tomb w parent child pk g0 m hmP htomb (by simp [hs, hn, hk0])
            rw [htombF] at hsee
            cases hsee
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
        exact hfresh (heq ▸ hold)
      rw [hother i hne]
      exact h.present i hold
    · have hiEq : i = id := List.mem_singleton.mp hnew
      cases hiEq
      rw [hself]
      intro hbad
      rw [hborn.1] at hbad
      cases hbad
  · intro host m hm
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [born, bornActor, withKeyTokens, withTokens] at hm
    · rw [hother host hh] at hm
      exact h.plainBox host m hm
  · intro i
    by_cases hh : i = id
    · rw [hh, hself]
      intro hbad
      have hp : born.parent = some parent := by simp [born, bornActor, withKeyTokens, withTokens]
      have hbad' : some parent = some id := by simpa [hp] using hbad
      injection hbad' with hbad'
      unfold parent id at hbad'
      injection hbad' with hname
      exact hneName hname
    · rw [hother i hh]
      exact h.noSelf i
  · intro host p hp
    by_cases hh : host = id
    · rw [hh, hself] at hp
      simp [born, bornActor, withKeyTokens, withTokens] at hp
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
        exact absurd (occupied_of_live w hO child pk g2 h2old) (by simpa using hoccF)
    · by_cases h2n : InstId.peer n key g2 = id
      · have h1old : (w.st (InstId.peer n key g1)).life = .alive := by
          rw [← hother _ h1n]
          exact h1
        unfold id at h2n
        cases h2n
        exact absurd (occupied_of_live w hO child pk g1 h1old) (by simpa using hoccF)
      · exact h.oneLive n key g1 g2 (by rw [← hother _ h1n]; exact h1)
          (by rw [← hother _ h2n]; exact h2)
  · intro host m hm htomb
    by_cases hh : host = id
    · rw [hh, hself] at hm
      simp [born, bornActor, withKeyTokens, withTokens] at hm
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
          exact hfresh (by simpa [heq] using hmem)
        refine ⟨?_, ?_, ?_⟩
        · rw [hros]
          exact List.mem_append_left _ hmem
        · rw [hother _ hne]
          exact hp
        · rw [hother _ hne]
          exact hd
  · intro n key g hmem t' ht' hsup' hsub'
    rw [hros] at hmem
    rw [admit_nextIx I w id born n]
    rcases List.mem_append.mp hmem with hold | hnew
    · exact h.ixPast n key g hold t' ht' hsup' hsub'
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname, id] using ht'.symm.trans ht
        cases hsame
        rfl
      exact absurd hsub' (by simpa [htEq] using hsub)
  · intro n key g hmem t' ht' hne
    rw [hros] at hmem
    rw [admit_nextKey I w id born (templateSubtree I.desc n)]
    rcases List.mem_append.mp hmem with hold | hnew
    · exact h.keyPast n key g hold t' ht' hne
    · have hnew := List.mem_singleton.mp hnew
      unfold id at hnew
      cases hnew
      have htEq : t' = t := by
        have hsame : some t' = some t := by simpa [tname, id] using ht'.symm.trans ht
        cases hsame
        rfl
      have hlt := h.keyPast pname pk pg hmemP ts hts (by simpa [hshare] using hsub)
      simpa [id, htree, htreeP, hshare, htEq] using hlt

/-- `spawnChild` keeps the parent facts. A blocked slot and a dead parent leave
the world alone. A core parent admits nobody. A per-peer parent admits the
child at its own key (`birth_child_at`). -/
theorem birth_spawn_child (I : Impl) (hG : GraphOk I.desc) (w w' : World) (parent : InstId)
    (child : String) (h : BirthInv I.desc w)
    (hO : ∀ id, (w.st id).life ≠ .absent → id ∈ w.roster) (hP : PeerRole I.desc w)
    (hC : CoreRole I.desc w) (hsp : spawnChild I w parent child = some w') :
    BirthInv I.desc w' := by
  unfold spawnChild at hsp
  cases ht : templateOf I.desc child with
  | none => simp [ht] at hsp
  | some t =>
    simp only [ht] at hsp
    by_cases hcond : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
    · rw [hcond] at hsp
      rw [ite_eq_left (by decide : true = true)] at hsp
      cases parent with
      | core _ => simp at hsp
      | peer pname pk pg =>
        dsimp only at hsp
        by_cases hblock : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = true
        · rw [hblock] at hsp
          rw [ite_eq_left (by decide : true = true)] at hsp
          cases hsp
          exact h
        · have hblockF : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk
            · rfl
            · exact absurd hbb hblock
          rw [hblockF] at hsp
          rw [ite_eq_right (by decide : ¬ false = true)] at hsp
          have hparts := by simpa [Bool.and_eq_true] using hcond
          have hmul := mul_per t hparts.1.1
          have hsup := sup_is pname t.supervisor (by simpa [tname] using hparts.1.2)
          have hlive : (w.st (InstId.peer pname pk pg)).life = .alive := hparts.2
          injection hsp with hw
          subst hw
          exact birth_child_at I hG w h hO hP hC pname child pk pg t ht hmul
            (by simpa using hsup) hlive hblockF
    · have hcondF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = false := by
        cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive
        · rfl
        · exact absurd hbb hcond
      rw [hcondF] at hsp
      rw [ite_eq_right (by decide : ¬ false = true)] at hsp
      by_cases hcond2 : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · rw [hcond2] at hsp
        rw [ite_eq_left (by decide : true = true)] at hsp
        cases hsp
        exact h
      · have hcond2F : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)
          · rfl
          · exact absurd hbb hcond2
        rw [hcond2F] at hsp
        rw [ite_eq_right (by decide : ¬ false = true)] at hsp
        simp at hsp

/-- Sealing recorded descendants keeps the parent facts. A descendant is released,
not tombstoned. `birth_release` does not ask it to be alive. -/
theorem fold_seal_birth (D : Description) (fuel : Nat) (id : InstId) (ids : List InstId)
    (w : World) (h : BirthInv D w)
    (ih : ∀ w' c, BirthInv D w' → BirthInv D (sealBranch fuel D w' c)) :
    BirthInv D (ids.foldl (fun acc child =>
      if isChild acc id child then sealBranch fuel D acc child else acc) w) := by
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

theorem birth_seal_branch (D : Description) (fuel : Nat) (w : World) (id : InstId)
    (h : BirthInv D w) : BirthInv D (sealBranch fuel D w id) := by
  induction fuel generalizing w id with
  | zero => simpa [sealBranch] using h
  | succ fuel ih =>
    unfold sealBranch
    dsimp only
    have hfold := fold_seal_birth D fuel id w.roster w h ih
    by_cases hl : (((w.roster.foldl (fun acc child =>
        if isChild acc id child then sealBranch fuel D acc child else acc) w).st id).life ==
        .alive) = true
    · simp only [hl, ite_true]
      exact birth_release D _ id _ hfold
    · have hlf : (((w.roster.foldl (fun acc child =>
          if isChild acc id child then sealBranch fuel D acc child else acc) w).st id).life ==
          .alive) = false := by
        cases hbb : ((w.roster.foldl (fun acc child =>
            if isChild acc id child then sealBranch fuel D acc child else acc) w).st id).life == .alive
        · rfl
        · exact absurd hbb hl
      simp only [hlf, ite_false]
      exact hfold

theorem birth_drop (D : Description) (w : World) (id : InstId) (h : BirthInv D w) :
    BirthInv D (dropDescendants D w id) := by
  unfold dropDescendants
  exact fold_seal_birth D w.roster.length id w.roster w h (fun w' c hw' => birth_seal_branch D _ w' c hw')

/-- Seal `id` when it is alive and on the roster. A life that is not alive is
left alone, and that is the whole step. -/
theorem birth_shutdown (D : Description) (w : World) (id : InstId) (h : BirthInv D w)
    (hmem : (w.st id).life = .alive → id ∈ w.roster) : BirthInv D (shutdownActor D w id) := by
  unfold shutdownActor
  by_cases hl : ((w.st id).life == .alive) = true
  · simp only [hl, ite_true]
    have hlive : (w.st id).life = .alive := beq_iff_eq.mp hl
    exact birth_seal D w id (w.st id) h (hmem hlive) hlive
  · have hlf : ((w.st id).life == .alive) = false := by
      cases hbb : (w.st id).life == .alive
      · rfl
      · exact absurd hbb hl
    simp only [hlf, ite_false]
    exact h

/-- Descendants are released, then `id` is sealed if it is still alive. The
roster does not change, so a member stays a member. -/
theorem birth_terminate (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : BirthInv D w) (hmem : id ∈ w.roster) : BirthInv D (terminateStage D w id a) := by
  unfold terminateStage
  dsimp only
  exact birth_shutdown D (dropDescendants D w id) id (birth_drop D w id h)
    (fun _ => (drop_roster D w id).symm ▸ hmem)

theorem birth_abort_go (D : Description) (parent : InstId) (ids : List InstId) (base w : World)
    (h : BirthInv D w) (hr : w.roster = base.roster) (hsub : ∀ i, i ∈ ids → i ∈ base.roster) :
    BirthInv D (ids.foldl (fun w child =>
      if isChild w parent child && (w.st child).life == .alive then
        shutdownActor D (dropDescendants D w child) child
      else w) w) := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons c cs ih =>
    simp only [List.foldl_cons]
    by_cases hc : (isChild w parent c && (w.st c).life == .alive) = true
    · simp only [hc, ite_true]
      have hmemc : c ∈ w.roster := hr.symm ▸ hsub c (by simp)
      have hlive : (w.st c).life = .alive := by
        exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hc).2
      have hstep := birth_shutdown D (dropDescendants D w c) c (birth_drop D w c h)
        (fun _ => (drop_roster D w c).symm ▸ hmemc)
      have hr' : (shutdownActor D (dropDescendants D w c) c).roster = base.roster :=
        (shutdown_roster D _ c).trans ((drop_roster D w c).trans hr)
      exact ih _ hstep hr' (fun i hi => hsub i (List.mem_cons_of_mem _ hi))
    · have hcf : (isChild w parent c && (w.st c).life == .alive) = false := by
        cases hbb : isChild w parent c && (w.st c).life == .alive
        · rfl
        · exact absurd hbb hc
      simp only [hcf, ite_false]
      exact ih _ h hr (fun i hi => hsub i (List.mem_cons_of_mem _ hi))

/-- Abort seals every live child and that child's descendants. Each child is
taken from the roster, and neither the drop nor the seal removes it. -/
theorem birth_abort (D : Description) (w : World) (parent : InstId) (h : BirthInv D w) :
    BirthInv D (abortChildren D w parent) := by
  unfold abortChildren
  exact birth_abort_go D parent w.roster w w h rfl (fun _ hi => hi)

/-- Install the continuation unless the effect already crashed the roster. -/
theorem birth_commit (D : Description) (w : World) (id : InstId) (next : Actor)
    (h : BirthInv D w)
    (hl : next.life = (w.st id).life ∧ next.parent = (w.st id).parent ∧
      next.box = (w.st id).box ∧ next.prio = (w.st id).prio ∧
      next.parked = (w.st id).parked) :
    BirthInv D (commitCont w id next) := by
  unfold commitCont
  by_cases hc : w.crashed = true
  · simp [hc]
    exact h
  · have hcf : w.crashed = false := by
      cases hb : w.crashed
      · rfl
      · exact absurd hb hc
    simp [hcf]
    exact birth_keep_line D w id next h hl

theorem birth_set_cell (D : Description) (w : World) (dst label : String) (c : Cell)
    (h : BirthInv D w) : BirthInv D (setCell w dst label c) := by
  refine birth_quiet D w _ h rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => Or.inl rfl)
    ?box ?park ?prio
  · intro host m hm
    exact h.plainBox host m hm
  · intro host p hp
    exact h.plainParked host p hp
  · intro host m hm
    exact Or.inl hm

/-- A cell wake is a plain priority message. A dead reader and a label already
queued are left alone. A full lane crashes, which `birth_offer` already covers. -/
theorem birth_try_wake (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (h : BirthInv D w) : BirthInv D (tryWake D w dstId label writer) := by
  unfold tryWake
  dsimp only
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip]
    exact h
  · have hsf : ((w.st dstId).life != .alive ||
        (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      cases hbb : (w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)
      · rfl
      · exact absurd hbb hskip
    simp only [hsf, ite_false]
    exact birth_offer D w dstId
      { label := label, sender := writer, callFrom := none, reliable := false,
        mid := (w.st dstId).nextMid } h (PrioFrom.plain (by simp))

theorem birth_wake_ids (D : Description) (ids : List InstId) (w : World) (dst label : String)
    (writer : InstId) (h : BirthInv D w) :
    BirthInv D (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (birth_try_wake D w i label writer h)

theorem birth_readers (D : Description) (w : World) (dst label : String) (writer : InstId)
    (h : BirthInv D w) : BirthInv D (wakeReaders D w dst label writer) := by
  unfold wakeReaders readersOf
  exact birth_wake_ids D _ w dst label writer h

/-- A reply resumes the caller only when the wait matches. Both writes keep
life, parent, and mail. -/
theorem birth_reply (D : Description) (w : World) (sender : InstId) (k : Cont)
    (h : BirthInv D w) : BirthInv D (performReply w sender k) := by
  unfold performReply
  dsimp only
  cases hr : k.replyTo with
  | none =>
    simp [hr]
    exact birth_keep_line D w sender _ h (proceed_lineage _ _)
  | some caller =>
    simp only [hr]
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hmatch : (dst = sender && (w.st sender).oweId = some (w.st caller).waitId) = true
      · simp only [hph, hmatch, ite_true]
        have hcaller := birth_keep_line D w caller (finishCall (w.st caller) ck .reply) h
          (finish_lineage _ _ _)
        by_cases hsame : sender = caller
        · subst hsame
          refine birth_keep_line D _ sender _ hcaller ?_
          simp only [setActor_self]
          exact proceed_lineage _ _
        · refine birth_keep_line D _ sender _ hcaller ?_
          simp only [setActor_other _ _ _ _ hsame]
          exact proceed_lineage _ _
      · have hmf : (dst = sender && (w.st sender).oweId = some (w.st caller).waitId) = false := by
          cases hbb : dst = sender && (w.st sender).oweId = some (w.st caller).waitId
          · rfl
          · exact absurd hbb hmatch
        simp only [hph, hmf, ite_false]
        exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | idle =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | run _ =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | awaitEffect _ =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | awaitPeer _ =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | parked _ _ _ =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)
    | crashed =>
      simp [hph]
      exact birth_keep_line D w sender _ h (proceed_lineage _ _)

/-- One effect of a live actor. `spawnChild` is the only branch that admits
anyone, and it keeps `keyPast` by `birth_spawn_child`. `terminate` seals
through `shutdownActor` and `dropDescendants`. -/
theorem birth_exec (I : Impl) (hG : GraphOk I.desc) (w : World) (id : InstId) (a : Actor)
    (k : Cont) (h : BirthInv I.desc w)
    (hO : ∀ i, (w.st i).life ≠ .absent → i ∈ w.roster) (hP : PeerRole I.desc w)
    (hC : CoreRole I.desc w) (ha : a = w.st id) : BirthInv I.desc (execRun I w id a k) := by
  subst ha
  unfold execRun
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive, ite_true]
    cases hk : k.rest with
    | nil =>
      simp only [hk]
      exact birth_keep_line I.desc w id _ h (by simp)
    | cons eff rest =>
      simp only [hk]
      cases eff with
      | send dst label hint =>
        cases hr : route w I.desc id dst with
        | none =>
          simp [hr]
          exact birth_keep_line I.desc (noteStale w id dst) id _ (birth_note I.desc w id dst h)
            (by simpa [noteStale_st] using proceed_lineage (w.st id) (afterHead k))
        | some dstId =>
          simp [hr]
          exact birth_mail I.desc w id dstId { label := label, sender := id, callFrom := none }
            false (afterHead k) h (by simp)
      | trySend dst label hint onFull onGone =>
        cases hr : route w I.desc id dst with
        | none =>
          simp [hr]
          exact birth_keep_line I.desc (noteStale w id dst) id _
            (birth_note I.desc w id dst h)
            (by simpa [noteStale_st] using proceed_lineage (w.st id) _)
        | some dstId =>
          simp only [hr]
          split
          · exact birth_mail I.desc w id dstId
              { label := label, sender := id, callFrom := none, reliable := false }
              false (afterHead k) h (by simp)
          · split
            · exact birth_keep_line I.desc w id _ h (proceed_lineage _ _)
            · exact birth_keep_line I.desc w id _ h (proceed_lineage _ _)
      | call dst label hint onNotAdmitted onTimedOut =>
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp [hr]
          exact birth_keep_line I.desc (noteStale w id dst) id _
            (birth_note I.desc w id dst h)
            (by simpa [noteStale_st] using issue_finish_line (w.st id) _ .notAdmitted)
        | some dstId =>
          simp [hr]
          exact birth_mail I.desc w id dstId
            { label := label, sender := id, callFrom := some id } true _ h (by simp)
      | reply =>
        simp
        exact birth_reply I.desc w id k h
      | selfSchedule label =>
        by_cases hqueued : ((w.st id).prio.any (fun p => p.label == label)) = true
        · simp only [hqueued, ite_true]
          exact birth_keep_line I.desc w id _ h (proceed_lineage _ _)
        · have hqf : ((w.st id).prio.any (fun p => p.label == label)) = false := by
            cases hbb : (w.st id).prio.any (fun p => p.label == label)
            · rfl
            · exact absurd hbb hqueued
          simp only [hqf, ite_false]
          by_cases hroom : prioLoad (w.st id).prio < capPrio I.desc w.N id
          · simp only [hroom, ite_true]
            let msg : Msg :=
              { label := label, sender := id, callFrom := none, reliable := true,
                mid := (w.st id).nextMid }
            refine birth_set I.desc w id _ h ?par (Or.inl ?life) ?box ?park ?prio
            · simpa using (proceed_lineage _ _).2.1
            · simpa using (proceed_lineage _ _).1
            · intro m hm
              rw [(proceed_lineage _ _).2.2.1] at hm
              exact h.plainBox id m hm
            · intro p hp
              rw [(proceed_lineage _ _).2.2.2.2] at hp
              exact h.plainParked id p hp
            · intro m hm
              rw [(proceed_lineage _ _).2.2.2.1] at hm
              exact upsert_from (w.st id).prio msg m (by simp [msg]) hm
          · simp [hroom]
            exact birth_crash I.desc w h
      | cell dst label value =>
        simp only
        let previous := w.cell dst label
        let written := max previous.value value
        let w1 := setCell w dst label { value := written, dirty := true }
        have hst : w1.st = w.st := by simp [w1, setCell]
        have h1 := birth_set_cell I.desc w dst label { value := written, dirty := true } h
        have h2 := birth_keep_line I.desc w1 id (proceed (w1.st id) (afterHead k)) h1
          (by simpa [hst] using proceed_lineage (w.st id) (afterHead k))
        by_cases hdirty : previous.dirty = true
        · simp [previous, written, w1, hdirty]
          exact h2
        · have hdf : previous.dirty = false := by
            cases hb : previous.dirty
            · rfl
            · exact absurd hb hdirty
          simp [previous, written, w1, hdf]
          exact birth_readers I.desc _ dst label id h2
      | internal =>
        simp
        exact birth_keep_line I.desc w id _ h (by simp)
      | peer onTimeout =>
        simp
        exact birth_keep_line I.desc w id _ h (by simp)
      | abort =>
        simp
        exact birth_commit I.desc _ id _ (birth_abort I.desc w id h) (proceed_lineage _ _)
      | spawn child =>
        cases hsp : spawnChild I w id child with
        | none =>
          simp [hsp]
          exact birth_crash I.desc w h
        | some w' =>
          simp [hsp]
          exact birth_commit I.desc w' id _ (birth_spawn_child I hG w w' id child h hO hP hC hsp)
            (proceed_lineage _ _)
      | terminate =>
        have hmem : id ∈ w.roster := hO id (by
          intro habs
          have hliveA : (w.st id).life = .alive := beq_iff_eq.mp hlive
          cases hliveA.symm.trans habs)
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp [ht]
          exact birth_crash I.desc w h
        | some t =>
          simp only [ht]
          by_cases hcore : (t.multiplicity == .one) = true
          · simp [hcore]
            exact birth_crash I.desc w h
          · rw [ite_eq_right hcore]
            by_cases htree : (t.multiplicity == .perPeer && t.subtree != "") = true
            · simp [htree]
              exact birth_terminate I.desc w id (w.st id) h hmem
            · rw [ite_eq_right htree]
              by_cases hlone : (t.terminable && t.subtree == "" &&
                  !hasParkedCall (w.st id).parked && !(hasChild I.desc w id)) = true
              · simp [hlone]
                exact birth_shutdown I.desc w id h (fun _ => hmem)
              · rw [ite_eq_right hlone]
                by_cases hkids : (t.terminable && t.subtree == "" &&
                    !hasParkedCall (w.st id).parked && hasChild I.desc w id) = true
                · simp [hkids]
                  exact birth_terminate I.desc w id (w.st id) h hmem
                · rw [ite_eq_right hkids]
                  exact birth_crash I.desc w h
  · have hlf : ((w.st id).life == .alive) = false := by
      cases hbb : (w.st id).life == .alive
      · rfl
      · exact absurd hbb hlive
    simp only [hlf, ite_false]
    exact h

/-- A step that does not make a new peer alive keeps `PeerRole`. -/
theorem peer_mono (D : Description) (w w' : World) (hP : PeerRole D w)
    (hl : ∀ n k g, (w'.st (InstId.peer n k g)).life = .alive →
      (w.st (InstId.peer n k g)).life = .alive) : PeerRole D w' := by
  intro n k g ha
  exact hP n k g (hl n k g ha)

/-- A step that does not make a new core alive keeps `CoreRole`. -/
theorem core_mono (D : Description) (w w' : World) (hC : CoreRole D w)
    (hl : ∀ n, (w'.st (InstId.core n)).life = .alive → (w.st (InstId.core n)).life = .alive) :
    CoreRole D w' := by
  intro n ha
  exact hC n (hl n ha)

theorem fold_cells_st (D : Description) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun acc id => readCells D acc id) w).st i) = w.st i := by
  revert w
  induction ids with
  | nil =>
    intro w
    rfl
  | cons id ids ih =>
    intro w
    simp only [List.foldl_cons]
    exact (ih (readCells D w id)).trans (cellsSt D w id i)

/-- Workaround `nameSplit`: `Projects.peer_init` is the population fact. -/
theorem peer_role_init (I : Impl) (hG : GraphOk I.desc) (N : Nat) : PeerRole I.desc (initWorld I N) := by
  intro n k g hl
  have hst : (initWorld I N).st (InstId.peer n k g) = absentActor := by
    unfold initWorld
    dsimp only
    rw [fold_cells_st]
    dsimp
    split
    · rename_i hc
      have hmem : InstId.peer n k g ∈ coreRoster I.desc := by simpa [List.elem_iff] using hc
      obtain ⟨_, _, _, hid⟩ := birth_core_template I.desc _ hG hmem
      cases hid
    · rfl
  simp [hst, absentActor] at hl

theorem core_init (I : Impl) (hG : GraphOk I.desc) (N : Nat) : CoreRole I.desc (initWorld I N) := by
  intro name hl
  have hst : (initWorld I N).st (InstId.core name) =
      (if (coreRoster I.desc).contains (InstId.core name) then initActor I.desc (InstId.core name)
        else absentActor) := by
    unfold initWorld
    dsimp only
    rw [fold_cells_st]
  rw [hst] at hl
  split at hl
  · rename_i hc
    have hmem : InstId.core name ∈ coreRoster I.desc := by simpa [List.elem_iff] using hc
    obtain ⟨t, ht, hone, _⟩ := birth_core_template I.desc _ hG hmem
    exact ⟨t, ht, hone⟩
  ·     simp [absentActor] at hl

/-- A reachable core was placed at the start. No step makes a core alive. -/
theorem core_reachable (I : Impl) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : CoreRole I.desc w := by
  induction hR with
  | init => exact core_init I hG N
  | step w w' a _ h ih =>
    intro name hl
    exact ih name (apply_core_prev I w w' a name h hl)

/-- `execHead` runs `execRun` on the stored actor, or does nothing. -/
theorem birth_head (I : Impl) (hG : GraphOk I.desc) (w w' : World) (id : InstId)
    (h : BirthInv I.desc w) (hO : ∀ i, (w.st i).life ≠ .absent → i ∈ w.roster)
    (hP : PeerRole I.desc w) (hC : CoreRole I.desc w) (hex : execHead I w id = some w') :
    BirthInv I.desc w' := by
  unfold execHead at hex
  by_cases hdead : (w.st id).life ≠ .alive
  · simp [hdead] at hex
  · simp only [hdead, ite_false] at hex
    cases hph : (w.st id).phase with
    | run k =>
      simp only [hph] at hex
      cases hex
      exact birth_exec I hG w id (w.st id) k h hO hP hC rfl
    | idle => simp [hph] at hex
    | awaitReply _ _ => simp [hph] at hex
    | awaitEffect _ => simp [hph] at hex
    | awaitPeer _ => simp [hph] at hex
    | parked _ _ _ => simp [hph] at hex
    | crashed => simp [hph] at hex

/-- One enabled action keeps the parent facts. `exec` is `birth_head`.
`PeerRole` and `CoreRole` are what a child birth needs, and a spawn uses
`OpenSlots`. -/
theorem birth_apply (I : Impl) (hG : GraphOk I.desc) (a : Action) (w w' : World)
    (h : BirthInv I.desc w) (hO : ∀ i, (w.st i).life ≠ .absent → i ∈ w.roster)
    (hP : PeerRole I.desc w) (hC : CoreRole I.desc w) (ha : apply I a w = some w') :
    BirthInv I.desc w' := by
  have ⟨_, hstep⟩ := apply_step I a w w' ha
  cases a with
  | recvBulk id =>
    simpa [stepWorld] using birth_bulk I w w' id h hstep
  | recvPrio id =>
    simpa [stepWorld] using birth_prio I w w' id h hstep
  | exec id =>
    simpa [stepWorld] using birth_head I hG w w' id h hO hP hC hstep
  | finish id =>
    simpa [stepWorld] using birth_finish I w w' id h hstep
  | spawn template =>
    simpa [stepWorld] using birth_spawn I hG w w' template h hO hstep
  | ingress dst label =>
    simpa [stepWorld] using birth_ingress I w w' dst label h hstep
  | callTimeout id =>
    simpa [stepWorld] using birth_timeout I.desc w w' id h hstep
  | stutter =>
    simpa [stutter_unchanged I w w' ha] using h

/-- `setActor` keeps every life, so a per-peer peer stays per-peer. -/
theorem peer_set (D : Description) (w : World) (id : InstId) (a : Actor) (hP : PeerRole D w)
    (hl : a.life = (w.st id).life) : PeerRole D (setActor w id a) :=
  peer_mono D w _ hP fun n key gen ha => (setActor_keeps_life w id _ a hl).symm.trans ha

/-- A send or a call stores mail without bringing anyone to life. -/
theorem enqueue_id_life (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).life = (w.st i).life := by
  cases isCall <;>
    (unfold enqueueOrPark
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive]
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor]
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken, issueCall, proceed_keeps_life]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall, proceed_keeps_life]
           · by_cases hid : i = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor]
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken, issueCall]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall]
           · by_cases hid : i = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
     · rw [if_pos hlive]
       by_cases hi : i = sender
       · simp [hi, setActor, issueCall, finishCall, selectCall, proceed_keeps_life]
       · simp [setActor, hi])

/-- A reply resumes one caller and does not bring anyone to life. -/
theorem reply_id_life (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).life = (w.st i).life := by
  unfold performReply
  cases hr : k.replyTo with
  | none =>
    by_cases hi : i = sender
    · rw [hi]; simp [setActor, proceed_keeps_life]
    · simp [setActor, hi]
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · by_cases hm : (w.st sender).oweId = some (w.st caller).waitId
        · by_cases hi : i = sender
          · rw [hi]
            by_cases hsc : sender = caller
            · subst hsc
              simp [setActor, hph, hd, hm, finishCall, proceed]
              split <;> split <;> rfl
            · simp [setActor, hph, hd, hm, hsc, proceed]
              split <;> rfl
          · by_cases hc : i = caller
            · rw [hc]
              have hflip : ¬caller = sender := fun h => hi (hc.trans h)
              simp [setActor, hph, hd, hm, hflip, finishCall, proceed]
              split <;> rfl
            · simp [setActor, hi, hc, hph, hd, hm]
        · by_cases hi : i = sender
          · rw [hi]; simp [setActor, proceed_keeps_life, hph, hd, hm]
          · simp [setActor, hi, hph, hd, hm]
      · by_cases hi : i = sender
        · rw [hi]; simp [setActor, proceed_keeps_life, hph, hd]
        · simp [setActor, hi, hph, hd]
    | idle =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | run _ =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | parked _ _ _ =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | awaitEffect _ =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | awaitPeer _ =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]
    | crashed =>
      by_cases hi : i = sender
      · rw [hi]; simp [setActor, proceed_keeps_life, hph]
      · simp [setActor, hi, hph]

/-- A cell wake that leaves `i` alive did not create that life. -/
theorem tryWake_id_life (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) (h : ((tryWake D w dstId label writer).st i).life = .alive) :
    (w.st i).life = .alive := by
  unfold tryWake offerPrio at h
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip] at h
    exact h
  · have hgo : ((w.st dstId).life != .alive ||
        (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      simpa [Bool.not_eq_true] using hskip
    simp only [hgo, ite_false] at h
    by_cases hfull : decide (prioLoad (w.st dstId).prio >= capPrio D w.N dstId) = true
    · simp only [hfull, ite_true] at h
      exact crashWorld_prev w i h
    · have hroom : decide (prioLoad (w.st dstId).prio >= capPrio D w.N dstId) = false := by
        simpa [Bool.not_eq_true] using hfull
      simp only [hroom, ite_false] at h
      by_cases hi : i = dstId
      · rw [hi] at h ⊢
        simp [setActor] at h
        exact h
      · simpa [setActor, hi] using h

theorem wake_id_life (D : Description) (w : World) (dst label : String) (writer i : InstId)
    (h : ((wakeReaders D w dst label writer).st i).life = .alive) : (w.st i).life = .alive := by
  unfold wakeReaders at h
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w id => tryWake D w id label writer) w0).st i).life = .alive →
      (w0.st i).life = .alive from
    this (readersOf w dst) w h
  intro ids
  induction ids with
  | nil =>
    intro _ h0
    exact h0
  | cons j js ih =>
    intro w0 h0
    rw [List.foldl_cons] at h0
    exact tryWake_id_life D w0 j label writer i (ih _ h0)

/-- Sealing a stage does not bring anyone to life. -/
theorem terminate_prev (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId)
    (h : ((terminateStage D w id a).st i).life = .alive) : (w.st i).life = .alive := by
  unfold terminateStage at h
  exact dropDescendants_prev D w id i (shutdownActor_prev D (dropDescendants D w id) id i h)

/-- The continuation after an effect keeps the lives the effect left. -/
theorem commit_peer (D : Description) (w : World) (id : InstId) (next : Actor) (hP : PeerRole D w)
    (hl : next.life = (w.st id).life) : PeerRole D (commitCont w id next) := by
  unfold commitCont
  split
  · exact hP
  · exact peer_set D w id next hP hl

theorem may_per (D : Description) (w : World) (template : String) (t : Template)
    (h : maySpawnRoot D w template t = true) : t.multiplicity = .perPeer := by
  unfold maySpawnRoot at h
  have h1 := (Bool.and_eq_true _ _).mp h
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact mul_per t h3.1

/-- The peer `placePeer` admits is the template it was given, which is per-peer.
Everyone else keeps the life they had. -/
theorem place_peer_role (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World) (t : Template)
    (hst : ∀ u i, (next u).st i = u.st i) (hP : PeerRole I.desc w)
    (ht : templateOf I.desc template = some t) (hper : t.multiplicity = .perPeer) :
    PeerRole I.desc (placePeer I w template k initial parent next) := by
  intro n key g ha
  let bornId := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  have hstB : (placePeer I w template k initial parent next).st (InstId.peer n key g) =
      (setActor (next { w with roster := w.roster ++ [bornId] }) bornId born).st
        (InstId.peer n key g) := by
    simp [placePeer, bornId, born, cellsSt]
  rw [hstB] at ha
  by_cases hnew : InstId.peer n key g = bornId
  · unfold bornId at hnew
    cases hnew
    exact ⟨t, ht, hper⟩
  · unfold bornId at hnew
    rw [setActor_other _ _ _ born hnew] at ha
    rw [hst] at ha
    exact hP n key g ha

/-- A scheduler birth admits one per-peer root and leaves every other life. -/
theorem spawn_peer_role (I : Impl) (w w' : World) (template : String) (hP : PeerRole I.desc w)
    (h : spawn I w template = some w') : PeerRole I.desc w' := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo : maySpawnRoot I.desc w template t = true
    · simp only [hgo, ite_true] at h
      have hper := may_per I.desc w template t hgo
      cases hsup : t.supervisor with
      | some supName =>
        simp only [hsup] at h
        cases h
        exact place_peer_role I w template (freshKey I.desc w t.subtree) t.initial
          (some (InstId.core supName))
          (fun u => { u with nextKey := fun s =>
            if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
          t (fun _ _ => rfl) hP ht hper
      | none =>
        simp only [hsup] at h
        by_cases hsub : (t.subtree == "") = true
        · simp only [hsub, ite_true] at h
          cases h
          exact place_peer_role I w template (w.nextIx template) t.initial none
            (fun u => { u with nextIx := fun n =>
              if n = template then w.nextIx template + 1 else u.nextIx n })
            t (fun _ _ => rfl) hP ht hper
        · have hsubF : (t.subtree == "") = false := by simpa [Bool.not_eq_true] using hsub
          simp only [hsubF, ite_false] at h
          cases h
          exact place_peer_role I w template (freshKey I.desc w t.subtree) t.initial none
            (fun u => { u with nextKey := fun s =>
              if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            t (fun _ _ => rfl) hP ht hper
    · simp [hgo] at h

/-- A child birth admits one per-peer actor at the parent's key, or changes nothing. -/
theorem spawnChild_peer_role (I : Impl) (w w' : World) (parent : InstId) (child : String)
    (hP : PeerRole I.desc w) (h : spawnChild I w parent child = some w') : PeerRole I.desc w' := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hcond : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
    · rw [hcond] at h
      rw [ite_eq_left (by decide : true = true)] at h
      cases parent with
      | core _ => simp at h
      | peer pname pk pg =>
        dsimp only at h
        by_cases hblock : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = true
        · rw [hblock] at h
          rw [ite_eq_left (by decide : true = true)] at h
          cases h
          exact hP
        · have hblockF : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk
            · rfl
            · exact absurd hbb hblock
          rw [hblockF] at h
          rw [ite_eq_right (by decide : ¬ false = true)] at h
          have hparts := by simpa [Bool.and_eq_true] using hcond
          have hmul := mul_per t hparts.1.1
          injection h with hw
          subst hw
          intro n key g ha
          let bornId := InstId.peer child pk (maxGen w child pk)
          by_cases hnew : InstId.peer n key g = bornId
          · unfold bornId at hnew
            cases hnew
            exact ⟨t, ht, hmul⟩
          · unfold bornId at hnew
            simp [admitBorn, cellsSt, setActor, hnew] at ha
            exact hP n key g ha
    · have hcondF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = false := by
        cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive
        · rfl
        · exact absurd hbb hcond
      rw [hcondF] at h
      rw [ite_eq_right (by decide : ¬ false = true)] at h
      by_cases hcond2 : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · rw [hcond2] at h
        rw [ite_eq_left (by decide : true = true)] at h
        cases h
        exact hP
      · have hcond2F : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)
          · rfl
          · exact absurd hbb hcond2
        rw [hcond2F] at h
        rw [ite_eq_right (by decide : ¬ false = true)] at h
        simp at h

/-- One effect keeps `PeerRole`. The only new life is a per-peer child or root. -/
theorem execRun_peer_role (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hP : PeerRole I.desc w) (hact : a.life = (w.st id).life) :
    PeerRole I.desc (execRun I w id a k) := by
  by_cases hliveB : (a.life == .alive) = true
  · cases hk : k.rest with
    | nil =>
      simp only [execRun, hliveB, hk]
      exact peer_set I.desc w id { a with phase := .idle, typestate := k.toState } hP (by simp [hact])
    | cons e es =>
      cases e with
      | send dst label hint =>
        simp only [execRun, hliveB, hk]
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr]
          exact peer_set I.desc (noteStale w id dst) id (proceed a (afterHead k))
            (peer_mono _ _ _ hP fun n key gen ha => by simpa [noteStale_st] using ha)
            (by simp [noteStale_st, proceed_keeps_life, hact])
        | some dstId =>
          simp only [hr]
          exact peer_mono _ _ _ hP fun n key gen ha =>
            (enqueue_id_life w I.desc id dstId _ false (afterHead k) _).symm.trans ha
      | trySend dst label hint onFull onGone =>
        simp only [execRun, hliveB, hk]
        let goneK :=
          { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone }
        let fullK :=
          { afterHead k with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull }
        intro n key gen ha
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr] at ha
          exact hP n key gen
            ((setActor_keeps_life (noteStale w id dst) id _ (proceed a goneK)
              (by simp [noteStale_st, proceed_keeps_life, hact, goneK])).symm.trans ha)
        | some dstId =>
          simp only [hr] at ha
          generalize hadm : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
            decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = admitted at ha
          by_cases hcond : admitted = true
          · simp only [hcond, ite_true] at ha
            exact hP n key gen
              ((enqueue_id_life w I.desc id dstId _ false (afterHead k) _).symm.trans ha)
          · have hcondF : admitted = false := by
              cases hbb : admitted
              · rfl
              · exact absurd hbb hcond
            simp only [hcondF, ite_false] at ha
            by_cases halive : ((w.st dstId).life == .alive) = true
            · simp only [halive, ite_true] at ha
              exact hP n key gen
                ((setActor_keeps_life w id _ (proceed a fullK)
                  (by simp [proceed_keeps_life, hact, fullK])).symm.trans ha)
            · have haliveF : ((w.st dstId).life == .alive) = false := by
                cases hbb : (w.st dstId).life == .alive
                · rfl
                · exact absurd hbb halive
              simp only [haliveF, ite_false] at ha
              exact hP n key gen
                ((setActor_keeps_life w id _ (proceed a goneK)
                  (by simp [proceed_keeps_life, hact, goneK])).symm.trans ha)
      | call dst label hint onNotAdmitted onTimedOut =>
        simp only [execRun, hliveB, hk]
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp only [hr]
          exact peer_set I.desc (noteStale w id dst) id
            (finishCall (issueCall a)
              { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
              .notAdmitted)
            (peer_mono _ _ _ hP fun n key gen ha => by simpa [noteStale_st] using ha)
            (by simp [noteStale_st, finishCall_life, issueCall, hact])
        | some dstId =>
          simp only [hr]
          exact peer_mono _ _ _ hP fun n key gen ha =>
            (enqueue_id_life w I.desc id dstId _ true
              { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut } _).symm.trans ha
      | reply =>
        simp only [execRun, hliveB, hk]
        exact peer_mono _ _ _ hP fun n key gen ha => (reply_id_life w id k _).symm.trans ha
      | selfSchedule label =>
        simp only [execRun, hliveB, hk]
        intro n key gen ha
        by_cases hdup : (a.prio.any (fun p => p.label == label)) = true
        · simp only [hdup, ite_true] at ha
          exact hP n key gen
            ((setActor_keeps_life w id _ (proceed a (afterHead k))
              (by simp [proceed_keeps_life, hact])).symm.trans ha)
        · have hdupF : (a.prio.any (fun p => p.label == label)) = false := by
            cases hbb : a.prio.any (fun p => p.label == label)
            · rfl
            · exact absurd hbb hdup
          simp only [hdupF, ite_false] at ha
          by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
          · simp only [hroom, ite_true] at ha
            exact hP n key gen
              ((setActor_keeps_life w id _
                (proceed { a with
                  prio := upsertPrio a.prio
                    { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid },
                  nextMid := a.nextMid + 1 } (afterHead k))
                (by simp [proceed_keeps_life, hact])).symm.trans ha)
          · simp only [hroom, ite_false] at ha
            exact hP n key gen (crashWorld_prev w _ ha)
      | cell dst label value =>
        simp only [execRun, hliveB, hk]
        let c : Cell := { value := max (w.cell dst label).value value, dirty := true }
        intro n key gen ha
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp only [hdirty, ite_true, c] at ha
          exact hP n key gen
            ((setActor_keeps_life (setCell w dst label c) id _
              (proceed ((setCell w dst label c).st id) (afterHead k))
              (by simp [setCell, proceed_keeps_life])).symm.trans ha)
        · have hdirtyF : (w.cell dst label).dirty = false := by
            cases hbb : (w.cell dst label).dirty
            · rfl
            · exact absurd hbb hdirty
          simp only [hdirtyF, ite_false, c] at ha
          exact hP n key gen (by
            simpa [setCell] using
              (setActor_keeps_life (setCell w dst label c) id _
                (proceed ((setCell w dst label c).st id) (afterHead k))
                (by simp [setCell, proceed_keeps_life])).symm.trans
                (wake_id_life I.desc _ dst label id _ ha))
      | internal =>
        simp only [execRun, hliveB, hk]
        exact peer_set I.desc w id { a with phase := .awaitEffect (afterHead k) } hP (by simp [hact])
      | peer _ =>
        simp only [execRun, hliveB, hk]
        exact peer_set I.desc w id { a with phase := .awaitPeer _ } hP (by simp [hact])
      | abort =>
        simp only [execRun, hliveB, hk]
        exact commit_peer I.desc (abortChildren I.desc w id) id
          (proceed ((abortChildren I.desc w id).st id) (afterHead k))
          (peer_mono _ _ _ hP fun n key gen ha => abortChildren_prev I.desc w id _ ha)
          (by simp [proceed_keeps_life])
      | spawn child =>
        simp only [execRun, hliveB, hk]
        cases hs : spawnChild I w id child with
        | none =>
          simp only [hs]
          exact peer_mono _ _ _ hP fun n key gen ha => crashWorld_prev w _ ha
        | some w' =>
          simp only [hs]
          exact commit_peer I.desc w' id (proceed (w'.st id) (afterHead k))
            (spawnChild_peer_role I w w' id child hP hs) (by simp [proceed_keeps_life])
      | terminate =>
        have hliveA : a.life = .alive := by simpa [beq_iff_eq] using hliveB
        have hstep := exec_term_step I w id a k hliveA ⟨es, hk⟩
        revert hstep
        generalize hw : execRun I w id a k = wR
        intro hstep
        cases hstep with
        | fall =>
          exact peer_mono _ _ _ hP fun n key gen ha => crashWorld_prev w _ ha
        | crash _ _ _ =>
          exact peer_mono _ _ _ hP fun n key gen ha => crashWorld_prev w _ ha
        | lone _ _ _ _ _ _ _ =>
          exact peer_mono _ _ _ hP fun n key gen ha => shutdownActor_prev I.desc w id _ ha
        | tree _ _ _ _ =>
          exact peer_mono _ _ _ hP fun n key gen ha => terminate_prev I.desc w id a _ ha
        | cascade _ _ _ _ _ _ _ =>
          exact peer_mono _ _ _ hP fun n key gen ha => terminate_prev I.desc w id a _ ha
  · have hlf : (a.life == .alive) = false := by
      cases hbb : a.life == .alive
      · rfl
      · exact absurd hbb hliveB
    simp only [execRun, hlf]
    exact hP

/-- An enabled step keeps `PeerRole`. -/
theorem peer_apply (I : Impl) (w w' : World) (a : Action) (hP : PeerRole I.desc w)
    (h : apply I a w = some w') : PeerRole I.desc w' := by
  have ⟨_, hstep⟩ := apply_step I a w w' h
  cases a with
  | recvBulk id =>
    simpa [stepWorld] using peer_mono _ _ _ hP fun n key gen ha =>
      (receiveBulk_keeps_life I w w' id _ (by simpa [stepWorld] using hstep)).symm.trans ha
  | recvPrio id =>
    exact peer_mono _ _ _ hP fun n key gen ha =>
      (receivePrio_keeps_life I w w' id _ (by simpa [stepWorld] using hstep)).symm.trans ha
  | exec id =>
    have hhead : execHead I w id = some w' := by simpa [stepWorld] using hstep
    unfold execHead at hhead
    by_cases hlive : (w.st id).life = .alive
    · simp only [hlive, ite_false] at hhead
      cases hph : (w.st id).phase with
      | run k =>
        simp only [hph] at hhead
        cases hhead
        exact execRun_peer_role I w id (w.st id) k hP rfl
      | idle => simp [hph] at hhead
      | parked _ _ _ => simp [hph] at hhead
      | awaitReply _ _ => simp [hph] at hhead
      | awaitEffect _ => simp [hph] at hhead
      | awaitPeer _ => simp [hph] at hhead
      | crashed => simp [hph] at hhead
    · simp [hlive] at hhead
  | finish id =>
    obtain ⟨k, _, hw⟩ := finish_proceed I w w' id (by simpa [stepWorld] using hstep)
    rw [hw]
    exact peer_set I.desc w id (proceed (w.st id) k) hP (by simp [proceed_keeps_life])
  | spawn template =>
    exact spawn_peer_role I w w' template hP (by simpa [stepWorld] using hstep)
  | ingress dst label =>
    exact peer_mono _ _ _ hP fun n key gen ha =>
      ((ingress_phase I w w' dst label _ (by simpa [stepWorld] using hstep)).2.1).symm.trans ha
  | callTimeout id =>
    exact peer_mono _ _ _ hP fun n key gen ha =>
      (callTimeout_life w w' id _ (by simpa [stepWorld] using hstep)).symm.trans ha
  | stutter =>
    have hstep := hstep
    simp [stepWorld] at hstep
    cases hstep.2
    exact hP

/-- A reachable peer was born per-peer. The initial world has no live peer.
Workaround `nameSplit`: `Projects.peer_reachable` is the population fact. -/
theorem peer_role_reachable (I : Impl) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : PeerRole I.desc w := by
  induction hR with
  | init => exact peer_role_init I hG N
  | step w w' a _ h ih =>
    exact peer_apply I w w' a ih h

/-- A child birth leaves every phase as it was, except the admitted actor, which
is idle. A blocked or refused spawn changes nothing. -/
theorem spawnChild_phase (I : Impl) (w w' : World) (parent : InstId) (child : String) (i : InstId)
    (h : spawnChild I w parent child = some w') :
    (w'.st i).phase = (w.st i).phase ∨ (w'.st i).phase = .idle := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hcond : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
    · rw [hcond] at h
      rw [ite_eq_left (by decide : true = true)] at h
      cases parent with
      | core _ => simp at h
      | peer pname pk pg =>
        dsimp only at h
        by_cases hblock : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = true
        · rw [hblock] at h
          rw [ite_eq_left (by decide : true = true)] at h
          cases h
          exact Or.inl rfl
        · have hblockF : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = false := by
            cases hbb : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk
            · rfl
            · exact absurd hbb hblock
          rw [hblockF] at h
          rw [ite_eq_right (by decide : ¬ false = true)] at h
          injection h with hw
          subst hw
          let bornId := InstId.peer child pk (maxGen w child pk)
          by_cases hnew : i = bornId
          · unfold bornId at hnew
            cases hnew
            exact Or.inr (by simp [admitBorn, cellsSt, setActor, bornActor, withKeyTokens])
          · unfold bornId at hnew
            exact Or.inl (by simp [admitBorn, cellsSt, setActor, hnew])
    · have hcondF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = false := by
        cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive
        · rfl
        · exact absurd hbb hcond
      rw [hcondF] at h
      rw [ite_eq_right (by decide : ¬ false = true)] at h
      by_cases hcond2 : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · rw [hcond2] at h
        rw [ite_eq_left (by decide : true = true)] at h
        cases h
        exact Or.inl rfl
      · have hcond2F : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hbb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)
          · rfl
          · exact absurd hbb hcond2
        rw [hcond2F] at h
        rw [ite_eq_right (by decide : ¬ false = true)] at h
        simp at h

end Deadlock
