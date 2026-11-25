import Deadlock.Inv2

set_option autoImplicit false

namespace Deadlock

/-! A priority tombstone on a reachable world is the message `enqueueTombstone`
built for a peer. Its base label is the child template's `tombstone`, and
`tombstoneHandled` — not `labelHandled` — puts a transition on that label in
every state of the supervisor. `deliver` therefore finds a handler for a
current tombstone. An older generation is dropped before the lookup. A waiting
tombstone is skipped, so a receive still needs some message that is not waiting. -/

def ShapedTomb (D : Description) (m : Msg) : Prop :=
  ∃ n k g t,
    m.sender = InstId.peer n k g ∧
    templateOf D n = some t ∧
    t.tombstone ≠ "" ∧
    m.baseLabel = t.tombstone ∧
    m.label = tombstoneLabel D (InstId.peer n k g) ∧
    m.callFrom = none

def TombShape (D : Description) (w : World) : Prop :=
  ∀ host m, m ∈ (w.st host).prio → m.tombstone = true → ShapedTomb D m

def CoreRoot (w : World) : Prop :=
  ∀ name, (w.st (.core name)).parent = none

structure ShapeRoot (D : Description) (w : World) : Prop where
  shape : TombShape D w
  root : CoreRoot w

theorem ts_bool_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

theorem ts_if_pos {α : Type} (b : Bool) (x y : α) (h : b = true) :
    (if b then x else y) = x := by
  cases b <;> simp_all

theorem ts_if_neg {α : Type} (b : Bool) (x y : α) (h : ¬ b = true) :
    (if b then x else y) = y := by
  cases b <;> simp_all

theorem ts_root {w w' : World} (h : CoreRoot w)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent) : CoreRoot w' := by
  intro name
  rw [hp (.core name)]
  exact h name

theorem ts_st (D : Description) {w w' : World} (h : ShapeRoot D w)
    (hst : ∀ i, w'.st i = w.st i) : ShapeRoot D w' := by
  refine ⟨?_, ?_⟩
  · intro host m hm ht
    rw [hst host] at hm
    exact h.shape host m hm ht
  · intro name
    rw [hst (.core name)]
    exact h.root name

theorem ts_frame (D : Description) {w w' : World} (h : ShapeRoot D w)
    (hp : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) : ShapeRoot D w' := by
  refine ⟨?_, ts_root h.root hpar⟩
  · intro host m hm ht
    rw [hp host] at hm
    exact h.shape host m hm ht

theorem ts_keep (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : ShapeRoot D w) (hp : a.prio = (w.st id).prio) (hpar : a.parent = (w.st id).parent) :
    ShapeRoot D (setActor w id a) := by
  refine ⟨?_, ts_root h.root (fun i => setActor_parent_keep w id a i hpar)⟩
  · intro host m hm ht
    by_cases hh : host = id
    · rw [hh] at hm
      rw [setActor_self, hp] at hm
      exact h.shape id m hm ht
    · rw [setActor_other w id host a hh] at hm
      exact h.shape host m hm ht

theorem ts_crash_prio (w : World) (i : InstId) : ((crashWorld w).st i).prio = (w.st i).prio := by
  simp only [crashWorld]
  by_cases hm : decide (i ∈ w.roster) = true
  · simp only [hm, ite_true, crashActor]
    split <;> simp
  · simp [hm]

theorem ts_crash (D : Description) (w : World) (h : ShapeRoot D w) :
    ShapeRoot D (crashWorld w) :=
  ts_frame D h (ts_crash_prio w) (crashWorld_parent w)

theorem ts_init_st (I : Impl) (N : Nat) (id : InstId) :
    (initWorld I N).st id =
      if (coreRoster I.desc).contains id then initActor I.desc id else absentActor := by
  unfold initWorld
  dsimp only
  rw [fold_cells_st I.desc (coreRoster I.desc) _ id]

theorem ts_init (I : Impl) (N : Nat) : ShapeRoot I.desc (initWorld I N) := by
  refine ⟨?_, ?_⟩
  · intro host m hm _
    rw [ts_init_st] at hm
    split at hm
    · unfold initActor at hm
      split at hm
      · simp [withTokens, tname] at hm
      · simp [absentActor] at hm
    · simp [absentActor] at hm
  · intro name
    rw [ts_init_st]
    split
    · unfold initActor
      split <;> simp [withTokens, absentActor]
    · simp [absentActor]

theorem ts_msg (D : Description) (a : Actor) (n : String) (k g : Nat)
    (h : (tombstoneMsg D a (InstId.peer n k g)).label ≠ "") :
    ShapedTomb D (tombstoneMsg D a (InstId.peer n k g)) := by
  cases ht : templateOf D n with
  | none =>
    exfalso
    simp [tombstoneMsg, tombstoneLabel, tname, ht] at h
  | some t =>
    have hne : t.tombstone ≠ "" := by
      intro heq
      simp [tombstoneMsg, tombstoneLabel, tname, ht, heq] at h
    refine ⟨n, k, g, t, ?_, ht, hne, ?_, ?_, ?_⟩
    · simp [tombstoneMsg]
    · simp [tombstoneMsg, tname, ht]
    · simp [tombstoneMsg]
    · simp [tombstoneMsg]

theorem ts_offer (D : Description) (w : World) (host : InstId) (msg : Msg)
    (h : ShapeRoot D w) (hmsg : msg.tombstone = true → ShapedTomb D msg) :
    ShapeRoot D (offerPrio D w host msg) := by
  unfold offerPrio
  dsimp
  by_cases hfull : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = true
  · rw [ts_if_pos _ _ _ hfull]
    exact ts_crash D w h
  · rw [ts_if_neg _ _ _ hfull]
    let grown := ({ (w.st host) with prio := (w.st host).prio ++ [msg], nextMid := (w.st host).nextMid + 1 })
    refine ⟨?_, ts_root h.root (fun i => setActor_parent_keep w host grown i rfl)⟩
    intro host' m hm ht
    by_cases hh : host' = host
    · rw [hh] at hm
      rw [setActor_self] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h.shape host m hm ht
      · simp only [List.mem_singleton] at hm
        subst hm
        exact hmsg ht
    · rw [setActor_other w host host' grown hh] at hm
      exact h.shape host' m hm ht

theorem ts_release_prio (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).prio = [] := by
  simp only [releaseWorld]
  rw [(releaseParked_prio _ id a.parked id).1]
  simp [setActor]

theorem ts_release (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : ShapeRoot D w) : ShapeRoot D (releaseWorld D w id a) := by
  refine ⟨?_, ts_root h.root (releaseWorld_parent D w id a)⟩
  · intro host m hm ht
    by_cases hh : host = id
    · subst hh
      rw [ts_release_prio] at hm
      cases hm
    · rw [(releaseWorld_prio D w id a host hh).1] at hm
      exact h.shape host m hm ht

theorem ts_enqueue (D : Description) (w : World) (child : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (enqueueTombstone D w child) := by
  cases hpar : (w.st child).parent with
  | none =>
    simp [enqueueTombstone, hpar]
    exact h
  | some parent =>
    cases child with
    | core name =>
      have hnone := h.root name
      rw [hpar] at hnone
      cases hnone
    | peer n k g =>
      simp only [enqueueTombstone, hpar]
      by_cases hlive : ((w.st parent).life != .alive) = true
      · simp only [hlive, ite_true]
        exact h
      · simp only [ts_bool_false hlive, ite_false]
        by_cases hlab : ((tombstoneMsg D (w.st parent) (InstId.peer n k g)).label == "") = true
        · simp only [hlab, ite_true]
          exact ts_crash D w h
        · simp only [ts_bool_false hlab, ite_false]
          have hne : (tombstoneMsg D (w.st parent) (InstId.peer n k g)).label ≠ "" := by
            intro heq
            exact hlab (by simpa [beq_iff_eq] using heq)
          exact ts_offer D w parent (tombstoneMsg D (w.st parent) (InstId.peer n k g)) h
            (fun _ => ts_msg D (w.st parent) n k g hne)

theorem ts_seal (fuel : Nat) (D : Description) :
    ∀ (w : World) (id : InstId), ShapeRoot D w → ShapeRoot D (sealBranch fuel D w id) := by
  induction fuel with
  | zero =>
    intro w id h
    simpa [sealBranch] using h
  | succ fuel ih =>
    intro w id h
    simp only [sealBranch]
    let step (acc : World) (child : InstId) : World :=
      if isChild acc id child then sealBranch fuel D acc child else acc
    have hfold : ∀ (ids : List InstId) (w0 : World), ShapeRoot D w0 →
        ShapeRoot D (ids.foldl step w0) := by
      intro ids
      induction ids with
      | nil =>
        intro w0 h0
        simpa using h0
      | cons c cs ihc =>
        intro w0 h0
        simp only [List.foldl_cons, step]
        by_cases hc : isChild w0 id c = true
        · simp only [hc, ite_true]
          exact ihc _ (ih w0 c h0)
        · simp only [show isChild w0 id c = false from ts_bool_false hc, ite_false]
          exact ihc _ h0
    have hsealed : ShapeRoot D (w.roster.foldl step w) := hfold w.roster w h
    by_cases hl : (((w.roster.foldl step w).st id).life == .alive) = true
    · rw [ts_if_pos _ _ _ hl]
      exact ts_release D (w.roster.foldl step w) id ((w.roster.foldl step w).st id) hsealed
    · rw [ts_if_neg _ _ _ hl]
      exact hsealed

theorem ts_drop (D : Description) (w : World) (id : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (dropDescendants D w id) := by
  unfold dropDescendants
  suffices ∀ (ids : List InstId) (w0 : World), ShapeRoot D w0 →
      ShapeRoot D (ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch w.roster.length D acc child else acc) w0) from
    this w.roster w h
  intro ids
  induction ids with
  | nil =>
    intro w0 h0
    simpa using h0
  | cons c cs ih =>
    intro w0 h0
    simp only [List.foldl_cons]
    by_cases hc : isChild w0 id c = true
    · simp only [hc, ite_true]
      exact ih _ (ts_seal _ D w0 c h0)
    · simp only [show isChild w0 id c = false from ts_bool_false hc, ite_false]
      exact ih _ h0

theorem ts_shutdown (D : Description) (w : World) (id : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (shutdownActor D w id) := by
  unfold shutdownActor
  by_cases hl : ((w.st id).life == .alive) = true
  · simp only [hl, ite_true]
    exact ts_enqueue D (releaseWorld D w id (w.st id)) id
      (ts_release D w id (w.st id) h)
  · simp only [show ((w.st id).life == .alive) = false from ts_bool_false hl, ite_false]
    exact h

theorem ts_terminate (D : Description) (w : World) (id : InstId) (a : Actor)
    (h : ShapeRoot D w) : ShapeRoot D (terminateStage D w id a) := by
  simp only [terminateStage]
  exact ts_shutdown D (dropDescendants D w id) id (ts_drop D w id h)

theorem ts_abort (D : Description) (w : World) (parent : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (abortChildren D w parent) := by
  unfold abortChildren
  suffices ∀ (ids : List InstId) (w0 : World), ShapeRoot D w0 →
      ShapeRoot D (ids.foldl (fun acc child =>
        if isChild acc parent child && (acc.st child).life == .alive then
          shutdownActor D (dropDescendants D acc child) child
        else acc) w0) from
    this w.roster w h
  intro ids
  induction ids with
  | nil =>
    intro w0 h0
    simpa using h0
  | cons c cs ih =>
    intro w0 h0
    simp only [List.foldl_cons]
    by_cases hc : (isChild w0 parent c && (w0.st c).life == .alive) = true
    · simp only [hc, ite_true]
      exact ih _ (ts_shutdown D (dropDescendants D w0 c) c (ts_drop D w0 c h0))
    · simp only [show (isChild w0 parent c && (w0.st c).life == .alive) = false from
        ts_bool_false hc, ite_false]
      exact ih _ h0

theorem ts_note (D : Description) (w : World) (s : InstId) (dst : String) (h : ShapeRoot D w) :
    ShapeRoot D (noteStale w s dst) :=
  ts_st D h (fun i => noteStale_st w s dst i)

theorem ts_mail (D : Description) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (h : ShapeRoot D w) :
    ShapeRoot D (enqueueOrPark w D sender dst msg isCall k) :=
  ts_frame D h (enqueue_prio w D sender dst msg isCall k)
    (enqueue_parent w D sender dst msg isCall k)

theorem ts_credit (D : Description) (w : World) (tmpl : String) (sender : InstId)
    (h : ShapeRoot D w) : ShapeRoot D (creditSender w tmpl sender) := by
  unfold creditSender
  exact ts_keep D w sender (bumpToken (w.st sender) tmpl (.ofNat 1)) h
    (bump_lineage _ _ _).2.2.2.1 (bump_lineage _ _ _).2.1

theorem ts_live (D : Description) (w : World) (tmpl : String) (sender : InstId)
    (h : ShapeRoot D w) : ShapeRoot D (creditLive w tmpl sender) :=
  ts_credit D w tmpl (budgetHolder w sender) h

theorem ts_commit (D : Description) (w : World) (id : InstId) (next : Actor)
    (h : ShapeRoot D w) (hp : next.prio = (w.st id).prio) (hpar : next.parent = (w.st id).parent) :
    ShapeRoot D (commitCont w id next) := by
  unfold commitCont
  cases hcr : w.crashed with
  | true =>
    simp [hcr]
    exact h
  | false =>
    simp [hcr]
    exact ts_keep D w id next h hp hpar

theorem ts_self (D : Description) (w : World) (id : InstId) (msg : Msg) (k : Cont)
    (h : ShapeRoot D w) (hplain : msg.tombstone = false) :
    ShapeRoot D (setActor w id (proceed
      ({ (w.st id) with prio := upsertPrio (w.st id).prio msg, nextMid := (w.st id).nextMid + 1 }) k)) := by
  let grown := ({ (w.st id) with prio := upsertPrio (w.st id).prio msg, nextMid := (w.st id).nextMid + 1 })
  let a1 := proceed grown k
  refine ⟨?_, ts_root h.root (fun i => setActor_parent_keep w id a1 i ?_)⟩
  · intro host m hm ht
    by_cases hh : host = id
    · rw [hh] at hm
      rw [setActor_self, proceed_keeps_prio] at hm
      change m ∈ upsertPrio (w.st id).prio msg at hm
      rcases upsert_mem _ msg m hm with hm | rfl
      · exact h.shape id m hm ht
      · rw [ht] at hplain
        cases hplain
    · rw [setActor_other w id host a1 hh] at hm
      exact h.shape host m hm ht
  · rw [(proceed_lineage _ k).2.1]

theorem ts_try (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (h : ShapeRoot D w) : ShapeRoot D (tryWake D w dstId label writer) := by
  unfold tryWake
  dsimp only
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp only [hskip, ite_true]
    exact h
  · rw [ts_if_neg _ _ _ hskip]
    let wake : Msg := { label := label, sender := writer, callFrom := none, reliable := false, mid := (w.st dstId).nextMid }
    have htomb : wake.tombstone = false := rfl
    exact ts_offer D w dstId wake h (fun ht => by rw [htomb] at ht; cases ht)

theorem ts_wake_ids (D : Description) (ids : List InstId) (w : World) (dst label : String)
    (writer : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (ids.foldl (fun acc id => tryWake D acc id label writer) w) := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (ts_try D w i label writer h)

theorem ts_readers (D : Description) (w : World) (dst label : String) (writer : InstId)
    (h : ShapeRoot D w) : ShapeRoot D (wakeReaders D w dst label writer) := by
  unfold wakeReaders readersOf
  exact ts_wake_ids D _ w dst label writer h

theorem ts_reply (D : Description) (w : World) (sender : InstId) (k : Cont)
    (h : ShapeRoot D w) : ShapeRoot D (performReply w sender k) := by
  unfold performReply
  dsimp only
  cases hr : k.replyTo with
  | none =>
    simp [hr]
    exact ts_keep D w sender (proceed (w.st sender) (afterHead k)) h
      (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
  | some caller =>
    simp only [hr]
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hmatch : (dst = sender && (w.st sender).oweId = some (w.st caller).waitId) = true
      · simp only [hph, hmatch, ite_true]
        let w1 := setActor w caller (finishCall (w.st caller) ck .reply)
        have hcaller := ts_keep D w caller (finishCall (w.st caller) ck .reply) h
          (finish_lineage _ _ _).2.2.2.1 (finish_lineage _ _ _).2.1
        exact ts_keep D w1 sender (proceed (w1.st sender) (afterHead k)) hcaller
          (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
      · simp only [hph, ts_bool_false hmatch, ite_false]
        exact ts_keep D w sender (proceed (w.st sender) (afterHead k)) h
          (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | idle =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | run _ =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | awaitEffect _ =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | awaitPeer _ =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | parked _ _ _ =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | crashed =>
      simp [hph]
      exact ts_keep D w sender _ h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1

theorem ts_admit (I : Impl) (w : World) (id : InstId) (a : Actor) (h : ShapeRoot I.desc w)
    (hp : a.prio = []) (hnot : ∀ name, id ≠ InstId.core name) :
    ShapeRoot I.desc (admitBorn I w id a) := by
  unfold admitBorn
  let base := { w with roster := w.roster ++ [id] }
  have hbase : ShapeRoot I.desc base := ts_st I.desc h (fun _ => rfl)
  have hset : ShapeRoot I.desc (setActor base id a) := by
    refine ⟨?_, ?_⟩
    · intro host m hm ht
      by_cases hh : host = id
      · rw [hh] at hm
        rw [setActor_self, hp] at hm
        simp at hm
      · rw [setActor_other base id host a hh] at hm
        exact hbase.shape host m hm ht
    · intro name
      by_cases hh : InstId.core name = id
      · exact absurd hh.symm (hnot name)
      · rw [setActor_other base id (.core name) a hh]
        exact hbase.root name
  exact ts_st I.desc hset (fun i => cellsSt I.desc (setActor base id a) id i)

theorem ts_place (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World) (h : ShapeRoot I.desc w)
    (hn : ∀ w0 i, (next w0).st i = w0.st i) :
    ShapeRoot I.desc (placePeer I w template k initial parent next) := by
  unfold placePeer
  dsimp
  let id := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  let base := next { w with roster := w.roster ++ [id] }
  have hbase : ShapeRoot I.desc base :=
    ts_st I.desc (ts_st I.desc h (fun _ => rfl)) (hn _)
  have hp : born.prio = [] := by simp [born, bornActor, withKeyTokens]
  have hset : ShapeRoot I.desc (setActor base id born) := by
    refine ⟨?_, ?_⟩
    · intro host m hm ht
      by_cases hh : host = id
      · rw [hh] at hm
        rw [setActor_self, hp] at hm
        simp at hm
      · rw [setActor_other base id host born hh] at hm
        exact hbase.shape host m hm ht
    · intro name
      by_cases hh : InstId.core name = id
      · exact absurd hh.symm (fun heq => by nomatch heq)
      · rw [setActor_other base id (.core name) born hh]
        exact hbase.root name
  exact ts_st I.desc hset (fun i => cellsSt I.desc (setActor base id born) id i)

theorem ts_spawn_child (I : Impl) (w w' : World) (parent : InstId) (child : String)
    (h : ShapeRoot I.desc w) (hw : spawnChild I w parent child = some w') :
    ShapeRoot I.desc w' := by
  unfold spawnChild at hw
  cases htemp : templateOf I.desc child with
  | none => simp [htemp] at hw
  | some t =>
    simp only [htemp] at hw
    by_cases hgo : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
    · cases parent with
      | core _ =>
        simp only [hgo, ite_true] at hw
        simp at hw
      | peer n k g =>
        simp only [hgo, ite_true] at hw
        by_cases hblock : slotRespawnBlocked I.desc w (.peer n k g) child k = true
        · simp only [hblock, ite_true] at hw
          cases hw
          exact h
        · simp only [ts_bool_false hblock] at hw
          cases hw
          exact ts_admit I w (InstId.peer child k (maxGen w child k))
            { bornActor I.desc w child k t.initial with parent := some (.peer n k g) } h
            (by rfl) (fun name heq => by nomatch heq)
    · simp only [ts_bool_false hgo, ite_false] at hw
      by_cases hrest : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hrest, ite_true] at hw
        cases hw
        exact h
      · simp only [ts_bool_false hrest, ite_false] at hw
        simp at hw

theorem ts_spawn (I : Impl) (w w' : World) (template : String) (h : ShapeRoot I.desc w)
    (hw : spawn I w template = some w') : ShapeRoot I.desc w' := by
  unfold spawn at hw
  cases ht : templateOf I.desc template with
  | none => simp [ht] at hw
  | some t =>
    simp only [ht] at hw
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at hw
      cases hsup : t.supervisor with
      | some name =>
        simp only [hsup] at hw
        let k := freshKey I.desc w t.subtree
        cases hw
        exact ts_place I w template k t.initial (some (.core name))
          (fun w0 => { w0 with nextKey := fun s => if s = t.subtree then k + 1 else w0.nextKey s })
          h (fun _ _ => rfl)
      | none =>
        simp only [hsup] at hw
        by_cases hsub : (t.subtree == "") = true
        · simp only [hsub, ite_true] at hw
          let k := w.nextIx template
          cases hw
          exact ts_place I w template k t.initial none
            (fun w0 => { w0 with nextIx := fun n => if n = template then k + 1 else w0.nextIx n })
            h (fun _ _ => rfl)
        · simp only [ts_bool_false hsub, ite_false] at hw
          let k := freshKey I.desc w t.subtree
          cases hw
          exact ts_place I w template k t.initial none
            (fun w0 => { w0 with nextKey := fun s => if s = t.subtree then k + 1 else w0.nextKey s })
            h (fun _ _ => rfl)
    · simp [hmay] at hw

theorem ts_resume (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).prio = a.prio ∧ (resumeSender a isCall dst).parent = a.parent := by
  unfold resumeSender
  split
  · split
    · exact ⟨rfl, rfl⟩
    · exact ⟨proceed_keeps_prio _ _, (proceed_lineage _ _).2.1⟩
  · exact ⟨rfl, rfl⟩

theorem ts_resume_at (D : Description) (w : World) (sender : InstId) (isCall : Bool) (dst : InstId)
    (h : ShapeRoot D w) :
    ShapeRoot D (setActor w sender (resumeSender (w.st sender) isCall dst)) :=
  ts_keep D w sender (resumeSender (w.st sender) isCall dst) h
    (ts_resume _ _ _).1 (ts_resume _ _ _).2

theorem ts_install (D : Description) (w w1 : World) (id : InstId) (a1 : Actor)
    (h : ShapeRoot D w) (hst : ∀ i, w1.st i = w.st i)
    (hp : a1.prio = (w.st id).prio) (hpar : a1.parent = (w.st id).parent) :
    ShapeRoot D (setActor w1 id a1) := by
  exact ts_keep D w1 id a1 (ts_st D h hst) (by rw [hp, hst id]) (by rw [hpar, hst id])

theorem ts_bulk (I : Impl) (w w' : World) (id : InstId) (h : ShapeRoot I.desc w)
    (hr : receiveBulk I w id = some w') : ShapeRoot I.desc w' := by
  unfold receiveBulk at hr
  dsimp at hr
  split at hr
  · simp at hr
  · cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at hr
      | cons p ps =>
        simp only [hbox, hpark] at hr
        cases hd : deliver I w id ({ (w.st id) with parked := ps }) p.msg with
        | none =>
          simp only [hbox] at hd
          rw [hd] at hr
          simp at hr
        | some pair =>
          obtain ⟨w1, a1⟩ := pair
          simp only [hbox] at hd
          rw [hd] at hr
          obtain ⟨_, hpA, _, hparA, _, _, _, _, hst⟩ :=
            deliver_frame I w id _ p.msg w1 a1 hd
          have hset := ts_install I.desc w w1 id a1 h hst hpA hparA
          have hcred := ts_live I.desc _ (tname id) p.msg.sender hset
          have hw' : w' = setActor (creditLive (setActor w1 id a1) (tname id) p.msg.sender) p.sender
              (resumeSender ((creditLive (setActor w1 id a1) (tname id) p.msg.sender).st p.sender)
                p.isCall id) := by simpa [Option.some.injEq] using hr.symm
          rw [hw']
          exact ts_resume_at I.desc _ p.sender p.isCall id hcred
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp only [hbox, hpark] at hr
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at hr
          simp at hr
        | some pair =>
          obtain ⟨w1, a1⟩ := pair
          simp only [hpark] at hd
          rw [hd] at hr
          obtain ⟨_, hpA, _, hparA, _, _, _, _, hst⟩ :=
            deliver_frame I w id _ m w1 a1 hd
          have hset := ts_install I.desc w w1 id a1 h hst hpA hparA
          have hw' : w' = creditLive (setActor w1 id a1) (tname id) m.sender := by
            simpa [Option.some.injEq] using hr.symm
          rw [hw']
          exact ts_live I.desc _ (tname id) m.sender hset
      | cons p ps =>
        simp only [hbox, hpark] at hr
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at hr
          simp at hr
        | some pair =>
          obtain ⟨w1, a1⟩ := pair
          simp only [hpark] at hd
          rw [hd] at hr
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          obtain ⟨_, hpA, _, hparA, _, _, _, _, hst⟩ :=
            deliver_frame I w id _ m w1 a1 hd
          have hset := ts_install I.desc w w1 id admitted h hst
            (by simp [admitted, hpA]) (by simp [admitted, hparA])
          have hcred := ts_live I.desc _ (tname id) m.sender hset
          have hw' : w' = setActor (creditLive (setActor w1 id admitted) (tname id) m.sender) p.sender
              (resumeSender ((creditLive (setActor w1 id admitted) (tname id) m.sender).st p.sender)
                p.isCall id) := by simpa [Option.some.injEq, admitted] using hr.symm
          rw [hw']
          exact ts_resume_at I.desc _ p.sender p.isCall id hcred

theorem ts_prio (I : Impl) (w w' : World) (id : InstId) (h : ShapeRoot I.desc w)
    (hr : receivePrio I w id = some w') : ShapeRoot I.desc w' := by
  obtain ⟨_, pre, suf, w1, a1, _, _, hsplit, _, hdel, hw'⟩ := receivePrio_spec I w w' id hr
  obtain ⟨_, hpA, _, hparA, _, _, _, _, hst⟩ :=
    deliver_frame I w id ({ (w.st id) with prio := pre ++ suf }) _ w1 a1 hdel
  rw [hw']
  refine ⟨?_, ?_⟩
  · intro host msg hmem ht
    by_cases hh : host = id
    · rw [hh] at hmem
      rw [setActor_self, hpA] at hmem
      have hsub : msg ∈ (w.st id).prio := by
        rw [hsplit]
        rcases List.mem_append.mp hmem with hpre | hsuf
        · exact List.mem_append_left _ hpre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hsuf)
      exact h.shape id msg hsub ht
    · rw [setActor_other w1 id host a1 hh, hst host] at hmem
      exact h.shape host msg hmem ht
  · intro name
    have hpar : a1.parent = (w1.st id).parent := by
      rw [hparA, hst id]
    rw [setActor_parent_keep w1 id a1 (.core name) hpar, hst (.core name)]
    exact h.root name

theorem ts_detach (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).prio = a.prio ∧
      (detachReply (detachBox a caller) caller cid).parent = a.parent := by
  unfold detachReply detachBox
  split <;> simp

theorem ts_credit_frame (w : World) (tmpl : String) (sender i : InstId) :
    ((creditSender w tmpl sender).st i).prio = (w.st i).prio ∧
      ((creditSender w tmpl sender).st i).parent = (w.st i).parent := by
  unfold creditSender
  by_cases hi : i = sender
  · subst hi
    simp [setActor, bump_lineage]
  · simp [setActor, hi]

theorem ts_credit_fold_frame (ps : List Parked) (w : World) (tmpl : String) (sender i : InstId) :
    ((ps.foldl (fun acc _ => creditSender acc tmpl sender) w).st i).prio = (w.st i).prio ∧
      ((ps.foldl (fun acc _ => creditSender acc tmpl sender) w).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have h1 := ts_credit_frame w tmpl sender i
    have h2 := ih (creditSender w tmpl sender)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem ts_refund_frame (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).prio = (w.st i).prio ∧
      ((refundParkedCall w caller dst).st i).parent = (w.st i).parent := by
  unfold refundParkedCall
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · rename_i hne
    let keep := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall)
    let w1 := setActor w dst { (w.st dst) with parked := keep }
    have h1 : (w1.st i).prio = (w.st i).prio ∧ (w1.st i).parent = (w.st i).parent := by
      by_cases hi : i = dst
      · subst hi
        simp [w1, setActor, keep]
      · simp [w1, setActor, hi]
    have h2 := ts_credit_fold_frame ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall)
      w1 (tname dst) caller i
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem ts_refund (D : Description) (w : World) (caller dst : InstId) (h : ShapeRoot D w) :
    ShapeRoot D (refundParkedCall w caller dst) :=
  ts_frame D h (fun i => (ts_refund_frame w caller dst i).1)
    (fun i => (ts_refund_frame w caller dst i).2)

theorem ts_timeout (D : Description) (w w' : World) (id : InstId) (h : ShapeRoot D w)
    (ht : callTimeout w id = some w') : ShapeRoot D w' := by
  unfold callTimeout at ht
  dsimp at ht
  split at ht
  · simp at ht
  · cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at ht
      cases ht
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hhost := ts_keep D w dst host h (ts_detach _ _ _).1 (ts_detach _ _ _).2
      exact ts_keep D w1 id (finishCall (w1.st id) k .timedOut) hhost
        (finish_lineage _ _ _).2.2.2.1 (finish_lineage _ _ _).2.1
    | parked dst c k =>
      cases c with
      | false => simp [hph] at ht
      | true =>
        simp only [hph] at ht
        cases ht
        have href := ts_refund D w id dst h
        let w1 := refundParkedCall w id dst
        exact ts_keep D w1 id (finishCall (w1.st id) k .notAdmitted) href
          (finish_lineage _ _ _).2.2.2.1 (finish_lineage _ _ _).2.1
    | awaitPeer k =>
      simp only [hph] at ht
      cases ht
      exact ts_keep D w id (proceed (w.st id)
        { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }) h
        (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
    | idle => simp [hph] at ht
    | run _ => simp [hph] at ht
    | awaitEffect _ => simp [hph] at ht
    | crashed => simp [hph] at ht

theorem ts_finish (I : Impl) (w w' : World) (id : InstId) (h : ShapeRoot I.desc w)
    (hf : finishWait I w id = some w') : ShapeRoot I.desc w' := by
  obtain ⟨k, _, hw⟩ := finish_proceed I w w' id hf
  rw [hw]
  exact ts_keep I.desc w id (proceed (w.st id) k) h
    (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1

theorem ts_ingress_parent (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') : (w'.st i).parent = (w.st i).parent := by
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
            by_cases hi : i = dst
            · simp [setActor, hi, chargeSender, bumpToken]
            · simp [setActor, hi]

theorem ts_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : ShapeRoot I.desc w) (hi : receiveIngress I w dst label = some w') :
    ShapeRoot I.desc w' :=
  ts_frame I.desc h (fun i => (ingress_phase I w w' dst label i hi).2.2.1)
    (fun i => ts_ingress_parent I w w' dst label i hi)

theorem ts_exec (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (h : ShapeRoot I.desc w) (ha : a = w.st id) : ShapeRoot I.desc (execRun I w id a k) := by
  subst ha
  unfold execRun
  cases hb : ((w.st id).life == .alive) with
  | false => exact h
  | true =>
    cases hk : k.rest with
    | nil =>
      simp only [hk]
      exact ts_keep I.desc w id ({ (w.st id) with phase := .idle, typestate := k.toState }) h rfl rfl
    | cons eff rest =>
      simp only [hk]
      cases eff with
      | send dst label hint =>
        cases hr : route w I.desc id dst with
        | none =>
          simp [hr]
          exact ts_keep I.desc (noteStale w id dst) id (proceed (w.st id) (afterHead k))
            (ts_note I.desc w id dst h)
            (by rw [proceed_keeps_prio, noteStale_st])
            (by rw [(proceed_lineage (w.st id) (afterHead k)).2.1, noteStale_st])
        | some dstId =>
          simp [hr]
          exact ts_mail I.desc w id dstId { label := label, sender := id, callFrom := none }
            false (afterHead k) h
      | trySend dst label hint onFull onGone =>
        cases hr : route w I.desc id dst with
        | none =>
          simp [hr]
          exact ts_keep I.desc (noteStale w id dst) id
            (proceed (w.st id) { (afterHead k) with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone })
            (ts_note I.desc w id dst h)
            (by rw [proceed_keeps_prio, noteStale_st])
            (by rw [(proceed_lineage _ _).2.1, noteStale_st])
        | some dstId =>
          simp only [hr]
          by_cases hadmit : ((w.st dstId).life == .alive &&
              decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
          · rw [ts_if_pos _ _ _ hadmit]
            exact ts_mail I.desc w id dstId
              { label := label, sender := id, callFrom := none, reliable := false }
              false (afterHead k) h
          · rw [ts_if_neg _ _ _ hadmit]
            by_cases hliveD : ((w.st dstId).life == .alive) = true
            · rw [ts_if_pos _ _ _ hliveD]
              exact ts_keep I.desc w id
                (proceed (w.st id) { (afterHead k) with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull })
                h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
            · rw [ts_if_neg _ _ _ hliveD]
              exact ts_keep I.desc w id
                (proceed (w.st id) { (afterHead k) with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone })
                h (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
      | call dst label hint onNotAdmitted onTimedOut =>
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp [hr]
          exact ts_keep I.desc (noteStale w id dst) id
            (finishCall (issueCall (w.st id))
              ({ (afterHead k) with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut })
              .notAdmitted)
            (ts_note I.desc w id dst h)
            (by rw [(issue_finish_line (w.st id) _ _).2.2.2.1, noteStale_st])
            (by rw [(issue_finish_line (w.st id) _ _).2.1, noteStale_st])
        | some dstId =>
          simp [hr]
          exact ts_mail I.desc w id dstId { label := label, sender := id, callFrom := some id }
            true ({ (afterHead k) with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }) h
      | reply =>
        simp
        exact ts_reply I.desc w id k h
      | selfSchedule label =>
        dsimp
        by_cases hqueued : ((w.st id).prio.any (fun p => p.label == label)) = true
        · rw [ts_if_pos _ _ _ hqueued]
          exact ts_keep I.desc w id (proceed (w.st id) (afterHead k)) h
            (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
        · rw [ts_if_neg _ _ _ hqueued]
          by_cases hroom : prioLoad (w.st id).prio < capPrio I.desc w.N id
          · rw [if_pos hroom]
            let msg : Msg := { label := label, sender := id, callFrom := none, reliable := true, mid := (w.st id).nextMid }
            exact ts_self I.desc w id msg (afterHead k) h rfl
          · rw [if_neg hroom]
            exact ts_crash I.desc w h
      | cell dst label value =>
        simp only
        let previous := w.cell dst label
        let written := max previous.value value
        let w1 := setCell w dst label { value := written, dirty := true }
        have h2 := ts_keep I.desc w1 id (proceed (w1.st id) (afterHead k))
          (ts_st I.desc h (fun _ => rfl))
          (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
        by_cases hdirty : previous.dirty = true
        · simp [previous, written, w1, hdirty]
          exact h2
        · simp [previous, written, w1, ts_bool_false hdirty]
          exact ts_readers I.desc _ dst label id h2
      | internal =>
        simp
        exact ts_keep I.desc w id ({ (w.st id) with phase := .awaitEffect (afterHead k) }) h rfl rfl
      | peer onTimeout =>
        simp
        exact ts_keep I.desc w id
          ({ (w.st id) with phase := .awaitPeer ({ (afterHead k) with onTimeout := onTimeout }) }) h rfl rfl
      | abort =>
        simp
        exact ts_commit I.desc (abortChildren I.desc w id) id
          (proceed ((abortChildren I.desc w id).st id) (afterHead k))
          (ts_abort I.desc w id h) (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
      | spawn child =>
        cases hsp : spawnChild I w id child with
        | none =>
          simp [hsp]
          exact ts_crash I.desc w h
        | some w' =>
          simp [hsp]
          exact ts_commit I.desc w' id (proceed (w'.st id) (afterHead k))
            (ts_spawn_child I w w' id child h hsp)
            (proceed_keeps_prio _ _) (proceed_lineage _ _).2.1
      | terminate =>
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp [ht]
          exact ts_crash I.desc w h
        | some t =>
          simp only [ht]
          by_cases hcore : (t.multiplicity == .one) = true
          · simp [hcore]
            exact ts_crash I.desc w h
          · rw [ite_eq_right hcore]
            by_cases htree : (t.multiplicity == .perPeer && t.subtree != "") = true
            · simp [htree]
              exact ts_terminate I.desc w id (w.st id) h
            · rw [ite_eq_right htree]
              by_cases hlone : (t.terminable && t.subtree == "" &&
                  !hasParkedCall (w.st id).parked && !(hasChild I.desc w id)) = true
              · simp [hlone]
                exact ts_shutdown I.desc w id h
              · rw [ite_eq_right hlone]
                by_cases hkids : (t.terminable && t.subtree == "" &&
                    !hasParkedCall (w.st id).parked && hasChild I.desc w id) = true
                · simp [hkids]
                  exact ts_terminate I.desc w id (w.st id) h
                · rw [ite_eq_right hkids]
                  exact ts_crash I.desc w h
theorem ts_head (I : Impl) (w w' : World) (id : InstId) (h : ShapeRoot I.desc w)
    (hex : execHead I w id = some w') : ShapeRoot I.desc w' := by
  unfold execHead at hex
  by_cases hdead : (w.st id).life ≠ .alive
  · simp [hdead] at hex
  · simp only [hdead, ite_false] at hex
    cases hph : (w.st id).phase with
    | run k =>
      simp only [hph] at hex
      cases hex
      exact ts_exec I w id (w.st id) k h rfl
    | idle => simp [hph] at hex
    | awaitReply _ _ => simp [hph] at hex
    | awaitEffect _ => simp [hph] at hex
    | awaitPeer _ => simp [hph] at hex
    | parked _ _ _ => simp [hph] at hex
    | crashed => simp [hph] at hex

theorem ts_apply (I : Impl) (a : Action) (w w' : World) (h : ShapeRoot I.desc w)
    (ha : apply I a w = some w') : ShapeRoot I.desc w' := by
  have ⟨_, hstep⟩ := apply_step I a w w' ha
  cases a with
  | recvBulk id => simpa [stepWorld] using ts_bulk I w w' id h hstep
  | recvPrio id => simpa [stepWorld] using ts_prio I w w' id h hstep
  | exec id => simpa [stepWorld] using ts_head I w w' id h hstep
  | finish id => simpa [stepWorld] using ts_finish I w w' id h hstep
  | spawn template => simpa [stepWorld] using ts_spawn I w w' template h hstep
  | ingress dst label => simpa [stepWorld] using ts_ingress I w w' dst label h hstep
  | callTimeout id => simpa [stepWorld] using ts_timeout I.desc w w' id h hstep
  | stutter =>
    cases stutter_unchanged I w w' ha
    exact h

theorem ts_reach (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) : ShapeRoot I.desc w := by
  induction hR with
  | init => exact ts_init I N
  | step _ _ _ _ ha ih => exact ts_apply I _ _ _ ih ha

/-- Every priority tombstone of a reachable world is a peer `tombstoneMsg`. -/
theorem tomb_shape_reachable (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) :
    TombShape I.desc w :=
  (ts_reach I N w hR).shape

theorem ts_findTr (I : Impl) (template state label : String) (tr : Transition)
    (hm : tr ∈ I.transitions) (ht : tr.template = template) (hs : tr.fromState = state)
    (hl : tr.label = label) : ∃ tr', findTr I template state label = some tr' := by
  cases hf : findTr I template state label with
  | some tr' => exact ⟨tr', rfl⟩
  | none =>
    unfold findTr at hf
    have hnone := (List.findSome?_eq_none_iff.mp hf) tr hm
    simp [ht, hs, hl] at hnone

theorem ts_findDeliver (I : Impl) (template state : String) (m : Msg) (tr : Transition)
    (ht : m.tombstone = true) (hb : m.baseLabel ≠ "")
    (htr : findTr I template state m.baseLabel = some tr) :
    ∃ tr', findDeliver I template state m = some tr' := by
  unfold findDeliver
  cases hf : findTr I template state m.label with
  | some tr1 => exact ⟨tr1, by simp [hf]⟩
  | none =>
    have hdiff : m.baseLabel ≠ m.label := by
      intro heq
      rw [heq] at htr
      simp [hf] at htr
    have hbne : (m.baseLabel == "") = false := by simpa [beq_iff_eq] using hb
    have hneq : (m.baseLabel == m.label) = false := by simpa [beq_iff_eq] using hdiff
    simp [hf, ht, hbne, hneq, bne, htr]

theorem ts_handled (I : Impl) (hL : LocalOk I) (childT sup : Template) (supName st : String)
    (hmem : childT ∈ I.desc.templates) (hsupN : childT.supervisor = some supName)
    (hsup : templateOf I.desc supName = some sup) (hst : st ∈ sup.states) :
    childT.tombstone ≠ "" ∧ ∃ tr, findTr I supName st childT.tombstone = some tr := by
  have hall := tombstone_handled_local I hL
  unfold tombstoneHandled at hall
  have hone := (List.all_eq_true _ _).mp hall childT hmem
  simp only [hsupN] at hone
  have hpair := (Bool.and_eq_true _ _).mp hone
  have hne : childT.tombstone ≠ "" := by
    intro heq
    have hb : (childT.tombstone == "") = true := by simpa [beq_iff_eq] using heq
    simp [bne, hb] at hpair
  have hrest := hpair.2
  simp only [hsup] at hrest
  have hstAll := (List.all_eq_true _ _).mp hrest st hst
  rcases (List.any_eq_true _ _).mp hstAll with ⟨tr, hm, hcond⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  exact ⟨hne, ts_findTr I supName st childT.tombstone tr hm hcond.1.1 hcond.1.2 hcond.2⟩

theorem ts_ty (D : Description) (w : World) (id : InstId) (hT : TyOk D w)
    (hl : (w.st id).life = .alive) :
    ∃ t, templateOf D (tname id) = some t ∧ (w.st id).typestate ∈ t.states := by
  have helem := hT id hl
  simp [statesOf] at helem
  cases ht : templateOf D (tname id) with
  | none => simp [ht] at helem
  | some t =>
    simp [ht, List.elem_eq_mem] at helem
    exact ⟨t, rfl, helem⟩

/-- A current tombstone at a live receiver has a transition in that receiver's
state. `LocalOk` is `tombstoneHandled`: the supervisor names the child's
tombstone in every declared state. `BirthInv.tombOnParent` says the receiver
is that supervisor, and `TyOk` says the typestate is one of those states. -/
theorem queued_tomb_transition (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (host : InstId) (m : Msg)
    (hlive : (w.st host).life = .alive) (hm : m ∈ (w.st host).prio) (ht : m.tombstone = true) :
    ∃ tr, findDeliver I (tname host) (w.st host).typestate m = some tr := by
  have hS := tomb_shape_reachable I N w hR
  have hB := birth_reachable I hL hG N w hR
  have hT := ty_reachable I hL hG N w hR
  obtain ⟨n, k, g, t, hsend, htT, hne, hbase, _, _⟩ := hS host m hm ht
  have hon := hB.tombOnParent host m hm ht
  rw [hsend] at hon
  obtain ⟨hros, hpar, _⟩ := hon
  obtain ⟨sup, hsupT, hst⟩ := ts_ty I.desc w host hT hlive
  cases hsupN : t.supervisor with
  | none =>
    have hP := hB.parented (InstId.peer n k g) t hros htT
    simp [hsupN, hpar] at hP
  | some supName =>
    have hP := hB.parented (InstId.peer n k g) t hros htT
    simp only [hsupN] at hP
    obtain ⟨p, hp, htn, _⟩ := hP
    rw [hpar] at hp
    cases hp
    have hmemT : t ∈ I.desc.templates := (templateOf_mem I.desc n t htT).1
    have hsup : templateOf I.desc supName = some sup := by simpa [htn] using hsupT
    have hh := ts_handled I hL t sup supName (w.st host).typestate hmemT hsupN hsup hst
    rcases hh.2 with ⟨tr, htr⟩
    rw [← htn, ← hbase] at htr
    exact ts_findDeliver I (tname host) (w.st host).typestate m tr ht
      (by simpa [hbase] using hh.1) htr

theorem ts_newer_cells (D : Description) (w : World) (id : InstId) (m : Msg) :
    newerGeneration (readCells D w id) m = newerGeneration w m := by
  cases hs : m.sender with
  | core _ => simp [newerGeneration, hs]
  | peer name key gen =>
    simp only [newerGeneration, hs, cellsRoster, cellsSt]

theorem ts_deliver (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (hl : a.life = .alive) (hc : m.callFrom = none)
    (hcur : m.tombstone = true → newerGeneration w m = false →
      ∃ tr, findDeliver I (tname id) a.typestate m = some tr) :
    ∃ r, deliver I w id a m = some r := by
  have hnew := ts_newer_cells I.desc w id m
  unfold deliver
  dsimp
  split
  · next hdead => simp [hl] at hdead
  · by_cases hflag : (m.tombstone && newerGeneration (readCells I.desc w id) m) = true
    · rw [ts_if_pos _ _ _ hflag]
      exact ⟨_, rfl⟩
    · rw [ts_if_neg _ _ _ hflag]
      cases hf : findDeliver I (tname id) a.typestate m with
      | some tr =>
        simp only [hf]
        have hcall : ¬ (m.callFrom.isSome && !tr.acceptsCall) = true := by simp [hc]
        rw [ts_if_neg _ _ _ hcall]
        exact ⟨_, rfl⟩
      | none =>
        simp only [hf]
        by_cases ht : m.tombstone = true
        · have hgen : newerGeneration w m = false := by
            simp [ht, hnew] at hflag
            exact hflag
          obtain ⟨tr, htr⟩ := hcur ht hgen
          simp [hf] at htr
        · have hstay : ¬ (m.callFrom.isSome || m.tombstone) = true := by simp [hc, ht]
          rw [ts_if_neg _ _ _ hstay]
          exact ⟨_, rfl⟩

theorem waits_plain (w : World) (m : Msg) (ht : m.tombstone = false) :
    tombstoneWaits w m = false := by
  simp [tombstoneWaits, ht]

/-- Skip waiting tombstones. A plain message, an older-generation tombstone, or
a current tombstone with a transition is delivered, so the walk does not stop. -/
theorem receivePrioFrom_ready (I : Impl) (w : World) (id : InstId) (skipped ms : List Msg)
    (hl : (w.st id).life = .alive) (hplain : ∀ m ∈ ms, m.callFrom = none)
    (hdel : ∀ m ∈ ms, m.tombstone = true → newerGeneration w m = false →
      ∃ tr, findDeliver I (tname id) (w.st id).typestate m = some tr)
    (hready : ∃ m ∈ ms, tombstoneWaits w m = false) :
    receivePrioFrom I w id skipped ms ≠ none := by
  induction ms generalizing skipped with
  | nil =>
    rcases hready with ⟨_, hm, _⟩
    simp at hm
  | cons m ms ih =>
    by_cases hwait : tombstoneWaits w m = true
    · simp only [receivePrioFrom, hwait, ite_true]
      exact ih (skipped ++ [m])
        (fun x hx => hplain x (List.mem_cons_of_mem _ hx))
        (fun x hx ht hn => hdel x (List.mem_cons_of_mem _ hx) ht hn)
        (by
          rcases hready with ⟨m0, hm0, hnw⟩
          rcases List.mem_cons.mp hm0 with rfl | hm0
          · simp [hwait] at hnw
          · exact ⟨m0, hm0, hnw⟩)
    · have hwf : tombstoneWaits w m = false := ts_bool_false hwait
      obtain ⟨r, hd⟩ := ts_deliver I w id { (w.st id) with prio := skipped ++ ms } m
        (by simp [hl]) (hplain m List.mem_cons_self)
        (fun ht hn => by
          simpa using hdel m List.mem_cons_self ht hn)
      cases r with
      | mk w1 a1 =>
        simp [receivePrioFrom, hwf, hd]

theorem receivePrio_ready (I : Impl) (w : World) (id : InstId)
    (hl : (w.st id).life = .alive) (hidle : (w.st id).phase = .idle)
    (hplain : ∀ m ∈ (w.st id).prio, m.callFrom = none)
    (hdel : ∀ m ∈ (w.st id).prio, m.tombstone = true → newerGeneration w m = false →
      ∃ tr, findDeliver I (tname id) (w.st id).typestate m = some tr)
    (hready : ∃ m ∈ (w.st id).prio, tombstoneWaits w m = false) :
    receivePrio I w id ≠ none := by
  unfold receivePrio
  simp only [hl, hidle, ne_eq, not_true_eq_false, decide_false, Bool.or_false, ite_false]
  exact receivePrioFrom_ready I w id [] (w.st id).prio hl hplain hdel hready

end Deadlock
