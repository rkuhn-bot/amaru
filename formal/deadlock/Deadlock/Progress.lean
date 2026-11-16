import Deadlock.Rank

set_option autoImplicit false

namespace Deadlock

/-- A live actor waiting on a send, a call, an effect, or a peer. -/
def Blocked (w : World) (id : InstId) : Prop :=
  (w.st id).life = .alive ∧
    match (w.st id).phase with
    | .parked _ _ _ => True
    | .awaitReply _ _ => True
    | .awaitEffect _ => True
    | .awaitPeer _ => True
    | _ => False

def nodeAt (w : World) (id : InstId) : Node :=
  { template := tname id, state := (w.st id).typestate }

/-- Who an action steps, when it has a subject. Ingress is included so a proof
can show it is not on the wait chain. -/
def actionSubject : Action → Option InstId
  | .recvBulk s => some s
  | .recvPrio s => some s
  | .exec s => some s
  | .finish s => some s
  | .ingress s _ => some s
  | .spawn _ => none
  | .kill _ _ => none
  | .stutter => none

/-- `id` is blocked on `dst`. -/
def WaitsOn (w : World) (id dst : InstId) : Prop :=
  match (w.st id).phase with
  | .parked d _ _ => d = dst
  | .awaitReply d _ => d = dst
  | _ => False

/-- Actors reachable by following wait targets, including `id` itself. -/
inductive InChain (w : World) : InstId → InstId → Prop where
  | refl (id : InstId) : InChain w id id
  | step (id dst nxt : InstId) : InChain w id dst → WaitsOn w dst nxt → InChain w id nxt

/-- A step whose subject lies on `root`'s wait chain. Ingress and spawn never do. -/
def OnChain (w : World) (root : InstId) (act : Action) : Prop :=
  match actionSubject act with
  | some s => InChain w root s ∧
      match act with
      | .ingress _ _ => False
      | .spawn _ => False
      | .stutter => False
      | _ => True
  | none => False

/-- A list of chain steps. Each action is `OnChain` in the world where it is taken. -/
inductive ChainRun (I : Impl) (root : InstId) : World → List Action → Prop where
  | nil (w : World) : ChainRun I root w []
  | cons (w : World) (a : Action) (w' : World) (as : List Action)
      (hC : OnChain w root a) (hA : apply I a w = some w')
      (hR : ChainRun I root w' as) : ChainRun I root w (a :: as)

theorem waits_on_park (w : World) (id dst : InstId) (isCall : Bool) (k : Cont)
    (h : (w.st id).phase = .parked dst isCall k) : WaitsOn w id dst := by
  simp [WaitsOn, h]

theorem waits_on_reply (w : World) (id dst : InstId) (k : Cont)
    (h : (w.st id).phase = .awaitReply dst k) : WaitsOn w id dst := by
  simp [WaitsOn, h]

theorem chain_of_wait (w : World) (id dst : InstId) (h : WaitsOn w id dst) : InChain w id dst :=
  InChain.step id id dst (InChain.refl id) h

theorem chain_prefix (w : World) (id dst s : InstId) (hwait : WaitsOn w id dst)
    (h : InChain w dst s) : InChain w id s :=
  match h with
  | .refl _ => chain_of_wait w id dst hwait
  | .step _ mid nxt hmid hnext =>
    InChain.step id mid nxt (chain_prefix w id dst mid hwait hmid) hnext

theorem ingress_off_chain (w : World) (id dst : InstId) (label : String) :
    ¬ OnChain w id (.ingress dst label) := by
  intro h
  simp [OnChain, actionSubject] at h

theorem on_finish_self (w : World) (id : InstId) : OnChain w id (.finish id) := by
  simp [OnChain, actionSubject, InChain.refl]

theorem on_self_bulk (w : World) (id : InstId) : OnChain w id (.recvBulk id) := by
  simp [OnChain, actionSubject, InChain.refl]

theorem on_self_exec (w : World) (id : InstId) : OnChain w id (.exec id) := by
  simp [OnChain, actionSubject, InChain.refl]

theorem on_partner (w : World) (id dst : InstId) (act : Action) (hwait : WaitsOn w id dst)
    (h : OnChain w dst act) : OnChain w id act := by
  simp [OnChain] at h ⊢
  cases act with
  | recvBulk s =>
    rcases h with ⟨hc, _⟩
    exact ⟨chain_prefix w id dst s hwait hc, trivial⟩
  | recvPrio s =>
    rcases h with ⟨hc, _⟩
    exact ⟨chain_prefix w id dst s hwait hc, trivial⟩
  | exec s =>
    rcases h with ⟨hc, _⟩
    exact ⟨chain_prefix w id dst s hwait hc, trivial⟩
  | finish s =>
    rcases h with ⟨hc, _⟩
    exact ⟨chain_prefix w id dst s hwait hc, trivial⟩
  | ingress _ _ => exact h.2.elim
  | spawn _ => exact False.elim (by simp [actionSubject] at h)
  | kill _ _ => exact False.elim (by simp [actionSubject] at h)
  | stutter => exact False.elim (by simp [actionSubject] at h)

theorem core_alive_reachable (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (dst : String) (t : Template) (ht : templateOf I.desc dst = some t)
    (hone : t.multiplicity = .one) (hterm : t.terminable = false) :
    (w.st (InstId.core dst)).life = .alive := by
  induction hR with
  | init => exact init_core_alive I N dst t ht hone
  | step w w' a _ ha ih =>
    by_cases hdie : (w'.st (InstId.core dst)).life = .alive
    · exact hdie
    · cases only_terminate_kills I a w w' (InstId.core dst) ha ih hdie with
      | inl hExecKill =>
        rcases hExecKill with ⟨_, _, _, t', _, _, ht', hflag⟩
        have hto : templateOf I.desc dst = some t' := by simpa [tname] using ht'
        have hsame : t' = t := by injection (hto.symm.trans ht)
        simp [hsame, hterm] at hflag
      | inr hSubKill =>
        rcases hSubKill with ⟨_, _, _, hmem⟩
        simp [isMember] at hmem

theorem enqueue_roster (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) : (enqueueOrPark w D sender dst msg isCall k).roster = w.roster := by
  unfold enqueueOrPark
  by_cases hl : (w.st dst).life = .alive
  · by_cases hr : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hs : sender = dst <;> cases isCall <;> simp [hl, hr, hs, setActor]
    · by_cases hs : sender = dst <;> simp [hl, hr, hs, setActor]
  · simp [hl, setActor]

theorem perform_roster (w : World) (id : InstId) (k : Cont) :
    (performReply w id k).roster = w.roster := by
  unfold performReply
  cases hr : k.replyTo with
  | none => simp [hr, setActor]
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst _ =>
      by_cases hdst : dst = id <;> simp [hr, hph, hdst, setActor]
    | idle => simp [hr, hph, setActor]
    | run _ => simp [hr, hph, setActor]
    | parked _ _ _ => simp [hr, hph, setActor]
    | awaitEffect _ => simp [hr, hph, setActor]
    | awaitPeer _ => simp [hr, hph, setActor]
    | crashed => simp [hr, hph, setActor]

theorem release_roster (w : World) (id : InstId) (ps : List Parked) :
    (releaseParked w id ps).roster = w.roster := by
  induction ps generalizing w with
  | nil =>
    unfold releaseParked
    rfl
  | cons p ps ih =>
    unfold releaseParked
    simp only [List.foldl_cons]
    by_cases h : (p.isCall || decide (p.sender = id)) = true
    · simp only [h]
      exact ih w
    · simp only [h]
      exact ih (setActor w p.sender (resumeSender (w.st p.sender) false id))

theorem try_wake_roster (D : Description) (w : World) (id : InstId) (label : String) (writer : InstId) :
    (tryWake D w id label writer).roster = w.roster := by
  unfold tryWake
  by_cases hgo : ((w.st id).life == .alive && (w.st id).prio.length < capPrio D w.N id &&
      !((w.st id).prio.any (fun p => p.label == label))) = true
  · simp [hgo, setActor]
  · simp [hgo]

theorem wakes_roster (ids : List InstId) (D : Description) (w : World) (dst label : String) (writer : InstId) :
    (ids.foldl (fun w id => tryWake D w id label writer) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    rw [ih, try_wake_roster]

theorem exec_roster (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) :
    (execRun I w id a k).roster = w.roster := by
  unfold execRun
  cases hk : k.rest with
  | nil => simp [setActor]
  | cons e _ =>
    cases e with
    | send dst label hint =>
      simp [hk]
      cases route w I.desc id dst with
      | none => simp [setActor]
      | some dstId => exact enqueue_roster w I.desc id dstId _ false _
    | trySend dst label hint =>
      simp [hk]
      cases hr : route w I.desc id dst with
      | none => simp [hr, setActor]
      | some dstId =>
        simp [hr]
        by_cases hroom : ((w.st dstId).life = .alive ∧ (w.st dstId).parked = []) ∧
            (w.st dstId).box.length < capBulk I.desc w.N dstId
        · simp [hroom]
          exact enqueue_roster w I.desc id dstId _ false _
        · simp [hroom, setActor]
    | call dst label hint =>
      simp [hk]
      cases route w I.desc id dst with
      | none => simp [setActor]
      | some dstId => exact enqueue_roster w I.desc id dstId _ true _
    | reply => simp [hk, perform_roster]
    | selfSchedule label =>
      by_cases hany : a.prio.any (fun p => p.label == label) = true
      · simp [hk, hany, setActor]
      · by_cases hlen : a.prio.length < capPrio I.desc w.N id
        · simp [hk, hany, hlen, setActor]
        · simp [hk, hany, hlen, setActor]
    | cell dst label value =>
      simp only [hk]
      by_cases hdirty : (w.cell dst label).dirty = true
      · simp only [hdirty]
        dsimp
        rfl
      · have hfalse : (w.cell dst label).dirty = false := by
          cases hb : (w.cell dst label).dirty with
          | true => exact False.elim (hdirty hb)
          | false => rfl
        rw [hfalse]
        have hnot : ¬ (false = true) := by decide
        rw [ite_eq_right hnot]
        have hwk : wakeReaders I.desc
            (setActor (setCell w dst label { value := max (w.cell dst label).value value, dirty := true }) id
              (proceed ((setCell w dst label { value := max (w.cell dst label).value value, dirty := true }).st id)
                (afterHead k))) dst label id =
            ((readersOf (setActor (setCell w dst label { value := max (w.cell dst label).value value, dirty := true }) id
              (proceed ((setCell w dst label { value := max (w.cell dst label).value value, dirty := true }).st id)
                (afterHead k))) dst).foldl
              (fun acc j => tryWake I.desc acc j label id)
              (setActor (setCell w dst label { value := max (w.cell dst label).value value, dirty := true }) id
                (proceed ((setCell w dst label { value := max (w.cell dst label).value value, dirty := true }).st id)
                  (afterHead k)))) := by
          unfold wakeReaders
          rfl
        rw [hwk]
        rw [wakes_roster _ I.desc _ dst label id]
        rfl
    | internal => simp [hk, setActor]
    | peer => simp [hk, setActor]
    | terminate =>
      cases ht : templateOf I.desc (tname id) with
      | none => simp only [hk, ht]
      | some t =>
        by_cases hgo : t.terminable = true ∧ hasParkedCall a.parked = false
        · simp only [hk, ht, hgo]
          dsimp
          rw [release_roster, (frame_set _ _ _).2.1, (frame_refundP _ _ _).2.1,
            (frame_refund _ _ _).2.1, readCells_roster]
        · have hf : (t.terminable && !hasParkedCall a.parked) = false := by
            by_cases htB : t.terminable = true <;> by_cases hp : hasParkedCall a.parked = false <;>
              simp [htB, hp] at hgo ⊢
          simp only [hk, ht, hf]
          rfl

theorem bulk_roster (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : receiveBulk I w id = some w') : w'.roster = w.roster := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · simp at h
        · next w1 a1 hdel =>
          cases h
          rw [(frame_set _ p.sender _).2.1, (frame_credit _ _ _).2.1, (frame_set w1 id a1).2.1,
            deliver_roster I w id _ p.msg w1 a1 hdel]
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · simp at h
        · next w1 a1 hdel =>
          cases h
          rw [(frame_credit _ _ _).2.1, (frame_set w1 id a1).2.1,
            deliver_roster I w id _ m w1 a1 hdel]
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · simp at h
        · next w1 a1 hdel =>
          cases h
          rw [(frame_set _ _ _).2.1, (frame_credit _ _ _).2.1, (frame_set w1 id _).2.1,
            deliver_roster I w id _ m w1 a1 hdel]

theorem prio_roster (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : receivePrio I w id = some w') : w'.roster = w.roster := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp [hp] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      rw [(frame_set w1 id a1).2.1, deliver_roster I w id _ m w1 a1 hdel]

theorem head_roster (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : execHead I w id = some w') : w'.roster = w.roster := by
  unfold execHead at h
  by_cases hl : (w.st id).life = .alive
  · simp [hl] at h
    cases hp : (w.st id).phase <;> simp [hp] at h
    · cases h
      exact exec_roster I w id (w.st id) _
  · simp [hl] at h

theorem finish_roster (I : Impl) (w : World) (id : InstId) (w' : World)
    (h : finishWait I w id = some w') : w'.roster = w.roster := by
  obtain ⟨_, _, hw⟩ := finish_proceed I w w' id h
  simp [hw, setActor]

/-- A per-peer id of a multiplicity-one template is never on the roster. -/
theorem one_peer_absent (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (name : String) (t : Template) (ht : templateOf I.desc name = some t)
    (hone : t.multiplicity = .one) (i : Nat) : InstId.peer name i ∉ w.roster := by
  induction hR with
  | init =>
    intro hin
    rw [init_roster] at hin
    have hnin : InstId.peer name i ∉ coreRoster I.desc := by
      simpa [List.contains_iff_mem] using peer_not_roster I.desc name i
    exact hnin hin
  | step w w' a _ ha ih =>
    intro hin
    have hback : InstId.peer name i ∈ w.roster := by
      cases a with
      | ingress dst label =>
        rw [(ingress_phase I w w' dst label (InstId.peer name i)
          (by simpa [apply] using ha)).2.2.2.2.1] at hin
        exact hin
      | finish fid =>
        rw [finish_roster I w fid w' (by simpa [apply] using ha)] at hin
        exact hin
      | recvPrio rid =>
        rw [prio_roster I w rid w' (by simpa [apply] using ha)] at hin
        exact hin
      | recvBulk rid =>
        rw [bulk_roster I w rid w' (by simpa [apply] using ha)] at hin
        exact hin
      | exec eid =>
        rw [head_roster I w eid w' (by simpa [apply] using ha)] at hin
        exact hin
      | spawn template =>
        simp only [apply, spawn] at ha
        split at ha
        · cases ha
        · next ts hto =>
          by_cases hgo : (ts.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
          · simp [hgo] at ha
            cases ha
            rw [readCells_roster, (frame_set _ _ _).2.1] at hin
            simp at hin
            rcases hin with hin | ⟨hname, _⟩
            · exact hin
            · have hsame : ts = t := by
                have hto' : templateOf I.desc name = some ts := by simpa [hname] using hto
                injection (hto'.symm.trans ht)
              have hmul : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
              simp [hsame, hone, hmul] at hgo
          · simp [hgo] at ha
      | kill sub key =>
        have hw := kill_apply_world I w w' sub key (by simpa [apply] using ha)
        rw [hw, killSubtree_roster] at hin
        exact hin
      | stutter =>
        cases stutter_unchanged I w w' (by simpa [apply] using ha)
        exact hin
    exact ih hback

theorem edge_reliable (D : Description) (hS : structLines D = []) (e : Edge) (he : e ∈ D.edges)
    (heff : e.effect = .send ∨ e.effect = .call) : e.reliability = .reliable := by
  cases hr : e.reliability with
  | reliable => rfl
  | superseding =>
    have hmem : (s!"fail: superseding edge {e.src}/{e.srcState} -[{e.label}]-> {e.dst} must be a non-blocking cell write") ∈
        cellFails D := by
      refine List.mem_filterMap.mpr ⟨e, he, ?_⟩
      cases heff with
      | inl hs =>
        have hrelb : (Reliability.superseding != Reliability.superseding) = false := by decide
        have hcell : (EffectKind.send != EffectKind.cell) = true := by decide
        simp [cellFails, hr, hs, hrelb, hcell]
      | inr hc =>
        have hrelb : (Reliability.superseding != Reliability.superseding) = false := by decide
        have hcell : (EffectKind.call != EffectKind.cell) = true := by decide
        simp [cellFails, hr, hc, hrelb, hcell]
    have hstruct : (s!"fail: superseding edge {e.src}/{e.srcState} -[{e.label}]-> {e.dst} must be a non-blocking cell write") ∈
        structLines D := by
      simpa [structLines] using
        (List.mem_append_left (cellEffectFails D ++ ingressFails D ++ allowedFails D ++ compatFails D)
          (List.mem_append_right (nameFails D ++ stateFails D ++ endpointFails D ++ kindFails D ++ scopeFails D)
            hmem))
    simp [hS] at hstruct

theorem wait_template (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (e : Edge) (he : e ∈ I.desc.edges)
    (heff : e.effect = .send ∨ e.effect = .call) :
    ∃ t, templateOf I.desc e.dst = some t ∧
      ((t.multiplicity = .one ∧ t.terminable = false) ∨ sameSubtree I.desc e.src e.dst = true) := by
  have hrel := edge_reliable I.desc hG.struct e he heff
  have hall := (List.all_eq_true _ _).mp (permanent_target_local I hL) e he
  have hcond : ((e.effect == .send || e.effect == .call) && e.reliability == .reliable) = true := by
    cases heff with
    | inl hs =>
      simp only [hs, hrel]
      decide
    | inr hc =>
      simp only [hc, hrel]
      decide
  cases ht : templateOf I.desc e.dst with
  | none =>
    simpa [hcond, ht] using hall
  | some t =>
    have hbody :
        ((t.multiplicity == .one && t.terminable == false) ||
          sameSubtree I.desc e.src e.dst) = true := by
      simpa [hcond, ht] using hall
    rw [Bool.or_eq_true] at hbody
    rcases hbody with hperm | hsub
    · rw [Bool.and_eq_true] at hperm
      cases hm : t.multiplicity with
      | one =>
        exact ⟨t, rfl, Or.inl ⟨hm, (beq_iff_eq).mp (by simpa [hm] using hperm.2)⟩⟩
      | perPeer =>
        have hf : (Multiplicity.perPeer == Multiplicity.one) = false := by decide
        rw [hm, hf] at hperm
        nomatch hperm.1
    · exact ⟨t, rfl, Or.inr hsub⟩

theorem park_target_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (isCall : Bool) (k : Cont)
    (hph : (w.st id).phase = .parked dst isCall k) : (w.st dst).life = .alive := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨p, hp, _, _⟩ := hI.2.1.bwd id dst isCall k hph
  exact mailbox_alive I hL N w hR dst (by
    intro hempty
    simp [hempty] at hp)

theorem reply_target_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .awaitReply dst k) : (w.st dst).life = .alive := by
  have hT := call_tag_reachable I hL hG N w hR
  rcases hT.awaiting id dst k hph with hmail | hhand | hpend
  · rcases hmail.1 with ⟨m, hm, _⟩ | ⟨p, hp, _⟩
    · exact box_alive I hL hG N w hR dst (by
        intro hempty
        simp [hempty] at hm)
    · exact mailbox_alive I hL N w hR dst (by
        intro hempty
        simp [hempty] at hp)
  · exact busy_alive I N w hR dst (by
      intro hidle
      rcases hhand.2.1 with ⟨_, hcar, _⟩
      simp [carriedCont, hidle] at hcar)
  · exact busy_alive I N w hR dst (by
      intro hidle
      rcases hpend.2.2 with ⟨_, hcar, _⟩
      simp [carriedCont, hidle] at hcar)

theorem blocked_go (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I) (N : Nat)
    (w : World) (hR : Reachable I N w) (hs : List (Node × Nat))
    (hok : heightsOkB (residualEdges I.desc) hs = true) (n : Nat) (id : InstId)
    (hn : heightOf hs (nodeAt w id) < n) (hB : Blocked w id) :
    (∃ act, OnChain w id act ∧ Enabled I w act) ∨ PurePeerEnd I.desc w id := by
  induction n generalizing id with
  | zero => omega
  | succ n ih =>
    have hlive := hB.1
    cases hph : (w.st id).phase with
    | idle =>
      unfold Blocked at hB
      simp [hph] at hB
    | run _ =>
      unfold Blocked at hB
      simp [hph] at hB
    | crashed =>
      unfold Blocked at hB
      simp [hph] at hB
    | awaitEffect k =>
      exact Or.inl ⟨.finish id, on_finish_self w id, effect_finish_enabled I w id k hph⟩
    | awaitPeer k =>
      cases hf : peerFinishable I.desc id with
      | true =>
        exact Or.inl ⟨.finish id, on_finish_self w id, peer_finish_enabled I w id k hph hf⟩
      | false =>
        exact Or.inr ⟨k, hph, hf⟩
    | parked dst isCall k =>
      have hliveD := park_target_alive I hL hG N w hR id dst isCall k hph
      have hdrop : heightOf hs (nodeAt w dst) < heightOf hs (nodeAt w id) := by
        cases isCall with
        | false =>
          exact park_below I hL hG N w hR ((inv3_reachable I hL hG N w hR).1.2.1)
            id dst k hs hok hph hliveD
        | true => exact call_below I hL hG N w hR id dst k hs hok hph hliveD
      cases hphD : (w.st dst).phase with
      | idle =>
        have hmail : (w.st dst).box ≠ [] ∨ (w.st dst).parked ≠ [] := by
          obtain ⟨p, hp, _, _⟩ := (inv_reachable I N w hL hR).2.1.bwd id dst isCall k hph
          exact Or.inr (fun hempty => by simp [hempty] at hp)
        exact Or.inl ⟨.recvBulk dst,
          on_partner w id dst (.recvBulk dst) (waits_on_park w id dst isCall k hph) (on_self_bulk w dst),
          can_receive_enabled I hL w dst
          ((inv3_reachable I hL hG N w hR).1.2.2.1) (mail_accepted_reachable I hL N w hR)
          ⟨⟨hliveD, hphD⟩, hmail⟩⟩
      | run kD =>
        exact Or.inl ⟨.exec dst,
          on_partner w id dst (.exec dst) (waits_on_park w id dst isCall k hph) (on_self_exec w dst),
          run_enabled I w dst kD hphD hliveD⟩
      | awaitEffect kD =>
        exact Or.inl ⟨.finish dst,
          on_partner w id dst (.finish dst) (waits_on_park w id dst isCall k hph) (on_finish_self w dst),
          effect_finish_enabled I w dst kD hphD⟩
      | awaitPeer kD =>
        have hfin := target_finishable I hG w (inv_reachable I N w hL hR) id dst
          (Or.inl ⟨isCall, k, hph⟩)
        exact Or.inl ⟨.finish dst,
          on_partner w id dst (.finish dst) (waits_on_park w id dst isCall k hph) (on_finish_self w dst),
          peer_finish_enabled I w dst kD hphD hfin⟩
      | crashed =>
        exact False.elim ((reachable_not_crashed I hL hG N w hR) dst (by simp [hphD]))
      | parked _ _ _ =>
        rcases ih dst (Nat.lt_of_lt_of_le hdrop (Nat.le_of_lt_succ hn))
          ⟨hliveD, by simp [hphD]⟩ with ⟨act, hchain, hen⟩ | ⟨kP, hkP, _⟩
        · exact Or.inl ⟨act, on_partner w id dst act (waits_on_park w id dst isCall k hph) hchain, hen⟩
        · rw [hphD] at hkP; cases hkP
      | awaitReply _ _ =>
        rcases ih dst (Nat.lt_of_lt_of_le hdrop (Nat.le_of_lt_succ hn))
          ⟨hliveD, by simp [hphD]⟩ with ⟨act, hchain, hen⟩ | ⟨kP, hkP, _⟩
        · exact Or.inl ⟨act, on_partner w id dst act (waits_on_park w id dst isCall k hph) hchain, hen⟩
        · rw [hphD] at hkP; cases hkP
    | awaitReply dst k =>
      have hliveD := reply_target_alive I hL hG N w hR id dst k hph
      have hdrop := reply_below I hL hG N w hR id dst k hs hok hph hliveD
      cases hphD : (w.st dst).phase with
      | idle =>
        have hT := call_tag_reachable I hL hG N w hR
        have hmail : (w.st dst).box ≠ [] ∨ (w.st dst).parked ≠ [] := by
          rcases hT.awaiting id dst k hph with hmail | hhand | hpend
          · rcases hmail.1 with ⟨m, hm, _⟩ | ⟨p, hp, _⟩
            · exact Or.inl (fun hempty => by simp [hempty] at hm)
            · exact Or.inr (fun hempty => by simp [hempty] at hp)
          · rcases hhand.2.1 with ⟨_, hcar, _⟩
            simp [carriedCont, hphD] at hcar
          · rcases hpend.2.2 with ⟨_, hcar, _⟩
            simp [carriedCont, hphD] at hcar
        exact Or.inl ⟨.recvBulk dst,
          on_partner w id dst (.recvBulk dst) (waits_on_reply w id dst k hph) (on_self_bulk w dst),
          can_receive_enabled I hL w dst
          ((inv3_reachable I hL hG N w hR).1.2.2.1) (mail_accepted_reachable I hL N w hR)
          ⟨⟨hliveD, hphD⟩, hmail⟩⟩
      | run kD =>
        exact Or.inl ⟨.exec dst,
          on_partner w id dst (.exec dst) (waits_on_reply w id dst k hph) (on_self_exec w dst),
          run_enabled I w dst kD hphD hliveD⟩
      | awaitEffect kD =>
        exact Or.inl ⟨.finish dst,
          on_partner w id dst (.finish dst) (waits_on_reply w id dst k hph) (on_finish_self w dst),
          effect_finish_enabled I w dst kD hphD⟩
      | awaitPeer kD =>
        have hfin := target_finishable I hG w (inv_reachable I N w hL hR) id dst
          (Or.inr ⟨k, hph⟩)
        exact Or.inl ⟨.finish dst,
          on_partner w id dst (.finish dst) (waits_on_reply w id dst k hph) (on_finish_self w dst),
          peer_finish_enabled I w dst kD hphD hfin⟩
      | crashed =>
        exact False.elim ((reachable_not_crashed I hL hG N w hR) dst (by simp [hphD]))
      | parked _ _ _ =>
        rcases ih dst (Nat.lt_of_lt_of_le hdrop (Nat.le_of_lt_succ hn))
          ⟨hliveD, by simp [hphD]⟩ with ⟨act, hchain, hen⟩ | ⟨kP, hkP, _⟩
        · exact Or.inl ⟨act, on_partner w id dst act (waits_on_reply w id dst k hph) hchain, hen⟩
        · rw [hphD] at hkP; cases hkP
      | awaitReply _ _ =>
        rcases ih dst (Nat.lt_of_lt_of_le hdrop (Nat.le_of_lt_succ hn))
          ⟨hliveD, by simp [hphD]⟩ with ⟨act, hchain, hen⟩ | ⟨kP, hkP, _⟩
        · exact Or.inl ⟨act, on_partner w id dst act (waits_on_reply w id dst k hph) hchain, hen⟩
        · rw [hphD] at hkP; cases hkP

/-- In a reachable world every live wait has an enabled step whose subject is
on that actor's wait chain. An ingress into an unrelated core does not count. -/
theorem blocked_progress (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    (N : Nat) (w : World) (hR : Reachable I N w) (id : InstId) (hB : Blocked w id) :
    (∃ act, OnChain w id act ∧ Enabled I w act) ∨ PurePeerEnd I.desc w id := by
  obtain ⟨hs, hok⟩ := hG.ranked
  exact blocked_go I hL hG hA N w hR hs hok (heightOf hs (nodeAt w id) + 1) id (by omega) hB

theorem runtimeBusy_roster (I : Impl) (w : World) (hb : runtimeBusy I w = false) (id : InstId)
    (hid : id ∈ w.roster) :
    receiveBulk I w id = none ∧ receivePrio I w id = none ∧
      execHead I w id = none ∧ finishWait I w id = none := by
  rw [runtimeBusy, Bool.or_eq_false_iff] at hb
  have hall : ∀ x ∈ w.roster,
      ((receiveBulk I w x).isSome || (receivePrio I w x).isSome ||
        (execHead I w x).isSome || (finishWait I w x).isSome) = false := by
    simpa using (List.any_eq_false.mp hb.1)
  have hfalse := hall id hid
  rw [Bool.or_eq_false_iff] at hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  rw [Bool.or_eq_false_iff] at hfalse
  rcases hfalse with ⟨⟨⟨hr, hp⟩, he⟩, hf⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : receiveBulk I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hr
  · cases h : receivePrio I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hp
  · cases h : execHead I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at he
  · cases h : finishWait I w id with
    | none => rfl
    | some _ => simp [h, Option.isSome] at hf

theorem quiet_no_forced (I : Impl) (w : World)
    (hoff : ∀ id, id ∉ w.roster → (w.st id).life ≠ .alive ∧ (w.st id).phase = .idle)
    (hb : runtimeBusy I w = false) (a : Action) (hf : forced a = true) : ¬ Enabled I w a := by
  cases a with
  | spawn _ => simp [forced] at hf
  | ingress _ _ => simp [forced] at hf
  | kill sub key =>
    intro hen
    have hwait : killWait w I.desc sub key = true := by
      simp [Enabled, apply] at hen
      cases hcond : killWait w I.desc sub key <;> simp [hcond] at hen
      rfl
    have hbusy := killWait_imp_busy I w sub key hwait
    simp [runtimeBusy, hbusy] at hb
  | stutter => simp [forced] at hf
  | recvBulk s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      simp [Enabled, apply, receiveBulk, hdead] at hen
  | recvPrio s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      cases hp : (w.st s).prio with
      | nil => simp [Enabled, apply, receivePrio, hp] at hen
      | cons _ _ => simp [Enabled, apply, receivePrio, hp, hdead] at hen
  | exec s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.2.1
      simp [Enabled, apply, hnone] at hen
    · have hdead := (hoff s hid).1
      simp [Enabled, apply, execHead, hdead] at hen
  | finish s =>
    intro hen
    by_cases hid : s ∈ w.roster
    · have hnone := (runtimeBusy_roster I w hb s hid).2.2.2
      simp [Enabled, apply, hnone] at hen
    · have hidle := (hoff s hid).2
      simp [Enabled, apply, finishWait, hidle] at hen


/-- An id that the initial roster does not name is the absent actor. -/
theorem off_idle_init (I : Impl) (N : Nat) (id : InstId) (h : id ∉ (initWorld I N).roster) :
    ((initWorld I N).st id).phase = .idle ∧ ((initWorld I N).st id).life ≠ .alive := by
  refine ⟨init_phase I N id, ?_⟩
  rw [init_roster] at h
  rw [init_base_st]
  split
  · next hc => exact False.elim (h (List.contains_iff_mem.mp hc))
  · simp [absentActor]

/-- A step does not wake an actor that is off the roster. Spawn puts the new id
on the roster, and every other step leaves that actor idle and not alive. -/
theorem off_idle_step (I : Impl) (a : Action) (w w' : World)
    (hoff : ∀ id, id ∉ w.roster → (w.st id).phase = .idle ∧ (w.st id).life ≠ .alive)
    (h : apply I a w = some w') (s : InstId) (hs : s ∉ w'.roster) :
    (w'.st s).phase = .idle ∧ (w'.st s).life ≠ .alive := by
  cases a with
  | kill sub key =>
    have hw := kill_apply_world I w w' sub key h
    have hs0 : s ∉ w.roster := by
      rw [hw, killSubtree_roster] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hs0
    have hkeep := killSubtree_off w I.desc sub key s hs0 hdead
    rw [hw]
    exact ⟨hkeep.1.trans hidle, by rw [hkeep.2]; exact hdead⟩
  | stutter =>
    have heq := stutter_unchanged I w w' h
    subst heq
    exact hoff s hs
  | ingress dst label =>
    have hkeep := ingress_phase I w w' dst label s (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hkeep.2.2.2.2.1] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    refine ⟨hkeep.1.trans hidle, ?_⟩
    rw [hkeep.2.1]
    exact hdead
  | finish id =>
    have hr := finish_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    obtain ⟨k, hph, hw⟩ := finish_proceed I w w' id (by simpa [apply] using h)
    have hne : s ≠ id := by
      intro heq
      rcases hph with hph | hph
      · rw [← heq, hidle] at hph
        cases hph
      · rw [← heq, hidle] at hph
        cases hph
    rw [hw]
    refine ⟨?_, ?_⟩
    · simp [setActor, hne, hidle]
    · simp [setActor, hne]
      exact hdead
  | recvPrio id =>
    have hr := prio_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    have hrecv : receivePrio I w id = some w' := by simpa [apply] using h
    unfold receivePrio at hrecv
    cases hp : (w.st id).prio with
    | nil => simp [hp] at hrecv
    | cons m ms =>
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hp, hready] at hrecv
      · simp [hp, hready] at hrecv
        split at hrecv
        · cases hrecv
        · next w1 a1 hdel =>
          cases hrecv
          have hlid : (w.st id).life = .alive := by
            by_cases hl : (w.st id).life = .alive
            · exact hl
            · exact False.elim (hready (Or.inl hl))
          have hne : s ≠ id := by
            intro heq
            exact hdead (by simpa [heq] using hlid)
          have hst := deliver_st I w id ({ (w.st id) with prio := ms }) m w1 a1 s hdel
          refine ⟨?_, ?_⟩
          · simp [setActor, hne, hst, hidle]
          · simp [setActor, hne, hst]
            exact hdead
  | recvBulk id =>
    have hr := bulk_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    have hrecv : receiveBulk I w id = some w' := by simpa [apply] using h
    have hlid : (w.st id).life = .alive := by
      unfold receiveBulk at hrecv
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hready] at hrecv
      · by_cases hl : (w.st id).life = .alive
        · exact hl
        · exact False.elim (hready (Or.inl hl))
    have hne : s ≠ id := by
      intro heq
      exact hdead (by simpa [heq] using hlid)
    have hnpark : ∀ d c k, (w.st s).phase ≠ .parked d c k := by
      intro d c k hbad
      rw [hidle] at hbad
      cases hbad
    have hkeep := bulk_keeps_quiet I w id w' s hne hnpark hrecv
    refine ⟨hkeep.1.trans hidle, ?_⟩
    rw [hkeep.2]
    exact hdead
  | exec id =>
    have hr := head_roster I w id w' (by simpa [apply] using h)
    have hold : s ∉ w.roster := by
      rw [hr] at hs
      exact hs
    obtain ⟨hidle, hdead⟩ := hoff s hold
    simp only [apply] at h
    unfold execHead at h
    by_cases hlid : (w.st id).life = .alive
    · simp [hlid] at h
      cases hph : (w.st id).phase with
      | run k =>
        simp [hph] at h
        cases h
        have hne : s ≠ id := by
          intro heq
          exact hdead (by simpa [heq] using hlid)
        have hnpark : ∀ d c ck, (w.st s).phase ≠ .parked d c ck := by
          intro d c ck hbad
          rw [hidle] at hbad
          cases hbad
        have hnreply : ∀ d ck, (w.st s).phase ≠ .awaitReply d ck := by
          intro d ck hbad
          rw [hidle] at hbad
          cases hbad
        have hkeep := exec_keeps_quiet I w id (w.st id) k s hne hnpark hnreply
        refine ⟨hkeep.1.trans hidle, ?_⟩
        rw [hkeep.2]
        exact hdead
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlid] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    cases ht : templateOf I.desc template with
    | none => simp [ht] at h
    | some t =>
      by_cases hgo : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
      · simp [ht, hgo] at h
        cases h
        simp only [readCells_st]
        by_cases hfresh : s = InstId.peer template (w.nextIx template)
        · exfalso
          apply hs
          simp [readCells_roster, setActor, hfresh, List.mem_append]
        · have hold : s ∉ w.roster := by
            intro hin
            apply hs
            simp [readCells_roster, setActor, List.mem_append, hin]
          obtain ⟨hidle, hdead⟩ := hoff s hold
          refine ⟨?_, ?_⟩
          · simpa [setActor, hfresh] using hidle
          · simpa [setActor, hfresh] using hdead
      · simp [ht, hgo] at h

theorem off_idle_reachable (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (h : id ∉ w.roster) :
    (w.st id).phase = .idle ∧ (w.st id).life ≠ .alive := by
  induction hR generalizing id with
  | init => exact off_idle_init I N id h
  | step w w' a _ ha ih =>
    exact off_idle_step I a w w' ih ha id h



/-- A stopped execution has no live wait except a pure untimed peer. `finish` is
disabled there, and no cohort timeout can end it. Stopping means `runtimeBusy`
is false: no forced `recv`, `exec`, or `finish`. -/
theorem fin_exec_no_blocked (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    {N : Nat} (e : FinExec I N) (id : InstId) (hB : Blocked (e.cfg e.len) id) :
    PurePeerEnd I.desc (e.cfg e.len) id := by
  have hR := fin_exec_reachable I e e.len (Nat.le_refl _)
  rcases blocked_progress I hG hL hA N (e.cfg e.len) hR id hB with ⟨act, hon, hen⟩ | hpure
  · have hf : forced act = true := by
      cases act <;> simp_all [OnChain, actionSubject, forced]
    have hoff : ∀ s, s ∉ (e.cfg e.len).roster →
        ((e.cfg e.len).st s).life ≠ .alive ∧ ((e.cfg e.len).st s).phase = .idle := by
      intro s hs
      have h := off_idle_reachable I N (e.cfg e.len) hR s hs
      exact ⟨h.2, h.1⟩
    exact False.elim (quiet_no_forced I (e.cfg e.len) hoff e.maximal act hf hen)
  · exact hpure

/-- A live reader with `label` still on its priority lane can take a step.
Idle, that step is `recvPrio`, which runs `readCells` and clears the wake. -/
theorem cell_wake_enabled (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    (N : Nat) (w : World) (hR : Reachable I N w) (r : InstId) (label : String)
    (hlive : (w.st r).life = .alive) (hhas : hasLabel ((w.st r).prio) label) :
    ∃ act, Enabled I w act ∧ forced act = true ∧ ((w.st r).phase = .idle → act = .recvPrio r) := by
  cases hph : (w.st r).phase with
  | idle =>
    exact ⟨.recvPrio r, recv_prio_enabled I w r label (call_tag_reachable I hL hG N w hR) hlive hph hhas,
      rfl, fun _ => rfl⟩
  | run k =>
    exact ⟨.exec r, run_enabled I w r k hph hlive, rfl, fun hbad => by simp [hph] at hbad⟩
  | awaitEffect k =>
    exact ⟨.finish r, effect_finish_enabled I w r k hph, rfl, fun hbad => by simp [hph] at hbad⟩
  | awaitPeer k =>
    cases hf : peerFinishable I.desc r with
    | true =>
      exact ⟨.finish r, peer_finish_enabled I w r k hph hf, rfl, fun hbad => by simp [hph] at hbad⟩
    | false =>
      have hLane := lane_reachable I hL hG N w hR
      have hempty : (w.st r).prio = [] := by
        have hp := pure_of_silent I.desc r hf
        exact prio_empty_of_pure I hL hG w hLane r hp
      simp [hasLabel, hempty] at hhas
  | parked _ _ _ =>
    rcases blocked_progress I hG hL hA N w hR r ⟨hlive, by simp [hph]⟩ with
      ⟨act, hon, hen⟩ | ⟨kP, hkP, _⟩
    · have hf : forced act = true := by
        cases act <;> simp_all [OnChain, actionSubject, forced]
      exact ⟨act, hen, hf, fun hbad => by simp [hph] at hbad⟩
    · rw [hph] at hkP; cases hkP
  | awaitReply _ _ =>
    rcases blocked_progress I hG hL hA N w hR r ⟨hlive, by simp [hph]⟩ with
      ⟨act, hon, hen⟩ | ⟨kP, hkP, _⟩
    · have hf : forced act = true := by
        cases act <;> simp_all [OnChain, actionSubject, forced]
      exact ⟨act, hen, hf, fun hbad => by simp [hph] at hbad⟩
    · rw [hph] at hkP; cases hkP
  | crashed =>
    exact False.elim ((reachable_not_crashed I hL hG N w hR) r (by simp [hph]))

/-- A stopped execution has no live reader still holding a priority wake. -/
theorem fin_exec_no_wake (I : Impl) (hG : GraphOk I.desc) (hL : LocalOk I) (hA : Assumptions I)
    {N : Nat} (e : FinExec I N) (r : InstId) (label : String)
    (hlive : ((e.cfg e.len).st r).life = .alive)
    (hhas : hasLabel (((e.cfg e.len).st r).prio) label) : False := by
  have hR := fin_exec_reachable I e e.len (Nat.le_refl _)
  obtain ⟨act, hen, hf, _⟩ := cell_wake_enabled I hG hL hA N (e.cfg e.len) hR r label hlive hhas
  have hoff : ∀ s, s ∉ (e.cfg e.len).roster →
      ((e.cfg e.len).st s).life ≠ .alive ∧ ((e.cfg e.len).st s).phase = .idle := by
    intro s hs
    have h := off_idle_reachable I N (e.cfg e.len) hR s hs
    exact ⟨h.2, h.1⟩
  exact quiet_no_forced I (e.cfg e.len) hoff e.maximal act hf hen

theorem fin_exec_not_blocked_on_idle (I : Impl) {N : Nat} (e : FinExec I N)
    (hM : MailInv (e.cfg e.len)) (id dst : InstId) (k : Cont)
    (hph : ((e.cfg e.len).st id).phase = .parked dst false k)
    (hl : ((e.cfg e.len).st dst).life = .alive)
    (hidle : ((e.cfg e.len).st dst).phase = .idle)
    (hc : ∀ p, p ∈ ((e.cfg e.len).st dst).parked → p.msg.callFrom = none)
    (hbox : ((e.cfg e.len).st dst).box = [] ∨
      ∃ m ms, ((e.cfg e.len).st dst).box = m :: ms ∧ m.callFrom = none) : False := by
  have hen : Enabled I (e.cfg e.len) (.recvBulk dst) := by
    obtain ⟨p, hmem, _, _⟩ := hM.bwd id dst false k hph
    cases hpark : ((e.cfg e.len).st dst).parked with
    | nil => simp [hpark] at hmem
    | cons q qs =>
      exact parked_idle_enabled I (e.cfg e.len) dst hl hidle q qs hpark
        (hc q (by simp [hpark])) hbox
  have hR := fin_exec_reachable I e e.len (Nat.le_refl _)
  have hmem : dst ∈ (e.cfg e.len).roster := by
    by_cases hin : dst ∈ (e.cfg e.len).roster
    · exact hin
    · exact False.elim ((off_idle_reachable I N (e.cfg e.len) hR dst hin).2 hl)
  have hnone := (runtimeBusy_roster I (e.cfg e.len) e.maximal dst hmem).1
  simp [Enabled, apply, hnone] at hen


end Deadlock
