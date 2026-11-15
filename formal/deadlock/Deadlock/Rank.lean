import Deadlock.Inv2
import Deadlock.Proof
import Deadlock.Theorem

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

theorem await_callee_unterminable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .awaitReply dst k) (t : Template)
    (ht : templateOf I.desc (tname dst) = some t) : t.terminable = false := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨_, e, he, _, _, hdst, _, heff, _⟩ := described_reply I w hI id dst k hph
  exact call_edge_unterminable I.desc hG e he heff t (by simpa [hdst] using ht)

theorem parked_call_unterminable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .parked dst true k) (t : Template)
    (ht : templateOf I.desc (tname dst) = some t) : t.terminable = false := by
  have hI := inv_reachable I N w hL hR
  obtain ⟨_, e, he, _, _, hdst, _, heff, _⟩ := described_park I w hI id dst true k hph
  exact call_edge_unterminable I.desc hG e he heff t (by simpa [hdst] using ht)

theorem resume_life (a : Actor) (b : Bool) (dst : InstId) : (resumeSender a b dst).life = a.life := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases b <;> simp [resumeSender, hph, proceed_life]
  | _ => simp [resumeSender, hph]

theorem proceed_phase_same (a b : Actor) (k : Cont) : (proceed a k).phase = (proceed b k).phase := by
  cases hk : k.rest <;> simp [proceed, hk]

theorem release_keeps_proceed (w : World) (id : InstId) (ps : List Parked) (sender : InstId) (k : Cont)
    (hp : (w.st sender).phase = (proceed (w.st sender) k).phase) :
    ((releaseParked w id ps).st sender).phase = (proceed (w.st sender) k).phase := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hp
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih _ hp
    · rw [if_neg hskip]
      let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
      by_cases hs : sender = p.sender
      · have hp' : (w'.st sender).phase = (proceed (w.st sender) k).phase := by
          cases hk : k.rest with
          | nil =>
            have hph : (w.st sender).phase = .idle := by simpa [proceed, hk] using hp
            simp [w', setActor, ← hs, resumeSender, hph, proceed, hk]
          | cons _ _ =>
            have hph : (w.st sender).phase = .run k := by simpa [proceed, hk] using hp
            simp [w', setActor, ← hs, resumeSender, hph, proceed, hk]
        have hp'' : (w'.st sender).phase = (proceed (w'.st sender) k).phase := by
          rw [hp', proceed_phase_same (w.st sender) (w'.st sender)]
        have hih := ih w' hp''
        rw [proceed_phase_same (w'.st sender) (w.st sender)] at hih
        simpa [releaseParked] using hih
      · have hw : (w'.st sender) = w.st sender := by
          simp [w', setActor, hs]
        have hp' : (w'.st sender).phase = (proceed (w'.st sender) k).phase := by
          simpa [hw, proceed_phase_same (w.st sender) (w'.st sender)] using hp
        have hih := ih w' hp'
        rw [proceed_phase_same (w'.st sender) (w.st sender)] at hih
        simpa [releaseParked] using hih

/-- `releaseParked` resumes a non-call sender. A parked call is skipped, and a
killing terminate is refused while any parked call remains. -/
theorem release_resumes_send (w : World) (id : InstId) (ps : List Parked) (sender : InstId)
    (k : Cont) (hmem : ∃ p, p ∈ ps ∧ p.sender = sender ∧ p.isCall = false)
    (hne : sender ≠ id) (hph : (w.st sender).phase = .parked id false k) :
    ((releaseParked w id ps).st sender).phase = (proceed (w.st sender) k).phase := by
  suffices ∀ ps w, (∃ p, p ∈ ps ∧ p.sender = sender ∧ p.isCall = false) →
      (w.st sender).phase = .parked id false k →
      ((releaseParked w id ps).st sender).phase = (proceed (w.st sender) k).phase from
    this ps w hmem hph
  intro ps
  induction ps with
  | nil =>
    intro w hex _
    obtain ⟨_, hp, _⟩ := hex
    cases hp
  | cons p ps ih =>
    intro w hex hph
    obtain ⟨p0, hp0, hs0, hc0⟩ := hex
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · have hprop : p.isCall = true ∨ p.sender = id := by
        simpa [Bool.or_eq_true, decide_eq_true_eq] using hskip
      have hex' : ∃ q, q ∈ ps ∧ q.sender = sender ∧ q.isCall = false := by
        cases hp0 with
        | head =>
          rcases hprop with hc | hid
          · simp [hc] at hc0
          · exact False.elim (hne (hs0.symm.trans hid))
        | tail _ ht => exact ⟨p0, ht, hs0, hc0⟩
      rw [if_pos hskip]
      exact ih w hex' hph
    · rw [if_neg hskip]
      by_cases hself : sender = p.sender
      · let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
        have hnow : (w'.st sender).phase = (proceed (w'.st sender) k).phase := by
          simp [w', setActor, ← hself, resumeSender, hph]
          cases hk : k.rest <;> simp [proceed, hk]
        have hgot := release_keeps_proceed w' id ps sender k hnow
        rw [proceed_phase_same (w'.st sender) (w.st sender)] at hgot
        simpa [releaseParked, w'] using hgot
      · have hex' : ∃ q, q ∈ ps ∧ q.sender = sender ∧ q.isCall = false := by
          cases hp0 with
          | head => exact False.elim (hself hs0.symm)
          | tail _ ht => exact ⟨p0, ht, hs0, hc0⟩
        let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
        have hph' : (w'.st sender).phase = .parked id false k := by
          simp [w', setActor, hself, hph]
        have hgot := ih w' hex' hph'
        rw [proceed_phase_same (w'.st sender) (w.st sender)] at hgot
        simpa [releaseParked, w'] using hgot

/-- A node of least residual rank is not blocked on a live partner. Either wait
would be a residual edge to a strictly lower node. -/
theorem minimal_not_blocked (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hO : OccInv I w) (id dst : InstId) (k : Cont)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hmin : ∀ n, heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) ≤
      heightOf hs n) :
    ((w.st id).phase = .parked dst false k → (w.st dst).life ≠ .alive) ∧
      ((w.st id).phase = .awaitReply dst k → (w.st dst).life ≠ .alive) := by
  constructor
  · intro hph hlive
    have hdrop := park_below I hL hG N w hR hO id dst k hs hok hph hlive
    have hle := hmin ({ template := tname dst, state := (w.st dst).typestate } : Node)
    omega
  · intro hph hlive
    have hdrop := reply_below I hL hG N w hR id dst k hs hok hph hlive
    have hle := hmin ({ template := tname dst, state := (w.st dst).typestate } : Node)
    omega

/-- An accepts-call program is a straight line: one `reply`, and no `terminate`
before it. There is no other path through the handler. -/
theorem call_program_replies (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (hacc : tr.acceptsCall = true) (t : Template) (ht : templateOf I.desc tr.template = some t) :
    replyCount tr.program = 1 ∧ terminateBeforeReply tr.program = false := by
  have hok := transitionOk_of_mem I hL tr hm
  simp only [transitionOk, ht, hacc, ite_true] at hok
  repeat rw [Bool.and_eq_true] at hok
  have hrep := hok.1.1.2
  have hcount : replyCount tr.program = 1 := beq_iff_eq.mp hrep.1
  have hbefore : terminateBeforeReply tr.program = false := by
    cases hb : terminateBeforeReply tr.program
    · rfl
    · simp [hb] at hrep
  exact ⟨hcount, hbefore⟩

theorem bulk_keeps_run (I : Impl) (w : World) (id : InstId) (w' : World) (s : InstId) (k : Cont)
    (hp : (w.st s).phase = .run k) (hne : s ≠ id) (h : receiveBulk I w id = some w') :
    (w'.st s).phase = .run k := by
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
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ p.msg w1 a1 s hdel
          have hph1 : (w1.st s).phase = .run k := by simpa [hst] using hp
          have hset : ((setActor w1 id a1).st s).phase = .run k := by
            simp [setActor, hne, hph1]
          have hcred := credit_preserves_run (setActor w1 id a1) (tname id) p.msg.sender s k hset
          by_cases hs : s = p.sender
          · have hrun := resumeSender_run ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender)
              p.isCall id k (by simpa [hs] using hcred)
            simpa [setActor, hs] using hrun
          · simpa [setActor, hs] using hcred
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          exact credit_preserves_run (setActor w1 id a1) (tname id) m.sender s k
            (by simp [setActor, hne, hst, hp])
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          have hph1 : (w1.st s).phase = .run k := by simpa [hst] using hp
          by_cases hs : s = p.sender
          · have hset : ((setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps }).st s).phase = .run k := by
              simp [setActor, hne, hph1]
            have hcred := credit_preserves_run _ (tname id) m.sender s k hset
            have hrun := resumeSender_run _ p.isCall id k (by simpa [hs] using hcred)
            simpa [setActor, hs] using hrun
          · have hset : ((setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps }).st s).phase = .run k := by
              simp [setActor, hne, hph1]
            have hcred := credit_preserves_run _ (tname id) m.sender s k hset
            simpa [setActor, hs] using hcred

/-- One step of someone else does not replace a running continuation. -/
theorem step_keeps_run (I : Impl) (a : Action) (w w' : World) (hO : OccInv I w) (s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k) (hl : (w.st s).life = .alive)
    (h : apply I a w = some w') (hnot : a ≠ .exec s) : (w'.st s).phase = .run k := by
  cases a with
  | exec id =>
    have hne : s ≠ id := by
      intro hs
      apply hnot
      simp [hs]
    simp [apply] at h
    unfold execHead at h
    by_cases hlive : (w.st id).life = .alive
    · simp [hlive] at h
      cases hph : (w.st id).phase with
      | run k0 =>
        simp [hph] at h
        cases h
        exact execRun_preserves_other_run I w id (w.st id) k0 k s hne hp hph
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlive] at h
  | finish id =>
    simp [apply, finishWait] at h
    split at h
    · next k0 heq =>
      cases h
      have hne : s ≠ id := by
        intro hs
        rw [← hs] at heq
        simp [hp] at heq
      simp [setActor, hne, hp]
    · next k0 heq =>
      cases h
      have hne : s ≠ id := by
        intro hs
        rw [← hs] at heq
        simp [hp] at heq
      simp [setActor, hne, hp]
    · cases h
  | spawn template =>
    simp [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        have hmem := hO.aliveIn s hl
        have hfresh : s ≠ InstId.peer template (w.nextIx template) := by
          intro hs
          have hix := hO.indexed template (w.nextIx template)
          rw [← hs] at hix
          exact absurd (hix hmem) (by omega)
        simp [readCells_st, setActor, hfresh, withTokens, hp]
      · cases h
  | recvPrio id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      rw [← hs] at h
      simp [receivePrio, hp] at h
      split at h <;> cases h
    unfold receivePrio at h
    cases hprio : (w.st id).prio with
    | nil => simp [hprio] at h
    | cons m ms =>
      simp [hprio] at h
      split at h
      · simp at h
      · next w1 a1 hdel =>
        cases h.2
        have hst := deliver_st I w id _ m w1 a1 s hdel
        simp [setActor, hne, hst, hp]
  | recvBulk id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      rw [← hs] at h
      simp [receiveBulk, hp] at h
    exact bulk_keeps_run I w id w' s k hp hne h

theorem proceed_run_rest (a : Actor) (k k' : Cont) (h : (proceed a k).phase = .run k') :
    k'.rest = k.rest ∧ k.rest ≠ [] := by
  cases hk : k.rest with
  | nil => simp [proceed, hk] at h
  | cons _ _ =>
    simp [proceed, hk] at h
    exact ⟨by rw [← h]; simp [hk], by simp [hk]⟩

theorem after_shorter (k k' : Cont) (a : Actor) (hrest : k.rest ≠ [])
    (h : (proceed a (afterHead k)).phase = .run k') : k'.rest.length < k.rest.length := by
  have htail : (afterHead k).rest = k.rest.tail := by simp [afterHead]
  have ⟨heq, hne⟩ := proceed_run_rest a (afterHead k) k' h
  rw [heq, htail]
  cases hk : k.rest with
  | nil => exact absurd hk hrest
  | cons _ es => simp [hk]

/-- A `terminate` anywhere in a list is still there after a head is pushed back. -/
theorem hasTerminate_cons (e : Eff) (es : List Eff) (h : hasTerminate es = true) :
    hasTerminate (e :: es) = true := by
  cases e <;> simp [hasTerminate, h]

/-- The list a phase is still obliged to run, when it has one. -/
def carried : Phase → Option (List Eff)
  | .run k => some k.rest
  | .parked _ _ k => some k.rest
  | .awaitReply _ k => some k.rest
  | .awaitEffect k => some k.rest
  | .awaitPeer k => some k.rest
  | _ => none

/-- A continuation that still contains `terminate` was installed from a checked
transition, so the actor's template is terminable. `programOk` does not say
this: `effectsOk` skips `terminate`. -/
def TermOk (I : Impl) (w : World) : Prop :=
  ∀ id es, carried (w.st id).phase = some es → hasTerminate es = true →
    terminableName I.desc (tname id)

theorem term_ok_init (I : Impl) (N : Nat) : TermOk I (initWorld I N) := by
  intro id es hc _
  simp [init_phase, carried] at hc

theorem term_ok_replace (I : Impl) (w : World) (id : InstId) (a : Actor) (hT : TermOk I w)
    (hnew : ∀ es, carried a.phase = some es → hasTerminate es = true →
      terminableName I.desc (tname id)) : TermOk I (setActor w id a) := by
  intro i es hc ht
  by_cases hi : i = id
  · rw [hi] at hc ⊢
    simp [setActor] at hc
    exact hnew es hc ht
  · simp [setActor, hi] at hc
    exact hT i es hc ht

theorem term_ok_phase (I : Impl) (w w' : World) (hT : TermOk I w)
    (h : ∀ i, (w'.st i).phase = (w.st i).phase) : TermOk I w' := by
  intro i es hc ht
  rw [h i] at hc
  exact hT i es hc ht

theorem term_program (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (hterm : hasTerminate tr.program = true) (t : Template)
    (ht : templateOf I.desc tr.template = some t) : t.terminable = true := by
  have hok := transitionOk_of_mem I hL tr hm
  simp only [transitionOk, ht] at hok
  repeat rw [Bool.and_eq_true] at hok
  have hcl := hok.1.2
  simp [hterm] at hcl
  cases ht' : t.terminable
  · simp [ht'] at hcl
  · rfl

theorem terminable_no_parked_call (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (id : InstId)
    (hterm : terminableName I.desc (tname id)) : hasParkedCall (w.st id).parked = false := by
  have hM := (inv_reachable I N w hL hR).2.1
  simp [hasParkedCall, List.any_eq_false]
  intro p hp
  obtain ⟨k, hph⟩ := hM.fwd id p hp
  cases hc : p.isCall
  · rfl
  · obtain ⟨t, ht, htm⟩ := hterm
    have hbad := parked_call_unterminable I hL hG N w hR p.sender id k
      (by simpa [hc] using hph) t ht
    simp [htm] at hbad

theorem release_keeps_victim (w : World) (id : InstId) (ps : List Parked) :
    ((releaseParked w id ps).st id).phase = (w.st id).phase ∧
      ((releaseParked w id ps).st id).life = (w.st id).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih _
    · rw [if_neg hskip]
      have hne : p.sender ≠ id := by
        intro hs
        exact hskip (by simp [hs])
      let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
      have hst : (w'.st id) = w.st id := by
        have hswap : id ≠ p.sender := fun h => hne h.symm
        simp [w', setActor, hswap]
      have hih := ih w'
      rw [hst] at hih
      simpa [releaseParked, w'] using hih

/-- A reachable `terminate` head is not the refused branch. The template is
terminable because the program came from a checked transition, and `callTermFails`
says no parked call can name that template, so the kill runs. -/
theorem terminate_commits (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hT : TermOk I w) (id : InstId) (k : Cont) (es : List Eff)
    (hph : (w.st id).phase = .run { k with rest := .terminate :: es })
    (hl : (w.st id).life = .alive) :
    ((execRun I w id (w.st id) { k with rest := .terminate :: es }).st id).life = .dead ∧
      ((execRun I w id (w.st id) { k with rest := .terminate :: es }).st id).phase = .idle := by
  have hterm : terminableName I.desc (tname id) :=
    hT id (.terminate :: es) (by simp [carried, hph]) (by simp [hasTerminate])
  have hcall := terminable_no_parked_call I hL hG N w hR id hterm
  obtain ⟨t, ht, htm⟩ := hterm
  simp [execRun, hph, ht, htm, hcall]
  have hrel := release_keeps_victim
      (setActor (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
        (tname id) ((w.st id).parked)) id
        { (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
            (tname id) ((w.st id).parked)).st id with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] })
      id ((w.st id).parked)
  -- The victim installed above is dead and idle; release does not move it.
  have hbase : ((setActor (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
        (tname id) ((w.st id).parked)) id
        { (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
            (tname id) ((w.st id).parked)).st id with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }).st id).life = .dead ∧
      ((setActor (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
        (tname id) ((w.st id).parked)) id
        { (refundParked (refundMsgs (readCells I.desc w id) (tname id) ((w.st id).box))
            (tname id) ((w.st id).parked)).st id with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }).st id).phase = .idle := by
    simp [setActor]
  exact ⟨hrel.2.trans hbase.1, hrel.1.trans hbase.2⟩

theorem term_ok_of (I : Impl) (hL : LocalOk I) (w w' : World) (hT : TermOk I w)
    (hjust : ∀ i es, carried (w'.st i).phase = some es → hasTerminate es = true →
      (∃ es0, carried (w.st i).phase = some es0 ∧ (es = es0 ∨ ∃ e, es0 = e :: es)) ∨
      ∃ tr ∈ I.transitions, tr.template = tname i ∧ es = tr.program) : TermOk I w' := by
  intro i es hc ht
  rcases hjust i es hc ht with ⟨es0, hc0, hsub⟩ | ⟨tr, hm, htmpl, hprog⟩
  · rcases hsub with rfl | ⟨e, heq⟩
    · exact hT i es hc0 ht
    · exact hT i es0 hc0 (by simpa [heq] using hasTerminate_cons e es ht)
  · rw [← htmpl]
    cases htpl : templateOf I.desc tr.template with
    | none =>
      have hok := transitionOk_of_mem I hL tr hm
      simp [transitionOk, htpl] at hok
    | some t =>
      exact ⟨t, htpl, term_program I hL tr hm (by simpa [hprog] using ht) t htpl⟩

theorem term_ok_finish (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hT : TermOk I w)
    (h : finishWait w id = some w') : TermOk I w' := by
  apply term_ok_of I hL w w' hT
  intro i es hc ht
  unfold finishWait at h
  split at h
  · next k heq =>
    cases h
    by_cases hi : i = id
    · rw [hi] at hc ⊢
      simp [setActor] at hc
      cases hk : k.rest with
      | nil => simp [proceed, hk, carried] at hc
      | cons _ _ =>
        simp [proceed, hk, carried] at hc
        exact Or.inl ⟨k.rest, by simp [carried, hi, heq], Or.inl (by simp [hc, hk])⟩
    · simp [setActor, hi] at hc
      exact Or.inl ⟨es, hc, Or.inl rfl⟩
  · next k heq =>
    cases h
    by_cases hi : i = id
    · rw [hi] at hc ⊢
      simp [setActor] at hc
      cases hk : k.rest with
      | nil => simp [proceed, hk, carried] at hc
      | cons _ _ =>
        simp [proceed, hk, carried] at hc
        exact Or.inl ⟨k.rest, by simp [carried, hi, heq], Or.inl (by simp [hc, hk])⟩
    · simp [setActor, hi] at hc
      exact Or.inl ⟨es, hc, Or.inl rfl⟩
  · cases h

theorem deliver_carries (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (es : List Eff) (h : deliver I w id a m = some (w1, a1))
    (hc : carried a1.phase = some es) : ∃ tr ∈ I.transitions, tr.template = tname id ∧ es = tr.program := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · next heq =>
      split at h
      · cases h
      · cases h
        simp [carried] at hc
    · next tr heq =>
      split at h
      · cases h
      · cases h
        by_cases hempty : tr.program.isEmpty = true
        · simp [hempty, carried] at hc
        · simp [hempty, carried] at hc
          have hmem := findTr_mem I (tname id) a.typestate m.label tr heq
          exact ⟨tr, hmem.1, hmem.2.1, by simpa [hc]⟩

theorem term_ok_prio (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hT : TermOk I w)
    (h : receivePrio I w id = some w') : TermOk I w' := by
  apply term_ok_of I hL w w' hT
  intro i es hc ht
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      by_cases hi : i = id
      · rw [hi] at hc ⊢
        have hc' : carried a1.phase = some es := by
          simpa [setActor] using hc
        obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc'
        exact Or.inr ⟨tr, hm, htmpl, hprog⟩
      · have hst := deliver_st I w id _ m w1 a1 i hdel
        have hc0 : carried (w.st i).phase = some es := by
          simpa [setActor, hi, hst] using hc
        exact Or.inl ⟨es, hc0, Or.inl rfl⟩

theorem carried_resume (a : Actor) (b : Bool) (dst : InstId) (es : List Eff)
    (h : carried (resumeSender a b dst).phase = some es) : carried a.phase = some es := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases b with
    | true => simp [resumeSender, hph, carried] at h ⊢; exact h
    | false =>
      cases hk : k.rest with
      | nil => simp [resumeSender, hph, proceed, hk, carried] at h
      | cons _ _ => simp [resumeSender, hph, proceed, hk, carried] at h ⊢; exact h
  | idle => simp [resumeSender, hph, carried] at h
  | run k => simp [resumeSender, hph, carried] at h ⊢; exact h
  | awaitReply _ k => simp [resumeSender, hph, carried] at h ⊢; exact h
  | awaitEffect k => simp [resumeSender, hph, carried] at h ⊢; exact h
  | awaitPeer k => simp [resumeSender, hph, carried] at h ⊢; exact h
  | crashed => simp [resumeSender, hph, carried] at h

theorem term_ok_spawn (I : Impl) (hL : LocalOk I) (w w' : World) (template : String) (hT : TermOk I w)
    (h : spawn I w template = some w') : TermOk I w' := by
  apply term_ok_of I hL w w' hT
  intro i es hc ht
  unfold spawn at h
  split at h
  · cases h
  · next t _ =>
    split at h
    · cases h
      by_cases hi : i = InstId.peer template (w.nextIx template)
      · simp [readCells_st, setActor, hi, withTokens, carried] at hc
      · simp [readCells_st, setActor, hi] at hc
        exact Or.inl ⟨es, hc, Or.inl rfl⟩
    · cases h

theorem term_ok_bulk (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hT : TermOk I w)
    (h : receiveBulk I w id = some w') : TermOk I w' := by
  apply term_ok_of I hL w w' hT
  intro i es hc ht
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
        · cases h
        · next w1 a1 hdel =>
          cases h
          by_cases hid : i = id
          · rw [hid] at hc ⊢
            by_cases hs : id = p.sender
            · rw [hs] at hc
              have hph : ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender).phase = a1.phase := by
                simp [phase_credit, setActor, hs]
              have hold := carried_resume
                ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender) p.isCall p.sender es
                (by simpa [setActor, hs] using hc)
              have hc1 : carried a1.phase = some es := by simpa [hph] using hold
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ p.msg w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
            · have hc1 : carried a1.phase = some es := by
                simpa [setActor, hs, phase_credit] using hc
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ p.msg w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · by_cases hs : i = p.sender
            · rw [hs] at hc
              have hpre : carried ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender).phase =
                  some es := carried_resume _ p.isCall id es (by simpa [setActor] using hc)
              have hst := deliver_st I w id _ p.msg w1 a1 p.sender hdel
              have hne : p.sender ≠ id := fun h => hid (hs.trans h)
              have hc0 : carried (w.st p.sender).phase = some es := by
                simpa [setActor, hne, phase_credit, hst] using hpre
              exact Or.inl ⟨es, by simpa [hs] using hc0, Or.inl rfl⟩
            · have hst := deliver_st I w id _ p.msg w1 a1 i hdel
              have hc0 : carried (w.st i).phase = some es := by
                simpa [setActor, hs, hid, phase_credit, hst] using hc
              exact Or.inl ⟨es, hc0, Or.inl rfl⟩
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          by_cases hid : i = id
          · rw [hid] at hc ⊢
            have hc1 : carried a1.phase = some es := by
              simpa [setActor, phase_credit] using hc
            obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
            exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · have hst := deliver_st I w id _ m w1 a1 i hdel
            have hc0 : carried (w.st i).phase = some es := by
              simpa [setActor, hid, phase_credit, hst] using hc
            exact Or.inl ⟨es, hc0, Or.inl rfl⟩
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hphA : admitted.phase = a1.phase := by simp [admitted]
          by_cases hid : i = id
          · rw [hid] at hc ⊢
            by_cases hs : id = p.sender
            · rw [hs] at hc
              have hpre := carried_resume _ p.isCall p.sender es (by simpa [setActor, hs] using hc)
              have hc1 : carried a1.phase = some es := by
                simpa [phase_credit, setActor, hphA, hs] using hpre
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
            · have hc1 : carried a1.phase = some es := by
                simpa [setActor, hs, phase_credit, hphA] using hc
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · by_cases hs : i = p.sender
            · rw [hs] at hc
              have hpre := carried_resume _ p.isCall id es (by simpa [setActor] using hc)
              have hst := deliver_st I w id _ m w1 a1 p.sender hdel
              have hne : p.sender ≠ id := fun h => hid (hs.trans h)
              have hc0 : carried (w.st p.sender).phase = some es := by
                simpa [setActor, hne, phase_credit, hst, hphA] using hpre
              exact Or.inl ⟨es, by simpa [hs] using hc0, Or.inl rfl⟩
            · have hst := deliver_st I w id _ m w1 a1 i hdel
              have hc0 : carried (w.st i).phase = some es := by
                simpa [setActor, hs, hid, phase_credit, hst, hphA] using hc
              exact Or.inl ⟨es, hc0, Or.inl rfl⟩

theorem carried_proceed (a : Actor) (k : Cont) (es : List Eff)
    (h : carried (proceed a k).phase = some es) : es = k.rest := by
  cases hk : k.rest with
  | nil => simp [proceed, hk, carried] at h
  | cons _ _ =>
    simp [proceed, hk, carried] at h
    exact h.symm

theorem enqueue_carried (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (b : Bool) (k : Cont) (es : List Eff)
    (h : carried ((enqueueOrPark w D sender dst msg b k).st sender).phase = some es) : es = k.rest := by
  unfold enqueueOrPark at h
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive] at h
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom] at h
      by_cases hsame : sender = dst
      · cases b with
        | true => simp [hsame, setActor, carried] at h; exact h.symm
        | false =>
          cases hk : k.rest <;> simp [hsame, setActor, proceed, hk, carried] at h
          · exact h.symm
      · cases b with
        | true => simp [hsame, setActor, carried] at h; exact h.symm
        | false =>
          cases hk : k.rest <;> simp [hsame, setActor, proceed, hk, carried] at h
          · exact h.symm
    · simp [hroom] at h
      by_cases hsame : sender = dst <;> simp [hsame, setActor, carried] at h <;> exact h.symm
  · cases hk : k.rest <;> simp [hlive, setActor, proceed, hk, carried] at h
    · exact h.symm

theorem release_carried (w : World) (id : InstId) (ps : List Parked) (i : InstId) (es : List Eff)
    (h : carried ((releaseParked w id ps).st i).phase = some es) : carried (w.st i).phase = some es := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using h
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons] at h
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip] at h
      exact ih _ h
    · rw [if_neg hskip] at h
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id)) h
      by_cases hi : i = p.sender
      · exact carried_resume _ false id es (by simpa [setActor, hi] using hmid)
      · simpa [setActor, hi] using hmid

theorem reply_sender_rest (w : World) (sender : InstId) (k : Cont) (es : List Eff)
    (h : carried ((performReply w sender k).st sender).phase = some es) : es = (afterHead k).rest := by
  unfold performReply at h
  cases hr : k.replyTo with
  | none =>
    simp [hr, setActor] at h
    exact carried_proceed _ _ _ h
  | some caller =>
    simp [hr] at h
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender <;> simp [hph, hd, setActor] at h <;> exact carried_proceed _ _ _ h
    | idle => simp [hph, setActor] at h; exact carried_proceed _ _ _ h
    | run ck => simp [hph, setActor] at h; exact carried_proceed _ _ _ h
    | parked _ _ ck => simp [hph, setActor] at h; exact carried_proceed _ _ _ h
    | awaitEffect ck => simp [hph, setActor] at h; exact carried_proceed _ _ _ h
    | awaitPeer ck => simp [hph, setActor] at h; exact carried_proceed _ _ _ h
    | crashed => simp [hph, setActor] at h; exact carried_proceed _ _ _ h

theorem term_ok_exec (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (k : Cont) (hT : TermOk I w)
    (hph : (w.st id).phase = .run k) : TermOk I (execRun I w id (w.st id) k) := by
  apply term_ok_of I hL w _ hT
  intro i es hc ht
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      simp [execRun, hrest, setActor] at hc
      by_cases hi : i = id
      · simp [hi, carried] at hc
      · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
    | cons e tail =>
      have hold : carried (w.st id).phase = some (e :: tail) := by simp [carried, hph, hrest]
      cases e with
      | send dst label hint =>
        simp [execRun, hrest] at hc
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := carried_proceed _ (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) es
              (by simpa [setActor] using hc)
            exact Or.inl ⟨.send dst label hint :: tail, hold, Or.inr ⟨.send dst label hint, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
        | some dstId =>
          simp [hr] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false
              (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) es hc
            exact Or.inl ⟨.send dst label hint :: tail, hold, Or.inr ⟨.send dst label hint, by simp [afterHead, heq]⟩⟩
          · have hsame := enqueue_phase_other w I.desc id dstId ⟨label, id, none⟩ false
              (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) i hi
            exact Or.inl ⟨es, by simpa [hsame] using hc, Or.inl rfl⟩
      | call dst label hint =>
        simp [execRun, hrest] at hc
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := carried_proceed _ (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) es
              (by simpa [setActor] using hc)
            exact Or.inl ⟨.call dst label hint :: tail, hold, Or.inr ⟨.call dst label hint, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
        | some dstId =>
          simp [hr] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true
              (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) es hc
            exact Or.inl ⟨.call dst label hint :: tail, hold, Or.inr ⟨.call dst label hint, by simp [afterHead, heq]⟩⟩
          · have hsame := enqueue_phase_other w I.desc id dstId ⟨label, id, some id⟩ true
              (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) i hi
            exact Or.inl ⟨es, by simpa [hsame] using hc, Or.inl rfl⟩
      | trySend dst label hint =>
        simp [execRun, hrest] at hc
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
            exact Or.inl ⟨.trySend dst label hint :: tail, hold,
              Or.inr ⟨.trySend dst label hint, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
        | some dstId =>
          simp [hr] at hc
          split at hc
          · by_cases hi : i = id
            · rw [hi] at hc ⊢
              by_cases hdst : dstId = id
              · simp [hdst, setActor] at hc
                have heq := carried_proceed _ _ es hc
                exact Or.inl ⟨.trySend dst label hint :: tail, hold,
                  Or.inr ⟨.trySend dst label hint, by simp [afterHead, heq]⟩⟩
              · simp [hdst, setActor] at hc
                have heq := carried_proceed _ _ es hc
                exact Or.inl ⟨.trySend dst label hint :: tail, hold,
                  Or.inr ⟨.trySend dst label hint, by simp [afterHead, heq]⟩⟩
            · by_cases hd : i = dstId
              · have hne : dstId ≠ id := fun h => hi (hd.trans h)
                have hswap : id ≠ dstId := fun h => hne h.symm
                simp [setActor, hi, hd, hne, hswap] at hc
                exact Or.inl ⟨es, by simpa [hd] using hc, Or.inl rfl⟩
              · simp [setActor, hi, hd] at hc
                exact Or.inl ⟨es, hc, Or.inl rfl⟩
          · by_cases hi : i = id
            · rw [hi] at hc ⊢
              have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
              exact Or.inl ⟨.trySend dst label hint :: tail, hold,
                Or.inr ⟨.trySend dst label hint, by simp [afterHead, heq]⟩⟩
            · exact Or.inl ⟨es, by simpa [setActor, hi] using hc, Or.inl rfl⟩
      | reply =>
        simp [execRun, hrest] at hc
        unfold performReply at hc
        by_cases hi : i = id
        · rw [hi] at hc ⊢
          have heq := reply_sender_rest w id ⟨.reply :: tail, toState, replyTo⟩ es hc
          exact Or.inl ⟨.reply :: tail, hold, Or.inr ⟨.reply, by simp [afterHead, heq]⟩⟩
        · cases hto : replyTo with
          | none =>
            simp [hto, setActor, hi] at hc
            exact Or.inl ⟨es, hc, Or.inl rfl⟩
          | some caller =>
            simp [hto] at hc
            cases hcall : (w.st caller).phase with
            | awaitReply dst ck =>
              by_cases hd : dst = id
              · simp [hcall, hd, setActor, hi] at hc
                by_cases hc2 : i = caller
                · rw [hc2] at hc
                  have heq := carried_proceed _ ck es (by simpa [setActor] using hc)
                  exact Or.inl ⟨ck.rest, by simp [carried, hc2, hcall], Or.inl (by simp [heq])⟩
                · simp [hc2] at hc
                  exact Or.inl ⟨es, hc, Or.inl rfl⟩
              · simp [hcall, hd, setActor, hi] at hc
                exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | _ =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
      | selfSchedule label =>
        simp [execRun, hrest] at hc
        split at hc
        · by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
            exact Or.inl ⟨.selfSchedule label :: tail, hold,
              Or.inr ⟨.selfSchedule label, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [setActor, hi] using hc, Or.inl rfl⟩
        · split at hc
          · by_cases hi : i = id
            · rw [hi] at hc ⊢
              have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
              exact Or.inl ⟨.selfSchedule label :: tail, hold,
                Or.inr ⟨.selfSchedule label, by simp [afterHead, heq]⟩⟩
            · exact Or.inl ⟨es, by simpa [setActor, hi] using hc, Or.inl rfl⟩
          · by_cases hi : i = id
            · simp [setActor, hi, carried] at hc
            · exact Or.inl ⟨es, by simpa [setActor, hi] using hc, Or.inl rfl⟩
      | cell dst label value =>
        simp [execRun, hrest, setCell] at hc
        by_cases hi : i = id
        · rw [hi] at hc ⊢
          cases hdirty : (w.cell dst label).dirty with
          | false =>
            rw [if_neg (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at hc
            rw [wakeReaders] at hc
            rw [wakes_phase (readersOf _ dst) I.desc _ dst label id id] at hc
            simp [setActor] at hc
            have heq := carried_proceed _ _ es hc
            exact Or.inl ⟨.cell dst label value :: tail, hold,
              Or.inr ⟨.cell dst label value, by simp [afterHead, heq]⟩⟩
          | true =>
            simp [hdirty, setActor] at hc
            have heq := carried_proceed _ _ es hc
            exact Or.inl ⟨.cell dst label value :: tail, hold,
              Or.inr ⟨.cell dst label value, by simp [afterHead, heq]⟩⟩
        · cases hdirty : (w.cell dst label).dirty with
          | false =>
            rw [if_neg (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at hc
            rw [wakeReaders] at hc
            rw [wakes_phase (readersOf _ dst) I.desc _ dst label id i] at hc
            simp [setActor, hi] at hc
            exact Or.inl ⟨es, hc, Or.inl rfl⟩
          | true =>
            simp [hdirty, setActor, hi] at hc
            exact Or.inl ⟨es, hc, Or.inl rfl⟩
      | internal =>
        simp [execRun, hrest, setActor] at hc
        by_cases hi : i = id
        · rw [hi] at hc ⊢
          simp [carried, afterHead] at hc
          exact Or.inl ⟨.internal :: tail, hold, Or.inr ⟨.internal, congrArg (List.cons .internal) hc⟩⟩
        · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
      | peer =>
        simp [execRun, hrest, setActor] at hc
        by_cases hi : i = id
        · rw [hi] at hc ⊢
          simp [carried, afterHead] at hc
          exact Or.inl ⟨.peer :: tail, hold, Or.inr ⟨.peer, congrArg (List.cons .peer) hc⟩⟩
        · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
      | terminate =>
        simp only [execRun, hrest] at hc
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simp [htpl] at hc
          exact Or.inl ⟨es, hc, Or.inl rfl⟩
        | some t =>
          simp only [htpl] at hc
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · rw [if_pos hkill] at hc
            by_cases hi : i = id
            · rw [hi] at hc
              let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
                (tname id) (w.st id).parked
              let dead : Actor := { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
              have hv := (release_keeps_victim (setActor base id dead) id (w.st id).parked).1
              rw [hv] at hc
              simp [base, dead, setActor, carried] at hc
            · have hrel := release_carried _ id (w.st id).parked i es hc
              have hpre : carried (w.st i).phase = some es := by
                simpa [readCells_st, phase_refund, phase_refundP, setActor, hi] using hrel
              exact Or.inl ⟨es, hpre, Or.inl rfl⟩
          · rw [if_neg hkill] at hc
            exact Or.inl ⟨es, hc, Or.inl rfl⟩

theorem term_ok_head (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hT : TermOk I w)
    (h : execHead I w id = some w') : TermOk I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact term_ok_exec I hL w id k hT hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem term_ok_apply (I : Impl) (hL : LocalOk I) (a : Action) (w w' : World) (hT : TermOk I w)
    (h : apply I a w = some w') : TermOk I w' := by
  cases a with
  | recvBulk id => simpa [apply] using term_ok_bulk I hL w w' id hT h
  | recvPrio id => simpa [apply] using term_ok_prio I hL w w' id hT h
  | exec id => simpa [apply] using term_ok_head I hL w w' id hT h
  | finish id => simpa [apply] using term_ok_finish I hL w w' id hT h
  | spawn template => simpa [apply] using term_ok_spawn I hL w w' template hT h

theorem term_ok_reachable (I : Impl) (hL : LocalOk I) (N : Nat) (w : World)
    (hR : Reachable I N w) : TermOk I w := by
  induction hR with
  | init => exact term_ok_init I N
  | step w w' a _ h ih => exact term_ok_apply I hL a w w' ih h

/-- `Inv2` plus the fact that a carried `terminate` came from a checked transition. -/
def Inv3 (I : Impl) (w : World) : Prop := Inv2 I w ∧ TermOk I w

theorem inv3_init (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) : Inv3 I (initWorld I N) :=
  ⟨inv2_init I hL hG N, term_ok_init I N⟩

theorem inv3_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : Inv3 I w :=
  ⟨inv2_reachable I hL hG N w hR, term_ok_reachable I hL N w hR⟩

theorem run_tail_shorter (e : Eff) (tail : List Eff) (k' : Cont) (heq : k'.rest = tail) :
    k'.rest.length < (e :: tail).length := by
  simp [heq]

/-- Every running head that is still `.run` afterwards is a strictly shorter tail.
A `terminate` head is not still `.run`: the refusal is unreachable. -/
theorem exec_shortens (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id : InstId) (k k' : Cont)
    (hph : (w.st id).phase = .run k) (hl : (w.st id).life = .alive)
    (h : ((execRun I w id (w.st id) k).st id).phase = .run k') :
    k'.rest.length < k.rest.length := by
  have hT := term_ok_reachable I hL N w hR
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil => simp [execRun, hrest, setActor] at h
    | cons e tail =>
      cases e with
      | terminate =>
        have hidle := (terminate_commits I hL hG N w hR hT id
          { rest := .terminate :: tail, toState := toState, replyTo := replyTo } tail
          (by simpa [hrest] using hph) hl).2
        simpa [hrest, hidle] using h
      | send dst label hint =>
        simp [execRun, hrest] at h
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at h
          exact after_shorter ⟨.send dst label hint :: tail, toState, replyTo⟩ k' _ (by simp [hrest]) h
        | some dstId =>
          simp [hr] at h
          have hc : carried ((enqueueOrPark w I.desc id dstId ⟨label, id, none⟩ false
              (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩)).st id).phase = some k'.rest := by
            simp [carried, h]
          have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false _ k'.rest hc
          exact run_tail_shorter _ _ _ (by simp [afterHead, hrest, heq])
      | call dst label hint =>
        simp [execRun, hrest] at h
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at h
          exact after_shorter ⟨.call dst label hint :: tail, toState, replyTo⟩ k' _ (by simp [hrest]) h
        | some dstId =>
          simp [hr] at h
          have hc : carried ((enqueueOrPark w I.desc id dstId ⟨label, id, some id⟩ true
              (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩)).st id).phase = some k'.rest := by
            simp [carried, h]
          have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true _ k'.rest hc
          exact run_tail_shorter _ _ _ (by simp [afterHead, hrest, heq])
      | trySend dst label hint =>
        simp [execRun, hrest] at h
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at h
          exact after_shorter _ k' _ (by simp [hrest]) h
        | some dstId =>
          simp [hr] at h
          split at h
          · by_cases hdst : dstId = id <;> simp [hdst, setActor] at h
            · exact after_shorter _ k' _ (by simp [hrest]) h
            · exact after_shorter _ k' _ (by simp [hrest]) h
          · simp [setActor] at h
            exact after_shorter _ k' _ (by simp [hrest]) h
      | reply =>
        simp [execRun, hrest] at h
        have hc : carried ((performReply w id ⟨.reply :: tail, toState, replyTo⟩).st id).phase = some k'.rest := by
          simp [carried, h]
        have heq := reply_sender_rest w id _ k'.rest hc
        exact run_tail_shorter _ _ _ (by simp [afterHead, hrest, heq])
      | selfSchedule label =>
        simp [execRun, hrest] at h
        split at h
        · simp [setActor] at h
          exact after_shorter _ k' _ (by simp [hrest]) h
        · split at h
          · simp [setActor] at h
            exact after_shorter _ k' _ (by simp [hrest]) h
          · simp [setActor, carried] at h
      | cell dst label value =>
        simp [execRun, hrest, setCell] at h
        cases hdirty : (w.cell dst label).dirty with
        | false =>
          rw [if_neg (show ¬ ((w.cell dst label).dirty = true) from by simp [hdirty])] at h
          rw [wakeReaders, wakes_phase (readersOf _ dst) I.desc _ dst label id id] at h
          simp [setActor] at h
          exact after_shorter _ k' _ (by simp [hrest]) h
        | true =>
          simp [hdirty, setActor] at h
          exact after_shorter _ k' _ (by simp [hrest]) h
      | internal =>
        simp [execRun, hrest, setActor, carried] at h
      | peer =>
        simp [execRun, hrest, setActor, carried] at h

theorem cfg_reachable {I : Impl} {N : Nat} (ρ : Run I N) (n : Nat) : Reachable I N (ρ.cfg n) := by
  induction n with
  | zero => simpa [ρ.start] using (Reachable.init : Reachable I N (initWorld I N))
  | succ n ih => exact Reachable.step (ρ.cfg n) (ρ.cfg (n + 1)) (ρ.act n) ih (ρ.valid n)

theorem run_prefix {I : Impl} (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s : InstId) (i n : Nat) (k : Cont)
    (hp : ((ρ.cfg i).st s).phase = .run k)
    (hl : ∀ t, i ≤ t → t < i + n → ((ρ.cfg t).st s).life = .alive)
    (hnot : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .exec s) :
    ((ρ.cfg (i + n)).st s).phase = .run k := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    have hp' := ih
      (fun t h1 h2 => hl t h1 (Nat.lt_trans h2 (Nat.lt_succ_self _)))
      (fun t h1 h2 => hnot t h1 (Nat.lt_trans h2 (Nat.lt_succ_self _)))
    have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.2.1
    have hlife := hl (i + n) (Nat.le_add_right i n) (Nat.lt_succ_self _)
    have hact := hnot (i + n) (Nat.le_add_right i n) (Nat.lt_succ_self _)
    have hstep := step_keeps_run I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) hO s k hp'
      hlife (ρ.valid (i + n)) hact
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

def scanExec (act : Nat → Action) (s : InstId) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if act k = .exec s then k else scanExec act s fuel (k + 1)

theorem scanExec_spec (act : Nat → Action) (s : InstId) (fuel k : Nat)
    (h : ∃ d, d ≤ fuel ∧ act (k + d) = .exec s) :
    k ≤ scanExec act s fuel k ∧ act (scanExec act s fuel k) = .exec s ∧
      ∀ t, k ≤ t → t < scanExec act s fuel k → act t ≠ .exec s := by
  induction fuel generalizing k with
  | zero =>
    obtain ⟨d, hd, hact⟩ := h
    have hd0 : d = 0 := by omega
    simp [scanExec]
    constructor
    · simpa [hd0] using hact
    · intro t h1 h2
      omega
  | succ fuel ih =>
    simp [scanExec]
    by_cases hhere : act k = .exec s
    · simp [hhere]
      intro t h1 h2
      omega
    · simp [hhere]
      obtain ⟨d, hd, hact⟩ := h
      have hnext : ∃ d, d ≤ fuel ∧ act (k + 1 + d) = .exec s := by
        have hd0 : 0 < d := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hhere
          simpa [hz] using hact
        refine ⟨d - 1, by omega, ?_⟩
        have : k + d = k + 1 + (d - 1) := by omega
        simpa [this] using hact
      have ih' := ih (k + 1) hnext
      constructor
      · exact Nat.le_trans (Nat.le_succ k) ih'.1
      constructor
      · exact ih'.2.1
      · intro t ht1 ht2
        by_cases htk : t = k
        · simpa [htk] using hhere
        · exact ih'.2.2 t (by omega) (by omega)

/-- A live actor cannot stay in `.run` forever. Each of its own steps shortens
the continuation, and nothing else replaces that continuation. -/
theorem not_forever_run (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (hF : Fair ρ) (s : InstId) (i : Nat)
    (hl : ∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive)
    (hr : ∀ j, i ≤ j → ∃ k, ((ρ.cfg j).st s).phase = .run k) : False := by
  suffices ∀ n i, (∃ k, ((ρ.cfg i).st s).phase = .run k ∧ k.rest.length = n) →
      (∀ j, i ≤ j → ((ρ.cfg j).st s).life = .alive) →
      (∀ j, i ≤ j → ∃ k, ((ρ.cfg j).st s).phase = .run k) → False by
    obtain ⟨k, hk⟩ := hr i (Nat.le_refl _)
    exact this k.rest.length i ⟨k, hk, rfl⟩ hl hr
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hk hl hr
    obtain ⟨k, hp, hlen⟩ := hk
    have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.exec s) := by
      intro j hj
      obtain ⟨k', hk'⟩ := hr j hj
      exact run_enabled I (ρ.cfg j) s k' hk' (hl j hj)
    obtain ⟨j0, hj0, hact0⟩ := hF.weak (.exec s) i rfl hen
    have hscan := scanExec_spec ρ.act s (j0 - i) i ⟨j0 - i, Nat.le_refl _, by
      simpa [Nat.add_sub_of_le hj0] using hact0⟩
    let m := scanExec ρ.act s (j0 - i) i
    have him : i ≤ m := hscan.1
    have hact : ρ.act m = .exec s := hscan.2.1
    have hmin := hscan.2.2
    have hpre := run_prefix hL hG ρ s i (m - i) k hp
      (fun t h1 _ => hl t h1)
      (fun t h1 h2 => hmin t h1 (by
        have hsum : i + (m - i) = m := Nat.add_sub_of_le him
        omega))
    have hhere : ((ρ.cfg m).st s).phase = .run k := by
      simpa [Nat.add_sub_of_le him] using hpre
    obtain ⟨k', hk'⟩ := hr (m + 1) (Nat.le_trans him (Nat.le_succ _))
    have hrun : execRun I (ρ.cfg m) s ((ρ.cfg m).st s) k = ρ.cfg (m + 1) := by
      have hhead := ρ.valid m
      simp [apply, hact, execHead, hl m him, hhere] at hhead
      exact hhead
    have hshort := exec_shortens I hL hG N (ρ.cfg m) (cfg_reachable ρ m) s k k' hhere (hl m him)
      (by rw [hrun]; exact hk')
    have hlt : k'.rest.length < n := by simpa [hlen] using hshort
    exact ih k'.rest.length hlt (m + 1) ⟨k', hk', rfl⟩
      (fun j hj => hl j (Nat.le_trans (Nat.le_trans him (Nat.le_succ _)) hj))
      (fun j hj => hr j (Nat.le_trans (Nat.le_trans him (Nat.le_succ _)) hj))

end Deadlock
