import Deadlock.Inv2
import Deadlock.CallTag
import Deadlock.Proof
import Deadlock.Theorem

set_option autoImplicit false

namespace Deadlock

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

/-- `resumeSender` rewrites a parked phase only. Any other phase is left as it stands. -/
theorem resume_id_of_not_parked (a : Actor) (b : Bool) (dst : InstId)
    (hn : ∀ d c k, a.phase ≠ .parked d c k) : resumeSender a b dst = a := by
  cases h : a.phase with
  | parked d c k => exact absurd h (hn d c k)
  | idle => simp [resumeSender, h]
  | run k => simp [resumeSender, h]
  | awaitReply d k => simp [resumeSender, h]
  | awaitEffect k => simp [resumeSender, h]
  | awaitPeer k => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem release_keeps_nonparked (w : World) (id : InstId) (ps : List Parked) (s : InstId)
    (hn : ∀ d c k, (w.st s).phase ≠ .parked d c k) :
    ((releaseParked w id ps).st s).phase = (w.st s).phase ∧
      ((releaseParked w id ps).st s).life = (w.st s).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w hn
    · rw [if_neg hskip]
      let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
      have hpl : (w'.st s).phase = (w.st s).phase ∧ (w'.st s).life = (w.st s).life := by
        by_cases hs : s = p.sender
        · have hid := resume_id_of_not_parked (w.st p.sender) false id (by
            intro d c k hbad
            exact hn d c k (by simpa [hs] using hbad))
          simp [w', hs, hid, setActor]
        · simp [w', setActor, hs]
      have hn' : ∀ d c k, (w'.st s).phase ≠ .parked d c k := by
        intro d c k hbad
        exact hn d c k (hpl.1 ▸ hbad)
      have ih' := ih w' hn'
      exact ⟨ih'.1.trans hpl.1, ih'.2.trans hpl.2⟩

/-- A reply rewrites the caller only out of `awaitReply`, and the sender is `sender`. -/
theorem reply_keeps_quiet (w : World) (sender s : InstId) (k : Cont)
    (hp : ∀ d ck, (w.st s).phase ≠ .awaitReply d ck) (hs : s ≠ sender) :
    ((performReply w sender k).st s).phase = (w.st s).phase ∧
      ((performReply w sender k).st s).life = (w.st s).life := by
  unfold performReply
  cases hr : k.replyTo with
  | none =>
    refine ⟨?_, ?_⟩ <;> simp [hr, setActor_other, hs, proceed_life]
  | some caller =>
    by_cases hc : caller = s
    · rw [hc]
      cases hph : (w.st s).phase with
      | awaitReply dst ck => exact absurd hph (hp dst ck)
      | idle => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | run _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | awaitEffect _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | awaitPeer _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | parked _ _ _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | crashed => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
    · cases hph : (w.st caller).phase with
      | awaitReply dst ck =>
        by_cases hd : dst = sender
        · refine ⟨?_, ?_⟩
          · simp only [hph, hd, if_true]
            rw [setActor_other _ sender s _ hs, setActor_other _ caller s _ (Ne.symm hc)]
          · simp only [hph, hd, if_true]
            rw [setActor_other _ sender s _ hs, setActor_other _ caller s _ (Ne.symm hc)]
        · refine ⟨?_, ?_⟩ <;> simp [hph, hd, setActor_other, hs, proceed_life]
      | idle => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | run _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | awaitEffect _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | awaitPeer _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | parked _ _ _ => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]
      | crashed => refine ⟨?_, ?_⟩ <;> simp [hph, setActor_other, hs, proceed_life]

theorem enqueue_life (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
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
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken, proceed_life]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, proceed_life]
           · by_cases hid : i = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor]
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken]
           · by_cases hid : i = dst
             · simp [hid, hlive]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
     · simp [hlive, setActor, proceed_life]
       by_cases hi : i = sender <;> simp [hi, proceed_life])

theorem try_wake_life (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) : ((tryWake D w dstId label writer).st i).life = (w.st i).life := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_life (ids : List InstId) (D : Description) (w : World) (dst label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).life = (w.st i).life := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, try_wake_life]

theorem try_wake_ty (D : Description) (w : World) (dstId : InstId) (label : String) (writer i : InstId) :
    ((tryWake D w dstId label writer).st i).typestate = (w.st i).typestate := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_ty (ids : List InstId) (D : Description) (w : World) (dst label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).typestate = (w.st i).typestate := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, try_wake_ty]

/-- An `exec` of `id` does not rewrite `s` when `s` is neither parked nor awaiting `id`'s reply. -/
theorem exec_keeps_quiet (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (s : InstId)
    (hs : s ≠ id) (hnpark : ∀ d c ck, (w.st s).phase ≠ .parked d c ck)
    (hnreply : ∀ d ck, (w.st s).phase ≠ .awaitReply d ck) :
    ((execRun I w id a k).st s).phase = (w.st s).phase ∧
      ((execRun I w id a k).st s).life = (w.st s).life := by
  cases hk : k.rest with
  | nil =>
    refine ⟨?_, ?_⟩ <;> simp [execRun, hk, setActor_other, hs]
  | cons eff rest =>
    cases eff with
    | send dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => refine ⟨?_, ?_⟩ <;> simp [hr, setActor_other, hs, proceed_life]
      | some dstId =>
        refine ⟨enqueue_phase_other w I.desc id dstId _ false _ s hs,
          enqueue_life w I.desc id dstId _ false _ s⟩
    | trySend dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => refine ⟨?_, ?_⟩ <;> simp [hr, setActor_other, hs, proceed_life]
      | some dstId =>
        simp [hr]
        split
        · by_cases hc : s = dstId
          · by_cases hi : dstId = id
            · exact absurd (hc.trans hi) hs
            · rw [hc]
              refine ⟨?_, ?_⟩
              · rw [setActor_other _ id dstId _ hi]
                simp [setActor, hi]
              · rw [setActor_other _ id dstId _ hi]
                simp [setActor, hi, chargeSender, bumpToken, proceed_life]
          · refine ⟨?_, ?_⟩
            · rw [setActor_other _ id s _ hs, setActor_other _ dstId s _ hc, setActor_other _ id s _ hs]
            · rw [setActor_other _ id s _ hs, setActor_other _ dstId s _ hc, setActor_other _ id s _ hs]
        · refine ⟨?_, ?_⟩ <;> simp [setActor_other, hs, proceed_life]
    | call dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => refine ⟨?_, ?_⟩ <;> simp [hr, setActor_other, hs, proceed_life]
      | some dstId =>
        refine ⟨enqueue_phase_other w I.desc id dstId _ true _ s hs,
          enqueue_life w I.desc id dstId _ true _ s⟩
    | reply =>
      simpa [execRun, hk] using reply_keeps_quiet w id s k hnreply hs
    | selfSchedule label =>
      simp [execRun, hk]
      split
      · refine ⟨?_, ?_⟩ <;> simp [setActor_other, hs, proceed_life]
      · split
        · refine ⟨?_, ?_⟩ <;> simp [setActor_other, hs, proceed_life]
        · refine ⟨?_, ?_⟩ <;> simp [setActor_other, hs]
    | cell dst label value =>
      simp only [execRun, hk]
      split
      · refine ⟨?_, ?_⟩ <;> simp [setCell, setActor_other, hs, proceed_life]
      · rw [wakeReaders]
        refine ⟨?_, ?_⟩
        · rw [wakes_phase _ _ _ dst label id s]
          simp [setCell, setActor_other, hs, proceed_life]
        · rw [wakes_life _ _ _ dst label id s]
          simp [setCell, setActor_other, hs, proceed_life]
    | internal => refine ⟨?_, ?_⟩ <;> simp [execRun, hk, setActor_other, hs]
    | peer => refine ⟨?_, ?_⟩ <;> simp [execRun, hk, setActor_other, hs]
    | terminate =>
      simp [execRun, hk]
      split
      · rename_i t ht
        by_cases hkill : t.terminable = true ∧ hasParkedCall a.parked = false
        · rw [if_pos hkill]
          let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) a.box) (tname id) a.parked
          have hbase : (base.st s).phase = (w.st s).phase ∧ (base.st s).life = (w.st s).life := by
            refine ⟨?_, ?_⟩
            · simp [base, phase_refundP, phase_refund, readCells_st]
            · have hread : (readCells I.desc w id).st s = w.st s := readCells_st _ _ _ _
              have href := (refund_life (readCells I.desc w id) (tname id) a.box s).1
              have hrefp :=
                (refundP_life (refundMsgs (readCells I.desc w id) (tname id) a.box) (tname id) a.parked s).1
              simp [base, hread, href, hrefp]
          let dead : Actor := { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
          have hdead : ((setActor base id dead).st s).phase = (w.st s).phase ∧
              ((setActor base id dead).st s).life = (w.st s).life := by
            refine ⟨?_, ?_⟩
            · simp [setActor, hs, hbase.1]
            · simp [setActor, hs, hbase.2]
          have hn' : ∀ d c ck, ((setActor base id dead).st s).phase ≠ .parked d c ck := by
            intro d c ck hbad
            exact hnpark d c ck (hdead.1 ▸ hbad)
          have hrel := release_keeps_nonparked (setActor base id dead) id a.parked s hn'
          exact ⟨hrel.1.trans hdead.1, hrel.2.trans hdead.2⟩
        · rw [if_neg hkill]
          exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

/-- A receive does not rewrite `s` when `s` is not the receiver and not parked. -/
theorem bulk_keeps_quiet (I : Impl) (w : World) (id : InstId) (w' : World) (s : InstId)
    (hne : s ≠ id) (hnpark : ∀ d c k, (w.st s).phase ≠ .parked d c k)
    (h : receiveBulk I w id = some w') :
    (w'.st s).phase = (w.st s).phase ∧ (w'.st s).life = (w.st s).life := by
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
          by_cases hs : s = p.sender
          · have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase ∧
                ((setActor w1 id a1).st s).life = (w.st s).life := by
              refine ⟨?_, ?_⟩ <;> simp [setActor, hne, hst]
            have hcred := credit_life (setActor w1 id a1) (tname id) p.msg.sender s
            have hph0 : ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st s).phase =
                (w.st s).phase := hcred.2.2.1.trans hset.1
            have hid := resume_id_of_not_parked
              ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender) p.isCall id
              (by
                intro d c k hbad
                exact hnpark d c k (hph0.symm.trans (by simpa [hs] using hbad)))
            refine ⟨?_, ?_⟩
            · rw [hid]
              simpa [setActor, hs] using hph0
            · rw [hid]
              simpa [setActor, hs] using hcred.1.trans hset.2
          · have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase ∧
                ((setActor w1 id a1).st s).life = (w.st s).life := by
              refine ⟨?_, ?_⟩ <;> simp [setActor, hne, hst]
            have hcred := credit_life (setActor w1 id a1) (tname id) p.msg.sender s
            refine ⟨?_, ?_⟩
            · simpa [setActor, hs] using hcred.2.2.1.trans hset.1
            · simpa [setActor, hs] using hcred.1.trans hset.2
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          have hcred := credit_life (setActor w1 id a1) (tname id) m.sender s
          refine ⟨?_, ?_⟩
          · simpa [setActor, hne, hst] using hcred.2.2.1
          · simpa [setActor, hne, hst] using hcred.1
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          by_cases hs : s = p.sender
          · have hset : ((setActor w1 id admitted).st s).phase = (w.st s).phase ∧
                ((setActor w1 id admitted).st s).life = (w.st s).life := by
              refine ⟨?_, ?_⟩ <;> simp [admitted, setActor, hne, hst]
            have hcred := credit_life (setActor w1 id admitted) (tname id) m.sender s
            have hph0 : ((creditSender (setActor w1 id admitted) (tname id) m.sender).st s).phase =
                (w.st s).phase := hcred.2.2.1.trans hset.1
            have hid := resume_id_of_not_parked
              ((creditSender (setActor w1 id admitted) (tname id) m.sender).st p.sender) p.isCall id
              (by
                intro d c k hbad
                exact hnpark d c k (hph0.symm.trans (by simpa [hs] using hbad)))
            refine ⟨?_, ?_⟩
            · rw [hid]
              simpa [setActor, hs] using hph0
            · rw [hid]
              simpa [setActor, hs] using hcred.1.trans hset.2
          · have hset : ((setActor w1 id admitted).st s).phase = (w.st s).phase ∧
                ((setActor w1 id admitted).st s).life = (w.st s).life := by
              refine ⟨?_, ?_⟩ <;> simp [admitted, setActor, hne, hst]
            have hcred := credit_life (setActor w1 id admitted) (tname id) m.sender s
            refine ⟨?_, ?_⟩
            · simpa [setActor, hs] using hcred.2.2.1.trans hset.1
            · simpa [setActor, hs] using hcred.1.trans hset.2

/-- A step other than this actor's own `finish` leaves an effect or peer wait untouched. -/
theorem step_keeps_quiet (I : Impl) (a : Action) (w w' : World) (hO : OccInv I w) (s : InstId)
    (hnpark : ∀ d c k, (w.st s).phase ≠ .parked d c k)
    (hnreply : ∀ d ck, (w.st s).phase ≠ .awaitReply d ck)
    (hnidle : (w.st s).phase ≠ .idle) (hnrun : ∀ k, (w.st s).phase ≠ .run k)
    (hl : (w.st s).life = .alive) (h : apply I a w = some w') (hnot : a ≠ .finish s) :
    (w'.st s).phase = (w.st s).phase ∧ (w'.st s).life = (w.st s).life := by
  cases a with
  | exec id =>
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [← hs] at hhead
      simp [apply, execHead, hl, hnrun] at hhead
    simp [apply] at h
    unfold execHead at h
    by_cases hlive : (w.st id).life = .alive
    · simp [hlive] at h
      cases hph : (w.st id).phase with
      | run k0 =>
        simp [hph] at h
        cases h
        exact exec_keeps_quiet I w id (w.st id) k0 s hne hnpark hnreply
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlive] at h
  | finish id =>
    have hne : s ≠ id := by
      intro hs
      apply hnot
      simp [hs]
    simp [apply, finishWait] at h
    split at h
    · cases h
      refine ⟨?_, ?_⟩ <;> simp [setActor, hne, proceed_life]
    · cases h
      refine ⟨?_, ?_⟩ <;> simp [setActor, hne, proceed_life]
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
        refine ⟨?_, ?_⟩ <;> simp [readCells_st, setActor, hfresh, withTokens]
      · cases h
  | recvPrio id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [← hs] at hhead
      simp [receivePrio] at hhead
      cases hprio : (w.st s).prio with
      | nil => simp [hprio] at hhead
      | cons m ms =>
        simp [hprio, hl] at hhead
        by_cases hph : (w.st s).phase = .idle
        · exact hnidle hph
        · simp [hph] at hhead
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
        refine ⟨?_, ?_⟩ <;> simp [setActor, hne, hst]
  | recvBulk id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [← hs] at hhead
      simp [receiveBulk, hl] at hhead
      by_cases hph : (w.st s).phase = .idle
      · exact hnidle hph
      · simp [hph] at hhead
    exact bulk_keeps_quiet I w id w' s hne hnpark h

/-- Until this actor's own `finish`, an effect or peer wait keeps its phase and stays alive. -/
theorem quiet_prefix {I : Impl} (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s : InstId) (i n : Nat) (ph : Phase)
    (hp : ((ρ.cfg i).st s).phase = ph)
    (hnpark : ∀ d c k, ph ≠ .parked d c k) (hnreply : ∀ d ck, ph ≠ .awaitReply d ck)
    (hnidle : ph ≠ .idle) (hnrun : ∀ k, ph ≠ .run k)
    (hl : ((ρ.cfg i).st s).life = .alive)
    (hnot : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .finish s) :
    ((ρ.cfg (i + n)).st s).phase = ph ∧ ((ρ.cfg (i + n)).st s).life = .alive := by
  induction n with
  | zero =>
    simpa using And.intro hp hl
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hnot t h1 (Nat.lt_trans h2 (Nat.lt_succ_self _)))
    have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.2.1
    have hstep := step_keeps_quiet I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) hO s
      (fun d c k hbad => hnpark d c k (by simpa [hprev.1] using hbad))
      (fun d ck hbad => hnreply d ck (by simpa [hprev.1] using hbad))
      (by simpa [hprev.1] using hnidle)
      (fun k hbad => hnrun k (by simpa [hprev.1] using hbad))
      hprev.2 (ρ.valid (i + n))
      (hnot (i + n) (Nat.le_add_right i n) (Nat.lt_succ_self _))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      And.intro (hstep.1.trans hprev.1) (hstep.2.trans hprev.2)

def scanAct (act : Nat → Action) (target : Action) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if act k = target then k else scanAct act target fuel (k + 1)

theorem scanAct_spec (act : Nat → Action) (target : Action) (fuel k : Nat)
    (h : ∃ d, d ≤ fuel ∧ act (k + d) = target) :
    k ≤ scanAct act target fuel k ∧ act (scanAct act target fuel k) = target ∧
      ∀ t, k ≤ t → t < scanAct act target fuel k → act t ≠ target := by
  induction fuel generalizing k with
  | zero =>
    obtain ⟨d, hd, hact⟩ := h
    have hd0 : d = 0 := by omega
    simp [scanAct]
    constructor
    · simpa [hd0] using hact
    · intro t h1 h2
      omega
  | succ fuel ih =>
    simp [scanAct]
    by_cases hhere : act k = target
    · simp [hhere]
      intro t h1 h2
      omega
    · simp [hhere]
      obtain ⟨d, hd, hact⟩ := h
      have hnext : ∃ d, d ≤ fuel ∧ act (k + 1 + d) = target := by
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

theorem proceed_fuel (a : Actor) (k : Cont) :
    phaseFuel (proceed a k).phase ≤ 2 * k.rest.length := by
  cases hk : k.rest <;> simp [proceed, phaseFuel, hk]

theorem await_effect_fuel (k : Cont) : phaseFuel (.awaitEffect k) = 2 * k.rest.length + 1 := by
  simp [phaseFuel]

theorem await_peer_fuel (k : Cont) : phaseFuel (.awaitPeer k) = 2 * k.rest.length + 1 := by
  simp [phaseFuel]

/-- Fairness takes the `finish` of an `awaitEffect`. The actor comes back on the tail, still alive. -/
theorem effect_resumes (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (hF : Fair ρ) (s : InstId) (i : Nat) (k : Cont)
    (hp : ((ρ.cfg i).st s).phase = .awaitEffect k) (hl : ((ρ.cfg i).st s).life = .alive) :
    ∃ j, i ≤ j ∧ ((ρ.cfg (j + 1)).st s).phase = (proceed ((ρ.cfg j).st s) k).phase ∧
      ((ρ.cfg (j + 1)).st s).life = .alive := by
  have hhit : ∃ j, i ≤ j ∧ ρ.act j = .finish s := by
    cases Classical.em (∃ j, i ≤ j ∧ ρ.act j = .finish s) with
    | inl h => exact h
    | inr hmiss =>
      have hstay : ∀ n, ((ρ.cfg (i + n)).st s).phase = .awaitEffect k ∧
          ((ρ.cfg (i + n)).st s).life = .alive := by
        intro n
        exact quiet_prefix hL hG ρ s i n (.awaitEffect k) hp
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (by intro h; cases h)
          (fun _ h => by cases h) hl
          (fun t h1 _ hbad => hmiss ⟨t, h1, hbad⟩)
      have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
        intro j hj
        have hst := hstay (j - i)
        have hph : ((ρ.cfg j).st s).phase = .awaitEffect k := by
          simpa [Nat.add_sub_of_le hj] using hst.1
        exact enabled_finish_effect I (ρ.cfg j) s (by simp [waitKind, hph])
      obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
      exact absurd ⟨j, hj, hact⟩ hmiss
  obtain ⟨j0, hj0, hact0⟩ := hhit
  have hscan := scanAct_spec ρ.act (.finish s) (j0 - i) i ⟨j0 - i, Nat.le_refl _, by
    simpa [Nat.add_sub_of_le hj0] using hact0⟩
  let m := scanAct ρ.act (.finish s) (j0 - i) i
  have him : i ≤ m := hscan.1
  have hact : ρ.act m = .finish s := hscan.2.1
  have hpre := quiet_prefix hL hG ρ s i (m - i) (.awaitEffect k) hp
    (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (by intro h; cases h)
    (fun _ h => by cases h) hl
    (fun t h1 h2 hbad => hscan.2.2 t h1 (by
      have hsum : i + (m - i) = m := Nat.add_sub_of_le him
      omega) hbad)
  have hph : ((ρ.cfg m).st s).phase = .awaitEffect k := by
    simpa [Nat.add_sub_of_le him] using hpre.1
  have hl' : ((ρ.cfg m).st s).life = .alive := by
    simpa [Nat.add_sub_of_le him] using hpre.2
  have happ := ρ.valid m
  simp [apply, hact, finishWait, hph] at happ
  refine ⟨m, him, ?_, ?_⟩
  · rw [← happ]
    simp [setActor]
  · rw [← happ]
    simpa [setActor, proceed_life] using hl'

/-- Fairness takes the `finish` of an `awaitPeer`. The actor comes back on the tail, still alive. -/
theorem peer_resumes (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (hF : Fair ρ) (s : InstId) (i : Nat) (k : Cont)
    (hp : ((ρ.cfg i).st s).phase = .awaitPeer k) (hl : ((ρ.cfg i).st s).life = .alive) :
    ∃ j, i ≤ j ∧ ((ρ.cfg (j + 1)).st s).phase = (proceed ((ρ.cfg j).st s) k).phase ∧
      ((ρ.cfg (j + 1)).st s).life = .alive := by
  have hhit : ∃ j, i ≤ j ∧ ρ.act j = .finish s := by
    cases Classical.em (∃ j, i ≤ j ∧ ρ.act j = .finish s) with
    | inl h => exact h
    | inr hmiss =>
      have hstay : ∀ n, ((ρ.cfg (i + n)).st s).phase = .awaitPeer k ∧
          ((ρ.cfg (i + n)).st s).life = .alive := by
        intro n
        exact quiet_prefix hL hG ρ s i n (.awaitPeer k) hp
          (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (by intro h; cases h)
          (fun _ h => by cases h) hl
          (fun t h1 _ hbad => hmiss ⟨t, h1, hbad⟩)
      have hen : ∀ j, i ≤ j → Enabled I (ρ.cfg j) (.finish s) := by
        intro j hj
        have hst := hstay (j - i)
        have hph : ((ρ.cfg j).st s).phase = .awaitPeer k := by
          simpa [Nat.add_sub_of_le hj] using hst.1
        exact enabled_finish_peer I (ρ.cfg j) s (by simp [waitKind, hph])
      obtain ⟨j, hj, hact⟩ := hF.weak (.finish s) i rfl hen
      exact absurd ⟨j, hj, hact⟩ hmiss
  obtain ⟨j0, hj0, hact0⟩ := hhit
  have hscan := scanAct_spec ρ.act (.finish s) (j0 - i) i ⟨j0 - i, Nat.le_refl _, by
    simpa [Nat.add_sub_of_le hj0] using hact0⟩
  let m := scanAct ρ.act (.finish s) (j0 - i) i
  have him : i ≤ m := hscan.1
  have hact : ρ.act m = .finish s := hscan.2.1
  have hpre := quiet_prefix hL hG ρ s i (m - i) (.awaitPeer k) hp
    (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (by intro h; cases h)
    (fun _ h => by cases h) hl
    (fun t h1 h2 hbad => hscan.2.2 t h1 (by
      have hsum : i + (m - i) = m := Nat.add_sub_of_le him
      omega) hbad)
  have hph : ((ρ.cfg m).st s).phase = .awaitPeer k := by
    simpa [Nat.add_sub_of_le him] using hpre.1
  have hl' : ((ρ.cfg m).st s).life = .alive := by
    simpa [Nat.add_sub_of_le him] using hpre.2
  have happ := ρ.valid m
  simp [apply, hact, finishWait, hph] at happ
  refine ⟨m, him, ?_, ?_⟩
  · rw [← happ]
    simp [setActor]
  · rw [← happ]
    simpa [setActor, proceed_life] using hl'

/-- Idle, crashed, or blocked on a partner. An effect or peer wait is not one of these. -/
def Quiescent (w : World) (s : InstId) : Prop :=
  (w.st s).life ≠ .alive ∨ (w.st s).phase = .idle ∨ (w.st s).phase = .crashed ∨
    (∃ dst c k, (w.st s).phase = .parked dst c k) ∨
    (∃ dst k, (w.st s).phase = .awaitReply dst k)

theorem carried_fuel (ph : Phase) (es : List Eff)
    (h : ph = .idle ∨ ph = .crashed ∨ carried ph = some es) : phaseFuel ph ≤ 2 * es.length + 1 := by
  rcases h with h | h | h
  · simp [phaseFuel, h]
  · simp [phaseFuel, h]
  · cases ph with
    | idle => simp [carried] at h
    | crashed => simp [carried] at h
    | run k =>
      simp [carried, phaseFuel] at h ⊢
      simp [h]
    | parked _ _ k =>
      simp [carried, phaseFuel] at h ⊢
      simp [h]
    | awaitReply _ k =>
      simp [carried, phaseFuel] at h ⊢
      simp [h]
    | awaitEffect k =>
      simp [carried, phaseFuel] at h ⊢
      simp [h]
    | awaitPeer k =>
      simp [carried, phaseFuel] at h ⊢
      simp [h]

theorem proceed_after_fuel (a : Actor) (k : Cont) (e : Eff) (tail : List Eff)
    (hrest : k.rest = e :: tail) :
    phaseFuel (proceed a (afterHead k)).phase < 2 * (e :: tail).length := by
  cases htail : tail <;> simp [proceed, afterHead, phaseFuel, hrest, htail]

/-- One step of a nonempty program strictly lowers `phaseFuel`, including a crash or a killing terminate. -/
theorem exec_drops (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id : InstId) (k : Cont)
    (hph : (w.st id).phase = .run k) (hl : (w.st id).life = .alive) (hne : k.rest ≠ []) :
    phaseFuel ((execRun I w id (w.st id) k).st id).phase < phaseFuel ((w.st id).phase) := by
  have hT := term_ok_reachable I hL N w hR
  cases hrest : k.rest with
  | nil => exact absurd hrest hne
  | cons e tail =>
    have hlen : phaseFuel ((w.st id).phase) = 2 * (e :: tail).length := by
      simp [phaseFuel, hph, hrest]
    rw [hlen]
    cases e with
    | terminate =>
      have hk : { k with rest := .terminate :: tail } = k := by
        rw [← hrest]
      have hph' : (w.st id).phase = .run { k with rest := .terminate :: tail } := by
        simpa [hk] using hph
      have hidle := (terminate_commits I hL hG N w hR hT id k tail hph' hl).2
      rw [← hk]
      simp [phaseFuel, hidle]
    | internal =>
      simp [execRun, hrest, setActor, phaseFuel, afterHead]
      omega
    | peer =>
      simp [execRun, hrest, setActor, phaseFuel, afterHead]
      omega
    | selfSchedule label =>
      simp [execRun, hrest]
      split
      · cases htail : tail with
        | nil => simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
        | cons _ _ =>
          simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
      · split
        · cases htail : tail with
          | nil => simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
          | cons _ _ =>
            simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
        · simp [setActor, phaseFuel]
    | cell dst label value =>
      simp only [execRun, hrest]
      split
      · cases htail : tail with
        | nil => simp [setCell, setActor, proceed, afterHead, phaseFuel, hrest, htail]
        | cons _ _ =>
          simp [setCell, setActor, proceed, afterHead, phaseFuel, hrest, htail]
      · rw [wakeReaders, wakes_phase _ _ _ dst label id id]
        cases htail : tail with
        | nil => simp [setCell, setActor, proceed, afterHead, phaseFuel, hrest, htail]
        | cons _ _ =>
          simp [setCell, setActor, proceed, afterHead, phaseFuel, hrest, htail]
    | trySend dst label hint =>
      simp [execRun, hrest]
      cases hr : route w I.desc dst hint with
      | none =>
        simp [hr, setActor]
        exact proceed_after_fuel (w.st id) k (.trySend dst label hint) tail hrest
      | some dstId =>
        simp [hr]
        split
        · by_cases hdst : dstId = id
          · cases htail : tail with
            | nil => simp [hdst, setActor, proceed, afterHead, phaseFuel, hrest, htail]
            | cons _ _ => simp [hdst, setActor, proceed, afterHead, phaseFuel, hrest, htail]
          · cases htail : tail with
            | nil => simp [hdst, setActor, proceed, afterHead, phaseFuel, hrest, htail]
            | cons _ _ => simp [hdst, setActor, proceed, afterHead, phaseFuel, hrest, htail]
        · cases htail : tail with
          | nil => simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
          | cons _ _ => simp [setActor, proceed, afterHead, phaseFuel, hrest, htail]
    | reply =>
      simp [execRun, hrest]
      have hdis : ((performReply w id k).st id).phase = .idle ∨
          ((performReply w id k).st id).phase = .crashed ∨
          carried ((performReply w id k).st id).phase = some tail := by
        cases hnow : ((performReply w id k).st id).phase with
        | idle => exact Or.inl rfl
        | crashed => exact Or.inr (Or.inl rfl)
        | run k' =>
          exact Or.inr (Or.inr (by
            have heq := reply_sender_rest w id k k'.rest (by simp [carried, hnow])
            simp [carried, hnow, heq, afterHead, hrest]))
        | parked _ _ k' =>
          exact Or.inr (Or.inr (by
            have heq := reply_sender_rest w id k k'.rest (by simp [carried, hnow])
            simp [carried, hnow, heq, afterHead, hrest]))
        | awaitReply _ k' =>
          exact Or.inr (Or.inr (by
            have heq := reply_sender_rest w id k k'.rest (by simp [carried, hnow])
            simp [carried, hnow, heq, afterHead, hrest]))
        | awaitEffect k' =>
          exact Or.inr (Or.inr (by
            have heq := reply_sender_rest w id k k'.rest (by simp [carried, hnow])
            simp [carried, hnow, heq, afterHead, hrest]))
        | awaitPeer k' =>
          exact Or.inr (Or.inr (by
            have heq := reply_sender_rest w id k k'.rest (by simp [carried, hnow])
            simp [carried, hnow, heq, afterHead, hrest]))
      have hbound := carried_fuel ((performReply w id k).st id).phase tail hdis
      omega
    | send dst label hint =>
      simp [execRun, hrest]
      cases hr : route w I.desc dst hint with
      | none =>
        simp [hr, setActor]
        exact proceed_after_fuel (w.st id) k (.send dst label hint) tail hrest
      | some dstId =>
        simp [hr]
        let w' := enqueueOrPark w I.desc id dstId ⟨label, id, none⟩ false (afterHead k)
        have hbound : phaseFuel (w'.st id).phase ≤ 2 * tail.length + 1 := by
          cases hnow : (w'.st id).phase with
          | idle => simp [phaseFuel, hnow]
          | crashed => simp [phaseFuel, hnow]
          | run k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | parked _ _ k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitReply _ k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitEffect k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitPeer k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
        simp [w'] at hbound
        omega
    | call dst label hint =>
      simp [execRun, hrest]
      cases hr : route w I.desc dst hint with
      | none =>
        simp [hr, setActor]
        exact proceed_after_fuel (w.st id) k (.call dst label hint) tail hrest
      | some dstId =>
        simp [hr]
        let w' := enqueueOrPark w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k)
        have hbound : phaseFuel (w'.st id).phase ≤ 2 * tail.length + 1 := by
          cases hnow : (w'.st id).phase with
          | idle => simp [phaseFuel, hnow]
          | crashed => simp [phaseFuel, hnow]
          | run k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | parked _ _ k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitReply _ k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitEffect k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
          | awaitPeer k' =>
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true (afterHead k) k'.rest
              (by simp [w', carried, hnow])
            simp [phaseFuel, hnow, heq, afterHead, hrest]
        simp [w'] at hbound
        omega

/-- A step other than this actor's own `exec` keeps a running actor alive. -/
theorem step_run_alive (I : Impl) (a : Action) (w w' : World) (hO : OccInv I w) (s : InstId)
    (k : Cont) (hp : (w.st s).phase = .run k) (hl : (w.st s).life = .alive)
    (h : apply I a w = some w') (hnot : a ≠ .exec s) : (w'.st s).life = .alive := by
  cases a with
  | exec id =>
    have hne : s ≠ id := by
      intro hs
      exact hnot (by simp [hs])
    simp [apply] at h
    unfold execHead at h
    by_cases hlive : (w.st id).life = .alive
    · simp [hlive] at h
      cases hph : (w.st id).phase with
      | run k0 =>
        simp [hph] at h
        cases h
        exact ((exec_keeps_quiet I w id (w.st id) k0 s hne
          (fun _ _ _ hbad => by simp [hp] at hbad)
          (fun _ _ hbad => by simp [hp] at hbad)).2).trans hl
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlive] at h
  | finish id =>
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [hs] at hp
      simp [apply, finishWait, hp] at hhead
    simp [apply, finishWait] at h
    split at h
    · cases h
      simp [setActor, hne, proceed_life, hl]
    · cases h
      simp [setActor, hne, proceed_life, hl]
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
        simp [readCells_st, setActor, hfresh, withTokens, hl]
      · cases h
  | recvPrio id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [← hs] at hhead
      simp [receivePrio] at hhead
      cases hprio : (w.st s).prio with
      | nil => simp [hprio] at hhead
      | cons _ _ => simp [hprio, hp] at hhead
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
        simp [setActor, hne, hst, hl]
  | recvBulk id =>
    simp [apply] at h
    have hne : s ≠ id := by
      intro hs
      have hhead := h
      rw [← hs] at hhead
      simp [receiveBulk, hp] at hhead
    exact ((bulk_keeps_quiet I w id w' s hne
      (fun _ _ _ hbad => by simp [hp] at hbad) h).2).trans hl

theorem run_holds {I : Impl} (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s : InstId) (i n : Nat) (k : Cont)
    (hp : ((ρ.cfg i).st s).phase = .run k) (hl : ((ρ.cfg i).st s).life = .alive)
    (hnot : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .exec s) :
    ((ρ.cfg (i + n)).st s).phase = .run k ∧ ((ρ.cfg (i + n)).st s).life = .alive := by
  induction n with
  | zero => simpa using And.intro hp hl
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hnot t h1 (Nat.lt_trans h2 (Nat.lt_succ_self _)))
    have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.2.1
    have hact := hnot (i + n) (Nat.le_add_right i n) (Nat.lt_succ_self _)
    have hlife := step_run_alive I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) hO s k
      hprev.1 hprev.2 (ρ.valid (i + n)) hact
    have hphase := step_keeps_run I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) hO s k
      hprev.1 hprev.2 (ρ.valid (i + n)) hact
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hphase hlife

/-- A live actor reaches idle, dies, crashes, or blocks on a send or a call.
Effect and peer waits are taken by `finish`, and a running program gets shorter at every `exec`. -/
theorem reaches_block (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (hF : Fair ρ) (s : InstId) :
    ∀ i, ((ρ.cfg i).st s).life = .alive → ∃ j, i ≤ j ∧ Quiescent (ρ.cfg j) s := by
  suffices ∀ n i, phaseFuel (((ρ.cfg i).st s).phase) ≤ n → ((ρ.cfg i).st s).life = .alive →
      ∃ j, i ≤ j ∧ Quiescent (ρ.cfg j) s by
    intro i hl
    exact this _ i (Nat.le_refl _) hl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hfuel hl
    cases hph : ((ρ.cfg i).st s).phase with
    | idle => exact ⟨i, Nat.le_refl _, Or.inr (Or.inl hph)⟩
    | crashed => exact ⟨i, Nat.le_refl _, Or.inr (Or.inr (Or.inl hph))⟩
    | parked dst c k =>
      exact ⟨i, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl ⟨dst, c, k, hph⟩)))⟩
    | awaitReply dst k =>
      exact ⟨i, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inr ⟨dst, k, hph⟩)))⟩
    | awaitEffect k =>
      obtain ⟨j, hj, hproc, hlj⟩ := effect_resumes I hL hG ρ hF s i k hph hl
      have hlt : phaseFuel (((ρ.cfg (j + 1)).st s).phase) < n := by
        have hnew := proceed_fuel ((ρ.cfg j).st s) k
        rw [← hproc] at hnew
        have hold : phaseFuel (((ρ.cfg i).st s).phase) = 2 * k.rest.length + 1 := by
          simp [phaseFuel, hph]
        omega
      obtain ⟨j2, hj2, hq⟩ := ih _ hlt (j + 1) (Nat.le_refl _) hlj
      exact ⟨j2, Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) hj2), hq⟩
    | awaitPeer k =>
      obtain ⟨j, hj, hproc, hlj⟩ := peer_resumes I hL hG ρ hF s i k hph hl
      have hlt : phaseFuel (((ρ.cfg (j + 1)).st s).phase) < n := by
        have hnew := proceed_fuel ((ρ.cfg j).st s) k
        rw [← hproc] at hnew
        have hold : phaseFuel (((ρ.cfg i).st s).phase) = 2 * k.rest.length + 1 := by
          simp [phaseFuel, hph]
        omega
      obtain ⟨j2, hj2, hq⟩ := ih _ hlt (j + 1) (Nat.le_refl _) hlj
      exact ⟨j2, Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) hj2), hq⟩
    | run k =>
      have hhit : ∃ j, i ≤ j ∧ ρ.act j = .exec s := by
        cases Classical.em (∃ j, i ≤ j ∧ ρ.act j = .exec s) with
        | inl h => exact h
        | inr hmiss =>
          have hstay : ∀ t, i ≤ t → ((ρ.cfg t).st s).phase = .run k ∧
              ((ρ.cfg t).st s).life = .alive := by
            intro t ht
            have hgot := run_holds hL hG ρ s i (t - i) k hph hl
              (fun u h1 h2 hbad => hmiss ⟨u, h1, hbad⟩)
            simpa [Nat.add_sub_of_le ht] using hgot
          exact False.elim (not_forever_run I hL hG ρ hF s i (fun j hj => (hstay j hj).2)
            (fun j hj => ⟨k, (hstay j hj).1⟩))
      obtain ⟨j0, hj0, hact0⟩ := hhit
      have hscan := scanExec_spec ρ.act s (j0 - i) i ⟨j0 - i, Nat.le_refl _, by
        simpa [Nat.add_sub_of_le hj0] using hact0⟩
      let m := scanExec ρ.act s (j0 - i) i
      have him : i ≤ m := hscan.1
      have hact : ρ.act m = .exec s := hscan.2.1
      have hpre := run_holds hL hG ρ s i (m - i) k hph hl
        (fun t h1 h2 hbad => hscan.2.2 t h1 (by
          have hsum : i + (m - i) = m := Nat.add_sub_of_le him
          omega) hbad)
      have hhere : ((ρ.cfg m).st s).phase = .run k := by
        simpa [Nat.add_sub_of_le him] using hpre.1
      have hl' : ((ρ.cfg m).st s).life = .alive := by
        simpa [Nat.add_sub_of_le him] using hpre.2
      have hrun : execRun I (ρ.cfg m) s ((ρ.cfg m).st s) k = ρ.cfg (m + 1) := by
        have hhead := ρ.valid m
        simp [apply, hact, execHead, hl', hhere] at hhead
        exact hhead
      by_cases hempty : k.rest = []
      · have hidle : ((ρ.cfg (m + 1)).st s).phase = .idle := by
          rw [← hrun]
          simp [execRun, hempty, setActor]
        exact ⟨m + 1, Nat.le_trans him (Nat.le_succ _), Or.inr (Or.inl hidle)⟩
      · have hdrop := exec_drops I hL hG N (ρ.cfg m) (cfg_reachable ρ m) s k hhere hl' hempty
        rw [hrun] at hdrop
        have hlt : phaseFuel (((ρ.cfg (m + 1)).st s).phase) < n := by
          have hold : phaseFuel (((ρ.cfg m).st s).phase) ≤ n := by
            simpa [hhere, hph] using hfuel
          omega
        by_cases hlive : ((ρ.cfg (m + 1)).st s).life = .alive
        · obtain ⟨j2, hj2, hq⟩ := ih _ hlt (m + 1) (Nat.le_refl _) hlive
          exact ⟨j2, Nat.le_trans (Nat.le_trans him (Nat.le_succ m)) hj2, hq⟩
        · exact ⟨m + 1, Nat.le_trans him (Nat.le_succ _), Or.inl hlive⟩

theorem erase_succ_length {α} [DecidableEq α] (ys : List α) (x : α) (hx : x ∈ ys) :
    (ys.erase x).length + 1 = ys.length := by
  induction ys with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : y == x
    · simp [List.erase, hxy]
    · have hx' : x ∈ ys := by
        cases hx with
        | head =>
          have : (x == x) = true := by rw [beq_iff_eq]
          exact absurd this hxy
        | tail _ ht => exact ht
      simp [List.erase, hxy]
      have ih' := ih hx'
      omega

theorem nodup_mem_length {α} [DecidableEq α] (xs ys : List α)
    (hnd : xs.Nodup) (h : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have hx : x ∈ ys := h x (List.Mem.head _)
    have hpair := List.nodup_cons.mp hnd
    have hsub : ∀ y ∈ xs, y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by
        intro heq
        exact hpair.1 (heq ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (h y (List.Mem.tail _ hy))
    have ih' : xs.length ≤ (ys.erase x).length := ih (ys.erase x) hpair.2 hsub
    have hlen : (ys.erase x).length + 1 = ys.length := erase_succ_length ys x hx
    have hgoal : xs.length + 1 ≤ ys.length := by omega
    simpa [List.length_cons] using hgoal

/-- A lane of distinct labels drawn from a set no bigger than the capacity cannot
overflow by taking one more label from that set. -/
theorem prio_no_crash (cap : Nat) (labels prio : List String) (label : String)
    (hsub : ∀ x ∈ prio, x ∈ labels) (hnd : prio.Nodup) (hlen : labels.length ≤ cap)
    (hfull : cap ≤ prio.length) (hfresh : label ∉ prio) (hmem : label ∈ labels) : False := by
  have hsub' : ∀ x ∈ prio, x ∈ labels.erase label := by
    intro x hx
    have hne : x ≠ label := by
      intro heq
      exact hfresh (by simpa [heq] using hx)
    exact (List.mem_erase_of_ne hne).mpr (hsub x hx)
  have hshort := nodup_mem_length prio (labels.erase label) hnd hsub'
  have herase := erase_succ_length labels label hmem
  have hle := nodup_mem_length prio labels hnd hsub
  omega

def laneLabels (ms : List Msg) : List String := ms.map (·.label)

theorem selfLabels_append (pre es : List Eff) :
    selfLabels (pre ++ es) = selfLabels pre ++ selfLabels es := by
  induction pre with
  | nil => simp [selfLabels]
  | cons e pre ih =>
    cases e <;> simp [selfLabels, ih]

theorem cellWake_append (reader : String) (pre es : List Eff) :
    cellWakeLabels reader (pre ++ es) = cellWakeLabels reader pre ++ cellWakeLabels reader es := by
  induction pre with
  | nil => simp [cellWakeLabels]
  | cons e pre ih =>
    cases e <;> simp [cellWakeLabels, ih]

theorem self_in_collected (trs : List Transition) (template : String) (tr : Transition)
    (hm : tr ∈ trs) (ht : tr.template = template) (l : String) (hl : l ∈ selfLabels tr.program) :
    l ∈ (trs.filterMap fun t =>
      if t.template == template then some (selfLabels t.program) else none).flatten := by
  induction trs with
  | nil => cases hm
  | cons t ts ih =>
    cases hm with
    | head =>
      simp [List.filterMap, List.flatten, ht, hl, List.mem_append]
    | tail _ ht' =>
      have ih' := ih ht'
      by_cases hif : t.template == template
      · simp [List.filterMap, List.flatten, hif, List.mem_append] at ih' ⊢
        exact Or.inr ih'
      · simp [List.filterMap, List.flatten, hif] at ih' ⊢
        exact ih'

theorem cell_in_collected (trs : List Transition) (reader : String) (tr : Transition)
    (hm : tr ∈ trs) (l : String) (hl : l ∈ cellWakeLabels reader tr.program) :
    l ∈ (trs.map fun t => cellWakeLabels reader t.program).flatten := by
  induction trs with
  | nil => cases hm
  | cons t ts ih =>
    cases hm with
    | head =>
      simp [List.flatten, hl, List.mem_append]
    | tail _ ht' =>
      have ih' := ih ht'
      simp [List.flatten, List.mem_append] at ih' ⊢
      exact Or.inr ih'

theorem self_in_prio (I : Impl) (tr : Transition) (hm : tr ∈ I.transitions) (l : String)
    (hl : l ∈ selfLabels tr.program) : l ∈ prioLabels I tr.template := by
  have hcol := self_in_collected I.transitions tr.template tr hm rfl l hl
  have hmem : l ∈
      (I.transitions.filterMap fun t =>
        if t.template == tr.template then some (selfLabels t.program) else none).flatten ++
      cellLabels I.desc tr.template ++
      (I.transitions.map fun t => cellWakeLabels tr.template t.program).flatten := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hcol)))
  simpa [prioLabels] using mem_dedup _ l hmem

theorem cell_in_prio (I : Impl) (reader : String) (tr : Transition) (hm : tr ∈ I.transitions)
    (l : String) (hl : l ∈ cellWakeLabels reader tr.program) : l ∈ prioLabels I reader := by
  have hcol := cell_in_collected I.transitions reader tr hm l hl
  have hmem : l ∈
      (I.transitions.filterMap fun t =>
        if t.template == reader then some (selfLabels t.program) else none).flatten ++
      cellLabels I.desc reader ++
      (I.transitions.map fun t => cellWakeLabels reader t.program).flatten := by
    exact List.mem_append.mpr (Or.inr hcol)
  simpa [prioLabels] using mem_dedup _ l hmem

/-- A carried program is a suffix of a listed transition of the same template. -/
def ProgSrc (I : Impl) (w : World) : Prop :=
  ∀ id es, carried ((w.st id).phase) = some es →
    ∃ tr ∈ I.transitions, tr.template = tname id ∧ ∃ pre, pre ++ es = tr.program

/-- Priority-lane labels are distinct and belong to the template's declared set. -/
def LaneOk (I : Impl) (w : World) : Prop :=
  ∀ id, (laneLabels ((w.st id).prio)).Nodup ∧
    ∀ m ∈ (w.st id).prio, m.label ∈ prioLabels I (tname id)

theorem self_of_suffix (pre es : List Eff) (l : String) (hl : l ∈ selfLabels es) :
    l ∈ selfLabels (pre ++ es) := by
  rw [selfLabels_append]
  exact List.mem_append.mpr (Or.inr hl)

theorem cell_of_suffix (reader : String) (pre es : List Eff) (l : String)
    (hl : l ∈ cellWakeLabels reader es) : l ∈ cellWakeLabels reader (pre ++ es) := by
  rw [cellWake_append]
  exact List.mem_append.mpr (Or.inr hl)

theorem sched_declared (I : Impl) (w : World) (hS : ProgSrc I w) (id : InstId) (es : List Eff)
    (hc : carried ((w.st id).phase) = some es) (l : String) (hl : l ∈ selfLabels es) :
    l ∈ prioLabels I (tname id) := by
  obtain ⟨tr, hm, ht, pre, hpre⟩ := hS id es hc
  have hsub := self_of_suffix pre es l hl
  rw [hpre] at hsub
  simpa [ht] using self_in_prio I tr hm l hsub

theorem wake_declared (I : Impl) (w : World) (hS : ProgSrc I w) (id : InstId) (es : List Eff)
    (hc : carried ((w.st id).phase) = some es) (reader l : String)
    (hl : l ∈ cellWakeLabels reader es) : l ∈ prioLabels I reader := by
  obtain ⟨tr, hm, _, pre, hpre⟩ := hS id es hc
  have hsub := cell_of_suffix reader pre es l hl
  rw [hpre] at hsub
  exact cell_in_prio I reader tr hm l hsub

theorem filterMap_nil_mem {α β} (xs : List α) (f : α → Option β) (h : xs.filterMap f = [])
    (x : α) (hx : x ∈ xs) : f x = none := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    cases hx with
    | head =>
      cases hf : f x
      · rfl
      · simp [List.filterMap, hf] at h
    | tail _ ht =>
      cases hf : f y
      · rw [List.filterMap, hf] at h
        exact ih h ht
      · simp [List.filterMap, hf] at h

theorem priority_le_cap (D : Description) (hG : GraphOk D) (t : Template) (ht : t ∈ D.templates) :
    Affine.leB t.priorityBound t.priorityCapacity = true := by
  have hnone := filterMap_nil_mem D.templates
    (fun u => if Affine.leB u.priorityBound u.priorityCapacity then none
      else some s!"fail: priority lane {u.name}: bound {u.priorityBound.toString} > capacity {u.priorityCapacity.toString}")
    (by simpa [priorityFails] using hG.priority) t ht
  by_cases hle : Affine.leB t.priorityBound t.priorityCapacity = true
  · exact hle
  · simp [hle] at hnone

theorem prio_len_bound (I : Impl) (hL : LocalOk I) (t : Template) (ht : t ∈ I.desc.templates) :
    (prioLabels I t.name).length ≤ t.priorityBound.b ∧ t.priorityBound.a = 0 := by
  have hok := (local_parts I hL).2.2.2.2.2.1
  unfold prioOk at hok
  have hbody := (List.all_eq_true _ _).mp hok t ht
  rw [Bool.and_eq_true] at hbody
  exact ⟨decide_eq_true_eq.mp hbody.1, (beq_iff_eq).mp hbody.2⟩

theorem lane_find_name (xs : List Template) (r : String) (t : Template)
    (h : xs.findSome? (fun u => if u.name == r then some u else none) = some t) : t.name = r := by
  induction xs with
  | nil => simp at h
  | cons u us ih =>
    rw [List.findSome?_cons] at h
    by_cases hn : (u.name == r) = true
    · simp only [hn, ite_true] at h
      cases h
      exact (beq_iff_eq).mp hn
    · have hf : (u.name == r) = false := by
        cases hbb : u.name == r <;> simp_all
      simp only [hf, ite_false] at h
      exact ih h

theorem template_name (D : Description) (r : String) (t : Template)
    (ht : templateOf D r = some t) : t.name = r := by
  exact lane_find_name D.templates r t (by simpa [templateOf] using ht)

theorem declared_le_cap (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (id : InstId)
    (t : Template) (ht : templateOf I.desc (tname id) = some t) :
    (prioLabels I (tname id)).length ≤ capPrio I.desc N id := by
  have hname := template_name I.desc (tname id) t ht
  have hmem := template_mem I.desc (tname id) t ht
  have hlen := prio_len_bound I hL t hmem
  have hle := priority_le_cap I.desc hG t hmem
  have hcoeff := (Affine.leB_iff t.priorityBound t.priorityCapacity).mp hle
  have heval : t.priorityBound.eval N ≤ t.priorityCapacity.eval N :=
    Affine.eval_le_of_coeff _ _ hcoeff.1 hcoeff.2 N
  have hb : (prioLabels I t.name).length ≤ t.priorityBound.eval N := by
    simpa [Affine.eval, hlen.2] using hlen.1
  simpa [capPrio, ht, hname] using Nat.le_trans hb heval

theorem any_label_false (ms : List Msg) (label : String)
    (h : (ms.any fun p => p.label == label) = false) : label ∉ laneLabels ms := by
  intro hmem
  induction ms with
  | nil => cases hmem
  | cons m ms ih =>
    rw [List.any_cons] at h
    rw [laneLabels, List.map_cons, List.mem_cons] at hmem
    cases hb : m.label == label
    · rw [hb, Bool.false_or] at h
      cases hmem with
      | inl hhead =>
        have ht : (m.label == label) = true := (beq_iff_eq).mpr hhead.symm
        simp [ht] at hb
      | inr ht =>
        exact ih h ht
    · rw [hb] at h
      simp at h

theorem proceed_prio (a : Actor) (k : Cont) : (proceed a k).prio = a.prio := by
  cases hr : k.rest <;> simp [proceed, hr]

theorem lane_has_room (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hLane : LaneOk I w) (id : InstId) (t : Template)
    (ht : templateOf I.desc (tname id) = some t) (label : String)
    (hmem : label ∈ prioLabels I (tname id))
    (hfresh : ((w.st id).prio.any fun p => p.label == label) = false) :
    (w.st id).prio.length < capPrio I.desc N id := by
  have hcap := declared_le_cap I hL hG N id t ht
  have hnd := (hLane id).1
  have hsub : ∀ x ∈ laneLabels ((w.st id).prio), x ∈ prioLabels I (tname id) := by
    intro x hx
    simp [laneLabels, List.mem_map] at hx
    obtain ⟨m, hm, hlab⟩ := hx
    simpa [hlab] using (hLane id).2 m hm
  have hnot : label ∉ laneLabels ((w.st id).prio) := any_label_false _ _ hfresh
  cases Classical.em ((w.st id).prio.length < capPrio I.desc N id) with
  | inl hlt => exact hlt
  | inr hge =>
    have hfull : capPrio I.desc N id ≤ (w.st id).prio.length := Nat.le_of_not_lt hge
    have hlen : (laneLabels ((w.st id).prio)).length = (w.st id).prio.length := by
      simp [laneLabels]
    exact False.elim (prio_no_crash (capPrio I.desc N id) (prioLabels I (tname id))
      (laneLabels ((w.st id).prio)) label hsub hnd hcap (by simpa [hlen] using hfull) hnot hmem)

theorem prog_src_of (I : Impl) (w w' : World) (hS : ProgSrc I w)
    (horigin : ∀ i es, carried ((w'.st i).phase) = some es →
      (∃ es0, carried ((w.st i).phase) = some es0 ∧ (es = es0 ∨ ∃ e, es0 = e :: es)) ∨
      ∃ tr ∈ I.transitions, tr.template = tname i ∧ es = tr.program) : ProgSrc I w' := by
  intro i es hc
  rcases horigin i es hc with ⟨es0, hc0, hsub⟩ | ⟨tr, hm, ht, hprog⟩
  · obtain ⟨tr, hm, ht, pre, happ⟩ := hS i es0 hc0
    rcases hsub with rfl | ⟨e, heq⟩
    · exact ⟨tr, hm, ht, pre, happ⟩
    · exact ⟨tr, hm, ht, pre ++ [e], by
        simp [List.append_assoc, List.singleton_append, ← heq, happ]⟩
  · exact ⟨tr, hm, ht, [], by simp [hprog]⟩

theorem prog_src_init (I : Impl) (N : Nat) : ProgSrc I (initWorld I N) := by
  intro id es hc
  simp [init_phase, carried] at hc

theorem lane_init (I : Impl) (N : Nat) : LaneOk I (initWorld I N) := by
  intro id
  have hst := init_base_st I N id
  rw [hst]
  split
  · cases ht : templateOf I.desc (tname id) <;>
      simp [initActor, withTokens, absentActor, ht, laneLabels]
  · simp [absentActor, laneLabels]

theorem lane_tail (I : Impl) (w : World) (hLane : LaneOk I w) (id : InstId) (m : Msg) (ms : List Msg)
    (hp : (w.st id).prio = m :: ms) : (laneLabels ms).Nodup ∧ ∀ x ∈ ms, x.label ∈ prioLabels I (tname id) := by
  have hnd := (hLane id).1
  have hmem := (hLane id).2
  rw [hp, laneLabels, List.map_cons, List.nodup_cons] at hnd
  refine ⟨hnd.2, ?_⟩
  intro x hx
  exact hmem x (by simp [hp, hx])

theorem lane_upsert (I : Impl) (w : World) (hLane : LaneOk I w) (id : InstId) (label : String)
    (hsender : InstId) (hmem : label ∈ prioLabels I (tname id)) :
    (laneLabels (upsertPrio (w.st id).prio { label := label, sender := hsender, callFrom := none })).Nodup ∧
      ∀ m ∈ upsertPrio (w.st id).prio { label := label, sender := hsender, callFrom := none },
        m.label ∈ prioLabels I (tname id) := by
  by_cases hany : ((w.st id).prio.any fun p => p.label == label) = true
  · have hsame : upsertPrio (w.st id).prio { label := label, sender := hsender, callFrom := none } =
        (w.st id).prio := by simp [upsertPrio, hany]
    rw [hsame]
    exact hLane id
  · have hfalse : ((w.st id).prio.any fun p => p.label == label) = false := by
      cases hbit : (w.st id).prio.any fun p => p.label == label <;> simp_all
    have hnot := any_label_false _ _ hfalse
    have hlabels : laneLabels (upsertPrio (w.st id).prio { label := label, sender := hsender, callFrom := none }) =
        laneLabels ((w.st id).prio) ++ [label] := by
      simp [upsertPrio, hfalse, laneLabels]
    refine ⟨?_, ?_⟩
    · rw [hlabels]
      exact nodup_snoc (hLane id).1 hnot
    · intro m hm
      have hgrown : upsertPrio (w.st id).prio { label := label, sender := hsender, callFrom := none } =
          (w.st id).prio ++ [{ label := label, sender := hsender, callFrom := none }] := by
        simp [upsertPrio, hfalse]
      rw [hgrown] at hm
      simp [List.mem_append] at hm
      cases hm with
      | inl hold => exact (hLane id).2 m hold
      | inr hnew =>
        cases hnew
        exact hmem

theorem enqueue_prio (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).prio = (w.st i).prio := by
  cases isCall <;>
    (unfold enqueueOrPark
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive]
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor, chargeSender, bumpToken, proceed_prio]
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken, proceed_prio]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip, chargeSender, bumpToken, proceed_prio]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, proceed_prio]
           · by_cases hid : i = dst
             · simp [hid]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
       · simp [hroom]
         by_cases hsame : sender = dst
         · rw [if_pos hsame]
           simp [setActor, chargeSender, bumpToken]
           by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken]
         · rw [if_neg hsame]
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip, chargeSender, bumpToken]
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken]
           · by_cases hid : i = dst
             · simp [hid]
               rw [if_neg hflip]
             · rw [if_neg hi, if_neg hid]
     · simp [hlive, setActor, proceed_prio]
       by_cases hi : i = sender <;> simp [hi, proceed_prio])

theorem cell_head_label (dst label : String) (value : Nat) (es : List Eff) :
    label ∈ cellWakeLabels dst (.cell dst label value :: es) := by
  simp [cellWakeLabels]

theorem self_head_label (label : String) (es : List Eff) :
    label ∈ selfLabels (.selfSchedule label :: es) := by
  simp [selfLabels]

/-- The list an actor is still carrying after `exec` is the list it carried before,
a one-effect tail of that list, or the program of a listed transition. -/
theorem carried_origin_exec (I : Impl) (w : World) (id : InstId) (k : Cont)
    (hph : (w.st id).phase = .run k) (i : InstId) (es : List Eff)
    (hc : carried ((execRun I w id (w.st id) k).st i).phase = some es) :
    (∃ es0, carried ((w.st i).phase) = some es0 ∧ (es = es0 ∨ ∃ e, es0 = e :: es)) ∨
      ∃ tr ∈ I.transitions, tr.template = tname i ∧ es = tr.program := by
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      simp [execRun, hrest, setActor] at hc
      by_cases hi : i = id
      · simp [hi, carried] at hc
      · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
    | cons e tail =>
      have hold : carried ((w.st id).phase) = some (e :: tail) := by simp [carried, hph, hrest]
      cases e with
      | send dst label hint =>
        simp [execRun, hrest] at hc
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr, setActor] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
            exact Or.inl ⟨.send dst label hint :: tail, hold,
              Or.inr ⟨.send dst label hint, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
        | some dstId =>
          simp [hr] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, none⟩ false
              (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) es hc
            exact Or.inl ⟨.send dst label hint :: tail, hold,
              Or.inr ⟨.send dst label hint, by simp [afterHead, heq]⟩⟩
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
            have heq := carried_proceed _ _ es (by simpa [setActor] using hc)
            exact Or.inl ⟨.call dst label hint :: tail, hold,
              Or.inr ⟨.call dst label hint, by simp [afterHead, heq]⟩⟩
          · exact Or.inl ⟨es, by simpa [hi] using hc, Or.inl rfl⟩
        | some dstId =>
          simp [hr] at hc
          by_cases hi : i = id
          · rw [hi] at hc ⊢
            have heq := enqueue_carried w I.desc id dstId ⟨label, id, some id⟩ true
              (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) es hc
            exact Or.inl ⟨.call dst label hint :: tail, hold,
              Or.inr ⟨.call dst label hint, by simp [afterHead, heq]⟩⟩
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
        by_cases hi : i = id
        · rw [hi] at hc ⊢
          have heq := reply_sender_rest w id _ es hc
          exact Or.inl ⟨.reply :: tail, hold, Or.inr ⟨.reply, by simp [afterHead, heq]⟩⟩
        · unfold performReply at hc
          cases hto : replyTo with
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
            | idle =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | run _ =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | awaitEffect _ =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | awaitPeer _ =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | parked _ _ _ =>
              simp [hcall, setActor, hi] at hc
              exact Or.inl ⟨es, hc, Or.inl rfl⟩
            | crashed =>
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
              have hpre : carried ((w.st i).phase) = some es := by
                simpa [readCells_st, phase_refund, phase_refundP, setActor, hi] using hrel
              exact Or.inl ⟨es, hpre, Or.inl rfl⟩
          · rw [if_neg hkill] at hc
            exact Or.inl ⟨es, hc, Or.inl rfl⟩

theorem prog_src_exec (I : Impl) (w : World) (id : InstId) (k : Cont) (hS : ProgSrc I w)
    (hph : (w.st id).phase = .run k) : ProgSrc I (execRun I w id (w.st id) k) :=
  prog_src_of I w _ hS (fun i es hc => carried_origin_exec I w id k hph i es hc)

theorem prog_src_finish (I : Impl) (w w' : World) (id : InstId) (hS : ProgSrc I w)
    (h : finishWait w id = some w') : ProgSrc I w' := by
  apply prog_src_of I w w' hS
  intro i es hc
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
        exact Or.inl ⟨k.rest, by simp [carried, heq], Or.inl (by simp [hc, hk])⟩
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
        exact Or.inl ⟨k.rest, by simp [carried, heq], Or.inl (by simp [hc, hk])⟩
    · simp [setActor, hi] at hc
      exact Or.inl ⟨es, hc, Or.inl rfl⟩
  · cases h

theorem prog_src_spawn (I : Impl) (w w' : World) (template : String) (hS : ProgSrc I w)
    (h : spawn I w template = some w') : ProgSrc I w' := by
  apply prog_src_of I w w' hS
  intro i es hc
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

theorem prog_src_prio (I : Impl) (w w' : World) (id : InstId) (hS : ProgSrc I w)
    (h : receivePrio I w id = some w') : ProgSrc I w' := by
  apply prog_src_of I w w' hS
  intro i es hc
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
        have hc' : carried a1.phase = some es := by simpa [setActor] using hc
        obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc'
        exact Or.inr ⟨tr, hm, htmpl, hprog⟩
      · have hst := deliver_st I w id _ m w1 a1 i hdel
        exact Or.inl ⟨es, by simpa [setActor, hi, hst] using hc, Or.inl rfl⟩

theorem prog_src_bulk (I : Impl) (w w' : World) (id : InstId) (hS : ProgSrc I w)
    (h : receiveBulk I w id = some w') : ProgSrc I w' := by
  apply prog_src_of I w w' hS
  intro i es hc
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
              have hph : ((creditSender (setActor w1 id a1) (tname id) p.msg.sender).st p.sender).phase =
                  a1.phase := by simp [phase_credit, setActor, hs]
              have hold := carried_resume _ p.isCall p.sender es (by simpa [setActor, hs] using hc)
              have hc1 : carried a1.phase = some es := by
                simpa [phase_credit, setActor, hs] using hold
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ p.msg w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
            · have hc1 : carried a1.phase = some es := by simpa [setActor, hs, phase_credit] using hc
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ p.msg w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · by_cases hs : i = p.sender
            · rw [hs] at hc
              have hpre := carried_resume _ p.isCall id es (by simpa [setActor] using hc)
              have hst := deliver_st I w id _ p.msg w1 a1 p.sender hdel
              have hne : p.sender ≠ id := fun h => hid (hs.trans h)
              have hc0 : carried ((w.st p.sender).phase) = some es := by
                simpa [setActor, hne, phase_credit, hst] using hpre
              exact Or.inl ⟨es, by simpa [hs] using hc0, Or.inl rfl⟩
            · have hst := deliver_st I w id _ p.msg w1 a1 i hdel
              exact Or.inl ⟨es, by simpa [setActor, hs, hid, phase_credit, hst] using hc, Or.inl rfl⟩
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
            have hc1 : carried a1.phase = some es := by simpa [setActor, phase_credit] using hc
            obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
            exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · have hst := deliver_st I w id _ m w1 a1 i hdel
            exact Or.inl ⟨es, by simpa [setActor, hid, phase_credit, hst] using hc, Or.inl rfl⟩
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
              have hc1 : carried a1.phase = some es := by simpa [phase_credit, setActor, hphA, hs] using hpre
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
            · have hc1 : carried a1.phase = some es := by simpa [setActor, hs, phase_credit, hphA] using hc
              obtain ⟨tr, hm, htmpl, hprog⟩ := deliver_carries I w id _ m w1 a1 es hdel hc1
              exact Or.inr ⟨tr, hm, htmpl, hprog⟩
          · by_cases hs : i = p.sender
            · rw [hs] at hc
              have hpre := carried_resume _ p.isCall id es (by simpa [setActor] using hc)
              have hst := deliver_st I w id _ m w1 a1 p.sender hdel
              have hne : p.sender ≠ id := fun h => hid (hs.trans h)
              have hc0 : carried ((w.st p.sender).phase) = some es := by
                simpa [setActor, hne, phase_credit, hst, hphA] using hpre
              exact Or.inl ⟨es, by simpa [hs] using hc0, Or.inl rfl⟩
            · have hst := deliver_st I w id _ m w1 a1 i hdel
              exact Or.inl ⟨es, by simpa [setActor, hs, hid, phase_credit, hst, hphA] using hc, Or.inl rfl⟩

theorem prog_src_head (I : Impl) (w w' : World) (id : InstId) (hS : ProgSrc I w)
    (h : execHead I w id = some w') : ProgSrc I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact prog_src_exec I w id k hS hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem prog_src_apply (I : Impl) (a : Action) (w w' : World) (hS : ProgSrc I w)
    (h : apply I a w = some w') : ProgSrc I w' := by
  cases a with
  | recvBulk id => exact prog_src_bulk I w w' id hS (by simpa [apply] using h)
  | recvPrio id => exact prog_src_prio I w w' id hS (by simpa [apply] using h)
  | exec id => exact prog_src_head I w w' id hS (by simpa [apply] using h)
  | finish id => exact prog_src_finish I w w' id hS (by simpa [apply] using h)
  | spawn template => exact prog_src_spawn I w w' template hS (by simpa [apply] using h)

theorem prog_src_reachable (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) : ProgSrc I w := by
  induction hR with
  | init => exact prog_src_init I N
  | step w w' a _ h ih => exact prog_src_apply I a w w' ih h

theorem lane_same (I : Impl) (w w' : World) (hLane : LaneOk I w)
    (h : ∀ i, (w'.st i).prio = (w.st i).prio) : LaneOk I w' := by
  intro i
  simpa [h i] using hLane i

theorem lane_set (I : Impl) (w : World) (hLane : LaneOk I w) (id : InstId) (a : Actor)
    (hok : (laneLabels a.prio).Nodup ∧ ∀ m ∈ a.prio, m.label ∈ prioLabels I (tname id)) :
    LaneOk I (setActor w id a) := by
  intro i
  by_cases hi : i = id
  · rw [hi]
    simpa [setActor] using hok
  · simpa [setActor, hi] using hLane i

theorem try_wake_lane (I : Impl) (w : World) (hLane : LaneOk I w) (dstId : InstId)
    (label : String) (writer : InstId) (hmem : label ∈ prioLabels I (tname dstId)) :
    LaneOk I (tryWake I.desc w dstId label writer) := by
  by_cases hif : (((w.st dstId).life == .alive) &&
      decide ((w.st dstId).prio.length < capPrio I.desc w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · let grown := upsertPrio (w.st dstId).prio { label := label, sender := writer, callFrom := none }
    let a : Actor := { (w.st dstId) with prio := grown }
    have hup := lane_upsert I w hLane dstId label writer hmem
    have hstep : tryWake I.desc w dstId label writer = setActor w dstId a := by
      simp [tryWake, hif, a, grown]
    rw [hstep]
    exact lane_set I w hLane dstId a hup
  · simp [tryWake, hif]
    exact hLane

theorem wakes_lane (I : Impl) (ids : List InstId) (w : World) (hLane : LaneOk I w)
    (dst label : String) (writer : InstId)
    (hmem : ∀ id ∈ ids, tname id = dst ∧ label ∈ prioLabels I dst) :
    LaneOk I (ids.foldl (fun w id => tryWake I.desc w id label writer) w) := by
  induction ids generalizing w with
  | nil => simpa using hLane
  | cons j js ih =>
    simp only [List.foldl_cons]
    have hj := hmem j (List.Mem.head _)
    have h1 := try_wake_lane I w hLane j label writer (by simpa [hj.1] using hj.2)
    exact ih _ h1 (fun id hid => hmem id (List.Mem.tail _ hid))

theorem reader_name (w : World) (dst : String) (id : InstId) (h : id ∈ readersOf w dst) :
    tname id = dst := by
  simp [readersOf] at h
  exact h.2.1

theorem resume_prio (a : Actor) (b : Bool) (dst : InstId) : (resumeSender a b dst).prio = a.prio := by
  cases h : a.phase with
  | parked _ _ k =>
    cases b <;> cases hk : k.rest <;> simp [resumeSender, h, hk, proceed]
  | idle => simp [resumeSender, h]
  | run _ => simp [resumeSender, h]
  | awaitReply _ _ => simp [resumeSender, h]
  | awaitEffect _ => simp [resumeSender, h]
  | awaitPeer _ => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem release_prio (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).prio = (w.st i).prio := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      by_cases hi : i = p.sender
      · have hset : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i).prio =
            (w.st i).prio := by
          rw [hi]
          simp [setActor, resume_prio]
        exact hmid.trans hset
      · have hset : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i).prio =
            (w.st i).prio := by simp [setActor, hi]
        exact hmid.trans hset

theorem src_template (I : Impl) (hL : LocalOk I) (w : World) (hS : ProgSrc I w) (id : InstId)
    (es : List Eff) (hc : carried ((w.st id).phase) = some es) :
    ∃ t, templateOf I.desc (tname id) = some t := by
  obtain ⟨tr, hm, ht, _, _⟩ := hS id es hc
  have hok := transitionOk_of_mem I hL tr hm
  rw [← ht]
  cases htpl : templateOf I.desc tr.template with
  | none => simp [transitionOk, htpl] at hok
  | some t => exact ⟨t, rfl⟩

/-- A reachable actor is never crashed: the only write of `.crashed` is a priority
lane that `lane_has_room` shows still has space. -/
theorem schedule_not_crashed (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (id : InstId) (label : String) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (hph : (w.st id).phase = .run ⟨.selfSchedule label :: tail, toState, replyTo⟩)
    (hpre : ∀ i, (w.st i).phase ≠ .crashed) (i : InstId) :
    ((execRun I w id (w.st id) ⟨.selfSchedule label :: tail, toState, replyTo⟩).st i).phase ≠ .crashed := by
  have hc : carried ((w.st id).phase) = some (.selfSchedule label :: tail) := by
    simp [carried, hph]
  have hdecl := sched_declared I w hS id _ hc label (self_head_label label tail)
  obtain ⟨t, ht⟩ := src_template I hL w hS id _ hc
  simp only [execRun]
  cases hany : ((w.st id).prio.any fun p => p.label == label)
  · have hlt := lane_has_room I hL hG w.N w hLane id t ht label hdecl hany
    simp [hany, hlt]
    by_cases hi : i = id
    · rw [hi]
      cases htail : tail <;> simp [setActor, proceed, htail] <;> intro h <;> cases h
    · simpa [setActor, hi] using hpre i
  · simp [hany]
    by_cases hi : i = id
    · rw [hi]
      cases htail : tail <;> simp [setActor, proceed, htail] <;> intro h <;> cases h
    · simpa [setActor, hi] using hpre i

theorem lane_schedule (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (id : InstId) (label : String) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (hph : (w.st id).phase = .run ⟨.selfSchedule label :: tail, toState, replyTo⟩) :
    LaneOk I (execRun I w id (w.st id) ⟨.selfSchedule label :: tail, toState, replyTo⟩) := by
  have hc : carried ((w.st id).phase) = some (.selfSchedule label :: tail) := by simp [carried, hph]
  have hdecl := sched_declared I w hS id _ hc label (self_head_label label tail)
  obtain ⟨t, ht⟩ := src_template I hL w hS id _ hc
  cases hany : ((w.st id).prio.any fun p => p.label == label)
  · have hlt := lane_has_room I hL hG w.N w hLane id t ht label hdecl hany
    let grown := upsertPrio (w.st id).prio { label := label, sender := id, callFrom := none }
    let a := proceed { (w.st id) with prio := grown }
      (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩)
    have hup := lane_upsert I w hLane id label id hdecl
    have hok : (laneLabels a.prio).Nodup ∧ ∀ m ∈ a.prio, m.label ∈ prioLabels I (tname id) := by
      simpa [a, proceed_prio] using hup
    have hstep : execRun I w id (w.st id) ⟨.selfSchedule label :: tail, toState, replyTo⟩ =
        setActor w id a := by simp [execRun, hany, hlt, a, grown]
    rw [hstep]
    exact lane_set I w hLane id a hok
  · simp [execRun, hany]
    exact lane_same I w _ hLane (fun i => by
      by_cases hi : i = id
      · simp [setActor, hi, proceed_prio]
      · simp [setActor, hi])

theorem credit_prio (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).prio = (w.st i).prio :=
  (credit_life w dst sender i).2.2.2

theorem refund_prio (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).prio = (w.st i).prio :=
  (refund_life w dst ms i).2.2.2

theorem refundP_prio (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).prio = (w.st i).prio :=
  (refundP_life w dst ps i).2.2.2

theorem deliver_prio (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : a1.prio = a.prio := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        rfl
    · split at h
      · cases h
      · cases h
        split <;> rfl

theorem lane_finish (I : Impl) (w w' : World) (id : InstId) (hLane : LaneOk I w)
    (h : finishWait w id = some w') : LaneOk I w' := by
  unfold finishWait at h
  split at h
  · cases h
    exact lane_same I w _ hLane (fun i => by
      by_cases hi : i = id <;> simp [setActor, proceed_prio, hi])
  · cases h
    exact lane_same I w _ hLane (fun i => by
      by_cases hi : i = id <;> simp [setActor, proceed_prio, hi])
  · cases h

theorem lane_spawn (I : Impl) (w w' : World) (template : String) (hLane : LaneOk I w)
    (h : spawn I w template = some w') : LaneOk I w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · cases h
      let nid := InstId.peer template (w.nextIx template)
      let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n } : World)
      have hR : LaneOk I wR := lane_same I w wR hLane (fun _ => rfl)
      let born : Actor := withTokens I.desc template
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 }
      have hborn : LaneOk I (setActor wR nid born) :=
        lane_set I wR hR nid born (by simp [born, withTokens, laneLabels])
      have hst : ∀ i, ((readCells I.desc (setActor wR nid born) nid).st i).prio =
          ((setActor wR nid born).st i).prio := fun i => by simp [readCells_st]
      simpa [nid, wR, born] using lane_same I _ _ hborn hst
    · cases h

theorem lane_prio (I : Impl) (w w' : World) (id : InstId) (hLane : LaneOk I w)
    (h : receivePrio I w id = some w') : LaneOk I w' := by
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      have hst : ∀ i, (w1.st i).prio = (w.st i).prio := fun i => by
        simp [deliver_st I w id _ m w1 a1 i hdel]
      have hW : LaneOk I w1 := lane_same I w w1 hLane hst
      have hp : a1.prio = ms := by
        have hdelp := deliver_prio I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel
        simpa using hdelp
      have htail := lane_tail I w hLane id m ms hprio
      exact lane_set I w1 hW id a1 (by simpa [hp] using htail)

theorem lane_bulk (I : Impl) (w w' : World) (id : InstId) (hLane : LaneOk I w)
    (h : receiveBulk I w id = some w') : LaneOk I w' := by
  apply lane_same I w w' hLane
  intro i
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
          have hst := deliver_st I w id _ p.msg w1 a1 i hdel
          have hp := deliver_prio I w id _ p.msg w1 a1 hdel
          have hset : ((setActor w1 id a1).st i).prio = (w.st i).prio := by
            by_cases hi : i = id
            · rw [hi]; simp [setActor, hp]
            · simp [setActor, hi, hst]
          by_cases hi : i = id
          · rw [hi]
            by_cases hs : id = p.sender
            · simp [setActor, hs, resume_prio, credit_prio, hp]
            · simp [setActor, hs, credit_prio, hp]
          · by_cases hs : i = p.sender
            · have hne : ¬ p.sender = id := fun h => hi (by simpa [h] using hs)
              simp [setActor, hi, hs, resume_prio, credit_prio]
              rw [if_neg hne]
              have hpri : (w1.st i).prio = (w.st i).prio := congrArg (·.prio) hst
              simpa [hs] using hpri
            · simp [setActor, hi, hs, credit_prio, hst]
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 i hdel
          have hp := deliver_prio I w id _ m w1 a1 hdel
          rw [credit_prio]
          by_cases hi : i = id
          · rw [hi]; simp [setActor, hp]
          · simp [setActor, hi, hst]
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hst := deliver_st I w id _ m w1 a1 i hdel
          have hp := deliver_prio I w id _ m w1 a1 hdel
          have hset : ((setActor w1 id admitted).st i).prio = (w.st i).prio := by
            by_cases hi : i = id
            · rw [hi]; simp [admitted, setActor, hp]
            · simp [admitted, setActor, hi, hst]
          by_cases hi : i = id
          · rw [hi]
            by_cases hs : id = p.sender
            · simp [setActor, admitted, hs, resume_prio, credit_prio, hp]
            · simp [setActor, admitted, hs, credit_prio, hp]
          · by_cases hs : i = p.sender
            · have hne : ¬ p.sender = id := fun h => hi (by simpa [h] using hs)
              simp [setActor, admitted, hi, hs, resume_prio, credit_prio]
              rw [if_neg hne]
              have hpri : (w1.st i).prio = (w.st i).prio := congrArg (·.prio) hst
              simpa [hs] using hpri
            · simp [setActor, admitted, hi, hs, credit_prio, hst]

theorem lane_exec (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (id : InstId) (k : Cont)
    (hph : (w.st id).phase = .run k) : LaneOk I (execRun I w id (w.st id) k) := by
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      exact lane_same I w _ hLane (fun i => by
        by_cases hi : i = id <;> simp [execRun, hrest, setActor, hi])
    | cons e tail =>
      cases e with
      | selfSchedule label =>
        exact lane_schedule I hL hG w hLane hS id label tail toState replyTo (by simpa [hrest] using hph)
      | send dst label hint =>
        simp [execRun, hrest]
        cases hr : route w I.desc dst hint with
        | none =>
          exact lane_same I w _ hLane (fun i => by
            by_cases hi : i = id <;> simp [hr, setActor, proceed_prio, hi])
        | some dstId =>
          simp [hr]
          exact lane_same I w _ hLane (fun i => enqueue_prio w I.desc id dstId _ false _ i)
      | call dst label hint =>
        simp [execRun, hrest]
        cases hr : route w I.desc dst hint with
        | none =>
          exact lane_same I w _ hLane (fun i => by
            by_cases hi : i = id <;> simp [hr, setActor, proceed_prio, hi])
        | some dstId =>
          simp [hr]
          exact lane_same I w _ hLane (fun i => enqueue_prio w I.desc id dstId _ true _ i)
      | internal =>
        exact lane_same I w _ hLane (fun i => by
          by_cases hi : i = id <;> simp [execRun, hrest, setActor, hi])
      | peer =>
        exact lane_same I w _ hLane (fun i => by
          by_cases hi : i = id <;> simp [execRun, hrest, setActor, hi])
      | trySend dst label hint =>
        exact lane_same I w _ hLane (fun i => by
          simp [execRun, hrest]
          cases hr : route w I.desc dst hint with
          | none =>
            by_cases hi : i = id <;> simp [hr, setActor, proceed_prio, hi]
          | some dstId =>
            simp [hr, chargeSender, bumpToken, proceed_prio]
            split
            · by_cases hi : i = id
              · by_cases hdi : dstId = id
                · simp [setActor, proceed_prio, chargeSender, bumpToken, hi, hdi]
                · have hflip : ¬ id = dstId := fun h => hdi h.symm
                  simp [setActor, proceed_prio, chargeSender, bumpToken, hi, hflip]
              · by_cases hd : i = dstId
                · have hne : dstId ≠ id := fun h => hi (by simpa [h, hd] using rfl)
                  simp [setActor, proceed_prio, chargeSender, bumpToken, hi, hd, hne]
                · simp [setActor, proceed_prio, chargeSender, bumpToken, hi, hd]
            · by_cases hi : i = id <;> simp [setActor, proceed_prio, hi])
      | reply =>
        exact lane_same I w _ hLane (fun i => by
          simp [execRun, hrest]
          unfold performReply
          cases hto : replyTo with
          | none =>
            by_cases hi : i = id <;> simp [hto, setActor, proceed_prio, hi]
          | some caller =>
            cases hcall : (w.st caller).phase with
            | awaitReply dst ck =>
              by_cases hd : dst = id
              · by_cases hi : i = id
                · by_cases hc : i = caller
                  · have hid : id = caller := hi.symm.trans hc
                    simp [hto, hcall, hd, setActor, proceed_prio, hi, hc, hid]
                  · have hne : id ≠ caller := fun h => hc (hi.trans h)
                    simp [hto, hcall, hd, setActor, proceed_prio, hi, hne]
                · by_cases hc : i = caller
                  · have hne : caller ≠ id := fun h => hi (hc.trans h)
                    simp [hto, hcall, hd, setActor, proceed_prio, hi, hc, hne]
                  · simp [hto, hcall, hd, setActor, proceed_prio, hi, hc]
              · by_cases hi : i = id
                · simp [hto, hcall, hd, setActor, proceed_prio, hi]
                · by_cases hc : i = caller
                  · have hne : caller ≠ id := fun h => hi (hc.trans h)
                    simp [hto, hcall, hd, setActor, proceed_prio, hi, hc, hne]
                  · simp [hto, hcall, hd, setActor, proceed_prio, hi, hc]
            | idle =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi]
            | run _ =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi]
            | awaitEffect _ =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi]
            | awaitPeer _ =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi]
            | parked _ _ _ =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi]
            | crashed =>
              by_cases hi : i = id <;> simp [hto, hcall, setActor, proceed_prio, hi])
      | cell dst label value =>
        have hdecl : label ∈ prioLabels I dst := by
          have hcar : carried ((w.st id).phase) = some (.cell dst label value :: tail) := by
            simp [carried, hph, hrest]
          exact wake_declared I w hS id _ hcar dst label (cell_head_label dst label value tail)
        let base := setCell w dst label { value := max (w.cell dst label).value value, dirty := true }
        let stepped := setActor base id
          (proceed (base.st id) (afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩))
        have hbase := lane_same I w base hLane (fun _ => by simp [base, setCell])
        have hstepL : LaneOk I stepped := by
          apply lane_set I base hbase id _
          simpa [stepped, proceed_prio, base, setCell] using hLane id
        simp only [execRun, hrest]
        cases hdirty : (w.cell dst label).dirty
        · simp [hdirty, base, stepped]
          rw [wakeReaders]
          exact wakes_lane I (readersOf stepped dst) stepped hstepL dst label id (fun r hr =>
            ⟨reader_name _ _ _ hr, by simpa [reader_name _ _ _ hr] using hdecl⟩)
        · simp [hdirty]
          apply lane_set
          · exact lane_same I w _ hLane (fun _ => rfl)
          · simpa [proceed_prio, setCell] using hLane id
      | terminate =>
        simp only [execRun, hrest]
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simp [htpl]
          exact hLane
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill]
            let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
              (tname id) (w.st id).parked
            have hbase : LaneOk I base :=
              lane_same I w base hLane (fun i => by
                simp [base, readCells_st, refund_prio, refundP_prio])
            let dead : Actor :=
              { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
            have hempty : (laneLabels dead.prio).Nodup ∧ ∀ m ∈ dead.prio, m.label ∈ prioLabels I (tname id) := by
              simp [dead, laneLabels]
            have hdead := lane_set I base hbase id dead hempty
            exact lane_same I _ _ hdead (fun i => release_prio _ id (w.st id).parked i)
          · simp [htpl, hkill]
            exact hLane

theorem lane_head (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w w' : World) (id : InstId)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (h : execHead I w id = some w') : LaneOk I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact lane_exec I hL hG w hLane hS id k hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem lane_apply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (a : Action) (w w' : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (h : apply I a w = some w') : LaneOk I w' := by
  cases a with
  | recvBulk id => exact lane_bulk I w w' id hLane (by simpa [apply] using h)
  | recvPrio id => exact lane_prio I w w' id hLane (by simpa [apply] using h)
  | exec id => exact lane_head I hL hG w w' id hLane hS (by simpa [apply] using h)
  | finish id => exact lane_finish I w w' id hLane (by simpa [apply] using h)
  | spawn template => exact lane_spawn I w w' template hLane (by simpa [apply] using h)

theorem lane_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : LaneOk I w := by
  induction hR with
  | init => exact lane_init I N
  | step w w' a prev h ih =>
    exact lane_apply I hL hG a w w' ih (prog_src_reachable I N w prev) h

/-- No actor is in the overflow phase. -/
def NoCrash (w : World) : Prop := ∀ i, (w.st i).phase ≠ .crashed

theorem proceed_not_crashed (a : Actor) (k : Cont) : (proceed a k).phase ≠ .crashed := by
  cases hk : k.rest <;> simp [proceed, hk] <;> intro h <;> cases h

theorem set_not_crashed (w : World) (hpre : NoCrash w) (id : InstId) (a : Actor)
    (hp : a.phase ≠ .crashed) (i : InstId) :
    ((setActor w id a).st i).phase ≠ .crashed := by
  by_cases hi : i = id
  · rw [hi]
    simpa [setActor] using hp
  · simpa [setActor, hi] using hpre i

theorem resume_not_crashed (a : Actor) (b : Bool) (dst : InstId) (h : a.phase ≠ .crashed) :
    (resumeSender a b dst).phase ≠ .crashed := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases b
    · cases hk : k.rest <;> simp [resumeSender, hph, hk, proceed] <;> intro hc <;> cases hc
    · simp [resumeSender, hph]
  | idle => simpa [resumeSender, hph] using h
  | run _ => simpa [resumeSender, hph] using h
  | awaitReply _ _ => simpa [resumeSender, hph] using h
  | awaitEffect _ => simpa [resumeSender, hph] using h
  | awaitPeer _ => simpa [resumeSender, hph] using h
  | crashed => exact False.elim (h hph)

theorem enqueue_not_crashed (w : World) (hpre : NoCrash w) (D : Description) (sender dst : InstId)
    (msg : Msg) (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).phase ≠ .crashed := by
  by_cases hi : i = sender
  · rw [hi]
    cases isCall with
    | false =>
      unfold enqueueOrPark
      by_cases hlive : (w.st dst).life = .alive
      · simp [hlive]
        by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
        · simp [hroom]
          by_cases hsame : sender = dst
          · simp [hsame, setActor]
            exact proceed_not_crashed _ k
          · simp [hsame, setActor]
            exact proceed_not_crashed _ k
        · simp [hroom]
          by_cases hsame : sender = dst <;> simp [hsame, setActor]
      · simp [hlive, setActor]
        exact proceed_not_crashed _ k
    | true =>
      unfold enqueueOrPark
      by_cases hlive : (w.st dst).life = .alive
      · simp [hlive]
        by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
        · simp [hroom]
          by_cases hsame : sender = dst <;> simp [hsame, setActor]
        · simp [hroom]
          by_cases hsame : sender = dst <;> simp [hsame, setActor]
      · simp [hlive, setActor]
        exact proceed_not_crashed _ k
  · simpa [enqueue_phase_other w D sender dst msg isCall k i hi] using hpre i

theorem deliver_not_crashed (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : a1.phase ≠ .crashed := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        simp
    · split at h
      · cases h
      · cases h
        split <;> simp

theorem release_not_crashed (w : World) (hpre : NoCrash w) (id : InstId) (ps : List Parked)
    (i : InstId) : ((releaseParked w id ps).st i).phase ≠ .crashed := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hpre i
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w hpre
    · rw [if_neg hskip]
      have hres := resume_not_crashed (w.st p.sender) false id (hpre p.sender)
      have hset : NoCrash (setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
        intro j
        by_cases hj : j = p.sender
        · rw [hj]
          simpa [setActor] using hres
        · simpa [setActor, hj] using hpre j
      exact ih _ hset

theorem exec_not_crashed (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (hpre : NoCrash w) (id : InstId) (k : Cont)
    (hph : (w.st id).phase = .run k) (i : InstId) :
    ((execRun I w id (w.st id) k).st i).phase ≠ .crashed := by
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      have hp : ({ (w.st id) with phase := Phase.idle, typestate := toState }).phase ≠ .crashed := by
        simp
      simpa [execRun, hrest] using set_not_crashed w hpre id _ hp i
    | cons e tail =>
      cases e with
      | selfSchedule label =>
        exact schedule_not_crashed I hL hG w hLane hS id label tail toState replyTo
          (by simpa [hrest] using hph) hpre i
      | send dst label hint =>
        simp only [execRun, hrest]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using set_not_crashed w hpre id (proceed (w.st id) (afterHead
            ⟨.send dst label hint :: tail, toState, replyTo⟩)) (proceed_not_crashed _ _) i
        | some dstId =>
          simpa [hr] using enqueue_not_crashed w hpre I.desc id dstId
            { label := label, sender := id, callFrom := none } false
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) i
      | call dst label hint =>
        simp only [execRun, hrest]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using set_not_crashed w hpre id (proceed (w.st id) (afterHead
            ⟨.call dst label hint :: tail, toState, replyTo⟩)) (proceed_not_crashed _ _) i
        | some dstId =>
          simpa [hr] using enqueue_not_crashed w hpre I.desc id dstId
            { label := label, sender := id, callFrom := some id } true
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) i
      | internal =>
        have hp : ({ (w.st id) with phase := .awaitEffect (afterHead
            ⟨.internal :: tail, toState, replyTo⟩) }).phase ≠ .crashed := by
          simp
        simpa [execRun, hrest] using set_not_crashed w hpre id _ hp i
      | peer =>
        have hp : ({ (w.st id) with phase := .awaitPeer (afterHead
            ⟨.peer :: tail, toState, replyTo⟩) }).phase ≠ .crashed := by
          simp
        simpa [execRun, hrest] using set_not_crashed w hpre id _ hp i
      | trySend dst label hint =>
        simp only [execRun, hrest]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using set_not_crashed w hpre id (proceed (w.st id) (afterHead
            ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) (proceed_not_crashed _ _) i
        | some dstId =>
          simp only [hr]
          split
          · let k' := afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩
            let charged := chargeSender (w.st id) (tname dstId)
            have hch : charged.phase = (w.st id).phase := by simp [charged, chargeSender, bumpToken]
            let w1 := setActor w id charged
            have h1 : NoCrash w1 := by
              intro j
              by_cases hj : j = id
              · rw [hj]
                simpa [w1, setActor, hch] using hpre id
              · simpa [w1, setActor, hj] using hpre j
            let stored : Actor := { (w1.st dstId) with box := (w1.st dstId).box ++ [{ label := label, sender := id, callFrom := none }] }
            have hstored : stored.phase = (w1.st dstId).phase := by simp [stored]
            let w2 := setActor w1 dstId stored
            have h2 : NoCrash w2 := set_not_crashed w1 h1 dstId stored (by simpa [hstored] using h1 dstId)
            show ((setActor w2 id (proceed (w2.st id) k')).st i).phase ≠ .crashed
            exact set_not_crashed w2 h2 id (proceed (w2.st id) k') (proceed_not_crashed _ _) i
          · simpa using set_not_crashed w hpre id (proceed (w.st id) (afterHead
              ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) (proceed_not_crashed _ _) i
      | reply =>
        simp only [execRun, hrest]
        unfold performReply
        cases hto : replyTo with
        | none =>
          simpa [hto] using set_not_crashed w hpre id
            (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
            (proceed_not_crashed _ _) i
        | some caller =>
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            by_cases hd : dst = id
            · let k' := afterHead ⟨.reply :: tail, toState, replyTo⟩
              let resumed := proceed (w.st caller) ck
              let w1 := setActor w caller resumed
              have h1 : NoCrash w1 := set_not_crashed w hpre caller resumed (proceed_not_crashed _ _)
              simp only [hto, hcall, hd]
              rw [ite_true]
              exact set_not_crashed
                (setActor w caller (proceed (w.st caller) ck))
                (by simpa [w1, resumed] using h1) id
                (proceed ((setActor w caller (proceed (w.st caller) ck)).st id)
                  (afterHead { rest := .reply :: tail, toState := toState, replyTo := some caller }))
                (proceed_not_crashed _ _) i
            · simpa [hto, hcall, hd] using set_not_crashed w hpre id
                (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
                (proceed_not_crashed _ _) i
          | idle =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
          | run _ =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
          | awaitEffect _ =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
          | awaitPeer _ =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
          | parked _ _ _ =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
          | crashed =>
            simpa [hto, hcall] using set_not_crashed w hpre id
              (proceed (w.st id) (afterHead ⟨.reply :: tail, toState, replyTo⟩))
              (proceed_not_crashed _ _) i
      | cell dst label value =>
        let k' := afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩
        let base := setCell w dst label { value := max (w.cell dst label).value value, dirty := true }
        let stepped := setActor base id (proceed (base.st id) k')
        have hbase : NoCrash base := by
          intro j
          simpa [base, setCell] using hpre j
        have hstep : NoCrash stepped :=
          set_not_crashed base hbase id (proceed (base.st id) k') (proceed_not_crashed _ _)
        simp only [execRun, hrest]
        cases hdirty : (w.cell dst label).dirty
        · show ((wakeReaders I.desc stepped dst label id).st i).phase ≠ .crashed
          simp only [wakeReaders]
          rw [wakes_phase (readersOf stepped dst) I.desc stepped dst label id i]
          exact hstep i
        · show (stepped.st i).phase ≠ .crashed
          exact hstep i
      | terminate =>
        simp only [execRun, hrest]
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simpa [htpl] using hpre i
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill]
            let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
              (tname id) (w.st id).parked
            have hbase : NoCrash base := by
              intro j
              simpa [base, readCells_st, phase_refund, phase_refundP] using hpre j
            let dead : Actor :=
              { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
            have hdead : NoCrash (setActor base id dead) := by
              intro j
              by_cases hj : j = id
              · rw [hj]
                simp [setActor, dead]
              · simpa [setActor, hj] using hbase j
            simpa [base, dead] using
              release_not_crashed (setActor base id dead) hdead id (w.st id).parked i
          · simpa [htpl, hkill] using hpre i

theorem head_not_crashed (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hLane : LaneOk I w) (hS : ProgSrc I w) (hpre : NoCrash w) (id : InstId) (w' : World)
    (h : execHead I w id = some w') : NoCrash w' := by
  intro i
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact exec_not_crashed I hL hG w hLane hS hpre id k hph i
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem finish_not_crashed (w : World) (hpre : NoCrash w) (id : InstId) (w' : World)
    (h : finishWait w id = some w') : NoCrash w' := by
  intro i
  unfold finishWait at h
  split at h
  · cases h
    exact set_not_crashed w hpre id (proceed (w.st id) _) (proceed_not_crashed _ _) i
  · cases h
    exact set_not_crashed w hpre id (proceed (w.st id) _) (proceed_not_crashed _ _) i
  · cases h

theorem spawn_not_crashed (I : Impl) (w : World) (hpre : NoCrash w) (template : String) (w' : World)
    (h : spawn I w template = some w') : NoCrash w' := by
  intro i
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · cases h
      let nid := InstId.peer template (w.nextIx template)
      let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n } : World)
      have hR : NoCrash wR := by
        intro j
        simpa [wR] using hpre j
      let born : Actor := withTokens I.desc template
        { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [],
          tokens := fun _ => 0 }
      have hp : born.phase ≠ .crashed := by simp [born, withTokens]
      have hborn : NoCrash (setActor wR nid born) := set_not_crashed wR hR nid born hp
      have hs := readCells_st I.desc (setActor wR nid born) nid i
      show ((readCells I.desc (setActor wR nid born) nid).st i).phase ≠ .crashed
      simpa [hs] using hborn i
    · cases h

theorem prio_not_crashed (I : Impl) (w : World) (hpre : NoCrash w) (id : InstId) (w' : World)
    (h : receivePrio I w id = some w') : NoCrash w' := by
  intro i
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      have hst := deliver_st I w id _ m w1 a1 i hdel
      have hp := deliver_not_crashed I w id _ m w1 a1 hdel
      by_cases hi : i = id
      · rw [hi]
        simpa [setActor] using hp
      · simpa [setActor, hi, hst] using hpre i

theorem bulk_not_crashed (I : Impl) (w : World) (hpre : NoCrash w) (id : InstId) (w' : World)
    (h : receiveBulk I w id = some w') : NoCrash w' := by
  intro i
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
          have hp := deliver_not_crashed I w id _ p.msg w1 a1 hdel
          have hinner : NoCrash (creditSender (setActor w1 id a1) (tname id) p.msg.sender) := by
            intro j
            rw [phase_credit]
            by_cases hj : j = id
            · rw [hj]
              simpa [setActor] using hp
            · have hst := deliver_st I w id _ p.msg w1 a1 j hdel
              simpa [setActor, hj, hst] using hpre j
          by_cases hs : i = p.sender
          · rw [hs]
            simpa [setActor] using resume_not_crashed _ _ _ (hinner p.sender)
          · simpa [setActor, hs] using hinner i
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hp := deliver_not_crashed I w id _ m w1 a1 hdel
          rw [phase_credit]
          by_cases hi : i = id
          · rw [hi]
            simpa [setActor] using hp
          · have hst := deliver_st I w id _ m w1 a1 i hdel
            simpa [setActor, hi, hst] using hpre i
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hp := deliver_not_crashed I w id _ m w1 a1 hdel
          have hadm : admitted.phase = a1.phase := by simp [admitted]
          have hinner : NoCrash (creditSender (setActor w1 id admitted) (tname id) m.sender) := by
            intro j
            rw [phase_credit]
            by_cases hj : j = id
            · rw [hj]
              simpa [setActor, hadm] using hp
            · have hst := deliver_st I w id _ m w1 a1 j hdel
              simpa [setActor, admitted, hj, hst] using hpre j
          by_cases hs : i = p.sender
          · rw [hs]
            simpa [setActor] using resume_not_crashed _ _ _ (hinner p.sender)
          · simpa [setActor, hs] using hinner i

theorem apply_not_crashed (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (a : Action)
    (w w' : World) (hpre : NoCrash w) (hLane : LaneOk I w) (hS : ProgSrc I w)
    (h : apply I a w = some w') : NoCrash w' := by
  cases a with
  | recvBulk id => exact bulk_not_crashed I w hpre id w' (by simpa [apply] using h)
  | recvPrio id => exact prio_not_crashed I w hpre id w' (by simpa [apply] using h)
  | exec id => exact head_not_crashed I hL hG w hLane hS hpre id w' (by simpa [apply] using h)
  | finish id => exact finish_not_crashed w hpre id w' (by simpa [apply] using h)
  | spawn template => exact spawn_not_crashed I w hpre template w' (by simpa [apply] using h)

theorem fold_read_st (D : Description) (ids : List InstId) (w : World) (i : InstId) :
    ((ids.foldl (fun w id => readCells D w id) w).st i) = w.st i := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact (ih (readCells D w j)).trans (readCells_st D w j i)

theorem init_not_crashed (I : Impl) (N : Nat) : NoCrash (initWorld I N) := by
  intro i
  have hidle : ((initWorld I N).st i).phase = .idle := by
    unfold initWorld
    rw [fold_read_st]
    cases hb : (coreRoster I.desc).contains i with
    | false =>
      show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).phase = .idle
      rw [hb]
      simp [absentActor]
    | true =>
      show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).phase = .idle
      rw [hb]
      unfold initActor
      cases templateOf I.desc (tname i) with
      | none => simp [absentActor]
      | some _ => simp [withTokens]
  simp [hidle]

theorem reachable_not_crashed (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) : NoCrash w := by
  induction hR with
  | init => exact init_not_crashed I N
  | step w w' a prev happ ih =>
    exact apply_not_crashed I hL hG a w w' ih (lane_reachable I hL hG N w prev)
      (prog_src_reachable I N w prev) happ

theorem proceed_wait_none (a : Actor) (k : Cont) : waitKind (proceed a k) = none := by
  cases hk : k.rest <;> simp [proceed, waitKind, hk]

/-- Resuming a blocking send leaves the sender running or idle. -/
theorem resume_send_clears (a : Actor) (dst : InstId) (k : Cont)
    (h : a.phase = .parked dst false k) : waitKind (resumeSender a false dst) = none := by
  simp [resumeSender, h]
  exact proceed_wait_none a k

/-- Resuming a parked call is the caller's `awaitReply`. The wait kind stays a call reply. -/
theorem resume_call_waits (a : Actor) (dst : InstId) (k : Cont)
    (h : a.phase = .parked dst true k) : (resumeSender a true dst).phase = .awaitReply dst k := by
  simp [resumeSender, h]

/-- Installing the receiver and crediting some sender leaves a different actor's phase. -/
theorem install_sender_phase (w w1 : World) (id : InstId) (installed : Actor) (who sender : InstId)
    (hne : sender ≠ id) (hst : w1.st sender = w.st sender) :
    ((creditSender (setActor w1 id installed) (tname id) who).st sender).phase =
      (w.st sender).phase := by
  rw [phase_credit, setActor_other w1 id sender installed hne, hst]

theorem bulk_resumes_send (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) (s : InstId)
    (hs : s = p.sender) (hne : s ≠ id) (k : Cont)
    (hph : (w.st s).phase = .parked id false k) (hc : p.isCall = false) :
    waitKind (w'.st s) = none := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hst := deliver_st I w id _ p.msg w1 a1 s hdel
        have hpre := install_sender_phase w w1 id a1 p.msg.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self]
        rw [hc]
        exact resume_send_clears _ id k (hpre.trans hph)
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hst := deliver_st I w id _ m w1 a1 s hdel
        have hpre := install_sender_phase w w1 id admitted m.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self, admitted]
        rw [hc]
        exact resume_send_clears _ id k (hpre.trans hph)

theorem bulk_admits_call (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) (s : InstId)
    (hs : s = p.sender) (hne : s ≠ id) (k : Cont)
    (hph : (w.st s).phase = .parked id true k) (hc : p.isCall = true) :
    (w'.st s).phase = .awaitReply id k := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hst := deliver_st I w id _ p.msg w1 a1 s hdel
        have hpre := install_sender_phase w w1 id a1 p.msg.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self]
        rw [hc]
        exact resume_call_waits _ id k (hpre.trans hph)
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hst := deliver_st I w id _ m w1 a1 s hdel
        have hpre := install_sender_phase w w1 id admitted m.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self, admitted]
        rw [hc]
        exact resume_call_waits _ id k (hpre.trans hph)

theorem credit_parked (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).parked = (w.st i).parked := by
  by_cases hi : i = sender
  · simp [creditSender, setActor, hi, bumpToken]
  · simp [creditSender, setActor, hi]

theorem deliver_parked (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : a1.parked = a.parked := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        rfl
    · split at h
      · cases h
      · cases h
        split <;> rfl

theorem finish_parked (w w' : World) (id i : InstId) (h : finishWait w id = some w') :
    (w'.st i).parked = (w.st i).parked := by
  unfold finishWait at h
  split at h
  · cases h
    by_cases hi : i = id
    · simp [setActor, hi, proceed_parked]
    · simp [setActor, hi]
  · cases h
    by_cases hi : i = id
    · simp [setActor, hi, proceed_parked]
    · simp [setActor, hi]
  · cases h

theorem prio_parked (I : Impl) (w w' : World) (id i : InstId) (h : receivePrio I w id = some w') :
    (w'.st i).parked = (w.st i).parked := by
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      have hpk := deliver_parked I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel
      have hst := deliver_st I w id _ m w1 a1 i hdel
      by_cases hi : i = id
      · rw [hi]
        simp [setActor, hpk]
      · simp [setActor, hi, hst]

theorem bulk_other_parked (I : Impl) (w w' : World) (j i : InstId)
    (h : receiveBulk I w j = some w') (hne : i ≠ j) :
    (w'.st i).parked = (w.st i).parked := by
  unfold receiveBulk at h
  by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st j).box with
    | nil =>
      cases hpark : (w.st j).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w j _ p.msg w1 a1 i hdel
          by_cases hs : i = p.sender
          · have hnj : p.sender ≠ j := fun h => hne (hs.trans h)
            rw [hs] at hst ⊢
            simp [setActor_self, resume_parked, credit_parked]
            rw [setActor_other w1 j p.sender a1 hnj]
            exact congrArg (·.parked) hst
          · simp [setActor_other (creditSender (setActor w1 j a1) (tname j) p.msg.sender) p.sender i _ hs,
              credit_parked, setActor_other w1 j i a1 hne, hst]
    | cons m ms =>
      cases hpark : (w.st j).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w j _ m w1 a1 i hdel
          rw [credit_parked]
          simp [setActor, hne, hst]
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hst := deliver_st I w j _ m w1 a1 i hdel
          by_cases hs : i = p.sender
          · have hnj : p.sender ≠ j := fun h => hne (hs.trans h)
            rw [hs] at hst ⊢
            simp [setActor_self, resume_parked, credit_parked, admitted]
            rw [setActor_other w1 j p.sender admitted hnj]
            exact congrArg (·.parked) hst
          · simp [admitted, setActor_other (creditSender (setActor w1 j admitted) (tname j) m.sender)
              p.sender i _ hs, credit_parked, setActor_other w1 j i admitted hne, hst]

theorem spawn_keeps_parked (I : Impl) (w w' : World) (template : String)
    (h : spawn I w template = some w') (hO : OpenSlots w) (i : InstId) (p : Parked)
    (hm : p ∈ (w.st i).parked) : p ∈ (w'.st i).parked := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · cases h
      let nid := InstId.peer template (w.nextIx template)
      have hfree := (hO template (w.nextIx template) (Nat.le_refl _)).2.2
      by_cases hi : i = nid
      · rw [hi, hfree] at hm
        cases hm
      · let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [], tokens := fun _ => 0 }
        have hs := readCells_st I.desc (setActor wR nid born) nid i
        rw [hs]
        simpa [wR, setActor, hi] using hm
    · cases h

/-- Where a sender sits in a parked list. An absent sender is reported at `length`. -/
def parkIndex : List Parked → InstId → Nat
  | [], _ => 0
  | p :: ps, s => if p.sender == s then 0 else parkIndex ps s + 1

theorem parkIndex_nil (s : InstId) : parkIndex [] s = 0 := rfl

theorem parkIndex_head (p : Parked) (ps : List Parked) (s : InstId) (h : p.sender = s) :
    parkIndex (p :: ps) s = 0 := by
  simp [parkIndex, h]

theorem parkIndex_skip (p : Parked) (ps : List Parked) (s : InstId) (h : p.sender ≠ s) :
    parkIndex (p :: ps) s = parkIndex ps s + 1 := by
  have hb : (p.sender == s) = false := by simpa [beq_iff_eq] using h
  simp [parkIndex, hb]

theorem parkIndex_append (ps : List Parked) (s : InstId) (q : Parked)
    (h : parkIndex ps s < ps.length) : parkIndex (ps ++ [q]) s = parkIndex ps s := by
  induction ps with
  | nil => simp [parkIndex] at h
  | cons p ps ih =>
    by_cases hs : p.sender = s
    · simp [parkIndex, hs]
    · have hb : (p.sender == s) = false := by simpa [beq_iff_eq] using hs
      have hlt : parkIndex ps s < ps.length := by
        simp [parkIndex, hb, List.length] at h
        omega
      simp [parkIndex, hb, ih hlt]

theorem parkIndex_mem (ps : List Parked) (s : InstId) (h : parkIndex ps s < ps.length) :
    ∃ p, p ∈ ps ∧ p.sender = s := by
  induction ps with
  | nil => simp [parkIndex] at h
  | cons p ps ih =>
    by_cases hs : p.sender = s
    · exact ⟨p, List.Mem.head _, hs⟩
    · have hb : (p.sender == s) = false := by simpa [beq_iff_eq] using hs
      have hlt : parkIndex ps s < ps.length := by
        simp [parkIndex, hb, List.length] at h
        omega
      obtain ⟨q, hq, hqs⟩ := ih hlt
      exact ⟨q, List.Mem.tail _ hq, hqs⟩

/-- A step of one mailbox: leave it, append behind every current entry, or take the head. -/
def QueueStep (old new : List Parked) : Prop :=
  new = old ∨ (∃ a, new = old ++ [a]) ∨ (∃ p ps, old = p :: ps ∧ new = ps)

/-- An update that does not drop a parked entry. Exec and enqueue are of this form. -/
def QueueGrow (old new : List Parked) : Prop :=
  new = old ∨ ∃ a, new = old ++ [a]

theorem grow_step (old new : List Parked) (h : QueueGrow old new) : QueueStep old new := by
  rcases h with h | ⟨a, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨a, h⟩)

theorem queue_place (old new : List Parked) (s : InstId) (h : QueueStep old new)
    (hin : parkIndex old s < old.length) :
    (parkIndex new s < new.length ∧ parkIndex new s ≤ parkIndex old s) ∨
      ∃ p ps, old = p :: ps ∧ new = ps ∧ p.sender = s ∧ parkIndex old s = 0 := by
  rcases h with h | h | ⟨p, ps, hold, hnew⟩
  · rw [h]
    exact Or.inl ⟨hin, Nat.le_refl _⟩
  · obtain ⟨a, hnew⟩ := h
    rw [hnew]
    have hidx := parkIndex_append old s a hin
    refine Or.inl ⟨?_, ?_⟩
    · rw [hidx, List.length_append]
      simp
      exact Nat.lt_succ_of_lt hin
    · rw [hidx]
      exact Nat.le_refl _
  · rw [hold] at hin
    rw [hold, hnew]
    by_cases hs : p.sender = s
    · exact Or.inr ⟨p, ps, rfl, rfl, hs, parkIndex_head p ps s hs⟩
    · have hidx := parkIndex_skip p ps s hs
      have hlt : parkIndex ps s < ps.length := by
        rw [hidx, List.length_cons] at hin
        omega
      exact Or.inl ⟨hlt, by rw [hidx]; omega⟩

theorem bulk_drops_head (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) :
    (w'.st id).parked = ps := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hpk := deliver_parked I w id _ p.msg w1 a1 hdel
        by_cases hs : id = p.sender
        · rw [hs]
          simp [setActor_self, resume_parked, credit_parked, hpk]
        · simp [hs, credit_parked, setActor, hpk]
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        by_cases hs : id = p.sender
        · rw [hs]
          simp [setActor_self, resume_parked, credit_parked, admitted]
        · simp [hs, admitted, credit_parked, setActor]

/-- A parked entry is only ever added at the end of the list. -/
theorem enqueue_queue (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    QueueGrow ((w.st i).parked) ((enqueueOrPark w D sender dst msg isCall k).st i).parked := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall
      · by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            simp [setActor, charge_parked, proceed_parked]
            exact Or.inl rfl
          · simp [setActor, hi]
            exact Or.inl rfl
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬ dst = sender := fun h => hsame h.symm
            have hempty : (w.st dst).parked = [] := hroom.1
            simp [setActor, hempty, charge_parked, proceed_parked]
            rw [if_neg hflip]
            exact Or.inl rfl
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              simp [setActor, hi, charge_parked, proceed_parked]
              exact Or.inl rfl
            · rw [if_neg hsame]
              simp [setActor, hi, his]
              exact Or.inl rfl
      · by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            simp [setActor, charge_parked]
            exact Or.inl rfl
          · simp [setActor, hi]
            exact Or.inl rfl
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬ dst = sender := fun h => hsame h.symm
            have hempty : (w.st dst).parked = [] := hroom.1
            simp [setActor, hempty, charge_parked, proceed_parked]
            rw [if_neg hflip]
            exact Or.inl rfl
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              simp [setActor, hi, charge_parked]
              exact Or.inl rfl
            · rw [if_neg hsame]
              simp [setActor, hi, his]
              exact Or.inl rfl
    · simp [hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        by_cases hi : i = dst
        · rw [hi]
          simp [setActor, charge_parked]
          exact Or.inr ⟨{ sender := dst, msg := msg, isCall := isCall }, rfl⟩
        · simp [setActor, hi]
          exact Or.inl rfl
      · by_cases hi : i = dst
        · rw [if_neg hsame, hi]
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          simp [setActor, charge_parked]
          rw [if_neg hflip]
          exact Or.inr ⟨{ sender := sender, msg := msg, isCall := isCall }, rfl⟩
        · by_cases his : i = sender
          · rw [his, if_neg hsame]
            simp [setActor, hi, charge_parked]
            exact Or.inl rfl
          · rw [if_neg hsame]
            simp [setActor, hi, his]
            exact Or.inl rfl
  · simp [hlive]
    by_cases hi : i = sender
    · rw [hi]
      simp [setActor, proceed_parked]
      exact Or.inl rfl
    · simp [setActor, hi]
      exact Or.inl rfl

theorem release_preserves_parked (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      have hset : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i).parked =
          (w.st i).parked := by
        by_cases hi : i = p.sender
        · rw [hi]
          simp [setActor, resume_parked]
        · simp [setActor, hi]
      rw [hset] at hmid
      exact hmid

theorem refund_msgs_parked (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    simpa [refundMsgs, credit_parked] using ih (creditSender w dst m.sender)

theorem refund_park_parked (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    simpa [refundParked, credit_parked] using ih (creditSender w dst p.msg.sender)

theorem try_wake_parked (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) : ((tryWake D w dstId label writer).st i).parked = (w.st i).parked := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_parked (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).parked = (w.st i).parked := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (try_wake_parked D w j label writer i)

/-- Resuming a blocking send does not leave it blocked on the same partner. -/
theorem resume_leaves_block (a : Actor) (dst : InstId) (k : Cont) (b : Bool)
    (h : a.phase = .parked dst false k) :
    waitKind (resumeSender a b dst) ≠ some (.blockingSend dst) := by
  cases b
  · simp [resumeSender, h]
    rw [proceed_wait_none]
    intro hc
    cases hc
  · simp [resumeSender, h, waitKind]

theorem bulk_queue (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w') :
    QueueStep ((w.st id).parked) ((w'.st id).parked) := by
  cases hp : (w.st id).parked with
  | nil =>
    unfold receiveBulk at h
    by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
    · simp [hready] at h
    · simp [hready, hp] at h
      cases hbox : (w.st id).box with
      | nil => simp [hbox] at h
      | cons m ms =>
        simp [hbox] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hpk := deliver_parked I w id _ m w1 a1 hdel
          simp [credit_parked, setActor_self, hpk, hp]
          exact Or.inl rfl
  | cons p ps =>
    exact Or.inr (Or.inr ⟨p, ps, rfl, bulk_drops_head I w w' id h p ps hp⟩)

theorem release_life_self (w : World) (id : InstId) (ps : List Parked) :
    ((releaseParked w id ps).st id).life = (w.st id).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hne : p.sender ≠ id := by
        intro h
        have : (p.isCall || decide (p.sender = id)) = true := by simp [h]
        simp [this] at hskip
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      have hflip : id ≠ p.sender := fun h => hne h.symm
      rwa [setActor_other w p.sender id (resumeSender (w.st p.sender) false id) hflip] at hmid

theorem queue_actor (w : World) (id : InstId) (a : Actor) (mb : InstId)
    (h : a.parked = (w.st id).parked) :
    QueueGrow ((w.st mb).parked) ((setActor w id a).st mb).parked := by
  by_cases hmb : mb = id
  · rw [hmb, setActor_self, h]
    exact Or.inl rfl
  · rw [setActor_other w id mb a hmb]
    exact Or.inl rfl

theorem exec_queue (I : Impl) (w : World) (id : InstId) (k : Cont) (mb : InstId)
    (hlive : ((execRun I w id (w.st id) k).st mb).life = .alive) :
    QueueGrow ((w.st mb).parked) ((execRun I w id (w.st id) k).st mb).parked := by
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil =>
      simpa [execRun] using queue_actor w id { (w.st id) with phase := .idle, typestate := toState } mb rfl
    | cons e tail =>
      cases e with
      | send dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using queue_actor w id (proceed (w.st id)
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
        | some dstId =>
          simpa [hr] using enqueue_queue w I.desc id dstId
            { label := label, sender := id, callFrom := none } false
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) mb
      | call dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using queue_actor w id (proceed (w.st id)
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
        | some dstId =>
          simpa [hr] using enqueue_queue w I.desc id dstId
            { label := label, sender := id, callFrom := some id } true
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) mb
      | internal =>
        simpa [execRun] using queue_actor w id
          { (w.st id) with phase := .awaitEffect (afterHead ⟨.internal :: tail, toState, replyTo⟩) }
          mb rfl
      | peer =>
        simpa [execRun] using queue_actor w id
          { (w.st id) with phase := .awaitPeer (afterHead ⟨.peer :: tail, toState, replyTo⟩) }
          mb rfl
      | selfSchedule label =>
        simp only [execRun]
        by_cases hany : ((w.st id).prio.any fun p => p.label == label) = true
        · simpa [hany] using queue_actor w id (proceed (w.st id)
            (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
        · by_cases hlt : (w.st id).prio.length < capPrio I.desc w.N id
          · simpa [hany, hlt] using queue_actor w id (proceed { (w.st id) with prio := upsertPrio (w.st id).prio { label := label, sender := id, callFrom := none } } (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩)) mb (by simp [proceed_parked])
          · simpa [hany, hlt] using queue_actor w id { (w.st id) with phase := .crashed } mb rfl
      | trySend dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using queue_actor w id (proceed (w.st id)
            (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
        | some dstId =>
          simp only [hr]
          split
          · by_cases hmb : mb = id
            · rw [hmb]
              by_cases hd : dstId = id
              · rw [hd]
                simp [setActor, chargeSender, bumpToken, proceed_parked]
                exact Or.inl rfl
              · have hflip : ¬ id = dstId := fun h => hd h.symm
                simp [setActor, chargeSender, bumpToken, proceed_parked]
                rw [if_neg hflip]
                exact Or.inl rfl
            · by_cases hd : mb = dstId
              · rw [hd]
                have hne : dstId ≠ id := fun h => hmb (hd.trans h)
                simp [setActor, hne, chargeSender, bumpToken]
                exact Or.inl rfl
              · simp [setActor, hmb, hd]
                exact Or.inl rfl
          · exact queue_actor w id (proceed (w.st id)
              (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
      | reply =>
        simp only [execRun]
        unfold performReply
        cases hto : replyTo with
        | none =>
          simpa [hto] using queue_actor w id (proceed (w.st id)
            (afterHead ⟨.reply :: tail, toState, replyTo⟩)) mb (proceed_parked _ _)
        | some caller =>
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            by_cases hd : dst = id
            · simp [hto, hcall, hd]
              by_cases hmb : mb = id
              · rw [hmb]
                by_cases hc : caller = id
                · rw [hc]
                  simp [setActor, proceed_parked]
                  exact Or.inl rfl
                · have hflip : ¬ id = caller := fun h => hc h.symm
                  simp [setActor, proceed_parked]
                  rw [if_neg hflip]
                  exact Or.inl rfl
              · by_cases hc : mb = caller
                · rw [hc]
                  have hne : ¬ caller = id := fun h => hmb (hc.trans h)
                  simp [setActor, hne, proceed_parked]
                  exact Or.inl rfl
                · simp [setActor, hmb, hc]
                  exact Or.inl rfl
            · simpa [hto, hcall, hd] using queue_actor w id (proceed (w.st id)
                (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | idle =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | run _ =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | awaitEffect _ =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | awaitPeer _ =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | parked _ _ _ =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
          | crashed =>
            simpa [hto, hcall] using queue_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_parked _ _)
      | cell dst label value =>
        simp only [execRun]
        cases hdirty : (w.cell dst label).dirty
        · simp [hdirty, wakeReaders]
          rw [wakes_parked]
          exact queue_actor (setCell w dst label
            { value := max (w.cell dst label).value value, dirty := true }) id
            (proceed ((setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }).st id)
              (afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩)) mb
            (by simpa [setCell] using proceed_parked _ _)
        · simp [hdirty]
          exact queue_actor (setCell w dst label
            { value := max (w.cell dst label).value value, dirty := true }) id
            (proceed ((setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }).st id)
              (afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩)) mb
            (by simpa [setCell] using proceed_parked _ _)
      | terminate =>
        simp only [execRun]
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simp [htpl]
          exact Or.inl rfl
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill]
            by_cases hmb : mb = id
            · exfalso
              rw [hmb] at hlive
              simp [execRun, htpl, hkill] at hlive
              rw [release_life_self] at hlive
              simp [setActor] at hlive
            · have hbase : ∀ i, ((refundParked (refundMsgs (readCells I.desc w id) (tname id)
                  (w.st id).box) (tname id) (w.st id).parked).st i).parked = (w.st i).parked := by
                intro i
                rw [refund_park_parked, refund_msgs_parked, readCells_st]
              rw [release_preserves_parked, setActor_other _ id mb _ hmb, hbase]
              exact Or.inl rfl
          · simp [htpl, hkill]
            exact Or.inl rfl

theorem alive_queue (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hO : OpenSlots w) (mb : InstId) (hlive : (w'.st mb).life = .alive) :
    QueueStep ((w.st mb).parked) ((w'.st mb).parked) := by
  cases a with
  | recvBulk id =>
    by_cases hmb : mb = id
    · rw [hmb]
      exact bulk_queue I w w' id (by simpa [apply] using h)
    · exact Or.inl (bulk_other_parked I w w' id mb (by simpa [apply] using h) hmb)
  | recvPrio id =>
    exact Or.inl (prio_parked I w w' id mb (by simpa [apply] using h))
  | finish id =>
    exact Or.inl (finish_parked w w' id mb (by simpa [apply] using h))
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hliveA : (w.st id).life = .alive
    · simp [hliveA] at h
      cases hph : (w.st id).phase with
      | run k =>
        simp [hph] at h
        cases h
        exact grow_step _ _ (exec_queue I w id k mb hlive)
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hliveA] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [], tokens := fun _ => 0 }
        have hfree := (hO template (w.nextIx template) (Nat.le_refl _)).2.2
        by_cases hmb : mb = nid
        · rw [hmb, hfree]
          have hs := readCells_st I.desc (setActor wR nid born) nid nid
          rw [hs]
          simp [wR, setActor, born]
          exact Or.inl rfl
        · have hs := readCells_st I.desc (setActor wR nid born) nid mb
          rw [hs]
          simp [wR, setActor, hmb]
          exact Or.inl rfl
      · cases h

/-- Dropping a head in front of `s` moves `s` one place closer to the head. -/
theorem recv_closer (I : Impl) (w w' : World) (dst : InstId) (h : receiveBulk I w dst = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st dst).parked = p :: ps) (s : InstId)
    (hne : p.sender ≠ s) (hin : parkIndex (p :: ps) s < (p :: ps).length) :
    parkIndex ((w'.st dst).parked) s + 1 = parkIndex (p :: ps) s ∧
      parkIndex ((w'.st dst).parked) s < ((w'.st dst).parked).length := by
  have hdrop := bulk_drops_head I w w' dst h p ps hp
  have hidx := parkIndex_skip p ps s hne
  have hlt : parkIndex ps s < ps.length := by
    rw [hidx, List.length_cons] at hin
    omega
  rw [hdrop]
  exact ⟨hidx.symm, hlt⟩

theorem grow_index (old new : List Parked) (s : InstId) (h : QueueGrow old new)
    (hin : parkIndex old s < old.length) :
    parkIndex new s = parkIndex old s ∧ parkIndex new s < new.length := by
  rcases h with h | ⟨a, h⟩
  · simp [h, hin]
  · rw [h]
    have hidx := parkIndex_append old s a hin
    refine ⟨hidx, ?_⟩
    rw [hidx, List.length_append]
    simp
    exact Nat.lt_succ_of_lt hin

theorem bulk_head_unblocks (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) (s : InstId)
    (hs : s = p.sender) (hne : s ≠ id) (k : Cont) (hph : (w.st s).phase = .parked id false k) :
    waitKind (w'.st s) ≠ some (.blockingSend id) := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hst := deliver_st I w id _ p.msg w1 a1 s hdel
        have hpre := install_sender_phase w w1 id a1 p.msg.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self]
        exact resume_leaves_block _ id k p.isCall (hpre.trans hph)
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hst := deliver_st I w id _ m w1 a1 s hdel
        have hpre := install_sender_phase w w1 id admitted m.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self, admitted]
        exact resume_leaves_block _ id k p.isCall (hpre.trans hph)

theorem resume_not_parked (a : Actor) (dst : InstId) (k : Cont) (b c : Bool)
    (h : a.phase = .parked dst c k) : ∀ d bit k', (resumeSender a b dst).phase ≠ .parked d bit k' := by
  intro d bit k' hbad
  cases b with
  | false =>
    cases hk : k.rest with
    | nil => simp [resumeSender, h, proceed, hk] at hbad
    | cons _ _ => simp [resumeSender, h, proceed, hk] at hbad
  | true => simp [resumeSender, h] at hbad

/-- A bulk receive whose parked head is `s` takes `s` out of every parked phase. -/
theorem bulk_head_leaves (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) (s : InstId)
    (hs : s = p.sender) (hne : s ≠ id) (c : Bool) (k : Cont)
    (hph : (w.st s).phase = .parked id c k) :
    ∀ d bit k', ((w'.st s).phase) ≠ .parked d bit k' := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hst := deliver_st I w id _ p.msg w1 a1 s hdel
        have hpre := install_sender_phase w w1 id a1 p.msg.sender s (by simpa [hs] using hne) hst
        intro d bit k' hbad
        rw [hs] at hpre hph hbad
        simp only [setActor_self] at hbad
        exact resume_not_parked _ id k p.isCall c (hpre.trans hph) d bit k' hbad
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hst := deliver_st I w id _ m w1 a1 s hdel
        have hpre := install_sender_phase w w1 id admitted m.sender s (by simpa [hs] using hne) hst
        intro d bit k' hbad
        rw [hs] at hpre hph hbad
        simp only [setActor_self, admitted] at hbad
        exact resume_not_parked _ id k p.isCall c (hpre.trans hph) d bit k' hbad

/-- While a parked wait stays parked on a live receiver, its queue index does not increase. -/
theorem step_index (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hO : OpenSlots w) (s dst : InstId) (c : Bool) (k k' : Cont)
    (hph : (w.st s).phase = .parked dst c k)
    (hph' : (w'.st s).phase = .parked dst c k')
    (halive : (w.st dst).life = .alive) (halive' : (w'.st dst).life = .alive)
    (hin : parkIndex ((w.st dst).parked) s < ((w.st dst).parked).length) :
    parkIndex ((w'.st dst).parked) s ≤ parkIndex ((w.st dst).parked) s ∧
      parkIndex ((w'.st dst).parked) s < ((w'.st dst).parked).length := by
  cases a with
  | recvBulk id =>
    by_cases hid : id = dst
    · rw [hid] at h
      cases hp : (w.st dst).parked with
      | nil => simp [parkIndex, hp] at hin
      | cons p ps =>
        rw [hp] at hin
        by_cases hs : p.sender = s
        · exfalso
          have hrecv : receiveBulk I w dst = some w' := by simpa [apply] using h
          have hne : s ≠ dst := by
            intro heq
            unfold receiveBulk at hrecv
            by_cases hready : (w.st dst).life ≠ .alive ∨ (w.st dst).phase ≠ .idle
            · simp [hready] at hrecv
            · have hidle : (w.st dst).phase = .idle := by
                by_cases hpI : (w.st dst).phase = .idle
                · exact hpI
                · exact False.elim (hready (Or.inr hpI))
              rw [← heq] at hidle
              simp [hph] at hidle
          have hleft := bulk_head_leaves I w w' dst hrecv p ps hp s (by rw [hs]) hne c k hph
          exact hleft dst c k' hph'
        · have hrec := recv_closer I w w' dst (by simpa [apply] using h) p ps hp s hs hin
          constructor
          · rw [← hrec.1]
            exact Nat.le_succ _
          · exact hrec.2
    · have heq := bulk_other_parked I w w' id dst (by simpa [apply] using h) (fun h => hid h.symm)
      rw [heq]
      exact ⟨Nat.le_refl _, hin⟩
  | recvPrio id =>
    have heq := prio_parked I w w' id dst (by simpa [apply] using h)
    rw [heq]
    exact ⟨Nat.le_refl _, hin⟩
  | finish id =>
    have heq := finish_parked w w' id dst (by simpa [apply] using h)
    rw [heq]
    exact ⟨Nat.le_refl _, hin⟩
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hrun : (w.st id).life = .alive
    · simp [hrun] at h
      cases hphase : (w.st id).phase with
      | run kk =>
        simp [hphase] at h
        cases h
        have hg := grow_index _ _ s (exec_queue I w id kk dst halive') hin
        exact ⟨Nat.le_of_eq hg.1, hg.2⟩
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hrun] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n } : World)
        let born : Actor := withTokens I.desc template { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [], parked := [], tokens := fun _ => 0 }
        have hfresh : dst ≠ nid := by
          intro heq
          have habsent := (hO template (w.nextIx template) (Nat.le_refl _)).1
          rw [heq] at halive
          rw [habsent] at halive
          cases halive
        have hs := readCells_st I.desc (setActor wR nid born) nid dst
        rw [hs]
        simp only [wR, setActor, hfresh]
        exact And.intro (Nat.le_refl _) hin
      · cases h

theorem index_zero_head (ps : List Parked) (s : InstId) (h : parkIndex ps s = 0)
    (hlen : 0 < ps.length) : ∃ p rest, ps = p :: rest ∧ p.sender = s := by
  cases ps with
  | nil => simp at hlen
  | cons p rest =>
    by_cases hs : p.sender = s
    · exact ⟨p, rest, rfl, hs⟩
    · have hidx := parkIndex_skip p rest s hs
      simp [hidx] at h

theorem index_mono (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (c : Bool) (i n : Nat)
    (hstay : ∀ t, i ≤ t → t ≤ i + n → ∃ k, ((ρ.cfg t).st s).phase = .parked dst c k)
    (halive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st dst).life = .alive)
    (hin : parkIndex (((ρ.cfg i).st dst).parked) s < (((ρ.cfg i).st dst).parked).length) :
    parkIndex (((ρ.cfg (i + n)).st dst).parked) s ≤ parkIndex (((ρ.cfg i).st dst).parked) s ∧
      parkIndex (((ρ.cfg (i + n)).st dst).parked) s <
        (((ρ.cfg (i + n)).st dst).parked).length := by
  induction n with
  | zero =>
    simp only [Nat.add_zero]
    exact And.intro (Nat.le_refl _) hin
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hstay t h1 (Nat.le_trans h2 (Nat.le_succ _)))
      (fun t h1 h2 => halive t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.1.2.2
    obtain ⟨k0, hk0⟩ := hstay (i + n) (Nat.le_add_right i n) (by omega)
    obtain ⟨k1, hk1⟩ := hstay (i + n + 1) (by omega) (by omega)
    have hstep := step_index I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) (ρ.valid (i + n))
      hO s dst c k0 k1 hk0 hk1
      (halive (i + n) (Nat.le_add_right i n) (by omega))
      (halive (i + n + 1) (by omega) (by omega))
      hprev.2
    exact And.intro (Nat.le_trans hstep.1 hprev.1) hstep.2

theorem next_bulk {I : Impl} {N : Nat} (ρ : Run I N) (hF : Fair ρ) (dst : InstId) (i : Nat)
    (hio : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) dst) :
    ∃ j, i ≤ j ∧ ρ.act j = .recvBulk dst ∧ ∀ t, i ≤ t → t < j → ρ.act t ≠ .recvBulk dst := by
  obtain ⟨j0, hj0, hact0⟩ := hF.bulk dst hio i
  have hscan := scanAct_spec ρ.act (.recvBulk dst) (j0 - i) i
    ⟨j0 - i, Nat.le_refl _, by simpa [Nat.add_sub_of_le hj0] using hact0⟩
  exact ⟨scanAct ρ.act (.recvBulk dst) (j0 - i) i, hscan.1, hscan.2⟩

/-- A blocking send that stays queued is removed by bulk receives.
`n` bounds the waiter's index. Each receive of the live receiver moves that
index strictly closer to the head, and the receive that finds it at the head
clears the wait. -/
theorem queued_forever_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (s dst : InstId) (n i : Nat)
    (hstay : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst false k)
    (halive : ∀ t, i ≤ t → ((ρ.cfg t).st dst).life = .alive)
    (hin : parkIndex (((ρ.cfg i).st dst).parked) s ≤ n)
    (hlt : parkIndex (((ρ.cfg i).st dst).parked) s < (((ρ.cfg i).st dst).parked).length)
    (hio : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) dst) : False := by
  induction n generalizing i with
  | zero =>
    have hzero : parkIndex (((ρ.cfg i).st dst).parked) s = 0 := by omega
    obtain ⟨j, hj, hact, _⟩ := next_bulk ρ hF dst i hio
    have hmono := index_mono I hL hG ρ s dst false i (j - i)
      (fun t h1 h2 => hstay t h1)
      (fun t h1 h2 => halive t h1) (by omega)
    have hat : parkIndex (((ρ.cfg j).st dst).parked) s = 0 := by
      have hle := hmono.1
      have : i + (j - i) = j := Nat.add_sub_of_le hj
      simp [this] at hle
      omega
    have hlen : 0 < (((ρ.cfg j).st dst).parked).length := by
      have := hmono.2
      simp [Nat.add_sub_of_le hj] at this
      omega
    obtain ⟨p, ps, hp, hs⟩ := index_zero_head _ s hat hlen
    obtain ⟨k, hk⟩ := hstay j hj
    have hne : s ≠ dst := by
      intro heq
      obtain ⟨k0, hk0⟩ := hstay i (Nat.le_refl _)
      have hrecv : receiveBulk I (ρ.cfg j) dst = some (ρ.cfg (j + 1)) := by
        have hv := ρ.valid j
        simp [hact] at hv
        exact hv
      unfold receiveBulk at hrecv
      by_cases hready : ((ρ.cfg j).st dst).life ≠ .alive ∨ ((ρ.cfg j).st dst).phase ≠ .idle
      · simp [hready] at hrecv
      · have hidle : ((ρ.cfg j).st dst).phase = .idle := by
          by_cases hpI : ((ρ.cfg j).st dst).phase = .idle
          · exact hpI
          · exact False.elim (hready (Or.inr hpI))
        rw [← heq] at hidle
        simp [hk] at hidle
    have hun := bulk_head_unblocks I (ρ.cfg j) (ρ.cfg (j + 1)) dst
      (by simpa [apply, hact] using ρ.valid j) p ps hp s hs.symm hne k hk
    obtain ⟨k', hk'⟩ := hstay (j + 1) (Nat.le_succ_of_le hj)
    have hstill : waitKind ((ρ.cfg (j + 1)).st s) = some (.blockingSend dst) := by simp [waitKind, hk']
    exact hun hstill
  | succ n ih =>
    obtain ⟨j, hj, hact, hfirst⟩ := next_bulk ρ hF dst i hio
    have hmono := index_mono I hL hG ρ s dst false i (j - i)
      (fun t h1 _ => hstay t h1) (fun t h1 _ => halive t h1) (by omega)
    have hatj : parkIndex (((ρ.cfg j).st dst).parked) s ≤ n + 1 := by
      have hle := hmono.1
      simp [Nat.add_sub_of_le hj] at hle
      exact Nat.le_trans hle hin
    have hlenj : parkIndex (((ρ.cfg j).st dst).parked) s < (((ρ.cfg j).st dst).parked).length := by
      have hltj := hmono.2
      simp [Nat.add_sub_of_le hj] at hltj
      exact hltj
    by_cases hzero : parkIndex (((ρ.cfg j).st dst).parked) s = 0
    · have hlenpos : 0 < (((ρ.cfg j).st dst).parked).length := by omega
      obtain ⟨p, ps, hp, hs⟩ := index_zero_head _ s hzero hlenpos
      obtain ⟨k, hk⟩ := hstay j hj
      have hrecv : receiveBulk I (ρ.cfg j) dst = some (ρ.cfg (j + 1)) := by
        simpa [apply, hact] using ρ.valid j
      have hne : s ≠ dst := by
        intro heq
        unfold receiveBulk at hrecv
        by_cases hready : ((ρ.cfg j).st dst).life ≠ .alive ∨ ((ρ.cfg j).st dst).phase ≠ .idle
        · simp [hready] at hrecv
        · have hidle : ((ρ.cfg j).st dst).phase = .idle := by
            by_cases hpI : ((ρ.cfg j).st dst).phase = .idle
            · exact hpI
            · exact False.elim (hready (Or.inr hpI))
          rw [← heq] at hidle
          simp [hk] at hidle
      have hun := bulk_head_unblocks I (ρ.cfg j) (ρ.cfg (j + 1)) dst hrecv p ps hp s hs.symm hne k hk
      obtain ⟨k', hk'⟩ := hstay (j + 1) (Nat.le_succ_of_le hj)
      exact hun (by simp [waitKind, hk'])
    · have hpos : 0 < parkIndex (((ρ.cfg j).st dst).parked) s := Nat.pos_of_ne_zero hzero
      cases hp : ((ρ.cfg j).st dst).parked with
      | nil => simp [parkIndex, hp] at hlenj
      | cons p ps =>
        have hsnd : p.sender ≠ s := by
          intro heq
          have h0 := parkIndex_head p ps s heq
          rw [hp] at hzero
          exact hzero h0
        rw [hp] at hlenj hatj
        have hrec := recv_closer I (ρ.cfg j) (ρ.cfg (j + 1)) dst
          (by simpa [apply, hact] using ρ.valid j) p ps hp s hsnd (by omega)
        have hnext : parkIndex (((ρ.cfg (j + 1)).st dst).parked) s ≤ n := by
          have := hrec.1
          omega
        have hltn : parkIndex (((ρ.cfg (j + 1)).st dst).parked) s <
            (((ρ.cfg (j + 1)).st dst).parked).length := hrec.2
        exact ih (j + 1)
          (fun t ht => hstay t (Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) ht)))
          (fun t ht => halive t (Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) ht)))
          hnext hltn

/-- A parked wait, send or call, does not stay parked once the receiver is idle
with mail infinitely often. For a call this is admission: the phase cannot
remain `.parked dst true`. -/
theorem parked_forever_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (s dst : InstId) (c : Bool) (n i : Nat)
    (hstay : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst c k)
    (halive : ∀ t, i ≤ t → ((ρ.cfg t).st dst).life = .alive)
    (hin : parkIndex (((ρ.cfg i).st dst).parked) s ≤ n)
    (hlt : parkIndex (((ρ.cfg i).st dst).parked) s < (((ρ.cfg i).st dst).parked).length)
    (hio : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) dst) : False := by
  induction n generalizing i with
  | zero =>
    have hzero : parkIndex (((ρ.cfg i).st dst).parked) s = 0 := by omega
    obtain ⟨j, hj, hact, _⟩ := next_bulk ρ hF dst i hio
    have hmono := index_mono I hL hG ρ s dst c i (j - i)
      (fun t h1 _ => hstay t h1) (fun t h1 _ => halive t h1) (by omega)
    have hat : parkIndex (((ρ.cfg j).st dst).parked) s = 0 := by
      have hle := hmono.1
      simp [Nat.add_sub_of_le hj] at hle
      omega
    have hlen : 0 < (((ρ.cfg j).st dst).parked).length := by
      have := hmono.2
      simp [Nat.add_sub_of_le hj] at this
      omega
    obtain ⟨p, ps, hp, hs⟩ := index_zero_head _ s hat hlen
    obtain ⟨k, hk⟩ := hstay j hj
    have hrecv : receiveBulk I (ρ.cfg j) dst = some (ρ.cfg (j + 1)) := by
      simpa [apply, hact] using ρ.valid j
    have hne : s ≠ dst := by
      intro heq
      unfold receiveBulk at hrecv
      by_cases hready : ((ρ.cfg j).st dst).life ≠ .alive ∨ ((ρ.cfg j).st dst).phase ≠ .idle
      · simp [hready] at hrecv
      · have hidle : ((ρ.cfg j).st dst).phase = .idle := by
          by_cases hpI : ((ρ.cfg j).st dst).phase = .idle
          · exact hpI
          · exact False.elim (hready (Or.inr hpI))
        rw [← heq] at hidle
        simp [hk] at hidle
    have hleft := bulk_head_leaves I (ρ.cfg j) (ρ.cfg (j + 1)) dst hrecv p ps hp s hs.symm hne c k hk
    obtain ⟨k', hk'⟩ := hstay (j + 1) (Nat.le_succ_of_le hj)
    exact hleft dst c k' hk'
  | succ n ih =>
    obtain ⟨j, hj, hact, _⟩ := next_bulk ρ hF dst i hio
    have hmono := index_mono I hL hG ρ s dst c i (j - i)
      (fun t h1 _ => hstay t h1) (fun t h1 _ => halive t h1) (by omega)
    have hatj : parkIndex (((ρ.cfg j).st dst).parked) s ≤ n + 1 := by
      have hle := hmono.1
      simp [Nat.add_sub_of_le hj] at hle
      exact Nat.le_trans hle hin
    have hlenj : parkIndex (((ρ.cfg j).st dst).parked) s < (((ρ.cfg j).st dst).parked).length := by
      have hltj := hmono.2
      simp [Nat.add_sub_of_le hj] at hltj
      exact hltj
    by_cases hzero : parkIndex (((ρ.cfg j).st dst).parked) s = 0
    · have hlenpos : 0 < (((ρ.cfg j).st dst).parked).length := by omega
      obtain ⟨p, ps, hp, hs⟩ := index_zero_head _ s hzero hlenpos
      obtain ⟨k, hk⟩ := hstay j hj
      have hrecv : receiveBulk I (ρ.cfg j) dst = some (ρ.cfg (j + 1)) := by
        simpa [apply, hact] using ρ.valid j
      have hne : s ≠ dst := by
        intro heq
        unfold receiveBulk at hrecv
        by_cases hready : ((ρ.cfg j).st dst).life ≠ .alive ∨ ((ρ.cfg j).st dst).phase ≠ .idle
        · simp [hready] at hrecv
        · have hidle : ((ρ.cfg j).st dst).phase = .idle := by
            by_cases hpI : ((ρ.cfg j).st dst).phase = .idle
            · exact hpI
            · exact False.elim (hready (Or.inr hpI))
          rw [← heq] at hidle
          simp [hk] at hidle
      have hleft := bulk_head_leaves I (ρ.cfg j) (ρ.cfg (j + 1)) dst hrecv p ps hp s hs.symm hne c k hk
      obtain ⟨k', hk'⟩ := hstay (j + 1) (Nat.le_succ_of_le hj)
      exact hleft dst c k' hk'
    · have hpos : 0 < parkIndex (((ρ.cfg j).st dst).parked) s := Nat.pos_of_ne_zero hzero
      cases hp : ((ρ.cfg j).st dst).parked with
      | nil => simp [parkIndex, hp] at hlenj
      | cons p ps =>
        have hsnd : p.sender ≠ s := by
          intro heq
          have h0 := parkIndex_head p ps s heq
          rw [hp] at hzero
          exact hzero h0
        rw [hp] at hlenj hatj
        have hrec := recv_closer I (ρ.cfg j) (ρ.cfg (j + 1)) dst
          (by simpa [apply, hact] using ρ.valid j) p ps hp s hsnd (by omega)
        have hnext : parkIndex (((ρ.cfg (j + 1)).st dst).parked) s ≤ n := by
          have := hrec.1
          omega
        have hltn : parkIndex (((ρ.cfg (j + 1)).st dst).parked) s <
            (((ρ.cfg (j + 1)).st dst).parked).length := hrec.2
        exact ih (j + 1)
          (fun t ht => hstay t (Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) ht)))
          (fun t ht => halive t (Nat.le_trans hj (Nat.le_trans (Nat.le_succ j) ht)))
          hnext hltn

theorem terminate_unblocks (I : Impl) (w : World) (id : InstId) (t : Template) (tail : List Eff)
    (toState : String) (replyTo : Option InstId) (s : InstId) (k : Cont) (hM : MailInv w)
    (ht : templateOf I.desc (tname id) = some t)
    (hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true)
    (hph : (w.st s).phase = .parked id false k) (hne : s ≠ id) :
    waitKind ((execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩).st s) ≠
      some (.blockingSend id) := by
  obtain ⟨p, hp, hs, hc⟩ := hM.bwd s id false k hph
  let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
    (tname id) (w.st id).parked
  have hphb : (base.st s).phase = .parked id false k := by
    simp [base, readCells_st, phase_refund, phase_refundP, hph]
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hphs : ((setActor base id dead).st s).phase = .parked id false k := by
    simp [setActor, hne, hphb]
  have hrel := release_resumes_send (setActor base id dead) id (w.st id).parked s k
    ⟨p, hp, hs, hc⟩ hne hphs
  have hstep : execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ =
      releaseParked (setActor base id dead) id (w.st id).parked := by
    simp [execRun, ht, hkill, base, dead]
  rw [hstep]
  cases hk : k.rest with
  | nil =>
    simp [proceed, hk] at hrel
    unfold waitKind
    rw [hrel]
    simp
  | cons _ _ =>
    simp [proceed, hk] at hrel
    unfold waitKind
    rw [hrel]
    simp

theorem parkIndex_of_mem (ps : List Parked) (s : InstId) (h : ∃ p, p ∈ ps ∧ p.sender = s) :
    parkIndex ps s < ps.length := by
  induction ps with
  | nil =>
    obtain ⟨_, hp, _⟩ := h
    cases hp
  | cons p ps ih =>
    obtain ⟨q, hq, hqs⟩ := h
    by_cases hs : p.sender = s
    · simp [parkIndex, hs, List.length]
    · have hb : (p.sender == s) = false := by simpa [beq_iff_eq] using hs
      cases hq with
      | head => exact absurd hqs hs
      | tail _ ht =>
        have hlt := ih ⟨q, ht, hqs⟩
        simp [parkIndex, hb, List.length]
        omega

theorem blocking_parked (a : Actor) (dst : InstId) (h : waitKind a = some (.blockingSend dst)) :
    ∃ k, a.phase = .parked dst false k := by
  cases hph : a.phase <;> simp [waitKind, hph] at h
  case parked dst' c k =>
    cases c <;> simp at h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨k, rfl⟩

theorem call_parked_or_await (a : Actor) (dst : InstId) (h : waitKind a = some (.callReply dst)) :
    (∃ k, a.phase = .parked dst true k) ∨ (∃ k, a.phase = .awaitReply dst k) := by
  cases hph : a.phase <;> simp [waitKind, hph] at h
  case parked dst' c k =>
    cases c <;> simp at h
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨k, rfl⟩
  case awaitReply dst' k =>
    cases h
    exact Or.inr ⟨k, rfl⟩

def rankAt (hs : List (Node × Nat)) (w : World) (id : InstId) : Nat :=
  heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node)

theorem finish_life (w w' : World) (id i : InstId) (h : finishWait w id = some w')
    (hl : (w.st i).life = .alive) : (w'.st i).life = .alive := by
  unfold finishWait at h
  split at h
  · cases h
    by_cases hi : i = id
    · rw [hi] at hl ⊢
      simpa [setActor, proceed_life] using hl
    · simpa [setActor, hi] using hl
  · cases h
    by_cases hi : i = id
    · rw [hi] at hl ⊢
      simpa [setActor, proceed_life] using hl
    · simpa [setActor, hi] using hl
  · cases h

/-- Releasing a parked list resumes senders and never rewrites a life. -/
theorem release_life_all (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).life = (w.st i).life := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hstep :
          ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i).life =
            (w.st i).life := by
        by_cases hi : i = p.sender
        · rw [hi]
          simp [setActor, resume_life]
        · simp [setActor, hi]
      exact (ih _).trans hstep

/-- A reply proceeds the sender and, when the caller is waiting on them, the caller.
Neither write changes a life. -/
theorem reply_life (w : World) (sender : InstId) (k : Cont) (i : InstId) :
    ((performReply w sender k).st i).life = (w.st i).life := by
  unfold performReply
  cases hr : k.replyTo with
  | none =>
    by_cases hi : i = sender
    · rw [hi]
      simp [setActor, proceed_life]
    · simp [setActor, hi]
  | some caller =>
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = sender
      · by_cases hi : i = sender
        · rw [hi]
          by_cases hsc : sender = caller
          · simp [setActor, proceed_life, hph, hd, hsc]
          · simp [setActor, proceed_life, hph, hd, hsc]
        · by_cases hc : i = caller
          · rw [hc]
            have hflip : ¬caller = sender := fun h => hi (hc.trans h)
            simp [setActor, proceed_life, hph, hd, hflip]
          · simp [setActor, hi, hc, hph, hd]
      · by_cases hi : i = sender
        · rw [hi]
          simp [setActor, proceed_life, hph, hd]
        · simp [setActor, hi, hph, hd]
    | idle =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]
    | run _ =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]
    | parked _ _ _ =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]
    | awaitEffect _ =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]
    | awaitPeer _ =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]
    | crashed =>
      by_cases hi : i = sender
      · rw [hi]
        simp [setActor, proceed_life, hph]
      · simp [setActor, hi, hph]

/-- Delivering a message reads cells and installs a phase. It does not change a life. -/
theorem deliver_keeps_life (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (i : InstId) (h : deliver I w id a m = some (w1, a1)) :
    a1.life = a.life ∧ (w1.st i).life = (w.st i).life := by
  unfold deliver at h
  have hst := readCells_st I.desc w id i
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, congrArg (fun a => a.life) hst⟩
    · next tr =>
      split at h
      · cases h
      · split at h
        · cases h
          exact ⟨rfl, congrArg (fun a => a.life) hst⟩
        · cases h
          exact ⟨rfl, congrArg (fun a => a.life) hst⟩

/-- An `exec` of someone else does not change `i`'s life. -/
theorem exec_other_life (I : Impl) (w : World) (id i : InstId) (k : Cont) (hne : i ≠ id) :
    ((execRun I w id (w.st id) k).st i).life = (w.st i).life := by
  cases hk : k.rest with
  | nil => simp [execRun, hk, setActor, hne]
  | cons eff tail =>
    cases eff with
    | send dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => simp [hr, setActor, hne, proceed_life]
      | some dstId =>
        simp [hr]
        exact enqueue_life w I.desc id dstId _ false _ i
    | trySend dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => simp [hr, setActor, hne, proceed_life]
      | some dstId =>
        simp [hr]
        split
        · by_cases hid : dstId = id
          · simp [setActor, hid, hne, chargeSender, bumpToken, proceed_life]
          · by_cases hi : i = dstId
            · simp [setActor, hi, hid, chargeSender, bumpToken, proceed_life]
            · simp [setActor, hi, hne, chargeSender, bumpToken, proceed_life]
        · simp [setActor, hne, proceed_life]
    | call dst label hint =>
      simp [execRun, hk]
      cases hr : route w I.desc dst hint with
      | none => simp [hr, setActor, hne, proceed_life]
      | some dstId =>
        simp [hr]
        exact enqueue_life w I.desc id dstId _ true _ i
    | reply =>
      simp [execRun, hk]
      exact reply_life w id k i
    | selfSchedule label =>
      simp [execRun, hk]
      split
      · simp [setActor, hne, proceed_life]
      · split
        · simp [setActor, hne, proceed_life]
        · simp [setActor, hne]
    | cell dst label value =>
      simp only [execRun, hk]
      split
      · simp [setCell, setActor, hne, proceed_life]
      · rw [wakeReaders]
        rw [wakes_life _ _ _ dst label id i]
        simp [setCell, setActor, hne, proceed_life]
    | internal => simp [execRun, hk, setActor, hne]
    | peer => simp [execRun, hk, setActor, hne]
    | terminate =>
      cases ht : templateOf I.desc (tname id) with
      | none => simp [execRun, hk, ht]
      | some t =>
        by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
        · let base :=
            refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
              (w.st id).parked
          let dead : Actor :=
            { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
          have hbase : (base.st i).life = (w.st i).life := by
            have hread := readCells_st I.desc w id i
            have href := (refund_life (readCells I.desc w id) (tname id) (w.st id).box i).1
            have hrefp :=
              (refundP_life (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                (w.st id).parked i).1
            simp [base, hread, href, hrefp]
          have hset : ((setActor base id dead).st i).life = (w.st i).life := by
            simp [setActor, hne, hbase]
          have hstep :
              execRun I w id (w.st id) k =
                releaseParked (setActor base id dead) id (w.st id).parked := by
            simp [execRun, hk, ht, hkill, base, dead]
          rw [hstep]
          exact (release_life_all (setActor base id dead) id (w.st id).parked i).trans hset
        · rw [show execRun I w id (w.st id) k = w by simp [execRun, hk, ht, hkill]]

theorem bulk_life (I : Impl) (w w' : World) (id i : InstId) (h : receiveBulk I w id = some w') :
    (w'.st i).life = (w.st i).life := by
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
          have hkeep := deliver_keeps_life I w id _ p.msg w1 a1 i hdel
          have hset : ((setActor w1 id a1).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]
              simpa [setActor] using hkeep.1
            · simpa [setActor, hi] using hkeep.2
          have hcred := (credit_life (setActor w1 id a1) (tname id) p.msg.sender i).1
          by_cases hs : i = p.sender
          · rw [hs] at hcred hset ⊢
            simp only [setActor, ite_true, resume_life]
            exact hcred.trans hset
          · simp only [setActor, hs]
            exact hcred.trans hset
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hkeep := deliver_keeps_life I w id _ m w1 a1 i hdel
          have hset : ((setActor w1 id a1).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]
              simpa [setActor] using hkeep.1
            · simpa [setActor, hi] using hkeep.2
          exact ((credit_life (setActor w1 id a1) (tname id) m.sender i).1).trans hset
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hkeep := deliver_keeps_life I w id _ m w1 a1 i hdel
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hset : ((setActor w1 id admitted).st i).life = (w.st i).life := by
            by_cases hi : i = id
            · rw [hi]
              simpa [setActor, admitted] using hkeep.1
            · simpa [setActor, hi] using hkeep.2
          have hcred := (credit_life (setActor w1 id admitted) (tname id) m.sender i).1
          by_cases hs : i = p.sender
          · rw [hs] at hcred hset ⊢
            simp only [setActor, ite_true, resume_life]
            exact hcred.trans hset
          · simp only [setActor, hs]
            exact hcred.trans hset

theorem prio_life (I : Impl) (w w' : World) (id i : InstId) (h : receivePrio I w id = some w') :
    (w'.st i).life = (w.st i).life := by
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
    · simp [hp, hready] at h
    · simp [hp, hready] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hkeep := deliver_keeps_life I w id _ m w1 a1 i hdel
        by_cases hi : i = id
        · rw [hi]
          simpa [setActor] using hkeep.1
        · simpa [setActor, hi] using hkeep.2

theorem spawn_life (I : Impl) (w : World) (template : String) (w' : World) (i : InstId)
    (h : spawn I w template = some w') (hl : (w.st i).life = .alive) :
    (w'.st i).life = .alive := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · cases h
      simp only [readCells_st]
      by_cases hi : i = InstId.peer template (w.nextIx template)
      · simp [setActor, hi, withTokens]
      · simpa [setActor, hi] using hl
    · cases h

/-- A life leaves `alive` only when that actor executes a killing `terminate`. -/
theorem only_terminate_kills (I : Impl) (a : Action) (w w' : World) (i : InstId)
    (h : apply I a w = some w') (hl : (w.st i).life = .alive) (hdead : (w'.st i).life ≠ .alive) :
    ∃ tail toState replyTo t,
      a = .exec i ∧ (w.st i).phase = .run ⟨.terminate :: tail, toState, replyTo⟩ ∧
        templateOf I.desc (tname i) = some t ∧
        (t.terminable && !hasParkedCall (w.st i).parked) = true := by
  cases a with
  | recvBulk id =>
    exact absurd (bulk_life I w w' id i (by simpa [apply] using h) ▸ hl) hdead
  | recvPrio id =>
    exact absurd (prio_life I w w' id i (by simpa [apply] using h) ▸ hl) hdead
  | finish id =>
    exact absurd (finish_life w w' id i (by simpa [apply] using h) hl) hdead
  | spawn template =>
    exact absurd (spawn_life I w template w' i (by simpa [apply] using h) hl) hdead
  | exec id =>
    unfold apply execHead at h
    by_cases hlid : (w.st id).life = .alive
    · simp [hlid] at h
      cases hph : (w.st id).phase with
      | run k =>
        simp [hph] at h
        cases h
        by_cases hme : i = id
        · cases hk : k.rest with
          | nil =>
            exfalso
            rw [hme] at hdead
            simp [execRun, hk, setActor, hlid] at hdead
          | cons e tail =>
            cases e with
            | terminate =>
              cases htpl : templateOf I.desc (tname id) with
              | none =>
                exfalso
                rw [hme] at hdead
                simp [execRun, hk, htpl, hlid] at hdead
              | some t =>
                by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
                · have hk' : k = ⟨.terminate :: tail, k.toState, k.replyTo⟩ := by
                    cases k with
                    | mk rest toState replyTo =>
                      have : rest = .terminate :: tail := hk
                      subst this
                      rfl
                  have hphase : (w.st i).phase = .run ⟨.terminate :: tail, k.toState, k.replyTo⟩ := by
                    rw [hk'] at hph
                    rw [hme]
                    exact hph
                  have htmpl : templateOf I.desc (tname i) = some t := by
                    simpa [hme] using htpl
                  have hflag : (t.terminable && !hasParkedCall (w.st i).parked) = true := by
                    simpa [hme] using hkill
                  exact ⟨tail, k.toState, k.replyTo, t, by rw [hme], hphase, htmpl, hflag⟩
                · exfalso
                  rw [hme] at hdead
                  have hfalse : (t.terminable && !hasParkedCall (w.st id).parked) = false := by
                    cases hb : t.terminable && !hasParkedCall (w.st id).parked <;> simp_all
                  simp [execRun, hk, htpl, hfalse, hlid] at hdead
            | send dst label hint =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk] at hdead
              cases hr : route w I.desc dst hint with
              | none => simp [hr, setActor, proceed_life, hlid] at hdead
              | some dstId =>
                simp [hr] at hdead
                have heq := enqueue_life w I.desc id dstId
                  ({ label := label, sender := id, callFrom := none } : Msg) false (afterHead k) id
                simp [heq, hlid] at hdead
            | trySend dst label hint =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk] at hdead
              cases hr : route w I.desc dst hint with
              | none => simp [hr, setActor, proceed_life, hlid] at hdead
              | some dstId =>
                simp [hr] at hdead
                split at hdead
                · by_cases hid : id = dstId
                  · simp [setActor, chargeSender, bumpToken, proceed_life, hid] at hdead
                    rw [hid] at hlid
                    exact hdead hlid
                  · have hflip : ¬dstId = id := fun h => hid h.symm
                    simp [setActor, chargeSender, bumpToken, proceed_life, hid, hflip, hlid] at hdead
                · simp [setActor, proceed_life, hlid] at hdead
            | call dst label hint =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk] at hdead
              cases hr : route w I.desc dst hint with
              | none => simp [hr, setActor, proceed_life, hlid] at hdead
              | some dstId =>
                simp [hr] at hdead
                have heq := enqueue_life w I.desc id dstId
                  ({ label := label, sender := id, callFrom := some id } : Msg) true (afterHead k) id
                simp [heq, hlid] at hdead
            | reply =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk, reply_life, hlid] at hdead
            | selfSchedule label =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk] at hdead
              split at hdead
              · simp [setActor, proceed_life, hlid] at hdead
              · split at hdead
                · simp [setActor, proceed_life, hlid] at hdead
                · simp [setActor, hlid] at hdead
            | cell dst label value =>
              exfalso
              rw [hme] at hdead
              simp only [execRun, hk] at hdead
              split at hdead
              · simp [setCell, setActor, proceed_life, hlid] at hdead
              · rw [wakeReaders] at hdead
                rw [wakes_life (readersOf _ _) I.desc _ dst label id id] at hdead
                simp [setCell, setActor, proceed_life, hlid] at hdead
            | internal =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk, setActor, hlid] at hdead
            | peer =>
              exfalso
              rw [hme] at hdead
              simp [execRun, hk, setActor, hlid] at hdead
        · have hrun := exec_other_life I w id i k (fun h => hme h)
          exact absurd (hrun.trans hl) hdead
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlid] at h

/-- While a blocking send stays parked, its receiver cannot die: the killing step would resume it. -/
theorem receiver_stays (I : Impl) (hL : LocalOk I) (N : Nat) (w : World) (hR : Reachable I N w)
    (a : Action) (w' : World) (s dst : InstId) (k k' : Cont)
    (h : apply I a w = some w') (hph : (w.st s).phase = .parked dst false k)
    (hph' : (w'.st s).phase = .parked dst false k') (halive : (w.st dst).life = .alive) :
    (w'.st dst).life = .alive := by
  cases Classical.em ((w'.st dst).life = .alive) with
  | inl h' => exact h'
  | inr hdead =>
    have hkill := only_terminate_kills I a w w' dst h halive hdead
    obtain ⟨tail, toState, replyTo, t, hact, hrun, ht, hflag⟩ := hkill
    have hM := (inv_reachable I N w hL hR).2.1
    have hstep : w' = execRun I w dst (w.st dst) ⟨.terminate :: tail, toState, replyTo⟩ := by
      simp [apply, hact, execHead, halive, hrun] at h
      exact h.symm
    by_cases hne : s = dst
    · let base :=
        refundParked (refundMsgs (readCells I.desc w dst) (tname dst) (w.st dst).box) (tname dst)
          (w.st dst).parked
      let dead : Actor :=
        { base.st dst with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
      have hrunEq :
          execRun I w dst (w.st dst) ⟨.terminate :: tail, toState, replyTo⟩ =
            releaseParked (setActor base dst dead) dst (w.st dst).parked := by
        simp [execRun, ht, hflag, base, dead]
      have hidle : ((setActor base dst dead).st dst).phase = .idle := by simp [setActor, dead]
      have hn : ∀ d c ck, ((setActor base dst dead).st dst).phase ≠ .parked d c ck := by
        intro d c ck hbad
        simp [hidle] at hbad
      have hstay :=
        (release_keeps_nonparked (setActor base dst dead) dst (w.st dst).parked dst hn).1
      rw [hne] at hph'
      rw [hstep, hrunEq, hstay, hidle] at hph'
      cases hph'
    · have hclear :=
        terminate_unblocks I w dst t tail toState replyTo s k hM ht hflag hph hne
      have hnow :
          waitKind ((execRun I w dst (w.st dst) ⟨.terminate :: tail, toState, replyTo⟩).st s) =
            some (.blockingSend dst) := by
        have hphE := hph'
        rw [hstep] at hphE
        simp [waitKind, hphE]
      exact False.elim (hclear hnow)

theorem release_misses (w : World) (id : InstId) (ps : List Parked) (s : InstId)
    (h : ∀ p, p ∈ ps → p.sender ≠ s) : ((releaseParked w id ps).st s) = w.st s := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w (fun q hq => h q (List.mem_cons_of_mem p hq))
    · rw [if_neg hskip]
      have hne : s ≠ p.sender := fun heq => h p List.mem_cons_self heq.symm
      have hstep : (setActor w p.sender (resumeSender (w.st p.sender) false id)).st s = w.st s := by
        simp [setActor, hne]
      exact (ih _ (fun q hq => h q (List.mem_cons_of_mem p hq))).trans hstep

theorem resume_proceed_phase (a : Actor) (dst : InstId) (k : Cont)
    (h : a.phase = .parked dst false k) :
    (resumeSender a false dst).phase = (proceed a k).phase := by
  simp [resumeSender, h]

theorem proceed_phase_actor (a b : Actor) (k : Cont) :
    (proceed a k).phase = (proceed b k).phase := by
  cases hk : k.rest <;> simp [proceed, hk]

/-- Resuming the parked head of a blocking send runs its continuation. -/
theorem bulk_send_proceed (I : Impl) (w w' : World) (id : InstId) (h : receiveBulk I w id = some w')
    (p : Parked) (ps : List Parked) (hp : (w.st id).parked = p :: ps) (s : InstId)
    (hs : s = p.sender) (hne : s ≠ id) (k : Cont)
    (hph : (w.st s).phase = .parked id false k) (hc : p.isCall = false) :
    (w'.st s).phase = (proceed (w.st s) k).phase := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        have hst := deliver_st I w id _ p.msg w1 a1 s hdel
        have hpre := install_sender_phase w w1 id a1 p.msg.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self]
        rw [hc]
        exact (resume_proceed_phase _ id k (hpre.trans hph)).trans
          (proceed_phase_actor _ (w.st p.sender) k)
    | cons m ms =>
      simp [hbox, hp] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hst := deliver_st I w id _ m w1 a1 s hdel
        have hpre := install_sender_phase w w1 id admitted m.sender s (by simpa [hs] using hne) hst
        rw [hs] at hpre hph ⊢
        simp only [setActor_self, admitted]
        rw [hc]
        exact (resume_proceed_phase _ id k (hpre.trans hph)).trans
          (proceed_phase_actor _ (w.st p.sender) k)

/-- One step either leaves a blocking send parked on the same continuation, or runs it. -/
theorem blocking_next (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : (w.st s).phase = .parked dst false k) :
    (w'.st s).phase = .parked dst false k ∨ (w'.st s).phase = (proceed (w.st s) k).phase := by
  cases a with
  | finish id =>
    simp only [apply] at h
    unfold finishWait at h
    cases hphF : (w.st id).phase with
    | awaitEffect kF =>
      simp [hphF] at h
      cases h
      have hs : s ≠ id := by
        intro heq
        rw [heq] at hph
        rw [hph] at hphF
        cases hphF
      exact Or.inl (by simpa [setActor, hs] using hph)
    | awaitPeer kF =>
      simp [hphF] at h
      cases h
      have hs : s ≠ id := by
        intro heq
        rw [heq] at hph
        rw [hph] at hphF
        cases hphF
      exact Or.inl (by simpa [setActor, hs] using hph)
    | idle => simp [hphF] at h
    | run _ => simp [hphF] at h
    | parked _ _ _ => simp [hphF] at h
    | awaitReply _ _ => simp [hphF] at h
    | crashed => simp [hphF] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        have hslot := hO template (w.nextIx template) (Nat.le_refl _)
        have hne : s ≠ InstId.peer template (w.nextIx template) := by
          intro heq
          rw [heq] at hph
          rw [hslot.2.1] at hph
          cases hph
        simp only [readCells_st, setActor, hne]
        exact Or.inl hph
      · cases h
  | recvPrio id =>
    simp only [apply] at h
    have hsne : s ≠ id := by
      intro heq
      rw [heq] at hph
      cases hp : (w.st id).prio with
      | nil => simp [receivePrio, hp] at h
      | cons _ _ => simp [receivePrio, hp, hph] at h
    unfold receivePrio at h
    cases hp : (w.st id).prio with
    | nil => simp [hp] at h
    | cons m ms =>
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hp, hready] at h
      · simp [hp, hready] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          exact Or.inl (by simpa [setActor, hsne, hst] using hph)
  | recvBulk id =>
    simp only [apply] at h
    have hsne : s ≠ id := by
      intro heq
      rw [heq] at hph
      unfold receiveBulk at h
      simp [hph] at h
    by_cases hid : id = dst
    · obtain ⟨p0, hp0, hs0, hc0⟩ := hM.bwd s dst false k hph
      cases hpk : (w.st dst).parked with
      | nil => exact absurd hp0 (by simp [hpk])
      | cons p ps =>
        by_cases hhead : s = p.sender
        · have hc : p.isCall = false := by
            have hmem : p ∈ (w.st dst).parked := by simp [hpk]
            exact (hM.uniq dst dst p0 p hp0 hmem (hs0.trans hhead)).2 ▸ hc0
          have hrecv : receiveBulk I w dst = some w' := by
            rw [hid] at h
            exact h
          have hsd : s ≠ dst := fun hsd => hsne (hsd.trans hid.symm)
          exact Or.inr (bulk_send_proceed I w w' dst hrecv p ps hpk s hhead hsd k
            (by simpa [hid] using hph) hc)
        · unfold receiveBulk at h
          by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
          · simp [hready] at h
          · simp [hready] at h
            cases hbox : (w.st id).box with
            | nil =>
              simp [hbox] at h
              cases hpark : (w.st id).parked with
              | nil => simp [hpark] at h
              | cons q qs =>
                simp [hpark] at h
                split at h
                · cases h
                · next w1 a1 hdel =>
                  cases h
                  have hst := deliver_st I w id _ q.msg w1 a1 s hdel
                  have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
                    simpa [setActor, hsne, hst] using hph
                  have hcred := (credit_life (setActor w1 id a1) (tname id) q.msg.sender s).2.2.1
                  have hsender : s ≠ q.sender := by
                    have hsame : (w.st id).parked = (w.st dst).parked := by simp [hid]
                    rw [hsame, hpk] at hpark
                    cases hpark
                    exact hhead
                  simp only [setActor, hsender, ite_false]
                  exact Or.inl (hcred.trans (hset.trans hph))
            | cons m ms =>
              cases hpark : (w.st id).parked with
              | nil =>
                simp [hbox, hpark] at h
                split at h
                · cases h
                · next w1 a1 hdel =>
                  cases h
                  have hst := deliver_st I w id _ m w1 a1 s hdel
                  have hcred := (credit_life (setActor w1 id a1) (tname id) m.sender s).2.2.1
                  have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
                    simpa [setActor, hsne, hst] using hph
                  exact Or.inl (hcred.trans (hset.trans hph))
              | cons q qs =>
                simp [hbox, hpark] at h
                split at h
                · cases h
                · next w1 a1 hdel =>
                  cases h
                  have hst := deliver_st I w id _ m w1 a1 s hdel
                  let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
                  have hset : ((setActor w1 id admitted).st s).phase = (w.st s).phase := by
                    simpa [setActor, hsne, hst] using hph
                  have hcred := (credit_life (setActor w1 id admitted) (tname id) m.sender s).2.2.1
                  have hsender : s ≠ q.sender := by
                    have hsame : (w.st id).parked = (w.st dst).parked := by simp [hid]
                    rw [hsame, hpk] at hpark
                    cases hpark
                    exact hhead
                  simp only [setActor, hsender, ite_false]
                  exact Or.inl (hcred.trans (hset.trans hph))
    · unfold receiveBulk at h
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hready] at h
      · simp [hready] at h
        cases hbox : (w.st id).box with
        | nil =>
          cases hpark : (w.st id).parked with
          | nil => simp [hbox, hpark] at h
          | cons q qs =>
            simp [hbox, hpark] at h
            have hns : s ≠ q.sender := by
              intro heq
              obtain ⟨p0, hp0, hs0, _⟩ := hM.bwd s dst false k hph
              have hmemq : q ∈ (w.st id).parked := by simp [hpark]
              exact hid ((hM.uniq id dst q p0 hmemq hp0 (heq.symm.trans hs0.symm)).1)
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w id _ q.msg w1 a1 s hdel
              have hcred := (credit_life (setActor w1 id a1) (tname id) q.msg.sender s).2.2.1
              have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
                simpa [setActor, hsne, hst] using hph
              simp only [setActor, hns, ite_false]
              exact Or.inl (hcred.trans (hset.trans hph))
        | cons m ms =>
          cases hpark : (w.st id).parked with
          | nil =>
            simp [hbox, hpark] at h
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w id _ m w1 a1 s hdel
              have hcred := (credit_life (setActor w1 id a1) (tname id) m.sender s).2.2.1
              have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
                simpa [setActor, hsne, hst] using hph
              exact Or.inl (hcred.trans (hset.trans hph))
          | cons q qs =>
            simp [hbox, hpark] at h
            have hns : s ≠ q.sender := by
              intro heq
              obtain ⟨p0, hp0, hs0, _⟩ := hM.bwd s dst false k hph
              have hmemq : q ∈ (w.st id).parked := by simp [hpark]
              exact hid ((hM.uniq id dst q p0 hmemq hp0 (heq.symm.trans hs0.symm)).1)
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w id _ m w1 a1 s hdel
              let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
              have hcred := (credit_life (setActor w1 id admitted) (tname id) m.sender s).2.2.1
              have hset : ((setActor w1 id admitted).st s).phase = (w.st s).phase := by
                simpa [setActor, hsne, hst] using hph
              simp only [setActor, hns, ite_false]
              exact Or.inl (hcred.trans (hset.trans hph))
  | exec id =>
    simp only [apply] at h
    have hsne : s ≠ id := by
      intro heq
      rw [heq] at hph
      simp [execHead, hph] at h
    unfold execHead at h
    by_cases hlid : (w.st id).life = .alive
    · simp [hlid] at h
      cases hphE : (w.st id).phase with
      | run kE =>
        simp [hphE] at h
        cases h
        cases hk : kE.rest with
        | nil => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
        | cons e tail =>
          cases e with
          | send name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, proceed_life, hph])
            | some dstId =>
              simp [hr]
              exact Or.inl ((enqueue_phase_other w I.desc id dstId
                ({ label := label, sender := id, callFrom := none } : Msg) false (afterHead kE) s hsne).trans hph)
          | call name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, hph])
            | some dstId =>
              simp [hr]
              exact Or.inl ((enqueue_phase_other w I.desc id dstId
                ({ label := label, sender := id, callFrom := some id } : Msg) true (afterHead kE) s hsne).trans hph)
          | trySend name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, hph])
            | some dstId =>
              simp [hr]
              split
              · by_cases hd : s = dstId
                · have hid : ¬dstId = id := fun h => hsne (hd.trans h)
                  simp [setActor, hd, hid, chargeSender, bumpToken, hph]
                  have hph' := hph
                  rw [hd] at hph'
                  exact Or.inl hph'
                · exact Or.inl (by simp [setActor, hd, hsne, chargeSender, bumpToken, hph])
              · exact Or.inl (by simp [setActor, hsne, hph])
          | reply =>
            simp [execRun, hk]
            exact Or.inl ((reply_keeps_quiet w id s kE (fun d ck hbad => by simp [hph] at hbad) hsne).1.trans hph)
          | selfSchedule label =>
            simp [execRun, hk]
            split
            · exact Or.inl (by simp [setActor, hsne, hph])
            · split
              · exact Or.inl (by simp [setActor, hsne, hph])
              · exact Or.inl (by simp [setActor, hsne, hph])
          | cell name label value =>
            simp only [execRun, hk]
            split
            · exact Or.inl (by simp [setCell, setActor, hsne, hph])
            · rw [wakeReaders]
              exact Or.inl (by
                rw [wakes_phase (readersOf _ _) I.desc _ name label id s]
                simp [setCell, setActor, hsne, hph])
          | internal => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
          | peer => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
          | terminate =>
            cases ht : templateOf I.desc (tname id) with
            | none => exact Or.inl (by simp [execRun, hk, ht, hph])
            | some t =>
              by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
              · by_cases hdst : id = dst
                · have hmem : ∃ p, p ∈ (w.st id).parked ∧ p.sender = s ∧ p.isCall = false := by
                    rw [hdst]
                    exact hM.bwd s dst false k hph
                  let base :=
                    refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                      (w.st id).parked
                  let dead : Actor :=
                    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hphB : ((setActor base id dead).st s).phase = .parked id false k := by
                    have hread := readCells_st I.desc w id s
                    have href := (refund_life (readCells I.desc w id) (tname id) (w.st id).box s).2.2.1
                    have hrefp :=
                      (refundP_life (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                        (w.st id).parked s).2.2.1
                    have hchain : (base.st s).phase = (w.st s).phase := by simp [base, hread, href, hrefp]
                    have hphId : (w.st s).phase = .parked id false k := by simpa [hdst] using hph
                    simpa [setActor, hsne, hchain] using hphId
                  have hstep :
                      execRun I w id (w.st id) kE =
                        releaseParked (setActor base id dead) id (w.st id).parked := by
                    simp [execRun, hk, ht, hkill, base, dead]
                  have hrel := release_resumes_send (setActor base id dead) id (w.st id).parked s k hmem hsne hphB
                  rw [hstep]
                  exact Or.inr (hrel.trans (proceed_phase_actor _ (w.st s) k))
                · have habsent : ∀ p, p ∈ (w.st id).parked → p.sender ≠ s := by
                    intro p hp heq
                    obtain ⟨q, hq, hqs, _⟩ := hM.bwd s dst false k hph
                    exact hdst ((hM.uniq id dst p q hp hq (heq.trans hqs.symm)).1)
                  let base :=
                    refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                      (w.st id).parked
                  let dead : Actor :=
                    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hbase : (base.st s).phase = (w.st s).phase := by
                    have hread := readCells_st I.desc w id s
                    have href := (refund_life (readCells I.desc w id) (tname id) (w.st id).box s).2.2.1
                    have hrefp :=
                      (refundP_life (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                        (w.st id).parked s).2.2.1
                    simp [base, hread, href, hrefp]
                  have hset : ((setActor base id dead).st s).phase = (w.st s).phase := by
                    simp [setActor, hsne, hbase]
                  have hrel : ((releaseParked (setActor base id dead) id (w.st id).parked).st s).phase =
                      (w.st s).phase := by
                    have hskip := release_misses (setActor base id dead) id (w.st id).parked s habsent
                    exact (congrArg (fun a => a.phase) hskip).trans hset
                  have hstep :
                      execRun I w id (w.st id) kE =
                        releaseParked (setActor base id dead) id (w.st id).parked := by
                    simp [execRun, hk, ht, hkill, base, dead]
                  rw [hstep]
                  exact Or.inl (hrel.trans hph)
              · exact Or.inl (by simp [execRun, hk, ht, hkill, hph])
      | idle => simp [hphE] at h
      | parked _ _ _ => simp [hphE] at h
      | awaitReply _ _ => simp [hphE] at h
      | awaitEffect _ => simp [hphE] at h
      | awaitPeer _ => simp [hphE] at h
      | crashed => simp [hphE] at h
    · simp [hlid] at h

/-- Leaving a blocking send runs a strictly shorter continuation. -/
theorem blocking_fuel (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : (w.st s).phase = .parked dst false k)
    (hdiff : waitKind (w'.st s) ≠ some (.blockingSend dst)) :
    phaseFuel ((w'.st s).phase) < phaseFuel ((w.st s).phase) := by
  rcases blocking_next I a w w' s dst k hM hO h hph with hsame | hpro
  · exact absurd (by simp [waitKind, hsame]) hdiff
  · rw [hpro]
    have hle := proceed_fuel (w.st s) k
    have hold : phaseFuel ((w.st s).phase) = 2 * k.rest.length + 1 := by simp [phaseFuel, hph]
    rw [hold]
    omega

/-- A receiver stays alive for as long as the blocking send stays parked. -/
theorem alive_while_send (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (i : Nat)
    (hstay : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst false k)
    (halive : ((ρ.cfg i).st dst).life = .alive) :
    ∀ t, i ≤ t → ((ρ.cfg t).st dst).life = .alive := by
  suffices ∀ n, ((ρ.cfg (i + n)).st dst).life = .alive by
    intro t ht
    simpa [Nat.add_sub_of_le ht] using this (t - i)
  intro n
  induction n with
  | zero => simpa using halive
  | succ n ih =>
    have hi : i ≤ i + n := Nat.le_add_right _ _
    have hi' : i ≤ i + n + 1 := Nat.le_trans hi (Nat.le_succ _)
    obtain ⟨k, hk⟩ := hstay (i + n) hi
    obtain ⟨k', hk'⟩ := hstay (i + n + 1) hi'
    exact receiver_stays I hL N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n)) (ρ.act (i + n))
      (ρ.cfg (i + n + 1)) s dst k k' (ρ.valid (i + n)) hk hk' ih

/-- An actor awaiting a reply keeps that wait, or the reply runs its continuation. -/
theorem await_next (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : (w.st s).phase = .awaitReply dst k) :
    (w'.st s).phase = .awaitReply dst k ∨ (w'.st s).phase = (proceed (w.st s) k).phase := by
  cases a with
  | finish id =>
    simp only [apply] at h
    unfold finishWait at h
    cases hphF : (w.st id).phase with
    | awaitEffect kF =>
      simp [hphF] at h
      cases h
      have hs : s ≠ id := by
        intro heq
        rw [heq] at hph
        rw [hph] at hphF
        cases hphF
      exact Or.inl (by simpa [setActor, hs] using hph)
    | awaitPeer kF =>
      simp [hphF] at h
      cases h
      have hs : s ≠ id := by
        intro heq
        rw [heq] at hph
        rw [hph] at hphF
        cases hphF
      exact Or.inl (by simpa [setActor, hs] using hph)
    | idle => simp [hphF] at h
    | run _ => simp [hphF] at h
    | parked _ _ _ => simp [hphF] at h
    | awaitReply _ _ => simp [hphF] at h
    | crashed => simp [hphF] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        have hslot := hO template (w.nextIx template) (Nat.le_refl _)
        have hne : s ≠ InstId.peer template (w.nextIx template) := by
          intro heq
          rw [heq] at hph
          rw [hslot.2.1] at hph
          cases hph
        simp only [readCells_st, setActor, hne]
        exact Or.inl hph
      · cases h
  | recvPrio id =>
    simp only [apply] at h
    have hs : s ≠ id := by
      intro heq
      rw [heq] at hph
      unfold receivePrio at h
      cases hp : (w.st id).prio with
      | nil => simp [hp] at h
      | cons _ _ => simp [hp, hph] at h
    unfold receivePrio at h
    cases hp : (w.st id).prio with
    | nil => simp [hp] at h
    | cons m ms =>
      by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
      · simp [hp, hready] at h
      · simp [hp, hready] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w id _ m w1 a1 s hdel
          exact Or.inl (by simpa [setActor, hs, hst] using hph)
  | recvBulk id =>
    simp only [apply] at h
    have hs : s ≠ id := by
      intro heq
      rw [heq] at hph
      unfold receiveBulk at h
      simp [hph] at h
    -- A receive resumes a parked sender. An actor already awaiting is not that sender's phase,
    -- so the installed resume is the identity on `s` unless `s` is parked, which it is not.
    unfold receiveBulk at h
    by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
    · simp [hready] at h
    · simp [hready] at h
      cases hbox : (w.st id).box with
      | nil =>
        cases hpark : (w.st id).parked with
        | nil => simp [hbox, hpark] at h
        | cons q qs =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hdel =>
            cases h
            have hst := deliver_st I w id _ q.msg w1 a1 s hdel
            have hpre : ((creditSender (setActor w1 id a1) (tname id) q.msg.sender).st s).phase =
                (w.st s).phase := by
              have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
                simpa [setActor, hs, hst] using hph
              exact ((credit_life (setActor w1 id a1) (tname id) q.msg.sender s).2.2.1).trans hset
            by_cases hsender : s = q.sender
            · have hid := resume_id_of_not_parked
                ((creditSender (setActor w1 id a1) (tname id) q.msg.sender).st s) q.isCall id
                (fun d c ck hbad => by rw [hpre] at hbad; simp [hph] at hbad)
              rw [← hsender]
              simp only [setActor, ite_true]
              have hres : (resumeSender ((creditSender (setActor w1 id a1) (tname id) q.msg.sender).st s) q.isCall id).phase =
                  ((creditSender (setActor w1 id a1) (tname id) q.msg.sender).st s).phase := by rw [hid]
              exact Or.inl (hres.trans (hpre.trans hph))
            · simp only [setActor, hsender, ite_false]
              exact Or.inl (hpre.trans hph)
      | cons m ms =>
        cases hpark : (w.st id).parked with
        | nil =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hdel =>
            cases h
            have hst := deliver_st I w id _ m w1 a1 s hdel
            have hcred := (credit_life (setActor w1 id a1) (tname id) m.sender s).2.2.1
            have hset : ((setActor w1 id a1).st s).phase = (w.st s).phase := by
              simpa [setActor, hs, hst] using hph
            exact Or.inl ((hcred.trans hset).trans hph)
        | cons q qs =>
          simp [hbox, hpark] at h
          split at h
          · cases h
          · next w1 a1 hdel =>
            cases h
            have hst := deliver_st I w id _ m w1 a1 s hdel
            let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
            have hpre : ((creditSender (setActor w1 id admitted) (tname id) m.sender).st s).phase =
                (w.st s).phase := by
              have hset : ((setActor w1 id admitted).st s).phase = (w.st s).phase := by
                simpa [setActor, hs, hst] using hph
              exact ((credit_life (setActor w1 id admitted) (tname id) m.sender s).2.2.1).trans hset
            by_cases hsender : s = q.sender
            · have hid := resume_id_of_not_parked
                ((creditSender (setActor w1 id admitted) (tname id) m.sender).st s) q.isCall id
                (fun d c ck hbad => by rw [hpre] at hbad; simp [hph] at hbad)
              rw [← hsender]
              simp only [setActor, ite_true]
              have hres :
                  (resumeSender ((creditSender (setActor w1 id admitted) (tname id) m.sender).st s) q.isCall id).phase =
                    ((creditSender (setActor w1 id admitted) (tname id) m.sender).st s).phase := by rw [hid]
              exact Or.inl (hres.trans (hpre.trans hph))
            · simp only [setActor, hsender, ite_false]
              exact Or.inl (hpre.trans hph)
  | exec id =>
    simp only [apply] at h
    have hsne : s ≠ id := by
      intro heq
      rw [heq] at hph
      simp [execHead, hph] at h
    unfold execHead at h
    by_cases hlid : (w.st id).life = .alive
    · simp [hlid] at h
      cases hphE : (w.st id).phase with
      | run kE =>
        simp [hphE] at h
        cases h
        cases hk : kE.rest with
        | nil => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
        | cons e tail =>
          cases e with
          | reply =>
            simp [execRun, hk]
            unfold performReply
            cases hr : kE.replyTo with
            | none => exact Or.inl (by simp [setActor, hsne, hph])
            | some caller =>
              cases hcall : (w.st caller).phase with
              | awaitReply dst' ck =>
                by_cases hd : dst' = id
                · by_cases hc : s = caller
                  · rw [hc, hcall] at hph
                    cases hph
                    have hcne : ¬caller = id := fun h => hsne (hc.trans h)
                    simp [hcall, hd, hc, hcne, setActor]
                  · simp [hcall, hd, setActor, hc, hsne]
                    exact Or.inl hph
                · exact Or.inl (by simp [hcall, hd, setActor, hsne, hph])
              | idle => exact Or.inl (by simp [hcall, setActor, hsne, hph])
              | run _ => exact Or.inl (by simp [hcall, setActor, hsne, hph])
              | parked _ _ _ => exact Or.inl (by simp [hcall, setActor, hsne, hph])
              | awaitEffect _ => exact Or.inl (by simp [hcall, setActor, hsne, hph])
              | awaitPeer _ => exact Or.inl (by simp [hcall, setActor, hsne, hph])
              | crashed => exact Or.inl (by simp [hcall, setActor, hsne, hph])
          | send name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, hph])
            | some dstId =>
              simp [hr]
              exact Or.inl ((enqueue_phase_other w I.desc id dstId
                ({ label := label, sender := id, callFrom := none } : Msg) false (afterHead kE) s hsne).trans hph)
          | call name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, hph])
            | some dstId =>
              simp [hr]
              exact Or.inl ((enqueue_phase_other w I.desc id dstId
                ({ label := label, sender := id, callFrom := some id } : Msg) true (afterHead kE) s hsne).trans hph)
          | trySend name label hint =>
            simp [execRun, hk]
            cases hr : route w I.desc name hint with
            | none => exact Or.inl (by simp [hr, setActor, hsne, hph])
            | some dstId =>
              simp [hr]
              split
              · by_cases hd : s = dstId
                · have hid : ¬dstId = id := fun hne => hsne (hd.trans hne)
                  simp [setActor, hd, hid, chargeSender, bumpToken]
                  have hph' := hph
                  rw [hd] at hph'
                  exact Or.inl hph'
                · exact Or.inl (by simp [setActor, hd, hsne, hph])
              · exact Or.inl (by simp [setActor, hsne, hph])
          | selfSchedule label =>
            simp [execRun, hk]
            split
            · exact Or.inl (by simp [setActor, hsne, hph])
            · split
              · exact Or.inl (by simp [setActor, hsne, hph])
              · exact Or.inl (by simp [setActor, hsne, hph])
          | cell name label value =>
            simp only [execRun, hk]
            split
            · exact Or.inl (by simp [setCell, setActor, hsne, hph])
            · rw [wakeReaders]
              exact Or.inl (by
                rw [wakes_phase (readersOf _ _) I.desc _ name label id s]
                simp [setCell, setActor, hsne, hph])
          | internal => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
          | peer => exact Or.inl (by simp [execRun, hk, setActor, hsne, hph])
          | terminate =>
            cases ht : templateOf I.desc (tname id) with
            | none => exact Or.inl (by simp [execRun, hk, ht, hph])
            | some t =>
              by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
              · let base :=
                  refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                    (w.st id).parked
                let dead : Actor :=
                  { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                have hmiss : ∀ p, p ∈ (w.st id).parked → p.sender ≠ s := by
                  intro p hp heq
                  obtain ⟨k0, hk0⟩ := hM.fwd id p hp
                  rw [heq, hph] at hk0
                  cases hk0
                have hbase : (base.st s).phase = (w.st s).phase := by
                  have hread := readCells_st I.desc w id s
                  have href := (refund_life (readCells I.desc w id) (tname id) (w.st id).box s).2.2.1
                  have hrefp :=
                    (refundP_life (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id)
                      (w.st id).parked s).2.2.1
                  simp [base, hread, href, hrefp]
                have hset : ((setActor base id dead).st s).phase = (w.st s).phase := by
                  simp [setActor, hsne, hbase]
                have hrel :=
                  (congrArg (fun a => a.phase)
                    (release_misses (setActor base id dead) id (w.st id).parked s hmiss)).trans hset
                have hstep : execRun I w id (w.st id) kE =
                    releaseParked (setActor base id dead) id (w.st id).parked := by
                  simp [execRun, hk, ht, hkill, base, dead]
                rw [hstep]
                exact Or.inl (hrel.trans hph)
              · exact Or.inl (by simp [execRun, hk, ht, hkill, hph])
      | idle => simp [hphE] at h
      | parked _ _ _ => simp [hphE] at h
      | awaitReply _ _ => simp [hphE] at h
      | awaitEffect _ => simp [hphE] at h
      | awaitPeer _ => simp [hphE] at h
      | crashed => simp [hphE] at h
    · simp [hlid] at h

/-- The reply that ends an `awaitReply` runs a strictly shorter continuation. -/
theorem await_fuel (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : (w.st s).phase = .awaitReply dst k)
    (hdiff : waitKind (w'.st s) ≠ some (.callReply dst)) :
    phaseFuel ((w'.st s).phase) < phaseFuel ((w.st s).phase) := by
  rcases await_next I a w w' s dst k hM hO h hph with hsame | hpro
  · exact absurd (by simp [waitKind, hsame]) hdiff
  · rw [hpro]
    have hle := proceed_fuel (w.st s) k
    have hold : phaseFuel ((w.st s).phase) = 2 * k.rest.length + 1 := by simp [phaseFuel, hph]
    rw [hold]
    omega

theorem proceed_not_blocking (a : Actor) (k : Cont) (dst : InstId) :
    waitKind (proceed a k) ≠ some (.blockingSend dst) := by
  cases hk : k.rest <;> simp [proceed, waitKind, hk]

theorem proceed_not_reply (a : Actor) (k : Cont) (dst : InstId) :
    waitKind (proceed a k) ≠ some (.callReply dst) := by
  cases hk : k.rest <;> simp [proceed, waitKind, hk]

/-- While the blocking-send kind persists, the parked continuation is unchanged. -/
theorem blocking_stays (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : ((ρ.cfg i).st s).phase = .parked dst false k)
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.blockingSend dst)) :
    ((ρ.cfg (i + n)).st s).phase = .parked dst false k := by
  induction n with
  | zero => simpa using hph
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hkind t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hR := cfg_reachable ρ (i + n)
    have hM := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.1
    have hO := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.2
    cases blocking_next I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) s dst k hM hO
        (ρ.valid (i + n)) hprev with
    | inl hsame => exact hsame
    | inr hpro =>
      have hnow := hkind (i + n + 1) (by omega) (by omega)
      have hwk : waitKind ((ρ.cfg (i + n + 1)).st s) =
          waitKind (proceed ((ρ.cfg (i + n)).st s) k) := by simp [waitKind, hpro]
      exact absurd (hwk.symm.trans hnow) (proceed_not_blocking ((ρ.cfg (i + n)).st s) k dst)

/-- While an `awaitReply` kind persists, that continuation is unchanged. -/
theorem await_stays (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : ((ρ.cfg i).st s).phase = .awaitReply dst k)
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.callReply dst)) :
    ((ρ.cfg (i + n)).st s).phase = .awaitReply dst k := by
  induction n with
  | zero => simpa using hph
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hkind t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hR := cfg_reachable ρ (i + n)
    have hM := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.1
    have hO := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.2
    cases await_next I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) s dst k hM hO
        (ρ.valid (i + n)) hprev with
    | inl hsame => exact hsame
    | inr hpro =>
      have hnow := hkind (i + n + 1) (by omega) (by omega)
      have hwk : waitKind ((ρ.cfg (i + n + 1)).st s) =
          waitKind (proceed ((ρ.cfg (i + n)).st s) k) := by simp [waitKind, hpro]
      exact absurd (hwk.symm.trans hnow) (proceed_not_reply ((ρ.cfg (i + n)).st s) k dst)

/-- Least `m ≥ i` at which `p` holds, given some later witness. -/
theorem earliest (p : Nat → Prop) : ∀ j i, i ≤ j → p j →
    ∃ m, i ≤ m ∧ p m ∧ ∀ t, i ≤ t → t < m → ¬p t := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro i hij hp
    cases Classical.em (∃ t, i ≤ t ∧ t < j ∧ p t) with
    | inl hex =>
      obtain ⟨t, ht, hlt, hpt⟩ := hex
      exact ih t hlt i ht hpt
    | inr hno =>
      refine ⟨j, hij, hp, ?_⟩
      intro t ht hlt hpt
      exact hno ⟨t, ht, hlt, hpt⟩

/-- The first step that leaves a blocking send drops `phaseFuel`. -/
theorem send_drops_at (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i j : Nat)
    (hph : ((ρ.cfg i).st s).phase = .parked dst false k) (hlt : i < j)
    (hbefore : ∀ t, i ≤ t → t < j → waitKind ((ρ.cfg t).st s) = some (.blockingSend dst))
    (hdiff : waitKind ((ρ.cfg j).st s) ≠ some (.blockingSend dst)) :
    phaseFuel (((ρ.cfg j).st s).phase) < phaseFuel (((ρ.cfg i).st s).phase) := by
  have hle : i ≤ j - 1 := by omega
  have hpre := blocking_stays I hL ρ s dst k i ((j - 1) - i) hph
    (fun t h1 h2 => hbefore t h1 (by
      have hn : i + ((j - 1) - i) = j - 1 := Nat.add_sub_of_le hle
      omega))
  have hidx : i + ((j - 1) - i) = j - 1 := Nat.add_sub_of_le hle
  have hph1 : ((ρ.cfg (j - 1)).st s).phase = .parked dst false k := by simpa [hidx] using hpre
  have hR := cfg_reachable ρ (j - 1)
  have hM := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.1
  have hO := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.2
  have hv := ρ.valid (j - 1)
  have hj1 : (j - 1) + 1 = j := by omega
  rw [hj1] at hv
  have hdrop := blocking_fuel I (ρ.act (j - 1)) (ρ.cfg (j - 1)) (ρ.cfg j) s dst k hM hO
    hv hph1 hdiff
  have heq : phaseFuel (((ρ.cfg (j - 1)).st s).phase) = phaseFuel (((ρ.cfg i).st s).phase) := by
    simp [phaseFuel, hph1, hph]
  omega

/-- The first step that leaves an `awaitReply` drops `phaseFuel`. -/
theorem await_drops_at (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i j : Nat)
    (hph : ((ρ.cfg i).st s).phase = .awaitReply dst k) (hlt : i < j)
    (hbefore : ∀ t, i ≤ t → t < j → waitKind ((ρ.cfg t).st s) = some (.callReply dst))
    (hdiff : waitKind ((ρ.cfg j).st s) ≠ some (.callReply dst)) :
    phaseFuel (((ρ.cfg j).st s).phase) < phaseFuel (((ρ.cfg i).st s).phase) := by
  have hle : i ≤ j - 1 := by omega
  have hpre := await_stays I hL ρ s dst k i ((j - 1) - i) hph
    (fun t h1 h2 => hbefore t h1 (by omega))
  have hidx : i + ((j - 1) - i) = j - 1 := Nat.add_sub_of_le hle
  have hph1 : ((ρ.cfg (j - 1)).st s).phase = .awaitReply dst k := by simpa [hidx] using hpre
  have hR := cfg_reachable ρ (j - 1)
  have hM := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.1
  have hO := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.2
  have hv := ρ.valid (j - 1)
  have hj1 : (j - 1) + 1 = j := by omega
  rw [hj1] at hv
  have hdrop := await_fuel I (ρ.act (j - 1)) (ρ.cfg (j - 1)) (ρ.cfg j) s dst k hM hO
    hv hph1 hdiff
  have heq : phaseFuel (((ρ.cfg (j - 1)).st s).phase) = phaseFuel (((ρ.cfg i).st s).phase) := by
    simp [phaseFuel, hph1, hph]
  omega

theorem kill_park_empty (I : Impl) (w : World) (id : InstId) (t : Template) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (ht : templateOf I.desc (tname id) = some t)
    (hflag : (t.terminable && !hasParkedCall (w.st id).parked) = true) :
    ((execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩).st id).parked = [] := by
  let base :=
    refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id) (w.st id).parked
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hstep : execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ =
      releaseParked (setActor base id dead) id (w.st id).parked := by
    simp [execRun, ht, hflag, base, dead]
  rw [hstep, release_preserves_parked]
  simp [setActor, dead]

theorem enqueue_miss_dead (w : World) (D : Description) (sender dst i : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hne : i ≠ sender) (hdead : (w.st i).life ≠ .alive) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).parked = (w.st i).parked := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · have hid : i ≠ dst := fun h => hdead (by simpa [h] using hlive)
    simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      by_cases hsame : sender = dst
      · cases isCall <;> simp [hsame, setActor, hne, hid, proceed_parked, chargeSender, bumpToken]
      · cases isCall <;> simp [hsame, setActor, hne, hid, proceed_parked, chargeSender, bumpToken]
    · simp [hroom]
      by_cases hsame : sender = dst
      · simp [hsame, setActor, hne, hid, chargeSender, bumpToken]
      · simp [hsame, setActor, hne, hid, chargeSender, bumpToken]
  · simp [hlive, setActor, hne, proceed_parked]

/-- A non-alive actor does not acquire parked mail. -/
theorem dead_no_mail (I : Impl) (a : Action) (w w' : World) (id : InstId)
    (h : apply I a w = some w') (hdead : (w.st id).life ≠ .alive)
    (hempty : (w.st id).parked = []) : (w'.st id).parked = [] := by
  cases a with
  | finish j => simpa [hempty] using finish_parked w w' j id (by simpa [apply] using h)
  | recvPrio j => simpa [hempty] using prio_parked I w w' j id (by simpa [apply] using h)
  | recvBulk j =>
    by_cases hji : id = j
    · simp only [apply] at h
      unfold receiveBulk at h
      have hguard : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle := Or.inl (by simpa [hji] using hdead)
      simp [hji, hguard] at h
    · simpa [hempty] using bulk_other_parked I w w' j id (by simpa [apply] using h) hji
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        simp only [readCells_st]
        by_cases hi : id = InstId.peer template (w.nextIx template)
        · simp [setActor, hi, withTokens, hempty]
        · simpa [setActor, hi] using hempty
      · cases h
  | exec j =>
    by_cases hji : id = j
    · rw [hji] at hdead
      simp only [apply] at h
      unfold execHead at h
      simp [hdead] at h
    · simp only [apply] at h
      unfold execHead at h
      by_cases hlj : (w.st j).life = .alive
      · simp [hlj] at h
        cases hp : (w.st j).phase with
        | run k =>
          simp [hp] at h
          cases h
          cases hk : k.rest with
          | nil => simp [execRun, hk, setActor, hji, hempty]
          | cons e tail =>
            cases e with
            | send name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_parked, hempty]
              | some dstId =>
                simp [hr]
                simpa [hempty] using enqueue_miss_dead w I.desc j dstId id
                  ({ label := label, sender := j, callFrom := none } : Msg) false (afterHead k) hji hdead
            | call name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_parked, hempty]
              | some dstId =>
                simp [hr]
                simpa [hempty] using enqueue_miss_dead w I.desc j dstId id
                  ({ label := label, sender := j, callFrom := some j } : Msg) true (afterHead k) hji hdead
            | trySend name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_parked, hempty]
              | some dstId =>
                simp [hr]
                split
                · next hguard =>
                  have hlived : (w.st dstId).life = .alive := hguard.1.1
                  have hid : id ≠ dstId := fun h => hdead (by simpa [h] using hlived)
                  simp [setActor, hji, hid, chargeSender, bumpToken, proceed_parked, hempty]
                · simp [setActor, hji, proceed_parked, hempty]
            | reply =>
              simp [execRun, hk]
              unfold performReply
              cases k.replyTo with
              | none =>
                by_cases hi : id = j
                · exact absurd hi hji
                · simp [setActor, hi, proceed_parked, hempty]
              | some caller =>
                cases hcall : (w.st caller).phase with
                | awaitReply dst' ck =>
                  by_cases hd : dst' = j
                  · by_cases hc : id = caller
                    · have hcj : caller ≠ j := fun h => hji (hc.trans h)
                      simp [hcall, hd, hc, hcj, setActor, proceed_parked]
                      simpa [hc] using hempty
                    · by_cases hi : id = j
                      · exact absurd hi hji
                      · simp [hcall, hd, hc, hi, setActor, proceed_parked, hempty]
                  · by_cases hi : id = j
                    · exact absurd hi hji
                    · simp [hcall, hd, hi, setActor, proceed_parked, hempty]
                | idle =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
                | run _ =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
                | parked _ _ _ =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
                | awaitEffect _ =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
                | awaitPeer _ =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
                | crashed =>
                  by_cases hi : id = j
                  · exact absurd hi hji
                  · simp [hcall, hi, setActor, proceed_parked, hempty]
            | selfSchedule _ =>
              simp [execRun, hk]
              split
              · simp [setActor, hji, proceed_parked, hempty]
              · split
                · simp [setActor, hji, proceed_parked, hempty]
                · simp [setActor, hji, hempty]
            | cell name label value =>
              simp only [execRun, hk]
              split
              · simp [setCell, setActor, hji, proceed_parked, hempty]
              · let w1 : World := setActor (setCell w name label { value := max (w.cell name label).value value, dirty := true }) j (proceed ((setCell w name label { value := max (w.cell name label).value value, dirty := true }).st j) (afterHead k))
                have hbase : (w1.st id).parked = (w.st id).parked := by
                  simp [w1, setCell, setActor, hji, proceed_parked]
                rw [wakeReaders]
                have hw := wakes_parked I.desc (readersOf w1 name) w1 label j id
                exact (hw.trans hbase).trans hempty
            | internal => simp [execRun, hk, setActor, hji, hempty]
            | peer => simp [execRun, hk, setActor, hji, hempty]
            | terminate =>
              cases ht : templateOf I.desc (tname j) with
              | none => simp [execRun, hk, ht, hempty]
              | some t =>
                by_cases hflag : (t.terminable && !hasParkedCall (w.st j).parked) = true
                · let base :=
                    refundParked (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                      (w.st j).parked
                  let deadA : Actor :=
                    { base.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hstep : execRun I w j (w.st j) k =
                      releaseParked (setActor base j deadA) j (w.st j).parked := by
                    simp [execRun, hk, ht, hflag, base, deadA]
                  rw [hstep, release_preserves_parked]
                  have hbase : (base.st id).parked = (w.st id).parked := by
                    simp [base, readCells_st, refund_msgs_parked, refund_park_parked]
                  simp [setActor, hji, hbase, hempty]
                · simp [execRun, hk, ht, hflag, hempty]
        | idle => simp [hp] at h
        | parked _ _ _ => simp [hp] at h
        | awaitReply _ _ => simp [hp] at h
        | awaitEffect _ => simp [hp] at h
        | awaitPeer _ => simp [hp] at h
        | crashed => simp [hp] at h
      · simp [hlj] at h

theorem init_park_empty (I : Impl) (N : Nat) (i : InstId) : ((initWorld I N).st i).parked = [] := by
  unfold initWorld
  rw [fold_read_st]
  cases hb : (coreRoster I.desc).contains i with
  | false =>
    show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).parked = []
    rw [hb]
    simp [absentActor]
  | true =>
    show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).parked = []
    rw [hb]
    unfold initActor
    cases templateOf I.desc (tname i) with
    | none => simp [absentActor]
    | some _ => simp [withTokens]

/-- A reachable mailbox that holds parked mail belongs to a live actor. -/
theorem mailbox_alive (I : Impl) (hL : LocalOk I) (N : Nat) (w : World) (hR : Reachable I N w)
    (id : InstId) (hne : (w.st id).parked ≠ []) : (w.st id).life = .alive := by
  induction hR generalizing id with
  | init => exact absurd (init_park_empty I N id) hne
  | step w w' a prev happ ih =>
    cases Classical.em ((w'.st id).life = .alive) with
    | inl hlive => exact hlive
    | inr hdead =>
      cases Classical.em ((w.st id).life = .alive) with
      | inl halive =>
        obtain ⟨tail, toState, replyTo, t, hact, hrun, ht, hflag⟩ :=
          only_terminate_kills I a w w' id happ halive hdead
        have hcleared := kill_park_empty I w id t tail toState replyTo ht hflag
        have hstep : w' = execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ := by
          simp [apply, hact, execHead, halive, hrun] at happ
          exact happ.symm
        rw [hstep] at hne
        exact absurd hcleared hne
      | inr hdead0 =>
        have hempty : (w.st id).parked = [] := by
          cases Classical.em ((w.st id).parked = []) with
          | inl hempty => exact hempty
          | inr hne0 => exact absurd (ih id hne0) hdead0
        exact absurd (dead_no_mail I a w w' id happ hdead0 hempty) hne

/-- Parked or waiting for a reply. These phases do not carry a new typestate. -/
def PhaseWait (ph : Phase) : Prop :=
  (∃ dst c k, ph = .parked dst c k) ∨ (∃ dst k, ph = .awaitReply dst k)

theorem proceed_not_wait (a : Actor) (k : Cont) : ¬PhaseWait (proceed a k).phase := by
  cases hk : k.rest <;> simp [proceed, PhaseWait, hk]

theorem resume_ty (a : Actor) (b : Bool) (dst : InstId) (h : PhaseWait (resumeSender a b dst).phase) :
    (resumeSender a b dst).typestate = a.typestate := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases b with
    | true => simp [resumeSender, hph]
    | false =>
      exact absurd (by simpa [resumeSender, hph] using h) (proceed_not_wait a k)
  | idle => simp [resumeSender, hph]
  | run _ => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

/-- Enqueue copies typestate whenever the actor is still parked or awaiting. -/
theorem enqueue_ty_wait (w : World) (D : Description) (sender dst i : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont)
    (hwait : PhaseWait ((enqueueOrPark w D sender dst msg isCall k).st i).phase) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).typestate = (w.st i).typestate := by
  cases isCall with
  | true =>
    unfold enqueueOrPark at hwait ⊢
    by_cases hlive : (w.st dst).life = .alive
    · simp [hlive] at hwait ⊢
      by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
      · simp [hroom] at hwait ⊢
        by_cases hsame : sender = dst
        · rw [if_pos hsame] at hwait ⊢
          simp [setActor, chargeSender, bumpToken]
          by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken]
        · rw [if_neg hsame] at hwait ⊢
          have hflip : ¬dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst <;> simp [setActor, hi, hid, hflip]
      · simp [hroom] at hwait ⊢
        by_cases hsame : sender = dst
        · rw [if_pos hsame] at hwait ⊢
          simp [setActor, chargeSender, bumpToken]
          by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken]
        · rw [if_neg hsame] at hwait ⊢
          have hflip : ¬dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst <;> simp [setActor, hi, hid, hflip]
    · simp [hlive, setActor] at hwait ⊢
      by_cases hi : i = sender
      · simp [hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ k)
      · simp [hi]
  | false =>
    unfold enqueueOrPark at hwait ⊢
    by_cases hlive : (w.st dst).life = .alive
    · simp [hlive] at hwait ⊢
      by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
      · simp [hroom] at hwait ⊢
        by_cases hsame : sender = dst
        · rw [if_pos hsame] at hwait ⊢
          simp [setActor, chargeSender, bumpToken] at hwait ⊢
          by_cases hi : i = sender
          · simp [hi] at hwait ⊢
            exact absurd hwait (proceed_not_wait _ k)
          · simp [hi]
        · rw [if_neg hsame] at hwait ⊢
          have hflip : ¬dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken] at hwait ⊢
            exact absurd hwait (proceed_not_wait _ k)
          · by_cases hid : i = dst <;> simp [setActor, hi, hid, hflip]
      · simp [hroom] at hwait ⊢
        by_cases hsame : sender = dst
        · rw [if_pos hsame] at hwait ⊢
          simp [setActor, chargeSender, bumpToken]
          by_cases hi : i = sender <;> simp [hi, chargeSender, bumpToken]
        · rw [if_neg hsame] at hwait ⊢
          have hflip : ¬dst = sender := fun h => hsame h.symm
          by_cases hi : i = sender
          · simp [setActor, hi, chargeSender, bumpToken]
          · by_cases hid : i = dst <;> simp [setActor, hi, hid, hflip]
    · simp [hlive, setActor] at hwait ⊢
      by_cases hi : i = sender
      · simp [hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ k)
      · simp [hi]

theorem reply_ty_wait (w : World) (sender : InstId) (k : Cont) (i : InstId)
    (hwait : PhaseWait ((performReply w sender k).st i).phase) :
    ((performReply w sender k).st i).typestate = (w.st i).typestate := by
  unfold performReply at hwait ⊢
  cases hr : k.replyTo with
  | none =>
    simp [hr] at hwait
    by_cases hi : i = sender
    · simp [setActor, hi] at hwait ⊢
      exact absurd hwait (proceed_not_wait _ (afterHead k))
    · simp [setActor, hi]
  | some caller =>
    simp [hr] at hwait
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      simp [hph] at hwait
      by_cases hd : dst = sender
      · simp [hd] at hwait
        by_cases hi : i = sender
        · simp [setActor, hi] at hwait ⊢
          exact absurd hwait (proceed_not_wait _ (afterHead k))
        · by_cases hc : i = caller
          · have hcs : ¬caller = sender := fun h => hi (hc.trans h)
            simp [setActor, hi, hc, hcs] at hwait ⊢
            exact absurd hwait (proceed_not_wait _ ck)
          · simp [setActor, hi, hc, hph, hd]
      · simp [hd] at hwait
        by_cases hi : i = sender
        · simp [setActor, hi] at hwait ⊢
          exact absurd hwait (proceed_not_wait _ (afterHead k))
        · simp [setActor, hi, hph, hd]
    | idle =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]
    | run ck =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]
    | parked _ _ _ =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]
    | awaitEffect _ =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]
    | awaitPeer _ =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]
    | crashed =>
      simp [hph] at hwait
      by_cases hi : i = sender
      · simp [setActor, hi] at hwait ⊢
        exact absurd hwait (proceed_not_wait _ (afterHead k))
      · simp [setActor, hi, hph]

theorem release_preserves_nonwait (w : World) (id : InstId) (ps : List Parked) (s : InstId)
    (hn : ¬PhaseWait ((w.st s).phase)) : ¬PhaseWait ((releaseParked w id ps).st s).phase := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hn
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w hn
    · rw [if_neg hskip]
      by_cases hs : s = p.sender
      · cases hph : (w.st p.sender).phase with
        | parked _ _ k =>
          exact ih _ (by simpa [setActor, hs, resumeSender, hph] using proceed_not_wait (w.st p.sender) k)
        | idle => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
        | run k => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
        | awaitReply _ _ => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
        | awaitEffect _ => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
        | awaitPeer _ => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
        | crashed => exact ih _ (by simpa [setActor, hs, resumeSender, hph] using hn)
      · exact ih _ (by simpa [setActor, hs] using hn)

theorem release_ty_wait (w : World) (id : InstId) (ps : List Parked) (s : InstId)
    (hpost : PhaseWait ((releaseParked w id ps).st s).phase) :
    ((releaseParked w id ps).st s).typestate = (w.st s).typestate := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons] at hpost ⊢
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip] at hpost ⊢
      exact ih _ hpost
    · rw [if_neg hskip] at hpost ⊢
      by_cases hs : s = p.sender
      · cases hph : (w.st p.sender).phase with
        | parked _ _ k =>
          exact absurd hpost (release_preserves_nonwait _ id ps s
            (by simpa [setActor, hs, resumeSender, hph] using proceed_not_wait (w.st p.sender) k))
        | idle =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
        | run k =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
        | awaitReply _ k =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
        | awaitEffect _ =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
        | awaitPeer _ =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
        | crashed =>
          have hidr : resumeSender (w.st p.sender) false id = w.st p.sender := by simp [resumeSender, hph]
          rw [hidr] at hpost ⊢
          have hself : setActor w p.sender (w.st p.sender) = w := by
            simp [setActor]; congr; funext i; by_cases h : i = p.sender <;> simp [h]
          rw [hself] at hpost ⊢
          exact ih _ hpost
      · have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id)) hpost
        exact hmid.trans (by simp [setActor, hs])

/-- One step does not change the typestate of an actor that stays parked or awaiting. -/
theorem waiting_ty_step (I : Impl) (a : Action) (w w' : World) (s : InstId)
    (h : apply I a w = some w')
    (hpre : PhaseWait ((w.st s).phase)) (hpost : PhaseWait ((w'.st s).phase)) :
    (w'.st s).typestate = (w.st s).typestate := by
  cases a with
  | finish j =>
    simp only [apply] at h
    unfold finishWait at h
    cases hp : (w.st j).phase with
    | awaitEffect kF =>
      simp [hp] at h
      cases h
      by_cases hs : s = j
      · rw [hs] at hpost
        simp [setActor] at hpost
        exact absurd hpost (proceed_not_wait _ kF)
      · simp [setActor, hs]
    | awaitPeer kF =>
      simp [hp] at h
      cases h
      by_cases hs : s = j
      · rw [hs] at hpost
        simp [setActor] at hpost
        exact absurd hpost (proceed_not_wait _ kF)
      · simp [setActor, hs]
    | idle => simp [hp] at h
    | run _ => simp [hp] at h
    | parked _ _ _ => simp [hp] at h
    | awaitReply _ _ => simp [hp] at h
    | crashed => simp [hp] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        simp only [readCells_st]
        by_cases hi : s = InstId.peer template (w.nextIx template)
        · simp [readCells_st, setActor, hi, withTokens, PhaseWait] at hpost
        · simp [readCells_st, setActor, hi]
      · cases h
  | recvPrio j =>
    by_cases hs : s = j
    · rw [hs] at hpre
      simp only [apply] at h
      unfold receivePrio at h
      cases hp : (w.st j).prio with
      | nil => simp [hp] at h
      | cons _ _ =>
        simp [hp] at h
        rcases hpre with ⟨_, _, _, hph⟩ | ⟨_, _, hph⟩ <;> simp [hph] at h
    · simp only [apply] at h
      unfold receivePrio at h
      cases hp : (w.st j).prio with
      | nil => simp [hp] at h
      | cons m ms =>
        by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
        · simp [hp, hready] at h
        · simp [hp, hready] at h
          split at h
          · cases h
          · next w1 a1 hdel =>
            cases h
            have hst := deliver_st I w j _ m w1 a1 s hdel
            simpa [setActor, hs] using congrArg (·.typestate) hst
  | recvBulk j =>
    by_cases hs : s = j
    · rw [hs] at hpre
      simp only [apply] at h
      unfold receiveBulk at h
      rcases hpre with ⟨_, _, _, hph⟩ | ⟨_, _, hph⟩ <;> simp [hph] at h
    · simp only [apply] at h
      unfold receiveBulk at h
      by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
      · simp [hready] at h
      · simp [hready] at h
        cases hbox : (w.st j).box with
        | nil =>
          cases hpark : (w.st j).parked with
          | nil => simp [hbox, hpark] at h
          | cons q qs =>
            simp [hbox, hpark] at h
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w j _ q.msg w1 a1 s hdel
              have hset : ((setActor w1 j a1).st s).typestate = (w.st s).typestate := by
                simpa [setActor, hs] using congrArg (·.typestate) hst
              have hcred := (credit_life (setActor w1 j a1) (tname j) q.msg.sender s).2.1
              by_cases hsender : s = q.sender
              · rw [← hsender] at hpost ⊢
                simp [setActor] at hpost ⊢
                exact (resume_ty _ q.isCall j hpost).trans (hcred.trans hset)
              · simp [setActor, hsender]
                exact hcred.trans hset
        | cons m ms =>
          cases hpark : (w.st j).parked with
          | nil =>
            simp [hbox, hpark] at h
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w j _ m w1 a1 s hdel
              have hset : ((setActor w1 j a1).st s).typestate = (w.st s).typestate := by
                simpa [setActor, hs] using congrArg (·.typestate) hst
              exact ((credit_life (setActor w1 j a1) (tname j) m.sender s).2.1).trans hset
          | cons q qs =>
            simp [hbox, hpark] at h
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w j _ m w1 a1 s hdel
              let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
              have hset : ((setActor w1 j admitted).st s).typestate = (w.st s).typestate := by
                simpa [setActor, admitted, hs] using congrArg (·.typestate) hst
              have hcred := (credit_life (setActor w1 j admitted) (tname j) m.sender s).2.1
              by_cases hsender : s = q.sender
              · rw [← hsender] at hpost ⊢
                simp [setActor] at hpost ⊢
                exact (resume_ty _ q.isCall j hpost).trans (hcred.trans hset)
              · simp [setActor, hsender]
                exact hcred.trans hset
  | exec j =>
    by_cases hs : s = j
    · rw [hs] at hpre
      simp only [apply] at h
      unfold execHead at h
      rcases hpre with ⟨_, _, _, hph⟩ | ⟨_, _, hph⟩ <;> simp [hph] at h
    · simp only [apply] at h
      unfold execHead at h
      by_cases hlj : (w.st j).life = .alive
      · simp [hlj] at h
        cases hp : (w.st j).phase with
        | run kE =>
          simp [hp] at h
          cases h
          cases hk : kE.rest with
          | nil => simp [execRun, hk, setActor, hs]
          | cons e tail =>
            cases e with
            | send name label hint =>
              simp [execRun, hk] at hpost ⊢
              cases hr : route w I.desc name hint with
              | none =>
                simp [hr, setActor, hs] at hpost ⊢
              | some dstId =>
                simp [hr] at hpost ⊢
                exact enqueue_ty_wait w I.desc j dstId s
                  ({ label := label, sender := j, callFrom := none } : Msg) false (afterHead kE) hpost
            | call name label hint =>
              simp [execRun, hk] at hpost ⊢
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hs] at hpost ⊢
              | some dstId =>
                simp [hr] at hpost ⊢
                exact enqueue_ty_wait w I.desc j dstId s
                  ({ label := label, sender := j, callFrom := some j } : Msg) true (afterHead kE) hpost
            | trySend name label hint =>
              simp [execRun, hk] at hpost ⊢
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hs] at hpost ⊢
              | some dstId =>
                simp [hr]
                split
                · by_cases hid : dstId = j
                  · simp [setActor, hid, hs, chargeSender, bumpToken, proceed]
                  · by_cases hi : s = dstId
                    · simp [setActor, hi, hid, hs, chargeSender, bumpToken, proceed]
                    · simp [setActor, hi, hs, chargeSender, bumpToken, proceed]
                · simp [setActor, hs, proceed]
            | reply =>
              simp [execRun, hk] at hpost ⊢
              exact reply_ty_wait w j kE s hpost
            | selfSchedule _ =>
              simp [execRun, hk]
              split
              · simp [setActor, hs, proceed]
              · split
                · simp [setActor, hs, proceed]
                · simp [setActor, hs]
            | cell name label value =>
              simp only [execRun, hk]
              split
              · simp [setCell, setActor, hs, proceed]
              · let w1 : World := setActor (setCell w name label
                    { value := max (w.cell name label).value value, dirty := true }) j
                  (proceed ((setCell w name label
                    { value := max (w.cell name label).value value, dirty := true }).st j) (afterHead kE))
                have hbase : (w1.st s).typestate = (w.st s).typestate := by
                  simp [w1, setCell, setActor, hs, proceed]
                rw [wakeReaders]
                exact (wakes_ty (readersOf w1 name) I.desc w1 name label j s).trans hbase
            | internal => simp [execRun, hk, setActor, hs]
            | peer => simp [execRun, hk, setActor, hs]
            | terminate =>
              cases ht : templateOf I.desc (tname j) with
              | none => simp [execRun, hk, ht]
              | some t =>
                by_cases hflag : (t.terminable && !hasParkedCall (w.st j).parked) = true
                · let base :=
                    refundParked (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                      (w.st j).parked
                  let deadA : Actor :=
                    { base.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hbase : (base.st s).typestate = (w.st s).typestate := by
                    have hread := congrArg (·.typestate) (readCells_st I.desc w j s)
                    have href := (refund_life (readCells I.desc w j) (tname j) (w.st j).box s).2.1
                    have hrefp :=
                      (refundP_life (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                        (w.st j).parked s).2.1
                    simp [base, hread, href, hrefp]
                  have hset : ((setActor base j deadA).st s).typestate = (w.st s).typestate := by
                    simp [setActor, hs, hbase]
                  have hstep : execRun I w j (w.st j) kE =
                      releaseParked (setActor base j deadA) j (w.st j).parked := by
                    simp [execRun, hk, ht, hflag, base, deadA]
                  rw [hstep] at hpost ⊢
                  exact (release_ty_wait (setActor base j deadA) j (w.st j).parked s hpost).trans hset
                · simp [execRun, hk, ht, hflag]
        | idle => simp [hp] at h
        | parked _ _ _ => simp [hp] at h
        | awaitReply _ _ => simp [hp] at h
        | awaitEffect _ => simp [hp] at h
        | awaitPeer _ => simp [hp] at h
        | crashed => simp [hp] at h
      · simp [hlj] at h

/-- While `s` stays parked or awaiting, its typestate does not change. -/
theorem parked_typestate_stays (I : Impl) {N : Nat} (ρ : Run I N)
    (s : InstId) (i n : Nat)
    (hwait : ∀ t, i ≤ t → t ≤ i + n → PhaseWait (((ρ.cfg t).st s).phase)) :
    ((ρ.cfg (i + n)).st s).typestate = ((ρ.cfg i).st s).typestate := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hwait t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hstep := waiting_ty_step I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) s
      (ρ.valid (i + n))
      (hwait (i + n) (Nat.le_add_right i n) (by omega))
      (hwait (i + n + 1) (by omega) (by omega))
    exact hstep.trans hprev

/-- A blocking send keeps the waiter's height, and the live callee stays strictly below it. -/
theorem send_height_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : ((ρ.cfg i).st s).phase = .parked dst false k)
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.blockingSend dst))
    (hlive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st dst).life = .alive) :
    rankAt hs (ρ.cfg (i + n)) s = rankAt hs (ρ.cfg i) s ∧
      rankAt hs (ρ.cfg (i + n)) dst < rankAt hs (ρ.cfg i) s := by
  have hphn := blocking_stays I hL ρ s dst k i n hph hkind
  have hty := parked_typestate_stays I ρ s i n (fun t h1 h2 => by
    obtain ⟨k0, hk0⟩ := blocking_parked ((ρ.cfg t).st s) dst (hkind t h1 h2)
    exact Or.inl ⟨dst, false, k0, hk0⟩)
  have hrank : rankAt hs (ρ.cfg (i + n)) s = rankAt hs (ρ.cfg i) s := by
    simp [rankAt, hty]
  refine ⟨hrank, ?_⟩
  rw [← hrank]
  have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.2.1
  simpa [rankAt] using park_below I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n)) hO s dst k
    hs hok hphn (hlive (i + n) (Nat.le_add_right _ _) (Nat.le_refl _))

/-- Releasing a mailbox skips call entries, so a parked caller keeps its phase. -/
theorem release_keeps_caller (w : World) (id : InstId) (ps : List Parked) (s : InstId)
    (h : ∀ p, p ∈ ps → p.sender = s → p.isCall = true) :
    ((releaseParked w id ps).st s).phase = (w.st s).phase := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w (fun q hq => h q (List.mem_cons_of_mem p hq))
    · rw [if_neg hskip]
      have hne : s ≠ p.sender := by
        intro hs
        have hc : p.isCall = true := h p (by simp) hs.symm
        simp [hc] at hskip
      have hstep : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st s).phase =
          (w.st s).phase := by simp [setActor, hne]
      exact (ih _ (fun q hq => h q (List.mem_cons_of_mem p hq))).trans hstep

/-- A parked call is admitted to `awaitReply` with the same continuation, or it stays parked. -/
theorem call_park_next (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : (w.st s).phase = .parked dst true k) :
    (w'.st s).phase = .parked dst true k ∨ (w'.st s).phase = .awaitReply dst k := by
  cases a with
  | finish j =>
    simp only [apply] at h
    unfold finishWait at h
    cases hp : (w.st j).phase with
    | awaitEffect _ =>
      simp [hp] at h
      cases h
      by_cases hs : s = j
      · rw [hs] at hph
        simp [hph] at hp
      · exact Or.inl (by simpa [setActor, hs] using hph)
    | awaitPeer _ =>
      simp [hp] at h
      cases h
      by_cases hs : s = j
      · rw [hs] at hph
        simp [hph] at hp
      · exact Or.inl (by simpa [setActor, hs] using hph)
    | idle => simp [hp] at h
    | run _ => simp [hp] at h
    | parked _ _ _ => simp [hp] at h
    | awaitReply _ _ => simp [hp] at h
    | crashed => simp [hp] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        have hslot := hO template (w.nextIx template) (Nat.le_refl _)
        have hne : s ≠ InstId.peer template (w.nextIx template) := by
          intro heq
          rw [heq] at hph
          rw [hslot.2.1] at hph
          cases hph
        simp only [readCells_st, setActor, hne]
        exact Or.inl hph
      · cases h
  | recvPrio j =>
    simp only [apply] at h
    by_cases hs : s = j
    · rw [hs] at hph
      unfold receivePrio at h
      cases hp : (w.st j).prio with
      | nil => simp [hp] at h
      | cons _ _ => simp [hp, hph] at h
    · have hpk := prio_parked I w w' j s (by simpa using h)
      exact Or.inl (by
        unfold receivePrio at h
        cases hp : (w.st j).prio with
        | nil => simp [hp] at h
        | cons m ms =>
          by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
          · simp [hp, hready] at h
          · simp [hp, hready] at h
            split at h
            · cases h
            · next w1 a1 hdel =>
              cases h
              have hst := deliver_st I w j _ m w1 a1 s hdel
              simpa [setActor, hs, hst] using hph)
  | recvBulk j =>
    simp only [apply] at h
    by_cases hsj : s = j
    · rw [hsj] at hph
      unfold receiveBulk at h
      simp [hph] at h
    · by_cases hjd : j = dst
      · obtain ⟨p0, hp0, hs0, hc0⟩ := hM.bwd s dst true k hph
        cases hpk : (w.st dst).parked with
        | nil => exact absurd hp0 (by simp [hpk])
        | cons p ps =>
          by_cases hhead : s = p.sender
          · have hc : p.isCall = true := by
              have hmem : p ∈ (w.st dst).parked := by simp [hpk]
              exact (hM.uniq dst dst p0 p hp0 hmem (hs0.trans hhead)).2 ▸ hc0
            have hrecv : receiveBulk I w dst = some w' := by
              simpa [hjd] using h
            exact Or.inr (bulk_admits_call I w w' dst hrecv p ps hpk s hhead
              (by simpa [hjd] using hsj) k (by simpa [hjd] using hph) hc)
          · unfold receiveBulk at h
            by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
            · simp [hready] at h
            · simp [hready] at h
              cases hbox : (w.st j).box with
              | nil =>
                simp [hbox] at h
                cases hpark : (w.st j).parked with
                | nil => simp [hpark] at h
                | cons q qs =>
                  simp [hpark] at h
                  have hns : s ≠ q.sender := by
                    have hsame : (w.st j).parked = (w.st dst).parked := by simp [hjd]
                    rw [hsame, hpk] at hpark
                    cases hpark
                    exact hhead
                  split at h
                  · cases h
                  · next w1 a1 hdel =>
                    cases h
                    have hst := deliver_st I w j _ q.msg w1 a1 s hdel
                    have hset : ((setActor w1 j a1).st s).phase = (w.st s).phase := by
                      simpa [setActor, hsj, hst] using hph
                    have hcred := (credit_life (setActor w1 j a1) (tname j) q.msg.sender s).2.2.1
                    simp only [setActor, hns, ite_false]
                    exact Or.inl ((hcred.trans hset).trans hph)
              | cons m ms =>
                cases hpark : (w.st j).parked with
                | nil =>
                  simp [hbox, hpark] at h
                  split at h
                  · cases h
                  · next w1 a1 hdel =>
                    cases h
                    have hst := deliver_st I w j _ m w1 a1 s hdel
                    have hcred := (credit_life (setActor w1 j a1) (tname j) m.sender s).2.2.1
                    have hset : ((setActor w1 j a1).st s).phase = (w.st s).phase := by
                      simpa [setActor, hsj, hst] using hph
                    exact Or.inl ((hcred.trans hset).trans hph)
                | cons q qs =>
                  simp [hbox, hpark] at h
                  have hns : s ≠ q.sender := by
                    have hsame : (w.st j).parked = (w.st dst).parked := by simp [hjd]
                    rw [hsame, hpk] at hpark
                    cases hpark
                    exact hhead
                  split at h
                  · cases h
                  · next w1 a1 hdel =>
                    cases h
                    have hst := deliver_st I w j _ m w1 a1 s hdel
                    let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
                    have hset : ((setActor w1 j admitted).st s).phase = (w.st s).phase := by
                      simpa [setActor, admitted, hsj, hst] using hph
                    have hcred := (credit_life (setActor w1 j admitted) (tname j) m.sender s).2.2.1
                    simp only [setActor, hns, ite_false]
                    exact Or.inl ((hcred.trans hset).trans hph)
      · unfold receiveBulk at h
        by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
        · simp [hready] at h
        · simp [hready] at h
          cases hbox : (w.st j).box with
          | nil =>
            cases hpark : (w.st j).parked with
            | nil => simp [hbox, hpark] at h
            | cons q qs =>
              simp [hbox, hpark] at h
              have hns : s ≠ q.sender := by
                intro heq
                obtain ⟨p0, hp0, hs0, _⟩ := hM.bwd s dst true k hph
                have hmemq : q ∈ (w.st j).parked := by simp [hpark]
                exact hjd ((hM.uniq j dst q p0 hmemq hp0 (heq.symm.trans hs0.symm)).1)
              split at h
              · cases h
              · next w1 a1 hdel =>
                cases h
                have hst := deliver_st I w j _ q.msg w1 a1 s hdel
                have hset : ((setActor w1 j a1).st s).phase = (w.st s).phase := by
                  simpa [setActor, hsj, hst] using hph
                have hcred := (credit_life (setActor w1 j a1) (tname j) q.msg.sender s).2.2.1
                simp only [setActor, hns, ite_false]
                exact Or.inl ((hcred.trans hset).trans hph)
          | cons m ms =>
            cases hpark : (w.st j).parked with
            | nil =>
              simp [hbox, hpark] at h
              split at h
              · cases h
              · next w1 a1 hdel =>
                cases h
                have hst := deliver_st I w j _ m w1 a1 s hdel
                have hcred := (credit_life (setActor w1 j a1) (tname j) m.sender s).2.2.1
                have hset : ((setActor w1 j a1).st s).phase = (w.st s).phase := by
                  simpa [setActor, hsj, hst] using hph
                exact Or.inl ((hcred.trans hset).trans hph)
            | cons q qs =>
              simp [hbox, hpark] at h
              have hns : s ≠ q.sender := by
                intro heq
                obtain ⟨p0, hp0, hs0, _⟩ := hM.bwd s dst true k hph
                have hmemq : q ∈ (w.st j).parked := by simp [hpark]
                exact hjd ((hM.uniq j dst q p0 hmemq hp0 (heq.symm.trans hs0.symm)).1)
              split at h
              · cases h
              · next w1 a1 hdel =>
                cases h
                have hst := deliver_st I w j _ m w1 a1 s hdel
                let admitted : Actor := { a1 with box := a1.box ++ [q.msg], parked := qs }
                have hset : ((setActor w1 j admitted).st s).phase = (w.st s).phase := by
                  simpa [setActor, admitted, hsj, hst] using hph
                have hcred := (credit_life (setActor w1 j admitted) (tname j) m.sender s).2.2.1
                simp only [setActor, hns, ite_false]
                exact Or.inl ((hcred.trans hset).trans hph)
  | exec j =>
    simp only [apply] at h
    by_cases hsj : s = j
    · rw [hsj] at hph
      unfold execHead at h
      simp [hph] at h
    · unfold execHead at h
      by_cases hlj : (w.st j).life = .alive
      · simp [hlj] at h
        cases hp : (w.st j).phase with
        | run kE =>
          simp [hp] at h
          cases h
          cases hk : kE.rest with
          | nil => exact Or.inl (by simp [execRun, hk, setActor, hsj, hph])
          | cons e tail =>
            cases e with
            | send name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => exact Or.inl (by simp [hr, setActor, hsj, hph])
              | some dstId =>
                simp [hr]
                exact Or.inl ((enqueue_phase_other w I.desc j dstId
                  ({ label := label, sender := j, callFrom := none } : Msg) false (afterHead kE) s hsj).trans hph)
            | call name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => exact Or.inl (by simp [hr, setActor, hsj, hph])
              | some dstId =>
                simp [hr]
                exact Or.inl ((enqueue_phase_other w I.desc j dstId
                  ({ label := label, sender := j, callFrom := some j } : Msg) true (afterHead kE) s hsj).trans hph)
            | trySend name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => exact Or.inl (by simp [hr, setActor, hsj, hph])
              | some dstId =>
                simp [hr]
                split
                · by_cases hd : s = dstId
                  · have hdj : ¬dstId = j := fun h => hsj (hd.trans h)
                    simp [setActor, hd, hdj, chargeSender, bumpToken]
                    have hph' := hph
                    rw [hd] at hph'
                    exact Or.inl hph'
                  · exact Or.inl (by simp [setActor, hd, hsj, chargeSender, bumpToken, hph])
                · exact Or.inl (by simp [setActor, hsj, hph])
            | reply =>
              simp [execRun, hk]
              exact Or.inl ((reply_keeps_quiet w j s kE
                (fun d ck hbad => by simp [hph] at hbad) hsj).1.trans hph)
            | selfSchedule _ =>
              simp [execRun, hk]
              split
              · exact Or.inl (by simp [setActor, hsj, hph])
              · split
                · exact Or.inl (by simp [setActor, hsj, hph])
                · exact Or.inl (by simp [setActor, hsj, hph])
            | cell name label value =>
              simp only [execRun, hk]
              split
              · exact Or.inl (by simp [setCell, setActor, hsj, hph])
              · rw [wakeReaders]
                exact Or.inl (by
                  rw [wakes_phase (readersOf _ _) I.desc _ name label j s]
                  simp [setCell, setActor, hsj, hph])
            | internal => exact Or.inl (by simp [execRun, hk, setActor, hsj, hph])
            | peer => exact Or.inl (by simp [execRun, hk, setActor, hsj, hph])
            | terminate =>
              cases ht : templateOf I.desc (tname j) with
              | none => exact Or.inl (by simp [execRun, hk, ht, hph])
              | some t =>
                by_cases hflag : (t.terminable && !hasParkedCall (w.st j).parked) = true
                · let base :=
                    refundParked (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                      (w.st j).parked
                  let deadA : Actor :=
                    { base.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hcalls : ∀ p, p ∈ (w.st j).parked → p.sender = s → p.isCall = true := by
                    intro p hp hsnd
                    obtain ⟨q, hq, hqs, hc⟩ := hM.bwd s dst true k hph
                    have hjd : j = dst := (hM.uniq j dst p q hp hq (hsnd.trans hqs.symm)).1
                    have hsame := (hM.uniq j dst p q hp hq (hsnd.trans hqs.symm)).2
                    simpa [hsame] using hc
                  have hbase : (base.st s).phase = (w.st s).phase := by
                    have hread := readCells_st I.desc w j s
                    have href := (refund_life (readCells I.desc w j) (tname j) (w.st j).box s).2.2.1
                    have hrefp :=
                      (refundP_life (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                        (w.st j).parked s).2.2.1
                    simp [base, hread, href, hrefp]
                  have hset : ((setActor base j deadA).st s).phase = (w.st s).phase := by
                    simp [setActor, hsj, hbase]
                  have hrel := release_keeps_caller (setActor base j deadA) j (w.st j).parked s hcalls
                  have hstep : execRun I w j (w.st j) kE =
                      releaseParked (setActor base j deadA) j (w.st j).parked := by
                    simp [execRun, hk, ht, hflag, base, deadA]
                  rw [hstep]
                  exact Or.inl ((hrel.trans hset).trans hph)
                · exact Or.inl (by simp [execRun, hk, ht, hflag, hph])
        | idle => simp [hp] at h
        | parked _ _ _ => simp [hp] at h
        | awaitReply _ _ => simp [hp] at h
        | awaitEffect _ => simp [hp] at h
        | awaitPeer _ => simp [hp] at h
        | crashed => simp [hp] at h
      · simp [hlj] at h

/-- A call keeps its continuation: admission only rewrites parked into `awaitReply`. -/
def CallPhase (dst : InstId) (k : Cont) (ph : Phase) : Prop :=
  ph = .parked dst true k ∨ ph = .awaitReply dst k

theorem call_step (I : Impl) (a : Action) (w w' : World) (s dst : InstId) (k : Cont)
    (hM : MailInv w) (hO : OpenSlots w) (h : apply I a w = some w')
    (hph : CallPhase dst k ((w.st s).phase))
    (hkind : waitKind ((w'.st s)) = some (.callReply dst)) :
    CallPhase dst k ((w'.st s).phase) := by
  rcases hph with hpark | hawait
  · rcases call_park_next I a w w' s dst k hM hO h hpark with hstay | hadm
    · exact Or.inl hstay
    · exact Or.inr hadm
  · rcases await_next I a w w' s dst k hM hO h hawait with hstay | hpro
    · exact Or.inr hstay
    · have hwk : waitKind ((w'.st s)) = waitKind (proceed ((w.st s)) k) := by simp [waitKind, hpro]
      exact absurd (hwk.symm.trans hkind) (proceed_not_reply ((w.st s)) k dst)

theorem call_stays (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : CallPhase dst k (((ρ.cfg i).st s).phase))
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.callReply dst)) :
    CallPhase dst k (((ρ.cfg (i + n)).st s).phase) := by
  induction n with
  | zero => simpa using hph
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hkind t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hR := cfg_reachable ρ (i + n)
    have hM := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.1
    have hO := (inv_reachable I N (ρ.cfg (i + n)) hL hR).2.2
    exact call_step I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) s dst k hM hO
      (ρ.valid (i + n)) hprev (hkind (i + n + 1) (by omega) (by omega))

/-- The first step that leaves a call reply drops `phaseFuel`. -/
theorem call_drops_at (I : Impl) (hL : LocalOk I) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i j : Nat)
    (hph : CallPhase dst k (((ρ.cfg i).st s).phase)) (hlt : i < j)
    (hbefore : ∀ t, i ≤ t → t < j → waitKind ((ρ.cfg t).st s) = some (.callReply dst))
    (hdiff : waitKind ((ρ.cfg j).st s) ≠ some (.callReply dst)) :
    phaseFuel (((ρ.cfg j).st s).phase) < phaseFuel (((ρ.cfg i).st s).phase) := by
  have hle : i ≤ j - 1 := by omega
  have hpre := call_stays I hL ρ s dst k i ((j - 1) - i) hph
    (fun t h1 h2 => hbefore t h1 (by omega))
  have hidx : i + ((j - 1) - i) = j - 1 := Nat.add_sub_of_le hle
  have hph1 : CallPhase dst k (((ρ.cfg (j - 1)).st s).phase) := by simpa [hidx] using hpre
  have hR := cfg_reachable ρ (j - 1)
  have hM := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.1
  have hO := (inv_reachable I N (ρ.cfg (j - 1)) hL hR).2.2
  have hv := ρ.valid (j - 1)
  have hj1 : (j - 1) + 1 = j := by omega
  rw [hj1] at hv
  rcases hph1 with hpark | hawait
  · have hstep := call_park_next I (ρ.act (j - 1)) (ρ.cfg (j - 1)) (ρ.cfg j) s dst k hM hO hv hpark
    rcases hstep with hstay | hadm
    · exact absurd (by simp [waitKind, hstay]) hdiff
    · exact absurd (by simp [waitKind, hadm]) hdiff
  · have hdrop := await_fuel I (ρ.act (j - 1)) (ρ.cfg (j - 1)) (ρ.cfg j) s dst k hM hO hv hawait hdiff
    have heq : phaseFuel (((ρ.cfg (j - 1)).st s).phase) = phaseFuel (((ρ.cfg i).st s).phase) := by
      rcases hph with hpark0 | hawait0
      · simp [phaseFuel, hawait, hpark0]
      · simp [phaseFuel, hawait, hawait0]
    omega

theorem call_callee_step (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (a : Action) (w' : World) (s dst : InstId) (k : Cont)
    (h : apply I a w = some w') (hph : CallPhase dst k ((w.st s).phase))
    (halive : (w.st dst).life = .alive) : (w'.st dst).life = .alive := by
  cases Classical.em ((w'.st dst).life = .alive) with
  | inl h' => exact h'
  | inr hdead =>
    obtain ⟨_, _, _, t, _, _, ht, hflag⟩ := only_terminate_kills I a w w' dst h halive hdead
    have hterm : t.terminable = true := by
      cases hb : t.terminable with
      | false => simp [hb] at hflag
      | true => rfl
    rcases hph with hpark | hawait
    · exact absurd hterm (by
        simpa using parked_call_unterminable I hL hG N w hR s dst k hpark t ht)
    · exact absurd hterm (by
        simpa using await_callee_unterminable I hL hG N w hR s dst k hawait t ht)

theorem call_callee_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : CallPhase dst k (((ρ.cfg i).st s).phase))
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.callReply dst))
    (halive : ((ρ.cfg i).st dst).life = .alive) :
    ((ρ.cfg (i + n)).st dst).life = .alive := by
  induction n with
  | zero => simpa using halive
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => hkind t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    have hphase := call_stays I hL ρ s dst k i n hph
      (fun t h1 h2 => hkind t h1 (Nat.le_trans h2 (Nat.le_succ _)))
    exact call_callee_step I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))
      (ρ.act (i + n)) (ρ.cfg (i + n + 1)) s dst k (ρ.valid (i + n)) hphase hprev

/-- A call keeps the caller's height, and the live callee stays strictly below it. -/
theorem call_height_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (s dst : InstId) (k : Cont) (i n : Nat)
    (hph : CallPhase dst k (((ρ.cfg i).st s).phase))
    (hkind : ∀ t, i ≤ t → t ≤ i + n → waitKind ((ρ.cfg t).st s) = some (.callReply dst))
    (halive : ((ρ.cfg i).st dst).life = .alive) :
    rankAt hs (ρ.cfg (i + n)) s = rankAt hs (ρ.cfg i) s ∧
      rankAt hs (ρ.cfg (i + n)) dst < rankAt hs (ρ.cfg i) s := by
  have hphn := call_stays I hL ρ s dst k i n hph hkind
  have hty := parked_typestate_stays I ρ s i n (fun t h1 h2 => by
    have hphase := call_stays I hL ρ s dst k i (t - i) hph (fun u hu1 hu2 =>
      hkind u hu1 (by
        have ht : i + (t - i) = t := Nat.add_sub_of_le h1
        omega))
    have hidx : i + (t - i) = t := Nat.add_sub_of_le h1
    have hhere : CallPhase dst k (((ρ.cfg t).st s).phase) := by simpa [hidx] using hphase
    rcases hhere with hpark | hawait
    · exact Or.inl ⟨dst, true, k, hpark⟩
    · exact Or.inr ⟨dst, k, hawait⟩)
  have hrank : rankAt hs (ρ.cfg (i + n)) s = rankAt hs (ρ.cfg i) s := by
    simp [rankAt, hty]
  have hlive := call_callee_alive I hL hG ρ s dst k i n hph hkind halive
  refine ⟨hrank, ?_⟩
  rw [← hrank]
  rcases hphn with hpark | hawait
  · have hO := (inv3_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).1.2.1
    simpa [rankAt] using call_below I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n)) s dst k
      hs hok hpark hlive
  · simpa [rankAt] using reply_below I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n)) s dst k
      hs hok hawait hlive

/-- An actor that stays alive and is never stuck reaches idle. Blocks end, and each
ending step drops `phaseFuel`, including a call whose continuation was frozen. -/
theorem idle_when_free (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (x : InstId) (i0 : Nat)
    (halive : ∀ t, i0 ≤ t → ((ρ.cfg t).st x).life = .alive)
    (hfree : ∀ t, i0 ≤ t → ¬Stuck ρ x t) :
    ∀ t, i0 ≤ t → ∃ j, t ≤ j ∧ Idle (ρ.cfg j) x := by
  suffices ∀ n t, i0 ≤ t → phaseFuel (((ρ.cfg t).st x).phase) ≤ n →
      ∃ j, t ≤ j ∧ Idle (ρ.cfg j) x by
    intro t ht
    exact this _ t ht (Nat.le_refl _)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht hfuel
    cases hph : ((ρ.cfg t).st x).phase with
    | idle => exact ⟨t, Nat.le_refl _, ⟨halive t ht, hph⟩⟩
    | crashed =>
      exact absurd hph (reachable_not_crashed I hL hG N (ρ.cfg t) (cfg_reachable ρ t) x)
    | awaitEffect k =>
      obtain ⟨j, hj, hproc, _⟩ := effect_resumes I hL hG ρ hF x t k hph (halive t ht)
      have hlt : phaseFuel (((ρ.cfg (j + 1)).st x).phase) < n := by
        have hnew := proceed_fuel ((ρ.cfg j).st x) k
        rw [← hproc] at hnew
        have hold : phaseFuel (((ρ.cfg t).st x).phase) = 2 * k.rest.length + 1 := by
          simp [phaseFuel, hph]
        omega
      obtain ⟨j2, hj2, hq⟩ := ih _ hlt (j + 1)
        (Nat.le_trans ht (Nat.le_trans hj (Nat.le_succ j))) (Nat.le_refl _)
      exact ⟨j2, Nat.le_trans (Nat.le_trans hj (Nat.le_succ j)) hj2, hq⟩
    | awaitPeer k =>
      obtain ⟨j, hj, hproc, _⟩ := peer_resumes I hL hG ρ hF x t k hph (halive t ht)
      have hlt : phaseFuel (((ρ.cfg (j + 1)).st x).phase) < n := by
        have hnew := proceed_fuel ((ρ.cfg j).st x) k
        rw [← hproc] at hnew
        have hold : phaseFuel (((ρ.cfg t).st x).phase) = 2 * k.rest.length + 1 := by
          simp [phaseFuel, hph]
        omega
      obtain ⟨j2, hj2, hq⟩ := ih _ hlt (j + 1)
        (Nat.le_trans ht (Nat.le_trans hj (Nat.le_succ j))) (Nat.le_refl _)
      exact ⟨j2, Nat.le_trans (Nat.le_trans hj (Nat.le_succ j)) hj2, hq⟩
    | run k =>
      have hhit : ∃ j, t ≤ j ∧ ρ.act j = .exec x := by
        cases Classical.em (∃ j, t ≤ j ∧ ρ.act j = .exec x) with
        | inl h => exact h
        | inr hmiss =>
          have hstay : ∀ u, t ≤ u → ((ρ.cfg u).st x).phase = .run k ∧
              ((ρ.cfg u).st x).life = .alive := by
            intro u hu
            have hgot := run_holds hL hG ρ x t (u - t) k hph (halive t ht)
              (fun v h1 _ hbad => hmiss ⟨v, h1, hbad⟩)
            simpa [Nat.add_sub_of_le hu] using hgot
          exact False.elim (not_forever_run I hL hG ρ hF x t (fun j hj => (hstay j hj).2)
            (fun j hj => ⟨k, (hstay j hj).1⟩))
      obtain ⟨j0, hj0, hact0⟩ := hhit
      have hscan := scanExec_spec ρ.act x (j0 - t) t ⟨j0 - t, Nat.le_refl _, by
        simpa [Nat.add_sub_of_le hj0] using hact0⟩
      let m := scanExec ρ.act x (j0 - t) t
      have him : t ≤ m := hscan.1
      have hact : ρ.act m = .exec x := hscan.2.1
      have hpre := run_holds hL hG ρ x t (m - t) k hph (halive t ht)
        (fun u h1 _ hbad => hscan.2.2 u h1 (by omega) hbad)
      have hhere : ((ρ.cfg m).st x).phase = .run k := by
        simpa [Nat.add_sub_of_le him] using hpre.1
      have hl' : ((ρ.cfg m).st x).life = .alive := by
        simpa [Nat.add_sub_of_le him] using hpre.2
      have hrun : execRun I (ρ.cfg m) x ((ρ.cfg m).st x) k = ρ.cfg (m + 1) := by
        have hhead := ρ.valid m
        simp [apply, hact, execHead, hl', hhere] at hhead
        exact hhead
      by_cases hempty : k.rest = []
      · have hidle : ((ρ.cfg (m + 1)).st x).phase = .idle := by
          rw [← hrun]
          simp [execRun, hempty, setActor]
        exact ⟨m + 1, Nat.le_trans him (Nat.le_succ _),
          ⟨halive _ (Nat.le_trans ht (Nat.le_trans him (Nat.le_succ m))), hidle⟩⟩
      · have hdrop := exec_drops I hL hG N (ρ.cfg m) (cfg_reachable ρ m) x k hhere hl' hempty
        rw [hrun] at hdrop
        have hlt : phaseFuel (((ρ.cfg (m + 1)).st x).phase) < n := by
          have hold : phaseFuel (((ρ.cfg m).st x).phase) ≤ n := by
            simpa [hhere, hph] using hfuel
          omega
        obtain ⟨j2, hj2, hq⟩ := ih _ hlt (m + 1)
          (Nat.le_trans ht (Nat.le_trans him (Nat.le_succ m))) (Nat.le_refl _)
        exact ⟨j2, Nat.le_trans (Nat.le_trans him (Nat.le_succ m)) hj2, hq⟩
    | parked dst c k =>
      have hkind0 : waitKind ((ρ.cfg t).st x) =
          some (if c then .callReply dst else .blockingSend dst) := by simp [waitKind, hph]
      have hex : ∃ j, t ≤ j ∧ waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x) := by
        cases Classical.em (∃ j, t ≤ j ∧
            waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x)) with
        | inl h => exact h
        | inr hno =>
          have hS : Stuck ρ x t := by
            refine ⟨⟨rfl, by simp [waitKind, hph]⟩, ?_⟩
            intro j hj
            have heq : waitKind ((ρ.cfg j).st x) = waitKind ((ρ.cfg t).st x) := by
              cases Classical.em (waitKind ((ρ.cfg j).st x) = waitKind ((ρ.cfg t).st x)) with
              | inl h => exact h
              | inr h => exact absurd h (fun hne => hno ⟨j, hj, hne⟩)
            exact ⟨heq.symm, by simp [waitKind, hph]⟩
          exact absurd hS (hfree t ht)
      obtain ⟨j0, hj0, hdiff0⟩ := hex
      obtain ⟨j, hj, hpj, hmin⟩ := earliest
        (fun j => t ≤ j ∧ waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x)) j0 t hj0
        ⟨hj0, hdiff0⟩
      obtain ⟨_, hdiff⟩ := hpj
      have hltj : t < j := by
        have hne : j ≠ t := by
          intro heq
          simp [heq, hkind0] at hdiff
        exact Nat.lt_of_le_of_ne hj (fun h => hne h.symm)
      cases c with
      | false =>
        have hbefore : ∀ u, t ≤ u → u < j →
            waitKind ((ρ.cfg u).st x) = some (.blockingSend dst) := by
          intro u hu1 hu2
          have hnot := hmin u hu1 hu2
          have heq : waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x) := by
            cases Classical.em (waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x)) with
            | inl h => exact h
            | inr h => exact absurd (And.intro hu1 h) hnot
          simpa [waitKind, hph] using heq
        have hdrop := send_drops_at I hL ρ x dst k t j hph hltj hbefore
          (by simpa [hkind0] using hdiff)
        have hlt : phaseFuel (((ρ.cfg j).st x).phase) < n := by
          have hold : phaseFuel (((ρ.cfg t).st x).phase) ≤ n := hfuel
          omega
        obtain ⟨j2, hj2, hq⟩ := ih _ hlt j (Nat.le_trans ht (Nat.le_of_lt hltj)) (Nat.le_refl _)
        exact ⟨j2, Nat.le_trans (Nat.le_of_lt hltj) hj2, hq⟩
      | true =>
        have hbeforeC : ∀ u, t ≤ u → u < j →
            waitKind ((ρ.cfg u).st x) = some (.callReply dst) := by
          intro u hu1 hu2
          have hnot := hmin u hu1 hu2
          have heq : waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x) := by
            cases Classical.em (waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x)) with
            | inl h => exact h
            | inr h => exact absurd (And.intro hu1 h) hnot
          simpa [hkind0] using heq
        have hdrop := call_drops_at I hL ρ x dst k t j (Or.inl hph) hltj hbeforeC
          (by simpa [hkind0] using hdiff)
        have hlt : phaseFuel (((ρ.cfg j).st x).phase) < n := by omega
        obtain ⟨j2, hj2, hq⟩ := ih _ hlt j (Nat.le_trans ht (Nat.le_of_lt hltj)) (Nat.le_refl _)
        exact ⟨j2, Nat.le_trans (Nat.le_of_lt hltj) hj2, hq⟩
    | awaitReply dst k =>
      have hkind0 : waitKind ((ρ.cfg t).st x) = some (.callReply dst) := by simp [waitKind, hph]
      have hex : ∃ j, t ≤ j ∧ waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x) := by
        cases Classical.em (∃ j, t ≤ j ∧
            waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x)) with
        | inl h => exact h
        | inr hno =>
          have hS : Stuck ρ x t := by
            refine ⟨⟨rfl, by simp [waitKind, hph]⟩, ?_⟩
            intro j hj
            have heq : waitKind ((ρ.cfg j).st x) = waitKind ((ρ.cfg t).st x) := by
              cases Classical.em (waitKind ((ρ.cfg j).st x) = waitKind ((ρ.cfg t).st x)) with
              | inl h => exact h
              | inr h => exact absurd h (fun hne => hno ⟨j, hj, hne⟩)
            exact ⟨heq.symm, by simp [waitKind, hph]⟩
          exact absurd hS (hfree t ht)
      obtain ⟨j0, hj0, hdiff0⟩ := hex
      obtain ⟨j, hj, hpj, hmin⟩ := earliest
        (fun j => t ≤ j ∧ waitKind ((ρ.cfg j).st x) ≠ waitKind ((ρ.cfg t).st x)) j0 t hj0
        ⟨hj0, hdiff0⟩
      obtain ⟨_, hdiff⟩ := hpj
      have hltj : t < j := by
        have hne : j ≠ t := by
          intro heq
          simp [heq, hkind0] at hdiff
        exact Nat.lt_of_le_of_ne hj (fun h => hne h.symm)
      have hbefore : ∀ u, t ≤ u → u < j → waitKind ((ρ.cfg u).st x) = some (.callReply dst) := by
        intro u hu1 hu2
        have hnot : ¬(t ≤ u ∧ waitKind ((ρ.cfg u).st x) ≠ waitKind ((ρ.cfg t).st x)) := hmin u hu1 hu2
        have heq : waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x) := by
          cases Classical.em (waitKind ((ρ.cfg u).st x) = waitKind ((ρ.cfg t).st x)) with
          | inl h => exact h
          | inr h => exact absurd (And.intro hu1 h) hnot
        simpa [hkind0] using heq
      have hdrop := call_drops_at I hL ρ x dst k t j (Or.inr hph) hltj hbefore
        (by simpa [hkind0] using hdiff)
      have hlt : phaseFuel (((ρ.cfg j).st x).phase) < n := by omega
      obtain ⟨j2, hj2, hq⟩ := ih _ hlt j (Nat.le_trans ht (Nat.le_of_lt hltj)) (Nat.le_refl _)
      exact ⟨j2, Nat.le_trans (Nat.le_of_lt hltj) hj2, hq⟩

/-- A blocking send does not last forever when every actor strictly below the sender
stays idle infinitely often while it remains below. -/
theorem send_stuck_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (s dst : InstId) (i : Nat) (hS : Stuck ρ s i)
    (hkind : waitKind ((ρ.cfg i).st s) = some (.blockingSend dst))
    (hlower : ∀ (t : Nat) (x : InstId), rankAt hs (ρ.cfg t) x < rankAt hs (ρ.cfg i) s →
      (∀ u, t ≤ u → ((ρ.cfg u).st x).life = .alive) →
      (∀ u, t ≤ u → rankAt hs (ρ.cfg u) x < rankAt hs (ρ.cfg i) s) →
      ∀ u, t ≤ u → ∃ j, u ≤ j ∧ Idle (ρ.cfg j) x) : False := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some (.blockingSend dst) := by
    intro j hj
    exact ((hkind.symm.trans (hS.2 j hj).1).symm)
  obtain ⟨k, hph⟩ := blocking_parked ((ρ.cfg i).st s) dst hkind
  have hstay : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst false k := by
    intro t ht
    have hfreeze := blocking_stays I hL ρ s dst k i (t - i) hph
      (fun u hu1 _ => hall u hu1)
    exact ⟨k, by simpa [Nat.add_sub_of_le ht] using hfreeze⟩
  have hM := (inv_reachable I N (ρ.cfg i) hL (cfg_reachable ρ i)).2.1
  obtain ⟨p, hp, hps, _⟩ := hM.bwd s dst false k hph
  have hmail : ((ρ.cfg i).st dst).parked ≠ [] := by
    intro hempty
    simp [hempty] at hp
  have hl0 := mailbox_alive I hL N (ρ.cfg i) (cfg_reachable ρ i) dst hmail
  have halive := alive_while_send I hL hG ρ s dst i hstay hl0
  have hbelow : ∀ u, i ≤ u → rankAt hs (ρ.cfg u) dst < rankAt hs (ρ.cfg i) s := by
    intro u hu
    have hht := send_height_below I hL hG ρ hs hok s dst k i (u - i) hph
      (fun t ht1 _ => hall t ht1)
      (fun t ht1 _ => halive t ht1)
    simpa [Nat.add_sub_of_le hu] using hht.2
  have hidle := hlower i dst (hbelow i (Nat.le_refl _)) halive hbelow
  have hcan : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) dst := by
    intro t
    let u := max t i
    obtain ⟨j, hj, hId⟩ := hidle u (Nat.le_max_right _ _)
    have hj' : i ≤ j := Nat.le_trans (Nat.le_max_right t i) hj
    obtain ⟨k', hk'⟩ := hstay j hj'
    have hMj := (inv_reachable I N (ρ.cfg j) hL (cfg_reachable ρ j)).2.1
    obtain ⟨p', hp', _, _⟩ := hMj.bwd s dst false k' hk'
    have hbox : ((ρ.cfg j).st dst).parked ≠ [] := by
      intro hempty
      simp [hempty] at hp'
    exact ⟨j, Nat.le_trans (Nat.le_max_left _ _) hj, ⟨hId, Or.inr hbox⟩⟩
  have hidx := parkIndex_of_mem ((ρ.cfg i).st dst).parked s ⟨p, hp, hps⟩
  exact parked_forever_false I hL hG ρ hF s dst false (parkIndex ((ρ.cfg i).st dst).parked s) i
    hstay halive (Nat.le_refl _) hidx hcan

/-- A call that stays parked does not last forever when every actor strictly below
the caller stays idle infinitely often while it remains below. -/
theorem call_parked_stuck_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (s dst : InstId) (k : Cont) (i : Nat)
    (hph : ((ρ.cfg i).st s).phase = .parked dst true k)
    (hkind : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some (.callReply dst))
    (hstay : ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst true k)
    (hlower : ∀ (t : Nat) (x : InstId), rankAt hs (ρ.cfg t) x < rankAt hs (ρ.cfg i) s →
      (∀ u, t ≤ u → ((ρ.cfg u).st x).life = .alive) →
      (∀ u, t ≤ u → rankAt hs (ρ.cfg u) x < rankAt hs (ρ.cfg i) s) →
      ∀ u, t ≤ u → ∃ j, u ≤ j ∧ Idle (ρ.cfg j) x) : False := by
  have hM := (inv_reachable I N (ρ.cfg i) hL (cfg_reachable ρ i)).2.1
  obtain ⟨p, hp, hps, _⟩ := hM.bwd s dst true k hph
  have hmail : ((ρ.cfg i).st dst).parked ≠ [] := by
    intro hempty
    simp [hempty] at hp
  have hl0 := mailbox_alive I hL N (ρ.cfg i) (cfg_reachable ρ i) dst hmail
  have halive : ∀ t, i ≤ t → ((ρ.cfg t).st dst).life = .alive := by
    intro t ht
    have hgot := call_callee_alive I hL hG ρ s dst k i (t - i) (Or.inl hph)
      (fun u hu1 _ => hkind u hu1) hl0
    simpa [Nat.add_sub_of_le ht] using hgot
  have hbelow : ∀ u, i ≤ u → rankAt hs (ρ.cfg u) dst < rankAt hs (ρ.cfg i) s := by
    intro u hu
    have hht := call_height_below I hL hG ρ hs hok s dst k i (u - i) (Or.inl hph)
      (fun t ht1 _ => hkind t ht1) hl0
    simpa [Nat.add_sub_of_le hu] using hht.2
  have hidle := hlower i dst (hbelow i (Nat.le_refl _)) halive hbelow
  have hcan : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) dst := by
    intro t
    let u := max t i
    obtain ⟨j, hj, hId⟩ := hidle u (Nat.le_max_right _ _)
    have hj' : i ≤ j := Nat.le_trans (Nat.le_max_right t i) hj
    obtain ⟨k', hk'⟩ := hstay j hj'
    have hMj := (inv_reachable I N (ρ.cfg j) hL (cfg_reachable ρ j)).2.1
    obtain ⟨p', hp', _, _⟩ := hMj.bwd s dst true k' hk'
    have hbox : ((ρ.cfg j).st dst).parked ≠ [] := by
      intro hempty
      simp [hempty] at hp'
    exact ⟨j, Nat.le_trans (Nat.le_max_left _ _) hj, ⟨hId, Or.inr hbox⟩⟩
  have hidx := parkIndex_of_mem ((ρ.cfg i).st dst).parked s ⟨p, hp, hps⟩
  exact parked_forever_false I hL hG ρ hF s dst true (parkIndex ((ρ.cfg i).st dst).parked s) i
    hstay halive (Nat.le_refl _) hidx hcan

/-- A stuck call is admitted. It cannot stay parked, so some later phase is
`awaitReply` on the same continuation, and it stays there while the kind lasts. -/
theorem call_admitted (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (s dst : InstId) (i : Nat) (hS : Stuck ρ s i)
    (hkind : waitKind ((ρ.cfg i).st s) = some (.callReply dst))
    (hlower : ∀ (t : Nat) (x : InstId), rankAt hs (ρ.cfg t) x < rankAt hs (ρ.cfg i) s →
      (∀ u, t ≤ u → ((ρ.cfg u).st x).life = .alive) →
      (∀ u, t ≤ u → rankAt hs (ρ.cfg u) x < rankAt hs (ρ.cfg i) s) →
      ∀ u, t ≤ u → ∃ j, u ≤ j ∧ Idle (ρ.cfg j) x) :
    ∃ j k, i ≤ j ∧ ((ρ.cfg j).st s).phase = .awaitReply dst k ∧
      ∀ t, j ≤ t → ((ρ.cfg t).st s).phase = .awaitReply dst k := by
  have hall : ∀ j, i ≤ j → waitKind ((ρ.cfg j).st s) = some (.callReply dst) := by
    intro j hj
    exact ((hkind.symm.trans (hS.2 j hj).1).symm)
  rcases call_parked_or_await ((ρ.cfg i).st s) dst hkind with ⟨k, hpark⟩ | ⟨k, hawait⟩
  · have hnot : ¬ ∀ t, i ≤ t → ∃ k, ((ρ.cfg t).st s).phase = .parked dst true k := by
      intro hstay
      exact call_parked_stuck_false I hL hG ρ hF hs hok s dst k i hpark hall hstay hlower
    have hex : ∃ t, i ≤ t ∧ ∀ k, ((ρ.cfg t).st s).phase ≠ .parked dst true k := by
      cases Classical.em (∃ t, i ≤ t ∧ ∀ k, ((ρ.cfg t).st s).phase ≠ .parked dst true k) with
      | inl h => exact h
      | inr hno =>
        exact False.elim (hnot (by
          intro t ht
          cases Classical.em (∃ k, ((ρ.cfg t).st s).phase = .parked dst true k) with
          | inl h => exact h
          | inr hnp =>
            exact absurd ⟨t, ht, fun k hk => hnp ⟨k, hk⟩⟩ hno))
    obtain ⟨t0, ht0, hnp⟩ := hex
    obtain ⟨t, ht, hpT, _⟩ := earliest
      (fun t => i ≤ t ∧ ∀ k, ((ρ.cfg t).st s).phase ≠ .parked dst true k) t0 i ht0 ⟨ht0, hnp⟩
    obtain ⟨_, hnpT⟩ := hpT
    have hphase := call_stays I hL ρ s dst k i (t - i) (Or.inl hpark)
      (fun u hu1 _ => hall u hu1)
    have hidx : i + (t - i) = t := Nat.add_sub_of_le ht
    have hhere : CallPhase dst k (((ρ.cfg t).st s).phase) := by simpa [hidx] using hphase
    have hawait : ((ρ.cfg t).st s).phase = .awaitReply dst k := by
      rcases hhere with hpk | haw
      · exact absurd hpk (hnpT k)
      · exact haw
    refine ⟨t, k, ht, hawait, ?_⟩
    intro u hu
    have hfreeze := await_stays I hL ρ s dst k t (u - t) hawait
      (fun v hv1 _ => hall v (Nat.le_trans ht hv1))
    simpa [Nat.add_sub_of_le hu] using hfreeze
  · refine ⟨i, k, Nat.le_refl _, hawait, ?_⟩
    intro u hu
    have hfreeze := await_stays I hL ρ s dst k i (u - i) hawait (fun v hv1 _ => hall v hv1)
    simpa [Nat.add_sub_of_le hu] using hfreeze


/-- That resume is not the same wait: a blocking send at the parked head is over. -/
theorem recv_clears_head_send (I : Impl) (w w' : World) (id : InstId)
    (h : receiveBulk I w id = some w') (p : Parked) (ps : List Parked)
    (hp : (w.st id).parked = p :: ps) (s : InstId) (hs : s = p.sender) (hne : s ≠ id)
    (k : Cont) (hph : (w.st s).phase = .parked id false k) (hc : p.isCall = false) :
    ¬ SameWait (w.st s) (w'.st s) := by
  intro hsame
  have hwas : waitKind (w.st s) = some (.blockingSend id) := by simp [waitKind, hph]
  have hnow := bulk_resumes_send I w w' id h p ps hp s hs hne k hph hc
  have heq := hsame.1
  simp [hwas, hnow] at heq

theorem replyCount_append (xs ys : List Eff) :
    replyCount (xs ++ ys) = replyCount xs + replyCount ys := by
  induction xs with
  | nil => simp [replyCount]
  | cons e es ih =>
    cases e <;> simp [replyCount, ih] <;> omega

theorem terminateBefore_of_head (pre es : List Eff) (hpre : replyCount pre = 0) :
    terminateBeforeReply (pre ++ (.terminate :: es)) = true := by
  induction pre with
  | nil => simp [terminateBeforeReply]
  | cons e rest ih =>
    cases e <;> simp [replyCount, terminateBeforeReply] at hpre ⊢ <;> exact ih hpre

/-- A checked program has one reply and no earlier `terminate`, or no reply at all. -/
theorem program_reply_count (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (t : Template) (ht : templateOf I.desc tr.template = some t) :
    (tr.acceptsCall = true ∧ replyCount tr.program = 1 ∧ terminateBeforeReply tr.program = false) ∨
      (tr.acceptsCall = false ∧ replyCount tr.program = 0) := by
  have hok := transitionOk_of_mem I hL tr hm
  cases hacc : tr.acceptsCall
  · simp only [transitionOk, ht, hacc] at hok
    repeat rw [Bool.and_eq_true] at hok
    exact Or.inr ⟨rfl, beq_iff_eq.mp hok.1.1.2⟩
  · refine Or.inl ⟨?_, (call_program_replies I hL tr hm hacc t ht).1,
      (call_program_replies I hL tr hm hacc t ht).2⟩
    rfl

theorem terminate_suffix_quiet (I : Impl) (hL : LocalOk I) (w : World) (hS : ProgSrc I w)
    (id : InstId) (es : List Eff) (hc : carried ((w.st id).phase) = some (.terminate :: es)) :
    replyCount (.terminate :: es) = 0 := by
  obtain ⟨tr, hm, hname, pre, hpre⟩ := hS id (.terminate :: es) hc
  obtain ⟨t, ht⟩ := src_template I hL w hS id _ hc
  have ht' : templateOf I.desc tr.template = some t := by simpa [hname] using ht
  rcases program_reply_count I hL tr hm t ht' with ⟨_, hcount, hbefore⟩ | ⟨_, hzero⟩
  · have happ := replyCount_append pre (.terminate :: es)
    rw [hpre] at happ
    by_cases hz : replyCount (.terminate :: es) = 0
    · exact hz
    · have hpre0 : replyCount pre = 0 := by
        have hpos : 0 < replyCount (.terminate :: es) := Nat.pos_of_ne_zero hz
        omega
      have hb := terminateBefore_of_head pre es hpre0
      rw [hpre] at hb
      simp [hb] at hbefore
  · have happ := replyCount_append pre (.terminate :: es)
    rw [hpre, hzero] at happ
    omega

theorem reply_head_one (I : Impl) (hL : LocalOk I) (w : World) (hS : ProgSrc I w) (id : InstId)
    (k : Cont) (es : List Eff) (hc : carried ((w.st id).phase) = some k.rest)
    (hrest : k.rest = .reply :: es) : replyCount k.rest = 1 := by
  obtain ⟨tr, hm, hname, pre, hpre⟩ := hS id k.rest hc
  obtain ⟨t, ht⟩ := src_template I hL w hS id _ hc
  have ht' : templateOf I.desc tr.template = some t := by simpa [hname] using ht
  rcases program_reply_count I hL tr hm t ht' with ⟨_, hcount, _⟩ | ⟨_, hzero⟩
  · have happ := replyCount_append pre k.rest
    rw [hpre, hcount, hrest] at happ
    simp [replyCount] at happ
    have hsum : replyCount pre + replyCount es = 0 :=
      Nat.add_right_cancel (by
        show replyCount pre + replyCount es + 1 = 0 + 1
        rw [Nat.add_assoc, Nat.zero_add]
        exact happ.symm)
    have hes : replyCount es = 0 := (Nat.eq_zero_of_add_eq_zero hsum).2
    rw [hrest]
    simp [replyCount, hes]
  · have happ := replyCount_append pre k.rest
    rw [hpre, hzero, hrest] at happ
    simp [replyCount] at happ

/-- A call cannot be sitting in a terminable actor's box. -/
theorem terminable_no_call_box (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hT : CallTagInv w) (id : InstId) (t : Template)
    (ht : templateOf I.desc (tname id) = some t) (hterm : t.terminable = true) (m : Msg)
    (hm : m ∈ (w.st id).box) : m.callFrom = none := by
  cases hc : m.callFrom with
  | none => rfl
  | some c =>
    obtain ⟨k, hph⟩ := box_awaits w hT id m c hm hc
    have hbad := await_callee_unterminable I hL hG N w hR c id k hph t ht
    simp [hterm] at hbad

theorem parked_callfrom_none (w : World) (hT : CallTagInv w) (hM : MailInv w) (id : InstId)
    (p : Parked) (hp : p ∈ (w.st id).parked) (hc : p.isCall = false) : p.msg.callFrom = none := by
  cases hcf : p.msg.callFrom with
  | none => rfl
  | some s =>
    obtain ⟨hs, _, hk⟩ := (hT.parkFrom id p hp s).mp hcf
    obtain ⟨k2, hph⟩ := hM.fwd id p hp
    rw [hc] at hph
    rw [← hs, hph] at hk
    cases hk

theorem tag_of_read (D : Description) (w : World) (id : InstId) (hT : CallTagInv w) :
    CallTagInv (readCells D w id) := by
  apply call_tag_copy w (readCells D w id) hT
  intro i
  simp [readCells_st]

theorem tag_of_refund (w : World) (name : String) (ms : List Msg) (hT : CallTagInv w) :
    CallTagInv (refundMsgs w name ms) := by
  apply call_tag_copy w (refundMsgs w name ms) hT
  intro i
  exact ⟨(refund_life w name ms i).2.2.1, refund_box w name ms i, refund_park w name ms i,
    (refund_life w name ms i).2.2.2⟩

theorem tag_of_refundP (w : World) (name : String) (ps : List Parked) (hT : CallTagInv w) :
    CallTagInv (refundParked w name ps) := by
  apply call_tag_copy w (refundParked w name ps) hT
  intro i
  exact ⟨(refundP_life w name ps i).2.2.1, refundP_box w name ps i, refundP_park w name ps i,
    (refundP_life w name ps i).2.2.2⟩

/-- Killing `terminate`: the mailbox holds no call, the continuation owes no reply,
and plain parked senders are resumed. -/
theorem terminate_tag (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hT : CallTagInv w) (hM : MailInv w) (hS : ProgSrc I w)
    (hTerm : TermOk I w) (id : InstId) (k : Cont) (es : List Eff)
    (hph : (w.st id).phase = .run k) (hrest : k.rest = .terminate :: es) :
    CallTagInv (execRun I w id (w.st id) k) := by
  have hc : carried ((w.st id).phase) = some (.terminate :: es) := by simp [carried, hph, hrest]
  have hcount0 := terminate_suffix_quiet I hL w hS id es hc
  have hname := hTerm id (.terminate :: es) hc (by simp [hasTerminate])
  have hparkF := terminable_no_parked_call I hL hG N w hR id hname
  obtain ⟨t, ht, htm⟩ := hname
  simp [execRun, hrest, ht, htm, hparkF]
  let base := refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
    (tname id) (w.st id).parked
  have hBase : CallTagInv base := by
    simpa [base] using tag_of_refundP _ (tname id) (w.st id).parked
      (tag_of_refund _ (tname id) (w.st id).box (tag_of_read I.desc w id hT))
  have hphB (i : InstId) : (base.st i).phase = (w.st i).phase := by
    simp [base, readCells_st, (refund_life _ _ _ _).2.2.1, (refundP_life _ _ _ _).2.2.1]
  have hboxB (i : InstId) : (base.st i).box = (w.st i).box := by
    simp [base, readCells_st, refund_box, refundP_box]
  have hparkB (i : InstId) : (base.st i).parked = (w.st i).parked := by
    simp [base, readCells_st, refund_park, refundP_park]
  have hquiet (c : InstId) : ¬handlerOwes c (base.st id).phase ∧ ¬replyPending c (base.st id).phase := by
    have hrun : (base.st id).phase = .run k := by rw [hphB, hph]
    constructor
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hrun] at hk0
      cases hk0
      exact not_shape_zero c k (by rw [hrest]; exact hcount0) hs
    · intro ⟨k0, hk0, hs, _⟩
      simp [carriedCont, hrun] at hk0
      cases hk0
      exact not_shape_zero c k (by rw [hrest]; exact hcount0) hs
  have hcallB : ∀ m, m ∈ (base.st id).box → m.callFrom = none := by
    intro m hm
    rw [hboxB] at hm
    exact terminable_no_call_box I hL hG N w hR hT id t ht htm m hm
  have hplainP : ∀ p, p ∈ (w.st id).parked → p.isCall = false := by
    intro p hp
    have hall := by simpa [hasParkedCall, List.any_eq_false] using hparkF
    exact hall p hp
  have hcallP : ∀ p, p ∈ (base.st id).parked → p.msg.callFrom = none := by
    intro p hp
    rw [hparkB] at hp
    exact parked_callfrom_none w hT hM id p hp (hplainP p hp)
  have hClear := idle_clear_tag base id hBase
    (fun d kA hbad => by rw [hphB, hph] at hbad; cases hbad)
    (fun d kA hbad => by rw [hphB, hph] at hbad; cases hbad)
    hquiet hcallB hcallP
  let cleared := setActor base id { (base.st id) with phase := .idle, box := [], prio := [], parked := [] }
  let dead : Actor :=
    { (base.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hDead : CallTagInv (setActor base id dead) := by
    apply call_tag_copy cleared (setActor base id dead) hClear
    intro i
    by_cases hi : i = id <;> simp [cleared, dead, setActor, hi]
  have hstep : ∀ p, p ∈ (w.st id).parked → p.isCall = false ∧
      (p.sender = id ∨ ∃ k, ((setActor base id dead).st p.sender).phase = .parked id false k) := by
    intro p hp
    refine ⟨hplainP p hp, Or.inr ?_⟩
    obtain ⟨kS, hphS⟩ := hM.fwd id p hp
    rw [hplainP p hp] at hphS
    have hne : p.sender ≠ id := by
      intro hs
      rw [hs, hph] at hphS
      cases hphS
    exact ⟨kS, by simp [setActor, hne, hphB, hphS]⟩
  have hrel := release_plain_tag (setActor base id dead) id (w.st id).parked hDead
    (fun p1 p2 h1 h2 heq => (hM.uniq id id p1 p2 h1 h2 heq).2)
    (hM.once id) hstep
  simpa [base, dead] using hrel

theorem exec_tag (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hT : CallTagInv w) (id : InstId) (w' : World)
    (h : execHead I w id = some w') : CallTagInv w' := by
  have hM : MailInv w := (inv_reachable I N w hL hR).2.1
  have hS : ProgSrc I w := prog_src_reachable I N w hR
  have hLane : LaneOk I w := lane_reachable I hL hG N w hR
  have hTerm : TermOk I w := term_ok_reachable I hL N w hR
  unfold execHead at h
  by_cases hlive : (w.st id).life ≠ .alive
  · simp [hlive] at h
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
    | run k =>
      simp [hph] at h
      cases h
      cases hrest : k.rest with
      | nil =>
        simp [execRun, hrest]
        exact run_done_tag w id k hT hph hrest
      | cons e es =>
        cases e with
        | send dst label hint =>
          simp [execRun, hrest]
          cases hroute : route w I.desc dst hint with
          | none =>
            simp
            exact run_tail_tag w id k (.send dst label hint) es hT hph hrest
              (by intro h; cases h) (by intro h; cases h)
          | some dstId =>
            simp
            exact enqueue_send_tag w I.desc id dstId
              { label := label, sender := id, callFrom := none } k (.send dst label hint) es hT hph
              hrest (by intro h; cases h) (by intro h; cases h) rfl
        | trySend dst label hint =>
          simp [execRun, hrest]
          cases hroute : route w I.desc dst hint with
          | none =>
            simp
            exact run_tail_tag w id k (.trySend dst label hint) es hT hph hrest
              (by intro h; cases h) (by intro h; cases h)
          | some dstId =>
            simp
            split
            · next hgo =>
              have htag := enqueue_send_tag w I.desc id dstId
                { label := label, sender := id, callFrom := none } k (.trySend dst label hint) es hT
                hph hrest (by intro h; cases h) (by intro h; cases h) rfl
              have hliveD : (w.st dstId).life = .alive := hgo.1.1
              have hempty : (w.st dstId).parked = [] := hgo.1.2
              have hcap : (w.st dstId).box.length < capBulk I.desc w.N dstId := hgo.2
              by_cases hsame : id = dstId
              · have hliveS : (w.st id).life = .alive := by
                  have h := hliveD
                  rwa [← hsame] at h
                have hemptyS : (w.st id).parked = [] := by
                  have h := hempty
                  rwa [← hsame] at h
                have hcapS : (w.st id).box.length < capBulk I.desc w.N id := by
                  have h := hcap
                  rwa [← hsame] at h
                rw [← hsame] at htag
                rw [enqueue_room_self_send w I.desc id { label := label, sender := id, callFrom := none }
                  (afterHead k) hliveS hemptyS hcapS] at htag
                rw [← hsame]
                rw [setActor_same]
                simp [setActor_self]
                rw [setActor_same]
                exact htag
              · have hflip : ¬ dstId = id := fun h => hsame h.symm
                rw [enqueue_room_other_send w I.desc id dstId
                  { label := label, sender := id, callFrom := none } (afterHead k) hliveD hsame hempty hcap] at htag
                simp only [setActor, chargeSender, bumpToken, proceed, hflip, hsame] at htag ⊢
                have hdead {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b c d : α) :
                    (if p then a else if q then b else if p then c else d) =
                      if p then a else if q then b else d := by
                  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
                simpa [hdead] using htag
            · exact run_tail_tag w id k (.trySend dst label hint) es hT hph hrest
                (by intro h; cases h) (by intro h; cases h)
        | call dst label hint =>
          simp [execRun, hrest]
          cases hroute : route w I.desc dst hint with
          | none =>
            simp
            exact run_tail_tag w id k (.call dst label hint) es hT hph hrest
              (by intro h; cases h) (by intro h; cases h)
          | some dstId =>
            simp
            exact enqueue_call_tag w I.desc id dstId
              { label := label, sender := id, callFrom := some id } k (.call dst label hint) es hT hM
              hph hrest (by intro h; cases h) (by intro h; cases h) rfl
        | reply =>
          simp [execRun, hrest]
          have hcry : carried ((w.st id).phase) = some k.rest := by simp [carried, hph]
          exact reply_tag w id k es hT hph hrest (reply_head_one I hL w hS id k es hcry hrest)
        | selfSchedule label =>
          exact schedule_tag I w hT id k label es hph hrest (fun hfresh =>
            by
              obtain ⟨t, ht⟩ := src_template I hL w hS id (.selfSchedule label :: es)
                (by simp [carried, hph, hrest])
              exact lane_has_room I hL hG w.N w hLane id t ht label
                (sched_declared I w hS id _ (by simp [carried, hph, hrest]) label
                  (self_head_label label es)) hfresh)
        | cell dst label value =>
          simp [execRun, hrest]
          have hCell : CallTagInv (setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }) := by
            apply call_tag_copy w _ hT
            intro i
            simp [setCell]
          have hRun := run_tail_tag
            (setCell w dst label { value := max (w.cell dst label).value value, dirty := true })
            id k (.cell dst label value) es hCell (by simp [setCell, hph]) hrest
            (by intro h; cases h) (by intro h; cases h)
          by_cases hdirty : (w.cell dst label).dirty = true
          · simp [hdirty]
            exact hRun
          · simp [hdirty]
            exact wake_readers_tag I.desc _ dst label id (readersOf _ dst) hRun
        | internal =>
          simp [execRun, hrest]
          exact carry_step_tag w id k (.internal) es (.awaitEffect (afterHead k)) hT hph hrest
            (by intro h; cases h) (by intro h; cases h) (by simp [carriedCont])
            (by intro d kA hbad; cases hbad) (by intro d kA hbad; cases hbad)
        | peer =>
          simp [execRun, hrest]
          exact carry_step_tag w id k (.peer) es (.awaitPeer (afterHead k)) hT hph hrest
            (by intro h; cases h) (by intro h; cases h) (by simp [carriedCont])
            (by intro d kA hbad; cases hbad) (by intro d kA hbad; cases hbad)
        | terminate =>
          exact terminate_tag I hL hG N w hR hT hM hS hTerm id k es hph hrest

theorem call_tag_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : CallTagInv w := by
  induction hR with
  | init => exact call_tag_init I N
  | step w w' a prev happ ih =>
    cases a with
    | finish id =>
      exact finish_tag w id w' ih (by simpa [apply] using happ)
    | spawn template =>
      exact spawn_tag I w template w' (inv_reachable I N w hL prev).2.2
        (inv2_reachable I hL hG N w prev).2.1 ih (by simpa [apply] using happ)
    | recvPrio id =>
      exact prio_tag I w id w' ih (by simpa [apply] using happ)
    | recvBulk id =>
      exact recvBulk_tag I hL w w' id (inv_reachable I N w hL prev).2.1 ih
        (by simpa [apply] using happ)
    | exec id =>
      exact exec_tag I hL hG N w prev ih id w' (by simpa [apply] using happ)

/-- Index of the first bulk message that names `c`, or the length when there is none. -/
def callPos : List Msg → InstId → Nat
  | [], _ => 0
  | m :: ms, c => if m.callFrom = some c then 0 else callPos ms c + 1

theorem callPos_head (m : Msg) (ms : List Msg) (c : InstId) (hc : m.callFrom = some c) :
    callPos (m :: ms) c = 0 := by
  simp [callPos, hc]

theorem callPos_skip (m : Msg) (ms : List Msg) (c : InstId) (hne : m.callFrom ≠ some c) :
    callPos (m :: ms) c = callPos ms c + 1 := by
  simp [callPos, hne]

theorem callPos_append (ms extra : List Msg) (c : InstId) (h : callPos ms c < ms.length) :
    callPos (ms ++ extra) c = callPos ms c := by
  induction ms with
  | nil => simp [callPos] at h
  | cons m ms ih =>
    by_cases hc : m.callFrom = some c
    · simp [callPos, hc]
    · have hlt : callPos ms c < ms.length := by
        simp [callPos, hc, List.length] at h
        omega
      simp [callPos, hc, ih hlt]

theorem callPos_mem (ms : List Msg) (c : InstId) (h : callPos ms c < ms.length) :
    ∃ m, m ∈ ms ∧ m.callFrom = some c := by
  induction ms with
  | nil => simp [callPos] at h
  | cons m ms ih =>
    by_cases hc : m.callFrom = some c
    · exact ⟨m, List.Mem.head _, hc⟩
    · have hlt : callPos ms c < ms.length := by
        simp [callPos, hc, List.length] at h
        omega
      obtain ⟨m', hm, hc'⟩ := ih hlt
      exact ⟨m', List.Mem.tail _ hm, hc'⟩

theorem mem_call_pos (ms : List Msg) (m : Msg) (c : InstId) (hm : m ∈ ms) (hc : m.callFrom = some c) :
    callPos ms c < ms.length := by
  induction ms with
  | nil => cases hm
  | cons x xs ih =>
    cases hm with
    | head => simp [callPos, hc, List.length]
    | tail _ ht =>
      by_cases hx : x.callFrom = some c
      · simp [callPos, hx, List.length]
      · have hlt := ih ht
        simp [callPos, hx, List.length] at hlt ⊢
        omega

theorem countParkedCall_none (ps : List Parked) (c : InstId)
    (h : ∀ p, p ∈ ps → p.msg.callFrom ≠ some c) : countParkedCall ps c = 0 := by
  induction ps with
  | nil => simp [countParkedCall]
  | cons p ps ih =>
    have hp := h p (List.Mem.head _)
    simp [countParkedCall, hp, ih (fun q hq => h q (List.Mem.tail _ hq))]

/-- A caller in `awaitReply` has its call in the box, not in the parked list. -/
theorem await_mail_in_box (w : World) (hT : CallTagInv w) (c d : InstId) (k : Cont)
    (hph : (w.st c).phase = .awaitReply d k) (hmail : mailCall w d c) :
    callPos (w.st d).box c < (w.st d).box.length ∧
      ∀ p, p ∈ (w.st d).parked → p.msg.callFrom ≠ some c := by
  have hno (p) (hp : p ∈ (w.st d).parked) : p.msg.callFrom ≠ some c := by
    intro hc
    obtain ⟨_, _, hk⟩ := (hT.parkFrom d p hp c).mp hc
    simp [hph] at hk
  refine ⟨?_, hno⟩
  rcases hmail with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
  · exact mem_call_pos (w.st d).box m c hm hc
  · exact absurd hc (hno p hp)

/-- One bulk receive of a callee that still holds the call either installs the
handler or moves that message strictly closer to the head of the box. -/
theorem recv_box_progress (I : Impl) (hL : LocalOk I) (w w' : World) (d c : InstId) (k : Cont)
    (h : receiveBulk I w d = some w') (hM : MailInv w) (hT : CallTagInv w)
    (hph : (w.st c).phase = .awaitReply d k)
    (hpos : callPos (w.st d).box c < (w.st d).box.length) :
    ((w'.st c).phase = .awaitReply d k ∧ ¬mailCall w' d c ∧
        (handlerOwes c (w'.st d).phase ∨ replyPending c (w'.st d).phase)) ∨
      ((w'.st c).phase = .awaitReply d k ∧ mailCall w' d c ∧
        callPos (w'.st d).box c < callPos (w.st d).box c) := by
  have hlive : (w.st d).life = .alive := by
    by_cases hl : (w.st d).life = .alive
    · exact hl
    · have hready : (w.st d).life ≠ .alive ∨ (w.st d).phase ≠ .idle := Or.inl hl
      simp [receiveBulk, hready] at h
  have hidle : (w.st d).phase = .idle := by
    by_cases hp : (w.st d).phase = .idle
    · exact hp
    · have hready : (w.st d).life ≠ .alive ∨ (w.st d).phase ≠ .idle := Or.inr hp
      simp [receiveBulk, hready] at h
  have hcne : c ≠ d := by
    intro heq
    rw [heq] at hph
    simp [hidle] at hph
  have hnoP (p) (hp : p ∈ (w.st d).parked) : p.msg.callFrom ≠ some c := by
    intro hc
    obtain ⟨_, _, hk⟩ := (hT.parkFrom d p hp c).mp hc
    simp [hph] at hk
  unfold receiveBulk at h
  have hready : ¬((w.st d).life ≠ .alive ∨ (w.st d).phase ≠ .idle) := by
    intro hbad
    simp [hbad] at h
  simp [hready] at h
  cases hbox : (w.st d).box with
  | nil => simp [callPos, hbox] at hpos
  | cons m ms =>
    cases hpark : (w.st d).parked with
    | nil =>
      simp [hbox, hpark] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        injection h with hw
        have hdel' : deliver I w d ({ (w.st d) with box := ms }) m = some (w1, a1) := by
          simpa [hpark] using hdel
        have hst (i) : w1.st i = w.st i := deliver_st I w d _ m w1 a1 i hdel'
        by_cases hc : m.callFrom = some c
        · have hcall := deliver_call I hL w d ({ (w.st d) with box := ms }) m w1 a1 c hdel' hc
          obtain ⟨kH, hrun, hshape, _, _⟩ := hcall.2.2.2
          have hzero : countCall ms c = 0 := by
            have hs := hT.sole d c
            unfold soleCall at hs
            rw [hbox, hpark, count_some m ms c hc] at hs
            simp [countParkedCall] at hs
            omega
          have hphC : (w'.st c).phase = .awaitReply d k := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender c).2.2.1
            simpa [setActor, hcne, hst c, hph] using hcr
          have hphD : (w'.st d).phase = .run kH := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender d).2.2.1
            simpa [setActor, hrun] using hcr
          have hbox' : (w'.st d).box = ms := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender d).1
            simpa [setActor, hcall.1] using hcr
          have hpark' : (w'.st d).parked = [] := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender d).2.1
            simpa [setActor, hcall.2.1, hpark] using hcr
          have hnoB : ∀ x, x ∈ (w'.st d).box → x.callFrom ≠ some c := by
            intro x hx
            rw [hbox'] at hx
            exact count_zero_mem ms c hzero x hx
          refine Or.inl ⟨hphC, ?_, ?_⟩
          · intro hbad
            rcases hbad with ⟨x, hx, hc'⟩ | ⟨p, hp, hc'⟩
            · exact hnoB x hx hc'
            · simp [hpark'] at hp
          · have hduty : handlerOwes c a1.phase ∨ replyPending c a1.phase := by
              cases hrest : kH.rest with
              | nil =>
                have hc1 := hshape.2.1
                simp [replyCount, hrest] at hc1
              | cons e es =>
                by_cases he : e = .reply
                · exact Or.inr ⟨kH, by simp [carriedCont, hrun], hshape,
                    by simp [nextIsReply, hrest, he]⟩
                · exact Or.inl ⟨kH, by simp [carriedCont, hrun], hshape, by
                    cases e <;> simp [nextIsReply, hrest] at he ⊢⟩
            simpa [hphD, hrun] using hduty
        · have hboxA : a1.box = ms := by
            cases hcf : m.callFrom with
            | none =>
              exact (deliver_plain I w d ({ (w.st d) with box := ms }) m w1 a1 hdel' hcf).1
            | some s =>
              exact (deliver_call I hL w d ({ (w.st d) with box := ms }) m w1 a1 s hdel' hcf).1
          have hposT : callPos ms c < ms.length := by
            simp [callPos, hc, hbox] at hpos
            omega
          have hphC : (w'.st c).phase = .awaitReply d k := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender c).2.2.1
            simpa [setActor, hcne, hst c, hph] using hcr
          have hbox' : (w'.st d).box = ms := by
            rw [← hw]
            have hcr := (credit_same (setActor w1 d a1) (tname d) m.sender d).1
            simpa [setActor, hboxA] using hcr
          refine Or.inr ⟨hphC, ?_, ?_⟩
          · obtain ⟨m', hm', hc'⟩ := callPos_mem ms c hposT
            exact Or.inl ⟨m', by rw [hbox']; exact hm', hc'⟩
          · rw [hbox']
            simp [callPos, hc]
    | cons p ps =>
      simp [hbox, hpark] at h
      split at h
      · cases h
      · next w1 a1 hdel =>
        injection h with hw
        have hdel' : deliver I w d ({ (w.st d) with box := ms }) m = some (w1, a1) := by
          simpa [hpark] using hdel
        have hst (i) : w1.st i = w.st i := deliver_st I w d _ m w1 a1 i hdel'
        have hpmem : p ∈ (w.st d).parked := by simp [hpark]
        have hsnd : p.sender ≠ d := by
          intro heq
          obtain ⟨_, hkS⟩ := hM.fwd d p hpmem
          rw [heq] at hkS
          simp [hidle] at hkS
        have hsc : p.sender ≠ c := by
          intro heq
          obtain ⟨_, hkS⟩ := hM.fwd d p hpmem
          rw [heq] at hkS
          simp [hph] at hkS
        have hmsg : p.msg.callFrom ≠ some c := hnoP p hpmem
        have hflipC : ¬ c = p.sender := fun h => hsc h.symm
        have hflipD : ¬ d = p.sender := fun h => hsnd h.symm
        by_cases hc : m.callFrom = some c
        · have hcall := deliver_call I hL w d ({ (w.st d) with box := ms }) m w1 a1 c hdel' hc
          obtain ⟨kH, hrun, hshape, _, _⟩ := hcall.2.2.2
          have hzero : countCall ms c = 0 := by
            have hs := hT.sole d c
            unfold soleCall at hs
            rw [hbox, hpark, count_some m ms c hc] at hs
            have hpk : countParkedCall (p :: ps) c = 0 :=
              countParkedCall_none (p :: ps) c (fun q hq => hnoP q (by simpa [hpark] using hq))
            simp [hpk] at hs
            omega
          have hadm :
              ((setActor w1 d { a1 with box := a1.box ++ [p.msg], parked := ps }).st d).phase =
                .run kH ∧
              ((setActor w1 d { a1 with box := a1.box ++ [p.msg], parked := ps }).st d).box =
                ms ++ [p.msg] ∧
              ((setActor w1 d { a1 with box := a1.box ++ [p.msg], parked := ps }).st d).parked = ps := by
            simp [setActor, hrun, hcall.1]
          -- The final world resumes the parked sender, who is neither the callee nor the caller.
          have hphC : (w'.st c).phase = .awaitReply d k := by
            rw [← hw]
            simp [setActor, hflipC, credit_same, hcne, hst c, hph]
          have hphD : (w'.st d).phase = .run kH := by
            rw [← hw]
            simp [setActor, hflipD, credit_same]
            exact hrun
          have hbox' : (w'.st d).box = ms ++ [p.msg] := by
            rw [← hw]
            simp [setActor, hflipD, credit_same]
            rw [hcall.1]
          have hpark' : (w'.st d).parked = ps := by
            rw [← hw]
            simp [setActor, hflipD, credit_same]
          have hnoB : ∀ x, x ∈ (w'.st d).box → x.callFrom ≠ some c := by
            intro x hx
            rw [hbox'] at hx
            have hx' : x ∈ ms ∨ x ∈ [p.msg] := by simpa [List.mem_append] using hx
            rcases hx' with hx' | hx'
            · exact count_zero_mem ms c hzero x hx'
            · simp at hx'
              rw [hx']
              exact hmsg
          have hnoQ : ∀ q, q ∈ (w'.st d).parked → q.msg.callFrom ≠ some c := by
            intro q hq
            rw [hpark'] at hq
            exact hnoP q (by rw [hpark]; exact List.Mem.tail _ hq)
          refine Or.inl ⟨hphC, ?_, ?_⟩
          · intro hbad
            rcases hbad with ⟨x, hx, hc'⟩ | ⟨q, hq, hc'⟩
            · exact hnoB x hx hc'
            · exact hnoQ q hq hc'
          · rw [hphD]
            cases hrest : kH.rest with
            | nil =>
              have hc1 := hshape.2.1
              simp [replyCount, hrest] at hc1
            | cons e es =>
              by_cases he : e = .reply
              · exact Or.inr ⟨kH, by simp [carriedCont], hshape,
                  by simp [nextIsReply, hrest, he]⟩
              · exact Or.inl ⟨kH, by simp [carriedCont], hshape, by
                  cases e <;> simp [nextIsReply, hrest] at he ⊢⟩
        · have hboxA : a1.box = ms := by
            cases hcf : m.callFrom with
            | none =>
              exact (deliver_plain I w d ({ (w.st d) with box := ms }) m w1 a1 hdel' hcf).1
            | some s =>
              exact (deliver_call I hL w d ({ (w.st d) with box := ms }) m w1 a1 s hdel' hcf).1
          have hposT : callPos ms c < ms.length := by
            simp [callPos, hc, hbox] at hpos
            omega
          have hadm :
              ((setActor w1 d { a1 with box := a1.box ++ [p.msg], parked := ps }).st d).box =
                ms ++ [p.msg] := by
            simp [setActor, hboxA]
          have hphC : (w'.st c).phase = .awaitReply d k := by
            rw [← hw]
            simp [setActor, hflipC, credit_same, hcne, hst c, hph]
          have hbox' : (w'.st d).box = ms ++ [p.msg] := by
            rw [← hw]
            simp [setActor, hflipD, credit_same]
            rw [hboxA]
          have hposA : callPos (ms ++ [p.msg]) c = callPos ms c :=
            callPos_append ms [p.msg] c hposT
          refine Or.inr ⟨hphC, ?_, ?_⟩
          · unfold mailCall
            rw [hbox']
            have hlen : (ms ++ [p.msg]).length = ms.length + 1 := by simp
            exact Or.inl (callPos_mem (ms ++ [p.msg]) c (by rw [hposA, hlen]; omega))
          · simp [hbox', hposA, callPos, hc]

theorem charge_box (a : Actor) (name : String) : (chargeSender a name).box = a.box := by
  simp [chargeSender, bumpToken]

/-- A bulk mailbox grows only by keeping its messages and appending behind them. -/
def BoxGrow (old new : List Msg) : Prop :=
  new = old ∨ ∃ m, new = old ++ [m]

theorem call_grow (old new : List Msg) (c : InstId) (h : BoxGrow old new)
    (hin : callPos old c < old.length) :
    callPos new c = callPos old c ∧ callPos new c < new.length := by
  rcases h with h | ⟨m, h⟩
  · rw [h]
    exact ⟨rfl, hin⟩
  · rw [h, callPos_append old [m] c hin, List.length_append]
    refine ⟨rfl, ?_⟩
    simp
    omega

/-- Enqueue appends to the target box or leaves every box alone. -/
theorem enqueue_box (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    BoxGrow ((w.st i).box) ((enqueueOrPark w D sender dst msg isCall k).st i).box := by
  unfold enqueueOrPark
  by_cases hlive : (w.st dst).life = .alive
  · simp [hlive]
    by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · simp [hroom]
      cases isCall
      · by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            simp [setActor, charge_box, proceed_box]
            exact Or.inr ⟨msg, rfl⟩
          · simp [setActor, hi]
            exact Or.inl rfl
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, charge_box, proceed_box]
            rw [if_neg hflip]
            exact Or.inr ⟨msg, rfl⟩
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              simp [setActor, hi, charge_box, proceed_box]
              exact Or.inl rfl
            · rw [if_neg hsame]
              simp [setActor, hi, his]
              exact Or.inl rfl
      · by_cases hsame : sender = dst
        · rw [hsame]
          by_cases hi : i = dst
          · rw [hi]
            simp [setActor, charge_box]
            exact Or.inr ⟨msg, rfl⟩
          · simp [setActor, hi]
            exact Or.inl rfl
        · by_cases hi : i = dst
          · rw [hi, if_neg hsame]
            have hflip : ¬ dst = sender := fun h => hsame h.symm
            simp [setActor, charge_box]
            rw [if_neg hflip]
            exact Or.inr ⟨msg, rfl⟩
          · by_cases his : i = sender
            · rw [his, if_neg hsame]
              simp [setActor, hi, charge_box]
              exact Or.inl rfl
            · rw [if_neg hsame]
              simp [setActor, hi, his]
              exact Or.inl rfl
    · simp [hroom]
      by_cases hsame : sender = dst
      · rw [hsame]
        by_cases hi : i = dst
        · rw [hi]
          simp [setActor, charge_box]
          exact Or.inl rfl
        · simp [setActor, hi]
          exact Or.inl rfl
      · by_cases hi : i = dst
        · rw [if_neg hsame, hi]
          have hflip : ¬ dst = sender := fun h => hsame h.symm
          simp [setActor, charge_box]
          rw [if_neg hflip]
          exact Or.inl rfl
        · by_cases his : i = sender
          · rw [his, if_neg hsame]
            simp [setActor, hi, charge_box]
            exact Or.inl rfl
          · rw [if_neg hsame]
            simp [setActor, hi, his]
            exact Or.inl rfl
  · simp [hlive]
    by_cases hi : i = sender
    · rw [hi]
      simp [setActor, proceed_box]
      exact Or.inl rfl
    · simp [setActor, hi]
      exact Or.inl rfl

theorem box_actor (w : World) (id : InstId) (a : Actor) (mb : InstId)
    (h : a.box = (w.st id).box) :
    BoxGrow ((w.st mb).box) ((setActor w id a).st mb).box := by
  by_cases hmb : mb = id
  · rw [hmb, setActor_self, h]
    exact Or.inl rfl
  · rw [setActor_other w id mb a hmb]
    exact Or.inl rfl

theorem finish_box (w w' : World) (id i : InstId) (h : finishWait w id = some w') :
    (w'.st i).box = (w.st i).box := by
  unfold finishWait at h
  split at h
  · cases h
    by_cases hi : i = id <;> simp [setActor, hi, proceed_box]
  · cases h
    by_cases hi : i = id <;> simp [setActor, hi, proceed_box]
  · cases h

theorem deliver_box (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : a1.box = a.box := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        rfl
    · split at h
      · cases h
      · cases h
        split <;> rfl

theorem prio_box (I : Impl) (w w' : World) (id i : InstId) (h : receivePrio I w id = some w') :
    (w'.st i).box = (w.st i).box := by
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      have hbx := deliver_box I w id ({ (w.st id) with prio := ms }) m w1 a1 hdel
      have hst := deliver_st I w id _ m w1 a1 i hdel
      by_cases hi : i = id
      · rw [hi]
        simp [setActor, hbx]
      · simp [setActor, hi, hst]

/-- A bulk receive of someone else does not change this mailbox. -/
theorem bulk_other_box (I : Impl) (w w' : World) (j i : InstId)
    (h : receiveBulk I w j = some w') (hne : i ≠ j) :
    (w'.st i).box = (w.st i).box := by
  unfold receiveBulk at h
  by_cases hready : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st j).box with
    | nil =>
      cases hpark : (w.st j).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w j _ p.msg w1 a1 i hdel
          by_cases hs : i = p.sender
          · have hnj : p.sender ≠ j := fun h => hne (hs.trans h)
            rw [hs] at hst ⊢
            simp [setActor_self, resume_box, credit_box]
            rw [setActor_other w1 j p.sender a1 hnj]
            exact congrArg (·.box) hst
          · simp [setActor_other (creditSender (setActor w1 j a1) (tname j) p.msg.sender) p.sender i _ hs,
              credit_box, setActor_other w1 j i a1 hne, hst]
    | cons m ms =>
      cases hpark : (w.st j).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := deliver_st I w j _ m w1 a1 i hdel
          rw [credit_box]
          simp [setActor, hne, hst]
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hst := deliver_st I w j _ m w1 a1 i hdel
          by_cases hs : i = p.sender
          · have hnj : p.sender ≠ j := fun h => hne (hs.trans h)
            rw [hs] at hst ⊢
            simp [setActor_self, resume_box, credit_box, admitted]
            rw [setActor_other w1 j p.sender admitted hnj]
            exact congrArg (·.box) hst
          · simp [admitted, setActor_other (creditSender (setActor w1 j admitted) (tname j) m.sender)
              p.sender i _ hs, credit_box, setActor_other w1 j i admitted hne, hst]

theorem release_box (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hskip : (p.isCall || decide (p.sender = id)) = true
    · rw [if_pos hskip]
      exact ih w
    · rw [if_neg hskip]
      have hmid := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      have hset : ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i).box =
          (w.st i).box := by
        by_cases hi : i = p.sender
        · rw [hi]
          simp [setActor, resume_box]
        · simp [setActor, hi]
      rw [hset] at hmid
      exact hmid

theorem try_wake_box (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) : ((tryWake D w dstId label writer).st i).box = (w.st i).box := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_box (D : Description) (ids : List InstId) (w : World) (label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).box = (w.st i).box := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (try_wake_box D w j label writer i)

/-- One execution step appends to a mailbox or leaves it. Killing the mailbox
owner is excluded: that actor is not alive afterwards. -/
theorem exec_box (I : Impl) (w : World) (id : InstId) (k : Cont) (mb : InstId)
    (hlive : ((execRun I w id (w.st id) k).st mb).life = .alive) :
    BoxGrow ((w.st mb).box) ((execRun I w id (w.st id) k).st mb).box := by
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil =>
      simpa [execRun] using box_actor w id { (w.st id) with phase := .idle, typestate := toState } mb rfl
    | cons e tail =>
      cases e with
      | send dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using box_actor w id (proceed (w.st id)
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
        | some dstId =>
          simpa [hr] using enqueue_box w I.desc id dstId
            { label := label, sender := id, callFrom := none } false
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) mb
      | call dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using box_actor w id (proceed (w.st id)
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
        | some dstId =>
          simpa [hr] using enqueue_box w I.desc id dstId
            { label := label, sender := id, callFrom := some id } true
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) mb
      | internal =>
        simpa [execRun] using box_actor w id
          { (w.st id) with phase := .awaitEffect (afterHead ⟨.internal :: tail, toState, replyTo⟩) }
          mb rfl
      | peer =>
        simpa [execRun] using box_actor w id
          { (w.st id) with phase := .awaitPeer (afterHead ⟨.peer :: tail, toState, replyTo⟩) }
          mb rfl
      | selfSchedule label =>
        simp only [execRun]
        by_cases hany : ((w.st id).prio.any fun p => p.label == label) = true
        · simpa [hany] using box_actor w id (proceed (w.st id)
            (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
        · by_cases hlt : (w.st id).prio.length < capPrio I.desc w.N id
          · simpa [hany, hlt] using box_actor w id (proceed { (w.st id) with
              prio := upsertPrio (w.st id).prio { label := label, sender := id, callFrom := none } }
              (afterHead ⟨.selfSchedule label :: tail, toState, replyTo⟩)) mb (by simp [proceed_box])
          · simpa [hany, hlt] using box_actor w id { (w.st id) with phase := .crashed } mb rfl
      | trySend dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simpa [hr] using box_actor w id (proceed (w.st id)
            (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
        | some dstId =>
          simp only [hr]
          split
          · by_cases hmb : mb = id
            · rw [hmb]
              by_cases hd : dstId = id
              · rw [hd]
                simp [setActor, charge_box, proceed_box]
                exact Or.inr ⟨{ label := label, sender := id, callFrom := none }, rfl⟩
              · have hflip : ¬ id = dstId := fun h => hd h.symm
                simp [setActor, charge_box, proceed_box]
                rw [if_neg hflip]
                exact Or.inl rfl
            · by_cases hd : mb = dstId
              · rw [hd]
                have hne : dstId ≠ id := fun h => hmb (hd.trans h)
                simp [setActor, hne, charge_box]
                exact Or.inr ⟨{ label := label, sender := id, callFrom := none }, rfl⟩
              · simp [setActor, hmb, hd]
                exact Or.inl rfl
          · exact box_actor w id (proceed (w.st id)
              (afterHead ⟨.trySend dst label hint :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
      | reply =>
        simp only [execRun]
        unfold performReply
        cases hto : replyTo with
        | none =>
          simpa [hto] using box_actor w id (proceed (w.st id)
            (afterHead ⟨.reply :: tail, toState, replyTo⟩)) mb (proceed_box _ _)
        | some caller =>
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            by_cases hd : dst = id
            · simp [hto, hcall, hd]
              by_cases hmb : mb = id
              · rw [hmb]
                by_cases hc : caller = id
                · rw [hc]
                  simp [setActor, proceed_box]
                  exact Or.inl rfl
                · have hflip : ¬ id = caller := fun h => hc h.symm
                  simp [setActor, proceed_box]
                  rw [if_neg hflip]
                  exact Or.inl rfl
              · by_cases hc : mb = caller
                · rw [hc]
                  have hne : ¬ caller = id := fun h => hmb (hc.trans h)
                  simp [setActor, hne, proceed_box]
                  exact Or.inl rfl
                · simp [setActor, hmb, hc]
                  exact Or.inl rfl
            · simpa [hto, hcall, hd] using box_actor w id (proceed (w.st id)
                (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | idle =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | run _ =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | awaitEffect _ =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | awaitPeer _ =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | parked _ _ _ =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
          | crashed =>
            simpa [hto, hcall] using box_actor w id (proceed (w.st id)
              (afterHead ⟨.reply :: tail, toState, some caller⟩)) mb (proceed_box _ _)
      | cell dst label value =>
        simp only [execRun]
        cases hdirty : (w.cell dst label).dirty
        · simp [hdirty, wakeReaders]
          rw [wakes_box]
          exact box_actor (setCell w dst label
            { value := max (w.cell dst label).value value, dirty := true }) id
            (proceed ((setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }).st id)
              (afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩)) mb
            (by simpa [setCell] using proceed_box _ _)
        · simp [hdirty]
          exact box_actor (setCell w dst label
            { value := max (w.cell dst label).value value, dirty := true }) id
            (proceed ((setCell w dst label
              { value := max (w.cell dst label).value value, dirty := true }).st id)
              (afterHead ⟨.cell dst label value :: tail, toState, replyTo⟩)) mb
            (by simpa [setCell] using proceed_box _ _)
      | terminate =>
        simp only [execRun]
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simp [htpl]
          exact Or.inl rfl
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill]
            by_cases hmb : mb = id
            · exfalso
              rw [hmb] at hlive
              simp [execRun, htpl, hkill] at hlive
              rw [release_life_self] at hlive
              simp [setActor] at hlive
            · have hbase : ∀ i, ((refundParked (refundMsgs (readCells I.desc w id) (tname id)
                  (w.st id).box) (tname id) (w.st id).parked).st i).box = (w.st i).box := by
                intro i
                rw [refundP_box, refund_box, readCells_st]
              rw [release_box, setActor_other _ id mb _ hmb, hbase]
              exact Or.inl rfl
          · simp [htpl, hkill]
            exact Or.inl rfl

/-- A step other than this callee's bulk receive appends to its box or leaves the
box alone, so a call already in the box keeps its position. The call leaves the
box only when that receive delivers it. -/
theorem box_pos_mono (I : Impl) (a : Action) (w w' : World) (h : apply I a w = some w')
    (hOcc : OccInv I w) (d c : InstId)
    (hnot : a ≠ .recvBulk d) (halive : (w'.st d).life = .alive)
    (hpos : callPos (w.st d).box c < (w.st d).box.length) :
    callPos (w'.st d).box c = callPos (w.st d).box c ∧
      callPos (w'.st d).box c < (w'.st d).box.length := by
  have hgrow : BoxGrow (w.st d).box (w'.st d).box := by
    cases a with
    | recvBulk id =>
      have hid : id ≠ d := by
        intro heq
        exact hnot (by simp [heq])
      exact Or.inl (bulk_other_box I w w' id d (by simpa [apply] using h) hid.symm)
    | recvPrio id =>
      exact Or.inl (prio_box I w w' id d (by simpa [apply] using h))
    | finish id =>
      exact Or.inl (finish_box w w' id d (by simpa [apply] using h))
    | exec id =>
      simp only [apply] at h
      unfold execHead at h
      by_cases hrun : (w.st id).life = .alive
      · simp [hrun] at h
        cases hphase : (w.st id).phase with
        | run k =>
          simp [hphase] at h
          cases h
          exact exec_box I w id k d halive
        | idle => simp [hphase] at h
        | parked _ _ _ => simp [hphase] at h
        | awaitReply _ _ => simp [hphase] at h
        | awaitEffect _ => simp [hphase] at h
        | awaitPeer _ => simp [hphase] at h
        | crashed => simp [hphase] at h
      · simp [hrun] at h
    | spawn template =>
      simp only [apply] at h
      unfold spawn at h
      split at h
      · cases h
      · next t ht =>
        split at h
        · cases h
          let nid := InstId.peer template (w.nextIx template)
          let wR : World := ({ w with roster := w.roster ++ [nid], nextIx := fun n =>
            if n = template then w.nextIx n + 1 else w.nextIx n } : World)
          let born : Actor := withTokens I.desc template
            { life := .alive, typestate := t.initial, phase := .idle, box := [], prio := [],
              parked := [], tokens := fun _ => 0 }
          by_cases hd : d = nid
          · have hnin : nid ∉ w.roster := by
              intro hmem
              have hix := hOcc.indexed template (w.nextIx template) hmem
              omega
            have hempty := (hOcc.offEmpty nid hnin).1
            rw [hd, hempty] at hpos
            simp [callPos] at hpos
          · have hs := readCells_st I.desc (setActor wR nid born) nid d
            rw [hs]
            simp [wR, setActor, hd]
            exact Or.inl rfl
        · cases h
  exact call_grow _ _ _ hgrow hpos

/-- While the callee is not receiving, a call sitting in its box stays at the same index. -/
theorem call_pos_mono (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (c d : InstId) (i n : Nat)
    (halive : ∀ t, i ≤ t → t ≤ i + n → ((ρ.cfg t).st d).life = .alive)
    (hnorecv : ∀ t, i ≤ t → t < i + n → ρ.act t ≠ .recvBulk d)
    (hin : callPos ((ρ.cfg i).st d).box c < ((ρ.cfg i).st d).box.length) :
    callPos ((ρ.cfg (i + n)).st d).box c = callPos ((ρ.cfg i).st d).box c ∧
      callPos ((ρ.cfg (i + n)).st d).box c < ((ρ.cfg (i + n)).st d).box.length := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    exact ⟨rfl, hin⟩
  | succ n ih =>
    have hprev := ih (fun t h1 h2 => halive t h1 (Nat.le_trans h2 (Nat.le_succ _)))
      (fun t h1 h2 => hnorecv t h1 (by omega))
    have hOcc := (inv2_reachable I hL hG N (ρ.cfg (i + n)) (cfg_reachable ρ (i + n))).2.1
    have hstep := box_pos_mono I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1))
      (ρ.valid (i + n)) hOcc d c
      (hnorecv (i + n) (Nat.le_add_right i n) (by omega))
      (halive (i + n + 1) (by omega) (by omega)) hprev.2
    exact ⟨hstep.1.trans hprev.1, hstep.2⟩

/-- With the callee alive and able to receive infinitely often, the tagged call is
delivered and the handler is installed. `n` bounds the call's position. Each bulk
receive either installs the handler or moves the message strictly closer to the head. -/
theorem call_delivered (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (c d : InstId) (k : Cont) (n i : Nat)
    (hstay : ∀ t, i ≤ t → ((ρ.cfg t).st c).phase = .awaitReply d k)
    (halive : ∀ t, i ≤ t → ((ρ.cfg t).st d).life = .alive)
    (hin : callPos ((ρ.cfg i).st d).box c ≤ n)
    (hlt : callPos ((ρ.cfg i).st d).box c < ((ρ.cfg i).st d).box.length)
    (hio : ∀ t, ∃ j, t ≤ j ∧ CanReceive (ρ.cfg j) d) :
    ∃ j, i ≤ j ∧ ¬mailCall (ρ.cfg j) d c ∧
      (handlerOwes c ((ρ.cfg j).st d).phase ∨ replyPending c ((ρ.cfg j).st d).phase) ∧
      ((ρ.cfg j).st c).phase = .awaitReply d k := by
  induction n generalizing i with
  | zero =>
    have hzero : callPos ((ρ.cfg i).st d).box c = 0 := by omega
    obtain ⟨j, hj, hact, hfirst⟩ := next_bulk ρ hF d i hio
    have hmono := call_pos_mono I hL hG ρ c d i (j - i)
      (fun t h1 _ => halive t h1)
      (fun t h1 h2 => hfirst t h1 (by
        have hsum : i + (j - i) = j := Nat.add_sub_of_le hj
        omega))
      hlt
    have hposj : callPos ((ρ.cfg j).st d).box c = 0 := by
      have heq := hmono.1
      simp [Nat.add_sub_of_le hj] at heq
      rw [heq]
      exact hzero
    have hlenj : callPos ((ρ.cfg j).st d).box c < ((ρ.cfg j).st d).box.length := by
      simpa [Nat.add_sub_of_le hj] using hmono.2
    have hM := (inv_reachable I N (ρ.cfg j) hL (cfg_reachable ρ j)).2.1
    have hT := call_tag_reachable I hL hG N (ρ.cfg j) (cfg_reachable ρ j)
    have hrecv : receiveBulk I (ρ.cfg j) d = some (ρ.cfg (j + 1)) := by
      simpa [apply, hact] using ρ.valid j
    rcases recv_box_progress I hL (ρ.cfg j) (ρ.cfg (j + 1)) d c k hrecv hM hT (hstay j hj) hlenj with
      hinst | hdrop
    · exact ⟨j + 1, Nat.le_trans hj (Nat.le_succ j), hinst.2.1, hinst.2.2, hinst.1⟩
    · simp [hposj] at hdrop
  | succ n ih =>
    obtain ⟨j, hj, hact, hfirst⟩ := next_bulk ρ hF d i hio
    have hmono := call_pos_mono I hL hG ρ c d i (j - i)
      (fun t h1 _ => halive t h1)
      (fun t h1 h2 => hfirst t h1 (by
        have hsum : i + (j - i) = j := Nat.add_sub_of_le hj
        omega))
      hlt
    have hposj : callPos ((ρ.cfg j).st d).box c ≤ n + 1 := by
      have heq := hmono.1
      simp [Nat.add_sub_of_le hj] at heq
      rw [heq]
      exact hin
    have hlenj : callPos ((ρ.cfg j).st d).box c < ((ρ.cfg j).st d).box.length := by
      simpa [Nat.add_sub_of_le hj] using hmono.2
    have hM := (inv_reachable I N (ρ.cfg j) hL (cfg_reachable ρ j)).2.1
    have hT := call_tag_reachable I hL hG N (ρ.cfg j) (cfg_reachable ρ j)
    have hrecv : receiveBulk I (ρ.cfg j) d = some (ρ.cfg (j + 1)) := by
      simpa [apply, hact] using ρ.valid j
    rcases recv_box_progress I hL (ρ.cfg j) (ρ.cfg (j + 1)) d c k hrecv hM hT (hstay j hj) hlenj with
      hinst | hdrop
    · exact ⟨j + 1, Nat.le_trans hj (Nat.le_succ j), hinst.2.1, hinst.2.2, hinst.1⟩
    · have hnext : callPos ((ρ.cfg (j + 1)).st d).box c ≤ n := by
        have hltp := hdrop.2.2
        omega
      have hmail : mailCall (ρ.cfg (j + 1)) d c := hdrop.2.1
      have hph1 : ((ρ.cfg (j + 1)).st c).phase = .awaitReply d k := hdrop.1
      have hT1 := call_tag_reachable I hL hG N (ρ.cfg (j + 1)) (cfg_reachable ρ (j + 1))
      have hlen1 := (await_mail_in_box (ρ.cfg (j + 1)) hT1 c d k hph1 hmail).1
      obtain ⟨j1, hj1, hmail1, howe1, hphj⟩ := ih (j + 1)
        (fun t ht => hstay t (Nat.le_trans (Nat.le_trans hj (Nat.le_succ j)) ht))
        (fun t ht => halive t (Nat.le_trans (Nat.le_trans hj (Nat.le_succ j)) ht))
        hnext hlen1
      exact ⟨j1, Nat.le_trans (Nat.le_trans hj (Nat.le_succ j)) hj1, hmail1, howe1, hphj⟩

/-- Executing a reply whose target is waiting on this sender ends that wait. -/
theorem reply_exec_leaves (I : Impl) (w : World) (d c : InstId) (k ck : Cont) (es : List Eff)
    (hph : (w.st d).phase = .run k) (hl : (w.st d).life = .alive)
    (hrest : k.rest = .reply :: es) (hto : k.replyTo = some c)
    (hwait : (w.st c).phase = .awaitReply d ck) :
    waitKind ((execRun I w d (w.st d) k).st c) ≠ some (.callReply d) := by
  have hcne : c ≠ d := by
    intro heq
    rw [heq] at hwait
    simp [hph] at hwait
  simp [execRun, hrest, performReply, hto, hwait, setActor, hcne, proceed_not_call]

/-- A handler whose next effect is the reply does execute it, and the caller leaves
`awaitReply`. -/
theorem pending_reply_runs (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (c d : InstId) (k ck : Cont) (es : List Eff) (i : Nat)
    (hph : ((ρ.cfg i).st d).phase = .run k) (hl : ((ρ.cfg i).st d).life = .alive)
    (hrest : k.rest = .reply :: es) (hto : k.replyTo = some c)
    (hwait : ((ρ.cfg i).st c).phase = .awaitReply d ck)
    (hlive : ∀ t, i ≤ t → ((ρ.cfg t).st d).life = .alive)
    (hstay : ∀ t, i ≤ t → ((ρ.cfg t).st c).phase = .awaitReply d ck) :
    ∃ j, i ≤ j ∧ waitKind (((ρ.cfg (j + 1)).st c)) ≠ some (.callReply d) := by
  have hhit : ∃ j, i ≤ j ∧ ρ.act j = .exec d := by
    cases Classical.em (∃ j, i ≤ j ∧ ρ.act j = .exec d) with
    | inl h => exact h
    | inr hmiss =>
      have hstayR : ∀ u, i ≤ u → ((ρ.cfg u).st d).phase = .run k ∧ ((ρ.cfg u).st d).life = .alive := by
        intro u hu
        have hgot := run_holds hL hG ρ d i (u - i) k hph hl
          (fun v h1 _ hbad => hmiss ⟨v, h1, hbad⟩)
        simpa [Nat.add_sub_of_le hu] using hgot
      exact False.elim (not_forever_run I hL hG ρ hF d i (fun j hj => (hstayR j hj).2)
        (fun j hj => ⟨k, (hstayR j hj).1⟩))
  obtain ⟨j0, hj0, hact0⟩ := hhit
  have hscan := scanExec_spec ρ.act d (j0 - i) i ⟨j0 - i, Nat.le_refl _, by
    simpa [Nat.add_sub_of_le hj0] using hact0⟩
  let m := scanExec ρ.act d (j0 - i) i
  have him : i ≤ m := hscan.1
  have hact : ρ.act m = .exec d := hscan.2.1
  have hpre := run_holds hL hG ρ d i (m - i) k hph hl
    (fun t h1 _ hbad => hscan.2.2 t h1 (by
      have hsum : i + (m - i) = m := Nat.add_sub_of_le him
      omega) hbad)
  have hhere : ((ρ.cfg m).st d).phase = .run k := by
    simpa [Nat.add_sub_of_le him] using hpre.1
  have hlm : ((ρ.cfg m).st d).life = .alive := by
    simpa [Nat.add_sub_of_le him] using hpre.2
  have hrun : execRun I (ρ.cfg m) d ((ρ.cfg m).st d) k = ρ.cfg (m + 1) := by
    have hhead := ρ.valid m
    simp [apply, hact, execHead, hlm, hhere] at hhead
    exact hhead
  have hleft := reply_exec_leaves I (ρ.cfg m) d c k ck es hhere hlm hrest hto (hstay m him)
  rw [hrun] at hleft
  exact ⟨m, him, hleft⟩

/-- A caller that stays in `awaitReply` cannot be waiting on a handler whose next
effect is already the reply: that handler runs the reply and the wait ends. -/
theorem await_reply_head_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ) (c d : InstId) (k ck : Cont) (es : List Eff) (i : Nat)
    (hph : ((ρ.cfg i).st d).phase = .run k) (hl : ((ρ.cfg i).st d).life = .alive)
    (hrest : k.rest = .reply :: es) (hto : k.replyTo = some c)
    (hlive : ∀ t, i ≤ t → ((ρ.cfg t).st d).life = .alive)
    (hstay : ∀ t, i ≤ t → ((ρ.cfg t).st c).phase = .awaitReply d ck) : False := by
  obtain ⟨j, hj, hleft⟩ := pending_reply_runs I hL hG ρ hF c d k ck es i hph hl hrest hto
    (hstay i (Nat.le_refl _)) hlive hstay
  have hstill : ((ρ.cfg (j + 1)).st c).phase = .awaitReply d ck :=
    hstay (j + 1) (Nat.le_trans hj (Nat.le_succ j))
  simp [waitKind, hstill] at hleft

/-- An actor that is not running keeps its phase across someone else's execution,
and a dead idle actor is not resumed or parked on. -/
theorem exec_keeps_idle (I : Impl) (w : World) (id i : InstId) (k : Cont)
    (hne : i ≠ id) (hidle : (w.st i).phase = .idle) (hdead : (w.st i).life ≠ .alive) :
    ((execRun I w id (w.st id) k).st i).phase = .idle := by
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil => simp [execRun, setActor, hne, hidle]
    | cons e tail =>
      cases e with
      | send dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed, hidle]
        | some dstId =>
          simpa [hr, hidle] using enqueue_phase_other w I.desc id dstId
            { label := label, sender := id, callFrom := none } false
            (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) i hne
      | call dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed, hidle]
        | some dstId =>
          simpa [hr, hidle] using enqueue_phase_other w I.desc id dstId
            { label := label, sender := id, callFrom := some id } true
            (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) i hne
      | trySend dst label hint =>
        simp only [execRun]
        cases hr : route w I.desc dst hint with
        | none => simp [hr, setActor, hne, proceed, hidle]
        | some dstId =>
          simp only [hr]
          split
          · next hgo =>
            by_cases hid : i = dstId
            · have hnd : ¬ dstId = id := fun h => hne (hid.trans h)
              rw [← hid]
              simp [hgo, setActor, hne, hnd, proceed, hidle]
            · simp [hgo, setActor, hid, hne, proceed, hidle]
          · simp [setActor, hne, proceed, hidle]
      | reply =>
        simp only [execRun, performReply]
        cases hto : replyTo with
        | none => simp [hto, setActor, hne, proceed, hidle]
        | some caller =>
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            by_cases hd : dst = id
            · have hnc : caller ≠ i := by
                intro hc
                rw [hc] at hcall
                simp [hidle] at hcall
              have hflip : ¬ i = caller := fun h => hnc h.symm
              simp [hto, hcall, hd, setActor, hne, hflip, proceed, hidle]
            · simp [hto, hcall, hd, setActor, hne, proceed, hidle]
          | idle => simp [hto, hcall, setActor, hne, proceed, hidle]
          | run _ => simp [hto, hcall, setActor, hne, proceed, hidle]
          | parked _ _ _ => simp [hto, hcall, setActor, hne, proceed, hidle]
          | awaitEffect _ => simp [hto, hcall, setActor, hne, proceed, hidle]
          | awaitPeer _ => simp [hto, hcall, setActor, hne, proceed, hidle]
          | crashed => simp [hto, hcall, setActor, hne, proceed, hidle]
      | selfSchedule _ =>
        simp only [execRun]
        split <;> try split
        · simp [setActor, hne, proceed, hidle]
        · simp [setActor, hne, proceed, hidle]
        · simp [setActor, hne, hidle]
      | cell dst label value =>
        simp only [execRun]
        have hwake : ∀ (ids : List InstId) (w0 : World),
            ((ids.foldl (fun w r => tryWake I.desc w r label id) w0).st i).phase =
              (w0.st i).phase := by
          intro ids w0
          induction ids generalizing w0 with
          | nil => simp
          | cons j js ih =>
            simp only [List.foldl_cons]
            have hstep : ((tryWake I.desc w0 j label id).st i).phase = (w0.st i).phase := by
              by_cases hif : ((w0.st j).life == .alive &&
                  decide ((w0.st j).prio.length < capPrio I.desc w0.N j) &&
                  !((w0.st j).prio.any fun p => p.label == label)) = true
              · simp [tryWake, hif, setActor]
                by_cases hi : i = j <;> simp [hi]
              · simp [tryWake, hif]
            exact (ih _).trans hstep
        cases hdirty : (w.cell dst label).dirty
        · simp [hdirty, setCell, setActor, hne, proceed, wakeReaders, hwake, hidle]
        · simp [hdirty, setCell, setActor, hne, proceed, hidle]
      | internal => simp [execRun, setActor, hne, hidle]
      | peer => simp [execRun, setActor, hne, hidle]
      | terminate =>
        simp only [execRun]
        have hrel : ∀ (ps : List Parked) (w0 : World), (w0.st i).phase = .idle →
            ((releaseParked w0 id ps).st i).phase = .idle := by
          intro ps w0 h0
          induction ps generalizing w0 with
          | nil => simpa [releaseParked] using h0
          | cons p ps ih =>
            simp only [releaseParked, List.foldl_cons]
            by_cases hskip : (p.isCall || decide (p.sender = id)) = true
            · rw [if_pos hskip]
              exact ih w0 h0
            · rw [if_neg hskip]
              have hph : ((setActor w0 p.sender (resumeSender (w0.st p.sender) false id)).st i).phase =
                  .idle := by
                by_cases hi : i = p.sender
                · have hI : (w0.st p.sender).phase = .idle := by rw [← hi]; exact h0
                  simp [setActor, hi, resumeSender, hI]
                · simp [setActor, hi, h0]
              exact ih _ hph
        cases htpl : templateOf I.desc (tname id) with
        | none => simp [htpl, hidle]
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · have hpre : ((refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box)
                (tname id) (w.st id).parked).st i).phase = .idle := by
              rw [(refundP_life _ _ _ i).2.2.1, (refund_life _ _ _ i).2.2.1, readCells_st]
              exact hidle
            simp [htpl, hkill, readCells_st]
            exact hrel _ _ (by simp [setActor, hne, hpre])
          · simp [htpl, hkill, hidle]

/-- A message in a box after `enqueueOrPark` was already there, or it is the message
just enqueued into the live target. -/
theorem enqueue_box_mem (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (mb : InstId) (m : Msg)
    (hm : m ∈ ((enqueueOrPark w D sender dst msg isCall k).st mb).box) :
    m ∈ (w.st mb).box ∨
      (mb = dst ∧ m = msg ∧ (w.st dst).life = .alive) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hparkS : (w.st sender).parked = [] := by rw [hsame]; exact hroom.1
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by rw [hsame]; exact hroom.2
        cases isCall
        · rw [← hsame] at hm
          rw [enqueue_room_self_send w D sender msg k hliveS hparkS hcapS] at hm
          by_cases hmb : mb = sender
          · simp [setActor, hmb, proceed_box, charge_box, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact Or.inl (by rw [← hmb] at hm; exact hm)
            · exact Or.inr ⟨hmb.trans hsame, hm, hlive⟩
          · simp [setActor, hmb] at hm
            exact Or.inl hm
        · rw [← hsame] at hm
          rw [enqueue_room_self_call w D sender msg k hliveS hparkS hcapS] at hm
          by_cases hmb : mb = sender
          · simp [setActor, hmb, charge_box, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact Or.inl (by rw [← hmb] at hm; exact hm)
            · exact Or.inr ⟨hmb.trans hsame, hm, hlive⟩
          · simp [setActor, hmb] at hm
            exact Or.inl hm
      · have hflip : ¬ dst = sender := fun h => hsame h.symm
        cases isCall
        · rw [enqueue_room_other_send w D sender dst msg k hlive hsame hroom.1 hroom.2] at hm
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp [setActor, hmb, hne, hflip, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact Or.inl (by rw [← hmb] at hm; exact hm)
            · exact Or.inr ⟨hmb, hm, hlive⟩
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, proceed_box, charge_box] at hm
              exact Or.inl (by rw [← hsender] at hm; exact hm)
            · simp [setActor, hmb, hsender, hflip] at hm
              exact Or.inl hm
        · rw [enqueue_room_other_call w D sender dst msg k hlive hsame hroom.1 hroom.2] at hm
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp [setActor, hmb, hne, hflip, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact Or.inl (by rw [← hmb] at hm; exact hm)
            · exact Or.inr ⟨hmb, hm, hlive⟩
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, charge_box] at hm
              exact Or.inl (by rw [← hsender] at hm; exact hm)
            · simp [setActor, hmb, hsender, hflip] at hm
              exact Or.inl hm
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          rw [hsame]; exact hroom
        rw [← hsame] at hm
        rw [enqueue_park_self w D sender msg isCall k hliveS hroomS] at hm
        by_cases hmb : mb = sender
        · simp [setActor, hmb, charge_box] at hm
          exact Or.inl (by rw [← hmb] at hm; exact hm)
        · simp [setActor, hmb] at hm
          exact Or.inl hm
      · rw [enqueue_park_other w D sender dst msg isCall k hlive hsame hroom] at hm
        by_cases hmb : mb = dst
        · have hflip : ¬ dst = sender := fun h => hsame h.symm
          simp [setActor, hmb, hflip] at hm
          exact Or.inl (by rw [← hmb] at hm; exact hm)
        · by_cases hsender : mb = sender
          · simp [setActor, hmb, hsender, charge_box] at hm
            exact Or.inl (by rw [← hsender] at hm; exact hm)
          · simp [setActor, hmb, hsender] at hm
            exact Or.inl hm
  · rw [enqueue_dead w D sender dst msg isCall k hlive] at hm
    by_cases hmb : mb = sender
    · simp [setActor, hmb, proceed_box] at hm
      exact Or.inl (by rw [← hmb] at hm; exact hm)
    · simp [setActor, hmb] at hm
      exact Or.inl hm

/-- Some bulk mailbox holds a message naming `c`. -/
def anyCall (w : World) (c : InstId) : Prop :=
  (∃ i m, m ∈ (w.st i).box ∧ m.callFrom = some c) ∨
    (∃ i p, p ∈ (w.st i).parked ∧ p.msg.callFrom = some c)

theorem anyCall_mail (w : World) (d c : InstId) (h : mailCall w d c) : anyCall w c := by
  rcases h with ⟨m, hm, hc⟩ | ⟨p, hp, hc⟩
  · exact Or.inl ⟨d, m, hm, hc⟩
  · exact Or.inr ⟨d, p, hp, hc⟩

/-- While `c` is in `awaitReply d`, only `d` can hold a message naming `c`. -/
theorem only_call_here (w : World) (hT : CallTagInv w) (c d : InstId) (k : Cont)
    (hph : (w.st c).phase = .awaitReply d k) (i : InstId) :
    (∀ m, m ∈ (w.st i).box → m.callFrom = some c → i = d) ∧
      (∀ p, p ∈ (w.st i).parked → p.msg.callFrom = some c → i = d) := by
  refine ⟨?_, ?_⟩
  · intro m hm hc
    rcases hT.msgOwner i c (Or.inl ⟨m, hm, hc⟩) with ⟨k', hk⟩ | ⟨k', hk⟩
    · have heq : Phase.awaitReply i k' = Phase.awaitReply d k := by rw [← hk, hph]
      injection heq
    · rw [hph] at hk
      cases hk
  · intro p hp hc
    rcases hT.msgOwner i c (Or.inr ⟨p, hp, hc⟩) with ⟨k', hk⟩ | ⟨k', hk⟩
    · have heq : Phase.awaitReply i k' = Phase.awaitReply d k := by rw [← hk, hph]
      injection heq
    · rw [hph] at hk
      cases hk

theorem exec_no_foreign_call (I : Impl) (w : World) (id : InstId) (k : Cont) (c : InstId)
    (hne : id ≠ c) (hno : ¬ anyCall w c) :
    ¬ anyCall (execRun I w id (w.st id) k) c := by
  intro hyes
  have hne' : ¬ c = id := fun h => hne h.symm
  cases k with
  | mk rest toState replyTo =>
    cases rest with
    | nil =>
      rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
      · simp [execRun, setActor] at hm
        by_cases hmb : mb = id
        · rw [hmb] at hm
          simp [setActor] at hm
          exact hno (Or.inl ⟨id, m, hm, hc⟩)
        · simp [setActor, hmb] at hm
          exact hno (Or.inl ⟨mb, m, hm, hc⟩)
      · simp [execRun, setActor] at hp
        by_cases hmb : mb = id
        · rw [hmb] at hp
          simp [setActor] at hp
          exact hno (Or.inr ⟨id, p, hp, hc⟩)
        · simp [setActor, hmb] at hp
          exact hno (Or.inr ⟨mb, p, hp, hc⟩)
    | cons e tail =>
      cases e with
      | call dst label hint =>
        simp only [execRun] at hyes
        cases hr : route w I.desc dst hint with
        | none =>
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [hr, setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [hr, setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        | some dstId =>
          let msg : Msg := { label := label, sender := id, callFrom := some id }
          simp only [hr] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · rcases enqueue_box_mem w I.desc id dstId msg true
                (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) mb m hm with
              hold | ⟨_, heq, _⟩
            · exact hno (Or.inl ⟨mb, m, hold, hc⟩)
            · rw [heq] at hc
              injection hc with hid
              exact hne hid
          · rcases enqueue_parked_mem w I.desc id dstId msg true
                (afterHead ⟨.call dst label hint :: tail, toState, replyTo⟩) mb p hp with
              hold | ⟨_, _, heq, _, _⟩
            · exact hno (Or.inr ⟨mb, p, hold, hc⟩)
            · rw [heq] at hc
              injection hc with hid
              exact hne hid
      | send dst label hint =>
        simp only [execRun] at hyes
        cases hr : route w I.desc dst hint with
        | none =>
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [hr, setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [hr, setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        | some dstId =>
          let msg : Msg := { label := label, sender := id, callFrom := none }
          simp only [hr] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · rcases enqueue_box_mem w I.desc id dstId msg false
                (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) mb m hm with
              hold | ⟨_, heq, _⟩
            · exact hno (Or.inl ⟨mb, m, hold, hc⟩)
            · rw [heq] at hc
              simp at hc
          · rcases enqueue_parked_mem w I.desc id dstId msg false
                (afterHead ⟨.send dst label hint :: tail, toState, replyTo⟩) mb p hp with
              hold | ⟨_, _, heq, _, _⟩
            · exact hno (Or.inr ⟨mb, p, hold, hc⟩)
            · rw [heq] at hc
              simp at hc
      | trySend dst label hint =>
        simp only [execRun] at hyes
        cases hr : route w I.desc dst hint with
        | none =>
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [hr, setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [hr, setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [hr, setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        | some dstId =>
          simp only [hr] at hyes
          by_cases hgo : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
          · simp [hgo] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · by_cases hmb : mb = dstId
              · by_cases hself : dstId = id
                · simp [setActor, hmb, hself, charge_box, proceed_box, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact hno (Or.inl ⟨id, m, hm, hc⟩)
                  · rw [hm] at hc
                    simp at hc
                · have hnd : ¬ id = dstId := fun h => hself h.symm
                  simp [setActor, hmb, hself, hnd, charge_box, proceed_box, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact hno (Or.inl ⟨dstId, m, hm, hc⟩)
                  · rw [hm] at hc
                    simp at hc
              · by_cases hmi : mb = id
                · have hnd : ¬ id = dstId := fun h => hmb (hmi.trans h)
                  simp [setActor, hmb, hmi, hnd, proceed_box, charge_box] at hm
                  exact hno (Or.inl ⟨id, m, hm, hc⟩)
                · simp [setActor, hmb, hmi] at hm
                  exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · by_cases hmb : mb = id
              · by_cases hself : id = dstId
                · simp [setActor, hmb, hself, proceed_parked, charge_parked] at hp
                  rw [← hself] at hp
                  exact hno (Or.inr ⟨id, p, hp, hc⟩)
                · have hflip : ¬ dstId = id := fun h => hself h.symm
                  simp [setActor, hmb, hself, hflip, proceed_parked, charge_parked] at hp
                  exact hno (Or.inr ⟨id, p, hp, hc⟩)
              · by_cases hmd : mb = dstId
                · have hnd : ¬ dstId = id := fun h => hmb (hmd.trans h)
                  have hni : ¬ id = dstId := fun h => hnd h.symm
                  simp [setActor, hmb, hmd, hnd, hni, charge_parked] at hp
                  exact hno (Or.inr ⟨dstId, p, hp, hc⟩)
                · simp [setActor, hmb, hmd] at hp
                  exact hno (Or.inr ⟨mb, p, hp, hc⟩)
          · simp [hgo] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_box] at hm
                exact hno (Or.inl ⟨id, m, hm, hc⟩)
              · simp [setActor, hmb] at hm
                exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_parked] at hp
                exact hno (Or.inr ⟨id, p, hp, hc⟩)
              · simp [setActor, hmb] at hp
                exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | reply =>
        simp only [execRun] at hyes
        unfold performReply at hyes
        cases hto : replyTo with
        | none =>
          simp [hto] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        | some caller =>
          simp [hto] at hyes
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            simp [hcall] at hyes
            by_cases hd : dst = id
            · simp [hd] at hyes
              rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
              · by_cases hmb : mb = id
                · by_cases hcid : caller = id
                  · simp [setActor, hmb, hcid, hd, proceed_box] at hm
                    exact hno (Or.inl ⟨id, m, hm, hc⟩)
                  · have hni : ¬ id = caller := fun h => hcid h.symm
                    simp [setActor, hmb, hcid, hni, proceed_box] at hm
                    exact hno (Or.inl ⟨id, m, hm, hc⟩)
                · by_cases hmc : mb = caller
                  · have hnc : ¬ caller = id := fun h => hmb (hmc.trans h)
                    have hni : ¬ id = caller := fun h => hnc h.symm
                    simp [setActor, hmb, hmc, hnc, hni, proceed_box] at hm
                    exact hno (Or.inl ⟨caller, m, hm, hc⟩)
                  · simp [setActor, hmb, hmc] at hm
                    exact hno (Or.inl ⟨mb, m, hm, hc⟩)
              · by_cases hmb : mb = id
                · by_cases hcid : caller = id
                  · simp [setActor, hmb, hcid, hd, proceed_parked] at hp
                    exact hno (Or.inr ⟨id, p, hp, hc⟩)
                  · have hni : ¬ id = caller := fun h => hcid h.symm
                    simp [setActor, hmb, hcid, hni, proceed_parked] at hp
                    exact hno (Or.inr ⟨id, p, hp, hc⟩)
                · by_cases hmc : mb = caller
                  · have hnc : ¬ caller = id := fun h => hmb (hmc.trans h)
                    have hni : ¬ id = caller := fun h => hnc h.symm
                    simp [setActor, hmb, hmc, hnc, hni, proceed_parked] at hp
                    exact hno (Or.inr ⟨caller, p, hp, hc⟩)
                  · simp [setActor, hmb, hmc] at hp
                    exact hno (Or.inr ⟨mb, p, hp, hc⟩)
            · simp [hd] at hyes
              rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
              · by_cases hmb : mb = id
                · simp [setActor, hmb, proceed_box] at hm
                  exact hno (Or.inl ⟨id, m, hm, hc⟩)
                · simp [setActor, hmb] at hm
                  exact hno (Or.inl ⟨mb, m, hm, hc⟩)
              · by_cases hmb : mb = id
                · simp [setActor, hmb, proceed_parked] at hp
                  exact hno (Or.inr ⟨id, p, hp, hc⟩)
                · simp [setActor, hmb] at hp
                  exact hno (Or.inr ⟨mb, p, hp, hc⟩)
          | _ =>
            simp [hcall] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_box] at hm
                exact hno (Or.inl ⟨id, m, hm, hc⟩)
              · simp [setActor, hmb] at hm
                exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_parked] at hp
                exact hno (Or.inr ⟨id, p, hp, hc⟩)
              · simp [setActor, hmb] at hp
                exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | selfSchedule label =>
        simp only [execRun] at hyes
        by_cases hdup : ((w.st id).prio.any (fun p => p.label == label)) = true
        · simp [hdup] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        · simp [hdup] at hyes
          by_cases hroom : (w.st id).prio.length < capPrio I.desc w.N id
          · simp [hroom] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_box] at hm
                exact hno (Or.inl ⟨id, m, hm, hc⟩)
              · simp [setActor, hmb] at hm
                exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · by_cases hmb : mb = id
              · simp [setActor, hmb, proceed_parked] at hp
                exact hno (Or.inr ⟨id, p, hp, hc⟩)
              · simp [setActor, hmb] at hp
                exact hno (Or.inr ⟨mb, p, hp, hc⟩)
          · simp [hroom] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · by_cases hmb : mb = id
              · simp [setActor, hmb] at hm
                exact hno (Or.inl ⟨id, m, hm, hc⟩)
              · simp [setActor, hmb] at hm
                exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · by_cases hmb : mb = id
              · simp [setActor, hmb] at hp
                exact hno (Or.inr ⟨id, p, hp, hc⟩)
              · simp [setActor, hmb] at hp
                exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | cell dst label value =>
        simp only [execRun] at hyes
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp [hdirty, setCell] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
        · simp [hdirty, setCell, wakeReaders] at hyes
          rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
          · rw [wakes_box] at hm
            by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_box] at hm
              exact hno (Or.inl ⟨id, m, hm, hc⟩)
            · simp [setActor, hmb] at hm
              exact hno (Or.inl ⟨mb, m, hm, hc⟩)
          · rw [wakes_parked] at hp
            by_cases hmb : mb = id
            · simp [setActor, hmb, proceed_parked] at hp
              exact hno (Or.inr ⟨id, p, hp, hc⟩)
            · simp [setActor, hmb] at hp
              exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | internal =>
        simp [execRun, setActor] at hyes
        rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
        · by_cases hmb : mb = id
          · simp [setActor, hmb] at hm
            exact hno (Or.inl ⟨id, m, hm, hc⟩)
          · simp [setActor, hmb] at hm
            exact hno (Or.inl ⟨mb, m, hm, hc⟩)
        · by_cases hmb : mb = id
          · simp [setActor, hmb] at hp
            exact hno (Or.inr ⟨id, p, hp, hc⟩)
          · simp [setActor, hmb] at hp
            exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | peer =>
        simp [execRun, setActor] at hyes
        rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
        · by_cases hmb : mb = id
          · simp [setActor, hmb] at hm
            exact hno (Or.inl ⟨id, m, hm, hc⟩)
          · simp [setActor, hmb] at hm
            exact hno (Or.inl ⟨mb, m, hm, hc⟩)
        · by_cases hmb : mb = id
          · simp [setActor, hmb] at hp
            exact hno (Or.inr ⟨id, p, hp, hc⟩)
          · simp [setActor, hmb] at hp
            exact hno (Or.inr ⟨mb, p, hp, hc⟩)
      | terminate =>
        simp only [execRun] at hyes
        cases htpl : templateOf I.desc (tname id) with
        | none =>
          simp [htpl] at hyes
          exact hno hyes
        | some t =>
          by_cases hkill : (t.terminable && !hasParkedCall (w.st id).parked) = true
          · simp [htpl, hkill] at hyes
            rcases hyes with ⟨mb, m, hm, hc⟩ | ⟨mb, p, hp, hc⟩
            · rw [release_box] at hm
              by_cases hmb : mb = id
              · simp [setActor, hmb] at hm
              · simp [setActor, hmb, refundP_box, refund_box, readCells_st] at hm
                exact hno (Or.inl ⟨mb, m, hm, hc⟩)
            · rw [release_preserves_parked] at hp
              by_cases hmb : mb = id
              · simp [setActor, hmb] at hp
              · simp [setActor, hmb, refundP_park, refund_park, readCells_st] at hp
                exact hno (Or.inr ⟨mb, p, hp, hc⟩)
          · simp [htpl, hkill] at hyes
            exact hno hyes

/-- A bulk receive only rearranges messages that were already queued. -/
theorem recv_keeps_call (I : Impl) (w w' : World) (id c : InstId)
    (h : receiveBulk I w id = some w') (hno : ¬ anyCall w c) (hyes : anyCall w' c) : False := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · have hidle : (w.st id).phase = .idle := by
      by_cases hp : (w.st id).phase = .idle
      · exact hp
      · exact False.elim (hready (Or.inr hp))
    simp [hready] at h
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
          have hst := fun i => deliver_st I w id _ p.msg w1 a1 i hdel
          have hbx := deliver_box I w id _ p.msg w1 a1 hdel
          have hpk := deliver_parked I w id _ p.msg w1 a1 hdel
          rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, q, hq, hc⟩
          · by_cases hi : i = id
            · by_cases hs : id = p.sender
              · simp [credit_box, setActor, hi, hs, resume_box, hbx] at hm
              · simp [credit_box, setActor, hi, hs, hbx] at hm
            · by_cases hs : i = p.sender
              · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                simp [credit_box, setActor, hi, hs, hnj, resume_box] at hm
                rw [← hs, hst i] at hm
                exact hno (Or.inl ⟨i, m, hm, hc⟩)
              · simp [credit_box, setActor, hi, hs] at hm
                rw [hst i] at hm
                exact hno (Or.inl ⟨i, m, hm, hc⟩)
          · by_cases hi : i = id
            · by_cases hs : id = p.sender
              · simp [credit_parked, setActor, hi, hs, resume_parked, hpk] at hq
                exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
              · simp [credit_parked, setActor, hi, hs, hpk] at hq
                exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
            · by_cases hs : i = p.sender
              · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                simp [credit_parked, setActor, hi, hs, hnj, resume_parked] at hq
                rw [← hs, hst i] at hq
                exact hno (Or.inr ⟨i, q, hq, hc⟩)
              · simp [credit_parked, setActor, hi, hs] at hq
                rw [hst i] at hq
                exact hno (Or.inr ⟨i, q, hq, hc⟩)
    | cons m0 ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := fun i => deliver_st I w id _ m0 w1 a1 i hdel
          have hbx := deliver_box I w id _ m0 w1 a1 hdel
          have hpk := deliver_parked I w id _ m0 w1 a1 hdel
          rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, q, hq, hc⟩
          · by_cases hi : i = id
            · by_cases hsend : id = m0.sender
              · simp [credit_box, setActor, hi, hsend, hbx] at hm
                exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
              · simp [credit_box, setActor, hi, hsend, hbx] at hm
                exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
            · by_cases hsend : i = m0.sender
              · have hni : ¬ m0.sender = id := fun h => hi (hsend.trans h)
                simp [credit_box, setActor, hi, hsend, hni] at hm
                rw [← hsend, hst i] at hm
                exact hno (Or.inl ⟨i, m, hm, hc⟩)
              · simp [credit_box, setActor, hi, hsend] at hm
                rw [hst i] at hm
                exact hno (Or.inl ⟨i, m, hm, hc⟩)
          · by_cases hi : i = id
            · by_cases hsend : id = m0.sender
              · simp [credit_parked, setActor, hi, hsend, hpk, hpark] at hq
              · simp [credit_parked, setActor, hi, hsend, hpk, hpark] at hq
            · by_cases hsend : i = m0.sender
              · have hni : ¬ m0.sender = id := fun h => hi (hsend.trans h)
                simp [credit_parked, setActor, hi, hsend, hni] at hq
                rw [← hsend, hst i] at hq
                exact hno (Or.inr ⟨i, q, hq, hc⟩)
              · simp [credit_parked, setActor, hi, hsend] at hq
                rw [hst i] at hq
                exact hno (Or.inr ⟨i, q, hq, hc⟩)
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          have hst := fun i => deliver_st I w id _ m0 w1 a1 i hdel
          have hbx := deliver_box I w id _ m0 w1 a1 hdel
          rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, q, hq, hc⟩
          · by_cases hi : i = id
            · by_cases hs : id = p.sender
              · by_cases hsend : id = m0.sender
                · have hsp : m0.sender = p.sender := hsend.symm.trans hs
                  simp [credit_box, setActor, hi, hs, hsend, hsp, resume_box, hbx, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
                  · rw [hm] at hc
                    exact hno (Or.inr ⟨id, p, by rw [hpark]; exact List.Mem.head _, hc⟩)
                · have hsp : ¬ m0.sender = p.sender := fun h => hsend (hs.trans h.symm)
                  simp [credit_box, setActor, hi, hs, hsend, hsp, resume_box, hbx, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
                  · rw [hm] at hc
                    exact hno (Or.inr ⟨id, p, by rw [hpark]; exact List.Mem.head _, hc⟩)
              · by_cases hsend : id = m0.sender
                · have hsp : ¬ m0.sender = p.sender := fun h => hs (hsend.trans h)
                  simp [credit_box, setActor, hi, hs, hsend, hsp, hbx, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
                  · rw [hm] at hc
                    exact hno (Or.inr ⟨id, p, by rw [hpark]; exact List.Mem.head _, hc⟩)
                · by_cases hsp : m0.sender = p.sender
                  · simp [credit_box, setActor, hi, hs, hsend, hsp, hbx, List.mem_append,
                      List.mem_singleton] at hm
                    rcases hm with hm | hm
                    · exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
                    · rw [hm] at hc
                      exact hno (Or.inr ⟨id, p, by rw [hpark]; exact List.Mem.head _, hc⟩)
                  · simp [credit_box, setActor, hi, hs, hsend, hsp, hbx, List.mem_append,
                      List.mem_singleton] at hm
                    rcases hm with hm | hm
                    · exact hno (Or.inl ⟨id, m, by rw [hbox]; exact List.Mem.tail _ hm, hc⟩)
                    · rw [hm] at hc
                      exact hno (Or.inr ⟨id, p, by rw [hpark]; exact List.Mem.head _, hc⟩)
            · by_cases hs : i = p.sender
              · by_cases hsend : p.sender = m0.sender
                · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                  have hni : ¬ m0.sender = id := fun h => hnj (hsend.trans h)
                  simp [credit_box, setActor, hi, hs, hsend, hnj, hni, resume_box] at hm
                  rw [← hsend, ← hs, hst i] at hm
                  exact hno (Or.inl ⟨i, m, hm, hc⟩)
                · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                  have hflip : ¬ m0.sender = p.sender := fun h => hsend h.symm
                  simp [credit_box, setActor, hi, hs, hsend, hnj, hflip, resume_box] at hm
                  rw [← hs, hst i] at hm
                  exact hno (Or.inl ⟨i, m, hm, hc⟩)
              · by_cases hsend : i = m0.sender
                · have hni : ¬ m0.sender = id := fun h => hi (hsend.trans h)
                  have hsp : ¬ m0.sender = p.sender := fun h => hs (hsend.trans h)
                  simp [credit_box, setActor, hi, hs, hsend, hni, hsp] at hm
                  rw [← hsend, hst i] at hm
                  exact hno (Or.inl ⟨i, m, hm, hc⟩)
                · simp [credit_box, setActor, hi, hs, hsend] at hm
                  rw [hst i] at hm
                  exact hno (Or.inl ⟨i, m, hm, hc⟩)
          · by_cases hi : i = id
            · by_cases hs : id = p.sender
              · by_cases hsend : id = m0.sender
                · have hsp : m0.sender = p.sender := hsend.symm.trans hs
                  simp [credit_parked, setActor, hi, hs, hsend, hsp, resume_parked] at hq
                  exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
                · have hsp : ¬ m0.sender = p.sender := fun h => hsend (hs.trans h.symm)
                  simp [credit_parked, setActor, hi, hs, hsend, hsp, resume_parked] at hq
                  exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
              · by_cases hsend : id = m0.sender
                · have hsp : ¬ m0.sender = p.sender := fun h => hs (hsend.trans h)
                  simp [credit_parked, setActor, hi, hs, hsend, hsp] at hq
                  exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
                · by_cases hsp : m0.sender = p.sender
                  · simp [credit_parked, setActor, hi, hs, hsend, hsp] at hq
                    exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
                  · simp [credit_parked, setActor, hi, hs, hsend, hsp] at hq
                    exact hno (Or.inr ⟨id, q, by rw [hpark]; exact List.Mem.tail _ hq, hc⟩)
            · by_cases hs : i = p.sender
              · by_cases hsend : p.sender = m0.sender
                · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                  have hni : ¬ m0.sender = id := fun h => hnj (hsend.trans h)
                  simp [credit_parked, setActor, hi, hs, hsend, hnj, hni, resume_parked] at hq
                  rw [← hsend, ← hs, hst i] at hq
                  exact hno (Or.inr ⟨i, q, hq, hc⟩)
                · have hnj : ¬ p.sender = id := fun h => hi (hs.trans h)
                  have hflip : ¬ m0.sender = p.sender := fun h => hsend h.symm
                  simp [credit_parked, setActor, hi, hs, hsend, hnj, hflip, resume_parked] at hq
                  rw [← hs, hst i] at hq
                  exact hno (Or.inr ⟨i, q, hq, hc⟩)
              · by_cases hsend : i = m0.sender
                · have hni : ¬ m0.sender = id := fun h => hi (hsend.trans h)
                  have hsp : ¬ m0.sender = p.sender := fun h => hs (hsend.trans h)
                  simp [credit_parked, setActor, hi, hs, hsend, hni, hsp] at hq
                  rw [← hsend, hst i] at hq
                  exact hno (Or.inr ⟨i, q, hq, hc⟩)
                · simp [credit_parked, setActor, hi, hs, hsend] at hq
                  rw [hst i] at hq
                  exact hno (Or.inr ⟨i, q, hq, hc⟩)

/-- A caller parked in `awaitReply` does not run, so it cannot create a fresh
`callFrom` for itself. Messages already naming it stay the only ones. -/
theorem no_new_mailCall (I : Impl) (a : Action) (w w' : World) (c d : InstId) (k : Cont)
    (h : apply I a w = some w')
    (hph : (w.st c).phase = .awaitReply d k)
    (hph' : (w'.st c).phase = .awaitReply d k)
    (hno : ¬ anyCall w c) : ¬ anyCall w' c := by
  cases a with
  | exec id =>
    have hne : id ≠ c := by
      intro heq
      rw [← heq] at hph
      simp [apply, execHead, hph] at h
    simp only [apply] at h
    unfold execHead at h
    by_cases hlive : (w.st id).life = .alive
    · simp [hlive] at h
      cases hphase : (w.st id).phase with
      | run kRun =>
        simp [hphase] at h
        cases h
        exact exec_no_foreign_call I w id kRun c hne hno
      | idle => simp [hphase] at h
      | parked _ _ _ => simp [hphase] at h
      | awaitReply _ _ => simp [hphase] at h
      | awaitEffect _ => simp [hphase] at h
      | awaitPeer _ => simp [hphase] at h
      | crashed => simp [hphase] at h
    · simp [hlive] at h
  | finish id =>
    intro hyes
    rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, p, hp, hc⟩
    · have heq := finish_box w w' id i (by simpa [apply] using h)
      exact hno (Or.inl ⟨i, m, by rw [heq] at hm; exact hm, hc⟩)
    · have heq := finish_parked w w' id i (by simpa [apply] using h)
      exact hno (Or.inr ⟨i, p, by rw [heq] at hp; exact hp, hc⟩)
  | recvPrio id =>
    intro hyes
    rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, p, hp, hc⟩
    · have heq := prio_box I w w' id i (by simpa [apply] using h)
      exact hno (Or.inl ⟨i, m, by rw [heq] at hm; exact hm, hc⟩)
    · have heq := prio_parked I w w' id i (by simpa [apply] using h)
      exact hno (Or.inr ⟨i, p, by rw [heq] at hp; exact hp, hc⟩)
  | spawn template =>
    intro hyes
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        rcases hyes with ⟨i, m, hm, hc⟩ | ⟨i, p, hp, hc⟩
        · by_cases hi : i = nid
          · simp [nid, readCells_st, setActor, hi, withTokens] at hm
          · simp [nid, readCells_st, setActor, hi] at hm
            exact hno (Or.inl ⟨i, m, hm, hc⟩)
        · by_cases hi : i = nid
          · simp [nid, readCells_st, setActor, hi, withTokens] at hp
          · simp [nid, readCells_st, setActor, hi] at hp
            exact hno (Or.inr ⟨i, p, hp, hc⟩)
      · cases h
    | recvBulk id =>
    intro hyes
    have hrecv : receiveBulk I w id = some w' := by simpa [apply] using h
    exact recv_keeps_call I w w' id c hrecv hno hyes

/-- A non-alive idle actor is not given a new phase by one step. -/
theorem dead_stays_idle (I : Impl) (a : Action) (w w' : World) (i : InstId)
    (h : apply I a w = some w') (hdead : (w.st i).life ≠ .alive)
    (hidle : (w.st i).phase = .idle) : (w'.st i).phase = .idle := by
  cases a with
  | exec id =>
    simp only [apply] at h
    unfold execHead at h
    by_cases hl : (w.st id).life = .alive
    · simp [hl] at h
      cases hp : (w.st id).phase with
      | run k =>
        simp [hp] at h
        cases h
        by_cases hi : i = id
        · rw [hi] at hidle
          simp [hp] at hidle
        · rw [(exec_keeps_quiet I w id (w.st id) k i hi
            (fun d c ck hbad => by simp [hidle] at hbad)
            (fun d ck hbad => by simp [hidle] at hbad)).1]
          exact hidle
      | idle => simp [hp] at h
      | parked _ _ _ => simp [hp] at h
      | awaitReply _ _ => simp [hp] at h
      | awaitEffect _ => simp [hp] at h
      | awaitPeer _ => simp [hp] at h
      | crashed => simp [hp] at h
    · simp [hl] at h
  | recvBulk id =>
    simp only [apply] at h
    by_cases hi : i = id
    · have hdead' : (w.st id).life ≠ .alive := by rw [← hi]; exact hdead
      unfold receiveBulk at h
      have hguard : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle := Or.inl hdead'
      simp [hguard] at h
    · rw [(bulk_keeps_quiet I w id w' i hi
        (fun d c ck hbad => by simp [hidle] at hbad) h).1]
      exact hidle
  | recvPrio id =>
    simp only [apply] at h
    unfold receivePrio at h
    cases hprio : (w.st id).prio with
    | nil => simp [hprio] at h
    | cons m ms =>
      simp [hprio] at h
      by_cases hi : i = id
      · have hdead' : (w.st id).life ≠ .alive := by rw [← hi]; exact hdead
        simp [hdead'] at h
      · split at h
        · simp at h
        · next w1 a1 hdel =>
          simp at h
          rcases h with ⟨_, hw⟩
          rw [← hw, setActor_other w1 id i a1 hi, deliver_st I w id _ m w1 a1 i hdel, hidle]
  | finish id =>
    simp only [apply] at h
    unfold finishWait at h
    cases hp : (w.st id).phase with
    | awaitEffect k =>
      simp [hp] at h
      cases h
      by_cases hi : i = id
      · rw [hi] at hidle
        simp [hp] at hidle
      · simp [setActor, hi, proceed, hidle]
    | awaitPeer k =>
      simp [hp] at h
      cases h
      by_cases hi : i = id
      · rw [hi] at hidle
        simp [hp] at hidle
      · simp [setActor, hi, proceed, hidle]
    | idle => simp [hp] at h
    | run _ => simp [hp] at h
    | parked _ _ _ => simp [hp] at h
    | awaitReply _ _ => simp [hp] at h
    | crashed => simp [hp] at h
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        let nid := InstId.peer template (w.nextIx template)
        by_cases hi : i = nid
        · simp [nid, readCells_st, setActor, hi, withTokens]
        · simp [nid, readCells_st, setActor, hi, hidle]
      · cases h

/-- A reachable non-idle phase belongs to a live actor. Death writes `.idle`. -/
theorem nonidle_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (i : InstId) (hph : (w.st i).phase ≠ .idle) :
    (w.st i).life = .alive := by
  induction hR generalizing i with
  | init =>
    have hidle : ((initWorld I N).st i).phase = .idle := by
      unfold initWorld
      rw [fold_read_st]
      cases hb : (coreRoster I.desc).contains i with
      | false =>
        show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).phase = .idle
        rw [hb]
        simp [absentActor]
      | true =>
        show (if (coreRoster I.desc).contains i = true then initActor I.desc i else absentActor).phase = .idle
        rw [hb]
        unfold initActor
        cases templateOf I.desc (tname i) with
        | none => simp [absentActor]
        | some _ => simp [withTokens]
    exact absurd hidle hph
  | step w w' a prev happ ih =>
    by_cases hlive : (w'.st i).life = .alive
    · exact hlive
    · by_cases h0 : (w.st i).life = .alive
      · obtain ⟨tail, toState, replyTo, t, hact, hrun, ht, hflag⟩ :=
          only_terminate_kills I a w w' i happ h0 hlive
        have hdie := terminate_commits I hL hG N w prev
          (inv3_reachable I hL hG N w prev).2 i
          ⟨.terminate :: tail, toState, replyTo⟩ tail hrun h0
        have hstep : w' = execRun I w i (w.st i) ⟨.terminate :: tail, toState, replyTo⟩ := by
          simp [apply, hact, execHead, h0, hrun] at happ
          exact happ.symm
        rw [hstep] at hph
        exact absurd hdie.2 hph
      · have hidle : (w.st i).phase = .idle := by
          by_cases hp : (w.st i).phase = .idle
          · exact hp
          · exact absurd (ih i hp) h0
        exact absurd (dead_stays_idle I a w w' i happ h0 hidle) hph

/-- Killing `terminate` empties the victim's box. -/
theorem kill_box_empty (I : Impl) (w : World) (id : InstId) (t : Template) (tail : List Eff)
    (toState : String) (replyTo : Option InstId)
    (ht : templateOf I.desc (tname id) = some t)
    (hflag : (t.terminable && !hasParkedCall (w.st id).parked) = true) :
    ((execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩).st id).box = [] := by
  let base :=
    refundParked (refundMsgs (readCells I.desc w id) (tname id) (w.st id).box) (tname id) (w.st id).parked
  let dead : Actor :=
    { base.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hstep : execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ =
      releaseParked (setActor base id dead) id (w.st id).parked := by
    simp [execRun, ht, hflag, base, dead]
  rw [hstep, release_box]
  simp [setActor, dead]

/-- Enqueueing does not put mail into a non-alive mailbox. -/
theorem enqueue_dead_box (w : World) (D : Description) (sender dst i : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hdead : (w.st i).life ≠ .alive) (hempty : (w.st i).box = []) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).box = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro m hm
  rcases enqueue_box_mem w D sender dst msg isCall k i m hm with hold | ⟨hid, _, hl⟩
  · simp [hempty] at hold
  · exact hdead (by rw [← hid] at hl; exact hl)

/-- A non-alive actor does not acquire bulk mail. -/
theorem dead_no_box (I : Impl) (a : Action) (w w' : World) (id : InstId)
    (h : apply I a w = some w') (hdead : (w.st id).life ≠ .alive)
    (hempty : (w.st id).box = []) : (w'.st id).box = [] := by
  cases a with
  | finish j => simpa [hempty] using finish_box w w' j id (by simpa [apply] using h)
  | recvPrio j => simpa [hempty] using prio_box I w w' j id (by simpa [apply] using h)
  | recvBulk j =>
    by_cases hji : id = j
    · simp only [apply] at h
      unfold receiveBulk at h
      have hguard : (w.st j).life ≠ .alive ∨ (w.st j).phase ≠ .idle := Or.inl (by simpa [hji] using hdead)
      simp [hji, hguard] at h
    · simpa [hempty] using bulk_other_box I w w' j id (by simpa [apply] using h) hji
  | spawn template =>
    simp only [apply] at h
    unfold spawn at h
    split at h
    · cases h
    · next t ht =>
      split at h
      · cases h
        simp only [readCells_st]
        by_cases hi : id = InstId.peer template (w.nextIx template)
        · simp [setActor, hi, withTokens]
        · simpa [setActor, hi] using hempty
      · cases h
  | exec j =>
    by_cases hji : id = j
    · rw [hji] at hdead
      simp only [apply] at h
      unfold execHead at h
      simp [hdead] at h
    · simp only [apply] at h
      unfold execHead at h
      by_cases hlj : (w.st j).life = .alive
      · simp [hlj] at h
        cases hp : (w.st j).phase with
        | run k =>
          simp [hp] at h
          cases h
          cases hk : k.rest with
          | nil => simp [execRun, hk, setActor, hji, hempty]
          | cons e tail =>
            cases e with
            | send name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_box, hempty]
              | some dstId =>
                simp [hr]
                simpa [hempty] using enqueue_dead_box w I.desc j dstId id
                  ({ label := label, sender := j, callFrom := none } : Msg) false (afterHead k) hdead hempty
            | call name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_box, hempty]
              | some dstId =>
                simp [hr]
                simpa [hempty] using enqueue_dead_box w I.desc j dstId id
                  ({ label := label, sender := j, callFrom := some j } : Msg) true (afterHead k) hdead hempty
            | trySend name label hint =>
              simp [execRun, hk]
              cases hr : route w I.desc name hint with
              | none => simp [hr, setActor, hji, proceed_box, hempty]
              | some dstId =>
                simp [hr]
                split
                · next hguard =>
                  have hlived : (w.st dstId).life = .alive := hguard.1.1
                  have hid : id ≠ dstId := fun h => hdead (by simpa [h] using hlived)
                  simp [setActor, hji, hid, chargeSender, bumpToken, proceed_box, hempty]
                · simp [setActor, hji, proceed_box, hempty]
            | reply =>
              simp [execRun, hk]
              unfold performReply
              cases k.replyTo with
              | none => simp [setActor, hji, proceed_box, hempty]
              | some caller =>
                cases hcall : (w.st caller).phase with
                | awaitReply dst' ck =>
                  by_cases hd : dst' = j
                  · by_cases hc : id = caller
                    · have hcj : caller ≠ j := fun h => hji (hc.trans h)
                      simp [hcall, hd, hc, hcj, setActor, proceed_box]
                      simpa [hc] using hempty
                    · simp [hcall, hd, hc, hji, setActor, proceed_box, hempty]
                  · simp [hcall, hd, hji, setActor, proceed_box, hempty]
                | idle => simp [hcall, hji, setActor, proceed_box, hempty]
                | run _ => simp [hcall, hji, setActor, proceed_box, hempty]
                | parked _ _ _ => simp [hcall, hji, setActor, proceed_box, hempty]
                | awaitEffect _ => simp [hcall, hji, setActor, proceed_box, hempty]
                | awaitPeer _ => simp [hcall, hji, setActor, proceed_box, hempty]
                | crashed => simp [hcall, hji, setActor, proceed_box, hempty]
            | selfSchedule _ =>
              simp [execRun, hk]
              split
              · simp [setActor, hji, proceed_box, hempty]
              · split
                · simp [setActor, hji, proceed_box, hempty]
                · simp [setActor, hji, hempty]
            | cell name label value =>
              simp only [execRun, hk]
              split
              · simp [setCell, setActor, hji, proceed_box, hempty]
              · let w1 : World := setActor (setCell w name label
                    { value := max (w.cell name label).value value, dirty := true }) j
                  (proceed ((setCell w name label
                    { value := max (w.cell name label).value value, dirty := true }).st j) (afterHead k))
                have hbase : (w1.st id).box = (w.st id).box := by
                  simp [w1, setCell, setActor, hji, proceed_box]
                rw [wakeReaders]
                have hw := wakes_box I.desc (readersOf w1 name) w1 label j id
                exact (hw.trans hbase).trans hempty
            | internal => simp [execRun, hk, setActor, hji, hempty]
            | peer => simp [execRun, hk, setActor, hji, hempty]
            | terminate =>
              cases ht : templateOf I.desc (tname j) with
              | none => simp [execRun, hk, ht, hempty]
              | some t =>
                by_cases hflag : (t.terminable && !hasParkedCall (w.st j).parked) = true
                · let base :=
                    refundParked (refundMsgs (readCells I.desc w j) (tname j) (w.st j).box) (tname j)
                      (w.st j).parked
                  let deadA : Actor :=
                    { base.st j with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
                  have hstep : execRun I w j (w.st j) k =
                      releaseParked (setActor base j deadA) j (w.st j).parked := by
                    simp [execRun, hk, ht, hflag, base, deadA]
                  rw [hstep, release_box]
                  have hbase : (base.st id).box = (w.st id).box := by
                    simp [base, readCells_st, refund_box, refundP_box]
                  simp [setActor, hji, hbase, hempty]
                · simp [execRun, hk, ht, hflag, hempty]
        | idle => simp [hp] at h
        | parked _ _ _ => simp [hp] at h
        | awaitReply _ _ => simp [hp] at h
        | awaitEffect _ => simp [hp] at h
        | awaitPeer _ => simp [hp] at h
        | crashed => simp [hp] at h
      · simp [hlj] at h

/-- A reachable mailbox that holds bulk mail belongs to a live actor. -/
theorem box_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id : InstId) (hne : (w.st id).box ≠ []) : (w.st id).life = .alive := by
  induction hR generalizing id with
  | init => exact absurd (init_box I N id).1 hne
  | step w w' a prev happ ih =>
    cases Classical.em ((w'.st id).life = .alive) with
    | inl hlive => exact hlive
    | inr hdead =>
      cases Classical.em ((w.st id).life = .alive) with
      | inl halive =>
        obtain ⟨tail, toState, replyTo, t, hact, hrun, ht, hflag⟩ :=
          only_terminate_kills I a w w' id happ halive hdead
        have hcleared := kill_box_empty I w id t tail toState replyTo ht hflag
        have hstep : w' = execRun I w id (w.st id) ⟨.terminate :: tail, toState, replyTo⟩ := by
          simp [apply, hact, execHead, halive, hrun] at happ
          exact happ.symm
        rw [hstep] at hne
        exact absurd hcleared hne
      | inr hdead0 =>
        have hempty : (w.st id).box = [] := by
          cases Classical.em ((w.st id).box = []) with
          | inl hempty => exact hempty
          | inr hne0 => exact absurd (ih id hne0) hdead0
        exact absurd (dead_no_box I a w w' id happ hdead0 hempty) hne

/-- While `c` stays in `awaitReply`, a missing call tag stays missing. -/
theorem no_mail_while_await (I : Impl) {N : Nat} (ρ : Run I N) (c d : InstId) (k : Cont) (i : Nat)
    (hstay : ∀ t, i ≤ t → ((ρ.cfg t).st c).phase = .awaitReply d k)
    (hno : ¬ anyCall (ρ.cfg i) c) : ∀ t, i ≤ t → ¬ anyCall (ρ.cfg t) c := by
  intro t ht
  have hstep : ∀ n, ¬ anyCall (ρ.cfg (i + n)) c := by
    intro n
    induction n with
    | zero => simpa using hno
    | succ n ih =>
      exact no_new_mailCall I (ρ.act (i + n)) (ρ.cfg (i + n)) (ρ.cfg (i + n + 1)) c d k
        (ρ.valid (i + n)) (hstay (i + n) (Nat.le_add_right _ _))
        (hstay (i + n + 1) (by omega)) ih
  simpa [Nat.add_sub_of_le ht] using hstep (t - i)

/-- Under `awaitReply d`, every tag naming `c` sits in `d`'s mailbox. -/
theorem mail_of_any (w : World) (hT : CallTagInv w) (c d : InstId) (k : Cont)
    (hph : (w.st c).phase = .awaitReply d k) (h : anyCall w c) : mailCall w d c := by
  have honly := only_call_here w hT c d k hph
  rcases h with ⟨i, m, hm, hc⟩ | ⟨i, p, hp, hc⟩
  · have hid := (honly i).1 m hm hc
    rw [hid] at hm
    exact Or.inl ⟨m, hm, hc⟩
  · have hid := (honly i).2 p hp hc
    rw [hid] at hp
    exact Or.inr ⟨p, hp, hc⟩

theorem duty_not_idle (c : InstId) (ph : Phase)
    (h : handlerOwes c ph ∨ replyPending c ph) (hidle : ph = .idle) : False := by
  rcases h with ⟨k, hk, _, _⟩ | ⟨k, hk, _, _⟩ <;> simp [carriedCont, hidle] at hk

/-- A stuck actor keeps a non-idle phase, so it stays alive. -/
theorem stuck_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (x : InstId) (i : Nat) (hS : Stuck ρ x i) :
    ∀ t, i ≤ t → ((ρ.cfg t).st x).life = .alive := by
  intro t ht
  have hne : waitKind ((ρ.cfg t).st x) ≠ none := by
    intro hnone
    exact (hS.2 t ht).2 ((hS.2 t ht).1.trans hnone)
  have hph : ((ρ.cfg t).st x).phase ≠ .idle := by
    intro hidle
    simp [waitKind, hidle] at hne
  exact nonidle_alive I hL hG N (ρ.cfg t) (cfg_reachable ρ t) x hph

/-- A stuck call cannot last. After admission the callee holds the reply obligation,
so it is never idle, against the lower-rank hypothesis. -/
theorem call_stuck_false (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat}
    (ρ : Run I N) (hF : Fair ρ)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (x dst : InstId) (i : Nat) (hS : Stuck ρ x i)
    (hkind : waitKind ((ρ.cfg i).st x) = some (.callReply dst))
    (hlower : ∀ (t : Nat) (y : InstId), rankAt hs (ρ.cfg t) y < rankAt hs (ρ.cfg i) x →
      (∀ u, t ≤ u → ((ρ.cfg u).st y).life = .alive) →
      (∀ u, t ≤ u → rankAt hs (ρ.cfg u) y < rankAt hs (ρ.cfg i) x) →
      ∀ u, t ≤ u → ∃ j, u ≤ j ∧ Idle (ρ.cfg j) y) : False := by
  obtain ⟨j, k, hj, hph, hfreeze⟩ :=
    call_admitted I hL hG ρ hF hs hok x dst i hS hkind hlower
  have hTj := call_tag_reachable I hL hG N (ρ.cfg j) (cfg_reachable ρ j)
  have hlive0 : ((ρ.cfg j).st dst).life = .alive := by
    rcases hTj.awaiting x dst k hph with hmail | howe | hpend
    · have hpos := (await_mail_in_box (ρ.cfg j) hTj x dst k hph hmail.1).1
      have hbox : ((ρ.cfg j).st dst).box ≠ [] := by
        intro hempty
        simp [hempty, callPos] at hpos
      exact box_alive I hL hG N (ρ.cfg j) (cfg_reachable ρ j) dst hbox
    · exact nonidle_alive I hL hG N (ρ.cfg j) (cfg_reachable ρ j) dst (by
        intro hidle
        exact duty_not_idle x _ (Or.inl howe.2.1) hidle)
    · exact nonidle_alive I hL hG N (ρ.cfg j) (cfg_reachable ρ j) dst (by
        intro hidle
        exact duty_not_idle x _ (Or.inr hpend.2.2) hidle)
  have hallK : ∀ t, i ≤ t → waitKind ((ρ.cfg t).st x) = some (.callReply dst) := by
    intro t ht
    exact (hS.2 t ht).1.symm.trans hkind
  have hrX (u : Nat) (hu : i ≤ u) :
      rankAt hs (ρ.cfg u) x = rankAt hs (ρ.cfg i) x := by
    have hty := parked_typestate_stays I ρ x i (u - i) (fun t ht1 _ => by
      have hwk := hallK t ht1
      rcases call_parked_or_await ((ρ.cfg t).st x) dst hwk with ⟨k', hk'⟩ | ⟨k', hk'⟩
      · exact Or.inl ⟨dst, true, k', hk'⟩
      · exact Or.inr ⟨dst, k', hk'⟩)
    rw [← Nat.add_sub_of_le hu]
    simp [rankAt, hty]
  have halive (t : Nat) (ht : j ≤ t) : ((ρ.cfg t).st dst).life = .alive := by
    have hgot := call_callee_alive I hL hG ρ x dst k j (t - j) (Or.inr hph)
      (fun u hu1 _ => hallK u (Nat.le_trans hj hu1)) hlive0
    simpa [Nat.add_sub_of_le ht] using hgot
  have hlow (u : Nat) (hu : j ≤ u) :
      rankAt hs (ρ.cfg u) dst < rankAt hs (ρ.cfg i) x := by
    have hht := call_height_below I hL hG ρ hs hok x dst k j (u - j) (Or.inr hph)
      (fun t ht1 _ => hallK t (Nat.le_trans hj ht1)) hlive0
    have hlt := hht.2
    rw [hrX j hj] at hlt
    simpa [Nat.add_sub_of_le hu] using hlt
  have hidle := hlower j dst (hlow j (Nat.le_refl _)) halive hlow
  have hcontra (t0 : Nat) (ht0 : j ≤ t0) (hnomail : ¬ mailCall (ρ.cfg t0) dst x) : False := by
    have hT0 := call_tag_reachable I hL hG N (ρ.cfg t0) (cfg_reachable ρ t0)
    have hnoany : ¬ anyCall (ρ.cfg t0) x := by
      intro hany
      exact hnomail (mail_of_any (ρ.cfg t0) hT0 x dst k (hfreeze t0 ht0) hany)
    have hkeep := no_mail_while_await I ρ x dst k t0 (fun t ht => hfreeze t (Nat.le_trans ht0 ht)) hnoany
    obtain ⟨j', hj', hId⟩ := hidle t0 ht0
    have hT' := call_tag_reachable I hL hG N (ρ.cfg j') (cfg_reachable ρ j')
    have hph' := hfreeze j' (Nat.le_trans ht0 hj')
    have hnom : ¬ mailCall (ρ.cfg j') dst x := by
      intro hm
      exact hkeep j' hj' (anyCall_mail (ρ.cfg j') dst x hm)
    rcases hT'.awaiting x dst k hph' with hmail | howe | hpend
    · exact hnom hmail.1
    · exact duty_not_idle x _ (Or.inl howe.2.1) hId.2
    · exact duty_not_idle x _ (Or.inr hpend.2.2) hId.2
  cases Classical.em (∃ t, j ≤ t ∧ ¬ mailCall (ρ.cfg t) dst x) with
  | inl hex =>
    obtain ⟨t, ht, hno⟩ := hex
    exact hcontra t ht hno
  | inr hnever =>
    have hall : ∀ t, j ≤ t → mailCall (ρ.cfg t) dst x := by
      intro t ht
      cases Classical.em (mailCall (ρ.cfg t) dst x) with
      | inl hm => exact hm
      | inr hno => exact absurd ⟨t, ht, hno⟩ hnever
    have hio : ∀ t, ∃ j', t ≤ j' ∧ CanReceive (ρ.cfg j') dst := by
      intro t
      let u := max t j
      obtain ⟨j', hj', hId⟩ := hidle u (Nat.le_max_right _ _)
      have hjI : j ≤ j' := Nat.le_trans (Nat.le_max_right t j) hj'
      have hpos := (await_mail_in_box (ρ.cfg j')
        (call_tag_reachable I hL hG N (ρ.cfg j') (cfg_reachable ρ j')) x dst k
        (hfreeze j' hjI) (hall j' hjI)).1
      have hbox : ((ρ.cfg j').st dst).box ≠ [] := by
        intro hempty
        simp [hempty, callPos] at hpos
      exact ⟨j', Nat.le_trans (Nat.le_max_left _ _) hj', ⟨hId, Or.inl hbox⟩⟩
    have hpos := (await_mail_in_box (ρ.cfg j) hTj x dst k hph (hall j (Nat.le_refl _))).1
    obtain ⟨j2, hj2, hno, _, _⟩ := call_delivered I hL hG ρ hF x dst k
      (callPos ((ρ.cfg j).st dst).box x) j hfreeze halive (Nat.le_refl _) hpos hio
    exact hcontra j2 hj2 hno

/-- An actor that stays alive and below height `h` is idle infinitely often. -/
theorem below_idle (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true) :
    ∀ h t x, rankAt hs (ρ.cfg t) x < h →
      (∀ u, t ≤ u → ((ρ.cfg u).st x).life = .alive) →
      (∀ u, t ≤ u → rankAt hs (ρ.cfg u) x < h) →
      ∀ u, t ≤ u → ∃ j, u ≤ j ∧ Idle (ρ.cfg j) x := by
  intro h
  induction h using Nat.strongRecOn with
  | ind h ih =>
    intro t x hrank halive hstay u hu
    have hfree : ∀ v, t ≤ v → ¬ Stuck ρ x v := by
      intro v hv hStuck
      have hlower : ∀ (t' : Nat) (y : InstId),
          rankAt hs (ρ.cfg t') y < rankAt hs (ρ.cfg v) x →
          (∀ u', t' ≤ u' → ((ρ.cfg u').st y).life = .alive) →
          (∀ u', t' ≤ u' → rankAt hs (ρ.cfg u') y < rankAt hs (ρ.cfg v) x) →
          ∀ u', t' ≤ u' → ∃ j, u' ≤ j ∧ Idle (ρ.cfg j) y :=
        fun t' y hr hlive' hrank' u' hu' =>
          ih (rankAt hs (ρ.cfg v) x) (hstay v hv) t' y hr hlive' hrank' u' hu'
      cases hwk : waitKind ((ρ.cfg v).st x) with
      | none => exact (hStuck.1).2 hwk
      | some kind =>
        cases kind with
        | effect => exact not_stuck_effect_assumed ρ hA hF x v hStuck hwk
        | peer => exact not_stuck_peer_assumed ρ hA hF x v hStuck hwk
        | cell => exact absurd hwk (waitKind_ne_cell _)
        | blockingSend dst =>
          exact send_stuck_false I hL hG ρ hF hs hok x dst v hStuck hwk hlower
        | callReply dst =>
          exact call_stuck_false I hL hG ρ hF hs hok x dst v hStuck hwk hlower
    exact idle_when_free I hL hG ρ hF x t halive (fun v hv => hfree v hv) u hu

/-- No actor in a fair run stays blocked. -/
theorem never_stuck (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) (x : InstId) (t : Nat) (hS : Stuck ρ x t) : False := by
  obtain ⟨hs, hok⟩ := hG.ranked
  have halive := stuck_alive I hL hG ρ x t hS
  cases hwk : waitKind ((ρ.cfg t).st x) with
  | none => exact hS.1.2 hwk
  | some kind =>
    cases kind with
    | effect => exact not_stuck_effect_assumed ρ hA hF x t hS hwk
    | peer => exact not_stuck_peer_assumed ρ hA hF x t hS hwk
    | cell => exact absurd hwk (waitKind_ne_cell _)
    | blockingSend dst =>
      have hr (u : Nat) (hu : t ≤ u) :
          rankAt hs (ρ.cfg u) x = rankAt hs (ρ.cfg t) x := by
        have hty := parked_typestate_stays I ρ x t (u - t) (fun s hs1 _ => by
          have hkind := (hS.2 s hs1).1.symm.trans hwk
          obtain ⟨k, hk⟩ := blocking_parked ((ρ.cfg s).st x) dst hkind
          exact Or.inl ⟨dst, false, k, hk⟩)
        rw [← Nat.add_sub_of_le hu]
        simp [rankAt, hty]
      obtain ⟨j, hj, hId⟩ := below_idle I hL hG hA ρ hF hs hok
        (rankAt hs (ρ.cfg t) x + 1) t x (by omega) halive
        (fun u hu => by rw [hr u hu]; omega) t (Nat.le_refl _)
      have hne : waitKind ((ρ.cfg j).st x) ≠ none := by
        intro hnone
        exact (hS.2 j hj).2 ((hS.2 j hj).1.trans hnone)
      simp [waitKind, hId.2] at hne
    | callReply dst =>
      have hr (u : Nat) (hu : t ≤ u) :
          rankAt hs (ρ.cfg u) x = rankAt hs (ρ.cfg t) x := by
        have hty := parked_typestate_stays I ρ x t (u - t) (fun s hs1 _ => by
          have hkind := (hS.2 s hs1).1.symm.trans hwk
          rcases call_parked_or_await ((ρ.cfg s).st x) dst hkind with ⟨k, hk⟩ | ⟨k, hk⟩
          · exact Or.inl ⟨dst, true, k, hk⟩
          · exact Or.inr ⟨dst, k, hk⟩)
        rw [← Nat.add_sub_of_le hu]
        simp [rankAt, hty]
      obtain ⟨j, hj, hId⟩ := below_idle I hL hG hA ρ hF hs hok
        (rankAt hs (ρ.cfg t) x + 1) t x (by omega) halive
        (fun u hu => by rw [hr u hu]; omega) t (Nat.le_refl _)
      have hne : waitKind ((ρ.cfg j).st x) ≠ none := by
        intro hnone
        exact (hS.2 j hj).2 ((hS.2 j hj).1.trans hnone)
      simp [waitKind, hId.2] at hne

/-- A fair reachable run has no actor blocked forever on a send or a call. -/
theorem deadlock_freedom (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (hA : Assumptions I)
    {N : Nat} (ρ : Run I N) (hF : Fair ρ) : ¬ Deadlock ρ := by
  intro hD
  obtain ⟨s, i, _, hS, _⟩ := deadlock_kind ρ hA hF hD
  exact never_stuck I hL hG hA ρ hF s i hS

/-- A priority message whose label is `l`. -/
def hasLabel (ms : List Msg) (l : String) : Prop :=
  ∃ m, m ∈ ms ∧ m.label = l

theorem hasLabel_any (ms : List Msg) (l : String) (h : hasLabel ms l) :
    (ms.any fun p => p.label == l) = true := by
  rcases h with ⟨m, hm, hl⟩
  induction ms with
  | nil => cases hm
  | cons p ps ih =>
    cases hm with
    | head => simp [List.any_cons, hl]
    | tail _ ht =>
      have ih' := ih ht
      rw [List.any_cons]
      by_cases hp : p.label = l
      · simp [hp]
      · have hf : (p.label == l) = false := by simpa [beq_iff_eq] using hp
        simpa [hf] using ih'

theorem any_hasLabel (ms : List Msg) (l : String) (h : (ms.any fun p => p.label == l) = true) :
    hasLabel ms l := by
  induction ms with
  | nil => simp at h
  | cons p ps ih =>
    rw [List.any_cons] at h
    by_cases hp : (p.label == l) = true
    · exact ⟨p, List.Mem.head _, (beq_iff_eq).mp hp⟩
    · have hf : (p.label == l) = false := by
        cases hb : p.label == l <;> simp_all
      rw [hf, Bool.false_or] at h
      obtain ⟨m, hm, hl⟩ := ih h
      exact ⟨m, List.Mem.tail _ hm, hl⟩

theorem not_hasLabel_any (ms : List Msg) (l : String) (h : ¬ hasLabel ms l) :
    (ms.any fun p => p.label == l) = false := by
  cases ha : (ms.any fun p => p.label == l)
  · rfl
  · exact absurd (any_hasLabel ms l ha) h

theorem upsert_hasLabel (ms : List Msg) (m : Msg) (l : String) (h : hasLabel ms l) :
    hasLabel (upsertPrio ms m) l := by
  rcases h with ⟨p, hp, hl⟩
  unfold upsertPrio
  by_cases hany : (ms.any fun q => q.label == m.label) = true
  · simpa [hany] using ⟨p, hp, hl⟩
  · refine ⟨p, ?_, hl⟩
    have hf : (ms.any fun q => q.label == m.label) = false := by
      cases hb : (ms.any fun q => q.label == m.label) <;> simp_all
    simp [hf]
    exact Or.inl hp

theorem tryWake_hasLabel (D : Description) (w : World) (dstId : InstId) (label wake : String)
    (writer i : InstId) (h : hasLabel ((w.st i).prio) wake) :
    hasLabel (((tryWake D w dstId label writer).st i).prio) wake := by
  unfold tryWake
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [hif, setActor]
    by_cases hi : i = dstId
    · simpa [hi] using upsert_hasLabel _ _ wake h
    · simpa [hi] using h
  · simpa [hif] using h

theorem tryWake_install (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) (hlive : (w.st dstId).life = .alive)
    (hroom : (w.st dstId).prio.length < capPrio D w.N dstId)
    (hfresh : ((w.st dstId).prio.any fun p => p.label == label) = false) :
    hasLabel (((tryWake D w dstId label writer).st dstId).prio) label := by
  unfold tryWake
  simp [hlive, hroom, hfresh, upsertPrio, setActor]
  exact ⟨{ label := label, sender := writer, callFrom := none },
    List.mem_append.mpr (Or.inr (List.Mem.head _)), rfl⟩

theorem fold_tryWake_hasLabel (D : Description) (ids : List InstId) (w : World)
    (label : String) (writer r : InstId) (wake : String)
    (h : hasLabel ((w.st r).prio) wake) :
    hasLabel (((ids.foldl (fun w id => tryWake D w id label writer) w).st r).prio) wake := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact ih _ (tryWake_hasLabel D w j label wake writer r h)

/-- The latest index `≤ n` at which `d` is false. `d 0` is false. -/
def lastClean (d : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if d (n + 1) = false then n + 1 else lastClean d n

theorem lastClean_spec (d : Nat → Bool) (n : Nat) (h0 : d 0 = false) :
    lastClean d n ≤ n ∧ d (lastClean d n) = false ∧
      ∀ u, lastClean d n < u → u ≤ n → d u = true := by
  induction n with
  | zero =>
    refine ⟨Nat.le_refl _, h0, ?_⟩
    intro u hu hun
    omega
  | succ n ih =>
    by_cases h : d (n + 1) = false
    · simp [lastClean, h]
      intro u hu hun
      omega
    · have ht : d (n + 1) = true := by cases hb : d (n + 1) <;> simp_all
      simp [lastClean, h]
      refine ⟨Nat.le_trans ih.1 (Nat.le_succ _), ih.2.1, ?_⟩
      intro u hu hun
      have hle : u ≤ n ∨ u = n + 1 := by omega
      cases hle with
      | inl hlu => exact ih.2.2 u hu hlu
      | inr heq => simpa [heq] using ht

theorem core_of_one (D : Description) (dst : String) (t : Template)
    (ht : templateOf D dst = some t) (hone : t.multiplicity = .one) :
    InstId.core dst ∈ coreRoster D := by
  have hname := template_name D dst t ht
  rw [coreRoster]
  refine List.mem_filterMap.mpr ⟨t, template_mem D dst t ht, ?_⟩
  rw [hone]
  have hb : (Multiplicity.one == Multiplicity.one) = true := rfl
  simp [hb, hname]

theorem init_core_alive (I : Impl) (N : Nat) (dst : String) (t : Template)
    (ht : templateOf I.desc dst = some t) (hone : t.multiplicity = .one) :
    ((initWorld I N).st (InstId.core dst)).life = .alive := by
  have hmem := core_of_one I.desc dst t ht hone
  unfold initWorld
  rw [fold_read_st]
  simp [hmem, initActor, tname, ht, withTokens]

theorem core_alive (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) {N : Nat} (ρ : Run I N)
    (dst : String) (t : Template) (ht : templateOf I.desc dst = some t)
    (hone : t.multiplicity = .one) (hterm : t.terminable = false) :
    ∀ n, ((ρ.cfg n).st (InstId.core dst)).life = .alive := by
  intro n
  induction n with
  | zero => simpa [ρ.start] using init_core_alive I N dst t ht hone
  | succ n ih =>
    by_cases hdie : ((ρ.cfg (n + 1)).st (InstId.core dst)).life = .alive
    · exact hdie
    · obtain ⟨tail, toState, replyTo, t', _, _, ht', hflag⟩ :=
        only_terminate_kills I (ρ.act n) (ρ.cfg n) (ρ.cfg (n + 1)) (InstId.core dst)
          (ρ.valid n) ih hdie
      have hto : templateOf I.desc dst = some t' := by simpa [tname] using ht'
      have hsame : t' = t := by
        injection (hto.symm.trans ht)
      simp [hsame, hterm] at hflag

theorem readCells_value (D : Description) (w : World) (reader : InstId) (d l : String) :
    ((readCells D w reader).cell d l).value = (w.cell d l).value := by
  unfold readCells
  induction cellLabels D (tname reader) generalizing w with
  | nil => simp
  | cons lab labs ih =>
    simp only [List.foldl_cons]
    have hstep : ((setObserved
        (setCell w (tname reader) lab { (w.cell (tname reader) lab) with dirty := false })
        reader lab (w.cell (tname reader) lab).value).cell d l).value = (w.cell d l).value := by
      simp [setObserved, setCell]
      by_cases hd : d = tname reader
      · by_cases hl : l = lab <;> simp [hd, hl]
      · simp [hd]
    exact (ih _).trans hstep

theorem edge_in_prio (I : Impl) (dst label : String) (h : label ∈ cellLabels I.desc dst) :
    label ∈ prioLabels I dst := by
  have hmem : label ∈
      (I.transitions.filterMap fun tr =>
        if tr.template == dst then some (selfLabels tr.program) else none).flatten ++
      cellLabels I.desc dst ++
      (I.transitions.map fun tr => cellWakeLabels dst tr.program).flatten := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
  simpa [prioLabels] using mem_dedup _ label hmem

theorem deliver_noncall (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (hl : a.life = .alive) (hc : m.callFrom = none) :
    ∃ w1 a1, deliver I w id a m = some (w1, a1) := by
  simp [deliver, hl, hc]
  split
  · exact ⟨_, _, rfl⟩
  · rename_i tr _
    have hsome : m.callFrom.isSome = false := by simp [hc]
    simp [hsome]

theorem recv_prio_enabled (I : Impl) (w : World) (r : InstId) (label : String) (hT : CallTagInv w)
    (hlive : (w.st r).life = .alive) (hidle : (w.st r).phase = .idle)
    (hhas : hasLabel ((w.st r).prio) label) :
    Enabled I w (.recvPrio r) := by
  rcases hhas with ⟨m, hm, _⟩
  cases hp : (w.st r).prio with
  | nil => simp [hp] at hm
  | cons m0 ms =>
    have hplain : m0.callFrom = none := hT.prioPlain r m0 (by simp [hp])
    obtain ⟨w1, a1, hdel⟩ := deliver_noncall I w r { (w.st r) with prio := ms } m0
      (by simp [hlive]) hplain
    have hdel' : deliver I w r
        { life := (w.st r).life, typestate := (w.st r).typestate, phase := (w.st r).phase,
          box := (w.st r).box, prio := ms, parked := (w.st r).parked,
          tokens := (w.st r).tokens } m0 = some (w1, a1) := by
      simpa [hlive, hidle] using hdel
    unfold Enabled apply receivePrio
    simp [hp, hlive, hidle]
    rw [hlive, hidle] at hdel'
    simp [hdel']

end Deadlock
