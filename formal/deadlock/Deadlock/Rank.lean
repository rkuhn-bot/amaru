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

end Deadlock
