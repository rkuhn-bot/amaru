import Deadlock.Occ

set_option autoImplicit false

namespace Deadlock

/-- A terminable actor's continuation does not send, call, or self-schedule.
This is narrower than Amaru: a per-peer stage can terminate and still have sent
to a shared stage. -/
def BulkFree (I : Impl) (w : World) : Prop :=
  ∀ id, terminableName I.desc (tname id) → noBulkSend (contRest (w.st id).phase) = true

def Inv2 (I : Impl) (w : World) : Prop :=
  Inv I w ∧ OccInv I w ∧ TyOk I.desc w ∧ BulkFree I w

theorem nobulk_empty : noBulkSend [] = true := rfl

theorem nobulk_idle (a : Actor) (h : a.phase = .idle ∨ a.phase = .crashed) :
    noBulkSend (contRest a.phase) = true := by
  rcases h with h | h <;> simp [contRest, h, nobulk_empty]

theorem terminable_program (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions)
    (t : Template) (ht : templateOf I.desc tr.template = some t) (hterm : t.terminable = true) :
    noBulkSend tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  simp only [transitionOk, ht, hterm, ite_true] at hok
  repeat rw [Bool.and_eq_true] at hok
  exact hok.2

theorem bulk_init (I : Impl) (N : Nat) : BulkFree I (initWorld I N) := by
  intro id hterm
  have hph := init_phase I N id
  simp [contRest, hph, nobulk_empty]

theorem inv2_init (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) :
    Inv2 I (initWorld I N) :=
  ⟨inv_init I N hL, occ_init I hG N, ty_init I hG N, bulk_init I N⟩

theorem occ_apply (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (a : Action) (w w' : World)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hT : TyOk I.desc w) (hB : BulkFree I w)
    (h : apply I a w = some w') : OccInv I w' := by
  cases a with
  | recvBulk id =>
    simpa [apply] using occ_bulk I hL hG w id w' hO hS hM h
  | recvPrio id =>
    simpa [apply] using occ_prio I hL hG w id w' hO h
  | exec id =>
    simpa [apply] using occ_head I hL w w' id hO hT hS h
      (fun k hph ht => by simpa [contRest, hph] using hB id ht)
  | finish id =>
    simpa [apply] using occ_finish I w w' id hO hS h
  | spawn template =>
    simpa [apply] using occ_spawn I w w' template hO h
  | ingress dst label =>
    simpa [apply] using occ_ingress I w w' dst label hO h
  | kill sub key =>
    rw [kill_apply_world I w w' sub key h]
    exact occ_kill I hG w sub key hO hS.cont
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hO

theorem nobulk_drop (es : List Eff) (n : Nat) (h : noBulkSend es = true) : noBulkSend (es.drop n) = true := by
  induction n generalizing es with
  | zero => simpa using h
  | succ n ih =>
    cases es with
    | nil => exact nobulk_empty
    | cons e es => exact ih _ (noBulk_tail e es h)

theorem after_nobulk (a : Actor) (k : Cont) (h : noBulkSend k.rest = true) :
    noBulkSend (contRest (proceed a (afterHead k)).phase) = true := by
  cases hk : k.rest with
  | nil =>
    simp [proceed, afterHead, hk, contRest]
    exact nobulk_empty
  | cons e es =>
    have htail := noBulk_tail e es (by simpa [hk] using h)
    cases es with
    | nil =>
      simp [proceed, afterHead, hk, contRest]
      exact nobulk_empty
    | cons _ _ => simp [proceed, afterHead, hk, List.tail_cons, contRest, htail]

theorem resume_nobulk (a : Actor) (b : Bool) (dst : InstId) (h : noBulkSend (contRest a.phase) = true) :
    noBulkSend (contRest (resumeSender a b dst).phase) = true := by
  cases hph : a.phase with
  | parked _ _ k =>
    have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using h
    cases b with
    | true => simpa [resumeSender, hph, contRest] using hrest
    | false =>
      cases hk : k.rest with
      | nil =>
        simp [resumeSender, hph, proceed, hk, contRest]
        exact nobulk_empty
      | cons _ _ => simpa [resumeSender, hph, proceed, hk, contRest] using hrest
  | idle =>
    simp [resumeSender, hph, contRest]
    exact nobulk_empty
  | run k => simpa [resumeSender, hph, contRest] using h
  | awaitReply _ k => simpa [resumeSender, hph, contRest] using h
  | awaitEffect k => simpa [resumeSender, hph, contRest] using h
  | awaitPeer k => simpa [resumeSender, hph, contRest] using h
  | crashed =>
    simp [resumeSender, hph, contRest]
    exact nobulk_empty

theorem deliver_nobulk (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1))
    (hterm : terminableName I.desc (tname id)) :
    noBulkSend (contRest a1.phase) = true := by
  obtain ⟨t, ht, htm⟩ := hterm
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · next heq =>
      split at h
      · cases h
      · cases h
        simp [contRest]
        exact nobulk_empty
    · next tr heq =>
      split at h
      · cases h
      · cases h
        have hmem := findTr_mem I (tname id) a.typestate m.label tr heq
        have hprog := terminable_program I hL tr hmem.1 t (by simpa [hmem.2.1] using ht) htm
        by_cases hempty : tr.program.isEmpty = true
        · simp [hempty, contRest]
          exact nobulk_empty
        · simp [hempty, contRest, hprog]

theorem bulk_or (I : Impl) (w w' : World) (hB : BulkFree I w)
    (h : ∀ id, terminableName I.desc (tname id) →
      noBulkSend (contRest (w'.st id).phase) = true ∨ (w'.st id).phase = (w.st id).phase) :
    BulkFree I w' := by
  intro id ht
  rcases h id ht with h | h
  · exact h
  · simpa [h] using hB id ht

theorem enqueue_phase_other (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hne : i ≠ sender) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).phase = (w.st i).phase := by
  cases isCall <;>
    (unfold enqueueOrPark
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive]
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom]
         by_cases hsame : sender = dst
         · have hdst : i ≠ dst := fun h => hne (h.trans hsame.symm)
           simp [hsame, setActor, hdst]
         · simp [hsame, setActor]
           by_cases hid : i = dst
           · have hflip : dst ≠ sender := fun h => hsame h.symm
             simp [setActor, hid, hflip]
           · simp [setActor, hid, hne]
       · simp [hroom]
         by_cases hsame : sender = dst
         · have hdst : i ≠ dst := fun h => hne (h.trans hsame.symm)
           simp [hsame, setActor, hdst]
         · simp [hsame, setActor]
           by_cases hid : i = dst
           · have hflip : dst ≠ sender := fun h => hsame h.symm
             simp [setActor, hid, hflip]
           · simp [setActor, hid, hne]
     · simp [hlive, setActor, hne])

theorem phase_credit (w : World) (dst : String) (s i : InstId) :
    ((creditSender w dst s).st i).phase = (w.st i).phase :=
  (credit_life w dst s i).2.2.1

theorem phase_refund (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).phase = (w.st i).phase :=
  (refund_life w dst ms i).2.2.1

theorem phase_refundP (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).phase = (w.st i).phase :=
  (refundP_life w dst ps i).2.2.1

theorem bulk_finish (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : finishWait I w id = some w') : BulkFree I w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    apply bulk_or I w _ hB
    intro i ht
    by_cases hi : i = id
    · rw [hi] at ht ⊢
      have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using hB id ht
      cases hk : k.rest with
      | nil => simp [setActor, proceed, hk, contRest, nobulk_empty]
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    rw [← hw]
    apply bulk_or I w _ hB
    intro i ht
    by_cases hi : i = id
    · rw [hi] at ht ⊢
      have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using hB id ht
      cases hk : k.rest with
      | nil => simp [setActor, proceed, hk, contRest, nobulk_empty]
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

/-- An ingress delivery leaves every phase where it was, so a bulk-free world stays bulk-free. -/
theorem bulk_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String) (hB : BulkFree I w)
    (h : receiveIngress I w dst label = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro id _
  exact Or.inr (ingress_phase I w w' dst label id h).1

theorem bulk_spawn (I : Impl) (w w' : World) (template : String) (hB : BulkFree I w)
    (h : spawn I w template = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro i ht
  unfold spawn at h
  split at h
  · cases h
  · next t _ =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      by_cases hi : i = InstId.peer template (w.nextIx template)
      · simpa [readCells_st, setActor, hi, withTokens, contRest] using Or.inl nobulk_empty
      · simpa [readCells_st, setActor, hi] using Or.inr rfl
    · simp [hif] at h

theorem release_bulk (I : Impl) (w : World) (id : InstId) (ps : List Parked)
    (hB : BulkFree I w) : BulkFree I (releaseParked w id ps) := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using hB
  | cons p ps ih =>
    unfold releaseParked
    simp only [List.foldl_cons]
    by_cases hskip : p.isCall = true ∨ p.sender = id
    · simp [hskip]
      simpa [releaseParked] using ih w hB
    · simp [hskip]
      have hB' : BulkFree I (setActor w p.sender (resumeSender (w.st p.sender) false id)) := by
        apply bulk_or I w _ hB
        intro i ht
        by_cases hi : i = p.sender
        · rw [hi] at ht ⊢
          simp [setActor]
          exact Or.inl (resume_nobulk (w.st p.sender) false id (hB p.sender ht))
        · simp [setActor, hi]
      simpa [releaseParked] using ih _ hB'

theorem try_wake_phase (D : Description) (w : World) (dstId : InstId) (label : String) (writer i : InstId) :
    ((tryWake D w dstId label writer).st i).phase = (w.st i).phase := by
  by_cases hif : ((w.st dstId).life == .alive &&
      decide ((w.st dstId).prio.length < capPrio D w.N dstId) &&
      !((w.st dstId).prio.any fun p => p.label == label)) = true
  · simp [tryWake, hif, setActor]
    by_cases hi : i = dstId <;> simp [hi]
  · simp [tryWake, hif]

theorem wakes_phase (ids : List InstId) (D : Description) (w : World) (dst label : String)
    (writer i : InstId) :
    ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).phase = (w.st i).phase := by
  induction ids generalizing w with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, try_wake_phase]

theorem bulk_exec (I : Impl) (w : World) (id : InstId) (k : Cont) (hB : BulkFree I w)
    (hph : (w.st id).phase = .run k) : BulkFree I (execRun I w id (w.st id) k) := by
  apply bulk_or I w _ hB
  intro i ht
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      by_cases hi : i = id
      · rw [hi] at ht ⊢
        simp [execRun, hrest, setActor, contRest, nobulk_empty]
      · simp [execRun, hrest, setActor, hi]
    | cons e es =>
      cases e with
      | send dst label hint =>
        by_cases hi : i = id
        · rw [hi] at ht
          have hbad := hB id ht
          simp [contRest, hph, hrest, noBulkSend] at hbad
        · simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none => simp [hr, setActor, hi]
          | some dstId =>
            simp [hr]
            exact Or.inr (enqueue_phase_other w I.desc id dstId { label := label, sender := id, callFrom := none } false
              ⟨es, toState, replyTo⟩ i hi)
      | call dst label hint =>
        by_cases hi : i = id
        · rw [hi] at ht
          have hbad := hB id ht
          simp [contRest, hph, hrest, noBulkSend] at hbad
        · simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none => simp [hr, setActor, hi]
          | some dstId =>
            simp [hr]
            exact Or.inr (enqueue_phase_other w I.desc id dstId { label := label, sender := id, callFrom := some id } true
              ⟨es, toState, replyTo⟩ i hi)
      | trySend dst label hint =>
        by_cases hi : i = id
        · rw [hi] at ht
          have hbad := hB id ht
          simp [contRest, hph, hrest, noBulkSend] at hbad
        · simp [execRun, hrest]
          cases hr : route w I.desc id dst with
          | none => simp [hr, setActor, hi]
          | some dstId =>
            simp [hr]
            split
            · exact Or.inr (enqueue_phase_other w I.desc id dstId
                { label := label, sender := id, callFrom := none, reliable := false } false
                ⟨es, toState, replyTo⟩ i hi)
            · simp [setActor, hi]
      | reply =>
        simp [execRun, hrest]
        unfold performReply
        cases hto : replyTo with
        | none =>
          simp [hto, setActor]
          by_cases hi : i = id
          · rw [hi] at ht ⊢
            simp [setActor]
            exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, none⟩
              (by simpa [contRest, hph, hrest] using hB id ht))
          · simp [hi]
        | some caller =>
          simp [hto]
          cases hcall : (w.st caller).phase with
          | awaitReply dst ck =>
            by_cases hd : dst = id
            · simp [hd, setActor]
              by_cases hi : i = id
              · rw [hi] at ht ⊢
                simp [setActor]
                exact Or.inl (after_nobulk
                  (if id = caller then proceed (w.st caller) ck else w.st id)
                  ⟨.reply :: es, toState, some caller⟩
                  (by simpa [contRest, hph, hrest] using hB id ht))
              · by_cases hc : i = caller
                · by_cases hself : caller = id
                  · exact absurd (hc.trans hself) hi
                  · rw [hc] at ht ⊢
                    simp [setActor, hi, hself]
                    have hold : noBulkSend ck.rest = true := by simpa [contRest, hcall] using hB caller ht
                    cases hk : ck.rest with
                    | nil =>
                      simp [proceed, hk, contRest]
                      exact Or.inl nobulk_empty
                    | cons _ _ =>
                      simp [proceed, hk, contRest]
                      exact Or.inl (by simpa [hk] using hold)
                · simp [setActor, hi, hc]
            · simp [hd, setActor]
              by_cases hi : i = id
              · rw [hi] at ht ⊢
                simp [setActor]
                exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                  (by simpa [contRest, hph, hrest] using hB id ht))
              · simp [hi]
          | idle =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
          | run ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
          | parked dst b ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
          | awaitEffect ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
          | awaitPeer ck =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
          | crashed =>
            simp [setActor]
            by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor]
              exact Or.inl (after_nobulk (w.st id) ⟨.reply :: es, toState, some caller⟩
                (by simpa [contRest, hph, hrest] using hB id ht))
            · simp [hi]
      | selfSchedule label =>
        simp only [execRun, hrest]
        split
        · by_cases hi : i = id
          · rw [hi] at ht ⊢
            have htail := noBulk_tail (.selfSchedule label) es
              (by simpa [contRest, hph, hrest] using hB id ht)
            cases hes : es with
            | nil => simp [setActor, proceed, afterHead, hes, contRest, nobulk_empty]
            | cons _ _ =>
              simp [setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setActor, hi]
        · split
          · by_cases hi : i = id
            · rw [hi] at ht ⊢
              have htail := noBulk_tail (.selfSchedule label) es
                (by simpa [contRest, hph, hrest] using hB id ht)
              cases hes : es with
              | nil => simp [setActor, proceed, afterHead, hes, contRest, nobulk_empty]
              | cons _ _ =>
                simp [setActor, proceed, afterHead, hes, contRest]
                exact Or.inl (by simpa [hes] using htail)
            · simp [setActor, hi]
          · by_cases hi : i = id
            · rw [hi] at ht ⊢
              simp [setActor, contRest, nobulk_empty]
            · simp [setActor, hi]
      | cell dst label value =>
        simp only [execRun, hrest]
        split
        · by_cases hi : i = id
          · rw [hi] at ht ⊢
            have htail := noBulk_tail (.cell dst label value) es
              (by simpa [contRest, hph, hrest] using hB id ht)
            cases hes : es with
            | nil => simp [setCell, setActor, proceed, afterHead, hes, contRest, nobulk_empty]
            | cons _ _ =>
              simp [setCell, setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setCell, setActor, hi]
        · simp only [wakeReaders]
          rw [wakes_phase (readersOf _ dst) I.desc _ dst label id i]
          by_cases hi : i = id
          · rw [hi] at ht ⊢
            have htail := noBulk_tail (.cell dst label value) es
              (by simpa [contRest, hph, hrest] using hB id ht)
            cases hes : es with
            | nil => simp [setCell, setActor, proceed, afterHead, hes, contRest, nobulk_empty]
            | cons _ _ =>
              simp [setCell, setActor, proceed, afterHead, hes, contRest]
              exact Or.inl (by simpa [hes] using htail)
          · simp [setCell, setActor, hi]
      | internal =>
        by_cases hi : i = id
        · rw [hi] at ht ⊢
          have htail := noBulk_tail (.internal) es
            (by simpa [contRest, hph, hrest] using hB id ht)
          simp [execRun, hrest, setActor, contRest]
          exact Or.inl htail
        · simp [execRun, hrest, setActor, hi]
      | peer =>
        by_cases hi : i = id
        · rw [hi] at ht ⊢
          have htail := noBulk_tail (.peer) es
            (by simpa [contRest, hph, hrest] using hB id ht)
          simp [execRun, hrest, setActor, contRest]
          exact Or.inl htail
        · simp [execRun, hrest, setActor, hi]
      | terminate =>
        simp [execRun, hrest]
        cases htpl : templateOf I.desc (tname id) with
        | none => simp [htpl]
        | some t =>
          by_cases hkill : t.terminable = true ∧ hasParkedCall (w.st id).parked = false
          · simp [htpl, hkill]
            let wR := readCells I.desc w id
            let wM := refundMsgs wR (tname id) (w.st id).box
            let wP := refundParked wM (tname id) (w.st id).parked
            let dead : Actor :=
              { wP.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
            have hpre : BulkFree I (setActor wP id dead) := by
              apply bulk_or I w _ hB
              intro j _
              by_cases hj : j = id
              · rw [hj]
                simp [setActor, dead, contRest, nobulk_empty]
              · have hphj : (wP.st j).phase = (w.st j).phase := by
                  simp [wP, wM, wR, phase_refundP, phase_refund, readCells_st]
                simp [setActor, hj, hphj]
            exact Or.inl ((release_bulk I (setActor wP id dead) id (w.st id).parked hpre) i ht)
          · simp [htpl, hkill]

theorem bulk_head (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : execHead I w id = some w') : BulkFree I w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life = .alive
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact bulk_exec I w id k hB hph
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h
  · simp [hlive] at h

theorem place_bulk (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor) (dst : String) (sender : InstId)
    (hn : terminableName I.desc (tname id) → noBulkSend (contRest a1.phase) = true)
    (hst : ∀ i, w1.st i = w.st i) (hB : BulkFree I w) :
    BulkFree I (creditSender (setActor w1 id a1) dst sender) := by
  apply bulk_or I w _ hB
  intro i ht
  by_cases hi : i = id
  · rw [hi] at ht ⊢
    simp [phase_credit, setActor]
    exact Or.inl (hn ht)
  · simp [phase_credit, setActor, hi, hst i]

theorem place_actor (I : Impl) (w w1 : World) (id : InstId) (a1 : Actor)
    (hn : terminableName I.desc (tname id) → noBulkSend (contRest a1.phase) = true)
    (hst : ∀ i, w1.st i = w.st i) (hB : BulkFree I w) :
    BulkFree I (setActor w1 id a1) := by
  apply bulk_or I w _ hB
  intro i ht
  by_cases hi : i = id
  · rw [hi] at ht ⊢
    simp [setActor]
    exact Or.inl (hn ht)
  · simp [setActor, hi, hst i]

theorem resume_bulk (I : Impl) (w : World) (sender : InstId) (b : Bool) (dst : InstId)
    (hB : BulkFree I w) :
    BulkFree I (setActor w sender (resumeSender (w.st sender) b dst)) := by
  apply bulk_or I w _ hB
  intro i ht
  by_cases hi : i = sender
  · rw [hi] at ht ⊢
    simp [setActor]
    exact Or.inl (resume_nobulk (w.st sender) b dst (hB sender ht))
  · simp [setActor, hi]

theorem bulk_recv (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : receiveBulk I w id = some w') : BulkFree I w' := by
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
          have hplace := place_bulk I w w1 id a1 (tname id) p.msg.sender
            (deliver_nobulk I hL w id _ p.msg w1 a1 hdel)
            (fun i => deliver_st I w id _ p.msg w1 a1 i hdel) hB
          exact resume_bulk I _ p.sender p.isCall id hplace
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          exact place_bulk I w w1 id a1 (tname id) m.sender
            (deliver_nobulk I hL w id _ m w1 a1 hdel)
            (fun i => deliver_st I w id _ m w1 a1 i hdel) hB
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hph : admitted.phase = a1.phase := by simp [admitted]
          have hplace := place_bulk I w w1 id admitted (tname id) m.sender
            (fun ht => by simpa [hph] using deliver_nobulk I hL w id _ m w1 a1 hdel ht)
            (fun i => deliver_st I w id _ m w1 a1 i hdel) hB
          simpa [admitted] using resume_bulk I _ p.sender p.isCall id hplace

theorem bulk_prio (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId) (hB : BulkFree I w)
    (h : receivePrio I w id = some w') : BulkFree I w' := by
  unfold receivePrio at h
  cases hprio : (w.st id).prio with
  | nil => simp [hprio] at h
  | cons m ms =>
    simp [hprio] at h
    split at h
    · simp at h
    · next w1 a1 hdel =>
      cases h.2
      exact place_actor I w w1 id a1
        (deliver_nobulk I hL w id _ m w1 a1 hdel)
        (fun i => deliver_st I w id _ m w1 a1 i hdel) hB

/-- Failing a waiter either keeps its continuation or drops it. Either way a
terminable program stays free of bulk sends. -/
theorem nobulk_failWaiter (w : World) (dead i s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((failWaiter w dead i).st s).phase) = true := by
  by_cases hs : s = i
  · rw [hs] at h ⊢
    unfold failWaiter
    split
    · exact h
    · cases hph : (w.st i).phase with
      | parked d _ k =>
        have hrest : noBulkSend k.rest = true := by simpa [contRest, hph] using h
        simp [hph]
        split
        · cases hk : k.rest with
          | nil =>
            simp [setActor_self, proceed, hk, contRest]
            exact nobulk_empty
          | cons _ _ => simpa [setActor_self, proceed, hk, contRest] using hrest
        · exact h
      | awaitReply _ _ =>
        simp [hph]
        split
        · simp [setActor_self, contRest]
          exact nobulk_empty
        · simpa [contRest, hph] using h
      | idle => simpa [hph, contRest] using h
      | run k => simpa [hph, contRest] using h
      | awaitEffect k => simpa [hph, contRest] using h
      | awaitPeer k => simpa [hph, contRest] using h
      | crashed => simpa [hph, contRest] using h
  · rw [failWaiter_other w dead i s hs]
    exact h

theorem nobulk_failFold (w : World) (dead s : InstId) (ids : List InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase) = true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih (failWaiter w dead i) (nobulk_failWaiter w dead i s h)

theorem nobulk_killOne (w : World) (D : Description) (id s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((killOne w D id).st s).phase) = true := by
  by_cases hs : s = id
  · rw [hs, (killOne_self w D id).2.1]
    simp [contRest]
    exact nobulk_empty
  · let w1 := readCells D w id
    have hst1 : w1.st s = w.st s := cellsSt D w id s
    have h1 : noBulkSend (contRest (w1.st s).phase) = true := by simpa [hst1] using h
    let w2 := refundMsgs w1 (tname id) (w.st id).box
    have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
    have hph2 : (w2.st s).phase = (w1.st s).phase := by simpa [w2] using h2.1
    have h2n : noBulkSend (contRest (w2.st s).phase) = true := by simpa [hph2] using h1
    let w3 := refundParked w2 (tname id) (w.st id).parked
    have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
    have hph3 : (w3.st s).phase = (w2.st s).phase := by simpa [w3] using h3.1
    have h3n : noBulkSend (contRest (w3.st s).phase) = true := by simpa [hph3] using h2n
    let w4 := failWaiters w3 id
    have h4n : noBulkSend (contRest (w4.st s).phase) = true := by
      simpa [w4, failWaiters] using nobulk_failFold w3 id s w3.roster h3n
    let w5 := forgetSender w4 id
    have h5 := forgetFold_mail w4 id s w4.roster
    have hph5 : (w5.st s).phase = (w4.st s).phase := by simpa [w5, forgetSender] using h5.2.2.1
    have h5n : noBulkSend (contRest (w5.st s).phase) = true := by simpa [hph5] using h4n
    have hbody : killOne w D id =
        setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
      simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
    rw [hbody, setActor_other _ _ _ _ hs]
    exact h5n

theorem nobulk_killFold (w : World) (D : Description) (sub : String) (key : Nat)
    (ids : List InstId) (s : InstId) (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((ids.foldl (fun w id =>
      if isMember D id sub key && (w.st id).life == .alive then killOne w D id else w) w).st s).phase) =
      true := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hcond : (isMember D j sub key && (w.st j).life == .alive) = true
    · simp only [hcond, ite_true]
      exact ih (killOne w D j) (nobulk_killOne w D j s h)
    · simp only [hcond]
      exact ih w h

theorem nobulk_killSubtree (w : World) (D : Description) (sub : String) (key : Nat) (s : InstId)
    (h : noBulkSend (contRest (w.st s).phase) = true) :
    noBulkSend (contRest ((killSubtree w D sub key).st s).phase) = true := by
  simpa [killSubtree, killMembers, plant_st] using nobulk_killFold w D sub key w.roster s h

theorem bulk_apply (I : Impl) (hL : LocalOk I) (a : Action) (w w' : World) (hB : BulkFree I w)
    (h : apply I a w = some w') : BulkFree I w' := by
  cases a with
  | recvBulk id => simpa [apply] using bulk_recv I hL w w' id hB h
  | recvPrio id => simpa [apply] using bulk_prio I hL w w' id hB h
  | exec id => simpa [apply] using bulk_head I w w' id hB h
  | finish id => simpa [apply] using bulk_finish I w w' id hB h
  | spawn template => simpa [apply] using bulk_spawn I w w' template hB h
  | ingress dst label => simpa [apply] using bulk_ingress I w w' dst label hB h
  | kill sub key =>
    rw [kill_apply_world I w w' sub key h]
    intro id ht
    exact nobulk_killSubtree w I.desc sub key id (hB id ht)
  | stutter =>
    cases stutter_unchanged I w w' h
    exact hB

theorem inv2_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : Inv2 I w := by
  induction hR with
  | init => exact inv2_init I hL hG N
  | step w w' a hw happly ih =>
    rcases ih with ⟨hI, hO, hT, hB⟩
    exact ⟨step_inv I hL w w' ⟨a, happly⟩ hI, occ_apply I hL hG a w w' hO hI.1 hI.2.1 hT hB happly,
      ty_step I hL hG N w w' a hw happly hT,     bulk_apply I hL a w w' hB happly⟩

theorem residual_of_edge (D : Description) (e : Edge) (st : String) (he : e ∈ D.edges)
    (hd : discharged D e = false) (hs : st ∈ targetStates D e) :
    (({ template := e.src, state := e.srcState } : Node),
      ({ template := e.dst, state := st } : Node)) ∈ residualEdges D := by
  unfold residualEdges
  let step : List (Node × Node) → Edge → List (Node × Node) := fun acc e =>
    if discharged D e = true then acc
    else acc ++ (targetStates D e).map fun st =>
      (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := st } : Node))
  let pair : Node × Node :=
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := st } : Node))
  have hkeep : ∀ (es : List Edge) (acc : List (Node × Node)), pair ∈ acc → pair ∈ List.foldl step acc es := by
    intro es
    induction es with
    | nil =>
      intro acc hp
      exact hp
    | cons e0 es ih =>
      intro acc hp
      simp only [List.foldl_cons]
      by_cases hdis0 : discharged D e0 = true
      · simp [step, hdis0]
        exact ih _ hp
      · simp [step, hdis0]
        exact ih _ (List.mem_append_left _ hp)
  suffices ∀ (es : List Edge) (acc : List (Node × Node)), e ∈ es → pair ∈ List.foldl step acc es by
    simpa [residualEdges, step, pair] using this D.edges [] he
  intro es acc he
  induction es generalizing acc with
  | nil => cases he
  | cons e0 es ih =>
    simp only [List.foldl_cons]
    cases he with
    | head =>
      simp [step, hd]
      exact hkeep es _ (List.mem_append_right _ (List.mem_map.mpr ⟨st, hs, rfl⟩))
    | tail _ ht =>
      exact ih _ ht

theorem park_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (id dst : InstId) (k : Cont)
    (hs : List (Node × Nat)) (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .parked dst false k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_park I hL hG N w hR id dst false k hph
  obtain ⟨p, hp, _, _⟩ := (inv_reachable I N w hL hR).2.1.bwd id dst false k hph
  have hdis : discharged I.desc e = false := by
    by_cases hd : discharged I.desc e = true
    · have hl1 : l1 I.desc (tname dst) = true := by
        have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
        simp [discharged, hkind, heff, hdstn, hne] at hd
        exact hd.2
      simp [hO.clear dst hl1] at hp
    · cases hbit : discharged I.desc e
      · rfl
      · exact absurd hbit hd
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

theorem park_height (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .parked dst false k) (hlive : (w.st dst).life = .alive) :
    ∃ hs : List (Node × Nat),
      heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
        heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨hs, hok⟩ := hG.ranked
  exact ⟨hs, park_below I hL hG N w hR hO id dst k hs hok hph hlive⟩

theorem reply_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hs : List (Node × Nat))
    (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .awaitReply dst k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_reply I hL hG N w hR id dst k hph
  have hdis : discharged I.desc e = false := by
    have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
    have hcall : (EffectKind.call == EffectKind.send) = false := by decide
    simp [discharged, hkind, heff, hne, hcall]
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

/-- A parked call waits on a live callee of strictly smaller height. -/
theorem call_below (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont) (hs : List (Node × Nat))
    (hok : heightsOkB (residualEdges I.desc) hs = true)
    (hph : (w.st id).phase = .parked dst true k) (hlive : (w.st dst).life = .alive) :
    heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
      heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨_, e, he, hsrc, hss, hdstn, hkind, heff, _, hpart⟩ :=
    projects_park I hL hG N w hR id dst true k hph
  have heff' : e.effect = EffectKind.call := by simpa using heff
  have hdis : discharged I.desc e = false := by
    have hne : (EdgeKind.blocking == EdgeKind.nonBlocking) = false := by decide
    have hcall : (EffectKind.call == EffectKind.send) = false := by decide
    simp [discharged, hkind, heff', hne, hcall]
  have hst : (w.st dst).typestate ∈ targetStates I.desc e := by
    rcases hpart with hd | hmem
    · simp [hdis] at hd
    · exact hmem hlive
  have hmem := residual_of_edge I.desc e (w.st dst).typestate he hdis hst
  have hdrop := heightsOkB_mem (residualEdges I.desc) hs hok
    (({ template := e.src, state := e.srcState } : Node), ({ template := e.dst, state := (w.st dst).typestate } : Node))
    hmem
  simpa [hsrc, hss, hdstn] using hdrop

theorem reply_height (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (id dst : InstId) (k : Cont)
    (hph : (w.st id).phase = .awaitReply dst k) (hlive : (w.st dst).life = .alive) :
    ∃ hs : List (Node × Nat),
      heightOf hs ({ template := tname dst, state := (w.st dst).typestate } : Node) <
        heightOf hs ({ template := tname id, state := (w.st id).typestate } : Node) := by
  obtain ⟨hs, hok⟩ := hG.ranked
  exact ⟨hs, reply_below I hL hG N w hR id dst k hs hok hph hlive⟩

/-- A caller blocked on `callee` for this continuation. -/
def CallWait (ph : Phase) (callee : InstId) (k : Cont) : Prop :=
  ph = .parked callee true k ∨ ph = .awaitReply callee k

theorem proceed_not_callwait (a : Actor) (k : Cont) (callee : InstId) (k' : Cont) :
    ¬ CallWait (proceed a k).phase callee k' := by
  cases hk : k.rest <;> simp [proceed, hk, CallWait]

theorem template_subtree_of (D : Description) (name : String) (t : Template)
    (ht : templateOf D name = some t) : templateSubtree D name = t.subtree := by
  simp [templateSubtree, ht]

/-- A nonempty subtree member is terminable. `subtreeFails` is what the checker records. -/
theorem subtree_member_terminable (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hne : t.subtree ≠ "") : t.terminable = true := by
  have hmap := hG.subtrees
  simp [subtreeFails] at hmap
  have hf := hmap t (template_mem D name t ht)
  simp [hne] at hf
  cases hmul : t.multiplicity with
  | perPeer =>
    rw [hmul] at hf
    have hper : (Multiplicity.perPeer != Multiplicity.perPeer) = false := by decide
    rw [hper] at hf
    cases htm : t.terminable with
    | true => rfl
    | false => simp [htm] at hf
  | one =>
    rw [hmul] at hf
    have hper : (Multiplicity.one != Multiplicity.perPeer) = true := by decide
    rw [hper] at hf
    simp at hf

theorem same_src_terminable (D : Description) (hG : GraphOk D) (a b : String) (t : Template)
    (hsame : sameSubtree D a b = true) (ht : templateOf D a = some t) : t.terminable = true := by
  have hsub : templateSubtree D a ≠ "" := by
    simp [sameSubtree, Bool.and_eq_true] at hsame
    intro hempty
    simp [hempty] at hsame
  rw [template_subtree_of D a t ht] at hsub
  exact subtree_member_terminable D hG a t ht hsub

end Deadlock
