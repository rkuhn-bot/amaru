import Deadlock.Occ

set_option autoImplicit false

namespace Deadlock

/-- A terminable actor's continuation does not bulk-send. This is narrower than
Amaru: a per-peer stage can terminate and still have sent to a shared stage. -/
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

theorem bulk_finish (I : Impl) (w w' : World) (id : InstId) (hB : BulkFree I w) (hS : SemInv I w)
    (h : finishWait w id = some w') : BulkFree I w' := by
  apply bulk_or I w w' hB
  intro i ht
  unfold finishWait at h
  split at h
  · next k heq =>
    cases h
    by_cases hi : i = id
    · rw [hi] at ht ⊢
      have hrest : noBulkSend k.rest = true := by simpa [contRest, heq] using hB id ht
      cases hk : k.rest with
      | nil => simp [setActor, proceed, hk, contRest, nobulk_empty]
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  · next k heq =>
    cases h
    by_cases hi : i = id
    · rw [hi] at ht ⊢
      have hrest : noBulkSend k.rest = true := by simpa [contRest, heq] using hB id ht
      cases hk : k.rest with
      | nil => simp [setActor, proceed, hk, contRest, nobulk_empty]
      | cons _ _ =>
        simp [setActor, proceed, hk, contRest]
        exact Or.inl (by simpa [hk] using hrest)
    · simp [setActor, hi]
  · cases h

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

end Deadlock
