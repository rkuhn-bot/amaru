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

end Deadlock
