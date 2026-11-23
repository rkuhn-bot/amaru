import Deadlock.Semantics

set_option autoImplicit false

namespace Deadlock.TimeoutGap

/-!
A parked call's `tokenHold` subtracts the call's own slot from the
`NotAdmitted` reserve. Finishing that call as `NotAdmitted` spends the full
reserve. The two are not ordered, so a timeout preserves `tokenHold ≤ tokens`
only when the refund puts the slot back.
-/

def gapDesc : Description :=
  { name := "gap", freshNames := false, templates := [callerT], edges := [idleE, busyE],
    compatibility := .all, steps := [], cellEffects := [] }
where
  callerT : Template :=
    { name := "caller", multiplicity := .one, capacity := Affine.ofNat 1,
      priorityCapacity := Affine.ofNat 1, priorityBound := Affine.ofNat 1,
      states := ["idle", "busy"], initial := "idle", terminable := false,
      untimedPeer := false, mustFit := true }
  idleE : Edge :=
    { src := "caller", srcState := "idle", dst := "box", kind := .blocking,
      reliability := .reliable, effect := .send, label := "m", scope := .intra,
      occupancy := Affine.ofNat 2, repliesInDequeue := false, ingress := false,
      ingressLegal := none, cell := Inhabited.default }
  busyE : Edge :=
    { src := "caller", srcState := "busy", dst := "box", kind := .blocking,
      reliability := .reliable, effect := .send, label := "m", scope := .intra,
      occupancy := Affine.ofNat 0, repliesInDequeue := false, ingress := false,
      ingressLegal := none, cell := Inhabited.default }

def gapK : Cont :=
  { toState := "idle", replyTo := none, rest := [], onNotAdmitted := [],
    toNotAdmitted := "busy" }

def gapA : Actor :=
  { life := .alive, typestate := "idle", phase := .parked (.core "box") true gapK,
    box := [], prio := [], parked := [], tokens := fun _ => 1 }

theorem gap_old : tokenHold gapDesc "caller" "box" gapA = 1 := by
  decide

theorem gap_new :
    tokenHold gapDesc "caller" "box" (finishCall gapA gapK .notAdmitted) = 2 := by
  decide

theorem gap_grows :
    ¬ tokenHold gapDesc "caller" "box" (finishCall gapA gapK .notAdmitted) ≤
      tokenHold gapDesc "caller" "box" gapA := by
  decide

end Deadlock.TimeoutGap
