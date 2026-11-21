import Deadlock.Projects
import Deadlock.Safety

set_option autoImplicit false

namespace Deadlock

/-! Outstanding credit is one budget per live slot.
The live generation's `tokens dst`, as an `Int`, plus mail queued from every
generation of that slot, equals the template budget. Dead generations keep
whatever tokens they had; those tokens are not added in. A pool mailbox is
open: it is addressed by slot, not by the sender's subtree key. A crashed
world is exempt from the queue and parking obligations `crashWorld` leaves
behind. While an actor is alive, `tokenHold` — the worst remaining
`sends + floor(landing)`, including an outcome arm — fits in its tokens, so
picking that arm does not spend a slot the account did not reserve. -/

def terminableName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.terminable = true

theorem effSends_ge_tail (dst : String) (e : Eff) (tailN : Nat) : tailN ≤ effSends dst e tailN := by
  cases e <;> simp [effSends] <;> omega

theorem sends_drop_le (dst : String) (e : Eff) (es : List Eff) : sendsTo dst es ≤ sendsTo dst (e :: es) := by
  simp only [sendsTo]
  exact effSends_ge_tail dst e (sendsTo dst es)

/-- A plain `send` adds its own message on top of the tail. A `trySend` or
`call` takes the max of that and a replacing branch, so the same equality does
not hold for those effects. -/
theorem sends_drop_bulk (dst d : String) (es : List Eff) (label : String) (n : Nat) :
    sendsTo dst (.send d label n :: es) = (if d == dst then 1 else 0) + sendsTo dst es := by
  simp [sendsTo, effSends]

theorem sends_drop_other (dst : String) (e : Eff) (es : List Eff)
    (hsend : ∀ d label n, e ≠ .send d label n)
    (htry : ∀ d label n onFull onGone, e ≠ .trySend d label n onFull onGone)
    (hcall : ∀ d label n onNotAdmitted onTimedOut, e ≠ .call d label n onNotAdmitted onTimedOut)
    (hpeer : ∀ onTimeout, e ≠ .peer onTimeout) :
    sendsTo dst (e :: es) = sendsTo dst es := by
  cases e with
  | send d label n => exact absurd rfl (hsend d label n)
  | trySend d label n onFull onGone => exact absurd rfl (htry d label n onFull onGone)
  | call d label n onNotAdmitted onTimedOut =>
    exact absurd rfl (hcall d label n onNotAdmitted onTimedOut)
  | peer onTimeout => exact absurd rfl (hpeer onTimeout)
  | _ => simp [sendsTo, effSends]

theorem noBulk_tail (e : Eff) (es : List Eff) (h : noBulkSend (e :: es) = true) : noBulkSend es = true := by
  simp [noBulkSend, Bool.and_eq_true] at h
  exact h.2

theorem scope_empty (D : Description) (name : String) : bulkScopeOf D name [] = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht]
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : (t.multiplicity == .one) with
        | false => rfl
        | true => exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp only [hnot, hterm, Bool.or_false, Bool.not_true, Bool.false_or]
        by_cases hsub : (t.subtree == "") = true
        · simp [hsub, noBulkSend]
        · have hsub' : (t.subtree == "") = false := by
            cases hb : (t.subtree == "") with
            | false => rfl
            | true => exact absurd hb hsub
          simp [hsub', memberProgramOk]
      · have hterm' : t.terminable = false := by
          cases hb : t.terminable with
          | false => rfl
          | true => exact absurd hb hterm
        simp [hnot, hterm', Bool.not_false, Bool.or_true]

theorem scope_tail (D : Description) (name : String) (e : Eff) (es : List Eff)
    (h : bulkScopeOf D name (e :: es) = true) : bulkScopeOf D name es = true := by
  cases ht : templateOf D name with
  | none => simp [bulkScopeOf, ht]
  | some t =>
    simp only [bulkScopeOf, ht] at h ⊢
    by_cases hone : (t.multiplicity == .one) = true
    · simp [hone]
    · have hnot : (t.multiplicity == .one) = false := by
        cases hb : (t.multiplicity == .one) with
        | false => rfl
        | true => exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp only [hnot, hterm, Bool.or_false, Bool.not_true, Bool.false_or] at h ⊢
        by_cases hsub : (t.subtree == "") = true
        · simp only [hsub, ite_true] at h ⊢
          exact noBulk_tail e es h
        · have hsub' : (t.subtree == "") = false := by
            cases hb : (t.subtree == "") with
            | false => rfl
            | true => exact absurd hb hsub
          simp only [hsub', ite_false] at h ⊢
          exact memberProgram_tail D name e es h
      · have hterm' : t.terminable = false := by
          cases hb : t.terminable with
          | false => rfl
          | true => exact absurd hb hterm
        simp [hnot, hterm']

/-- A continuation that is in scope stays in scope after its head is consumed.
An empty tail is the idle continuation. -/
theorem scope_of_tail (D : Description) (name : String) (es : List Eff)
    (h : bulkScopeOf D name es = true) : bulkScopeOf D name es = true := h

/-- Key of a per-peer actor. The generation is not part of the key. A core has none. -/
def peerKey : InstId → Option Nat
  | .core _ => none
  | .peer _ k _ => some k

/-- A core, or a pool (`slots ≠ 0`). Pool mail is addressed by the slot in the
send, not by the sender's subtree key, so the mailbox is not keyed to the sender. -/
def openHost (D : Description) (host : InstId) : Prop :=
  match templateOf D (tname host) with
  | none => peerKey host = none
  | some t => peerKey host = none ∨ t.slots ≠ 0

/-- `sender` may sit in `host`'s mailbox. An open host accepts any sender.
A keyed per-peer host accepts only the sender of the same key. -/
def keyAgrees (D : Description) (sender host : InstId) : Prop :=
  openHost D host ∨ peerKey sender = peerKey host

/-- Placement of one queued message. Life is not part of it: a dead pool child's
box mail stays on a core after the seal, and a crashed world is not a step. -/
def queueOk (D : Description) (_w : World) (sender host : InstId) : Prop :=
  keyAgrees D sender host

/-- A roster id has the shape of its template. A multiplicity-one role is the
core. A per-peer role is some generation at its key. -/
def shapeOk (D : Description) (id : InstId) : Prop :=
  ∃ t, templateOf D (tname id) = some t ∧
    match t.multiplicity with
    | .one => id = InstId.core t.name
    | .perPeer => ∃ k g, id = InstId.peer t.name k g

/-- At most one alive generation of each slot. `findLive` is then the holder
of that slot's budget. -/
def oneLiveGen (w : World) : Prop :=
  ∀ name key g1 g2,
    InstId.peer name key g1 ∈ w.roster → InstId.peer name key g2 ∈ w.roster →
      (w.st (InstId.peer name key g1)).life = .alive →
        (w.st (InstId.peer name key g2)).life = .alive → g1 = g2

/-- Live-slot budget. Peer mail from every generation of the key is
`queuedFromKey`; only the live generation's tokens are added. A core is its
own slot and is not respawned, so its own `owed` is the queued mail. With no
live generation the key's mail is still at most the budget: the last live
holder had nonnegative tokens, and dying does not enqueue. -/
def slotBalance (I : Impl) (w : World) : Prop :=
  ((∀ name key id d, findLive w name key = some id →
      (w.st id).tokens d + (queuedFromKey w name key d : Int) = (budget I.desc name d : Int)) ∧
    (∀ name d, (w.st (.core name)).life = .alive → .core name ∈ w.roster →
      (w.st (.core name)).tokens d + (owed w.st d (.core name) w.roster : Int) =
        (budget I.desc name d : Int))) ∧
    (∀ name key d, findLive w name key = none →
      (queuedFromKey w name key d : Int) ≤ (budget I.desc name d : Int))

/-- Outstanding credit, queues, and the Lemma-1 promise that nothing is parked.
`clear`, `deadEmpty`, and `quiet` are not claimed of a crashed world: the crash
kills the roster and leaves the mail queued. -/
structure OccInv (I : Impl) (w : World) : Prop where
  nodup : w.roster.Nodup
  aliveIn : ∀ id, (w.st id).life = .alive → id ∈ w.roster
  indexed : oneLiveGen w
  liveOne : ∀ t, (∃ tmpl, templateOf I.desc t = some tmpl ∧ tmpl.multiplicity = .one) →
    aliveCount w t ≤ 1
  livePeer : ∀ t, (∃ tmpl, templateOf I.desc t = some tmpl ∧ tmpl.multiplicity = .perPeer) →
    aliveCount w t ≤ w.N
  offEmpty : ∀ id, id ∉ w.roster → (w.st id).box = [] ∧ (w.st id).parked = []
  sentFrom : ∀ id m, m ∈ (w.st id).box → m.sender ∈ w.roster
  parkFrom : ∀ id p, p ∈ (w.st id).parked → p.sender ∈ w.roster
  parkMsg : ∀ id p, p ∈ (w.st id).parked → p.sender = p.msg.sender
  balance : slotBalance I w
  slack : ∀ id d, (w.st id).life = .alive →
    (tokenHold I.desc (tname id) d (w.st id) : Int) ≤ (w.st id).tokens d
  /-- A lone terminable never sends, so it owes nothing. A subtree member may owe
  a sibling: that mail dies with the subtree. -/
  still : ∀ s d, s ∈ w.roster → loneTerminableName I.desc (tname s) → owed w.st d s w.roster = 0
  /-- A non-alive id, while the world has not crashed, owes at most its budget.
  Tokens left on that id are not part of the bound. -/
  quiet : w.crashed = false →
    ∀ s d, s ∈ w.roster → (w.st s).life ≠ .alive →
      (owed w.st d s w.roster : Int) ≤ (budget I.desc (tname s) d : Int)
  clear : w.crashed = false → ∀ id, l1 I.desc (tname id) = true → (w.st id).parked = []
  /-- An absent or dead actor keeps no queue, unless the world has crashed.
  The seal clears the mailbox in the step that kills the actor. -/
  deadEmpty : w.crashed = false →
    ∀ id, (w.st id).life = .absent ∨ (w.st id).life = .dead →
      (w.st id).box = [] ∧ (w.st id).parked = []
  /-- Keyed per-peer mail stays on the sender's own key. An open host — a core
  or a pool — accepts mail addressed to that host, whatever key sent it. -/
  sameKey : ∀ host,
    (∀ m ∈ (w.st host).box, queueOk I.desc w m.sender host) ∧
    (∀ p ∈ (w.st host).parked, queueOk I.desc w p.sender host)
  /-- Every roster id is the core or the peer its template declares. -/
  shaped : ∀ id, id ∈ w.roster → shapeOk I.desc id
  /-- Mail in a core comes from a core, or from a role that does not terminate.
  A terminating per-peer keeps its mail on its own key, so killing it does not
  leave that mail in a core. -/
  coreFrom : ∀ host, peerKey host = none →
    (∀ m ∈ (w.st host).box,
      peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false) ∧
    (∀ p ∈ (w.st host).parked,
      peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false)

theorem owed_le_debt (budget owed tokens floor pending debt : Nat)
    (hB : owed + tokens = budget) (hS : floor + pending ≤ tokens) (hF : floor + debt = budget) :
    owed + pending ≤ debt := by
  omega

theorem floor_add_debt (D : Description) (template state dst : String)
    (h : ∃ t, templateOf D template = some t ∧ state ∈ t.states) :
    floorState D template state dst + debt D template state dst = budget D template dst := by
  exact Nat.sub_add_cancel (debt_le_budget D template state dst h)

def sumFold (f : InstId → Nat) : List InstId → Nat
  | [] => 0
  | id :: ids => f id + sumFold f ids

theorem sum_add (f g : InstId → Nat) (ids : List InstId) :
    sumFold (fun id => f id + g id) ids = sumFold f ids + sumFold g ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [sumFold, ih]
    omega

theorem sum_congr (f g : InstId → Nat) (ids : List InstId) (h : ∀ id ∈ ids, f id = g id) :
    sumFold f ids = sumFold g ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [sumFold, h id (List.Mem.head _), ih (fun i hi => h i (List.Mem.tail _ hi))]

theorem sum_le (f g : InstId → Nat) (ids : List InstId) (h : ∀ id ∈ ids, f id ≤ g id) :
    sumFold f ids ≤ sumFold g ids := by
  induction ids with
  | nil => simp [sumFold]
  | cons id ids ih =>
    simp only [sumFold]
    exact Nat.add_le_add (h id (List.Mem.head _)) (ih fun i hi => h i (List.Mem.tail _ hi))

theorem sum_hit (s : InstId) (ids : List InstId) (nodup : ids.Nodup) :
    sumFold (fun id => if s = id then 1 else 0) ids = if s ∈ ids then 1 else 0 := by
  induction ids with
  | nil => simp [sumFold]
  | cons id ids ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [sumFold, List.mem_cons]
    by_cases hs : s = id
    · simp only [hs, ite_true]
      have ih' := ih hcons.2
      have hnin : id ∉ ids := hcons.1
      simp only [hs, hnin, ite_false] at ih'
      rw [ih']
      simp
    · simp only [hs, ite_false]
      rw [ih hcons.2]
      simp [hs]

theorem count_step (s : InstId) (m : Msg) (ms : List Msg) :
    countFrom s (m :: ms) = (if m.sender = s then 1 else 0) + countFrom s ms := by
  simp [countFrom]

theorem sum_count_cons (m : Msg) (ms : List Msg) (ids : List InstId) (nodup : ids.Nodup) :
    sumFold (fun id => countFrom id (m :: ms)) ids =
      (if m.sender ∈ ids then 1 else 0) + sumFold (fun id => countFrom id ms) ids := by
  have hsplit : sumFold (fun id => countFrom id (m :: ms)) ids =
      sumFold (fun id => (if m.sender = id then 1 else 0) + countFrom id ms) ids := by
    refine sum_congr _ _ ids ?_
    intro id _
    exact count_step id m ms
  rw [hsplit, sum_add, sum_hit m.sender ids nodup]

theorem sum_zero (ids : List InstId) : sumFold (fun _ => 0) ids = 0 := by
  induction ids with
  | nil => rfl
  | cons _ ids ih => simp [sumFold, ih]

theorem count_total (ms : List Msg) (ids : List InstId) (nodup : ids.Nodup)
    (h : ∀ m ∈ ms, m.sender ∈ ids) : sumFold (fun s => countFrom s ms) ids = ms.length := by
  induction ms with
  | nil =>
    have hz : sumFold (fun s => countFrom s ([] : List Msg)) ids = sumFold (fun _ => 0) ids := by
      refine sum_congr _ _ ids ?_
      intro _ _
      simp [countFrom]
    rw [hz, sum_zero]
    rfl
  | cons m ms ih =>
    rw [List.length_cons, sum_count_cons m ms ids nodup, ih (fun x hx => h x (List.Mem.tail _ hx))]
    have hm := h m (List.Mem.head _)
    simp [hm]
    omega

theorem park_step (s : InstId) (p : Parked) (ps : List Parked) :
    countParked s (p :: ps) = (if p.sender = s then 1 else 0) + countParked s ps := by
  simp [countParked]

theorem sum_park_cons (p : Parked) (ps : List Parked) (ids : List InstId) (nodup : ids.Nodup) :
    sumFold (fun id => countParked id (p :: ps)) ids =
      (if p.sender ∈ ids then 1 else 0) + sumFold (fun id => countParked id ps) ids := by
  have hsplit : sumFold (fun id => countParked id (p :: ps)) ids =
      sumFold (fun id => (if p.sender = id then 1 else 0) + countParked id ps) ids := by
    refine sum_congr _ _ ids ?_
    intro id _
    exact park_step id p ps
  rw [hsplit, sum_add, sum_hit p.sender ids nodup]

theorem park_total (ps : List Parked) (ids : List InstId) (nodup : ids.Nodup)
    (h : ∀ p ∈ ps, p.sender ∈ ids) : sumFold (fun s => countParked s ps) ids = ps.length := by
  induction ps with
  | nil =>
    have hz : sumFold (fun s => countParked s ([] : List Parked)) ids = sumFold (fun _ => 0) ids := by
      refine sum_congr _ _ ids ?_
      intro _ _
      simp [countParked]
    rw [hz, sum_zero]
    rfl
  | cons p ps ih =>
    rw [List.length_cons, sum_park_cons p ps ids nodup, ih (fun x hx => h x (List.Mem.tail _ hx))]
    have hm := h p (List.Mem.head _)
    simp [hm]
    omega

def sumOwed (st : InstId → Actor) (dst : String) (roster : List InstId) : Nat :=
  sumFold (fun s => owed st dst s roster) roster

def liveDebt (D : Description) (st : InstId → Actor) (dst : String) : List InstId → Nat
  | [] => 0
  | id :: ids =>
    (if (st id).life = .alive then debt D (tname id) (st id).typestate dst else 0) + liveDebt D st dst ids

theorem liveDebt_sum (D : Description) (st : InstId → Actor) (dst : String) (ids : List InstId) :
    liveDebt D st dst ids =
      sumFold (fun id => if (st id).life = .alive then debt D (tname id) (st id).typestate dst else 0) ids := by
  induction ids with
  | nil => rfl
  | cons _ _ ih => simp [liveDebt, sumFold, ih]

/-- `pathReserve` keeps the floor of `at_.here`: every branch is a max, and the
main branch is `sends +` the tail, which ends at that floor. -/
theorem pathReserve_ge_here (D : Description) (template dst : String) (at_ : BranchAt) :
    ∀ es, landFloor D template at_.here dst ≤ pathReserve D template dst at_ es := by
  intro es
  induction es with
  | nil => simp [pathReserve]
  | cons e es ih =>
    cases e with
    | send _ _ _ =>
      simp only [pathReserve, effReserve]
      exact Nat.le_trans ih (Nat.le_add_left _ _)
    | trySend _ _ _ _ _ =>
      simp only [pathReserve, effReserve]
      exact Nat.le_trans (Nat.le_trans ih (Nat.le_add_left _ _)) (Nat.le_max_left _ _)
    | call _ _ _ _ _ =>
      simp only [pathReserve, effReserve]
      exact Nat.le_trans (Nat.le_trans ih (Nat.le_add_left _ _)) (Nat.le_max_left _ _)
    | peer _ =>
      simp only [pathReserve, effReserve]
      exact Nat.le_trans ih (Nat.le_max_left _ _)
    | reply =>
      simp only [pathReserve, effReserve]
      exact ih
    | selfSchedule _ =>
      simp only [pathReserve, effReserve]
      exact ih
    | cell _ _ _ =>
      simp only [pathReserve, effReserve]
      exact ih
    | internal =>
      simp only [pathReserve, effReserve]
      exact ih
    | abort =>
      simp only [pathReserve, effReserve]
      exact ih
    | terminate =>
      simp only [pathReserve, effReserve]
      exact ih
    | spawn _ =>
      simp only [pathReserve, effReserve]
      exact ih

/-- While the continuation says `typestate = k.toState`, the hold is at least
the floor of that typestate. Idle and crashed hold exactly that floor. -/
theorem tokenHold_ge_floor (D : Description) (template dst : String) (a : Actor)
    (hc : contTy a) :
    landFloor D template a.typestate dst ≤ tokenHold D template dst a := by
  cases hp : a.phase with
  | idle => simp [tokenHold, hp]
  | crashed => simp [tokenHold, hp]
  | run k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hp] using hc
    simpa [tokenHold, hp, hty, contAt] using pathReserve_ge_here D template dst (contAt k) k.rest
  | awaitEffect k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hp] using hc
    simpa [tokenHold, hp, hty, contAt] using pathReserve_ge_here D template dst (contAt k) k.rest
  | awaitReply _ k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hp] using hc
    have hmain := pathReserve_ge_here D template dst (contAt k) k.rest
    simpa [tokenHold, hp, hty, contAt] using Nat.le_trans hmain (Nat.le_max_left _ _)
  | awaitPeer k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hp] using hc
    have hmain := pathReserve_ge_here D template dst (contAt k) k.rest
    simpa [tokenHold, hp, hty, contAt] using Nat.le_trans hmain (Nat.le_max_left _ _)
  | parked _ isCall k =>
    have hty : a.typestate = k.toState := by simpa [contTy, hp] using hc
    have hmain := pathReserve_ge_here D template dst (contAt k) k.rest
    cases isCall with
    | false =>
      simpa [tokenHold, hp, hty, contAt] using hmain
    | true =>
      simpa [tokenHold, hp, hty, contAt] using Nat.le_trans hmain (Nat.le_max_left _ _)

theorem tokens_ge_floor (I : Impl) (w : World) (h : OccInv I w) (s : InstId) (d : String)
    (hl : (w.st s).life = .alive) (hc : contTy (w.st s)) :
    (floorState I.desc (tname s) (w.st s).typestate d : Int) ≤ (w.st s).tokens d := by
  have hhold := tokenHold_ge_floor I.desc (tname s) d (w.st s) hc
  have hS := h.slack s d hl
  refine Int.le_trans ?_ hS
  simpa [landFloor, floorState] using Int.ofNat_le.mpr hhold

theorem queued_le_debt (budget queued floor debt : Nat) (tokens : Int)
    (hsum : tokens + (queued : Int) = (budget : Int))
    (hfloor : (floor : Int) ≤ tokens)
    (hF : floor + debt = budget) : queued ≤ debt := by
  have hnat : budget - floor = debt := by
    have hcancel := Nat.add_sub_cancel_left floor debt
    rwa [hF] at hcancel
  have hleF : floor ≤ budget := by
    have h := Nat.le_add_right floor debt
    rwa [hF] at h
  have hsub : (budget : Int) - (floor : Int) = (debt : Int) := by
    rw [← hnat]
    exact (Int.ofNat_sub hleF).symm
  have hq : (queued : Int) ≤ (budget : Int) - (floor : Int) := by omega
  rw [hsub] at hq
  exact Int.ofNat_le.mp hq

theorem find?_holds {α : Type} (p : α → Bool) (l : List α) (a : α)
    (hmem : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b ∧ p b = true := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.find?_cons]
    by_cases hx : p x = true
    · refine ⟨x, ?_, hx⟩
      simp [hx]
    · have hxf : p x = false := by
        cases hb : p x with
        | true => exact absurd hb hx
        | false => rfl
      simp [hxf]
      cases List.mem_cons.mp hmem with
      | inl heq =>
        subst heq
        simp [hp] at hxf
      | inr ht =>
        exact ih ht

theorem findLive_of_alive (w : World) (h1 : oneLiveGen w) (name : String) (key gen : Nat)
    (hmem : InstId.peer name key gen ∈ w.roster)
    (hl : (w.st (InstId.peer name key gen)).life = .alive) :
    findLive w name key = some (InstId.peer name key gen) := by
  let id := InstId.peer name key gen
  let pred : InstId → Bool := fun i =>
    match i with
    | .peer n k _ => n == name && k == key && (w.st i).life == .alive
    | .core _ => false
  have hp : pred id = true := by
    unfold pred
    simp [id, hl, beq_iff_eq]
  obtain ⟨b, hb, hpb⟩ := find?_holds pred w.roster id hmem hp
  have hbm : b ∈ w.roster := List.mem_of_find?_eq_some hb
  cases b with
  | core _ =>
    unfold pred at hpb
    simp at hpb
  | peer n k g =>
    unfold pred at hpb
    simp only [Bool.and_eq_true, beq_iff_eq] at hpb
    obtain ⟨⟨hn, hk⟩, hlive⟩ := hpb
    have hg : g = gen :=
      h1 name key g gen (by simpa [← hn, ← hk] using hbm) hmem
        (by simpa [hn, hk, beq_iff_eq] using hlive) hl
    have hb' : w.roster.find? pred = some id := by
      simpa [id, hn, hk, hg] using hb
    unfold findLive
    change w.roster.find? pred = some id
    exact hb'

def keyPred (name : String) (key : Nat) (m : Msg) : Bool :=
  match m.sender with
  | .peer s k _ => s == name && k == key
  | .core _ => false

theorem countFrom_key_le (name : String) (key gen : Nat) :
    ∀ ms, countFrom (InstId.peer name key gen) ms ≤ (ms.filter (keyPred name key)).length := by
  intro ms
  induction ms with
  | nil => simp [countFrom, keyPred]
  | cons m ms ih =>
    by_cases hs : m.sender = InstId.peer name key gen
    · have hf : keyPred name key m = true := by simp [keyPred, hs]
      simp [countFrom, List.filter, hs, hf, ih]
      omega
    · simp [countFrom, hs]
      cases hb : keyPred name key m with
      | true =>
        simp [List.filter, hb, ih]
        omega
      | false =>
        simp [List.filter, hb, ih]

theorem countParked_key_le (name : String) (key gen : Nat) (ps : List Parked)
    (hp : ∀ p ∈ ps, p.sender = p.msg.sender) :
    countParked (InstId.peer name key gen) ps ≤
      (ps.filter fun p => keyPred name key p.msg).length := by
  induction ps with
  | nil => simp [countParked]
  | cons p ps ih =>
    have hhead := hp p (List.Mem.head _)
    have htail := ih fun q hq => hp q (List.Mem.tail _ hq)
    by_cases hs : p.sender = InstId.peer name key gen
    · have hf : keyPred name key p.msg = true := by
        simp [keyPred, hs, ← hhead]
      simp [countParked, List.filter, hs, hf, htail]
      omega
    · simp [countParked, hs]
      cases hb : keyPred name key p.msg with
      | true =>
        simp [List.filter, hb, htail]
        omega
      | false =>
        simp [List.filter, hb, htail]

theorem slot_le_key (st : InstId → Actor) (name : String) (key gen : Nat) (dst : String)
    (host : InstId) (hp : ∀ p ∈ (st host).parked, p.sender = p.msg.sender) :
    slot st dst (InstId.peer name key gen) host ≤
      (if tname host != dst then 0
        else ((st host).box.filter (keyPred name key)).length +
          ((st host).parked.filter fun p => keyPred name key p.msg).length) := by
  by_cases ht : (tname host == dst) = true
  · have hne : (tname host != dst) = false := by simp [bne, ht]
    simp only [slot, ht, hne, ite_true, ite_false]
    exact Nat.add_le_add (countFrom_key_le name key gen _) (countParked_key_le name key gen _ hp)
  · have hf : (tname host == dst) = false := by
      cases hbb : tname host == dst with
      | false => rfl
      | true => exact absurd hbb ht
    have hne : (tname host != dst) = true := by simp [bne, hf]
    simp [slot, hf, hne]

theorem owed_peer_le_queued (w : World) (name : String) (key gen : Nat) (dst : String)
    (hp : ∀ host, ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender) :
    owed w.st dst (InstId.peer name key gen) w.roster ≤ queuedFromKey w name key dst := by
  let step : InstId → Nat := fun host =>
    if tname host != dst then 0
    else ((w.st host).box.filter (keyPred name key)).length +
      ((w.st host).parked.filter fun p => keyPred name key p.msg).length
  have hpt : ∀ host, host ∈ w.roster → slot w.st dst (InstId.peer name key gen) host ≤ step host :=
    fun host _ => slot_le_key w.st name key gen dst host (hp host)
  have hsum := sum_le _ _ w.roster hpt
  have howed : owed w.st dst (InstId.peer name key gen) w.roster =
      sumFold (fun host => slot w.st dst (InstId.peer name key gen) host) w.roster := by
    induction w.roster with
    | nil => rfl
    | cons host hosts ih => simp [owed, sumFold, ih]
  rw [howed]
  refine Nat.le_trans hsum ?_
  unfold queuedFromKey
  dsimp only
  suffices ∀ ids n,
      ids.foldl (fun n host =>
        if tname host != dst then n
        else n + ((w.st host).box.filter (keyPred name key)).length +
          ((w.st host).parked.filter fun p => keyPred name key p.msg).length) n =
        n + sumFold step ids by
    have heq := this w.roster 0
    change sumFold step w.roster ≤
      w.roster.foldl (fun n host =>
        if tname host != dst then n
        else n + ((w.st host).box.filter (keyPred name key)).length +
          ((w.st host).parked.filter fun p => keyPred name key p.msg).length) 0
    have : sumFold step w.roster =
        w.roster.foldl (fun n host =>
          if tname host != dst then n
          else n + ((w.st host).box.filter (keyPred name key)).length +
            ((w.st host).parked.filter fun p => keyPred name key p.msg).length) 0 := by
      have h0 : sumFold step w.roster = 0 + sumFold step w.roster := by omega
      exact h0.trans heq.symm
    exact Nat.le_of_eq this
  intro ids
  induction ids with
  | nil =>
    intro n
    simp [sumFold]
  | cons host ids ih =>
    intro n
    simp only [List.foldl_cons, sumFold]
    rw [ih]
    by_cases ht : (tname host == dst) = true
    · have hne : (tname host != dst) = false := by simp [bne, ht]
      simp only [step, hne, Bool.false_eq_true, ite_false, ht]
      omega
    · have hf : (tname host == dst) = false := by
        cases hbb : tname host == dst with
        | false => rfl
        | true => exact absurd hbb ht
      have hne : (tname host != dst) = true := by simp [bne, hf]
      simp only [step, hne, ite_true]
      omega

/-- An alive actor owes at most the debt of its current typestate: `contTy`
puts the floor of that typestate under `tokenHold`, slack puts that under the
tokens, and the slot equation turns the rest into queued mail. A non-alive
actor, while the world has not crashed, owes at most its budget. -/
theorem owed_one_le (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String)
    (s : InstId) (hs : s ∈ w.roster) (hC : contTy (w.st s)) (hcrash : w.crashed = false) :
    owed w.st dst s w.roster ≤
      if (w.st s).life = .alive then debt I.desc (tname s) (w.st s).typestate dst
      else budget I.desc (tname s) dst := by
  by_cases hl : (w.st s).life = .alive
  · simp [hl]
    cases ht : templateOf I.desc (tname s) with
    | none =>
      have hele := hT s hl
      simp [statesOf, ht, List.elem] at hele
    | some t =>
      have hele := hT s hl
      have hst : (w.st s).typestate ∈ t.states := by
        simpa [statesOf, ht, List.elem_iff] using hele
      have hF := floor_add_debt I.desc (tname s) (w.st s).typestate dst ⟨t, ht, hst⟩
      have hfloor := tokens_ge_floor I w h s dst hl hC
      cases s with
      | core name =>
        have hname : tname (InstId.core name) = name := rfl
        have hbal := h.balance.1.2 name dst (by simpa [hname] using hl) hs
        have hsum : (w.st (InstId.core name)).tokens dst +
            (owed w.st dst (InstId.core name) w.roster : Int) =
            (budget I.desc name dst : Int) := hbal
        have htok : (floorState I.desc name ((w.st (InstId.core name)).typestate) dst : Int) ≤
            (w.st (InstId.core name)).tokens dst := by simpa [hname] using hfloor
        have hdeb : floorState I.desc name ((w.st (InstId.core name)).typestate) dst +
            debt I.desc name ((w.st (InstId.core name)).typestate) dst =
            budget I.desc name dst := by simpa [hname] using hF
        exact queued_le_debt _ _ _ _ _ hsum htok hdeb
      | peer name key gen =>
        have hlive := findLive_of_alive w h.indexed name key gen hs hl
        have hbal := h.balance.1.1 name key (InstId.peer name key gen) dst hlive
        have howed := owed_peer_le_queued w name key gen dst fun host p hp => h.parkMsg host p hp
        have hsum := hbal
        have htok : (floorState I.desc name ((w.st (InstId.peer name key gen)).typestate) dst : Int) ≤
            (w.st (InstId.peer name key gen)).tokens dst := by simpa [tname] using hfloor
        have hdeb : floorState I.desc name ((w.st (InstId.peer name key gen)).typestate) dst +
            debt I.desc name ((w.st (InstId.peer name key gen)).typestate) dst =
            budget I.desc name dst := by simpa [tname] using hF
        have hq : queuedFromKey w name key dst ≤
            debt I.desc name ((w.st (InstId.peer name key gen)).typestate) dst :=
          queued_le_debt _ _ _ _ _ hsum htok hdeb
        exact Nat.le_trans howed hq
  · simp [hl]
    exact Int.ofNat_le.mp (h.quiet hcrash s dst hs hl)

theorem sumOwed_le_charge (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String)
    (hC : ∀ s, contTy (w.st s)) (hcrash : w.crashed = false) :
    sumOwed w.st dst w.roster ≤
      sumFold (fun s =>
        if (w.st s).life = .alive then debt I.desc (tname s) (w.st s).typestate dst
        else budget I.desc (tname s) dst) w.roster := by
  unfold sumOwed
  refine sum_le _ _ w.roster ?_
  intro s hs
  exact owed_one_le I w h hT dst s hs (hC s) hcrash

def aliveBit (st : InstId → Actor) (template : String) (id : InstId) : Nat :=
  if tname id == template && (st id).life == .alive then 1 else 0

def stateBit (st : InstId → Actor) (template state : String) (id : InstId) : Nat :=
  if tname id == template && (st id).life == .alive && (st id).typestate == state then 1 else 0

theorem fold_sum_acc (f : InstId → Nat) (ids : List InstId) (acc : Nat) :
    ids.foldl (fun n id => n + f id) acc = acc + sumFold f ids := by
  induction ids generalizing acc with
  | nil => simp [sumFold]
  | cons id ids ih =>
    simp only [List.foldl_cons, sumFold]
    rw [ih (acc + f id)]
    omega

theorem fold_sum (f : InstId → Nat) (ids : List InstId) :
    ids.foldl (fun n id => n + f id) 0 = sumFold f ids := by
  simpa using fold_sum_acc f ids 0

theorem aliveCount_acc (w : World) (template : String) (ids : List InstId) (acc : Nat) :
    ids.foldl (fun n id => if tname id == template && (w.st id).life == .alive then n + 1 else n) acc =
      acc + sumFold (aliveBit w.st template) ids := by
  induction ids generalizing acc with
  | nil => simp [sumFold]
  | cons id ids ih =>
    simp only [List.foldl_cons, sumFold, aliveBit]
    by_cases hc : (tname id == template && (w.st id).life == .alive) = true
    · simp only [hc, ite_true]
      rw [ih (acc + 1)]
      omega
    · have hf : (tname id == template && (w.st id).life == .alive) = false := by
        cases hbb : tname id == template && (w.st id).life == .alive <;> simp_all
      rw [hf]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih acc]
      omega

theorem aliveCount_sum (w : World) (template : String) :
    aliveCount w template = sumFold (aliveBit w.st template) w.roster := by
  simpa [aliveCount] using aliveCount_acc w template w.roster 0

theorem state_le_alive (st : InstId → Actor) (template state : String) (id : InstId) :
    stateBit st template state id ≤ aliveBit st template id := by
  unfold stateBit aliveBit
  by_cases hn : (tname id == template) = true <;>
    by_cases hl : ((st id).life == .alive) = true <;>
      by_cases hs : ((st id).typestate == state) = true <;>
        simp [hn, hl, hs]

theorem eval_add (x y : Affine) (n : Nat) : (x.add y).eval n = x.eval n + y.eval n := by
  simp [Affine.add, Affine.eval, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]

theorem total_eval_go (dst : String) (n : Nat) (es : List Edge) (acc : Affine) :
    ((es.foldl (fun acc e => if e.dst == dst then acc.add e.occupancy else acc) acc).eval n) =
      es.foldl (fun k e => if e.dst == dst then k + e.occupancy.eval n else k) (acc.eval n) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hd : (e.dst == dst) = true
    · simp only [hd, ite_true]
      rw [ih (acc.add e.occupancy), eval_add]
    · have hf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp only [hf, Bool.false_eq_true, ite_false]
      exact ih acc

theorem total_eval (D : Description) (dst : String) (n : Nat) :
    (totalOcc D dst).eval n =
      D.edges.foldl (fun acc e => if e.dst == dst then acc + e.occupancy.eval n else acc) 0 := by
  simpa [totalOcc, Affine.zero, Affine.eval] using total_eval_go dst n D.edges Affine.zero

theorem slot_here (st : InstId → Actor) (dstName : String) (sender id : InstId)
    (hname : tname id = dstName) :
    slot st dstName sender id = countFrom sender (st id).box + countParked sender (st id).parked := by
  have hb : (tname id == dstName) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb]

theorem owed_ge_here (st : InstId → Actor) (dstName : String) (sender id : InstId) (ids : List InstId)
    (nodup : ids.Nodup) (hmem : id ∈ ids) (hname : tname id = dstName) :
    countFrom sender (st id).box + countParked sender (st id).parked ≤ owed st dstName sender ids := by
  rw [← slot_here st dstName sender id hname]
  induction ids with
  | nil => cases hmem
  | cons j js ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [owed_cons]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      exact Nat.le_add_right _ _
    | inr htail =>
      exact Nat.le_trans (ih hcons.2 htail) (Nat.le_add_left _ _)

theorem mail_le_owed (st : InstId → Actor) (dstName : String) (id : InstId) (ids : List InstId)
    (nodup : ids.Nodup) (hmem : id ∈ ids) (hname : tname id = dstName)
    (hbox : ∀ m ∈ (st id).box, m.sender ∈ ids) (hpark : ∀ p ∈ (st id).parked, p.sender ∈ ids) :
    (st id).box.length + (st id).parked.length ≤ sumFold (fun s => owed st dstName s ids) ids := by
  have hboxL := count_total (st id).box ids nodup hbox
  have hparkL := park_total (st id).parked ids nodup hpark
  have hsum : sumFold (fun s => countFrom s (st id).box + countParked s (st id).parked) ids =
      sumFold (fun s => countFrom s (st id).box) ids + sumFold (fun s => countParked s (st id).parked) ids :=
    sum_add _ _ ids
  have hpoint : sumFold (fun s => countFrom s (st id).box + countParked s (st id).parked) ids ≤
      sumFold (fun s => owed st dstName s ids) ids := by
    refine sum_le _ _ ids ?_
    intro s hs
    exact owed_ge_here st dstName s id ids nodup hmem hname
  rw [← hboxL, ← hparkL, ← hsum]
  exact hpoint

def pay (D : Description) (dst : String) (e : Edge) (st : InstId → Actor) (id : InstId) : Nat :=
  if (st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (st id).typestate ∧ e.dst = dst then
    match templateOf D (tname id) with
    | some t => perInstance t.multiplicity e.occupancy
    | none => 0
  else 0

theorem debt_fold_acc (template state dst : String) (f : Edge → Nat) (acc : Nat) (es : List Edge) :
    es.foldl (fun n e =>
        if e.src == template && e.srcState == state && e.dst == dst then n + f e else n) acc =
      es.foldl (fun n e =>
        n + if e.src = template ∧ e.srcState = state ∧ e.dst = dst then f e else 0) acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hp : e.src = template ∧ e.srcState = state ∧ e.dst = dst
    · have hb : (e.src == template && e.srcState == state && e.dst == dst) = true := by
        rcases hp with ⟨hs, hst, hd⟩
        simp [hs, hst, hd]
      have hL : (if (e.src == template && e.srcState == state && e.dst == dst) = true then acc + f e else acc) =
          acc + f e := by simp [hb]
      have hR : acc + (if e.src = template ∧ e.srcState = state ∧ e.dst = dst then f e else 0) = acc + f e := by
        simp [hp]
      rw [hL, hR]
      exact ih (acc + f e)
    · have hb : (e.src == template && e.srcState == state && e.dst == dst) = false := by
        cases hsrc : e.src == template <;> cases hst : e.srcState == state <;> cases hd : e.dst == dst <;>
          simp_all [beq_iff_eq]
      have hL : (if (e.src == template && e.srcState == state && e.dst == dst) = true then acc + f e else acc) = acc := by
        simp [hb]
      have hR : acc + (if e.src = template ∧ e.srcState = state ∧ e.dst = dst then f e else 0) = acc := by
        simp [hp]
      rw [hL, hR]
      exact ih acc

theorem edge_acc (f : Edge → Nat) (es : List Edge) (acc : Nat) :
    es.foldl (fun n e => n + f e) acc = acc + es.foldl (fun n e => n + f e) 0 := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + f e), ih (f e)]
    omega

theorem per_le_eval (t : Template) (occ : Affine) (n c : Nat)
    (ha : t.multiplicity = .one → occ.a = 0) (hb : t.multiplicity = .perPeer → occ.b = 0)
    (hc1 : t.multiplicity = .one → c ≤ 1) (hcN : t.multiplicity = .perPeer → c ≤ n) :
    perInstance t.multiplicity occ * c ≤ occ.eval n := by
  cases hm : t.multiplicity with
  | one =>
    have h0 := ha hm
    have hcnt := hc1 hm
    simp [perInstance, hm, Affine.eval, h0]
    have hmul : occ.b * c ≤ occ.b * 1 := Nat.mul_le_mul_left _ hcnt
    simpa using hmul
  | perPeer =>
    have h0 := hb hm
    have hcnt := hcN hm
    simp [perInstance, hm, Affine.eval, h0]
    exact Nat.mul_le_mul_left _ hcnt

theorem occShape_edge (I : Impl) (hL : LocalOk I) (e : Edge) (he : e ∈ I.desc.edges) :
    ∃ t, templateOf I.desc e.src = some t ∧
      (t.multiplicity = .one → e.occupancy.a = 0) ∧ (t.multiplicity = .perPeer → e.occupancy.b = 0) := by
  have hshape := (local_parts I hL).2.2.2.1
  unfold occShape at hshape
  simp only [List.all_eq_true] at hshape
  have hall := hshape e he
  cases ht : templateOf I.desc e.src with
  | none => simp [ht] at hall
  | some t =>
    simp only [ht] at hall
    match hmul : t.multiplicity with
    | .one =>
      simp [hmul] at hall
      refine ⟨t, rfl, ?_, ?_⟩
      · intro _
        exact hall
      · intro h
        rw [hmul] at h
        cases h
    | .perPeer =>
      simp [hmul] at hall
      refine ⟨t, rfl, ?_, ?_⟩
      · intro h
        rw [hmul] at h
        cases h
      · intro _
        exact hall

theorem debt_eq (D : Description) (template state dst : String) (t : Template)
    (ht : templateOf D template = some t) :
    debt D template state dst =
      D.edges.foldl (fun n e =>
        n + if e.src = template ∧ e.srcState = state ∧ e.dst = dst then perInstance t.multiplicity e.occupancy else 0) 0 := by
  simp only [debt, ht]
  simpa using debt_fold_acc template state dst (fun e => perInstance t.multiplicity e.occupancy) 0 D.edges

theorem sum_edge (f : Edge → InstId → Nat) (ids : List InstId) (es : List Edge) :
    sumFold (fun id => es.foldl (fun n e => n + f e id) 0) ids =
      es.foldl (fun n e => n + sumFold (f e) ids) 0 := by
  induction es with
  | nil =>
    simp
    exact sum_zero ids
  | cons e es ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    have hrew : sumFold (fun id => es.foldl (fun n e => n + f e id) (f e id)) ids =
        sumFold (fun id => f e id + es.foldl (fun n e => n + f e id) 0) ids := by
      refine sum_congr _ _ ids ?_
      intro id _
      exact edge_acc (fun e => f e id) es (f e id)
    rw [hrew, sum_add, ih, edge_acc (fun e => sumFold (f e) ids) es (sumFold (f e) ids)]

def debtOn (template state dst : String) (k : Edge → Nat) (es : List Edge) : Nat :=
  es.foldl (fun n e =>
    n + if e.src == template && e.srcState == state && e.dst == dst then k e else 0) 0

def liveOn (D : Description) (dst : String) (st : InstId → Actor) (ids : List InstId) (es : List Edge) : Nat :=
  sumFold (fun id =>
    if (st id).life = .alive then
      match templateOf D (tname id) with
      | some t => debtOn (tname id) (st id).typestate dst (fun e => perInstance t.multiplicity e.occupancy) es
      | none => 0
    else 0) ids

theorem debtOn_cons (template state dst : String) (k : Edge → Nat) (e : Edge) (es : List Edge) :
    debtOn template state dst k (e :: es) =
      (if e.src == template && e.srcState == state && e.dst == dst then k e else 0) +
        debtOn template state dst k es := by
  simp only [debtOn, List.foldl_cons, Nat.zero_add]
  exact edge_acc (fun e => if e.src == template && e.srcState == state && e.dst == dst then k e else 0) es
    (if e.src == template && e.srcState == state && e.dst == dst then k e else 0)

theorem bit_01 (b : Bool) : (if b = true then 1 else 0) = 0 ∨ (if b = true then 1 else 0) = 1 := by
  cases b <;> simp

theorem sum_scale (k : Nat) (bit : InstId → Nat) (ids : List InstId)
    (hbit : ∀ id ∈ ids, bit id = 0 ∨ bit id = 1) :
    sumFold (fun id => k * bit id) ids = k * sumFold bit ids := by
  induction ids with
  | nil => simp [sumFold]
  | cons id ids ih =>
    have hid := hbit id (List.Mem.head _)
    simp only [sumFold]
    rw [ih (fun i hi => hbit i (List.Mem.tail _ hi))]
    cases hid with
    | inl hz => simp [hz]
    | inr ho => simp [ho, Nat.mul_add, Nat.add_comm]

theorem stateBit_eq (st : InstId → Actor) (template state : String) (id : InstId) :
    stateBit st template state id =
      if (st id).life = .alive ∧ tname id = template ∧ (st id).typestate = state then 1 else 0 := by
  unfold stateBit
  by_cases h1 : tname id = template <;> by_cases h2 : (st id).life = .alive <;>
      by_cases h3 : (st id).typestate = state <;> simp [h1, h2, h3, beq_iff_eq]

theorem head_le (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (e : Edge)
    (he : e ∈ I.desc.edges) (dst : String) :
    sumFold (fun id =>
      if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
        match templateOf I.desc (tname id) with
        | some t => perInstance t.multiplicity e.occupancy
        | none => 0
      else 0) w.roster ≤
      if e.dst = dst then e.occupancy.eval w.N else 0 := by
  by_cases hd : e.dst = dst
  · obtain ⟨t, ht, ha, hb⟩ := occShape_edge I hL e he
    have hcount : sumFold (stateBit w.st e.src e.srcState) w.roster ≤ aliveCount w e.src := by
      rw [aliveCount_sum]
      refine sum_le _ _ w.roster ?_
      intro id _
      exact state_le_alive w.st e.src e.srcState id
    have hc : sumFold (stateBit w.st e.src e.srcState) w.roster ≤
        if t.multiplicity = .one then 1 else w.N := by
      cases hm : t.multiplicity with
      | one =>
        simp [hm]
        exact Nat.le_trans hcount (hO.liveOne e.src ⟨t, ht, hm⟩)
      | perPeer =>
        simp [hm]
        exact Nat.le_trans hcount (hO.livePeer e.src ⟨t, ht, hm⟩)
    -- each matching actor contributes exactly perInstance, and non-matching contribute 0,
    -- so the sum is perInstance times the state count.
    have hscale : sumFold (fun id =>
        if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
          perInstance t.multiplicity e.occupancy else 0) w.roster =
        perInstance t.multiplicity e.occupancy *
          sumFold (stateBit w.st e.src e.srcState) w.roster := by
      have hfun : ∀ id ∈ w.roster,
          (if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
            perInstance t.multiplicity e.occupancy else 0) =
          perInstance t.multiplicity e.occupancy * stateBit w.st e.src e.srcState id := by
        intro id _
        rw [stateBit_eq]
        by_cases hm : (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate
        · simp [hm, hd]
        · have hif :
            (if (w.st id).life = .alive ∧ tname id = e.src ∧ (w.st id).typestate = e.srcState then 1 else 0) = 0 := by
            by_cases h2 : (w.st id).life = .alive ∧ tname id = e.src ∧ (w.st id).typestate = e.srcState
            · rcases h2 with ⟨hl, hn, hty⟩
              exact absurd ⟨hl, hn.symm, hty.symm⟩ hm
            · simp [h2]
          simp [hm, hd, hif, Nat.mul_zero]
      rw [sum_congr _ _ w.roster hfun]
      have hsc := sum_scale (perInstance t.multiplicity e.occupancy) (stateBit w.st e.src e.srcState) w.roster ?_
      · rw [hsc]
      · intro id _
        rw [stateBit_eq]
        by_cases hb : (w.st id).life = .alive ∧ tname id = e.src ∧ (w.st id).typestate = e.srcState <;> simp [hb]
    have htmpl : sumFold (fun id =>
        if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
          match templateOf I.desc (tname id) with
          | some t => perInstance t.multiplicity e.occupancy
          | none => 0
        else 0) w.roster =
        sumFold (fun id =>
          if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
            perInstance t.multiplicity e.occupancy else 0) w.roster := by
      refine sum_congr _ _ w.roster ?_
      intro id _
      by_cases hm : (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst
      · have hname : tname id = e.src := hm.2.1.symm
        rw [show (if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
            match templateOf I.desc (tname id) with
            | some t => perInstance t.multiplicity e.occupancy
            | none => 0
          else 0) = match templateOf I.desc (tname id) with
            | some t => perInstance t.multiplicity e.occupancy
            | none => 0 from by simp [hm]]
        rw [hname, ht]
        simp [hm]
      · rw [ite_eq_right hm, ite_eq_right hm]
    rw [ite_eq_left hd, htmpl, hscale]
    have hmul := per_le_eval t e.occupancy w.N (sumFold (stateBit w.st e.src e.srcState) w.roster) ha hb
      (by
        intro hone
        have := hc
        simp [hone] at this
        exact this)
      (by
        intro hpeer
        have := hc
        simp [hpeer] at this
        exact this)
    exact hmul
  · rw [ite_eq_right hd]
    have hz : sumFold (fun id =>
        if (w.st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (w.st id).typestate ∧ e.dst = dst then
          match templateOf I.desc (tname id) with
          | some t => perInstance t.multiplicity e.occupancy
          | none => 0
        else 0) w.roster = 0 := by
      refine (sum_congr _ _ w.roster ?_).trans (sum_zero _)
      intro id _
      rw [ite_eq_right (by intro h; exact hd h.2.2.2)]
    rw [hz]
    exact Nat.le_refl _

theorem fold_congr_acc (f g : Edge → Nat) (es : List Edge) (acc : Nat) (h : ∀ e ∈ es, f e = g e) :
    es.foldl (fun n e => n + f e) acc = es.foldl (fun n e => n + g e) acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [h e (List.Mem.head _)]
    exact ih (acc + g e) (fun e he => h e (List.Mem.tail _ he))

theorem fold_zero_add (es : List Edge) : es.foldl (fun n (_ : Edge) => n + 0) 0 = 0 := by
  induction es with
  | nil => rfl
  | cons _ es ih =>
    simp only [List.foldl_cons, Nat.add_zero]
    exact ih

theorem pay_dead (D : Description) (dst : String) (e : Edge) (st : InstId → Actor) (id : InstId)
    (hl : (st id).life ≠ .alive) : pay D dst e st id = 0 := by
  unfold pay
  rw [ite_eq_right (by intro h; exact hl h.1)]

theorem pay_none (D : Description) (dst : String) (e : Edge) (st : InstId → Actor) (id : InstId)
    (ht : templateOf D (tname id) = none) : pay D dst e st id = 0 := by
  unfold pay
  by_cases hc : (st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (st id).typestate ∧ e.dst = dst
  · rw [ite_eq_left hc]
    simp [ht]
  · rw [ite_eq_right hc]

/-- One actor's live debt is the sum, over edges, of what that actor pays into `dst`. -/
theorem actor_pay (D : Description) (st : InstId → Actor) (dst : String) (id : InstId) :
    (if (st id).life = .alive then debt D (tname id) (st id).typestate dst else 0) =
      D.edges.foldl (fun n e => n + pay D dst e st id) 0 := by
  by_cases hl : (st id).life = .alive
  · rw [ite_eq_left hl]
    cases ht : templateOf D (tname id) with
    | none =>
      simp only [debt, ht]
      have hpay : ∀ e ∈ D.edges, pay D dst e st id = 0 := fun e _ => pay_none D dst e st id ht
      rw [fold_congr_acc (pay D dst · st id) (fun _ => 0) D.edges 0 hpay]
      exact (fold_zero_add D.edges).symm
    | some t =>
      rw [debt_eq D (tname id) (st id).typestate dst t ht]
      refine fold_congr_acc _ _ D.edges 0 ?_
      intro e _
      by_cases hd : e.src = tname id ∧ e.srcState = (st id).typestate ∧ e.dst = dst
      · have hc : (st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (st id).typestate ∧ e.dst = dst :=
          ⟨hl, hd.1, hd.2.1, hd.2.2⟩
        unfold pay
        rw [ite_eq_left hc, ite_eq_left hd]
        simp [ht]
      · have hc : ¬ ((st id).life = .alive ∧ e.src = tname id ∧ e.srcState = (st id).typestate ∧ e.dst = dst) :=
          fun h => hd ⟨h.2.1, h.2.2.1, h.2.2.2⟩
        unfold pay
        rw [ite_eq_right hc, ite_eq_right hd]
  · rw [ite_eq_right hl]
    have hpay : ∀ e ∈ D.edges, pay D dst e st id = 0 := fun e _ => pay_dead D dst e st id hl
    rw [fold_congr_acc (pay D dst · st id) (fun _ => 0) D.edges 0 hpay]
    exact (fold_zero_add D.edges).symm

theorem live_pay (D : Description) (st : InstId → Actor) (dst : String) (ids : List InstId) :
    liveDebt D st dst ids =
      sumFold (fun id => D.edges.foldl (fun n e => n + pay D dst e st id) 0) ids := by
  rw [liveDebt_sum]
  refine sum_congr _ _ ids ?_
  intro id _
  exact actor_pay D st dst id

theorem live_swap (D : Description) (st : InstId → Actor) (dst : String) (ids : List InstId) :
    sumFold (fun id => D.edges.foldl (fun n e => n + pay D dst e st id) 0) ids =
      D.edges.foldl (fun n e => n + sumFold (pay D dst e st) ids) 0 :=
  sum_edge (fun e id => pay D dst e st id) ids D.edges

theorem fold_add_le (f g : Edge → Nat) (es : List Edge) (h : ∀ e ∈ es, f e ≤ g e) :
    es.foldl (fun n e => n + f e) 0 ≤ es.foldl (fun n e => n + g e) 0 := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [edge_acc f es (f e), edge_acc g es (g e)]
    exact Nat.add_le_add (h e (List.Mem.head _)) (ih fun e he => h e (List.Mem.tail _ he))

theorem eval_fold_acc (dst : String) (n : Nat) (es : List Edge) (acc : Nat) :
    es.foldl (fun k e => k + if e.dst = dst then e.occupancy.eval n else 0) acc =
      es.foldl (fun k e => if e.dst == dst then k + e.occupancy.eval n else k) acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hd : e.dst = dst
    · have hb : (e.dst == dst) = true := by simpa [beq_iff_eq] using hd
      rw [ite_eq_left hd]
      simp only [hb, ite_true]
      exact ih (acc + e.occupancy.eval n)
    · have hb : (e.dst == dst) = false := by
        cases hbb : e.dst == dst with
        | false => rfl
        | true => exact absurd ((beq_iff_eq).mp hbb) hd
      rw [ite_eq_right hd, Nat.add_zero]
      simp only [hb, Bool.false_eq_true, ite_false]
      exact ih acc

theorem pay_head (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (e : Edge)
    (he : e ∈ I.desc.edges) (dst : String) :
    sumFold (pay I.desc dst e w.st) w.roster ≤ if e.dst = dst then e.occupancy.eval w.N else 0 := by
  unfold pay
  exact head_le I hL w hO e he dst

/-- Live typestate debt, summed over the roster, fits in the Lemma-1 occupancy of `dst`. -/
theorem live_le_occ (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (dst : String) :
    liveDebt I.desc w.st dst w.roster ≤ (totalOcc I.desc dst).eval w.N := by
  rw [live_pay, live_swap]
  have hle := fold_add_le (fun e => sumFold (pay I.desc dst e w.st) w.roster)
    (fun e => if e.dst = dst then e.occupancy.eval w.N else 0) I.desc.edges
    (fun e he => pay_head I hL w hO e he dst)
  rw [eval_fold_acc, ← total_eval] at hle
  exact hle

theorem cap_of_l1 (D : Description) (id : InstId) (n : Nat) (hl1 : l1 D (tname id) = true) :
    (totalOcc D (tname id)).eval n ≤ capBulk D n id := by
  unfold l1 at hl1
  unfold capBulk
  cases ht : templateOf D (tname id) with
  | none => simp [ht] at hl1
  | some t =>
    simp only [ht] at hl1 ⊢
    exact Affine.eval_le_of_leB _ _ hl1 n

theorem queueOk_alive {D : Description} (w : World) (sender host : InstId)
    (hkey : keyAgrees D sender host) (_hlive : (w.st sender).life = .alive) :
    queueOk D w sender host := hkey

/-- A bulk effect that is in scope does not target a core from a terminable role.
A lone terminable does not send. A subtree member sends only to a per-peer role. -/
theorem core_send_from (I : Impl) (w : World) (hO : OccInv I w) (sender dstId : InstId)
    (e : Eff) (es : List Eff) (hmem : dstId ∈ w.roster)
    (hbulk : bulkScopeOf I.desc (tname sender) (e :: es) = true)
    (he : ∃ label hint,
      e = .send (tname dstId) label hint ∨ (∃ na to, e = .call (tname dstId) label hint na to) ∨
        (∃ full gone, e = .trySend (tname dstId) label hint full gone))
    (hk : peerKey dstId = none) :
    peerKey sender = none ∨ terminableB I.desc (tname sender) = false := by
  cases ht : templateOf I.desc (tname sender) with
  | none =>
    exact Or.inr (by simp [terminableB, ht])
  | some t =>
    by_cases hterm : t.terminable = true
    · by_cases hsub : t.subtree = ""
      · obtain ⟨label, hint, he⟩ := he
        have hnb : noBulkSend (e :: es) = true := by
          simpa [bulkScopeOf, ht, hterm, hsub] using hbulk
        rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [noBulkSend] at hnb
      · obtain ⟨label, hint, he⟩ := he
        have hm : memberProgramOk I.desc (tname sender) (e :: es) = true := by
          simpa [bulkScopeOf, ht, hterm, hsub] using hbulk
        have hok := memberProgram_head I.desc (tname sender) e es hm
        have hper : perPeerB I.desc (tname dstId) = true := by
          rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · simp [memberEffectOk, Bool.and_eq_true] at hok
            exact hok.2
          · simp [memberEffectOk, Bool.and_eq_true] at hok
            exact hok.2
          · simp [memberEffectOk, Bool.and_eq_true] at hok
            exact hok.2
        rcases hO.shaped dstId hmem with ⟨tD, htD, hshape⟩
        have hmul : tD.multiplicity = .perPeer := by
          simp only [perPeerB, htD] at hper
          cases hbb : tD.multiplicity with
          | perPeer => rfl
          | one =>
            have hfalse : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
            simp [hbb, hfalse] at hper
        have hex : ∃ k, dstId = InstId.peer tD.name k := by simpa [hmul] using hshape
        obtain ⟨k, hid⟩ := hex
        cases dstId with
        | core _ => cases hid
        | peer _ _ => simp [peerKey] at hk
    · exact Or.inr (by simp [terminableB, ht, hterm])

theorem open_of_nokey (D : Description) (host : InstId) (h : peerKey host = none) :
    openHost D host := by
  unfold openHost
  cases templateOf D (tname host) with
  | none => exact h
  | some _ => exact Or.inl h

theorem key_refl (D : Description) (id : InstId) : keyAgrees D id id :=
  Or.inr rfl

theorem route_agrees (w : World) (D : Description) (sender : InstId) (dst : String) (slot : Nat)
    (id : InstId) (h : route w D sender dst slot = some id) : keyAgrees D sender id := by
  unfold route at h
  split at h
  · cases h
  · next t ht =>
    cases hm : t.multiplicity with
    | one =>
      simp only [hm] at h
      split at h
      · cases h
        exact Or.inl (open_of_nokey D (InstId.core dst) rfl)
      · cases h
    | perPeer =>
      simp only [hm] at h
      by_cases hsl : (t.slots != 0) = true
      · simp only [hsl, ite_true] at h
        split at h
        · have hname := (findLive_spec w dst slot id h).1
          have hopen : openHost D id := by
            unfold openHost
            rw [hname, ht]
            exact Or.inr (by simpa [bne, beq_iff_eq] using hsl)
          exact Or.inl hopen
        · cases h
      · have hzero : (t.slots != 0) = false := by
          cases hbb : t.slots != 0 with
          | false => rfl
          | true => exact absurd hbb hsl
        simp only [hzero, ite_false] at h
        cases hk : memberKey sender with
        | none => simp [hk] at h
        | some k =>
          simp only [hk] at h
          have hname := (findLive_spec w dst k id h).1
          have hkey : peerKey id = some k := by
            have hp := List.find?_some h
            cases id with
            | core _ => simp [findLive, hname] at hp
            | peer n key g =>
              simp only [findLive, Bool.and_eq_true, beq_iff_eq] at hp
              obtain ⟨⟨_, hk'⟩, _⟩ := hp
              subst hk'
              rfl
          have hsend : peerKey sender = some k := by
            cases sender with
            | core _ => simp [memberKey] at hk
            | peer _ key _ =>
              simp [memberKey] at hk
              simp [peerKey, hk]
          exact Or.inr (hsend.symm.trans hkey)

theorem resolve_agrees (D : Description) (w : World) (sender : InstId) (dst : String) (slot : Nat)
    (id : InstId) (h : resolveId D w sender dst slot = some id) : keyAgrees D sender id := by
  unfold resolveId at h
  split at h
  · cases h
  · next t ht =>
    cases hm : t.multiplicity with
    | one =>
      simp only [hm] at h
      cases h
      exact Or.inl (open_of_nokey D (InstId.core dst) rfl)
    | perPeer =>
      simp only [hm] at h
      by_cases hsl : (t.slots != 0) = true
      · simp only [hsl, ite_true] at h
        split at h
        · cases h
        · next k hklt =>
          split at h
          · have hname := (findLive_spec w dst slot id h).1
            have hopen : openHost D id := by
              unfold openHost
              rw [hname, ht]
              exact Or.inr (by simpa [bne, beq_iff_eq] using hsl)
            exact Or.inl hopen
          · cases h
            exact Or.inl (by
              unfold openHost
              simp [tname, ht]
              exact Or.inr (by simpa [bne, beq_iff_eq] using hsl))
      · have hzero : (t.slots != 0) = false := by
          cases hbb : t.slots != 0 with
          | false => rfl
          | true => exact absurd hbb hsl
        simp only [hzero, ite_false] at h
        cases hk : memberKey sender with
        | none => simp [hk] at h
        | some k =>
          simp only [hk] at h
          have hsend : peerKey sender = some k := by
            cases sender with
            | core _ => simp [memberKey] at hk
            | peer _ key _ =>
              simp [memberKey] at hk
              simp [peerKey, hk]
          split at h
          · have hkey : peerKey id = some k := by
              have hp := List.find?_some h
              cases id with
              | core _ => simp [findLive] at hp
              | peer _ key _ =>
                simp only [findLive, Bool.and_eq_true, beq_iff_eq] at hp
                obtain ⟨⟨_, hk'⟩, _⟩ := hp
                subst hk'
                rfl
            cases h
            exact Or.inr (hsend.symm.trans hkey)
          · cases h
            exact Or.inr (by simpa [peerKey] using hsend)

theorem peer_same (a b : InstId) (k : Nat) (ha : peerKey a = some k) (hb : peerKey b = some k)
    (hn : tname a = tname b) : a = b := by
  cases a with
  | core _ => cases ha
  | peer na ka =>
    cases b with
    | core _ => cases hb
    | peer nb kb =>
      simp only [peerKey, tname] at ha hb hn
      injection ha with ha
      injection hb with hb
      subst ha
      subst hb
      subst hn
      rfl

theorem sum_ge_mem (f : InstId → Nat) (ids : List InstId) (s : InstId) (hs : s ∈ ids)
    (nodup : ids.Nodup) : f s ≤ sumFold f ids := by
  induction ids with
  | nil => cases hs
  | cons id ids ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [sumFold]
    cases List.mem_cons.mp hs with
    | inl heq =>
      subst heq
      exact Nat.le_add_right _ _
    | inr h =>
      exact Nat.le_trans (ih h hcons.2) (Nat.le_add_left _ _)

theorem owed_le_budget (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String)
    (s : InstId) (hs : s ∈ w.roster) (hC : contTy (w.st s)) (hcrash : w.crashed = false) :
    owed w.st dst s w.roster ≤ budget I.desc (tname s) dst := by
  have h1 := owed_one_le I w h hT dst s hs hC hcrash
  by_cases hl : (w.st s).life = .alive
  · simp [hl] at h1
    cases ht : templateOf I.desc (tname s) with
    | none =>
      have hele := hT s hl
      simp [statesOf, ht, List.elem] at hele
    | some t =>
      have hele := hT s hl
      have hst : (w.st s).typestate ∈ t.states := by
        simpa [statesOf, ht, List.elem_iff] using hele
      exact Nat.le_trans h1 (debt_le_budget I.desc (tname s) (w.st s).typestate dst ⟨t, ht, hst⟩)
  · simp [hl] at h1
    exact h1

def edgeInst (D : Description) (e : Edge) : Nat :=
  match templateOf D e.src with
  | some t => perInstance t.multiplicity e.occupancy
  | none => 0

def instFold (D : Description) (dst : String) : List Edge → Nat
  | [] => 0
  | e :: es => (if e.dst == dst then edgeInst D e else 0) + instFold D dst es

def srcFold (D : Description) (dst src : String) : List Edge → Nat
  | [] => 0
  | e :: es => (if e.dst == dst && e.src == src then edgeInst D e else 0) + srcFold D dst src es

theorem debt_src_go (D : Description) (template state dst : String) (t : Template)
    (ht : templateOf D template = some t) :
    ∀ es acc,
      es.foldl (fun n e =>
        if e.src == template && e.srcState == state && e.dst == dst then
          n + perInstance t.multiplicity e.occupancy else n) acc ≤
        acc + srcFold D dst template es := by
  intro es
  induction es with
  | nil => intro acc; simp [srcFold]
  | cons e es ih =>
    intro acc
    simp only [List.foldl_cons, srcFold]
    by_cases hp : e.src = template ∧ e.srcState = state ∧ e.dst = dst
    · have hb : (e.src == template && e.srcState == state && e.dst == dst) = true := by
        rcases hp with ⟨hs, hst, hd⟩
        simp [hs, hst, hd]
      have hsrc : (e.dst == dst && e.src == template) = true := by
        rcases hp with ⟨hs, _, hd⟩
        simp [hs, hd]
      have he : edgeInst D e = perInstance t.multiplicity e.occupancy := by
        have ht' : templateOf D e.src = some t := by simpa [hp.1] using ht
        simp [edgeInst, ht']
      simp only [hb, hsrc, ite_true, he]
      have ih' := ih (acc + perInstance t.multiplicity e.occupancy)
      rw [Nat.add_assoc] at ih'
      exact ih'
    · have hb : (e.src == template && e.srcState == state && e.dst == dst) = false := by
        cases hsrc : e.src == template <;> cases hst : e.srcState == state <;>
          cases hd : e.dst == dst <;> simp_all [beq_iff_eq]
      simp only [hb, ite_false]
      by_cases hs : e.src = template ∧ e.dst = dst
      · have hsrc : (e.dst == dst && e.src == template) = true := by
          rcases hs with ⟨hs, hd⟩
          simp [hs, hd]
        rw [hsrc]
        simp only [ite_true]
        have ih' := ih acc
        exact Nat.le_trans ih' (Nat.add_le_add_left (Nat.le_add_left _ _) _)
      · have hsrc : (e.dst == dst && e.src == template) = false := by
          cases hsb : e.src == template <;> cases hd : e.dst == dst <;> simp_all [beq_iff_eq]
        rw [hsrc]
        have hacc :
            (if false = true then acc + perInstance t.multiplicity e.occupancy else acc) = acc := by
          split
          · rename_i hfalse
            cases hfalse
          · rfl
        have hzero : (if false = true then edgeInst D e else 0) = 0 := by
          split
          · rename_i hfalse
            cases hfalse
          · rfl
        rw [hacc, hzero, Nat.zero_add]
        exact ih acc

theorem debt_le_srcFold (D : Description) (template state dst : String) :
    debt D template state dst ≤ srcFold D dst template D.edges := by
  cases ht : templateOf D template with
  | none => simp [debt, ht]
  | some t =>
    have h := debt_src_go D template state dst t ht D.edges 0
    simpa [debt, ht] using h

theorem maxFold_le {α : Type} (f : α → Nat) (bound : Nat) :
    ∀ (xs : List α) (acc : Nat), acc ≤ bound → (∀ x ∈ xs, f x ≤ bound) →
      xs.foldl (fun m y => Nat.max m (f y)) acc ≤ bound
  | [], _, hacc, _ => hacc
  | x :: xs, acc, hacc, hf => by
    simp only [List.foldl_cons]
    exact maxFold_le f bound xs (Nat.max acc (f x))
      (Nat.max_le.mpr ⟨hacc, hf x (List.Mem.head _)⟩)
      (fun y hy => hf y (List.Mem.tail _ hy))

theorem budget_le_srcFold (D : Description) (template dst : String) :
    budget D template dst ≤ srcFold D dst template D.edges := by
  cases ht : templateOf D template with
  | none => simp [budget, ht]
  | some t =>
    simp [budget, ht]
    refine maxFold_le (fun st => debt D template st dst) (srcFold D dst template D.edges) t.states 0
      (Nat.zero_le _) ?_
    intro st _
    exact debt_le_srcFold D template st dst

def allowed (banned : List String) (src : String) : Bool :=
  !(banned.elem src)

def instFoldB (D : Description) (dst : String) (banned : List String) : List Edge → Nat
  | [] => 0
  | e :: es =>
    (if e.dst == dst && allowed banned e.src then edgeInst D e else 0) + instFoldB D dst banned es

theorem instFoldB_nil (D : Description) (dst : String) :
    ∀ es, instFoldB D dst [] es = instFold D dst es := by
  intro es
  induction es with
  | nil => rfl
  | cons _ es ih =>
    simp [instFoldB, instFold, allowed, List.elem, ih]

theorem fold_split (D : Description) (dst name : String) (banned : List String)
    (h : allowed banned name = true) :
    ∀ es, instFoldB D dst banned es =
      srcFold D dst name es + instFoldB D dst (name :: banned) es := by
  intro es
  induction es with
  | nil => simp [instFoldB, srcFold]
  | cons e es ih =>
    by_cases hd : (e.dst == dst) = true
    · by_cases hn : (e.src == name) = true
      · have hname : e.src = name := by simpa [beq_iff_eq] using hn
        have hok : allowed banned e.src = true := by simpa [hname] using h
        have hallow : allowed (name :: banned) e.src = false := by
          unfold allowed
          simp only [List.elem_cons, hn, Bool.or_true, Bool.not_true]
        simp [instFoldB, srcFold, hd, hn, hok, hallow, ih]
        omega
      · have hnf : (e.src == name) = false := by
          cases hbb : e.src == name <;> simp_all
        have hallow : allowed (name :: banned) e.src = allowed banned e.src := by
          unfold allowed
          simp only [List.elem_cons, hnf, Bool.or_false]
        simp [instFoldB, srcFold, hd, hnf, hallow, ih]
        omega
    · have hdf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp [instFoldB, srcFold, hdf, ih]

theorem keySum_le (D : Description) (dst : String) (k : Nat) (banned : List String)
    (ids : List InstId) (nodup : ids.Nodup)
    (hban : ∀ s, s ∈ ids → peerKey s = some k → (banned.elem (tname s)) = false) :
    sumFold (fun s => if peerKey s = some k then budget D (tname s) dst else 0) ids ≤
      instFoldB D dst banned D.edges := by
  induction ids generalizing banned with
  | nil => simp [sumFold]
  | cons s ids ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [sumFold]
    by_cases hk : peerKey s = some k
    · simp only [hk, ite_true]
      have hfresh : allowed banned (tname s) = true := by
        have hfalse := hban s (List.Mem.head _) hk
        unfold allowed
        rw [hfalse]
        exact Bool.not_false
      have htail := ih (tname s :: banned) hcons.2 ?_
      · have hbudget := budget_le_srcFold D (tname s) dst
        have hsplit := fold_split D dst (tname s) banned hfresh D.edges
        rw [hsplit]
        exact Nat.add_le_add hbudget htail
      · intro s' hs' hk'
        have hne : tname s' ≠ tname s := by
          intro hn
          exact hcons.1 ((peer_same s' s k hk' hk hn) ▸ hs')
        have hold : (banned.elem (tname s')) = false := hban s' (List.Mem.tail _ hs') hk'
        have hbb : (tname s' == tname s) = false := by simpa [beq_iff_eq] using hne
        rw [List.elem_cons, hbb, hold]
    · simp only [hk, ite_false, Nat.zero_add]
      exact ih banned hcons.2 (fun s' hs' hk' => hban s' (List.Mem.tail _ hs') hk')

theorem edgeInst_le_eval (I : Impl) (hL : LocalOk I) (e : Edge) (he : e ∈ I.desc.edges) (n : Nat)
    (hn : 1 ≤ n) : edgeInst I.desc e ≤ e.occupancy.eval n := by
  obtain ⟨t, ht, ha, hb⟩ := occShape_edge I hL e he
  simp [edgeInst, ht]
  simpa [Nat.mul_one] using
    per_le_eval t e.occupancy n 1 ha hb (fun _ => Nat.le_refl _) (fun _ => hn)

theorem instFold_le_eval (I : Impl) (hL : LocalOk I) (dst : String) (n : Nat) (hn : 1 ≤ n) :
    instFold I.desc dst I.desc.edges ≤ (totalOcc I.desc dst).eval n := by
  rw [total_eval]
  have hgen : ∀ es acc, (∀ e ∈ es, e ∈ I.desc.edges) →
      instFold I.desc dst es + acc ≤
        es.foldl (fun k e => if e.dst == dst then k + e.occupancy.eval n else k) acc := by
    intro es
    induction es with
    | nil =>
      intro acc _
      simp [instFold]
    | cons e es ih =>
      intro acc hmem
      have he := hmem e (List.Mem.head _)
      simp only [instFold, List.foldl_cons]
      by_cases hd : (e.dst == dst) = true
      · simp only [hd, ite_true]
        have hle := edgeInst_le_eval I hL e he n hn
        have ih' := ih (acc + e.occupancy.eval n) (fun e' he' => hmem e' (List.Mem.tail _ he'))
        omega
      · have hdf : (e.dst == dst) = false := by
          cases hbb : e.dst == dst
          · rfl
          · exact absurd hbb hd
        simp only [hdf]
        have hleft : (if false = true then edgeInst I.desc e else 0) = 0 := by
          split
          · rename_i hfalse
            cases hfalse
          · rfl
        have hright : (if false = true then acc + e.occupancy.eval n else acc) = acc := by
          split
          · rename_i hfalse
            cases hfalse
          · rfl
        rw [hleft, hright, Nat.zero_add]
        exact ih acc (fun e' he' => hmem e' (List.Mem.tail _ he'))
  simpa using hgen I.desc.edges 0 (fun _ he => he)

theorem filter_nil_ban (es : List Edge) :
    es.filter (fun e => ((([] : List String).elem e.src) == false)) = es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp [List.elem, List.filter_cons, ih]

theorem mem_countFrom (sender : InstId) (m : Msg) (ms : List Msg) (hm : m ∈ ms)
    (hs : m.sender = sender) : 1 ≤ countFrom sender ms := by
  induction ms with
  | nil => cases hm
  | cons x xs ih =>
    cases hm with
    | head => simp [countFrom, hs]
    | tail _ htail =>
      simp [countFrom]
      by_cases hx : x.sender = sender
      · simp [hx]
      · simp [hx]
        exact ih htail

theorem mem_countParked (sender : InstId) (p : Parked) (ps : List Parked) (hp : p ∈ ps)
    (hs : p.sender = sender) : 1 ≤ countParked sender ps := by
  induction ps with
  | nil => cases hp
  | cons x xs ih =>
    cases hp with
    | head => simp [countParked, hs]
    | tail _ htail =>
      simp [countParked]
      by_cases hx : x.sender = sender
      · simp [hx]
      · simp [hx]
        exact ih htail

theorem countFrom_out (sender : InstId) : ∀ ms : List Msg, (∀ m ∈ ms, m.sender ≠ sender) → countFrom sender ms = 0
  | [], _ => rfl
  | m :: ms, h => by
    have hm : m.sender ≠ sender := h m (List.Mem.head _)
    have ht := countFrom_out sender ms (fun m' hm' => h m' (List.Mem.tail _ hm'))
    simp [countFrom, hm, ht]

/-- `name` belongs to a dead core on the roster. A multiplicity-one role is not
spawned again, so this is the only actor that can still owe on `name`. -/
def deadName (st : InstId → Actor) (ids : List InstId) (name : String) : Bool :=
  ids.any fun s => (peerKey s == none) && (tname s == name) && ((st s).life != .alive)

def evalSrc (dst src : String) (n : Nat) : List Edge → Nat
  | [] => 0
  | e :: es =>
    (if e.dst == dst && e.src == src then e.occupancy.eval n else 0) + evalSrc dst src n es

def evalDst (dst : String) (n : Nat) : List Edge → Nat
  | [] => 0
  | e :: es => (if e.dst == dst then e.occupancy.eval n else 0) + evalDst dst n es

/-- Edges into `dst` whose source is a dead core, skipping names in `banned`. -/
def evalDead (st : InstId → Actor) (ids : List InstId) (dst : String) (n : Nat)
    (banned : List String) : List Edge → Nat
  | [] => 0
  | e :: es =>
    (if e.dst == dst && deadName st ids e.src && allowed banned e.src then e.occupancy.eval n else 0) +
      evalDead st ids dst n banned es

/-- Edges into `dst` whose source is not a dead core. -/
def evalLive (st : InstId → Actor) (ids : List InstId) (dst : String) (n : Nat) : List Edge → Nat
  | [] => 0
  | e :: es =>
    (if e.dst == dst && !(deadName st ids e.src) then e.occupancy.eval n else 0) + evalLive st ids dst n es

theorem core_same (a b : InstId) (ha : peerKey a = none) (hb : peerKey b = none)
    (hn : tname a = tname b) : a = b := by
  cases a <;> cases b <;> simp [peerKey, tname] at ha hb hn
  · subst hn
    rfl

theorem one_edge_eval (I : Impl) (hL : LocalOk I) (e : Edge) (he : e ∈ I.desc.edges) (t : Template)
    (ht : templateOf I.desc e.src = some t) (hone : t.multiplicity = .one) (n : Nat) :
    edgeInst I.desc e = e.occupancy.eval n := by
  obtain ⟨t', ht', ha, _hb⟩ := occShape_edge I hL e he
  have hteq : t' = t := by
    injection ht'.symm.trans ht
  subst hteq
  have ha0 := ha hone
  simp [edgeInst, ht, hone, perInstance, Affine.eval, ha0, Nat.zero_mul, Nat.zero_add]

theorem src_le_eval_go (I : Impl) (hL : LocalOk I) (dst name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hone : t.multiplicity = .one) (n : Nat) :
    ∀ es, (∀ e ∈ es, e ∈ I.desc.edges) → srcFold I.desc dst name es ≤ evalSrc dst name n es := by
  intro es hes
  induction es with
  | nil => simp [srcFold, evalSrc]
  | cons e es ih =>
    have he := hes e (List.Mem.head _)
    by_cases hc : (e.dst == dst && e.src == name) = true
    · have hsrc : e.src = name := by
        simp [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.2
      have hinst := one_edge_eval I hL e he t (by simpa [hsrc] using ht) hone n
      simp [srcFold, evalSrc, hc, hinst]
      exact ih fun e' he' => hes e' (List.Mem.tail _ he')
    · have hf : (e.dst == dst && e.src == name) = false := by
        cases hbb : e.dst == dst && e.src == name <;> simp_all
      simp [srcFold, evalSrc, hf]
      exact ih fun e' he' => hes e' (List.Mem.tail _ he')

theorem eval_dead_split (st : InstId → Actor) (ids : List InstId) (dst name : String) (n : Nat)
    (banned : List String) (h : allowed banned name = true) (hdead : deadName st ids name = true) :
    ∀ es, evalDead st ids dst n banned es =
      evalSrc dst name n es + evalDead st ids dst n (name :: banned) es := by
  intro es
  induction es with
  | nil => simp [evalDead, evalSrc]
  | cons e es ih =>
    by_cases hd : (e.dst == dst) = true
    · by_cases hn : (e.src == name) = true
      · have hname : e.src = name := by simpa [beq_iff_eq] using hn
        have hok : allowed banned e.src = true := by simpa [hname] using h
        have hmark : deadName st ids e.src = true := by simpa [hname] using hdead
        have hallow : allowed (name :: banned) e.src = false := by
          unfold allowed
          simp only [List.elem_cons, hn, Bool.or_true, Bool.not_true]
        simp [evalDead, evalSrc, hd, hn, hok, hmark, hallow, ih]
        omega
      · have hnf : (e.src == name) = false := by
          cases hbb : e.src == name <;> simp_all
        have hallow : allowed (name :: banned) e.src = allowed banned e.src := by
          unfold allowed
          simp only [List.elem_cons, hnf, Bool.or_false]
        simp [evalDead, evalSrc, hd, hnf, hallow, ih]
        omega
    · have hdf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp [evalDead, evalSrc, hdf, ih]

theorem eval_parts (st : InstId → Actor) (ids : List InstId) (dst : String) (n : Nat) :
    ∀ es, evalLive st ids dst n es + evalDead st ids dst n [] es = evalDst dst n es := by
  intro es
  induction es with
  | nil => simp [evalLive, evalDead, evalDst]
  | cons e es ih =>
    by_cases hd : (e.dst == dst) = true
    · by_cases hdead : deadName st ids e.src = true
      · simp [evalLive, evalDead, evalDst, allowed, List.elem, hd, hdead, ih]
        omega
      · have hf : deadName st ids e.src = false := by
          cases hbb : deadName st ids e.src <;> simp_all
        simp [evalLive, evalDead, evalDst, allowed, List.elem, hd, hf, ih]
        omega
    · have hdf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp [evalLive, evalDead, evalDst, hdf, ih]

theorem fold_eval_add (dst : String) (n acc : Nat) :
    ∀ es : List Edge, es.foldl (fun a e => if e.dst == dst then a + e.occupancy.eval n else a) acc =
      acc + es.foldl (fun a e => if e.dst == dst then a + e.occupancy.eval n else a) 0 := by
  intro es
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hd : (e.dst == dst) = true
    · simp only [hd, ite_true, Nat.zero_add]
      rw [ih (acc + e.occupancy.eval n), ih (e.occupancy.eval n)]
      omega
    · have hf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp only [hf, ite_false]
      exact ih acc

theorem evalDst_fold (dst : String) (n : Nat) :
    ∀ es : List Edge, evalDst dst n es =
      es.foldl (fun acc e => if e.dst == dst then acc + e.occupancy.eval n else acc) 0 := by
  intro es
  induction es with
  | nil => simp [evalDst]
  | cons e es ih =>
    simp only [evalDst, List.foldl_cons]
    by_cases hd : (e.dst == dst) = true
    · simp only [hd, ite_true, Nat.zero_add]
      rw [fold_eval_add dst n (e.occupancy.eval n) es, ih]
    · have hf : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all
      simp only [hf, Bool.false_eq_true, ite_false, Nat.zero_add]
      exact ih

theorem evalDst_total (D : Description) (dst : String) (n : Nat) :
    evalDst dst n D.edges = (totalOcc D dst).eval n := by
  rw [evalDst_fold, ← total_eval]

theorem box_le_live (st : InstId → Actor) (dstName : String) (id : InstId) (ids : List InstId)
    (nodup : ids.Nodup) (hmem : id ∈ ids) (hname : tname id = dstName)
    (hfrom : ∀ m ∈ (st id).box, m.sender ∈ ids)
    (halive : ∀ m ∈ (st id).box, (st m.sender).life = .alive) :
    (st id).box.length ≤
      sumFold (fun s => if (st s).life = .alive then owed st dstName s ids else 0) ids := by
  have hlen := count_total (st id).box ids nodup hfrom
  have hpoint : sumFold (fun s => countFrom s (st id).box) ids ≤
      sumFold (fun s => if (st s).life = .alive then owed st dstName s ids else 0) ids := by
    refine sum_le _ _ ids ?_
    intro s hs
    by_cases hl : (st s).life = .alive
    · simp [hl]
      exact Nat.le_trans (Nat.le_add_right _ _) (owed_ge_here st dstName s id ids nodup hmem hname)
    · simp [hl]
      exact countFrom_out s (st id).box (fun m hm heq => by
        have hlive := halive m hm
        rw [heq] at hlive
        exact hl hlive)
  rw [← hlen]
  exact hpoint

theorem live_owed_le (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String)
    (hC : ∀ s, contTy (w.st s)) (hcrash : w.crashed = false) :
    sumFold (fun s => if (w.st s).life = .alive then owed w.st dst s w.roster else 0) w.roster ≤
      liveDebt I.desc w.st dst w.roster := by
  rw [liveDebt_sum]
  refine sum_le _ _ w.roster ?_
  intro s hs
  by_cases hl : (w.st s).life = .alive
  · simp [hl]
    have h1 := owed_one_le I w h hT dst s hs (hC s) hcrash
    simpa [hl] using h1
  · simp [hl]

theorem box_le_key (st : InstId → Actor) (dstName : String) (id : InstId) (ids : List InstId)
    (k : Nat) (nodup : ids.Nodup) (hmem : id ∈ ids) (hname : tname id = dstName)
    (hfrom : ∀ m ∈ (st id).box, m.sender ∈ ids)
    (hkey : ∀ m ∈ (st id).box, peerKey m.sender = some k) :
    (st id).box.length ≤
      sumFold (fun s => if peerKey s = some k then owed st dstName s ids else 0) ids := by
  have hlen := count_total (st id).box ids nodup hfrom
  have hpoint : sumFold (fun s => countFrom s (st id).box) ids ≤
      sumFold (fun s => if peerKey s = some k then owed st dstName s ids else 0) ids := by
    refine sum_le _ _ ids ?_
    intro s hs
    by_cases hp : peerKey s = some k
    · simp [hp]
      exact Nat.le_trans (Nat.le_add_right _ _) (owed_ge_here st dstName s id ids nodup hmem hname)
    · simp [hp]
      exact countFrom_out s (st id).box (fun m hm heq => by
        have hk := hkey m hm
        rw [heq] at hk
        exact hp hk)
  rw [← hlen]
  exact hpoint

theorem dead_mem (st : InstId → Actor) (ids : List InstId) (name : String)
    (h : deadName st ids name = true) :
    ∃ s, s ∈ ids ∧ peerKey s = none ∧ tname s = name ∧ (st s).life ≠ .alive := by
  induction ids with
  | nil => simp [deadName, List.any] at h
  | cons a as ih =>
    unfold deadName at h
    simp only [List.any_cons, Bool.or_eq_true] at h
    cases h with
    | inl hp =>
      simp [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hp
      exact ⟨a, List.Mem.head _, hp.1.1, hp.1.2, hp.2⟩
    | inr ht =>
      obtain ⟨s, hs, hk, hn, hl⟩ := ih ht
      exact ⟨s, List.Mem.tail _ hs, hk, hn, hl⟩

theorem deadName_of_mem (st : InstId → Actor) (ids : List InstId) (s : InstId) (hs : s ∈ ids)
    (hk : peerKey s = none) (hl : (st s).life ≠ .alive) : deadName st ids (tname s) = true := by
  induction ids with
  | nil => cases hs
  | cons a as ih =>
    cases List.mem_cons.mp hs with
    | inl heq =>
      subst heq
      simp [deadName, List.any_cons, hk, hl, beq_iff_eq, bne_iff_ne]
    | inr htail =>
      unfold deadName
      simp only [List.any_cons, Bool.or_eq_true]
      exact Or.inr (ih htail)

theorem pay_sum_dead (I : Impl) (w : World) (hO : OccInv I w) (e : Edge) (dst : String)
    (hdead : deadName w.st w.roster e.src = true) :
    sumFold (pay I.desc dst e w.st) w.roster = 0 := by
  obtain ⟨s, hs, hpk, htn, hdeadS⟩ := dead_mem w.st w.roster e.src hdead
  refine (sum_congr (pay I.desc dst e w.st) (fun _ => 0) w.roster ?_).trans (sum_zero w.roster)
  intro id hid
  unfold pay
  rw [ite_eq_right ?_]
  intro hc
  rcases hc with ⟨hlive, hsrc, _hst, _hdst⟩
  rcases hO.shaped s hs with ⟨t, ht, hmul⟩
  rcases hO.shaped id hid with ⟨t', ht', hmul'⟩
  have hname : tname id = tname s := by rw [← hsrc, htn]
  have hteq : t' = t := by
    injection ht'.symm.trans (by simpa [hname] using ht)
  cases hteq
  cases hm : t.multiplicity with
  | perPeer =>
    have hex : ∃ k, s = InstId.peer t.name k := by simpa [hm] using hmul
    obtain ⟨k, hidS⟩ := hex
    cases s with
    | core _ => cases hidS
    | peer _ _ => simp [peerKey] at hpk
  | one =>
    have hsId : s = InstId.core t.name := by simpa [hm] using hmul
    have hidId : id = InstId.core t.name := by simpa [hm] using hmul'
    have heq : id = s := by rw [hidId, hsId]
    exact hdeadS (heq ▸ hlive)

theorem fold_add_acc (f : Edge → Nat) (acc : Nat) :
    ∀ es : List Edge, es.foldl (fun a e => a + f e) acc = acc + es.foldl (fun a e => a + f e) 0 := by
  intro es
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + f e), ih (f e)]
    omega

theorem evalLive_add (st : InstId → Actor) (ids : List InstId) (dst : String) (n : Nat) :
    ∀ es : List Edge, es.foldl (fun acc e => acc +
        (if e.dst == dst && !(deadName st ids e.src) then e.occupancy.eval n else 0)) 0 =
      evalLive st ids dst n es := by
  intro es
  induction es with
  | nil => simp [evalLive]
  | cons e es ih =>
    simp only [List.foldl_cons, evalLive, Nat.zero_add]
    rw [fold_add_acc (fun e =>
        if e.dst == dst && !(deadName st ids e.src) then e.occupancy.eval n else 0)
      (if e.dst == dst && !(deadName st ids e.src) then e.occupancy.eval n else 0) es, ih]

/-- Live debt uses only edges whose source is not a dead core. A dead core's
pay is zero: it is the only actor of its template, and it is dead. -/
theorem live_le_open (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (dst : String) :
    liveDebt I.desc w.st dst w.roster ≤ evalLive w.st w.roster dst w.N I.desc.edges := by
  rw [live_pay, live_swap]
  have hle := fold_add_le (fun e => sumFold (pay I.desc dst e w.st) w.roster)
    (fun e => if e.dst == dst && !(deadName w.st w.roster e.src) then e.occupancy.eval w.N else 0)
    I.desc.edges ?_
  rw [evalLive_add] at hle
  exact hle
  intro e he
  by_cases hdead : deadName w.st w.roster e.src = true
  · simp [pay_sum_dead I w hO e dst hdead, hdead]
  · have hf : deadName w.st w.roster e.src = false := by
      cases hbb : deadName w.st w.roster e.src <;> simp_all
    have hpay := pay_head I hL w hO e he dst
    by_cases hd : e.dst = dst
    · have hb : (e.dst == dst) = true := by simpa [beq_iff_eq] using hd
      simp [hd] at hpay
      simp [hf, hb, hpay]
    · have hb : (e.dst == dst) = false := by
        cases hbb : e.dst == dst <;> simp_all [beq_iff_eq, hd]
      simp [hd] at hpay
      simp [hpay, hb]

/-- Budgets of dead cores, over a roster suffix, fit in the edges those cores
still own. `banned` names have already been counted. -/
theorem dead_budget_go (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (dst : String)
    (banned : List String) (ids : List InstId) (hsub : ∀ s ∈ ids, s ∈ w.roster) (nodup : ids.Nodup)
    (hban : ∀ s ∈ ids, peerKey s = none → (w.st s).life ≠ .alive → banned.elem (tname s) = false) :
    sumFold (fun s =>
      if peerKey s = none then
        if (w.st s).life = .alive then 0 else budget I.desc (tname s) dst
      else 0) ids ≤
      evalDead w.st w.roster dst w.N banned I.desc.edges := by
  induction ids generalizing banned with
  | nil =>
    simp [sumFold]
  | cons s ids ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [sumFold]
    by_cases hk : peerKey s = none
    · by_cases hl : (w.st s).life = .alive
      · simp only [hk, hl, ite_true, Nat.zero_add]
        exact ih banned (fun s' hs' => hsub s' (List.Mem.tail _ hs')) hcons.2
          (fun s' hs' hk' hl' => hban s' (List.Mem.tail _ hs') hk' hl')
      · simp only [hk, hl, ite_false]
        have hfresh : allowed banned (tname s) = true := by
          have hfalse := hban s (List.Mem.head _) hk hl
          unfold allowed
          rw [hfalse]
          exact Bool.not_false
        have htail := ih (tname s :: banned)
          (fun s' hs' => hsub s' (List.Mem.tail _ hs')) hcons.2 ?_
        · rcases hO.shaped s (hsub s (List.Mem.head _)) with ⟨t, ht, hmul⟩
          cases hm : t.multiplicity with
          | perPeer =>
            have hex : ∃ k, s = InstId.peer t.name k := by simpa [hm] using hmul
            obtain ⟨k, hidS⟩ := hex
            cases s with
            | core _ => cases hidS
            | peer _ _ => simp [peerKey] at hk
          | one =>
            have hsrc := src_le_eval_go I hL dst (tname s) t ht hm w.N I.desc.edges (fun _ he => he)
            have hbud := budget_le_srcFold I.desc (tname s) dst
            have hmark := deadName_of_mem w.st w.roster s (hsub s (List.Mem.head _)) hk hl
            have hsplit := eval_dead_split w.st w.roster dst (tname s) w.N banned hfresh hmark
              I.desc.edges
            rw [hsplit]
            exact Nat.add_le_add (Nat.le_trans hbud hsrc) htail
        · intro s' hs' hk' hl'
          have hne : tname s' ≠ tname s := by
            intro hn
            exact hcons.1 ((core_same s' s hk' hk hn) ▸ hs')
          have hold := hban s' (List.Mem.tail _ hs') hk' hl'
          have hbb : (tname s' == tname s) = false := by simpa [beq_iff_eq] using hne
          rw [List.elem_cons, hbb, hold]
    · simp only [hk, ite_false, Nat.zero_add]
      exact ih banned (fun s' hs' => hsub s' (List.Mem.tail _ hs')) hcons.2
        (fun s' hs' hk' hl' => hban s' (List.Mem.tail _ hs') hk' hl')

/-- Live typestate debt and the budgets left by dead cores share the Lemma-1
occupancy. The two sets of edges are disjoint. -/
theorem core_room (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (dst : String) :
    liveDebt I.desc w.st dst w.roster +
      sumFold (fun s =>
        if peerKey s = none then
          if (w.st s).life = .alive then 0 else budget I.desc (tname s) dst
        else 0) w.roster ≤
      (totalOcc I.desc dst).eval w.N := by
  have hlive := live_le_open I hL w hO dst
  have hdead := dead_budget_go I hL w hO dst [] w.roster (fun _ hs => hs) hO.nodup
    (fun _ _ _ => by simp [List.elem])
  have hparts := eval_parts w.st w.roster dst w.N I.desc.edges
  rw [evalDst_total] at hparts
  omega

theorem box_le_parts (st : InstId → Actor) (dstName : String) (id : InstId) (ids : List InstId)
    (nodup : ids.Nodup) (hmem : id ∈ ids) (hname : tname id = dstName)
    (hfrom : ∀ m ∈ (st id).box, m.sender ∈ ids)
    (hwho : ∀ m ∈ (st id).box, (st m.sender).life = .alive ∨ peerKey m.sender = none) :
    (st id).box.length ≤
      sumFold (fun s => if (st s).life = .alive then owed st dstName s ids else 0) ids +
      sumFold (fun s =>
        if peerKey s = none then
          if (st s).life = .alive then 0 else owed st dstName s ids
        else 0) ids := by
  have hlen := count_total (st id).box ids nodup hfrom
  have hpoint : sumFold (fun s => countFrom s (st id).box) ids ≤
      sumFold (fun s =>
        (if (st s).life = .alive then owed st dstName s ids else 0) +
        (if peerKey s = none then
          if (st s).life = .alive then 0 else owed st dstName s ids
        else 0)) ids := by
    refine sum_le _ _ ids ?_
    intro s hs
    by_cases hl : (st s).life = .alive
    · simp [hl]
      exact Nat.le_trans (Nat.le_add_right _ _) (owed_ge_here st dstName s id ids nodup hmem hname)
    · by_cases hk : peerKey s = none
      · simp [hl, hk]
        exact Nat.le_trans (Nat.le_add_right _ _) (owed_ge_here st dstName s id ids nodup hmem hname)
      · simp [hl, hk]
        exact countFrom_out s (st id).box (fun m hm heq => by
          have hdis := hwho m hm
          rw [heq] at hdis
          cases hdis with
          | inl hl' => exact hl hl'
          | inr hk' => exact hk hk')
  rw [hlen] at hpoint
  rw [sum_add
    (fun s => if (st s).life = .alive then owed st dstName s ids else 0)
    (fun s =>
      if peerKey s = none then
        if (st s).life = .alive then 0 else owed st dstName s ids
      else 0)] at hpoint
  exact hpoint

/-- A Lemma-1 mailbox holds at most `capBulk` messages, counting the parked lane.
A dead host is empty. A core holds live senders and at most one budget from each
dead core. A per-peer host holds one key, and each template on that key owes at
most its budget. -/
theorem l1_fit (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (hT : TyOk I.desc w)
    (id : InstId) (hl1 : l1 I.desc (tname id) = true) :
    (w.st id).box.length + (w.st id).parked.length ≤ capBulk I.desc w.N id := by
  have hpark := hO.clear id hl1
  rw [hpark, List.length_nil, Nat.add_zero]
  by_cases hlive : (w.st id).life = .alive
  · have hmem := hO.aliveIn id hlive
    cases hk : peerKey id with
    | none =>
      have hwho : ∀ m ∈ (w.st id).box,
          (w.st m.sender).life = .alive ∨ peerKey m.sender = none := by
        intro m hm
        exact ((hO.sameKey id).1 m hm).2 hk
      have hbox := box_le_parts w.st (tname id) id w.roster hO.nodup hmem rfl
        (fun m hm => hO.sentFrom id m hm) hwho
      have hliveD := live_owed_le I w hO hT (tname id)
      have hdead : sumFold (fun s =>
          if peerKey s = none then
            if (w.st s).life = .alive then 0 else owed w.st (tname id) s w.roster
          else 0) w.roster ≤
          sumFold (fun s =>
            if peerKey s = none then
              if (w.st s).life = .alive then 0 else budget I.desc (tname s) (tname id)
            else 0) w.roster := by
        refine sum_le _ _ w.roster ?_
        intro s hs
        by_cases hpk : peerKey s = none
        · by_cases hl : (w.st s).life = .alive
          · simp [hpk, hl]
          · simp [hpk, hl]
            exact hO.quiet s (tname id) hs hl
        · simp [hpk]
      have hroom := core_room I hL w hO (tname id)
      have hcap := cap_of_l1 I.desc id w.N hl1
      exact Nat.le_trans hbox (Nat.le_trans (Nat.add_le_add hliveD hdead)
        (Nat.le_trans hroom hcap))
    | some k =>
      have hshape := hO.shaped id hmem
      rcases hshape with ⟨t, ht, hmul⟩
      cases hm : t.multiplicity with
      | one =>
        have hid : id = InstId.core t.name := by simpa [hm] using hmul
        cases id with
        | core _ => simp [peerKey] at hk
        | peer _ _ => cases hid
      | perPeer =>
        have hex : ∃ k, id = InstId.peer t.name k := by simpa [hm] using hmul
        obtain ⟨k0, hid⟩ := hex
        cases id with
        | core _ => simp [peerKey] at hk
        | peer name key =>
          have hid' : InstId.peer name key = InstId.peer t.name k0 := hid
          simp [InstId.peer.injEq] at hid'
          rcases hid' with ⟨hname, hkey0⟩
          have hk' : key = k := by
            have hp : peerKey (InstId.peer name key) = some key := rfl
            simp [hp] at hk
            exact hk
          have hN1 : 1 ≤ w.N := by
            have hbit : aliveBit w.st (tname (InstId.peer name key)) (InstId.peer name key) = 1 := by
              unfold aliveBit
              simp [hlive, beq_iff_eq]
            have hge := sum_ge_mem (aliveBit w.st (tname (InstId.peer name key))) w.roster
              (InstId.peer name key) hmem hO.nodup
            have hone : 1 ≤ aliveCount w (tname (InstId.peer name key)) := by
              rw [aliveCount_sum]
              simpa [hbit] using hge
            exact Nat.le_trans hone (hO.livePeer (tname (InstId.peer name key)) ⟨t, by simpa [hname] using ht, hm⟩)
          have hkey : ∀ m ∈ (w.st (InstId.peer name key)).box, peerKey m.sender = some key := by
            intro m hm
            have hdis := ((hO.sameKey (InstId.peer name key)).1 m hm).1
            simp [keyAgrees, peerKey] at hdis
            exact hdis
          have hbox := box_le_key w.st (tname (InstId.peer name key)) (InstId.peer name key) w.roster
            key hO.nodup hmem rfl (fun m hm => hO.sentFrom _ m hm) hkey
          have hpoint : sumFold (fun s =>
              if peerKey s = some key then owed w.st (tname (InstId.peer name key)) s w.roster else 0)
              w.roster ≤
              sumFold (fun s =>
                if peerKey s = some key then budget I.desc (tname s) (tname (InstId.peer name key)) else 0)
                w.roster := by
            refine sum_le _ _ w.roster ?_
            intro s hs
            by_cases hp : peerKey s = some key
            · simp [hp]
              exact owed_le_budget I w hO hT _ s hs
            · simp [hp]
          have hkeys := keySum_le I.desc (tname (InstId.peer name key)) key [] w.roster hO.nodup
            (fun _ _ _ => rfl)
          rw [instFoldB_nil] at hkeys
          have hfold := instFold_le_eval I hL (tname (InstId.peer name key)) w.N hN1
          have hcap := cap_of_l1 I.desc (InstId.peer name key) w.N hl1
          exact Nat.le_trans hbox (Nat.le_trans hpoint (Nat.le_trans hkeys (Nat.le_trans hfold hcap)))
  · have hempty := (hO.deadEmpty id (by simpa [hlive])).1
    simp [hempty]

theorem sum_one_slack (f g : InstId → Nat) (ids : List InstId) (s : InstId) (hs : s ∈ ids)
    (nodup : ids.Nodup) (hle : ∀ id ∈ ids, f id ≤ g id) (hextra : f s + 1 ≤ g s) :
    sumFold f ids + 1 ≤ sumFold g ids := by
  induction ids with
  | nil => cases hs
  | cons id ids ih =>
    have hcons := (List.nodup_cons).mp nodup
    simp only [sumFold]
    cases List.mem_cons.mp hs with
    | inl heq =>
      subst heq
      have htail := sum_le f g ids (fun i hi => hle i (List.Mem.tail _ hi))
      have hhead := hextra
      omega
    | inr htail =>
      have ih' := ih htail hcons.2 (fun i hi => hle i (List.Mem.tail _ hi))
      have hhead := hle id (List.Mem.head _)
      omega

/-- The park branch of `enqueueOrPark` is unreachable for a Lemma-1 mailbox the
sender can actually deliver to. The sender still has the send in its
continuation, so its outstanding is strictly below the typestate debt, and
`clear` keeps the parked lane empty. A per-peer mailbox only counts the
sender's own key: residual mail of another key is not in this box. -/
theorem l1_park_unreachable (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w)
    (hT : TyOk I.desc w) (sender dst : InstId) (hlive : (w.st dst).life = .alive)
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hpend : 1 ≤ pending (w.st sender) (tname dst)) (hl1 : l1 I.desc (tname dst) = true)
    (hagree : keyAgrees sender dst) :
    (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst := by
  have hpark := hO.clear dst hl1
  have hmem : dst ∈ w.roster := hO.aliveIn dst hlive
  have hdebt : owed w.st (tname dst) sender w.roster + 1 ≤
      debt I.desc (tname sender) (w.st sender).typestate (tname dst) := by
    have hS := hO.slack sender (tname dst) hsend hsender
    have hB := hO.balance sender (tname dst) hsend
    cases ht : templateOf I.desc (tname sender) with
    | none =>
      have hele := hT sender hsender
      simp [statesOf, ht, List.elem] at hele
    | some t =>
      have hele := hT sender hsender
      have hst : (w.st sender).typestate ∈ t.states := by
        simpa [statesOf, ht, List.elem_iff] using hele
      have hF := floor_add_debt I.desc (tname sender) (w.st sender).typestate (tname dst) ⟨t, ht, hst⟩
      have hle := owed_le_debt _ _ _ _ _ _ hB hS hF
      omega
  have hdbud : owed w.st (tname dst) sender w.roster + 1 ≤
      budget I.desc (tname sender) (tname dst) := by
    cases ht : templateOf I.desc (tname sender) with
    | none =>
      have hele := hT sender hsender
      simp [statesOf, ht, List.elem] at hele
    | some t =>
      have hele := hT sender hsender
      have hst : (w.st sender).typestate ∈ t.states := by
        simpa [statesOf, ht, List.elem_iff] using hele
      exact Nat.le_trans hdebt (debt_le_budget I.desc (tname sender) (w.st sender).typestate
        (tname dst) ⟨t, ht, hst⟩)
  cases hk : peerKey dst with
  | none =>
    have hwho : ∀ m ∈ (w.st dst).box,
        (w.st m.sender).life = .alive ∨ peerKey m.sender = none := by
      intro m hm
      exact ((hO.sameKey dst).1 m hm).2 hk
    have hbox := box_le_parts w.st (tname dst) dst w.roster hO.nodup hmem rfl
      (fun m hm => hO.sentFrom dst m hm) hwho
    have hsum : sumFold (fun s =>
        if (w.st s).life = .alive then owed w.st (tname dst) s w.roster else 0) w.roster + 1 ≤
        liveDebt I.desc w.st (tname dst) w.roster := by
      rw [liveDebt_sum]
      refine sum_one_slack _ _ w.roster sender hsend hO.nodup ?_ ?_
      · intro s hs
        by_cases hl : (w.st s).life = .alive
        · simp [hl]
          have h1 := owed_one_le I w hO hT (tname dst) s hs
          simpa [hl] using h1
        · simp [hl]
      · simp [hsender]
        exact hdebt
    have hdead : sumFold (fun s =>
        if peerKey s = none then
          if (w.st s).life = .alive then 0 else owed w.st (tname dst) s w.roster
        else 0) w.roster ≤
        sumFold (fun s =>
          if peerKey s = none then
            if (w.st s).life = .alive then 0 else budget I.desc (tname s) (tname dst)
          else 0) w.roster := by
      refine sum_le _ _ w.roster ?_
      intro s hs
      by_cases hpk : peerKey s = none
      · by_cases hl : (w.st s).life = .alive
        · simp [hpk, hl]
        · simp [hpk, hl]
          exact hO.quiet s (tname dst) hs hl
      · simp [hpk]
    have hroom := core_room I hL w hO (tname dst)
    have hcap := cap_of_l1 I.desc dst w.N hl1
    have hlt : (w.st dst).box.length + 1 ≤ capBulk I.desc w.N dst := by
      have hjoin := Nat.add_le_add hsum hdead
      omega
    exact ⟨hpark, Nat.lt_of_succ_le hlt⟩
  | some k =>
    have hkS : peerKey sender = some k := by
      unfold keyAgrees at hagree
      rcases hagree with hnone | hsame
      · simp [hk] at hnone
      · simpa [hk] using hsame
    have hshape := hO.shaped dst hmem
    rcases hshape with ⟨t, ht, hmul⟩
    cases hm : t.multiplicity with
    | one =>
      have hid : dst = InstId.core t.name := by simpa [hm] using hmul
      cases dst with
      | core _ => simp [peerKey] at hk
      | peer _ _ => cases hid
    | perPeer =>
      have hex : ∃ k, dst = InstId.peer t.name k := by simpa [hm] using hmul
      obtain ⟨k0, hid⟩ := hex
      cases dst with
      | core _ => simp [peerKey] at hk
      | peer name key =>
        have hkeyM : ∀ m ∈ (w.st (InstId.peer name key)).box, peerKey m.sender = some key := by
          intro m hm
          have hdis := ((hO.sameKey (InstId.peer name key)).1 m hm).1
          simp [keyAgrees, peerKey] at hdis
          exact hdis
        have hkKey : key = k := by
          have hp : peerKey (InstId.peer name key) = some key := rfl
          simp [hp] at hk
          exact hk
        have hbox := box_le_key w.st (tname (InstId.peer name key)) (InstId.peer name key) w.roster
          key hO.nodup hmem rfl (fun m hm => hO.sentFrom _ m hm) hkeyM
        have hsum : sumFold (fun s =>
            if peerKey s = some key then owed w.st (tname (InstId.peer name key)) s w.roster else 0)
            w.roster + 1 ≤
            sumFold (fun s =>
              if peerKey s = some key then
                budget I.desc (tname s) (tname (InstId.peer name key)) else 0) w.roster := by
          refine sum_one_slack _ _ w.roster sender hsend hO.nodup ?_ ?_
          · intro s hs
            by_cases hp : peerKey s = some key
            · simp [hp]
              exact owed_le_budget I w hO hT _ s hs
            · simp [hp]
          · simp [hkS, hkKey]
            exact hdbud
        have hN1 : 1 ≤ w.N := by
          have hbit : aliveBit w.st (tname (InstId.peer name key)) (InstId.peer name key) = 1 := by
            unfold aliveBit
            simp [hlive, beq_iff_eq]
          have hge := sum_ge_mem (aliveBit w.st (tname (InstId.peer name key))) w.roster
            (InstId.peer name key) hmem hO.nodup
          have hone : 1 ≤ aliveCount w (tname (InstId.peer name key)) := by
            rw [aliveCount_sum]
            simpa [hbit] using hge
          have hid' : InstId.peer name key = InstId.peer t.name k0 := hid
          simp [InstId.peer.injEq] at hid'
          exact Nat.le_trans hone (hO.livePeer (tname (InstId.peer name key))
            ⟨t, by simpa [hid'.1] using ht, hm⟩)
        have hkeys := keySum_le I.desc (tname (InstId.peer name key)) key [] w.roster hO.nodup
          (fun _ _ _ => rfl)
        rw [instFoldB_nil] at hkeys
        have hfold := instFold_le_eval I hL (tname (InstId.peer name key)) w.N hN1
        have hcap := cap_of_l1 I.desc (InstId.peer name key) w.N hl1
        have hlt : (w.st (InstId.peer name key)).box.length + 1 ≤ capBulk I.desc w.N
            (InstId.peer name key) :=
          Nat.le_trans (Nat.add_le_add_right hbox 1)
            (Nat.le_trans hsum (Nat.le_trans hkeys (Nat.le_trans hfold hcap)))
        exact ⟨hpark, Nat.lt_of_succ_le hlt⟩

theorem name_lines (D : Description) (hG : GraphOk D) : nameFails D = [] := by
  have h := hG.struct
  unfold structLines at h
  exact append_nil_left (append_nil_left (append_nil_left (append_nil_left
    (append_nil_left (append_nil_left (append_nil_left (append_nil_left (append_nil_left h))))))))

theorem accum_fresh {α : Type} [DecidableEq α] (acc xs : List α) (hacc : acc.Nodup)
    (h : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) acc).length =
      acc.length + xs.length) :
    xs.Nodup ∧ ∀ x ∈ xs, x ∉ acc := by
  induction xs generalizing acc with
  | nil =>
    simp at h
    exact ⟨List.nodup_nil, fun _ hmem => by cases hmem⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons] at h
    cases hx : acc.elem x
    · simp only [hx, Bool.false_eq_true, ite_false] at h
      have hacc' : (acc ++ [x]).Nodup := nodup_snoc hacc (by
        intro hin
        have := List.elem_iff.mpr hin
        rw [hx] at this
        cases this)
      have hlen : (acc ++ [x]).length = acc.length + 1 := by simp [List.length_append]
      have h' : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) (acc ++ [x])).length =
          (acc ++ [x]).length + xs.length := by
        rw [hlen]
        omega
      obtain ⟨hxs, hfresh⟩ := ih (acc ++ [x]) hacc' h'
      refine ⟨?_, ?_⟩
      · refine (List.nodup_cons).mpr ⟨?_, hxs⟩
        intro hin
        exact hfresh x hin (List.mem_append_right _ (List.Mem.head _))
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · intro hin
          have := List.elem_iff.mpr hin
          rw [hx] at this
          cases this
        · intro hin
          exact hfresh y hy (List.mem_append_left _ hin)
    · simp only [hx, ite_true] at h
      have hle := foldDedup_len_le acc xs
      omega

theorem nodup_of_dedup_len {α : Type} [DecidableEq α] (xs : List α) (h : (dedup xs).length = xs.length) :
    xs.Nodup := by
  have h0 : (xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) ([] : List α)).length =
      ([] : List α).length + xs.length := by simpa [dedup, Nat.zero_add] using h
  exact (accum_fresh [] xs List.nodup_nil h0).1

theorem names_nodup (D : Description) (hG : GraphOk D) : (D.templates.map (·.name)).Nodup :=
  nodup_of_dedup_len _ (nameFails_len D (name_lines D hG))

theorem core_filter_nodup (xs : List Template) (h : (xs.map (·.name)).Nodup) :
    (xs.filterMap fun t => if t.multiplicity == .one then some (InstId.core t.name) else none).Nodup := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    have hcons := (List.nodup_cons).mp h
    rw [List.filterMap_cons]
    by_cases hb : (t.multiplicity == .one) = true
    · simp only [hb, ite_true]
      refine (List.nodup_cons).mpr ⟨?_, ih hcons.2⟩
      intro hin
      have hname : t.name ∈ ts.map (·.name) := by
        rw [List.mem_filterMap] at hin
        obtain ⟨u, hu, hif⟩ := hin
        cases hub : u.multiplicity == .one <;> rw [hub] at hif
        · simp at hif
        · simp at hif
          exact List.mem_map.mpr ⟨u, hu, hif⟩
      exact hcons.1 hname
    · have hf : (t.multiplicity == .one) = false := by
        cases hbb : t.multiplicity == .one <;> simp_all
      simp only [hf, ite_false]
      exact ih hcons.2

theorem coreRoster_nodup (D : Description) (hG : GraphOk D) : (coreRoster D).Nodup := by
  simpa [coreRoster] using core_filter_nodup D.templates (names_nodup D hG)

theorem find_named (xs : List Template) (t : Template) (ht : t ∈ xs) (h : (xs.map (·.name)).Nodup) :
    xs.findSome? (fun u => if u.name == t.name then some u else none) = some t := by
  induction xs with
  | nil => cases ht
  | cons u us ih =>
    have hcons := (List.nodup_cons).mp h
    rw [List.findSome?_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · simp
    · have hdiff : (u.name == t.name) = false := by
        by_cases hn : u.name = t.name
        · exact absurd (by
            have : t.name ∈ us.map (·.name) := List.mem_map.mpr ⟨t, ht, rfl⟩
            simpa [hn] using this) hcons.1
        · cases hbb : u.name == t.name <;> simp_all [beq_iff_eq]
      simp only [hdiff, ite_false]
      exact ih ht hcons.2

theorem core_template (D : Description) (id : InstId) (hG : GraphOk D) (h : id ∈ coreRoster D) :
    ∃ t, templateOf D (tname id) = some t ∧ t.multiplicity = .one ∧ id = InstId.core t.name := by
  rw [coreRoster, List.mem_filterMap] at h
  obtain ⟨t, hmem, hif⟩ := h
  cases hb : t.multiplicity == .one <;> simp [hb] at hif
  cases hif
  have hone : t.multiplicity = .one := by
    cases hm : t.multiplicity with
    | one => rfl
    | perPeer =>
      rw [hm] at hb
      have hfalse : (Multiplicity.perPeer == Multiplicity.one) = false := by decide
      rw [hfalse] at hb
      cases hb
  refine ⟨t, ?_, hone, rfl⟩
  simpa [templateOf, tname] using find_named D.templates t hmem (names_nodup D hG)

/-- An alive core of a reachable world is a multiplicity-one role.
Spawn only adds peers, and no step makes an absent core alive. -/
theorem reachable_core_one (I : Impl) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (name : String) (hl : (w.st (InstId.core name)).life = .alive) :
    ∃ t, templateOf I.desc name = some t ∧ t.multiplicity = .one := by
  induction hR generalizing name with
  | init =>
    obtain ⟨t, ht, hone, _⟩ :=
      core_template I.desc (InstId.core name) hG (init_core_mem I N name hl)
    exact ⟨t, by simpa [tname] using ht, hone⟩
  | step w w' a _ hstep ih =>
    exact ih name (apply_core_prev I w w' a name hstep hl)

/-- A multiplicity-one template is not a subtree member. `subtreeFails` records it. -/
theorem one_not_subtree (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hne : t.subtree ≠ "") (hone : t.multiplicity = .one) : False := by
  have hmap := hG.subtrees
  simp [subtreeFails] at hmap
  exact subtreeEntry_not_one D t hne hone (hmap t (templateOf_mem D name t ht).1)

theorem fold_cell_roster (reader : InstId) (labels : List String) (w : World) :
    ((labels.foldl (fun w label =>
        let c := w.cell (tname reader) label
        let w := setCell w (tname reader) label { c with dirty := false }
        setObserved w reader label c.value) w).roster) = w.roster := by
  induction labels generalizing w with
  | nil => rfl
  | cons label labels ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [setCell, setObserved]

theorem readCells_roster (D : Description) (w : World) (id : InstId) :
    (readCells D w id).roster = w.roster := by
  simpa [readCells] using fold_cell_roster id (cellLabels D (tname id)) w

theorem fold_read_roster (D : Description) (ids : List InstId) (w : World) :
    ((ids.foldl (fun w id => readCells D w id) w).roster) = w.roster := by
  induction ids generalizing w with
  | nil => rfl
  | cons id ids ih =>
    rw [List.foldl_cons, ih (readCells D w id), readCells_roster]

theorem fold_cell_N (reader : InstId) (labels : List String) (w : World) :
    ((labels.foldl (fun w label =>
        let c := w.cell (tname reader) label
        let w := setCell w (tname reader) label { c with dirty := false }
        setObserved w reader label c.value) w).N) = w.N := by
  induction labels generalizing w with
  | nil => rfl
  | cons label labels ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [setCell, setObserved]

theorem readCells_N (D : Description) (w : World) (id : InstId) : (readCells D w id).N = w.N := by
  simpa [readCells] using fold_cell_N id (cellLabels D (tname id)) w

theorem fold_read_N (D : Description) (ids : List InstId) (w : World) :
    ((ids.foldl (fun w id => readCells D w id) w).N) = w.N := by
  induction ids generalizing w with
  | nil => rfl
  | cons id ids ih =>
    rw [List.foldl_cons, ih (readCells D w id), readCells_N]

theorem init_N (I : Impl) (N : Nat) : (initWorld I N).N = N := by
  unfold initWorld
  simpa using fold_read_N I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

theorem fold_cell_crashed (reader : InstId) (labels : List String) (w : World) :
    ((labels.foldl (fun w label =>
        let c := w.cell (tname reader) label
        let w := setCell w (tname reader) label { c with dirty := false }
        setObserved w reader label c.value) w).crashed) = w.crashed := by
  induction labels generalizing w with
  | nil => rfl
  | cons label labels ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [setCell, setObserved]

theorem readCells_crashed (D : Description) (w : World) (id : InstId) :
    (readCells D w id).crashed = w.crashed := by
  simpa [readCells] using fold_cell_crashed id (cellLabels D (tname id)) w

theorem fold_read_crashed (D : Description) (ids : List InstId) (w : World) :
    ((ids.foldl (fun w id => readCells D w id) w).crashed) = w.crashed := by
  induction ids generalizing w with
  | nil => rfl
  | cons id ids ih =>
    rw [List.foldl_cons, ih (readCells D w id), readCells_crashed]

theorem init_crashed (I : Impl) (N : Nat) : (initWorld I N).crashed = false := by
  unfold initWorld
  simpa using fold_read_crashed I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

theorem findLive_mem (w : World) (name : String) (key : Nat) (id : InstId)
    (h : findLive w name key = some id) : id ∈ w.roster := by
  unfold findLive at h
  revert h
  induction w.roster with
  | nil =>
    intro h
    simp at h
  | cons x xs ih =>
    intro h
    rw [List.find?_cons] at h
    split at h
    · cases h
      exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem findLive_peer (w : World) (name : String) (key : Nat) (id : InstId)
    (h : findLive w name key = some id) : ∃ g, id = InstId.peer name key g := by
  have hp := List.find?_some h
  cases id with
  | core _ => simp [findLive] at hp
  | peer n k g =>
    simp only [findLive, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨hn, hk⟩, _hl⟩ := hp
    subst hn
    subst hk
    exact ⟨g, rfl⟩

theorem findLive_not_core (w : World) (name : String) (key : Nat) (id : InstId)
    (h : findLive w name key = some id) : ∀ n, id ≠ InstId.core n := by
  intro n heq
  obtain ⟨_g, hid⟩ := findLive_peer w name key id h
  cases hid
  cases heq

/-- `setActor` that keeps life does not move which generation holds a slot. -/
theorem findLive_set_life (w : World) (id : InstId) (a : Actor)
    (hlife : a.life = (w.st id).life) (name : String) (key : Nat) :
    findLive (setActor w id a) name key = findLive w name key := by
  unfold findLive
  simp only [setActor]
  congr 1
  funext i
  cases i with
  | core _ => rfl
  | peer n k g =>
    by_cases h : InstId.peer n k g = id
    · simp [h, hlife]
    · simp [h]

theorem foldl_pointwise {α β : Type} (f g : β → α → β) (l : List α) (b : β)
    (h : ∀ b a, a ∈ l → f b a = g b a) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h b a (List.Mem.head _)]
    exact ih (g b a) fun b' a' ha => h b' a' (List.Mem.tail _ ha)

/-- Queued mail is unchanged when the rewritten actor keeps its box and parked list. -/
theorem queuedFromKey_set (w : World) (id : InstId) (a : Actor)
    (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked)
    (name : String) (key : Nat) (dst : String) :
    queuedFromKey (setActor w id a) name key dst = queuedFromKey w name key dst := by
  unfold queuedFromKey
  simp only [setActor]
  refine foldl_pointwise _ _ w.roster 0 ?_
  intro n host _
  by_cases hh : host = id
  · simp [hh, hbox, hpark]
  · simp [hh]

theorem init_box (I : Impl) (N : Nat) (id : InstId) :
    ((initWorld I N).st id).box = [] ∧ ((initWorld I N).st id).parked = [] := by
  rw [init_base_st]
  split
  · cases ht : templateOf I.desc (tname id) with
    | none => simp [initActor, ht, absentActor]
    | some _ => simp [initActor, ht, withTokens]
  · simp [absentActor]

theorem init_tokens (I : Impl) (hG : GraphOk I.desc) (N : Nat) (id : InstId)
    (h : id ∈ (initWorld I N).roster) (d : String) :
    ((initWorld I N).st id).tokens d = (budget I.desc (tname id) d : Int) := by
  have hmem : id ∈ coreRoster I.desc := by simpa [init_roster] using h
  have hcont : (coreRoster I.desc).contains id = true := List.contains_iff_mem.mpr hmem
  rw [init_base_st, if_pos hcont]
  obtain ⟨t, ht, _, _⟩ := core_template I.desc id hG hmem
  simp [initActor, ht, withTokens]

theorem init_alive (I : Impl) (hG : GraphOk I.desc) (N : Nat) (id : InstId)
    (h : id ∈ (initWorld I N).roster) : ((initWorld I N).st id).life = .alive := by
  have hmem : id ∈ coreRoster I.desc := by simpa [init_roster] using h
  have hcont : (coreRoster I.desc).contains id = true := List.contains_iff_mem.mpr hmem
  rw [init_base_st, if_pos hcont]
  obtain ⟨t, ht, _, _⟩ := core_template I.desc id hG hmem
  simp [initActor, ht, withTokens]

theorem init_bit (I : Impl) (hG : GraphOk I.desc) (N : Nat) (template : String) (id : InstId)
    (h : id ∈ coreRoster I.desc) :
    aliveBit (initWorld I N).st template id = if id = InstId.core template then 1 else 0 := by
  obtain ⟨t, ht, _, hid⟩ := core_template I.desc id hG h
  have hcont : (coreRoster I.desc).contains id = true := List.contains_iff_mem.mpr h
  have halive : ((initWorld I N).st id).life = .alive := by
    rw [init_base_st, if_pos hcont]
    simp [initActor, ht, withTokens]
  unfold aliveBit
  by_cases hn : tname id = template
  · have hid' : id = InstId.core template := by
      rw [hid]
      have hname : t.name = template := by simpa [tname, hid] using hn
      rw [hname]
    have hb1 : (tname id == template) = true := by simpa [beq_iff_eq] using hn
    have hb2 : (((initWorld I N).st id).life == .alive) = true := by simpa [beq_iff_eq] using halive
    simp only [hid']
    rw [← hid']
    simp only [hb1, hb2, Bool.and_self, ite_true]
  · have hb1 : (tname id == template) = false := by
      cases hbb : tname id == template <;> simp_all [beq_iff_eq]
    have hdiff : id ≠ InstId.core template := by
      intro heq
      apply hn
      rw [hid] at heq
      cases heq
      simp [tname, hid]
    simp [hb1, hdiff]

/-- Every initial core is alive, idle, and holding exactly its send budget. -/
theorem occ_init (I : Impl) (hG : GraphOk I.desc) (N : Nat) : OccInv I (initWorld I N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [init_roster] using coreRoster_nodup I.desc hG
  · intro id hl
    rw [init_base_st] at hl
    simp only [List.contains_iff_mem] at hl
    by_cases hmem : id ∈ coreRoster I.desc
    · simpa [init_roster] using hmem
    · rw [ite_eq_right hmem] at hl
      simp [absentActor] at hl
  · intro name key g1 _g2 h1 _h2 _hl1 _hl2
    have hmem : InstId.peer name key g1 ∈ coreRoster I.desc := by simpa [init_roster] using h1
    obtain ⟨_t, _ht, _hone, hid⟩ := core_template I.desc (InstId.peer name key g1) hG hmem
    cases hid
  · intro template ⟨t, ht, hone⟩
    rw [aliveCount_sum, init_roster]
    have hfun : ∀ id ∈ coreRoster I.desc,
        aliveBit (initWorld I N).st template id = if id = InstId.core template then 1 else 0 :=
      fun id hid => init_bit I hG N template id hid
    have hflip : ∀ id ∈ coreRoster I.desc,
        (if id = InstId.core template then 1 else 0) = if InstId.core template = id then 1 else 0 := by
      intro id _
      by_cases heq : id = InstId.core template
      · simp [heq]
      · have hne : InstId.core template ≠ id := fun h => heq h.symm
        simp [heq, hne]
    rw [sum_congr _ _ _ hfun, sum_congr _ _ _ hflip,
      sum_hit (InstId.core template) (coreRoster I.desc) (coreRoster_nodup I.desc hG)]
    by_cases hmem : InstId.core template ∈ coreRoster I.desc <;> simp [hmem]
  · intro template ⟨t, ht, hpeer⟩
    rw [aliveCount_sum, init_roster, init_N]
    have hzero : sumFold (aliveBit (initWorld I N).st template) (coreRoster I.desc) = 0 := by
      refine (sum_congr _ _ _ ?_).trans (sum_zero _)
      intro id hid
      obtain ⟨u, hu, hone, hidc⟩ := core_template I.desc id hG hid
      unfold aliveBit
      by_cases hn : tname id = template
      · have hsame : u = t := by
          have : templateOf I.desc template = some u := by simpa [hn] using hu
          rw [ht] at this
          cases this
          rfl
        have hbad : t.multiplicity = .one := by rw [← hsame]; exact hone
        rw [hpeer] at hbad
        cases hbad
      · simp [hn, beq_iff_eq]
    rw [hzero]
    exact Nat.zero_le _
  · intro id hnin
    have hmem : id ∉ coreRoster I.desc := by simpa [init_roster] using hnin
    have hcont : (coreRoster I.desc).contains id = false := by
      rw [Bool.eq_false_iff]
      intro ht
      exact hmem (List.contains_iff_mem.mp ht)
    rw [init_base_st, hcont]
    simp [absentActor]
  · intro id m hm
    have hempty := (init_box I N id).1
    simp [hempty] at hm
  · intro id p hp
    have hempty := (init_box I N id).2
    simp [hempty] at hp
  · intro id p hp
    have hempty := (init_box I N id).2
    simp [hempty] at hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key id d hlive
      have hmem : id ∈ coreRoster I.desc := by simpa [init_roster] using findLive_mem _ _ _ _ hlive
      obtain ⟨_t, _ht, _hone, hid⟩ := core_template I.desc id hG hmem
      exact absurd hid (findLive_not_core _ _ _ _ hlive _)
    · intro name d _hl hmem
      have hzero := owed_zero_of_empty (initWorld I N).st d (.core name) (initWorld I N).roster
        (fun id _ => init_box I N id)
      rw [hzero, Int.natCast_zero, Int.add_zero]
      exact init_tokens I hG N (.core name) hmem d
    · intro _name _key d _hnone
      have hzero : queuedFromKey (initWorld I N) _name _key d = 0 := by
        unfold queuedFromKey
        suffices ∀ ids n,
            ids.foldl (fun n host =>
              if tname host != d then n
              else n + (((initWorld I N).st host).box.filter fun m =>
                match m.sender with
                | .peer s k _ => s == _name && k == _key
                | .core _ => false).length +
                (((initWorld I N).st host).parked.filter fun p =>
                  match p.msg.sender with
                  | .peer s k _ => s == _name && k == _key
                  | .core _ => false).length) n = n by
          exact this (initWorld I N).roster 0
        intro ids
        induction ids with
        | nil => intro n; rfl
        | cons host ids ih =>
          intro n
          have hempty := init_box I N host
          simp only [List.foldl_cons, hempty.1, hempty.2, List.filter_nil, List.length_nil,
            Nat.add_zero, ite_self]
          exact ih n
      rw [hzero, Int.natCast_zero]
      exact Int.natCast_nonneg _
  · intro id d hl
    have hmem : id ∈ coreRoster I.desc := by
      rw [init_base_st] at hl
      simp only [List.contains_iff_mem] at hl
      by_cases hmem : id ∈ coreRoster I.desc
      · exact hmem
      · rw [ite_eq_right hmem] at hl
        simp [absentActor] at hl
    have hs : id ∈ (initWorld I N).roster := by simpa [init_roster] using hmem
    have hph := init_phase I N id
    have hhold : tokenHold I.desc (tname id) d ((initWorld I N).st id) =
        floorState I.desc (tname id) ((initWorld I N).st id).typestate d := by
      simp [tokenHold, landFloor, floorState, hph]
    rw [hhold, init_tokens I hG N id hs]
    exact Int.ofNat_le.mpr (floor_le_budget I.desc (tname id) ((initWorld I N).st id).typestate d)
  · intro s d hs _hterm
    exact owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster (fun id _ => init_box I N id)
  · intro _hcrash s d hs _hdead
    rw [owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster (fun id _ => init_box I N id),
      Int.natCast_zero]
    exact Int.natCast_nonneg _
  · intro _hcrash id _hl1
    exact (init_box I N id).2
  · intro _hcrash id _hdead
    exact init_box I N id
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      simp [(init_box I N host).1] at hm
    · intro p hp
      simp [(init_box I N host).2] at hp
  · intro id hid
    rw [init_roster] at hid
    obtain ⟨t, ht, hone, hidc⟩ := core_template I.desc id hG hid
    refine ⟨t, ht, ?_⟩
    simp [hone, hidc]
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      simp [(init_box I N host).1] at hm
    · intro p hp
      simp [(init_box I N host).2] at hp

theorem owed_same_queues (st : InstId → Actor) (id : InstId) (a : Actor)
    (hbox : a.box = (st id).box) (hpark : a.parked = (st id).parked)
    (dst : String) (sender : InstId) (ids : List InstId) :
    owed (fun i => if i = id then a else st i) dst sender ids = owed st dst sender ids := by
  refine owed_mail_eq _ _ _ _ ids ?_
  intro j _
  by_cases hj : j = id
  · simp [hj, hbox, hpark]
  · simp [hj]

theorem aliveCount_set_life (w : World) (id : InstId) (a : Actor) (h : a.life = (w.st id).life)
    (template : String) : aliveCount (setActor w id a) template = aliveCount w template := by
  rw [aliveCount_sum, aliveCount_sum]
  refine sum_congr _ _ w.roster ?_
  intro i _
  unfold aliveBit
  by_cases hi : i = id
  · simp [setActor, hi, h, beq_iff_eq]
  · simp [setActor, hi]

/-- Placement does not read the world, so a life-preserving rewrite keeps it. -/
theorem queueOk_life {D : Description} (w w' : World) (sender host : InstId)
    (_hlife : (w'.st sender).life = (w.st sender).life) :
    queueOk D w sender host ↔ queueOk D w' sender host := by
  rfl

/-- Replacing one actor without touching its life, queues, or token vector.
The new actor's `tokenHold` must still fit in its tokens. -/
theorem occ_set (I : Impl) (w : World) (id : InstId) (a : Actor) (hO : OccInv I w)
    (hlife : a.life = (w.st id).life) (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked)
    (htok : ∀ d, a.tokens d = (w.st id).tokens d)
    (hslack : ∀ d, a.life = .alive →
      (tokenHold I.desc (tname id) d a : Int) ≤ a.tokens d) :
    OccInv I (setActor w id a) := by
  have hst : (setActor w id a).st = fun i => if i = id then a else w.st i := rfl
  have hr : (setActor w id a).roster = w.roster := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact hO.nodup
  · intro i hl
    by_cases hi : i = id
    · rw [hi] at hl ⊢
      rw [setActor_self] at hl
      rw [hlife] at hl
      rw [hr]
      exact hO.aliveIn id hl
    · rw [setActor_other w id i a hi] at hl
      exact hO.aliveIn i hl
  · intro name key g1 g2 ha hb hla hlb
    apply hO.indexed name key g1 g2 (by simpa [setActor] using ha) (by simpa [setActor] using hb)
    · by_cases hg : InstId.peer name key g1 = id
      · rw [hg, setActor_self] at hla
        rw [hg, ← hlife]
        exact hla
      · rw [setActor_other w id _ a hg] at hla
        exact hla
    · by_cases hg : InstId.peer name key g2 = id
      · rw [hg, setActor_self] at hlb
        rw [hg, ← hlife]
        exact hlb
      · rw [setActor_other w id _ a hg] at hlb
        exact hlb
  · intro template ht
    rw [aliveCount_set_life w id a hlife template]
    exact hO.liveOne template ht
  · intro template ht
    rw [aliveCount_set_life w id a hlife template]
    exact hO.livePeer template ht
  · intro i hnin
    by_cases hi : i = id
    · rw [hi] at hnin ⊢
      have hold := hO.offEmpty id hnin
      rw [setActor_self, hbox, hpark]
      exact hold
    · rw [setActor_other w id i a hi]
      exact hO.offEmpty i hnin
  · intro i m hm
    by_cases hi : i = id
    · rw [hi] at hm
      rw [setActor_self, hbox] at hm
      exact hO.sentFrom id m hm
    · rw [setActor_other w id i a hi] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    by_cases hi : i = id
    · rw [hi] at hp
      rw [setActor_self, hpark] at hp
      exact hO.parkFrom id p hp
    · rw [setActor_other w id i a hi] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    by_cases hi : i = id
    · rw [hi] at hp
      rw [setActor_self, hpark] at hp
      exact hO.parkMsg id p hp
    · rw [setActor_other w id i a hi] at hp
      exact hO.parkMsg i p hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key live d hfind
      have hfind0 := findLive_set_life w id a hlife name key
      rw [hfind0] at hfind
      have hbal := hO.balance.1.1 name key live d hfind
      have hq := queuedFromKey_set w id a hbox hpark name key d
      rw [hq]
      by_cases hlive : live = id
      · rw [hlive, setActor_self, htok]
        rw [hlive] at hbal
        exact hbal
      · rw [setActor_other w id live a hlive]
        exact hbal
    · intro name d hl hmem
      have hmem0 : InstId.core name ∈ w.roster := by simpa [setActor] using hmem
      have hl0 : (w.st (.core name)).life = .alive := by
        by_cases hc : InstId.core name = id
        · rw [hc, setActor_self] at hl
          rw [hc, ← hlife]
          exact hl
        · rw [setActor_other w id _ a hc] at hl
          exact hl
      have hbal := hO.balance.1.2 name d hl0 hmem0
      have howed := owed_same_queues w.st id a hbox hpark d (.core name) w.roster
      have heq : owed (setActor w id a).st d (.core name) (setActor w id a).roster =
          owed w.st d (.core name) w.roster := by simpa [setActor] using howed
      rw [heq]
      by_cases hc : InstId.core name = id
      · rw [hc, setActor_self, htok]
        rw [hc] at hbal
        exact hbal
      · rw [setActor_other w id _ a hc]
        exact hbal
    · intro name key d hnone
      have hfind0 := findLive_set_life w id a hlife name key
      rw [hfind0] at hnone
      have hq := queuedFromKey_set w id a hbox hpark name key d
      rw [hq]
      exact hO.balance.2 name key d hnone
  · intro s d hl
    by_cases hs : s = id
    · rw [hs] at hl ⊢
      rw [setActor_self] at hl ⊢
      exact hslack d hl
    · have hl' : (w.st s).life = .alive := by
        rw [setActor_other w id s a hs] at hl
        exact hl
      have hold := hO.slack s d hl'
      rw [setActor_other w id s a hs]
      exact hold
  · intro s d hs hterm
    have howed := owed_same_queues w.st id a hbox hpark d s w.roster
    rw [hr] at hs
    rw [hst, hr, howed]
    exact hO.still s d hs hterm
  · intro hcrash s d hs hdead
    have hc : w.crashed = false := by simpa [setActor] using hcrash
    have hs0 : s ∈ w.roster := by simpa [setActor] using hs
    have hdead0 : (w.st s).life ≠ .alive := by
      by_cases hs' : s = id
      · rw [hs', setActor_self] at hdead
        rw [hs', ← hlife]
        exact hdead
      · rw [setActor_other w id s a hs'] at hdead
        exact hdead
    have howed := owed_same_queues w.st id a hbox hpark d s w.roster
    have heq : owed (setActor w id a).st d s (setActor w id a).roster = owed w.st d s w.roster := by
      simpa [setActor] using howed
    rw [heq]
    exact hO.quiet hc s d hs0 hdead0
  · intro hcrash i hl1
    have hc : w.crashed = false := by simpa [setActor] using hcrash
    by_cases hi : i = id
    · rw [hi] at hl1 ⊢
      rw [setActor_self, hpark]
      exact hO.clear hc id hl1
    · rw [setActor_other w id i a hi]
      exact hO.clear hc i hl1
  · intro hcrash i hdead
    have hc : w.crashed = false := by simpa [setActor] using hcrash
    by_cases hi : i = id
    · rw [hi] at hdead ⊢
      rw [setActor_self] at hdead ⊢
      rw [hlife] at hdead
      rw [hbox, hpark]
      exact hO.deadEmpty hc id hdead
    · rw [setActor_other w id i a hi] at hdead ⊢
      exact hO.deadEmpty hc i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = id
      · rw [hh] at hm ⊢
        rw [setActor_self, hbox] at hm
        exact (hO.sameKey id).1 m hm
      · rw [setActor_other w id host a hh] at hm
        exact (hO.sameKey host).1 m hm
    · intro p hp
      by_cases hh : host = id
      · rw [hh] at hp ⊢
        rw [setActor_self, hpark] at hp
        exact (hO.sameKey id).2 p hp
      · rw [setActor_other w id host a hh] at hp
        exact (hO.sameKey host).2 p hp
  · intro i hi
    exact hO.shaped i (by simpa [hr] using hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = id
      · rw [hh, setActor_self, hbox] at hm
        exact (hO.coreFrom id (hh ▸ hk)).1 m hm
      · rw [setActor_other w id host a hh] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      by_cases hh : host = id
      · rw [hh, setActor_self, hpark] at hp
        exact (hO.coreFrom id (hh ▸ hk)).2 p hp
      · rw [setActor_other w id host a hh] at hp
        exact (hO.coreFrom host hk).2 p hp

theorem proceed_box (a : Actor) (k : Cont) : (proceed a k).box = a.box := by
  unfold proceed
  cases k.rest <;> rfl

theorem proceed_tokens (a : Actor) (k : Cont) (d : String) : (proceed a k).tokens d = a.tokens d := by
  unfold proceed
  cases k.rest <;> rfl

theorem proceed_pending (a : Actor) (k : Cont) (d : String)
    (h : a.phase = .awaitEffect k ∨ a.phase = .awaitPeer k) :
    pending (proceed a k) d ≤ pending a d := by
  unfold proceed pending
  cases hk : k.rest with
  | nil =>
    rcases h with hp | hp <;> simp [contRest, hk, hp, sendsTo]
  | cons _ _ =>
    rcases h with hp | hp <;> simp [contRest, hk, hp]

theorem owed_append_other (st : InstId → Actor) (dstName : String) (s dst : InstId) (msg : Msg)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : dst ∈ roster) (hname : tname dst = dstName)
    (hs : msg.sender ≠ s) :
    owed (fun i => if i = dst then { st dst with box := (st dst).box ++ [msg] } else st i) dstName s roster =
      owed st dstName s roster := by
  have hb : (tname dst == dstName) = true := by simpa [beq_iff_eq] using hname
  have hslot : slot (fun i => if i = dst then { st dst with box := (st dst).box ++ [msg] } else st i)
      dstName s dst = slot st dstName s dst := by
    have hne : (msg.sender == s) = false := by
      cases hbb : msg.sender == s with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hs
    simp [slot, hb, countFrom_append, hne]
    exact hs
  have hrep := owed_replace st dstName s dst { st dst with box := (st dst).box ++ [msg] } roster nodup hmem
  omega

theorem occ_ingress (I : Impl) (w w' : World) (dst : InstId) (label : String) (hO : OccInv I w)
    (h : receiveIngress I w dst label = some w') : OccInv I w' := by
  obtain ⟨hlive, _hopen, htermB, hfloor, hw⟩ := ingress_open I w w' dst label h
  let name := tname dst
  let a := w.st dst
  let msg : Msg :=
    { label := label, sender := dst, callFrom := none, reliable := true, mid := a.nextMid }
  let a' : Actor := { chargeSender a name with box := a.box ++ [msg], nextMid := a.nextMid + 1 }
  have hw' : w' = setActor w dst a' := by simpa [a', a, name, msg] using hw
  rw [hw']
  have hnot : ¬ loneTerminableName I.desc name := by
    intro ⟨t, ht, htv, hsub⟩
    have hb : loneTerminableB I.desc (tname dst) = true := by
      have hsubB : (t.subtree == "") = true := by simpa [beq_iff_eq] using hsub
      simp [loneTerminableB, name, ht, htv, hsubB]
    rw [hb] at htermB
    cases htermB
  have hone : 1 ≤ a.tokens name := by
    have h1 : 1 ≤ budget I.desc (tname dst) (tname dst) -
        debt I.desc (tname dst) a.typestate (tname dst) + pending a (tname dst) + 1 := by
      omega
    exact Nat.le_trans h1 (by simpa [a, name] using hfloor)
  have hcharge := charge_tokens a name hone
  have hpend' (d : String) : pending a' d = pending a d := by
    simp [a', pending, chargeSender, bumpToken]
  have hmem : dst ∈ w.roster := hO.aliveIn dst hlive
  have htok (d : String) : a'.tokens d + (if d = name then 1 else 0) = a.tokens d := by
    by_cases hd : d = name
    · simp [a', hd, hcharge]
    · simp [a', hd, chargeSender, bumpToken]
  let st0 := fun i => if i = dst then { a with box := a.box ++ [msg] } else w.st i
  have hqueues (i : InstId) : (if i = dst then a' else w.st i).box = (st0 i).box ∧
      (if i = dst then a' else w.st i).parked = (st0 i).parked := by
    by_cases hi : i = dst
    · simp [hi, st0, a', chargeSender, bumpToken]
    · simp [hi, st0]
  have hmail (d : String) (sender : InstId) :
      owed (fun i => if i = dst then a' else w.st i) d sender w.roster = owed st0 d sender w.roster := by
    refine owed_mail_eq _ _ _ _ _ ?_
    intro i _
    simpa [st0] using hqueues i
  have hnameB : (tname dst == name) = true := by simp [name]
  have hown (s : InstId) : owed (fun i => if i = dst then a' else w.st i) name s w.roster =
      owed w.st name s w.roster + if s = dst then 1 else 0 := by
    rw [hmail name s]
    by_cases hs : s = dst
    · simp [hs]
      have happ := owed_append_msg w.st name dst dst msg w.roster hO.nodup hmem hnameB rfl
      simpa [st0, hs] using happ
    · simp [hs]
      have hne : msg.sender ≠ s := by
        intro heq
        exact hs heq.symm
      have hother := owed_append_other w.st name s dst msg w.roster hO.nodup hmem (by simp [name]) hne
      simpa [st0] using hother
  have hother (d : String) (hd : d ≠ name) (s : InstId) :
      owed (fun i => if i = dst then a' else w.st i) d s w.roster = owed w.st d s w.roster := by
    rw [hmail d s]
    dsimp [st0]
    have hb : (tname dst == d) = false := by simpa [beq_iff_eq, name] using hd.symm
    have hslot : slot (fun i => if i = dst then { a with box := a.box ++ [msg] } else w.st i) d s dst =
        slot w.st d s dst := by simp [slot, hb]
    have hrep := owed_replace w.st d s dst { a with box := a.box ++ [msg] } w.roster hO.nodup hmem
    rw [hslot] at hrep
    exact Nat.add_right_cancel hrep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hO.nodup
  · intro i hl
    by_cases hi : i = dst
    · rw [hi] at hl ⊢
      rw [setActor_self] at hl
      simp [a', chargeSender, bumpToken] at hl
      exact hO.aliveIn dst hl
    · rw [setActor_other w dst i a' hi] at hl
      exact hO.aliveIn i hl
  · intro template i hi
    rw [actor_ix]
    exact hO.indexed template i (by simpa [setActor] using hi)
  · intro template ht
    rw [aliveCount_set_life w dst a' (by simp [a', a, chargeSender, bumpToken]) template]
    exact hO.liveOne template ht
  · intro template ht
    rw [aliveCount_set_life w dst a' (by simp [a', a, chargeSender, bumpToken]) template]
    exact hO.livePeer template ht
  · intro i hnin
    by_cases hi : i = dst
    · subst hi
      exact absurd hmem hnin
    · rw [setActor_other w dst i a' hi]
      exact hO.offEmpty i hnin
  · intro i m hm
    by_cases hi : i = dst
    · rw [hi] at hm
      rw [setActor_self] at hm
      simp [a', List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hO.sentFrom dst m hm
      · exact hmem
    · rw [setActor_other w dst i a' hi] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    by_cases hi : i = dst
    · rw [hi] at hp
      rw [setActor_self] at hp
      simp [a', chargeSender, bumpToken] at hp
      exact hO.parkFrom dst p hp
    · rw [setActor_other w dst i a' hi] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    by_cases hi : i = dst
    · rw [hi] at hp
      rw [setActor_self] at hp
      simp [a', a, chargeSender, bumpToken] at hp
      exact hO.parkMsg dst p hp
    · rw [setActor_other w dst i a' hi] at hp
      exact hO.parkMsg i p hp
  · intro s d hs
    simp [setActor]
    by_cases hsnd : s = dst
    · rw [hsnd] at hs ⊢
      simp
      by_cases hd : d = name
      · rw [hd]
        simp [name]
        have hown' := hown dst
        simp [name] at hown'
        have htk : a'.tokens (tname dst) + 1 = (w.st dst).tokens (tname dst) := by
          simpa [name, a] using htok (tname dst)
        have hbal := hO.balance dst (tname dst) hs
        rw [hown']
        omega
      · have htk : a'.tokens d = (w.st dst).tokens d := by
          have ht := htok d
          simp [name, a, hd, Nat.add_zero] at ht
          exact ht
        have hoth := hother d hd dst
        have hbal := hO.balance dst d hs
        rw [hoth, htk]
        exact hbal
    · simp [hsnd]
      by_cases hd : d = name
      · rw [hd]
        simp [name]
        have hown' := hown s
        simp [name, hsnd] at hown'
        have hbal := hO.balance s (tname dst) hs
        rw [hown']
        omega
      · have hoth := hother d hd s
        have hbal := hO.balance s d hs
        rw [hoth]
        exact hbal
  · intro s d hs hl
    simp [setActor] at hl ⊢
    by_cases hsnd : s = dst
    · rw [hsnd] at hs hl ⊢
      simp at hl ⊢
      rw [hpend' d]
      have hty : a'.typestate = (w.st dst).typestate := by simp [a', a, chargeSender, bumpToken]
      rw [hty]
      by_cases hd : d = name
      · rw [hd]
        simp [name]
        have htk : a'.tokens (tname dst) + 1 = (w.st dst).tokens (tname dst) := by
          simpa [name, a] using htok (tname dst)
        have hf : floorState I.desc (tname dst) (w.st dst).typestate (tname dst) +
            pending a (tname dst) + 1 ≤ (w.st dst).tokens (tname dst) := by
          simpa [floorState, a, name] using hfloor
        omega
      · have htk : a'.tokens d = (w.st dst).tokens d := by
          have ht := htok d
          simp [name, a, hd, Nat.add_zero] at ht
          exact ht
        have hold := hO.slack dst d hs hlive
        rw [htk]
        exact hold
    · simp [hsnd] at hl ⊢
      exact hO.slack s d hs hl
  · intro s d hs hterm
    simp [setActor]
    by_cases hsnd : s = dst
    · rw [hsnd] at hterm
      exact absurd (by simpa [name] using hterm) hnot
    · have h0 := hO.still s d hs hterm
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        simp [name] at h0 ⊢
        have hown' := hown s
        simp [name, hsnd, Nat.add_zero] at hown'
        rw [hown']
        exact h0
      · have hoth := hother d hd s
        rw [hoth]
        exact h0
  · intro s d hs hdead
    simp [setActor] at hdead ⊢
    by_cases hsnd : s = dst
    · rw [hsnd] at hdead
      simp [a', a, chargeSender, bumpToken, hlive] at hdead
    · simp [hsnd] at hdead ⊢
      have h0 := hO.quiet s d hs hdead
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        simp [name] at h0 ⊢
        have hown' := hown s
        simp [name, hsnd, Nat.add_zero] at hown'
        rw [hown']
        exact h0
      · have hoth := hother d hd s
        rw [hoth]
        exact h0
  · intro i hl1
    simp [setActor]
    by_cases hi : i = dst
    · rw [hi] at hl1 ⊢
      simp [a', a, chargeSender, bumpToken]
      exact hO.clear dst hl1
    · simp [hi]
      exact hO.clear i hl1
  · intro i hdead
    by_cases hi : i = dst
    · rw [hi, setActor_self] at hdead
      simp [a', a, chargeSender, bumpToken, hlive] at hdead
    · rw [setActor_other w dst i a' hi] at hdead ⊢
      exact hO.deadEmpty i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = dst
      · rw [hh] at hm ⊢
        rw [setActor_self] at hm
        simp [a', a, chargeSender, bumpToken, List.mem_append] at hm
        rcases hm with hm | hm
        · have hok := (hO.sameKey dst).1 m hm
          have hl : ((setActor w dst a').st m.sender).life = (w.st m.sender).life := by
            by_cases hs : m.sender = dst
            · rw [hs, setActor_self]
              simp [a', a, chargeSender, bumpToken]
            · rw [setActor_other w dst m.sender a' hs]
          exact (queueOk_life w (setActor w dst a') m.sender dst hl).1 hok
        · have hsend : m.sender = dst := by
            rw [hm]
          refine ⟨?_, ?_⟩
          · unfold keyAgrees
            rw [hsend]
            cases dst <;> simp [peerKey]
          · intro hk
            rw [hsend, setActor_self]
            simp [a', a, chargeSender, bumpToken, hlive]
      · rw [setActor_other w dst host a' hh] at hm
        have hok := (hO.sameKey host).1 m hm
        have hl : ((setActor w dst a').st m.sender).life = (w.st m.sender).life := by
          by_cases hs : m.sender = dst
          · rw [hs, setActor_self]
            simp [a', a, chargeSender, bumpToken]
          · rw [setActor_other w dst m.sender a' hs]
        exact (queueOk_life w (setActor w dst a') m.sender host hl).1 hok
    · intro p hp
      by_cases hh : host = dst
      · rw [hh] at hp ⊢
        rw [setActor_self] at hp
        simp [a', a, chargeSender, bumpToken] at hp
        have hok := (hO.sameKey dst).2 p hp
        have hl : ((setActor w dst a').st p.sender).life = (w.st p.sender).life := by
          by_cases hs : p.sender = dst
          · rw [hs, setActor_self]
            simp [a', a, chargeSender, bumpToken]
          · rw [setActor_other w dst p.sender a' hs]
        exact (queueOk_life w (setActor w dst a') p.sender dst hl).1 hok
      · rw [setActor_other w dst host a' hh] at hp
        have hok := (hO.sameKey host).2 p hp
        have hl : ((setActor w dst a').st p.sender).life = (w.st p.sender).life := by
          by_cases hs : p.sender = dst
          · rw [hs, setActor_self]
            simp [a', a, chargeSender, bumpToken]
          · rw [setActor_other w dst p.sender a' hs]
        exact (queueOk_life w (setActor w dst a') p.sender host hl).1 hok
  · intro i hi
    exact hO.shaped i (by simpa [setActor] using hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = dst
      · rw [hh, setActor_self] at hm
        simp [a', a, chargeSender, bumpToken, List.mem_append] at hm
        rcases hm with hm | hm
        · exact (hO.coreFrom dst (hh ▸ hk)).1 m hm
        · refine Or.inl ?_
          have hsend : m.sender = dst := by rw [hm]
          simpa [hsend] using (hh ▸ hk)
      · rw [setActor_other w dst host a' hh] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      by_cases hh : host = dst
      · rw [hh, setActor_self] at hp
        simp [a', a, chargeSender, bumpToken] at hp
        exact (hO.coreFrom dst (hh ▸ hk)).2 p hp
      · rw [setActor_other w dst host a' hh] at hp
        exact (hO.coreFrom host hk).2 p hp

/-- `finish` only advances a wait. The typestate is already the continuation's
target, and the remaining sends do not grow. -/
theorem occ_finish (I : Impl) (w w' : World) (id : InstId) (hO : OccInv I w) (hS : SemInv I w)
    (h : finishWait I w id = some w') : OccInv I w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    cases h
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hmem := hO.aliveIn id (by rw [proceed_life] at hl; exact hl)
        have hold := hO.slack id d hmem (by rw [proceed_life] at hl; exact hl)
        have hty' := proceed_keeps_ty (w.st id) k hty
        have hpend := proceed_pending (w.st id) k d (Or.inl hph)
        rw [hty']
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Nat.le_trans (Nat.add_le_add_left hpend _) hold)
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    cases hw
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hmem := hO.aliveIn id (by rw [proceed_life] at hl; exact hl)
        have hold := hO.slack id d hmem (by rw [proceed_life] at hl; exact hl)
        have hty' := proceed_keeps_ty (w.st id) k hty
        have hpend := proceed_pending (w.st id) k d (Or.inr hph)
        rw [hty']
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Nat.le_trans (Nat.add_le_add_left hpend _) hold)
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem occ_same (I : Impl) (w w' : World) (hO : OccInv I w) (hst : ∀ i, w'.st i = w.st i)
    (hr : w'.roster = w.roster) (hN : w'.N = w.N) (hix : ∀ n, w'.nextIx n = w.nextIx n) :
    OccInv I w' := by
  have hq : ∀ i ∈ w'.roster, (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked := by
    intro i _
    rw [hst]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact hO.nodup
  · intro id hl
    rw [hst] at hl
    rw [hr]
    exact hO.aliveIn id hl
  · intro template i hi
    rw [hix]
    exact hO.indexed template i (by rw [hr] at hi; exact hi)
  · intro template ht
    have hc : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_congr _ _ w.roster ?_
      intro id _
      unfold aliveBit
      simp [hst]
    rw [hc]
    exact hO.liveOne template ht
  · intro template ht
    have hc : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_congr _ _ w.roster ?_
      intro id _
      unfold aliveBit
      simp [hst]
    rw [hc, hN]
    exact hO.livePeer template ht
  · intro id hnin
    rw [hst]
    exact hO.offEmpty id (by rw [hr] at hnin; exact hnin)
  · intro id m hm
    rw [hst] at hm
    rw [hr]
    exact hO.sentFrom id m hm
  · intro id p hp
    rw [hst] at hp
    rw [hr]
    exact hO.parkFrom id p hp
  · intro id p hp
    rw [hst] at hp
    exact hO.parkMsg id p hp
  · intro s d hs
    have howed := owed_mail_eq w'.st w.st d s w'.roster hq
    rw [howed, hr, hst]
    exact hO.balance s d (by rw [← hr]; exact hs)
  · intro s d hs hl
    rw [hst] at hl ⊢
    exact hO.slack s d (by rw [← hr]; exact hs) hl
  · intro s d hs hterm
    have howed := owed_mail_eq w'.st w.st d s w'.roster hq
    rw [howed, hr]
    exact hO.still s d (by rw [← hr]; exact hs) hterm
  · intro s d hs hdead
    have howed := owed_mail_eq w'.st w.st d s w'.roster hq
    rw [hst] at hdead
    rw [howed, hr]
    exact hO.quiet s d (by rw [← hr]; exact hs) hdead
  · intro id hl1
    rw [hst]
    exact hO.clear id hl1
  · intro id hdead
    rw [hst] at hdead ⊢
    exact hO.deadEmpty id hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst] at hm
      have hmem := (hO.sameKey host).1 m hm
      exact (queueOk_life w w' m.sender host (by rw [hst])).1 hmem
    · intro p hp
      rw [hst] at hp
      have hmem := (hO.sameKey host).2 p hp
      exact (queueOk_life w w' p.sender host (by rw [hst])).1 hmem
  · intro i hi
    exact hO.shaped i (by rw [← hr]; exact hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst] at hm
      exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [hst] at hp
      exact (hO.coreFrom host hk).2 p hp

theorem deliver_roster (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1.roster = w.roster := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact readCells_roster I.desc w id
    · split at h
      · cases h
      · cases h
        exact readCells_roster I.desc w id

theorem deliver_N (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1.N = w.N := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact readCells_N I.desc w id
    · split at h
      · cases h
      · cases h
        exact readCells_N I.desc w id

theorem findSome_name (xs : List Template) (name : String) (t : Template)
    (h : xs.findSome? (fun u => if u.name == name then some u else none) = some t) : t.name = name := by
  induction xs with
  | nil => simp at h
  | cons u us ih =>
    rw [List.findSome?_cons] at h
    by_cases hn : (u.name == name) = true
    · simp only [hn, ite_true] at h
      cases h
      simpa [beq_iff_eq] using hn
    · have hf : (u.name == name) = false := by
        cases hbb : u.name == name <;> simp_all
      simp only [hf, ite_false] at h
      exact ih h

theorem templateOf_name (D : Description) (name : String) (t : Template) (h : templateOf D name = some t) :
    t.name = name := by
  simpa [templateOf] using findSome_name D.templates name t h

theorem find_none_any (xs : List Template) (name : String)
    (h : xs.findSome? (fun u => if u.name == name then some u else none) = none) :
    xs.any (fun u => u.name == name) = false := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    rw [List.findSome?_cons] at h
    by_cases hn : (u.name == name) = true
    · simp [hn] at h
    · have hf : (u.name == name) = false := by
        cases hbb : u.name == name <;> simp_all
      simp only [hf, ite_false] at h
      simp [hf, ih h, List.any]

theorem has_of_none (D : Description) (name : String) (h : templateOf D name = none) :
    hasTemplate D name = false := by
  simpa [templateOf, hasTemplate] using find_none_any D.templates name h

theorem endpoint_lines (D : Description) (hG : GraphOk D) : endpointFails D = [] := by
  have h := hG.struct
  unfold structLines at h
  exact append_nil_right (append_nil_left (append_nil_left (append_nil_left
    (append_nil_left (append_nil_left (append_nil_left (append_nil_left h)))))))

theorem edge_dst_template (D : Description) (h : endpointFails D = []) (e : Edge) (he : e ∈ D.edges) :
    hasTemplate D e.dst = true := by
  unfold endpointFails at h
  have hf := filterMap_mem_none _ D.edges e h he
  by_cases hs : hasTemplate D e.src = false
  · simp [hs] at hf
  · have hs' : hasTemplate D e.src = true := by
      cases hbb : hasTemplate D e.src <;> simp_all
    by_cases hst : stateMem D e.src e.srcState = false
    · simp [hs', hst] at hf
    · have hst' : stateMem D e.src e.srcState = true := by
        cases hbb : stateMem D e.src e.srcState <;> simp_all
      by_cases hd : hasTemplate D e.dst = false
      · simp [hs', hst', hd] at hf
      · cases hbb : hasTemplate D e.dst <;> simp_all

theorem no_edge_unknown (D : Description) (hG : GraphOk D) (dst : String) (h : templateOf D dst = none)
    (e : Edge) (he : e ∈ D.edges) : e.dst ≠ dst := by
  intro heq
  have hhas := edge_dst_template D (endpoint_lines D hG) e he
  rw [heq] at hhas
  rw [has_of_none D dst h] at hhas
  cases hhas

theorem fold_skip_dst (template state dst : String) (per : Edge → Nat) (es : List Edge) (acc : Nat)
    (h : ∀ e ∈ es, e.dst ≠ dst) :
    es.foldl (fun n e => if e.src == template && e.srcState == state && e.dst == dst then n + per e else n) acc =
      acc := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hd : e.dst ≠ dst := h e (List.Mem.head _)
    have hb : (e.dst == dst) = false := by
      cases hbb : e.dst == dst with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hd
    simp only [hb, Bool.and_false]
    exact ih acc (fun e he => h e (List.Mem.tail _ he))

theorem debt_unknown (D : Description) (hG : GraphOk D) (template state dst : String)
    (h : templateOf D dst = none) : debt D template state dst = 0 := by
  cases ht : templateOf D template with
  | none => simp [debt, ht]
  | some src =>
    simp only [debt, ht]
    exact fold_skip_dst template state dst (fun e => perInstance src.multiplicity e.occupancy) D.edges 0
      (fun e he => no_edge_unknown D hG dst h e he)

theorem fold_max_zero {β : Type} (f : β → Nat) (xs : List β) (acc : Nat) (ha : acc = 0)
    (h : ∀ x ∈ xs, f x = 0) : xs.foldl (fun m y => Nat.max m (f y)) acc = 0 := by
  induction xs generalizing acc with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx := h x (List.Mem.head _)
    rw [hx, ha]
    exact ih 0 rfl (fun y hy => h y (List.Mem.tail _ hy))

theorem floor_unknown (D : Description) (hG : GraphOk D) (template state dst : String)
    (h : templateOf D dst = none) : floorState D template state dst = 0 := by
  have hdebt := debt_unknown D hG template state dst h
  have hbud : budget D template dst = 0 := by
    cases ht : templateOf D template with
    | none => simp [budget, ht]
    | some src =>
      simp only [budget, ht]
      exact fold_max_zero (fun st => debt D template st dst) src.states 0 rfl
        (fun st _ => debt_unknown D hG template st dst h)
  simp [floorState, hbud, hdebt]

theorem tr_prog (I : Impl) (hL : LocalOk I) (tr : Transition) (hm : tr ∈ I.transitions) :
    sendsOk I.desc tr.template tr.fromState tr.toState tr.program = true ∧
      effectsOk I.desc tr.template tr.toState tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  unfold transitionOk at hok
  cases ht : templateOf I.desc tr.template with
  | none => simp [ht] at hok
  | some _ =>
    simp only [ht] at hok
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok; replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    have heff := hok.2
    replace hok := hok.1
    rw [Bool.and_eq_true] at hok
    exact ⟨hok.2, heff⟩

theorem sends_named (D : Description) (template fromState toState : String) (prog : List Eff) (dst : String)
    (t : Template) (h : sendsOk D template fromState toState prog = true)
    (ht : templateOf D dst = some t) :
    sendsTo dst prog + floorState D template toState dst ≤ floorState D template fromState dst := by
  have hname := templateOf_name D dst t ht
  unfold sendsOk at h
  have hmem := template_mem D dst t ht
  have hall := (List.all_eq_true _ _).mp h t hmem
  simpa [hname] using hall

theorem sends_outside (D : Description) (template state dst : String) (es : List Eff)
    (hok : effectsOk D template state es = true) (hno : ∀ e ∈ D.edges, e.dst ≠ dst) : sendsTo dst es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | send d label n =>
      simp [effectsOk, sendsTo, Bool.and_eq_true] at hok ⊢
      have ⟨edge, he, hsrc, hss, hdst, _, _, _⟩ :=
        hasEdge_mem D template state d .send .blocking label hok.1
      have hne : d ≠ dst := by
        intro heq
        exact hno edge he (by rw [← heq]; exact hdst)
      have hb : (d == dst) = false := by
        cases hbb : d == dst with
        | false => rfl
        | true => exact absurd ((beq_iff_eq).mp hbb) hne
      simp [hne]
      exact ih hok.2
    | trySend d label n _ _ =>
      simp [effectsOk, sendsTo, Bool.and_eq_true] at hok ⊢
      have ⟨edge, he, _, _, hdst, _, _, _⟩ :=
        hasEdge_mem D template state d .trySend .nonBlocking label hok.1.1
      have hne : d ≠ dst := fun heq => hno edge he (by rw [← heq]; exact hdst)
      have hb : (d == dst) = false := by
        cases hbb : d == dst with
        | false => rfl
        | true => exact absurd ((beq_iff_eq).mp hbb) hne
      simp [hne]
      exact ih hok.2
    | call d label n _ _ =>
      simp [effectsOk, sendsTo, Bool.and_eq_true] at hok ⊢
      have ⟨edge, he, _, _, hdst, _, _, _⟩ :=
        hasEdge_mem D template state d .call .blocking label hok.1
      have hne : d ≠ dst := fun heq => hno edge he (by rw [← heq]; exact hdst)
      have hb : (d == dst) = false := by
        cases hbb : d == dst with
        | false => rfl
        | true => exact absurd ((beq_iff_eq).mp hbb) hne
      simp [hne]
      exact ih hok.2
    | cell _ _ _ =>
      simp [effectsOk, sendsTo, Bool.and_eq_true] at hok
      exact ih hok.2
    | _ =>
      simp [effectsOk, sendsTo] at hok ⊢
      exact ih hok

theorem send_budget (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (tr : Transition)
    (hm : tr ∈ I.transitions) (dst : String) :
    sendsTo dst tr.program + floorState I.desc tr.template tr.toState dst ≤
      floorState I.desc tr.template tr.fromState dst := by
  obtain ⟨hs, he⟩ := tr_prog I hL tr hm
  cases hd : templateOf I.desc dst with
  | some t => exact sends_named I.desc tr.template tr.fromState tr.toState tr.program dst t hs hd
  | none =>
    have hz := sends_outside I.desc tr.template tr.toState dst tr.program he
      (fun e hee => no_edge_unknown I.desc hG dst hd e hee)
    have hto := floor_unknown I.desc hG tr.template tr.toState dst hd
    have hfrom := floor_unknown I.desc hG tr.template tr.fromState dst hd
    simp [hz, hto, hfrom]

theorem deliver_account (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (a : Actor) (m : Msg) (w1 : World) (a1 : Actor) (halive : a.life = .alive) (hph : a.phase = .idle)
    (h : deliver I w id a m = some (w1, a1)) :
    a1.life = a.life ∧ a1.box = a.box ∧ a1.parked = a.parked ∧ (∀ d, a1.tokens d = a.tokens d) ∧
      ∀ d, floorState I.desc (tname id) a1.typestate d + pending a1 d ≤
        floorState I.desc (tname id) a.typestate d := by
  unfold deliver at h
  simp [halive] at h
  cases hf : findTr I (tname id) a.typestate m.label with
  | none =>
    by_cases hc : m.callFrom.isSome = true
    · simp [hf, hc] at h
    · have hc' : m.callFrom.isSome = false := by
        cases hsome : m.callFrom.isSome
        · rfl
        · exact False.elim (hc hsome)
      simp [hf, hc'] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨halive.symm, rfl, rfl, fun _ => rfl, ?_⟩
      intro d
      simp [pending, contRest, hph, sendsTo]
  | some tr =>
    simp only [hf] at h
    by_cases href : m.callFrom.isSome = true ∧ tr.acceptsCall = false
    · rw [ite_eq_left href] at h
      cases h
    · rw [ite_eq_right href] at h
      have hmem := findTr_mem I (tname id) a.typestate m.label tr hf
      have hbud := send_budget I hL hG tr hmem.1
      cases hp : tr.program with
      | nil =>
        simp [hp, List.isEmpty_nil] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨halive.symm, rfl, rfl, fun _ => rfl, ?_⟩
        intro d
        have hb := hbud d
        simp [hp, sendsTo, Nat.zero_add, pending, contRest, hmem.2.1, hmem.2.2.1] at hb ⊢
        exact hb
      | cons e es =>
        simp [hp, List.isEmpty_cons] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨halive.symm, rfl, rfl, fun _ => rfl, ?_⟩
        intro d
        have hb := hbud d
        simp [Nat.add_comm, hmem.2.1, hmem.2.2.1, hp] at hb
        exact hb

theorem occ_prio (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId) (w' : World)
    (hO : OccInv I w) (h : receivePrio I w id = some w') : OccInv I w' := by
  have hready := prio_ready I w id w' h
  unfold receivePrio at h
  cases hp : (w.st id).prio with
  | nil => simp [hp] at h
  | cons m ms =>
    simp only [hp, hready.1, hready.2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        let a0 : Actor := {
          life := .alive, typestate := (w.st id).typestate, phase := .idle, box := (w.st id).box, prio := ms,
          parked := (w.st id).parked, tokens := (w.st id).tokens, nextMid := (w.st id).nextMid,
          waitId := (w.st id).waitId, nextCall := (w.st id).nextCall, oweId := (w.st id).oweId,
          lastCall := (w.st id).lastCall }
        have hacc := deliver_account I hL hG w id a0 m w1 a1 rfl rfl hd
        obtain ⟨hl, hbox, hpark, htok, hfloor⟩ := hacc
        have hO1 := occ_same I w w1 hO (fun i => deliver_st I w id a0 m w1 a1 i hd)
          (deliver_roster I w id a0 m w1 a1 hd) (deliver_N I w id a0 m w1 a1 hd)
          (fun n => deliver_ix I w id a0 m w1 a1 n hd)
        exact occ_set I w1 id a1 hO1
          (by
            rw [deliver_st I w id a0 m w1 a1 id hd, hl]
            simp [a0, hready.1])
          (by rw [deliver_st I w id a0 m w1 a1 id hd, hbox])
          (by rw [deliver_st I w id a0 m w1 a1 id hd, hpark])
          (by
            intro d
            rw [deliver_st I w id a0 m w1 a1 id hd, htok d])
          (by
            intro d hlive
            have hmem := hO.aliveIn id hready.1
            have hold := hO.slack id d hmem hready.1
            have hpend : pending (w.st id) d = 0 := by simp [pending, contRest, hready.2, sendsTo]
            rw [hpend, Nat.add_zero] at hold
            rw [htok d]
            simp [a0]
            exact Nat.le_trans (hfloor d) hold)

theorem slot_drop_box (st : InstId → Actor) (dst : String) (sender id : InstId) (m : Msg) (ms : List Msg)
    (hname : tname id = dst) (hs : m.sender = sender) (hbox : (st id).box = m :: ms) :
    slot (fun i => if i = id then { st id with box := ms } else st i) dst sender id + 1 =
      slot st dst sender id := by
  have hb : (tname id == dst) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb, hbox, countFrom, hs, Nat.add_comm]
  omega

theorem owed_drop_box (st : InstId → Actor) (dst : String) (sender id : InstId) (m : Msg) (ms : List Msg)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster) (hname : tname id = dst)
    (hs : m.sender = sender) (hbox : (st id).box = m :: ms) :
    owed (fun i => if i = id then { st id with box := ms } else st i) dst sender roster + 1 =
      owed st dst sender roster := by
  have hslot := slot_drop_box st dst sender id m ms hname hs hbox
  have hrep := owed_replace st dst sender id { st id with box := ms } roster nodup hmem
  omega

theorem bump_add (a : Actor) (dst d : String) :
    (bumpToken a dst (.ofNat 1)).tokens d = a.tokens d + if d = dst then 1 else 0 := by
  simp [bumpToken]
  by_cases h : d = dst <;> simp [h]

theorem owed_actor (st : InstId → Actor) (id : InstId) (a b : Actor) (dst : String) (sender : InstId)
    (roster : List InstId) (hb : a.box = b.box) (hp : a.parked = b.parked) :
    owed (fun i => if i = id then a else st i) dst sender roster =
      owed (fun i => if i = id then b else st i) dst sender roster := by
  refine owed_mail_eq _ _ _ _ roster ?_
  intro j _
  by_cases hj : j = id
  · simp [hj, hb, hp]
  · simp [hj]

theorem slot_keep_box (st : InstId → Actor) (dst : String) (sender id : InstId) (m : Msg) (ms : List Msg)
    (hname : tname id = dst) (hs : m.sender ≠ sender) (hbox : (st id).box = m :: ms) :
    slot (fun i => if i = id then { st id with box := ms } else st i) dst sender id =
      slot st dst sender id := by
  have hb : (tname id == dst) = true := by simpa [beq_iff_eq] using hname
  have hne : (m.sender == sender) = false := by
    cases hbb : m.sender == sender with
    | false => rfl
    | true => exact absurd ((beq_iff_eq).mp hbb) hs
  simp [slot, hb, hbox, countFrom, hne]
  exact hs

theorem owed_keep_box (st : InstId → Actor) (dst : String) (sender id : InstId) (m : Msg) (ms : List Msg)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster) (hname : tname id = dst)
    (hs : m.sender ≠ sender) (hbox : (st id).box = m :: ms) :
    owed (fun i => if i = id then { st id with box := ms } else st i) dst sender roster =
      owed st dst sender roster := by
  have hslot := slot_keep_box st dst sender id m ms hname hs hbox
  have hrep := owed_replace st dst sender id { st id with box := ms } roster nodup hmem
  omega

theorem owed_bump (st : InstId → Actor) (sender : InstId) (tmpl dst : String) (s : InstId)
    (roster : List InstId) :
    owed (fun i => if i = sender then bumpToken (st sender) tmpl (.ofNat 1) else st i) dst s roster =
      owed st dst s roster := by
  refine owed_mail_eq _ _ _ _ roster ?_
  intro j _
  by_cases hj : j = sender
  · simp [hj, bumpToken]
  · simp [hj]

theorem consume_pick {β : Type} (get : Actor → β)
    (hB : ∀ a tmpl, get (bumpToken a tmpl (.ofNat 1)) = get a)
    (w w1 : World) (id sender : InstId) (a1 : Actor) (s : InstId) (hst : ∀ i, w1.st i = w.st i) :
    get ((creditSender (setActor w1 id a1) (tname id) sender).st s) =
      if s = id then get a1 else get (w.st s) := by
  by_cases hs : s = sender
  · rw [hs, creditSender, setActor_self, hB]
    by_cases hid : sender = id
    · rw [hid, setActor_self]
      simp
    · rw [setActor_other w1 id sender a1 hid, hst]
      simp [hid]
  · rw [creditSender, setActor_other (setActor w1 id a1) sender s _ hs]
    by_cases hid : s = id
    · rw [hid, setActor_self]
      simp
    · rw [setActor_other w1 id s a1 hid, hst]
      simp [hid]

theorem consume_tokens (w w1 : World) (id sender : InstId) (a1 : Actor) (s : InstId) (d : String)
    (hst : ∀ i, w1.st i = w.st i) (htok : ∀ d, a1.tokens d = (w.st id).tokens d) :
    ((creditSender (setActor w1 id a1) (tname id) sender).st s).tokens d =
      (w.st s).tokens d + if s = sender then if d = tname id then 1 else 0 else 0 := by
  by_cases hs : s = sender
  · rw [hs, creditSender, setActor_self, bump_add]
    by_cases hid : sender = id
    · rw [hid, setActor_self, htok]
      simp
    · rw [setActor_other w1 id sender a1 hid, hst]
      simp
  · rw [creditSender, setActor_other (setActor w1 id a1) sender s _ hs]
    by_cases hid : s = id
    · have hne : id ≠ sender := fun heq => hs (hid.trans heq)
      rw [hid, setActor_self, htok, if_neg hne, Nat.add_zero]
    · rw [setActor_other w1 id s a1 hid, hst, if_neg hs, Nat.add_zero]

/-- Install `a1` for `id` and return one token to `sender`. `a1` keeps life and
tokens. At `tname id` it owes `sender` one message less; every other account is
unchanged. The new floor plus the new continuation fit in the old tokens. -/
theorem occ_consume (I : Impl) (w w1 : World) (id sender : InstId) (a1 : Actor) (hO : OccInv I w)
    (hst : ∀ i, w1.st i = w.st i) (hr : w1.roster = w.roster) (hN : w1.N = w.N)
    (hix : ∀ n, w1.nextIx n = w.nextIx n) (hlife : a1.life = (w.st id).life)
    (htok : ∀ d, a1.tokens d = (w.st id).tokens d) (hmem : id ∈ w.roster) (hsend : sender ∈ w.roster)
    (hown : ∀ s, owed (fun i => if i = id then a1 else w.st i) (tname id) s w.roster +
        (if s = sender then 1 else 0) = owed w.st (tname id) s w.roster)
    (hother : ∀ d, d ≠ tname id → ∀ s,
      owed (fun i => if i = id then a1 else w.st i) d s w.roster = owed w.st d s w.roster)
    (hfloor : ∀ d, floorState I.desc (tname id) a1.typestate d + pending a1 d ≤
      floorState I.desc (tname id) (w.st id).typestate d + pending (w.st id) d)
    (hboxFrom : ∀ m ∈ a1.box, m.sender ∈ w.roster)
    (hparkFrom : ∀ p ∈ a1.parked, p.sender ∈ w.roster)
    (hparkMsg : ∀ p ∈ a1.parked, p.sender = p.msg.sender)
    (hclear : l1 I.desc (tname id) = true → a1.parked = [])
    (hkeyB : ∀ m ∈ a1.box, queueOk w m.sender id)
    (hkeyP : ∀ p ∈ a1.parked, queueOk w p.sender id)
    (hdeadQ : a1.life ≠ .alive → a1.box = [] ∧ a1.parked = [])
    (hfromB : peerKey id = none → ∀ m ∈ a1.box,
      peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false)
    (hfromP : peerKey id = none → ∀ p ∈ a1.parked,
      peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false) :
    OccInv I (creditSender (setActor w1 id a1) (tname id) sender) := by
  let wF := creditSender (setActor w1 id a1) (tname id) sender
  suffices OccInv I wF by simpa [wF] using this
  have hrost : wF.roster = w.roster := by simp [wF, creditSender, setActor, hr]
  have hNf : wF.N = w.N := by simp [wF, creditSender, setActor, hN]
  have hixf : ∀ n, wF.nextIx n = w.nextIx n := by
    intro n; simp [wF, creditSender, setActor, hix]
  have hlifeF : ∀ s, (wF.st s).life = (w.st s).life := by
    intro s
    rw [consume_pick (·.life) (by intro a tmpl; simp [bumpToken]) w w1 id sender a1 s hst]
    by_cases hid : s = id <;> simp [hid, hlife]
  have hboxF : ∀ s, (wF.st s).box = if s = id then a1.box else (w.st s).box :=
    fun s => consume_pick (·.box) (by intro a tmpl; simp [bumpToken]) w w1 id sender a1 s hst
  have hparkF : ∀ s, (wF.st s).parked = if s = id then a1.parked else (w.st s).parked :=
    fun s => consume_pick (·.parked) (by intro a tmpl; simp [bumpToken]) w w1 id sender a1 s hst
  have htyF : ∀ s, (wF.st s).typestate = if s = id then a1.typestate else (w.st s).typestate :=
    fun s => consume_pick (·.typestate) (by intro a tmpl; simp [bumpToken]) w w1 id sender a1 s hst
  have hphF : ∀ s, (wF.st s).phase = if s = id then a1.phase else (w.st s).phase :=
    fun s => consume_pick (·.phase) (by intro a tmpl; simp [bumpToken]) w w1 id sender a1 s hst
  have howed : ∀ d s, owed wF.st d s w.roster =
      owed (fun i => if i = id then a1 else w.st i) d s w.roster := by
    intro d s
    have hpre : owed (setActor w1 id a1).st d s w.roster =
        owed (fun i => if i = id then a1 else w.st i) d s w.roster := by
      refine owed_mail_eq _ _ _ _ w.roster ?_
      intro j hj
      by_cases hjid : j = id
      · simp [hjid, setActor_self]
      · rw [setActor_other w1 id j a1 hjid, hst]
        simp [hjid]
    have hcred := owed_bump (setActor w1 id a1).st sender (tname id) d s w.roster
    simp only [wF, creditSender, setActor]
    exact hcred.trans hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrost]; exact hO.nodup
  · intro s hl
    rw [hlifeF] at hl
    rw [hrost]
    exact hO.aliveIn s hl
  · intro template i hi
    rw [hixf]
    exact hO.indexed template i (by rw [hrost] at hi; exact hi)
  · intro template ht
    have hc : aliveCount wF template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hrost]
      refine sum_congr _ _ w.roster ?_
      intro s _
      unfold aliveBit
      simp [hlifeF]
    rw [hc]; exact hO.liveOne template ht
  · intro template ht
    have hc : aliveCount wF template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hrost]
      refine sum_congr _ _ w.roster ?_
      intro s _
      unfold aliveBit
      simp [hlifeF]
    rw [hc, hNf]; exact hO.livePeer template ht
  · intro s hnin
    have hnin' : s ∉ w.roster := by rw [hrost] at hnin; exact hnin
    have hold := hO.offEmpty s hnin'
    have hne : s ≠ id := fun heq => hnin' (by rw [heq]; exact hmem)
    rw [hboxF, hparkF, if_neg hne, if_neg hne]
    exact hold
  · intro s m hm
    rw [hboxF] at hm
    by_cases hs : s = id
    · simp [hs] at hm
      rw [hrost]
      exact hboxFrom m hm
    · simp [hs] at hm
      rw [hrost]
      exact hO.sentFrom s m hm
  · intro s p hp
    rw [hparkF] at hp
    by_cases hs : s = id
    · simp [hs] at hp
      rw [hrost]
      exact hparkFrom p hp
    · simp [hs] at hp
      rw [hrost]
      exact hO.parkFrom s p hp
  · intro s p hp
    rw [hparkF] at hp
    by_cases hs : s = id
    · simp [hs] at hp
      exact hparkMsg p hp
    · simp [hs] at hp
      exact hO.parkMsg s p hp
  · intro s d hs
    rw [hrost] at hs ⊢
    have htokF := consume_tokens w w1 id sender a1 s d hst htok
    rw [howed, htokF]
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      by_cases hd : d = tname id
      · subst hd
        simp
        have hown' := hown sender
        simp at hown'
        have hbal := hO.balance sender (tname id) hs
        omega
      · simp [hd]
        have hother' := hother d hd sender
        have hbal := hO.balance sender d hs
        omega
    · by_cases hd : d = tname id
      · subst hd
        simp [hss]
        have hown' := hown s
        simp [hss] at hown'
        have hbal := hO.balance s (tname id) hs
        omega
      · simp [hss, hd]
        have hother' := hother d hd s
        have hbal := hO.balance s d hs
        omega
  · intro s d hs hl
    rw [hrost] at hs
    rw [hlifeF] at hl
    have hold := hO.slack s d hs hl
    have htokF := consume_tokens w w1 id sender a1 s d hst htok
    rw [htokF]
    by_cases hid : s = id
    · rw [hid] at hold ⊢
      have hph : (wF.st id).phase = a1.phase := by rw [hphF]; simp
      have hty : (wF.st id).typestate = a1.typestate := by rw [htyF]; simp
      have hpendEq : pending (wF.st id) d = pending a1 d := by simp [pending, hph]
      have hfloorEq : floorState I.desc (tname id) (wF.st id).typestate d =
          floorState I.desc (tname id) a1.typestate d := by rw [hty]
      rw [hpendEq, hfloorEq]
      have hfl := hfloor d
      omega
    · have hph : (wF.st s).phase = (w.st s).phase := by rw [hphF]; simp [hid]
      have hty : (wF.st s).typestate = (w.st s).typestate := by rw [htyF]; simp [hid]
      have hpendEq : pending (wF.st s) d = pending (w.st s) d := by simp [pending, hph]
      have hfloorEq : floorState I.desc (tname s) (wF.st s).typestate d =
          floorState I.desc (tname s) (w.st s).typestate d := by rw [hty]
      rw [hpendEq, hfloorEq]
      by_cases hss : s = sender
      · have hswap : sender = s := hss.symm
        subst hswap
        simp
        omega
      · simp [hss]
        omega
  · intro s d hs hterm
    rw [hrost] at hs ⊢
    have h0 := hO.still s d hs hterm
    rw [howed]
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      by_cases hd : d = tname id
      · subst hd
        have hown' := hown sender
        simp at hown'
        omega
      · rw [hother d hd sender, h0]
    · by_cases hd : d = tname id
      · subst hd
        have hown' := hown s
        simp [hss] at hown'
        rw [hown', h0]
      · rw [hother d hd s, h0]
  · intro s d hs hdead
    rw [hrost] at hs ⊢
    rw [hlifeF] at hdead
    have h0 := hO.quiet s d hs hdead
    rw [howed]
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      by_cases hd : d = tname id
      · subst hd
        have hown' := hown sender
        simp at hown'
        omega
      · rw [hother d hd sender]; exact h0
    · by_cases hd : d = tname id
      · subst hd
        have hown' := hown s
        simp [hss] at hown'
        rw [hown']; exact h0
      · rw [hother d hd s]; exact h0
  · intro s hl1
    by_cases hs : s = id
    · rw [hs] at hl1 ⊢
      rw [hparkF id]
      simp
      exact hclear hl1
    · rw [hparkF, if_neg hs]
      exact hO.clear s hl1
  · intro i hdead
    have hdead0 : (w.st i).life ≠ .alive := by rw [← hlifeF i]; exact hdead
    by_cases hi : i = id
    · rw [hi] at hdead ⊢
      rw [hboxF, hparkF]
      simp
      exact hdeadQ (by
        rw [hlife, ← hlifeF id]
        exact hdead)
    · rw [hboxF, hparkF, if_neg hi, if_neg hi]
      exact hO.deadEmpty i hdead0
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hboxF] at hm
      by_cases hh : host = id
      · simp [hh] at hm ⊢
        have hok := hkeyB m hm
        exact (queueOk_life w wF m.sender id (hlifeF m.sender)).1 hok
      · simp [hh] at hm
        have hok := (hO.sameKey host).1 m hm
        exact (queueOk_life w wF m.sender host (hlifeF m.sender)).1 hok
    · intro p hp
      rw [hparkF] at hp
      by_cases hh : host = id
      · simp [hh] at hp ⊢
        have hok := hkeyP p hp
        exact (queueOk_life w wF p.sender id (hlifeF p.sender)).1 hok
      · simp [hh] at hp
        have hok := (hO.sameKey host).2 p hp
        exact (queueOk_life w wF p.sender host (hlifeF p.sender)).1 hok
  · intro i hi
    exact hO.shaped i (by rw [hrost] at hi; exact hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hboxF] at hm
      by_cases hh : host = id
      · simp [hh] at hm
        exact hfromB (hh ▸ hk) m hm
      · simp [hh] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [hparkF] at hp
      by_cases hh : host = id
      · simp [hh] at hp
        exact hfromP (hh ▸ hk) p hp
      · simp [hh] at hp
        exact (hO.coreFrom host hk).2 p hp

theorem owed_off (st : InstId → Actor) (id : InstId) (a : Actor) (dst : String) (sender : InstId)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster) (hname : tname id ≠ dst) :
    owed (fun i => if i = id then a else st i) dst sender roster = owed st dst sender roster := by
  have hb : (tname id == dst) = false := by
    cases hbb : tname id == dst with
    | false => rfl
    | true => exact absurd ((beq_iff_eq).mp hbb) hname
  have hslot : slot (fun i => if i = id then a else st i) dst sender id = slot st dst sender id := by
    simp [slot, hb]
  have hrep := owed_replace st dst sender id a roster nodup hmem
  omega

theorem resume_pending (a : Actor) (isCall : Bool) (dst : InstId) (d : String) (hc : contTy a) :
    pending (resumeSender a isCall dst) d ≤ pending a d := by
  cases h : a.phase with
  | parked _ _ k =>
    have hty : a.typestate = k.toState := by simpa [contTy, h] using hc
    cases isCall <;> cases hk : k.rest <;>
      simp [resumeSender, h, proceed, pending, contRest, hk, hty]
  | idle => simp [resumeSender, h]
  | run k => simp [resumeSender, h]
  | awaitReply _ _ => simp [resumeSender, h]
  | awaitEffect _ => simp [resumeSender, h]
  | awaitPeer _ => simp [resumeSender, h]
  | crashed => simp [resumeSender, h]

theorem resume_box (a : Actor) (isCall : Bool) (dst : InstId) : (resumeSender a isCall dst).box = a.box := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases isCall with
    | true => simp [resumeSender, hph]
    | false =>
      cases hk : k.rest <;> simp [resumeSender, hph, proceed, hk]
  | idle => simp [resumeSender, hph]
  | run k => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem resume_park (a : Actor) (isCall : Bool) (dst : InstId) :
    (resumeSender a isCall dst).parked = a.parked := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases isCall with
    | true => simp [resumeSender, hph]
    | false =>
      cases hk : k.rest <;> simp [resumeSender, hph, proceed, hk]
  | idle => simp [resumeSender, hph]
  | run k => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem resume_tokens (a : Actor) (isCall : Bool) (dst : InstId) (d : String) :
    (resumeSender a isCall dst).tokens d = a.tokens d := by
  cases hph : a.phase with
  | parked _ _ k =>
    cases isCall with
    | true => simp [resumeSender, hph]
    | false =>
      cases hk : k.rest <;> simp [resumeSender, hph, proceed, hk]
  | idle => simp [resumeSender, hph]
  | run k => simp [resumeSender, hph]
  | awaitReply _ _ => simp [resumeSender, hph]
  | awaitEffect _ => simp [resumeSender, hph]
  | awaitPeer _ => simp [resumeSender, hph]
  | crashed => simp [resumeSender, hph]

theorem occ_resume (I : Impl) (w : World) (sender : InstId) (isCall : Bool) (dst : InstId)
    (hO : OccInv I w) (hc : contTy (w.st sender)) :
    OccInv I (setActor w sender (resumeSender (w.st sender) isCall dst)) := by
  let a := resumeSender (w.st sender) isCall dst
  exact occ_set I w sender a hO (by simp [a, resume_keeps (w.st sender) isCall dst hc])
    (by simp [a, resume_box]) (by simp [a, resume_park]) (by intro d; simp [a, resume_tokens]) (by
      intro d hl
      have hl0 : (w.st sender).life = .alive := by
        have hlife := (resume_keeps (w.st sender) isCall dst hc).2
        rw [← hlife]
        simpa [a] using hl
      have hmem := hO.aliveIn sender hl0
      have hold := hO.slack sender d hmem hl0
      have hty := (resume_keeps (w.st sender) isCall dst hc).1
      have hpend := resume_pending (w.st sender) isCall dst d hc
      have htok := resume_tokens (w.st sender) isCall dst d
      simp [a] at hty hpend htok ⊢
      rw [hty, htok]
      omega)

theorem occ_bulk_box (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (m : Msg) (ms : List Msg) (w1 : World) (a1 : Actor) (hO : OccInv I w)
    (hbox : (w.st id).box = m :: ms) (hpark : (w.st id).parked = [])
    (halive : (w.st id).life = .alive) (hidle : (w.st id).phase = .idle)
    (hd : deliver I w id {(w.st id) with box := ms} m = some (w1, a1)) :
    OccInv I (creditSender (setActor w1 id a1) (tname id) m.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with box := ms} m w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  have hmem := hO.aliveIn id halive
  have hsend := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  apply occ_consume I w w1 id m.sender a1 hO
      (fun i => deliver_st I w id _ m w1 a1 i hd)
      (deliver_roster I w id _ m w1 a1 hd) (deliver_N I w id _ m w1 a1 hd)
      (fun n => deliver_ix I w id _ m w1 a1 n hd)
      (by simpa [halive] using hl) (by intro d; simpa [halive] using htokA d) hmem hsend
  · intro s
    by_cases hs : s = m.sender
    · rw [hs]
      have hdrop := owed_drop_box w.st (tname id) m.sender id m ms w.roster hO.nodup hmem rfl rfl hbox
      have hsame := owed_actor w.st id a1 {(w.st id) with box := ms} (tname id) m.sender w.roster
        (by simpa using hb) (by simpa [hpark] using hparkA)
      simp
      rw [hsame]
      exact hdrop
    · have hkeep := owed_keep_box w.st (tname id) s id m ms w.roster hO.nodup hmem rfl (fun h => hs h.symm) hbox
      have hsame := owed_actor w.st id a1 {(w.st id) with box := ms} (tname id) s w.roster
        (by simpa using hb) (by simpa [hpark] using hparkA)
      simp [hs]
      rw [hsame]
      exact hkeep
  · intro d hdne s
    exact owed_off w.st id a1 d s w.roster hO.nodup hmem hdne.symm
  · intro d
    have hpend : pending (w.st id) d = 0 := by simp [pending, contRest, hidle, sendsTo]
    rw [hpend, Nat.add_zero]
    simpa using hfl d
  · intro msg hm
    rw [hb] at hm
    exact hO.sentFrom id msg (by rw [hbox]; exact List.Mem.tail _ hm)
  · intro p hp
    rw [hparkA, hpark] at hp
    cases hp
  · intro p hp
    rw [hparkA, hpark] at hp
    cases hp
  · intro _
    rw [hparkA, hpark]
  · intro msg hm
    rw [hb] at hm
    exact (hO.sameKey id).1 msg (by rw [hbox]; exact List.Mem.tail _ hm)
  · intro p hp
    rw [hparkA, hpark] at hp
    cases hp
  · intro hdead
    exact absurd (by simpa [halive] using hl) hdead
  · intro hk m' hm'
    rw [hb] at hm'
    exact (hO.coreFrom id hk).1 m' (by rw [hbox]; exact List.Mem.tail _ hm')
  · intro hk p hp
    rw [hparkA, hpark] at hp
    cases hp

theorem slot_drop_park (st : InstId → Actor) (dst : String) (sender id : InstId) (p : Parked)
    (ps : List Parked) (hname : tname id = dst) (hs : p.sender = sender)
    (hpark : (st id).parked = p :: ps) :
    slot (fun i => if i = id then { st id with parked := ps } else st i) dst sender id + 1 =
      slot st dst sender id := by
  have hb : (tname id == dst) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb, hpark, countParked, hs, Nat.add_comm]
  omega

theorem owed_drop_park (st : InstId → Actor) (dst : String) (sender id : InstId) (p : Parked)
    (ps : List Parked) (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster)
    (hname : tname id = dst) (hs : p.sender = sender) (hpark : (st id).parked = p :: ps) :
    owed (fun i => if i = id then { st id with parked := ps } else st i) dst sender roster + 1 =
      owed st dst sender roster := by
  have hslot := slot_drop_park st dst sender id p ps hname hs hpark
  have hrep := owed_replace st dst sender id { st id with parked := ps } roster nodup hmem
  omega

theorem slot_keep_park (st : InstId → Actor) (dst : String) (sender id : InstId) (p : Parked)
    (ps : List Parked) (hname : tname id = dst) (hs : p.sender ≠ sender)
    (hpark : (st id).parked = p :: ps) :
    slot (fun i => if i = id then { st id with parked := ps } else st i) dst sender id =
      slot st dst sender id := by
  have hb : (tname id == dst) = true := by simpa [beq_iff_eq] using hname
  have hne : (p.sender == sender) = false := by
    cases hbb : p.sender == sender with
    | false => rfl
    | true => exact absurd ((beq_iff_eq).mp hbb) hs
  simp [slot, hb, hpark, countParked, hne]
  exact hs

theorem owed_keep_park (st : InstId → Actor) (dst : String) (sender id : InstId) (p : Parked)
    (ps : List Parked) (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster)
    (hname : tname id = dst) (hs : p.sender ≠ sender) (hpark : (st id).parked = p :: ps) :
    owed (fun i => if i = id then { st id with parked := ps } else st i) dst sender roster =
      owed st dst sender roster := by
  have hslot := slot_keep_park st dst sender id p ps hname hs hpark
  have hrep := owed_replace st dst sender id { st id with parked := ps } roster nodup hmem
  omega

theorem occ_bulk_park (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (p : Parked) (ps : List Parked) (w1 : World) (a1 : Actor) (hO : OccInv I w)
    (hpark : (w.st id).parked = p :: ps) (hbox : (w.st id).box = [])
    (halive : (w.st id).life = .alive) (hidle : (w.st id).phase = .idle)
    (hsame : p.sender = p.msg.sender)
    (hd : deliver I w id {(w.st id) with parked := ps} p.msg = some (w1, a1)) :
    OccInv I (creditSender (setActor w1 id a1) (tname id) p.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with parked := ps} p.msg w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  have hmem := hO.aliveIn id halive
  have hsend := hO.parkFrom id p (by rw [hpark]; exact List.Mem.head _)
  apply occ_consume I w w1 id p.sender a1 hO
      (fun i => deliver_st I w id _ p.msg w1 a1 i hd)
      (deliver_roster I w id _ p.msg w1 a1 hd) (deliver_N I w id _ p.msg w1 a1 hd)
      (fun n => deliver_ix I w id _ p.msg w1 a1 n hd)
      (by simpa [halive] using hl) (by intro d; simpa [halive] using htokA d) hmem hsend
  · intro s
    by_cases hs : s = p.sender
    · rw [hs]
      have hdrop := owed_drop_park w.st (tname id) p.sender id p ps w.roster hO.nodup hmem rfl rfl hpark
      have hsameO := owed_actor w.st id a1 {(w.st id) with parked := ps} (tname id) p.sender w.roster
        (by simpa [hbox] using hb) (by simpa using hparkA)
      simp
      rw [hsameO]
      exact hdrop
    · have hkeep := owed_keep_park w.st (tname id) s id p ps w.roster hO.nodup hmem rfl
        (fun h => hs h.symm) hpark
      have hsameO := owed_actor w.st id a1 {(w.st id) with parked := ps} (tname id) s w.roster
        (by simpa [hbox] using hb) (by simpa using hparkA)
      simp [hs]
      rw [hsameO]
      exact hkeep
  · intro d hdne s
    exact owed_off w.st id a1 d s w.roster hO.nodup hmem hdne.symm
  · intro d
    have hpend : pending (w.st id) d = 0 := by simp [pending, contRest, hidle, sendsTo]
    rw [hpend, Nat.add_zero]
    simpa using hfl d
  · intro msg hm
    rw [hb, hbox] at hm
    cases hm
  · intro q hq
    rw [hparkA] at hq
    exact hO.parkFrom id q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro q hq
    rw [hparkA] at hq
    exact hO.parkMsg id q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro hl1
    have hempty := hO.clear id hl1
    rw [hpark] at hempty
    cases hempty
  · intro msg hm
    rw [hb, hbox] at hm
    cases hm
  · intro q hq
    rw [hparkA] at hq
    exact (hO.sameKey id).2 q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro hdead
    exact absurd (by simpa [halive] using hl) hdead
  · intro hk m hm
    rw [hb, hbox] at hm
    cases hm
  · intro hk q hq
    rw [hparkA] at hq
    exact (hO.coreFrom id hk).2 q (by rw [hpark]; exact List.Mem.tail _ hq)

theorem slot_admit (st : InstId → Actor) (dst : String) (s id : InstId) (m : Msg) (ms : List Msg)
    (p : Parked) (ps : List Parked) (hname : tname id = dst) (hbox : (st id).box = m :: ms)
    (hpark : (st id).parked = p :: ps) (hmsg : p.sender = p.msg.sender) :
    slot (fun i => if i = id then { st id with box := ms ++ [p.msg], parked := ps } else st i) dst s id +
        (if m.sender = s then 1 else 0) = slot st dst s id := by
  have hb : (tname id == dst) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb, hbox, hpark, countFrom, countParked, countFrom_append, hmsg]
  by_cases hm : m.sender = s <;> by_cases hp : p.sender = s <;> simp [hm, hp] <;> omega

theorem owed_admit (st : InstId → Actor) (dst : String) (s id : InstId) (m : Msg) (ms : List Msg)
    (p : Parked) (ps : List Parked) (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster)
    (hname : tname id = dst) (hbox : (st id).box = m :: ms) (hpark : (st id).parked = p :: ps)
    (hmsg : p.sender = p.msg.sender) :
    owed (fun i => if i = id then { st id with box := ms ++ [p.msg], parked := ps } else st i) dst s roster +
        (if m.sender = s then 1 else 0) = owed st dst s roster := by
  have hslot := slot_admit st dst s id m ms p ps hname hbox hpark hmsg
  have hrep := owed_replace st dst s id { st id with box := ms ++ [p.msg], parked := ps } roster nodup hmem
  omega

theorem occ_bulk_both (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (m : Msg) (ms : List Msg) (p : Parked) (ps : List Parked) (w1 : World) (a1 : Actor) (hO : OccInv I w)
    (hbox : (w.st id).box = m :: ms) (hpark : (w.st id).parked = p :: ps)
    (halive : (w.st id).life = .alive) (hidle : (w.st id).phase = .idle) (hmsg : p.sender = p.msg.sender)
    (hd : deliver I w id {(w.st id) with box := ms} m = some (w1, a1)) :
    OccInv I (creditSender (setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps }) (tname id) m.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with box := ms} m w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
  have hmem := hO.aliveIn id halive
  have hsend := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  apply occ_consume I w w1 id m.sender admitted hO
      (fun i => deliver_st I w id _ m w1 a1 i hd)
      (deliver_roster I w id _ m w1 a1 hd) (deliver_N I w id _ m w1 a1 hd)
      (fun n => deliver_ix I w id _ m w1 a1 n hd)
      (by simpa [admitted, halive] using hl) (by intro d; simpa [admitted, halive] using htokA d) hmem hsend
  · intro s
    have hmodel := owed_admit w.st (tname id) s id m ms p ps w.roster hO.nodup hmem rfl hbox hpark hmsg
    have hsameO := owed_actor w.st id admitted { w.st id with box := ms ++ [p.msg], parked := ps }
      (tname id) s w.roster (by simp [admitted, hb]) (by simp [admitted, hparkA])
    rw [hsameO]
    have hif : (if s = m.sender then 1 else 0) = (if m.sender = s then 1 else 0) := by
      by_cases h : s = m.sender
      · simp [h]
      · have h2 : m.sender ≠ s := fun he => h he.symm
        simp [h, h2]
    rw [hif]
    exact hmodel
  · intro d hdne s
    exact owed_off w.st id admitted d s w.roster hO.nodup hmem hdne.symm
  · intro d
    have hpend : pending (w.st id) d = 0 := by simp [pending, contRest, hidle, sendsTo]
    have hsameP : pending admitted d = pending a1 d := by simp [admitted, pending]
    have hsameT : admitted.typestate = a1.typestate := by simp [admitted]
    rw [hpend, Nat.add_zero, hsameP, hsameT]
    simpa using hfl d
  · intro msg hm
    simp [admitted, hb] at hm
    rcases hm with hm | hm
    · exact hO.sentFrom id msg (by rw [hbox]; exact List.Mem.tail _ hm)
    · rw [hm, ← hmsg]
      exact hO.parkFrom id p (by rw [hpark]; exact List.Mem.head _)
  · intro q hq
    simp [admitted] at hq
    exact hO.parkFrom id q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro q hq
    simp [admitted] at hq
    exact hO.parkMsg id q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro hl1
    have hempty := hO.clear id hl1
    rw [hpark] at hempty
    cases hempty
  · intro msg hm
    simp [admitted, hb] at hm
    rcases hm with hm | hm
    · exact (hO.sameKey id).1 msg (by rw [hbox]; exact List.Mem.tail _ hm)
    · rw [hm, ← hmsg]
      exact (hO.sameKey id).2 p (by rw [hpark]; exact List.Mem.head _)
  · intro q hq
    simp [admitted] at hq
    exact (hO.sameKey id).2 q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro hdead
    exact absurd (by simpa [admitted, halive] using hl) hdead
  · intro hk msg hm
    simp [admitted, hb] at hm
    rcases hm with hm | hm
    · exact (hO.coreFrom id hk).1 msg (by rw [hbox]; exact List.Mem.tail _ hm)
    · have hp : p ∈ (w.st id).parked := by rw [hpark]; exact List.Mem.head _
      simpa [hm, hmsg] using (hO.coreFrom id hk).2 p hp
  · intro hk q hq
    simp [admitted] at hq
    exact (hO.coreFrom id hk).2 q (by rw [hpark]; exact List.Mem.tail _ hq)

theorem occ_bulk (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId) (w' : World)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (h : receiveBulk I w id = some w') :
    OccInv I w' := by
  have hready := receive_ready I w id w' h
  unfold receiveBulk at h
  simp only [hready.1, hready.2] at h
  cases hbox : (w.st id).box with
  | nil =>
    cases hpk : (w.st id).parked with
    | nil => simp [hbox, hpk] at h
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hmsg := hO.parkMsg id p (by rw [hpk]; exact List.Mem.head _)
        have hne : p.sender ≠ id :=
          not_queued w id hM (by simp [notParked, hready.2]) id p (by rw [hpk]; exact List.Mem.head _)
        have hd' : deliver I w id {(w.st id) with parked := ps} p.msg = some (w1, a1) := by
          simpa [hready.1, hready.2, hbox] using hd
        have hO1 := occ_bulk_park I hL hG w id p ps w1 a1 hO hpk hbox hready.1 hready.2 hmsg hd'
        let wC := creditSender (setActor w1 id a1) (tname id) p.sender
        have hph : (wC.st p.sender).phase = (w.st p.sender).phase := by
          rw [(credit_phase (setActor w1 id a1) (tname id) p.sender p.sender).1,
            setActor_other w1 id p.sender a1 hne, deliver_st I w id _ p.msg w1 a1 p.sender hd, hmsg]
        have hty : (wC.st p.sender).typestate = (w.st p.sender).typestate := by
          rw [(credit_keeps_ty (setActor w1 id a1) (tname id) p.sender p.sender).2,
            setActor_other w1 id p.sender a1 hne, deliver_st I w id _ p.msg w1 a1 p.sender hd, hmsg]
        have hc : contTy (wC.st p.sender) := (contTy_match _ _ hph hty).mpr (hS.cont p.sender)
        simpa [wC, hmsg] using occ_resume I wC p.sender p.isCall id hO1 hc
  | cons m ms =>
    cases hpk : (w.st id).parked with
    | nil =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hd' : deliver I w id {(w.st id) with box := ms} m = some (w1, a1) := by
          simpa [hready.1, hready.2, hpk] using hd
        simpa using occ_bulk_box I hL hG w id m ms w1 a1 hO hbox hpk hready.1 hready.2 hd'
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hmsg := hO.parkMsg id p (by rw [hpk]; exact List.Mem.head _)
        have hne : p.sender ≠ id :=
          not_queued w id hM (by simp [notParked, hready.2]) id p (by rw [hpk]; exact List.Mem.head _)
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hd' : deliver I w id {(w.st id) with box := ms} m = some (w1, a1) := by
          simpa [hready.1, hready.2, hpk] using hd
        have hO1 := occ_bulk_both I hL hG w id m ms p ps w1 a1 hO hbox hpk hready.1 hready.2 hmsg hd'
        let wC := creditSender (setActor w1 id admitted) (tname id) m.sender
        have hph : (wC.st p.sender).phase = (w.st p.sender).phase := by
          by_cases hs : p.sender = m.sender
          · rw [hs, (credit_phase (setActor w1 id admitted) (tname id) m.sender m.sender).1,
              setActor_other w1 id m.sender admitted (by rw [← hs]; exact hne),
              deliver_st I w id _ m w1 a1 m.sender hd]
          · rw [(credit_phase (setActor w1 id admitted) (tname id) m.sender p.sender).1,
              setActor_other w1 id p.sender admitted hne, deliver_st I w id _ m w1 a1 p.sender hd]
        have hty : (wC.st p.sender).typestate = (w.st p.sender).typestate := by
          by_cases hs : p.sender = m.sender
          · rw [hs, (credit_keeps_ty (setActor w1 id admitted) (tname id) m.sender m.sender).2,
              setActor_other w1 id m.sender admitted (by rw [← hs]; exact hne),
              deliver_st I w id _ m w1 a1 m.sender hd]
          · rw [(credit_keeps_ty (setActor w1 id admitted) (tname id) m.sender p.sender).2,
              setActor_other w1 id p.sender admitted hne, deliver_st I w id _ m w1 a1 p.sender hd]
        have hc : contTy (wC.st p.sender) := (contTy_match _ _ hph hty).mpr (hS.cont p.sender)
        simpa [wC, admitted] using occ_resume I wC p.sender p.isCall id hO1 hc

/-- A life-preserving rewrite whose new `tokenHold` is no larger than the old one
keeps the account. The caller supplies the hold; typestate may change. -/
theorem occ_keep (I : Impl) (w : World) (id : InstId) (a : Actor) (hO : OccInv I w)
    (hlife : a.life = (w.st id).life) (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked)
    (htok : ∀ d, a.tokens d = (w.st id).tokens d)
    (hhold : ∀ d, a.life = .alive →
      (tokenHold I.desc (tname id) d a : Int) ≤ (tokenHold I.desc (tname id) d (w.st id) : Int)) :
    OccInv I (setActor w id a) := by
  apply occ_set I w id a hO hlife hbox hpark htok
  intro d hl
  have hl0 : (w.st id).life = .alive := by rw [← hlife]; exact hl
  exact le_trans (hhold d hl) (by rw [htok d]; exact hO.slack id d hl0)

theorem proceed_tail (a : Actor) (k : Cont) (d : String) (hty : a.typestate = k.toState)
    (hrest : contRest a.phase = k.rest) :
    pending (proceed a (afterHead k)) d ≤ pending a d ∧ (proceed a (afterHead k)).typestate = a.typestate := by
  simp only [afterHead]
  constructor
  · unfold proceed pending
    cases h : k.rest.tail with
    | nil =>
      cases hk : k.rest with
      | nil => simp [contRest, hk, hrest, sendsTo]
      | cons e es =>
        cases es with
        | nil =>
          simp [contRest, hk, hrest, sendsTo]
        | cons _ _ =>
          simp [hk] at h
    | cons e es =>
      rw [hrest]
      cases hk : k.rest with
      | nil =>
        simp [hk, List.tail_nil] at h
      | cons e0 es0 =>
        simp [hk, List.tail_cons] at h
        simp [h, contRest]
        exact sends_drop_le d e0 (e :: es)
  · unfold proceed
    cases h : k.rest.tail <;> simp [h, hty]

theorem occ_cell_st (w : World) (dst label : String) (c : Cell) (i : InstId) :
    (setCell w dst label c).st i = w.st i := by
  simp [setCell]

theorem occ_cell_roster (w : World) (dst label : String) (c : Cell) :
    (setCell w dst label c).roster = w.roster ∧ (setCell w dst label c).N = w.N := by
  simp [setCell]

theorem occ_cell_ix (w : World) (dst label : String) (c : Cell) (n : String) :
    (setCell w dst label c).nextIx n = w.nextIx n := by
  simp [setCell]

theorem occ_try_wake (I : Impl) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (hO : OccInv I w) : OccInv I (tryWake I.desc w dstId label writer) := by
  unfold tryWake
  extract_lets
  split
  · let wake : Msg :=
      { label := label, sender := writer, callFrom := none, reliable := false,
        mid := (w.st dstId).nextMid }
    let armed : Actor :=
      { (w.st dstId) with prio := upsertPrio (w.st dstId).prio wake, nextMid := (w.st dstId).nextMid + 1 }
    exact occ_keep I w dstId armed hO rfl rfl rfl (fun _ => rfl) rfl (fun _ => Nat.le_refl _)
  · exact hO

theorem occ_wakes (I : Impl) (ids : List InstId) (w : World) (dst label : String) (writer : InstId)
    (hO : OccInv I w) :
    OccInv I ((ids.foldl (fun w id => tryWake I.desc w id label writer) w)) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons id ids ih =>
    rw [List.foldl_cons]
    exact ih _ (occ_try_wake I w id label writer hO)

theorem occ_advance (I : Impl) (w : World) (id : InstId) (k : Cont) (hO : OccInv I w)
    (hty : (w.st id).typestate = k.toState) (hph : (w.st id).phase = .run k) :
    OccInv I (setActor w id (proceed (w.st id) (afterHead k))) := by
  apply occ_keep I w id (proceed (w.st id) (afterHead k)) hO (proceed_life _ _) (proceed_box _ _)
    (proceed_parked _ _) (proceed_tokens _ _)
  · exact (proceed_tail (w.st id) k "" hty (by simp [contRest, hph])).2
  · intro d
    exact (proceed_tail (w.st id) k d hty (by simp [contRest, hph])).1

theorem occ_reply (I : Impl) (w : World) (id : InstId) (k : Cont) (hO : OccInv I w) (hS : SemInv I w)
    (hph : (w.st id).phase = .run k) : OccInv I (performReply w id k) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
  unfold performReply
  cases hr : k.replyTo with
  | none =>
    simpa [hr] using occ_advance I w id k hO hty hph
  | some caller =>
    simp [hr]
    cases hcall : (w.st caller).phase with
    | awaitReply dst ck =>
      by_cases hd : dst = id
      · by_cases howe : (w.st id).oweId = some (w.st caller).waitId
        · have htyC : (w.st caller).typestate = ck.toState := by
            simpa [contTy, hcall] using hS.cont caller
          have hO1 := occ_keep I w caller (finishCall (w.st caller) ck .reply) hO
            (finishCall_life _ _ _)
            (by cases hk : ck.rest <;> simp [finishCall, proceed, hk])
            (by cases hk : ck.rest <;> simp [finishCall, proceed, hk])
            (by intro d; cases hk : ck.rest <;> simp [finishCall, proceed, hk])
            (by cases hk : ck.rest <;> simp [finishCall, proceed, hk, htyC])
            (by
              intro d
              cases hk : ck.rest <;> simp [finishCall, proceed, pending, contRest, hcall, hk])
          have hne : caller ≠ id := by
            intro hc
            rw [hc] at hcall
            rw [hcall] at hph
            cases hph
          have hstep := occ_advance I (setActor w caller (finishCall (w.st caller) ck .reply)) id k hO1
            (by rw [setActor_other w caller id _ (fun h => hne h.symm), hty])
            (by rw [setActor_other w caller id _ (fun h => hne h.symm), hph])
          simpa [hd, howe] using hstep
        · simpa [hd, howe] using occ_advance I w id k hO hty hph
      · simpa [hd] using occ_advance I w id k hO hty hph
    | idle => exact occ_advance I w id k hO hty hph
    | run _ => exact occ_advance I w id k hO hty hph
    | parked _ _ _ => exact occ_advance I w id k hO hty hph
    | awaitEffect _ => exact occ_advance I w id k hO hty hph
    | awaitPeer _ => exact occ_advance I w id k hO hty hph
    | crashed => exact occ_advance I w id k hO hty hph

theorem charge_skip (a : Actor) (dst d : String) (h : d ≠ dst) :
    (chargeSender a dst).tokens d = a.tokens d := by
  simp [chargeSender, bumpToken, h]

theorem charge_at (a : Actor) (dst : String) (h : 1 ≤ a.tokens dst) :
    (chargeSender a dst).tokens dst + 1 = a.tokens dst :=
  charge_tokens a dst h

/-- Spend one token at `name` and add one owed message for `sender`.
Every other account is unchanged. The sender is not a terminable template:
a terminable actor is not allowed to put a bulk message in flight. -/
theorem occ_pay (I : Impl) (w w' : World) (sender : InstId) (name : String) (hO : OccInv I w)
    (hrost : w'.roster = w.roster) (hN : w'.N = w.N) (hix : ∀ n, w'.nextIx n = w.nextIx n)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hSty : (w'.st sender).typestate = (w.st sender).typestate)
    (htyO : ∀ i, i ≠ sender → (w'.st i).typestate = (w.st i).typestate)
    (hSph : ∀ d, pending (w'.st sender) d + (if d = name then 1 else 0) ≤ pending (w.st sender) d)
    (hphO : ∀ i, i ≠ sender → (w'.st i).phase = (w.st i).phase)
    (htok : ∀ d, (w'.st sender).tokens d + (if d = name then 1 else 0) = (w.st sender).tokens d)
    (htokO : ∀ i, i ≠ sender → ∀ d, (w'.st i).tokens d = (w.st i).tokens d)
    (hown : ∀ s, owed w'.st name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s, owed w'.st d s w.roster = owed w.st d s w.roster)
    (hbox : ∀ i m, m ∈ (w'.st i).box → m.sender ∈ w.roster)
    (hpark : ∀ i p, p ∈ (w'.st i).parked → p.sender ∈ w.roster)
    (hpm : ∀ i p, p ∈ (w'.st i).parked → p.sender = p.msg.sender)
    (hclear : ∀ i, l1 I.desc (tname i) = true → (w'.st i).parked = [])
    (hoff : ∀ i, i ∉ w.roster → (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked)
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hdeadE : ∀ i, (w'.st i).life ≠ .alive → (w'.st i).box = [] ∧ (w'.st i).parked = [])
    (hkey : ∀ host,
      (∀ m ∈ (w'.st host).box, queueOk w m.sender host) ∧
      (∀ p ∈ (w'.st host).parked, queueOk w p.sender host))
    (hfrom : ∀ host, peerKey host = none →
      (∀ m ∈ (w'.st host).box,
        peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false) ∧
      (∀ p ∈ (w'.st host).parked,
        peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false)) :
    OccInv I w' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrost]; exact hO.nodup
  · intro i hl
    rw [hlife] at hl
    rw [hrost]
    exact hO.aliveIn i hl
  · intro template i hi
    rw [hix]
    exact hO.indexed template i (by rw [hrost] at hi; exact hi)
  · intro template ht
    have hc : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hrost]
      refine sum_congr _ _ w.roster ?_
      intro i _
      unfold aliveBit
      simp [hlife]
    rw [hc]; exact hO.liveOne template ht
  · intro template ht
    have hc : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hrost]
      refine sum_congr _ _ w.roster ?_
      intro i _
      unfold aliveBit
      simp [hlife]
    rw [hc, hN]; exact hO.livePeer template ht
  · intro i hnin
    have hnin' : i ∉ w.roster := by rw [hrost] at hnin; exact hnin
    have hold := hO.offEmpty i hnin'
    have hq := hoff i hnin'
    rw [hq.1, hq.2]
    exact hold
  · intro i m hm
    rw [hrost]
    exact hbox i m hm
  · intro i p hp
    rw [hrost]
    exact hpark i p hp
  · intro i p hp
    exact hpm i p hp
  · intro s d hs
    rw [hrost] at hs ⊢
    by_cases hd : d = name
    · rw [hd]
      rw [hown s]
      by_cases hss : s = sender
      · have hswap : sender = s := hss.symm
        subst hswap
        simp
        have htk := htok name
        simp at htk
        have hbal := hO.balance sender name hs
        omega
      · simp [hss]
        have htk := htokO s hss name
        have hbal := hO.balance s name hs
        omega
    · rw [hother d hd s]
      by_cases hss : s = sender
      · have hswap : sender = s := hss.symm
        subst hswap
        have htk := htok d
        simp [hd] at htk
        have hbal := hO.balance sender d hs
        omega
      · have htk := htokO s hss d
        have hbal := hO.balance s d hs
        omega
  · intro s d hs hl
    rw [hrost] at hs
    rw [hlife] at hl
    have hold := hO.slack s d hs hl
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      have hty : (w'.st sender).typestate = (w.st sender).typestate := hSty
      have hfloorEq : floorState I.desc (tname sender) (w'.st sender).typestate d =
          floorState I.desc (tname sender) (w.st sender).typestate d := by rw [hty]
      rw [hfloorEq]
      have hpen := hSph d
      have htk := htok d
      omega
    · have hph : (w'.st s).phase = (w.st s).phase := hphO s hss
      have hty : (w'.st s).typestate = (w.st s).typestate := htyO s hss
      have hpendEq : pending (w'.st s) d = pending (w.st s) d := by simp [pending, hph]
      have hfloorEq : floorState I.desc (tname s) (w'.st s).typestate d =
          floorState I.desc (tname s) (w.st s).typestate d := by rw [hty]
      rw [hpendEq, hfloorEq]
      have htk := htokO s hss d
      omega
  · intro s d hs hterm
    rw [hrost] at hs ⊢
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      exact absurd hterm hnot
    · have h0 := hO.still s d hs hterm
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s, h0]
  · intro s d hs hdead
    rw [hrost] at hs ⊢
    rw [hlife] at hdead
    by_cases hss : s = sender
    · have hswap : sender = s := hss.symm
      subst hswap
      exact absurd hsender hdead
    · have h0 := hO.quiet s d hs hdead
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s]; exact h0
  · intro i hl1
    exact hclear i hl1
  · intro i hdead
    exact hdeadE i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      exact (queueOk_life w w' m.sender host (hlife m.sender)).1 ((hkey host).1 m hm)
    · intro p hp
      exact (queueOk_life w w' p.sender host (hlife p.sender)).1 ((hkey host).2 p hp)
  · intro i hi
    exact hO.shaped i (by rw [hrost] at hi; exact hi)
  · exact hfrom

theorem charge_keeps (a : Actor) (dst : String) :
    (chargeSender a dst).life = a.life ∧ (chargeSender a dst).typestate = a.typestate ∧
      (chargeSender a dst).phase = a.phase ∧ (chargeSender a dst).box = a.box ∧
      (chargeSender a dst).parked = a.parked := by
  simp [chargeSender, bumpToken]

theorem charge_tok (a : Actor) (name d : String) (h : 1 ≤ a.tokens name) :
    (chargeSender a name).tokens d + (if d = name then 1 else 0) = a.tokens d := by
  by_cases hd : d = name
  · simp [hd, charge_at a name h]
  · simp [hd, charge_skip a name d hd]

theorem sends_to_tail (name d : String) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨ (∃ full gone, e = .trySend name label hint full gone)) :
    sendsTo d es + (if d = name then 1 else 0) ≤ sendsTo d (e :: es) := by
  rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> (
    simp only [sendsTo]
    by_cases h : name = d
    · have hb : (name == d) = true := beq_iff_eq.mpr h
      simp [hb, h]
      omega
    · have hb : (name == d) = false := by
        cases hbb : name == d with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hbb) h
      have hd : ¬ d = name := fun heq => h heq.symm
      simp [hb, hd])

theorem pending_stored (a : Actor) (dst : InstId) (b : Bool) (k' : Cont) (es : List Eff) (d : String)
    (hk : k'.rest = es)
    (hph : a.phase = .awaitReply dst k' ∨ a.phase = .parked dst b k' ∨ a.phase = (proceed a k').phase) :
    pending a d = sendsTo d es := by
  rcases hph with h | h | h
  · simp [pending, contRest, h, hk]
  · simp [pending, contRest, h, hk]
  · cases hk' : k'.rest with
    | nil =>
      unfold proceed at h
      simp [hk'] at h
      have hes : es = [] := hk.symm.trans hk'
      simp [pending, contRest, h, hes]
    | cons e es =>
      unfold proceed at h
      simp [hk'] at h
      simp [pending, contRest, h, hk, hk']

theorem owed_keep_mail (st : InstId → Actor) (id : InstId) (a : Actor) (dstName : String) (s : InstId)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster)
    (hb : a.box = (st id).box) (hp : a.parked = (st id).parked) :
    owed (fun i => if i = id then a else st i) dstName s roster = owed st dstName s roster := by
  have hslot := slot_eq_box st dstName s id a hb hp
  have hrep := owed_replace st dstName s id a roster nodup hmem
  omega

theorem slot_append_park (st : InstId → Actor) (dstName : String) (sender id : InstId) (p : Parked)
    (hname : tname id == dstName) (hs : p.sender = sender) :
    slot (fun i => if i = id then { st id with parked := (st id).parked ++ [p] } else st i) dstName sender id
      = slot st dstName sender id + 1 := by
  simp only [slot, hname]
  simp [countParked_append, hs, Nat.add_assoc]

theorem owed_append_park (st : InstId → Actor) (dstName : String) (sender dst : InstId) (p : Parked)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : dst ∈ roster)
    (hname : tname dst == dstName) (hs : p.sender = sender) :
    owed (fun i => if i = dst then { st dst with parked := (st dst).parked ++ [p] } else st i) dstName sender roster
      = owed st dstName sender roster + 1 := by
  have hcross := owed_replace st dstName sender dst { st dst with parked := (st dst).parked ++ [p] } roster nodup hmem
  have hslot := slot_append_park st dstName sender dst p hname hs
  omega

theorem owed_append_park_other (st : InstId → Actor) (dstName : String) (s dst : InstId) (p : Parked)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : dst ∈ roster) (hname : tname dst = dstName)
    (hs : p.sender ≠ s) :
    owed (fun i => if i = dst then { st dst with parked := (st dst).parked ++ [p] } else st i) dstName s roster =
      owed st dstName s roster := by
  have hb : (tname dst == dstName) = true := by simpa [beq_iff_eq] using hname
  have hslot : slot (fun i => if i = dst then { st dst with parked := (st dst).parked ++ [p] } else st i)
      dstName s dst = slot st dstName s dst := by
    have hne : (p.sender == s) = false := by
      cases hbb : p.sender == s with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hs
    simp [slot, hb, countParked_append, hne]
    exact hs
  have hrep := owed_replace st dstName s dst { st dst with parked := (st dst).parked ++ [p] } roster nodup hmem
  omega

@[simp] theorem issueCall_box (a : Actor) : (issueCall a).box = a.box := by simp [issueCall]

@[simp] theorem issueCall_parked (a : Actor) : (issueCall a).parked = a.parked := by simp [issueCall]

@[simp] theorem issueCall_life (a : Actor) : (issueCall a).life = a.life := by simp [issueCall]

@[simp] theorem issueCall_ty (a : Actor) : (issueCall a).typestate = a.typestate := by simp [issueCall]

@[simp] theorem issueCall_tokens (a : Actor) (d : String) : (issueCall a).tokens d = a.tokens d := by
  simp [issueCall]

@[simp] theorem issueCall_mid (a : Actor) : (issueCall a).nextMid = a.nextMid := by simp [issueCall]

@[simp] theorem issueCall_phase (a : Actor) : (issueCall a).phase = a.phase := by simp [issueCall]

@[simp] theorem issueCall_prio (a : Actor) : (issueCall a).prio = a.prio := by simp [issueCall]

@[simp] theorem issueCall_owe (a : Actor) : (issueCall a).oweId = a.oweId := by simp [issueCall]

@[simp] theorem issueCall_last (a : Actor) : (issueCall a).lastCall = a.lastCall := by simp [issueCall]

@[simp] theorem issued_life (a : Actor) (c : Bool) : (if c then issueCall a else a).life = a.life := by
  cases c <;> simp

@[simp] theorem issued_ty (a : Actor) (c : Bool) : (if c then issueCall a else a).typestate = a.typestate := by
  cases c <;> simp

@[simp] theorem issued_box (a : Actor) (c : Bool) : (if c then issueCall a else a).box = a.box := by
  cases c <;> simp

@[simp] theorem issued_parked (a : Actor) (c : Bool) : (if c then issueCall a else a).parked = a.parked := by
  cases c <;> simp

@[simp] theorem issued_tokens (a : Actor) (c : Bool) (d : String) :
    (if c then issueCall a else a).tokens d = a.tokens d := by
  cases c <;> simp

@[simp] theorem issued_mid (a : Actor) (c : Bool) : (if c then issueCall a else a).nextMid = a.nextMid := by
  cases c <;> simp

theorem enqueue_dead (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (h : (w.st dst).life ≠ .alive) :
    enqueueOrPark w D sender dst msg false k = setActor w sender (proceed (w.st sender) k) := by
  simp [enqueueOrPark, h]

/-- A call aimed at a name that is not alive is not stored. The caller takes
`NotAdmitted` immediately, whether the name is absent, shutting down, or dead. -/
theorem enqueue_miss (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (h : (w.st dst).life ≠ .alive) :
    enqueueOrPark w D sender dst msg true k =
      setActor w sender (finishCall (issueCall (w.st sender)) k .notAdmitted) := by
  simp [enqueueOrPark, h]

theorem enqueue_room_self_call (w : World) (D : Description) (sender : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk D w.N sender) :
    enqueueOrPark w D sender sender msg true k =
      setActor w sender
        { issueCall (chargeSender (w.st sender) (tname sender)) with
          box := (issueCall (chargeSender (w.st sender) (tname sender))).box ++
            [{ msg with mid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid }],
          nextMid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid + 1,
          phase := .awaitReply sender k } := by
  simp [enqueueOrPark, hlive, hpark, hcap]

theorem enqueue_room_self_send (w : World) (D : Description) (sender : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk D w.N sender) :
    enqueueOrPark w D sender sender msg false k =
      setActor w sender
        (proceed { chargeSender (w.st sender) (tname sender) with
          box := (chargeSender (w.st sender) (tname sender)).box ++
            [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }],
          nextMid := (chargeSender (w.st sender) (tname sender)).nextMid + 1 } k) := by
  simp [enqueueOrPark, hlive, hpark, hcap]

theorem enqueue_room_other_call (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk D w.N dst) :
    enqueueOrPark w D sender dst msg true k =
      setActor (setActor w dst { (w.st dst) with
        box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
        nextMid := (w.st dst).nextMid + 1 }) sender
        { issueCall (chargeSender (w.st sender) (tname dst)) with phase := .awaitReply dst k } := by
  simp [enqueueOrPark, hlive, hne, hpark, hcap]

theorem enqueue_room_other_send (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk D w.N dst) :
    enqueueOrPark w D sender dst msg false k =
      setActor (setActor w dst { (w.st dst) with
        box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
        nextMid := (w.st dst).nextMid + 1 }) sender
        (proceed (chargeSender (w.st sender) (tname dst)) k) := by
  simp [enqueueOrPark, hlive, hne, hpark, hcap]

theorem enqueue_park_self (w : World) (D : Description) (sender : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hroom : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender)) :
    enqueueOrPark w D sender sender msg isCall k =
      setActor w sender
        { (if isCall then issueCall (chargeSender (w.st sender) (tname sender))
            else chargeSender (w.st sender) (tname sender)) with
          parked := (if isCall then issueCall (chargeSender (w.st sender) (tname sender))
            else chargeSender (w.st sender) (tname sender)).parked ++
            [{ sender := sender,
               msg := { msg with
                 mid := (if isCall then issueCall (chargeSender (w.st sender) (tname sender))
                   else chargeSender (w.st sender) (tname sender)).nextMid },
               isCall := isCall }],
          nextMid := (if isCall then issueCall (chargeSender (w.st sender) (tname sender))
            else chargeSender (w.st sender) (tname sender)).nextMid + 1,
          phase := .parked sender isCall k } := by
  simp [enqueueOrPark, hlive, hroom]

theorem enqueue_park_other (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hroom : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst)) :
    enqueueOrPark w D sender dst msg isCall k =
      setActor
        (setActor w dst
          { (w.st dst) with
            parked := (w.st dst).parked ++
              [{ sender := sender,
                 msg := { msg with mid := (w.st dst).nextMid },
                 isCall := isCall }],
            nextMid := (w.st dst).nextMid + 1 })
        sender
        { (if isCall then issueCall (chargeSender (w.st sender) (tname dst))
            else chargeSender (w.st sender) (tname dst)) with phase := .parked dst isCall k } := by
  simp [enqueueOrPark, hlive, hne, hroom]

theorem owed_self_box (st : InstId → Actor) (name : String) (id : InstId) (a : Actor) (msg : Msg)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster) (hname : tname id = name)
    (hmsg : msg.sender = id) (hb : a.box = (st id).box ++ [msg]) (hp : a.parked = (st id).parked)
    (s : InstId) :
    owed (fun i => if i = id then a else st i) name s roster =
      owed st name s roster + if s = id then 1 else 0 := by
  let a0 : Actor := { st id with box := (st id).box ++ [msg] }
  have hmail := owed_mail_eq (fun i => if i = id then a else st i)
      (fun i => if i = id then a0 else st i) name s roster (by
        intro j _
        by_cases hj : j = id
        · simp [hj, a0, hb, hp]
        · simp [hj])
  by_cases hs : s = id
  · have hswap : id = s := hs.symm
    subst hswap
    have happ := owed_append_msg st name id id msg roster nodup hmem (beq_iff_eq.mpr hname) hmsg
    simp
    rw [hmail]
    simpa using happ
  · have hneS : msg.sender ≠ s := by
      intro heq
      exact hs (heq.symm.trans hmsg)
    have happ := owed_append_other st name s id msg roster nodup hmem hname hneS
    simp [hs]
    rw [hmail]
    simpa using happ

theorem owed_self_park (st : InstId → Actor) (name : String) (id : InstId) (a : Actor) (p : Parked)
    (roster : List InstId) (nodup : roster.Nodup) (hmem : id ∈ roster) (hname : tname id = name)
    (hsender : p.sender = id) (hb : a.box = (st id).box) (hp : a.parked = (st id).parked ++ [p])
    (s : InstId) :
    owed (fun i => if i = id then a else st i) name s roster =
      owed st name s roster + if s = id then 1 else 0 := by
  let a0 : Actor := { st id with parked := (st id).parked ++ [p] }
  have hmail := owed_mail_eq (fun i => if i = id then a else st i)
      (fun i => if i = id then a0 else st i) name s roster (by
        intro j _
        by_cases hj : j = id
        · simp [hj, a0, hb, hp]
        · simp [hj])
  by_cases hs : s = id
  · have hswap : id = s := hs.symm
    subst hswap
    have happ := owed_append_park st name id id p roster nodup hmem (beq_iff_eq.mpr hname) hsender
    simp
    rw [hmail]
    simpa using happ
  · have hneS : p.sender ≠ s := by
      intro heq
      exact hs (heq.symm.trans hsender)
    have happ := owed_append_park_other st name s id p roster nodup hmem hname hneS
    simp [hs]
    rw [hmail]
    simpa using happ

theorem pending_drop (a a' : Actor) (k : Cont) (e : Eff) (es : List Eff) (name label : String)
    (hint : Nat) (d : String) (hph : a.phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨ (∃ full gone, e = .trySend name label hint full gone))
    (hp : pending a' d = sendsTo d es) :
    pending a' d + (if d = name then 1 else 0) ≤ pending a d := by
  have hold : pending a d = sendsTo d (e :: es) := by simp [pending, contRest, hph, hk]
  rw [hp, hold]
  exact sends_to_tail name d e es label hint he

theorem proceed_ty_keep (a : Actor) (k : Cont) (h : a.typestate = k.toState) :
    (proceed a k).typestate = a.typestate := by
  unfold proceed
  cases k.rest <;> simp [h]

theorem proceed_phase_indep (a b : Actor) (k : Cont) : (proceed a k).phase = (proceed b k).phase := by
  unfold proceed
  cases k.rest <;> rfl

/-- One actor spends a token and takes the extra owed message. -/
theorem occ_one (I : Impl) (w : World) (sender : InstId) (aS : Actor) (name : String) (hO : OccInv I w)
    (hlife : aS.life = (w.st sender).life) (hty : aS.typestate = (w.st sender).typestate)
    (htok : ∀ d, aS.tokens d + (if d = name then 1 else 0) = (w.st sender).tokens d)
    (hpend : ∀ d, pending aS d + (if d = name then 1 else 0) ≤ pending (w.st sender) d)
    (hown : ∀ s, owed (fun i => if i = sender then aS else w.st i) name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s,
      owed (fun i => if i = sender then aS else w.st i) d s w.roster = owed w.st d s w.roster)
    (hbox : ∀ m ∈ aS.box, m.sender ∈ w.roster) (hpark : ∀ p ∈ aS.parked, p.sender ∈ w.roster)
    (hpm : ∀ p ∈ aS.parked, p.sender = p.msg.sender)
    (hclear : ∀ i, l1 I.desc (tname i) = true → (if i = sender then aS else (w.st i)).parked = [])
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hkeyB : ∀ m ∈ aS.box, queueOk w m.sender sender)
    (hkeyP : ∀ p ∈ aS.parked, queueOk w p.sender sender)
    (hdeadA : aS.life ≠ .alive → aS.box = [] ∧ aS.parked = [])
    (hfromB : peerKey sender = none → ∀ m ∈ aS.box,
      peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false)
    (hfromP : peerKey sender = none → ∀ p ∈ aS.parked,
      peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false) :
    OccInv I (setActor w sender aS) := by
  let w' := setActor w sender aS
  suffices OccInv I w' by simpa [w'] using this
  have hst : ∀ i, w'.st i = if i = sender then aS else w.st i := by
    intro i
    by_cases hs : i = sender <;> simp [w', setActor, hs]
  have howedEq : ∀ d s, owed w'.st d s w.roster =
      owed (fun i => if i = sender then aS else w.st i) d s w.roster := by
    intro d s
    refine owed_mail_eq _ _ _ _ w.roster ?_
    intro i _
    rw [hst i]
    exact ⟨rfl, rfl⟩
  apply occ_pay I w w' sender name hO
  · simp [w', setActor]
  · simp [w', setActor]
  · intro n; simp [w', setActor]
  · intro i
    rw [hst i]
    by_cases hs : i = sender <;> simp [hs, hlife]
  · have hs : (w'.st sender).typestate = aS.typestate := by rw [hst sender]; simp
    rw [hs]; exact hty
  · intro i hi
    rw [hst i]
    simp [hi]
  · intro d
    have hs : (w'.st sender).phase = aS.phase := by rw [hst sender]; simp
    have hp : pending (w'.st sender) d = pending aS d := by simp [pending, hs]
    rw [hp]
    exact hpend d
  · intro i hi
    rw [hst i]
    simp [hi]
  · intro d
    have hs : (w'.st sender).tokens d = aS.tokens d := by rw [hst sender]; simp
    rw [hs]
    exact htok d
  · intro i hi d
    rw [hst i]
    simp [hi]
  · intro s
    rw [howedEq]
    exact hown s
  · intro d hd s
    rw [howedEq]
    exact hother d hd s
  · intro i m hm
    rw [hst i] at hm
    by_cases hs : i = sender
    · simp [hs] at hm
      exact hbox m hm
    · simp [hs] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    rw [hst i] at hp
    by_cases hs : i = sender
    · simp [hs] at hp
      exact hpark p hp
    · simp [hs] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    rw [hst i] at hp
    by_cases hs : i = sender
    · simp [hs] at hp
      exact hpm p hp
    · simp [hs] at hp
      exact hO.parkMsg i p hp
  · intro i hl1
    rw [hst i]
    exact hclear i hl1
  · intro i hnin
    have hne : i ≠ sender := fun heq => hnin (heq ▸ hsend)
    rw [hst i]
    simp [hne]
  · exact hsend
  · exact hsender
  · exact hnot
  · intro i hdead
    rw [hst i] at hdead ⊢
    by_cases hs : i = sender
    · simp [hs] at hdead ⊢
      exact hdeadA hdead
    · simp [hs] at hdead ⊢
      exact hO.deadEmpty i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst host] at hm
      by_cases hs : host = sender
      · rw [hs] at hm ⊢
        simp at hm
        exact hkeyB m hm
      · simp [hs] at hm
        exact (hO.sameKey host).1 m hm
    · intro p hp
      rw [hst host] at hp
      by_cases hs : host = sender
      · rw [hs] at hp ⊢
        simp at hp
        exact hkeyP p hp
      · simp [hs] at hp
        exact (hO.sameKey host).2 p hp
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst host] at hm
      by_cases hs : host = sender
      · simp [hs] at hm
        exact hfromB (hs ▸ hk) m hm
      · simp [hs] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [hst host] at hp
      by_cases hs : host = sender
      · simp [hs] at hp
        exact hfromP (hs ▸ hk) p hp
      · simp [hs] at hp
        exact (hO.coreFrom host hk).2 p hp

theorem occ_self_call (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ (∃ na to, e = .call (tname sender) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg true (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_room_self_call w I.desc sender msg (afterHead k) hsender hpark hcap]
  let aS : Actor :=
    { issueCall (chargeSender (w.st sender) (tname sender)) with
      box := (issueCall (chargeSender (w.st sender) (tname sender))).box ++
        [{ msg with mid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid }],
      nextMid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid + 1,
      phase := .awaitReply sender (afterHead k) }
  suffices OccInv I (setActor w sender aS) by simpa [aS] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, hcl]
  · simp [aS, hcty]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname sender)).tokens d := by simp [aS]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS sender true (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inl (by simp [aS])
    exact pending_drop (w.st sender) aS k e es (tname sender) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_self_box w.st (tname sender) sender aS
      { msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }
      w.roster hO.nodup hmem rfl (by simpa using hmsg)
      (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, hcb] using hm
    simp [List.mem_append, List.mem_singleton] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom sender m h
    | inr h => simpa [h, hmsg] using hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkMsg sender p hp'
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1 ⊢
      simp [aS, hcp]
      exact hO.clear sender hl1
    · simp [hs]
      exact hO.clear i hl1
  · exact hmem
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, hcb] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey sender).1 m hm'
    · rw [hm', hmsg]
      exact queueOk_alive w sender sender (key_refl sender) hsender
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro hdead
    exact absurd (by simp [aS, hcl]; exact hsender) hdead
  · intro hk m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, hcb] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.coreFrom sender hk).1 m hm'
    · exact Or.inl (by simpa [hm', hmsg] using hk)
  · intro hk p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.coreFrom sender hk).2 p hp'

theorem occ_self_send (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ (∃ na to, e = .call (tname sender) label hint na to) ∨
      (∃ full gone, e = .trySend (tname sender) label hint full gone))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_room_self_send w I.desc sender msg (afterHead k) hsender hpark hcap]
  let base : Actor :=
    { chargeSender (w.st sender) (tname sender) with
      box := (chargeSender (w.st sender) (tname sender)).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }],
      nextMid := (chargeSender (w.st sender) (tname sender)).nextMid + 1 }
  let aS : Actor := proceed base (afterHead k)
  suffices OccInv I (setActor w sender aS) by simpa [aS, base] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, base, proceed_life, hcl]
  · have hbase : base.typestate = (afterHead k).toState := by simp [base, afterHead, hcty, hty]
    simpa [aS, base, hcty] using proceed_ty_keep base (afterHead k) hbase
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname sender)).tokens d := by
      simp [aS, base, proceed_tokens]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS sender false (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inr (proceed_phase_indep base aS (afterHead k)))
    exact pending_drop (w.st sender) aS k e es (tname sender) label hint d hph hk
      (by
        rcases he with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) hp
  · intro s
    exact owed_self_box w.st (tname sender) sender aS
      { msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }
      w.roster hO.nodup hmem rfl (by simpa using hmsg)
      (by simp [aS, base, proceed_box, hcb]) (by simp [aS, base, proceed_parked, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, base, proceed_box, hcb] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom sender m h
    | inr h => simpa [h, hmsg] using hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, base, proceed_parked, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, base, proceed_parked, hcp] using hp
    exact hO.parkMsg sender p hp'
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1 ⊢
      simp [aS, base, proceed_parked, hcp]
      exact hO.clear sender hl1
    · simp [hs]
      exact hO.clear i hl1
  · exact hmem
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, base, proceed_box, hcb] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey sender).1 m hm'
    · rw [hm', hmsg]
      exact queueOk_alive w sender sender (key_refl sender) hsender
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, base, proceed_parked, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro hdead
    exact absurd (by simp [aS, base, proceed_life, hcl]; exact hsender) hdead
  · intro hk m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, base, proceed_box, hcb] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.coreFrom sender hk).1 m hm'
    · exact Or.inl (by simpa [hm', hmsg] using hk)
  · intro hk p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, base, proceed_parked, hcp] using hp
    exact (hO.coreFrom sender hk).2 p hp'

theorem owed_other_box (st : InstId → Actor) (name : String) (sender dst : InstId) (aS aD : Actor)
    (msg : Msg) (roster : List InstId) (nodup : roster.Nodup) (hdst : dst ∈ roster) (hsend : sender ∈ roster)
    (hne : sender ≠ dst) (hname : tname dst = name) (hmsg : msg.sender = sender)
    (hbS : aS.box = (st sender).box) (hpS : aS.parked = (st sender).parked)
    (hbD : aD.box = (st dst).box ++ [msg]) (hpD : aD.parked = (st dst).parked) (s : InstId) :
    owed (fun i => if i = sender then aS else if i = dst then aD else st i) name s roster =
      owed st name s roster + if s = sender then 1 else 0 := by
  let pure : Actor := { st dst with box := (st dst).box ++ [msg] }
  let stD : InstId → Actor := fun i => if i = dst then pure else st i
  let stA : InstId → Actor := fun i => if i = dst then aD else st i
  have hAD : owed stA name s roster = owed stD name s roster := by
    refine owed_mail_eq _ _ _ _ roster ?_
    intro j _
    by_cases hj : j = dst
    · simp [stA, stD, hj, pure, hbD, hpD]
    · simp [stA, stD, hj]
  have hbase : owed stD name s roster = owed st name s roster + if s = sender then 1 else 0 := by
    by_cases hs : s = sender
    · have hswap : sender = s := hs.symm
      subst hswap
      have happ := owed_append_msg st name sender dst msg roster nodup hdst (beq_iff_eq.mpr hname) hmsg
      simpa [stD, pure] using happ
    · have hneS : msg.sender ≠ s := by
        intro heq
        exact hs (heq.symm.trans hmsg)
      have happ := owed_append_other st name s dst msg roster nodup hdst hname hneS
      simp [hs]
      simpa [stD, pure] using happ
  have hkeep : owed (fun i => if i = sender then aS else stA i) name s roster = owed stA name s roster := by
    have hb : aS.box = (stA sender).box := by simp [stA, hne, hbS]
    have hp : aS.parked = (stA sender).parked := by simp [stA, hne, hpS]
    exact owed_keep_mail stA sender aS name s roster nodup hsend hb hp
  have hfun : (fun i => if i = sender then aS else if i = dst then aD else st i) =
      fun i => if i = sender then aS else stA i := by
    funext i
    by_cases hs : i = sender <;> simp [stA, hs]
  rw [hfun, hkeep, hAD, hbase]

theorem owed_other_park (st : InstId → Actor) (name : String) (sender dst : InstId) (aS aD : Actor)
    (p : Parked) (roster : List InstId) (nodup : roster.Nodup) (hdst : dst ∈ roster) (hsend : sender ∈ roster)
    (hne : sender ≠ dst) (hname : tname dst = name) (hps : p.sender = sender)
    (hbS : aS.box = (st sender).box) (hpS : aS.parked = (st sender).parked)
    (hbD : aD.box = (st dst).box) (hpD : aD.parked = (st dst).parked ++ [p]) (s : InstId) :
    owed (fun i => if i = sender then aS else if i = dst then aD else st i) name s roster =
      owed st name s roster + if s = sender then 1 else 0 := by
  let pure : Actor := { st dst with parked := (st dst).parked ++ [p] }
  let stD : InstId → Actor := fun i => if i = dst then pure else st i
  let stA : InstId → Actor := fun i => if i = dst then aD else st i
  have hAD : owed stA name s roster = owed stD name s roster := by
    refine owed_mail_eq _ _ _ _ roster ?_
    intro j _
    by_cases hj : j = dst
    · simp [stA, stD, hj, pure, hbD, hpD]
    · simp [stA, stD, hj]
  have hbase : owed stD name s roster = owed st name s roster + if s = sender then 1 else 0 := by
    by_cases hs : s = sender
    · have hswap : sender = s := hs.symm
      subst hswap
      have happ := owed_append_park st name sender dst p roster nodup hdst (beq_iff_eq.mpr hname) hps
      simpa [stD, pure] using happ
    · have hneS : p.sender ≠ s := by
        intro heq
        exact hs (heq.symm.trans hps)
      have happ := owed_append_park_other st name s dst p roster nodup hdst hname hneS
      simp [hs]
      simpa [stD, pure] using happ
  have hkeep : owed (fun i => if i = sender then aS else stA i) name s roster = owed stA name s roster := by
    have hb : aS.box = (stA sender).box := by simp [stA, hne, hbS]
    have hp : aS.parked = (stA sender).parked := by simp [stA, hne, hpS]
    exact owed_keep_mail stA sender aS name s roster nodup hsend hb hp
  have hfun : (fun i => if i = sender then aS else if i = dst then aD else st i) =
      fun i => if i = sender then aS else stA i := by
    funext i
    by_cases hs : i = sender <;> simp [stA, hs]
  rw [hfun, hkeep, hAD, hbase]

theorem owed_other_skip (st : InstId → Actor) (sender dst : InstId) (aS aD : Actor) (d : String)
    (roster : List InstId) (nodup : roster.Nodup) (hdst : dst ∈ roster) (hsend : sender ∈ roster)
    (hne : sender ≠ dst) (hname : tname dst ≠ d)
    (hbS : aS.box = (st sender).box) (hpS : aS.parked = (st sender).parked) (s : InstId) :
    owed (fun i => if i = sender then aS else if i = dst then aD else st i) d s roster =
      owed st d s roster := by
  let stA : InstId → Actor := fun i => if i = dst then aD else st i
  have h1 : owed stA d s roster = owed st d s roster :=
    owed_off st dst aD d s roster nodup hdst hname
  have hkeep : owed (fun i => if i = sender then aS else stA i) d s roster = owed stA d s roster := by
    have hb : aS.box = (stA sender).box := by simp [stA, hne, hbS]
    have hp : aS.parked = (stA sender).parked := by simp [stA, hne, hpS]
    exact owed_keep_mail stA sender aS d s roster nodup hsend hb hp
  have hfun : (fun i => if i = sender then aS else if i = dst then aD else st i) =
      fun i => if i = sender then aS else stA i := by
    funext i
    by_cases hs : i = sender <;> simp [stA, hs]
  rw [hfun, hkeep, h1]

/-- The sender and a different mailbox change together. -/
theorem occ_two (I : Impl) (w : World) (sender dst : InstId) (aS aD : Actor) (name : String)
    (hO : OccInv I w) (hne : sender ≠ dst)
    (hlifeS : aS.life = (w.st sender).life) (hlifeD : aD.life = (w.st dst).life)
    (htyS : aS.typestate = (w.st sender).typestate) (htyD : aD.typestate = (w.st dst).typestate)
    (hphD : aD.phase = (w.st dst).phase)
    (htokS : ∀ d, aS.tokens d + (if d = name then 1 else 0) = (w.st sender).tokens d)
    (htokD : ∀ d, aD.tokens d = (w.st dst).tokens d)
    (hpend : ∀ d, pending aS d + (if d = name then 1 else 0) ≤ pending (w.st sender) d)
    (hown : ∀ s, owed (fun i => if i = sender then aS else if i = dst then aD else w.st i) name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s,
      owed (fun i => if i = sender then aS else if i = dst then aD else w.st i) d s w.roster =
        owed w.st d s w.roster)
    (hboxS : ∀ m ∈ aS.box, m.sender ∈ w.roster) (hboxD : ∀ m ∈ aD.box, m.sender ∈ w.roster)
    (hparkS : ∀ p ∈ aS.parked, p.sender ∈ w.roster) (hparkD : ∀ p ∈ aD.parked, p.sender ∈ w.roster)
    (hpmS : ∀ p ∈ aS.parked, p.sender = p.msg.sender) (hpmD : ∀ p ∈ aD.parked, p.sender = p.msg.sender)
    (hclear : ∀ i, l1 I.desc (tname i) = true →
      (if i = sender then aS else if i = dst then aD else w.st i).parked = [])
    (hsend : sender ∈ w.roster) (hdst : dst ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hkeyBS : ∀ m ∈ aS.box, queueOk w m.sender sender)
    (hkeyPS : ∀ p ∈ aS.parked, queueOk w p.sender sender)
    (hkeyBD : ∀ m ∈ aD.box, queueOk w m.sender dst)
    (hkeyPD : ∀ p ∈ aD.parked, queueOk w p.sender dst)
    (hdeadS : aS.life ≠ .alive → aS.box = [] ∧ aS.parked = [])
    (hdeadD : aD.life ≠ .alive → aD.box = [] ∧ aD.parked = [])
    (hfromS : peerKey sender = none →
      (∀ m ∈ aS.box, peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false) ∧
      (∀ p ∈ aS.parked, peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false))
    (hfromD : peerKey dst = none →
      (∀ m ∈ aD.box, peerKey m.sender = none ∨ terminableB I.desc (tname m.sender) = false) ∧
      (∀ p ∈ aD.parked, peerKey p.sender = none ∨ terminableB I.desc (tname p.sender) = false)) :
    OccInv I (setActor (setActor w dst aD) sender aS) := by
  let w' := setActor (setActor w dst aD) sender aS
  suffices OccInv I w' by simpa [w'] using this
  have hst : ∀ i, w'.st i = if i = sender then aS else if i = dst then aD else w.st i := by
    intro i
    by_cases hs : i = sender
    · simp [w', setActor, hs]
    · by_cases hd : i = dst <;> simp [w', setActor, hs, hd, hne]
  have howedEq : ∀ d s, owed w'.st d s w.roster =
      owed (fun i => if i = sender then aS else if i = dst then aD else w.st i) d s w.roster := by
    intro d s
    refine owed_mail_eq _ _ _ _ w.roster ?_
    intro i _
    rw [hst i]
    exact ⟨rfl, rfl⟩
  apply occ_pay I w w' sender name hO
  · simp [w', setActor]
  · simp [w', setActor]
  · intro n; simp [w', setActor]
  · intro i
    rw [hst i]
    by_cases hs : i = sender
    · simp [hs, hlifeS]
    · by_cases hd : i = dst
      · rw [hd] at hs ⊢
        simp [hs, hlifeD]
      · simp [hs, hd]
  · have hs : (w'.st sender).typestate = aS.typestate := by rw [hst sender]; simp
    rw [hs]; exact htyS
  · intro i hi
    rw [hst i]
    by_cases hd : i = dst
    · rw [hd] at hi ⊢
      simp [hi, htyD]
    · simp [hi, hd]
  · intro d
    have hs : (w'.st sender).phase = aS.phase := by rw [hst sender]; simp
    have hp : pending (w'.st sender) d = pending aS d := by simp [pending, hs]
    rw [hp]
    exact hpend d
  · intro i hi
    rw [hst i]
    by_cases hd : i = dst
    · rw [hd] at hi ⊢
      simp [hi, hphD]
    · simp [hi, hd]
  · intro d
    have hs : (w'.st sender).tokens d = aS.tokens d := by rw [hst sender]; simp
    rw [hs]
    exact htokS d
  · intro i hi d
    rw [hst i]
    by_cases hd : i = dst
    · rw [hd] at hi ⊢
      simp [hi, htokD]
    · simp [hi, hd]
  · intro s
    rw [howedEq]
    exact hown s
  · intro d hd s
    rw [howedEq]
    exact hother d hd s
  · intro i m hm
    rw [hst i] at hm
    by_cases hs : i = sender
    · simp [hs] at hm
      exact hboxS m hm
    · by_cases hd : i = dst
      · rw [hd] at hs hm
        simp [hs] at hm
        exact hboxD m hm
      · simp [hs, hd] at hm
        exact hO.sentFrom i m hm
  · intro i p hp
    rw [hst i] at hp
    by_cases hs : i = sender
    · simp [hs] at hp
      exact hparkS p hp
    · by_cases hd : i = dst
      · rw [hd] at hs hp
        simp [hs] at hp
        exact hparkD p hp
      · simp [hs, hd] at hp
        exact hO.parkFrom i p hp
  · intro i p hp
    rw [hst i] at hp
    by_cases hs : i = sender
    · simp [hs] at hp
      exact hpmS p hp
    · by_cases hd : i = dst
      · rw [hd] at hs hp
        simp [hs] at hp
        exact hpmD p hp
      · simp [hs, hd] at hp
        exact hO.parkMsg i p hp
  · intro i hl1
    rw [hst i]
    exact hclear i hl1
  · intro i hnin
    have hneS : i ≠ sender := fun heq => hnin (heq ▸ hsend)
    have hneD : i ≠ dst := fun heq => hnin (heq ▸ hdst)
    rw [hst i]
    simp [hneS, hneD]
  · exact hsend
  · exact hsender
  · exact hnot
  · intro i hdead
    by_cases hs : i = sender
    · rw [hs] at hdead ⊢
      rw [hst sender] at hdead ⊢
      simp at hdead ⊢
      exact hdeadS hdead
    · by_cases hd : i = dst
      · rw [hd] at hdead ⊢
        rw [hst dst] at hdead ⊢
        simp [hne.symm] at hdead ⊢
        exact hdeadD hdead
      · rw [hst i] at hdead ⊢
        simp [hs, hd] at hdead ⊢
        exact hO.deadEmpty i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hs : host = sender
      · rw [hs] at hm ⊢
        rw [hst sender] at hm
        simp at hm
        exact hkeyBS m hm
      · by_cases hd : host = dst
        · rw [hd] at hm ⊢
          rw [hst dst] at hm
          simp [hne.symm] at hm
          exact hkeyBD m hm
        · rw [hst host] at hm
          simp [hs, hd] at hm
          exact (hO.sameKey host).1 m hm
    · intro p hp
      by_cases hs : host = sender
      · rw [hs] at hp ⊢
        rw [hst sender] at hp
        simp at hp
        exact hkeyPS p hp
      · by_cases hd : host = dst
        · rw [hd] at hp ⊢
          rw [hst dst] at hp
          simp [hne.symm] at hp
          exact hkeyPD p hp
        · rw [hst host] at hp
          simp [hs, hd] at hp
          exact (hO.sameKey host).2 p hp
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst host] at hm
      by_cases hs : host = sender
      · simp [hs] at hm
        exact (hfromS (hs ▸ hk)).1 m hm
      · by_cases hd : host = dst
        · simp [hd, hne.symm] at hm
          exact (hfromD (hd ▸ hk)).1 m hm
        · simp [hs, hd] at hm
          exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [hst host] at hp
      by_cases hs : host = sender
      · simp [hs] at hp
        exact (hfromS (hs ▸ hk)).2 p hp
      · by_cases hd : host = dst
        · simp [hd, hne.symm] at hp
          exact (hfromD (hd ▸ hk)).2 p hp
        · simp [hs, hd] at hp
          exact (hO.coreFrom host hk).2 p hp

theorem occ_self_park (I : Impl) (hL : LocalOk I) (w : World) (sender : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ (∃ na to, e = .call (tname sender) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hroom : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk I.desc w.N sender)) :
    OccInv I (enqueueOrPark w I.desc sender sender msg isCall (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_park_self w I.desc sender msg isCall (afterHead k) hsender hroom]
  let charged := chargeSender (w.st sender) (tname sender)
  let base := if isCall then issueCall charged else charged
  let entry : Parked :=
    { sender := sender, msg := { msg with mid := base.nextMid }, isCall := isCall }
  let aS : Actor :=
    { life := base.life, typestate := base.typestate, phase := .parked sender isCall (afterHead k),
      box := base.box, prio := base.prio, parked := base.parked ++ [entry], tokens := base.tokens,
      nextMid := base.nextMid + 1, waitId := base.waitId, nextCall := base.nextCall,
      oweId := base.oweId, lastCall := base.lastCall }
  suffices OccInv I (setActor w sender aS) by simpa [aS, base, charged, entry, base, charged] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, base, charged, hcl]
  · simp [aS, base, charged, hcty]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname sender)).tokens d := by simp [aS, base, charged]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS sender isCall (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inl (by simp [aS, base, charged]))
    exact pending_drop (w.st sender) aS k e es (tname sender) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_self_park w.st (tname sender) sender aS entry w.roster hO.nodup hmem rfl rfl
      (by simp [aS, base, charged, hcb]) (by simp [aS, base, charged, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, base, charged, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, base, charged, hcp] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom sender p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, base, charged, hcp] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkMsg sender p h
    | inr h => simp [h, entry, hmsg]
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1
      exact absurd (l1_park_unreachable I hL w hO hT sender sender hsender hmem hsender hpend1 hl1
        (key_refl sender)) hroom
    · simp [hs]
      exact hO.clear i hl1
  · exact hmem
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, base, charged, hcb] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, base, charged, hcp] using hp
    simp [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact (hO.sameKey sender).2 p hp'
    · simp [hp', entry]
      exact queueOk_alive w sender sender (key_refl sender) hsender
  · intro hdead
    exact absurd (by simp [aS, base, charged, hcl]; exact hsender) hdead
  · intro hk m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, base, charged, hcb] using hm
    exact (hO.coreFrom sender hk).1 m hm'
  · intro hk p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, base, charged, hcp] using hp
    simp [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact (hO.coreFrom sender hk).2 p hp'
    · exact Or.inl (by simp [hp', entry, hmsg, hk])

theorem occ_other_call (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender)) (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst)
    (hagree : keyAgrees sender dst)
    (hcore : peerKey dst = none →
      peerKey sender = none ∨ terminableB I.desc (tname sender) = false) :
    OccInv I (enqueueOrPark w I.desc sender dst msg true (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_room_other_call w I.desc sender dst msg (afterHead k) hlive hne hpark hcap]
  let aD : Actor :=
    { (w.st dst) with
      box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
      nextMid := (w.st dst).nextMid + 1 }
  let aS : Actor :=
    { issueCall (chargeSender (w.st sender) (tname dst)) with phase := .awaitReply dst (afterHead k) }
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by simpa [aS, aD] using this
  apply occ_two I w sender dst aS aD (tname dst) hO hne
  · simp [aS, hcl]
  · simp [aD]
  · simp [aS, hcty]
  · simp [aD]
  · simp [aD]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname dst)).tokens d := by simp [aS]
    rw [htk]
    exact charge_tok (w.st sender) (tname dst) d htok1
  · intro d; simp [aD]
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS dst true (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inl (by simp [aS])
    exact pending_drop (w.st sender) aS k e es (tname dst) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_other_box w.st (tname dst) sender dst aS aD
      { msg with mid := (w.st dst).nextMid } w.roster hO.nodup hdst hmem hne rfl (by simpa using hmsg)
      (by simp [aS, hcb]) (by simp [aS, hcp]) (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by simpa [aD] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom dst m h
    | inr h => simpa [h, hmsg] using hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact hO.parkFrom dst p hp'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkMsg sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact hO.parkMsg dst p hp'
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1 ⊢
      simp [aS, hcp]
      exact hO.clear sender hl1
    · by_cases hd : i = dst
      · rw [hd] at hl1 ⊢
        have hne' : dst ≠ sender := fun h => hne h.symm
        simp [hne', aD]
        exact hO.clear dst hl1
      · simp [hs, hd]
        exact hO.clear i hl1
  · exact hmem
  · exact hdst
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by
      simpa [aD] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey dst).1 m hm'
    · rw [hm', hmsg]
      exact queueOk_alive w sender dst hagree hsender
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact (hO.sameKey dst).2 p hp'
  · intro hdead
    exact absurd (by simp [aS, hcl]; exact hsender) hdead
  · intro hdead
    exact absurd (by simp [aD]; exact hlive) hdead
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
      exact (hO.coreFrom sender hk).1 m hm'
    · intro p hp
      have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
      exact (hO.coreFrom sender hk).2 p hp'
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by
        simpa [aD] using hm
      simp [List.mem_append] at hm'
      rcases hm' with hm' | hm'
      · exact (hO.coreFrom dst hk).1 m hm'
      · rcases hcore hk with hpk | hterm
        · exact Or.inl (by simpa [hm', hmsg] using hpk)
        · exact Or.inr (by simpa [hm', hmsg] using hterm)
    · intro p hp
      have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
      exact (hO.coreFrom dst hk).2 p hp'

theorem occ_other_send (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to) ∨
      (∃ full gone, e = .trySend (tname dst) label hint full gone))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hne : sender ≠ dst) (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst)
    (hagree : keyAgrees sender dst)
    (hcore : peerKey dst = none →
      peerKey sender = none ∨ terminableB I.desc (tname sender) = false) :
    OccInv I (enqueueOrPark w I.desc sender dst msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_room_other_send w I.desc sender dst msg (afterHead k) hlive hne hpark hcap]
  let charged : Actor := chargeSender (w.st sender) (tname dst)
  let aD : Actor :=
    { (w.st dst) with
      box := (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }],
      nextMid := (w.st dst).nextMid + 1 }
  let aS : Actor := proceed charged (afterHead k)
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by simpa [aS, aD, charged] using this
  apply occ_two I w sender dst aS aD (tname dst) hO hne
  · simp [aS, charged, proceed_life, hcl]
  · simp [aD]
  · have hbase : charged.typestate = (afterHead k).toState := by simp [charged, afterHead, hcty, hty]
    simpa [aS, charged, hcty] using proceed_ty_keep charged (afterHead k) hbase
  · simp [aD]
  · simp [aD]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname dst)).tokens d := by
      simp [aS, charged, proceed_tokens]
    rw [htk]
    exact charge_tok (w.st sender) (tname dst) d htok1
  · intro d; simp [aD]
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS dst false (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inr (proceed_phase_indep charged aS (afterHead k)))
    exact pending_drop (w.st sender) aS k e es (tname dst) label hint d hph hk
      (by
        rcases he with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) hp
  · intro s
    exact owed_other_box w.st (tname dst) sender dst aS aD
      { msg with mid := (w.st dst).nextMid } w.roster hO.nodup hdst hmem hne rfl (by simpa using hmsg)
      (by simp [aS, charged, proceed_box, hcb]) (by simp [aS, charged, proceed_parked, hcp])
      (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, charged, proceed_box, hcb])
      (by simp [aS, charged, proceed_parked, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, proceed_box, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by simpa [aD] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom dst m h
    | inr h => simpa [h, hmsg] using hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, proceed_parked, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact hO.parkFrom dst p hp'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, proceed_parked, hcp] using hp
    exact hO.parkMsg sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact hO.parkMsg dst p hp'
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1 ⊢
      simp [aS, charged, proceed_parked, hcp]
      exact hO.clear sender hl1
    · by_cases hd : i = dst
      · rw [hd] at hl1 ⊢
        have hne' : dst ≠ sender := fun h => hne h.symm
        simp [hne', aD]
        exact hO.clear dst hl1
      · simp [hs, hd]
        exact hO.clear i hl1
  · exact hmem
  · exact hdst
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, proceed_box, hcb] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, proceed_parked, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by
      simpa [aD] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey dst).1 m hm'
    · rw [hm', hmsg]
      exact queueOk_alive w sender dst hagree hsender
  · intro p hp
    have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
    exact (hO.sameKey dst).2 p hp'
  · intro hdead
    exact absurd (by simp [aS, charged, proceed_life, hcl]; exact hsender) hdead
  · intro hdead
    exact absurd (by simp [aD]; exact hlive) hdead
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, proceed_box, hcb] using hm
      exact (hO.coreFrom sender hk).1 m hm'
    · intro p hp
      have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, proceed_parked, hcp] using hp
      exact (hO.coreFrom sender hk).2 p hp'
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st dst).box ++ [{ msg with mid := (w.st dst).nextMid }] := by
        simpa [aD] using hm
      simp [List.mem_append] at hm'
      rcases hm' with hm' | hm'
      · exact (hO.coreFrom dst hk).1 m hm'
      · rcases hcore hk with hpk | hterm
        · exact Or.inl (by simpa [hm', hmsg] using hpk)
        · exact Or.inr (by simpa [hm', hmsg] using hterm)
    · intro p hp
      have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
      exact (hO.coreFrom dst hk).2 p hp'

theorem occ_other_park (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname sender)) (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive)     (hagree : keyAgrees sender dst)
    (hroom : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst))
    (hcore : peerKey dst = none →
      peerKey sender = none ∨ terminableB I.desc (tname sender) = false) :
    OccInv I (enqueueOrPark w I.desc sender dst msg isCall (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | ⟨_, _, rfl⟩ <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_park_other w I.desc sender dst msg isCall (afterHead k) hlive hne hroom]
  let entry : Parked :=
    { sender := sender, msg := { msg with mid := (w.st dst).nextMid }, isCall := isCall }
  let aD : Actor := { (w.st dst) with parked := (w.st dst).parked ++ [entry], nextMid := (w.st dst).nextMid + 1 }
  let charged := chargeSender (w.st sender) (tname dst)
  let aS : Actor :=
    { (if isCall then issueCall charged else charged) with phase := .parked dst isCall (afterHead k) }
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by simpa [aS, aD, entry, charged] using this
  apply occ_two I w sender dst aS aD (tname dst) hO hne
  · simp [aS, charged, hcl]
  · simp [aD]
  · simp [aS, charged, hcty]
  · simp [aD]
  · simp [aD]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname dst)).tokens d := by simp [aS, charged]
    rw [htk]
    exact charge_tok (w.st sender) (tname dst) d htok1
  · intro d; simp [aD]
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS dst isCall (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inl (by simp [aS, charged]))
    exact pending_drop (w.st sender) aS k e es (tname dst) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_other_park w.st (tname dst) sender dst aS aD entry w.roster hO.nodup hdst hmem hne rfl rfl
      (by simp [aS, charged, hcb]) (by simp [aS, charged, hcp]) (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, charged, hcb]) (by simp [aS, charged, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box := by simpa [aD] using hm
    exact hO.sentFrom dst m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom dst p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, hcp] using hp
    exact hO.parkMsg sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkMsg dst p h
    | inr h => simp [h, entry, hmsg]
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1 ⊢
      simp [aS, charged, hcp]
      exact hO.clear sender hl1
    · by_cases hd : i = dst
      · rw [hd] at hl1
        exact absurd (l1_park_unreachable I hL w hO hT sender dst hlive hmem hsender hpend1 hl1
          hagree) hroom
      · simp [hs, hd]
        exact hO.clear i hl1
  · exact hmem
  · exact hdst
  · exact hsender
  · exact hnot
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, hcb] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro m hm
    have hm' : m ∈ (w.st dst).box := by simpa [aD] using hm
    exact (hO.sameKey dst).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact (hO.sameKey dst).2 p hp'
    · simp [hp', entry]
      exact queueOk_alive w sender dst hagree hsender
  · intro hdead
    exact absurd (by simp [aS, charged, hcl]; exact hsender) hdead
  · intro hdead
    exact absurd (by simp [aD]; exact hlive) hdead
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st sender).box := by simpa [aS, charged, hcb] using hm
      exact (hO.coreFrom sender hk).1 m hm'
    · intro p hp
      have hp' : p ∈ (w.st sender).parked := by simpa [aS, charged, hcp] using hp
      exact (hO.coreFrom sender hk).2 p hp'
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st dst).box := by simpa [aD] using hm
      exact (hO.coreFrom dst hk).1 m hm'
    · intro p hp
      have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
      simp [List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · exact (hO.coreFrom dst hk).2 p hp'
      · rcases hcore hk with hpk | hterm
        · exact Or.inl (by simp [hp', entry, hmsg, hpk])
        · exact Or.inr (by simp [hp', entry, hmsg, hterm])

/-- A blocking send or call. The target is charged for when it is alive.
On a Lemma-1 mailbox the park branch contradicts the occupancy invariant. -/
theorem occ_enqueue (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k)
    (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ loneTerminableName I.desc (tname sender))
    (hagree : keyAgrees sender dst)
    (hbulk : bulkScopeOf I.desc (tname sender) (e :: es) = true) :
    OccInv I (enqueueOrPark w I.desc sender dst msg isCall (afterHead k)) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst
    · by_cases hsame : sender = dst
      · subst hsame
        cases isCall with
        | false =>
          exact occ_self_send I w sender msg k e es label hint hO hph hk
            (by
              rcases he with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h))
            hmsg hty hsender hnot hroom.1 hroom.2
        | true =>
          exact occ_self_call I w sender msg k e es label hint hO hph hk he hmsg hsender hnot
            hroom.1 hroom.2
      · cases isCall with
        | false =>
          exact occ_other_send I w sender dst msg k e es label hint hO hph hk
            (by
              rcases he with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h))
            hmsg hty hsender hnot hsame hlive hroom.1 hroom.2 hagree
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive) hbulk
              ⟨label, hint, by
                rcases he with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)⟩ hk)
        | true =>
          exact occ_other_call I w sender dst msg k e es label hint hO hph hk he hmsg hsender hnot
            hsame hlive hroom.1 hroom.2 hagree
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive) hbulk
              ⟨label, hint, by
                rcases he with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)⟩ hk)
    · by_cases hsame : sender = dst
      · subst hsame
        exact occ_self_park I hL w sender msg isCall k e es label hint hO hT hph hk he hmsg hsender hnot
          hroom
      · exact occ_other_park I hL w sender dst msg isCall k e es label hint hO hT hph hk he hmsg
          hsender hnot hsame hlive hagree hroom
          (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive) hbulk
            ⟨label, hint, by
              rcases he with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)⟩ hk)
  · cases isCall with
    | false =>
      rw [enqueue_dead w I.desc sender dst msg (afterHead k) hlive]
      exact occ_advance I w sender k hO hty hph
    | true =>
      rw [enqueue_miss w I.desc sender dst msg (afterHead k) hlive]
      let aS : Actor := finishCall (issueCall (w.st sender)) (afterHead k) .notAdmitted
        suffices OccInv I (setActor w sender aS) by simpa [aS] using this
        apply occ_keep I w sender aS hO (finishCall_life _ _ _)
          (by cases hr : (afterHead k).rest <;> simp [aS, finishCall, proceed, hr])
          (by cases hr : (afterHead k).rest <;> simp [aS, finishCall, proceed, hr])
          (by intro d; cases hr : (afterHead k).rest <;> simp [aS, finishCall, proceed, hr])
          (by
            cases ht : k.rest.tail <;> simp [aS, finishCall, proceed, afterHead, ht, hty])
          (by
            intro d
            have hp : pending aS d = pending (proceed (w.st sender) (afterHead k)) d := by
              cases hr : (afterHead k).rest <;> simp [aS, finishCall, proceed, pending, contRest, hr]
            exact Nat.le_trans (Nat.le_of_eq hp)
              ((proceed_tail (w.st sender) k d hty (by simp [contRest, hph])).1))

theorem occ_schedule (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (label : String)
    (hO : OccInv I w) (ha : a = w.st id) (hph : a.phase = .run k) (hty : a.typestate = k.toState) :
    OccInv I
      (let cap := capPrio I.desc w.N id
      let msg : Msg :=
        { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
      let k' := afterHead k
      if a.prio.any (fun p => p.label == label) then setActor w id (proceed a k')
      else if prioLoad a.prio < cap then
        setActor w id (proceed { a with prio := upsertPrio a.prio msg, nextMid := a.nextMid + 1 } k')
      else setActor w id { a with phase := .crashed }) := by
  let msg : Msg :=
    { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
  cases hb : a.prio.any (fun p => p.label == label) with
  | true =>
    simp [hb, ha]
    exact occ_advance I w id k hO (by simpa [ha] using hty) (by simpa [ha] using hph)
  | false =>
    by_cases hlen : prioLoad a.prio < capPrio I.desc w.N id
    · simp [hb, hlen]
      let base : Actor := { a with prio := upsertPrio a.prio msg, nextMid := a.nextMid + 1 }
      let aS : Actor := proceed base (afterHead k)
      suffices OccInv I (setActor w id aS) by simpa [aS, base, msg] using this
      apply occ_keep I w id aS hO
      · simp [aS, base, proceed_life, ha]
      · simp [aS, base, proceed_box, ha]
      · simp [aS, base, proceed_parked, ha]
      · intro d; simp [aS, base, proceed_tokens, ha]
      · have hbase : base.typestate = (afterHead k).toState := by
          simp [base, afterHead]
          exact hty
        have htyS : aS.typestate = a.typestate := by
          simpa [aS, base] using proceed_ty_keep base (afterHead k) hbase
        simpa [ha] using htyS
      · intro d
        have htyb : base.typestate = k.toState := by simp [base]; exact hty
        have hrest : contRest base.phase = k.rest := by simp [base, contRest, hph]
        have htail := proceed_tail base k d htyb hrest
        have hbpend : pending base d = pending (w.st id) d := by
          simp [pending, base, contRest, hph, ha]
        simpa [aS, hbpend] using htail.1
    · simp [hb, hlen]
      apply occ_keep I w id ({ a with phase := .crashed }) hO
      · simp [ha]
      · simp [ha]
      · simp [ha]
      · intro d; simp [ha]
      · simp [ha]
      · intro d
        rw [ha] at hph
        simp [pending, contRest, hph]
        exact Nat.zero_le _

theorem occ_cell (I : Impl) (w : World) (id : InstId) (k : Cont) (dst label : String) (value : Nat)
    (hO : OccInv I w) (hph : (w.st id).phase = .run k) (hty : (w.st id).typestate = k.toState) :
    OccInv I
      (let previous := w.cell dst label
      let written := max previous.value value
      let w := setCell w dst label { value := written, dirty := true }
      let w := setActor w id (proceed (w.st id) (afterHead k))
      if previous.dirty then w else wakeReaders I.desc w dst label id) := by
  let previous := w.cell dst label
  let written := max previous.value value
  let w1 := setCell w dst label { value := written, dirty := true }
  have hO1 := occ_same I w w1 hO (fun i => occ_cell_st w dst label { value := written, dirty := true } i)
    (occ_cell_roster w dst label { value := written, dirty := true }).1
    (occ_cell_roster w dst label { value := written, dirty := true }).2
    (fun n => occ_cell_ix w dst label { value := written, dirty := true } n)
  have hO2 := occ_advance I w1 id k hO1
    (by simpa [w1, occ_cell_st] using hty) (by simpa [w1, occ_cell_st] using hph)
  let w2 := setActor w1 id (proceed (w1.st id) (afterHead k))
  have hO2' : OccInv I w2 := by simpa [w2] using hO2
  cases hdirty : previous.dirty with
  | true => simpa [previous, written, w1, w2, hdirty] using hO2'
  | false =>
    simpa [previous, written, w1, w2, hdirty, wakeReaders] using
      occ_wakes I (readersOf w2 dst) w2 dst label id hO2'

theorem read_roster (D : Description) (w : World) (id : InstId) :
    (readCells D w id).roster = w.roster ∧ (readCells D w id).N = w.N := by
  unfold readCells
  induction cellLabels D (tname id) generalizing w with
  | nil => simp
  | cons _ ls ih =>
    simp only [List.foldl_cons, setCell, setObserved]
    exact ih _

theorem sum_snoc (f : InstId → Nat) (ids : List InstId) (id : InstId) :
    sumFold f (ids ++ [id]) = sumFold f ids + f id := by
  induction ids with
  | nil => simp [sumFold]
  | cons j js ih => simp [sumFold, ih, Nat.add_assoc]

theorem slot_blank (st : InstId → Actor) (dstName : String) (sender id : InstId)
    (hb : (st id).box = []) (hp : (st id).parked = []) : slot st dstName sender id = 0 := by
  simp [slot, hb, hp, countFrom, countParked]

theorem owed_snoc_blank (st : InstId → Actor) (dstName : String) (sender : InstId) (ids : List InstId)
    (id : InstId) (hb : (st id).box = []) (hp : (st id).parked = []) :
    owed st dstName sender (ids ++ [id]) = owed st dstName sender ids := by
  rw [owed_append]
  simp [slot_blank st dstName sender id hb hp]

theorem countParked_out (sender : InstId) :
    ∀ ps : List Parked, (∀ p ∈ ps, p.sender ≠ sender) → countParked sender ps = 0
  | [], _ => rfl
  | p :: ps, h => by
    have hp : p.sender ≠ sender := h p (List.Mem.head _)
    have ht := countParked_out sender ps (fun p' hp' => h p' (List.Mem.tail _ hp'))
    simp [countParked, hp, ht]

theorem owed_out (st : InstId → Actor) (dstName : String) (sender : InstId) :
    ∀ ids : List InstId,
      (∀ id ∈ ids, (∀ m ∈ (st id).box, m.sender ≠ sender) ∧ (∀ p ∈ (st id).parked, p.sender ≠ sender)) →
        owed st dstName sender ids = 0
  | [], _ => rfl
  | id :: ids, h => by
    have hid := h id (List.Mem.head _)
    have hids := owed_out st dstName sender ids (fun i hi => h i (List.Mem.tail _ hi))
    have hbox := countFrom_out sender (st id).box hid.1
    have hpark := countParked_out sender (st id).parked hid.2
    simp [owed, slot, hbox, hpark, hids]

theorem occ_spawn (I : Impl) (w w' : World) (template : String) (hO : OccInv I w)
    (h : spawn I w template = some w') : OccInv I w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    by_cases hif : (t.multiplicity == .perPeer && decide (aliveCount w template < w.N)) = true
    · simp [hif] at h
      cases h
      simp [Bool.and_eq_true] at hif
      have hper : t.multiplicity = .perPeer := by
        cases hm : t.multiplicity with
        | perPeer => rfl
        | one =>
          simp [hm] at hif
          cases hif.1
      have hlt : aliveCount w template < w.N := hif.2
      let pid := InstId.peer template (w.nextIx template)
      let born := bornPeer I template t.initial
      let wG := growRoster w pid template
      let wA := setActor wG pid born
      let wF := readCells I.desc wA pid
      have hfresh : pid ∉ w.roster := by
        intro hin
        have hix := hO.indexed template (w.nextIx template) hin
        omega
      have hst : ∀ i, wF.st i = if i = pid then born else w.st i := by
        intro i
        simp only [wF]
        rw [readCells_st]
        simp [wA, setActor, wG, growRoster]
      have hrost : wF.roster = w.roster ++ [pid] := by
        simp only [wF]
        rw [(read_roster I.desc wA pid).1]
        simp [wA, setActor, wG, growRoster]
      have hN : wF.N = w.N := by
        simp only [wF]
        rw [(read_roster I.desc wA pid).2]
        simp [wA, setActor, wG, growRoster]
      have hixn : ∀ n, wF.nextIx n = if n = template then w.nextIx n + 1 else w.nextIx n := by
        intro n
        simp only [wF]
        rw [read_ix, actor_ix]
        simp [wA, wG, growRoster]
      have hborn : born.life = .alive ∧ born.box = [] ∧ born.parked = [] ∧ born.phase = .idle ∧
          born.typestate = t.initial ∧ ∀ d, born.tokens d = budget I.desc template d := by
        simp [born, bornPeer, withTokens]
      have hblank : (wF.st pid).box = [] ∧ (wF.st pid).parked = [] := by
        have hs := hst pid
        simp [hs, hborn]
      suffices OccInv I wF by simpa [wF, wA, wG, pid, born, growRoster, bornPeer, withTokens] using this
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrost]
        exact nodup_snoc hO.nodup hfresh
      · intro i hl
        rw [hrost]
        by_cases hi : i = pid
        · exact List.mem_append.mpr (Or.inr (by rw [hi]; exact List.Mem.head []))
        · rw [hst i] at hl
          simp [hi] at hl
          exact List.mem_append.mpr (Or.inl (hO.aliveIn i hl))
      · intro name i hi
        rw [hixn]
        rw [hrost] at hi
        simp [List.mem_append, List.mem_singleton] at hi
        cases hi with
        | inl hold =>
          have hold' := hO.indexed name i hold
          by_cases hn : name = template
          · rw [hn] at hold' ⊢
            simp
            exact Nat.lt_succ_of_lt hold'
          · simp [hn]
            exact hold'
        | inr hnew =>
          simp [pid] at hnew
          simp [hnew.1, hnew.2]
      · intro name hone
        by_cases hn : name = template
        · rw [hn] at hone
          obtain ⟨tmpl, htn, hm⟩ := hone
          have heq : tmpl = t := by
            rw [ht] at htn
            cases htn
            rfl
          rw [heq, hper] at hm
          cases hm
        · have hc : aliveCount wF name = aliveCount w name := by
            rw [aliveCount_sum, aliveCount_sum, hrost]
            rw [sum_snoc]
            have hbit : aliveBit wF.st name pid = 0 := by
              unfold aliveBit
              rw [hst pid]
              simp [pid, tname, hborn, show template ≠ name from fun h => hn h.symm]
            have hfold : sumFold (aliveBit wF.st name) w.roster = sumFold (aliveBit w.st name) w.roster := by
              refine sum_congr _ _ w.roster ?_
              intro i hi
              have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
              simp [aliveBit, hst i, hne]
            rw [hbit, hfold]
            simp
          rw [hc]
          exact hO.liveOne name hone
      · intro name hpeer
        by_cases hn : name = template
        · rw [hn]
          have hc : aliveCount wF template = aliveCount w template + 1 := by
            rw [aliveCount_sum, aliveCount_sum, hrost]
            rw [sum_snoc]
            have hbit : aliveBit wF.st template pid = 1 := by
              unfold aliveBit
              rw [hst pid]
              simp [pid, tname, hborn]
            have hfold : sumFold (aliveBit wF.st template) w.roster =
                sumFold (aliveBit w.st template) w.roster := by
              refine sum_congr _ _ w.roster ?_
              intro i hi
              have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
              simp [aliveBit, hst i, hne]
            rw [hbit, hfold]
          rw [hc, hN]
          omega
        · have hc : aliveCount wF name = aliveCount w name := by
            rw [aliveCount_sum, aliveCount_sum, hrost]
            rw [sum_snoc]
            have hbit : aliveBit wF.st name pid = 0 := by
              unfold aliveBit
              rw [hst pid]
              simp [pid, tname, hborn, show template ≠ name from fun h => hn h.symm]
            have hfold : sumFold (aliveBit wF.st name) w.roster = sumFold (aliveBit w.st name) w.roster := by
              refine sum_congr _ _ w.roster ?_
              intro i hi
              have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
              simp [aliveBit, hst i, hne]
            rw [hbit, hfold]
            simp
          rw [hc, hN]
          exact hO.livePeer name hpeer
      · intro i hnin
        rw [hrost] at hnin
        have hnin' : i ∉ w.roster := fun hin => hnin (List.mem_append.mpr (Or.inl hin))
        have hne : i ≠ pid := fun heq => hnin (List.mem_append.mpr (Or.inr (by rw [heq]; exact List.Mem.head [])))
        have hold := hO.offEmpty i hnin'
        rw [hst i]
        simp [hne]
        exact hold
      · intro i m hm
        rw [hrost]
        rw [hst i] at hm
        by_cases hi : i = pid
        · simp [hi, hborn] at hm
        · simp [hi] at hm
          exact List.mem_append.mpr (Or.inl (hO.sentFrom i m hm))
      · intro i p hp
        rw [hrost]
        rw [hst i] at hp
        by_cases hi : i = pid
        · simp [hi, hborn] at hp
        · simp [hi] at hp
          exact List.mem_append.mpr (Or.inl (hO.parkFrom i p hp))
      · intro i p hp
        rw [hst i] at hp
        by_cases hi : i = pid
        · simp [hi, hborn] at hp
        · simp [hi] at hp
          exact hO.parkMsg i p hp
      · intro s d hs
        rw [hrost] at hs
        simp [List.mem_append, List.mem_singleton] at hs
        by_cases hss : s = pid
        · rw [hss]
          have hzero : owed wF.st d pid wF.roster = 0 := by
            rw [hrost]
            apply owed_out
            intro i hi
            simp [List.mem_append, List.mem_singleton] at hi
            cases hi with
            | inl hold =>
              constructor
              · intro m hm
                rw [hst i] at hm
                have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hold)
                simp [hne] at hm
                intro heq
                exact hfresh (heq ▸ hO.sentFrom i m hm)
              · intro p hp
                rw [hst i] at hp
                have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hold)
                simp [hne] at hp
                intro heq
                exact hfresh (heq ▸ hO.parkFrom i p hp)
            | inr hnew =>
              cases hnew
              rw [hst pid]
              simp [hborn]
          have htok : (wF.st pid).tokens d = budget I.desc (tname pid) d := by
            rw [hst pid]
            simp [hborn, pid, tname]
          rw [hzero, htok]
          simp
        · have hs0 : s ∈ w.roster := by
            cases hs with
            | inl h => exact h
            | inr h => exact absurd h hss
          have howed : owed wF.st d s wF.roster = owed w.st d s w.roster := by
            rw [hrost]
            have hblankPid : (wF.st pid).box = [] ∧ (wF.st pid).parked = [] := hblank
            have hstep := owed_snoc_blank wF.st d s w.roster pid hblankPid.1 hblankPid.2
            rw [hstep]
            refine owed_mail_eq _ _ _ _ w.roster ?_
            intro i hi
            have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
            rw [hst i]
            simp [hne]
          have htok : (wF.st s).tokens d = (w.st s).tokens d := by
            rw [hst s]
            simp [hss]
          rw [howed, htok]
          exact hO.balance s d hs0
      · intro s d hs hl
        rw [hrost] at hs
        by_cases hss : s = pid
        · rw [hss] at hl ⊢
          rw [hst pid] at hl ⊢
          simp [hborn] at hl ⊢
          simp [pending, contRest]
          exact floor_le_budget I.desc template t.initial d
        · have hs0 : s ∈ w.roster := by
            simp [List.mem_append, List.mem_singleton] at hs
            cases hs with
            | inl h => exact h
            | inr h => exact absurd h hss
          have hphs : (wF.st s).phase = (w.st s).phase := by rw [hst s]; simp [hss]
          have htys : (wF.st s).typestate = (w.st s).typestate := by rw [hst s]; simp [hss]
          have hl0 : (w.st s).life = .alive := by
            rw [hst s] at hl
            simp [hss] at hl
            exact hl
          have hold := hO.slack s d hs0 hl0
          have hpend : pending (wF.st s) d = pending (w.st s) d := by simp [pending, hphs]
          have hfloor : floorState I.desc (tname s) (wF.st s).typestate d =
              floorState I.desc (tname s) (w.st s).typestate d := by rw [htys]
          have htok : (wF.st s).tokens d = (w.st s).tokens d := by rw [hst s]; simp [hss]
          rw [hpend, hfloor, htok]
          exact hold
      · intro s d hs hterm
        rw [hrost] at hs ⊢
        by_cases hss : s = pid
        · rw [hss]
          have hzero := owed_out wF.st d pid (w.roster ++ [pid]) (by
            intro i hi
            simp [List.mem_append, List.mem_singleton] at hi
            cases hi with
            | inl hold =>
              constructor
              · intro m hm
                have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hold)
                rw [hst i] at hm
                simp [hne] at hm
                intro heq
                exact hfresh (heq ▸ hO.sentFrom i m hm)
              · intro p hp
                have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hold)
                rw [hst i] at hp
                simp [hne] at hp
                intro heq
                exact hfresh (heq ▸ hO.parkFrom i p hp)
            | inr hnew =>
              cases hnew
              rw [hst pid]
              simp [hborn])
          exact hzero
        · have hs0 : s ∈ w.roster := by
            simp [List.mem_append, List.mem_singleton] at hs
            cases hs with
            | inl h => exact h
            | inr h => exact absurd h hss
          have h0 := hO.still s d hs0 hterm
          have howed : owed wF.st d s (w.roster ++ [pid]) = owed w.st d s w.roster := by
            have hstep := owed_snoc_blank wF.st d s w.roster pid hblank.1 hblank.2
            rw [hstep]
            refine owed_mail_eq _ _ _ _ w.roster ?_
            intro i hi
            have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
            rw [hst i]
            simp [hne]
          rw [howed, h0]
      · intro s d hs hdead
        rw [hrost] at hs
        by_cases hss : s = pid
        · rw [hss] at hdead
          rw [hst pid] at hdead
          simp [hborn] at hdead
        · have hs0 : s ∈ w.roster := by
            simp [List.mem_append, List.mem_singleton] at hs
            cases hs with
            | inl h => exact h
            | inr h => exact absurd h hss
          have hdead0 : (w.st s).life ≠ .alive := by
            rw [hst s] at hdead
            simp [hss] at hdead
            exact hdead
          have h0 := hO.quiet s d hs0 hdead0
          rw [hrost]
          have howed : owed wF.st d s (w.roster ++ [pid]) = owed w.st d s w.roster := by
            have hstep := owed_snoc_blank wF.st d s w.roster pid hblank.1 hblank.2
            rw [hstep]
            refine owed_mail_eq _ _ _ _ w.roster ?_
            intro i hi
            have hne : i ≠ pid := fun heq => hfresh (by rw [← heq]; exact hi)
            rw [hst i]
            simp [hne]
          rw [howed]; exact h0
      · intro i hl1
        by_cases hi : i = pid
        · rw [hi]
          rw [hst pid]
          simp [hborn]
        · rw [hst i]
          simp [hi]
          exact hO.clear i hl1
      · intro i hdead
        by_cases hi : i = pid
        · rw [hi] at hdead
          rw [hst pid] at hdead
          simp [hborn] at hdead
        · rw [hst i] at hdead ⊢
          simp [hi] at hdead ⊢
          exact hO.deadEmpty i hdead
      · intro host
        refine ⟨?_, ?_⟩
        · intro m hm
          rw [hst host] at hm
          by_cases hi : host = pid
          · simp [hi, hborn] at hm
          · simp [hi] at hm
            have hne : m.sender ≠ pid := by
              intro heq
              exact hfresh (heq ▸ hO.sentFrom host m hm)
            have hlife : (wF.st m.sender).life = (w.st m.sender).life := by
              rw [hst m.sender]
              simp [hne]
            exact (queueOk_life w wF m.sender host hlife).1 ((hO.sameKey host).1 m hm)
        · intro p hp
          rw [hst host] at hp
          by_cases hi : host = pid
          · simp [hi, hborn] at hp
          · simp [hi] at hp
            have hne : p.sender ≠ pid := by
              intro heq
              exact hfresh (heq ▸ hO.parkFrom host p hp)
            have hlife : (wF.st p.sender).life = (w.st p.sender).life := by
              rw [hst p.sender]
              simp [hne]
            exact (queueOk_life w wF p.sender host hlife).1 ((hO.sameKey host).2 p hp)
      · intro i hi
        rw [hrost] at hi
        simp [List.mem_append, List.mem_singleton] at hi
        cases hi with
        | inl hold => exact hO.shaped i hold
        | inr hnew =>
          cases hnew
          have hname := templateOf_name I.desc template t ht
          refine ⟨t, ?_, ?_⟩
          · simp [pid, tname, hname, ht]
          · simp [hper, pid, hname]
      · intro host hk
        refine ⟨?_, ?_⟩
        · intro m hm
          have hs := hst host
          by_cases hh : host = pid
          · have hempty : born.box = [] := hborn.2.1
            rw [hs, hh] at hm
            simp only [if_true] at hm
            rw [hempty] at hm
            simp at hm
          · rw [hs, if_neg hh] at hm
            exact (hO.coreFrom host hk).1 m hm
        · intro p hp
          have hs := hst host
          by_cases hh : host = pid
          · have hempty : born.parked = [] := hborn.2.2.1
            rw [hs, hh] at hp
            simp only [if_true] at hp
            rw [hempty] at hp
            simp at hp
          · rw [hs, if_neg hh] at hp
            exact (hO.coreFrom host hk).2 p hp
    · simp [hif] at h

theorem try_fit_self (w : World) (id : InstId) (msg : Msg) (k : Cont) :
    let a' := chargeSender (w.st id) (tname id)
    let w1 := setActor w id a'
    let stored :=
      { (w1.st id) with box := (w1.st id).box ++ [msg], nextMid := (w1.st id).nextMid + 1 }
    setActor (setActor w1 id stored) id (proceed ((setActor w1 id stored).st id) k) =
      setActor w id (proceed { a' with box := a'.box ++ [msg], nextMid := a'.nextMid + 1 } k) := by
  simp only [setActor]
  congr 1
  funext i
  by_cases hi : i = id <;> simp [hi]

theorem try_fit_other (w : World) (id dst : InstId) (msg : Msg) (k : Cont) (hne : id ≠ dst) :
    let a' := chargeSender (w.st id) (tname dst)
    let w1 := setActor w id a'
    let stored :=
      { (w1.st dst) with box := (w1.st dst).box ++ [msg], nextMid := (w1.st dst).nextMid + 1 }
    setActor (setActor w1 dst stored) id (proceed ((setActor w1 dst stored).st id) k) =
      setActor (setActor w dst { (w.st dst) with box := (w.st dst).box ++ [msg], nextMid := (w.st dst).nextMid + 1 }) id (proceed a' k) := by
  simp only [setActor, hne]
  congr 1
  funext i
  by_cases hi : i = id
  · simp [hi]
  · have hne' : dst ≠ id := fun h => hne h.symm
    simp [hi, hne']

/-- Occupancy talks about the roster and actor map. Failures and the tombstone do not. -/
theorem occ_of_core (I : Impl) (w1 w2 : World) (hN : w1.N = w2.N) (hr : w1.roster = w2.roster)
    (hix : w1.nextIx = w2.nextIx) (hst : w1.st = w2.st) (h : OccInv I w1) : OccInv I w2 := by
  rcases h with ⟨nodup, aliveIn, indexed, liveOne, livePeer, offEmpty, sentFrom, parkFrom, parkMsg,
      balance, slack, still, quiet, clear, deadEmpty, sameKey, shaped, coreFrom⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hr]; exact nodup
  · intro id hlife
    rw [← hr]
    apply aliveIn
    rwa [hst]
  · intro t i hmem
    rw [← hix]
    apply indexed
    rwa [hr]
  · intro t ht
    have hc : aliveCount w2 t = aliveCount w1 t := by simp [aliveCount, hst, hr]
    rw [hc]
    exact liveOne t ht
  · intro t ht
    have hc : aliveCount w2 t = aliveCount w1 t := by simp [aliveCount, hst, hr]
    rw [hc, ← hN]
    exact livePeer t ht
  · intro id hnin
    have hnin1 : id ∉ w1.roster := by rwa [hr]
    rw [← hst]
    exact offEmpty id hnin1
  · intro id m hm
    rw [← hr]
    apply sentFrom
    rwa [hst]
  · intro id p hp
    rw [← hr]
    apply parkFrom
    rwa [hst]
  · intro id p hp
    apply parkMsg
    rwa [hst]
  · intro s d hs
    rw [← hst, ← hr]
    apply balance
    rwa [hr]
  · intro s d hs hl
    rw [← hst]
    apply slack
    · rwa [hr]
    · rwa [hst]
  · intro s d hs hterm
    rw [← hst, ← hr]
    apply still
    · rwa [hr]
    · exact hterm
  · intro s d hs hl
    rw [← hst, ← hr]
    apply quiet
    · rwa [hr]
    · rwa [hst]
  · intro id hl1
    rw [← hst]
    exact clear id hl1
  · intro id hdead
    rw [← hst] at hdead ⊢
    exact deadEmpty id hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [← hst] at hm
      exact (queueOk_life w1 w2 m.sender host (by rw [hst])).1 ((sameKey host).1 m hm)
    · intro p hp
      rw [← hst] at hp
      exact (queueOk_life w1 w2 p.sender host (by rw [hst])).1 ((sameKey host).2 p hp)
  · intro id hid
    exact shaped id (by rw [← hr] at hid; exact hid)
  · intro host hk
    rw [← hst]
    exact coreFrom host hk

theorem occ_note (I : Impl) (w : World) (id : InstId) (dst : String) (a : Actor)
    (h : OccInv I (setActor w id a)) : OccInv I (setActor (noteStale w id dst) id a) := by
  apply occ_of_core I (setActor w id a) (setActor (noteStale w id dst) id a) _ _ _ _ h
  · simp [setActor, noteStale]
  · simp [setActor, noteStale]
  · simp [setActor, noteStale]
  · funext i
    simp [setActor, noteStale]

/-- A `trySend` that fits spends one token and stores the message.
A miss, a dead target, or a full mailbox continues without a charge. -/
theorem occ_try (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (k : Cont)
    (dstName label : String) (hint : Nat) (onFull onGone es : List Eff) (hO : OccInv I w)
    (hT : TyOk I.desc w)
    (hph : (w.st id).phase = .run { k with rest := .trySend dstName label hint onFull onGone :: es })
    (hty : (w.st id).typestate = k.toState) (hsender : (w.st id).life = .alive)
    (hnot : ¬ loneTerminableName I.desc (tname id))
    (hbulk : bulkScopeOf I.desc (tname id) (.trySend dstName label hint onFull onGone :: es) = true) :
    OccInv I (execRun I w id (w.st id) { k with rest := .trySend dstName label hint onFull onGone :: es }) := by
  let cont : Cont := { k with rest := .trySend dstName label hint onFull onGone :: es }
  have hph' : (w.st id).phase = .run cont := by simpa [cont] using hph
  have hty' : (w.st id).typestate = cont.toState := by simpa [cont] using hty
  simp [execRun, cont]
  cases hr : route w I.desc id dstName with
  | none =>
    simp [hr]
    exact occ_note I w id dstName (proceed (w.st id) (afterHead cont))
      (occ_advance I w id cont hO hty' hph')
  | some dst =>
    simp [hr]
    have hname := route_tname w I.desc id dstName dst hr
    split
    · next hcond =>
      have hlive : (w.st dst).life = .alive := hcond.1.1
      have hpark : (w.st dst).parked = [] := hcond.1.2
      have hcap : (w.st dst).box.length < capBulk I.desc w.N dst := hcond.2
      let msg : Msg := { label := label, sender := id, callFrom := none, reliable := false }
      have he : Eff.trySend dstName label hint onFull onGone = Eff.trySend (tname dst) label hint onFull onGone := by rw [hname]
      by_cases hsame : id = dst
      · subst hsame
        exact occ_self_send I w id msg cont (.trySend dstName label hint onFull onGone) es label hint hO
          hph' rfl (Or.inr (Or.inr ⟨onFull, onGone, he⟩)) rfl hty' hsender hnot hpark hcap
      · exact occ_other_send I w id dst msg cont (.trySend dstName label hint onFull onGone) es label hint hO
          hph' rfl (Or.inr (Or.inr ⟨onFull, onGone, he⟩)) rfl hty' hsender hnot hsame hlive hpark hcap
          (route_agrees w I.desc id dstName dst hr)
          (fun hk => core_send_from I w hO id dst (.trySend (tname dst) label hint onFull onGone) es
            (hO.aliveIn dst hlive) (by simpa [he] using hbulk)
            ⟨label, hint, Or.inr (Or.inr ⟨onFull, onGone, rfl⟩)⟩ hk)
    · exact occ_advance I w id cont hO hty' hph'

def drainBox (w : World) (id : InstId) (dst : String) : List Msg → World
  | [] => setActor w id { (w.st id) with box := [] }
  | m :: ms =>
    drainBox (creditSender (setActor w id { (w.st id) with box := ms }) dst m.sender) id dst ms

def refundClearBox (w : World) (id : InstId) (dst : String) (ms : List Msg) : World :=
  let wR := refundMsgs w dst ms
  setActor wR id { (wR.st id) with box := [] }

theorem credit_tok (w : World) (dst : String) (sender i : InstId) (d : String) :
    ((creditSender w dst sender).st i).tokens d =
      (w.st i).tokens d + if i = sender ∧ d = dst then 1 else 0 := by
  by_cases hi : i = sender
  · subst hi
    rw [creditSender, setActor_self, bump_add]
    by_cases hd : d = dst <;> simp [hd]
  · rw [creditSender, setActor_other w sender i _ hi]
    simp [hi]

theorem credit_box (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).box = (w.st i).box := by
  by_cases hi : i = sender
  · simp [creditSender, setActor, hi, bumpToken]
  · simp [creditSender, setActor_other w sender i _ hi]

theorem credit_park (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).parked = (w.st i).parked := by
  by_cases hi : i = sender
  · simp [creditSender, setActor, hi, bumpToken]
  · simp [creditSender, setActor_other w sender i _ hi]

theorem credit_life (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).life = (w.st i).life ∧
      ((creditSender w dst sender).st i).typestate = (w.st i).typestate ∧
      ((creditSender w dst sender).st i).phase = (w.st i).phase ∧
      ((creditSender w dst sender).st i).prio = (w.st i).prio := by
  by_cases hi : i = sender
  · simp [creditSender, setActor, hi, bumpToken]
  · simp [creditSender, setActor_other w sender i _ hi]

theorem refund_tok (w : World) (dst : String) (ms : List Msg) (i : InstId) (d : String) :
    ((refundMsgs w dst ms).st i).tokens d =
      (w.st i).tokens d + if d = dst then countFrom i ms else 0 := by
  induction ms generalizing w with
  | nil => simp [refundMsgs, countFrom]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_tok, countFrom]
    by_cases hd : d = dst
    · by_cases hs : m.sender = i
      · simp [hd, hs, Nat.add_assoc]
      · have hne : i ≠ m.sender := fun h => hs h.symm
        simp [hd, hne, Nat.zero_add]
        exact hs
    · simp [hd]

theorem refund_box (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).box = (w.st i).box := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_box]

theorem refund_park (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_park]

theorem refund_life (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).life = (w.st i).life ∧
      ((refundMsgs w dst ms).st i).typestate = (w.st i).typestate ∧
      ((refundMsgs w dst ms).st i).phase = (w.st i).phase ∧
      ((refundMsgs w dst ms).st i).prio = (w.st i).prio := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold]
    have hc := credit_life w dst m.sender i
    have hi := ih (creditSender w dst m.sender)
    simp [hc] at hi
    exact hi

theorem clear_tok (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) (d : String) :
    ((refundClearBox w id dst ms).st i).tokens d =
      (w.st i).tokens d + if d = dst then countFrom i ms else 0 := by
  simp [refundClearBox, setActor]
  by_cases hi : i = id
  · simp [hi, refund_tok]
  · simp [hi, refund_tok]

theorem clear_box (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundClearBox w id dst ms).st i).box = if i = id then [] else (w.st i).box := by
  simp [refundClearBox, setActor]
  by_cases hi : i = id
  · simp [hi]
  · simp [hi, refund_box]

theorem clear_park (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundClearBox w id dst ms).st i).parked = (w.st i).parked := by
  by_cases hi : i = id
  · simp [refundClearBox, setActor, hi, refund_park]
  · simp [refundClearBox, setActor, hi, refund_park]

theorem clear_life (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundClearBox w id dst ms).st i).life = (w.st i).life ∧
      ((refundClearBox w id dst ms).st i).typestate = (w.st i).typestate ∧
      ((refundClearBox w id dst ms).st i).phase = (w.st i).phase ∧
      ((refundClearBox w id dst ms).st i).prio = (w.st i).prio := by
  simp [refundClearBox, setActor]
  by_cases hi : i = id
  · simp [hi, refund_life]
  · simp [hi, refund_life]

theorem drain_tok (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) (d : String) :
    ((drainBox w id dst ms).st i).tokens d =
      (w.st i).tokens d + if d = dst then countFrom i ms else 0 := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor, countFrom]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox, countFrom]
    have hset : ∀ j, ((setActor w id { (w.st id) with box := ms }).st j).tokens d = (w.st j).tokens d := by
      intro j
      by_cases hj : j = id <;> simp [setActor, hj]
    have hcred := credit_tok (setActor w id { (w.st id) with box := ms }) dst m.sender i d
    rw [hset] at hcred
    have hih := ih (creditSender (setActor w id { (w.st id) with box := ms }) dst m.sender)
    rw [hih, hcred]
    by_cases hd : d = dst
    · by_cases hs : m.sender = i
      · simp [hd, hs, Nat.add_assoc]
      · have hne : i ≠ m.sender := fun h => hs h.symm
        simp [hd, hne, Nat.zero_add]
        exact hs
    · simp [hd]

theorem drain_box (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).box = if i = id then [] else (w.st i).box := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox]
    have hbox0 : ((setActor w id { (w.st id) with box := ms }).st i).box =
        if i = id then ms else (w.st i).box := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hcred := credit_box (setActor w id { (w.st id) with box := ms }) dst m.sender i
    rw [ih, hcred, hbox0]
    by_cases hi : i = id <;> simp [hi]

theorem drain_park (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox]
    have hpk : ((setActor w id { (w.st id) with box := ms }).st i).parked = (w.st i).parked := by
      by_cases hi : i = id <;> simp [setActor, hi]
    rw [ih, credit_park, hpk]

theorem drain_life (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).life = (w.st i).life ∧
      ((drainBox w id dst ms).st i).typestate = (w.st i).typestate ∧
      ((drainBox w id dst ms).st i).phase = (w.st i).phase ∧
      ((drainBox w id dst ms).st i).prio = (w.st i).prio := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox]
    have hL : ((setActor w id { (w.st id) with box := ms }).st i).life = (w.st i).life ∧
        ((setActor w id { (w.st id) with box := ms }).st i).typestate = (w.st i).typestate ∧
        ((setActor w id { (w.st id) with box := ms }).st i).phase = (w.st i).phase ∧
        ((setActor w id { (w.st id) with box := ms }).st i).prio = (w.st i).prio := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := credit_life (setActor w id { (w.st id) with box := ms }) dst m.sender i
    have hi := ih (creditSender (setActor w id { (w.st id) with box := ms }) dst m.sender)
    simp [hc, hL] at hi
    exact hi

theorem credit_mid (w : World) (dst : String) (sender i : InstId) :
    ((creditSender w dst sender).st i).nextMid = (w.st i).nextMid := by
  by_cases hi : i = sender
  · subst hi
    simp [creditSender, setActor, bumpToken]
  · simp [creditSender, setActor, hi]

theorem drain_mid (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).nextMid = (w.st i).nextMid := by
  induction ms generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [drainBox, setActor, hi]
  | cons m ms ih =>
    simp [drainBox]
    have hset : ((setActor w id { (w.st id) with box := ms }).st i).nextMid = (w.st i).nextMid := by
      by_cases hi : i = id <;> simp [setActor, hi]
    exact (ih _).trans ((credit_mid _ _ _ _).trans hset)

theorem refund_mid (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).nextMid = (w.st i).nextMid := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    exact (hfold ▸ ih _).trans (credit_mid w dst m.sender i)

theorem clear_mid (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundClearBox w id dst ms).st i).nextMid = (w.st i).nextMid := by
  by_cases hi : i = id <;> simp [refundClearBox, setActor, hi, refund_mid]

/-- Call ids are not touched by a credit, a drain, or a refund. -/
def sameStamps (a b : Actor) : Prop :=
  a.waitId = b.waitId ∧ a.nextCall = b.nextCall ∧ a.oweId = b.oweId ∧ a.lastCall = b.lastCall

theorem sameStamps_trans {a b c : Actor} (h1 : sameStamps a b) (h2 : sameStamps b c) : sameStamps a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem sameStamps_symm {a b : Actor} (h : sameStamps a b) : sameStamps b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem credit_stamps (w : World) (dst : String) (sender i : InstId) :
    sameStamps ((creditSender w dst sender).st i) (w.st i) := by
  by_cases hi : i = sender <;> simp [sameStamps, creditSender, setActor, bumpToken, hi]

theorem drain_stamps (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    sameStamps ((drainBox w id dst ms).st i) (w.st i) := by
  induction ms generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [sameStamps, drainBox, setActor, hi]
  | cons m ms ih =>
    simp [drainBox]
    have hset : sameStamps ((setActor w id { (w.st id) with box := ms }).st i) (w.st i) := by
      by_cases hi : i = id <;> simp [sameStamps, setActor, hi]
    exact sameStamps_trans (ih _) (sameStamps_trans (credit_stamps _ _ _ _) hset)

theorem refund_stamps (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    sameStamps ((refundMsgs w dst ms).st i) (w.st i) := by
  induction ms generalizing w with
  | nil => simp [sameStamps, refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    exact sameStamps_trans (hfold ▸ ih _) (credit_stamps w dst m.sender i)

theorem clear_stamps (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    sameStamps ((refundClearBox w id dst ms).st i) (w.st i) := by
  have hset : sameStamps ((refundClearBox w id dst ms).st i) ((refundMsgs w dst ms).st i) := by
    by_cases hi : i = id <;> simp [sameStamps, refundClearBox, setActor, hi]
  exact sameStamps_trans hset (refund_stamps w dst ms i)

theorem actor_fields (a b : Actor) (hl : a.life = b.life) (ht : a.typestate = b.typestate)
    (hp : a.phase = b.phase) (hb : a.box = b.box) (hpr : a.prio = b.prio) (hpk : a.parked = b.parked)
    (htk : ∀ d, a.tokens d = b.tokens d) (hm : a.nextMid = b.nextMid)
    (hw : a.waitId = b.waitId) (hn : a.nextCall = b.nextCall) (ho : a.oweId = b.oweId)
    (hc : a.lastCall = b.lastCall) : a = b := by
  cases a
  cases b
  cases hl
  cases ht
  cases hp
  cases hb
  cases hpr
  cases hpk
  cases hm
  cases hw
  cases hn
  cases ho
  cases hc
  simp
  funext d
  exact htk d

theorem frame_credit (w : World) (dst : String) (s : InstId) :
    (creditSender w dst s).N = w.N ∧ (creditSender w dst s).roster = w.roster ∧
      (creditSender w dst s).nextIx = w.nextIx ∧ (creditSender w dst s).cell = w.cell ∧
      (creditSender w dst s).observed = w.observed := by
  simp [creditSender, setActor]

theorem frame_refund (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).N = w.N ∧ (refundMsgs w dst ms).roster = w.roster ∧
      (refundMsgs w dst ms).nextIx = w.nextIx ∧ (refundMsgs w dst ms).cell = w.cell ∧
      (refundMsgs w dst ms).observed = w.observed := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditSender w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold]
    have hc := frame_credit w dst m.sender
    have hi := ih (creditSender w dst m.sender)
    exact ⟨hi.1.trans hc.1, hi.2.1.trans hc.2.1, hi.2.2.1.trans hc.2.2.1,
      hi.2.2.2.1.trans hc.2.2.2.1, hi.2.2.2.2.trans hc.2.2.2.2⟩

theorem frame_set (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).N = w.N ∧ (setActor w id a).roster = w.roster ∧
      (setActor w id a).nextIx = w.nextIx ∧ (setActor w id a).cell = w.cell ∧
      (setActor w id a).observed = w.observed := by
  simp [setActor]

theorem frame_drain (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (drainBox w id dst ms).N = w.N ∧ (drainBox w id dst ms).roster = w.roster ∧
      (drainBox w id dst ms).nextIx = w.nextIx ∧ (drainBox w id dst ms).cell = w.cell ∧
      (drainBox w id dst ms).observed = w.observed := by
  induction ms generalizing w with
  | nil => simp [drainBox, setActor]
  | cons m ms ih =>
    simp [drainBox]
    have hs := frame_set w id { (w.st id) with box := ms }
    have hc := frame_credit (setActor w id { (w.st id) with box := ms }) dst m.sender
    have hi := ih (creditSender (setActor w id { (w.st id) with box := ms }) dst m.sender)
    exact ⟨hi.1.trans (hc.1.trans hs.1), hi.2.1.trans (hc.2.1.trans hs.2.1),
      hi.2.2.1.trans (hc.2.2.1.trans hs.2.2.1), hi.2.2.2.1.trans (hc.2.2.2.1.trans hs.2.2.2.1),
      hi.2.2.2.2.trans (hc.2.2.2.2.trans hs.2.2.2.2)⟩

theorem frame_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (refundClearBox w id dst ms).N = w.N ∧ (refundClearBox w id dst ms).roster = w.roster ∧
      (refundClearBox w id dst ms).nextIx = w.nextIx ∧ (refundClearBox w id dst ms).cell = w.cell ∧
      (refundClearBox w id dst ms).observed = w.observed := by
  simp [refundClearBox, setActor, frame_refund]

theorem world_eq (w1 w2 : World) (hN : w1.N = w2.N) (hr : w1.roster = w2.roster)
    (hix : w1.nextIx = w2.nextIx) (hst : w1.st = w2.st) (hc : w1.cell = w2.cell)
    (ho : w1.observed = w2.observed) (hf : w1.failures = w2.failures) : w1 = w2 := by
  cases w1
  cases w2
  cases hN
  cases hr
  cases hix
  cases hst
  cases hc
  cases ho
  cases hf
  rfl

theorem meta_set (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).failures = w.failures := by
  simp [setActor]

theorem meta_credit (w : World) (dst : String) (s : InstId) :
    (creditSender w dst s).failures = w.failures := by
  simp [creditSender, setActor]

theorem meta_refund (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).failures = w.failures := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    simp [refundMsgs, List.foldl_cons]
    exact (ih (creditSender w dst m.sender)).trans (meta_credit w dst m.sender)

theorem meta_drain (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (drainBox w id dst ms).failures = w.failures := by
  induction ms generalizing w with
  | nil => simp [drainBox, setActor]
  | cons m ms ih =>
    simp [drainBox]
    exact (ih (creditSender (setActor w id { (w.st id) with box := ms }) dst m.sender)).trans
      ((meta_credit (setActor w id { (w.st id) with box := ms }) dst m.sender).trans
        (meta_set w id { (w.st id) with box := ms }))

theorem meta_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (refundClearBox w id dst ms).failures = w.failures := by
  simp [refundClearBox, setActor, meta_refund]

/-- Refunding every sender and then clearing the box is the same as dropping
each message and crediting its sender, including when that sender is `id`. -/
theorem drain_eq_refund (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    drainBox w id dst ms = refundClearBox w id dst ms := by
  have hD := frame_drain w id dst ms
  have hC := frame_clear w id dst ms
  have hst : (drainBox w id dst ms).st = (refundClearBox w id dst ms).st := by
    funext i
    apply actor_fields
    · exact (drain_life w id dst ms i).1.trans (clear_life w id dst ms i).1.symm
    · exact (drain_life w id dst ms i).2.1.trans (clear_life w id dst ms i).2.1.symm
    · exact (drain_life w id dst ms i).2.2.1.trans (clear_life w id dst ms i).2.2.1.symm
    · exact (drain_box w id dst ms i).trans (clear_box w id dst ms i).symm
    · exact (drain_life w id dst ms i).2.2.2.trans (clear_life w id dst ms i).2.2.2.symm
    · exact (drain_park w id dst ms i).trans (clear_park w id dst ms i).symm
    · intro d
      exact (drain_tok w id dst ms i d).trans (clear_tok w id dst ms i d).symm
    · exact (drain_mid w id dst ms i).trans (clear_mid w id dst ms i).symm
    · exact (sameStamps_trans (drain_stamps w id dst ms i) (sameStamps_symm (clear_stamps w id dst ms i))).1
    · exact (sameStamps_trans (drain_stamps w id dst ms i) (sameStamps_symm (clear_stamps w id dst ms i))).2.1
    · exact (sameStamps_trans (drain_stamps w id dst ms i) (sameStamps_symm (clear_stamps w id dst ms i))).2.2.1
    · exact (sameStamps_trans (drain_stamps w id dst ms i) (sameStamps_symm (clear_stamps w id dst ms i))).2.2.2
  have hM := meta_drain w id dst ms
  have hMc := meta_clear w id dst ms
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm) hst (hD.2.2.2.1.trans hC.2.2.2.1.symm)
    (hD.2.2.2.2.trans hC.2.2.2.2.symm) (hM.trans hMc.symm)

theorem occ_drop_box (I : Impl) (w : World) (id : InstId) (m : Msg) (ms : List Msg) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hbox : (w.st id).box = m :: ms) :
    OccInv I (creditSender (setActor w id { (w.st id) with box := ms }) (tname id) m.sender) := by
  have hsend : m.sender ∈ w.roster := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  let a1 : Actor := { (w.st id) with box := ms }
  apply occ_consume I w w id m.sender a1 hO (fun _ => rfl) rfl rfl (fun _ => rfl) rfl (fun _ => rfl)
    hmem hsend
  · intro s
    by_cases hs : s = m.sender
    · have hswap : m.sender = s := hs.symm
      subst hswap
      simpa [a1] using owed_drop_box w.st (tname id) m.sender id m ms w.roster hO.nodup hmem rfl rfl hbox
    · have hkeep := owed_keep_box w.st (tname id) s id m ms w.roster hO.nodup hmem rfl
        (fun h => hs h.symm) hbox
      simpa [a1, hs] using hkeep
  · intro d hd s
    exact owed_off w.st id a1 d s w.roster hO.nodup hmem (fun h => hd (h.symm))
  · intro d
    simp [a1, pending]
  · intro m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact hO.sentFrom id m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro p hp
    exact hO.parkFrom id p (by simpa [a1] using hp)
  · intro p hp
    exact hO.parkMsg id p (by simpa [a1] using hp)
  · intro hl1
    simpa [a1] using hO.clear id hl1
  · intro m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact (hO.sameKey id).1 m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro p hp
    exact (hO.sameKey id).2 p (by simpa [a1] using hp)
  · intro hdead
    rcases hdead with hdead | hdead
    · have hempty := (hO.deadEmpty id (Or.inl (by simpa [a1] using hdead))).1
      rw [hbox] at hempty
      simp at hempty
    · have hempty := (hO.deadEmpty id (Or.inr (by simpa [a1] using hdead))).1
      rw [hbox] at hempty
      simp at hempty
  · intro hk m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact (hO.coreFrom id hk).1 m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro hk p hp
    exact (hO.coreFrom id hk).2 p (by simpa [a1] using hp)

theorem occ_drain_box (I : Impl) (w : World) (id : InstId) (ms : List Msg) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hbox : (w.st id).box = ms) :
    OccInv I (drainBox w id (tname id) ms) := by
  induction ms generalizing w with
  | nil =>
    have hempty : (w.st id).box = [] := hbox
    apply occ_keep I w id ({ (w.st id) with box := [] }) hO rfl (by simp [hempty]) rfl (fun _ => rfl) rfl
    intro d
    simp [pending]
  | cons m ms ih =>
    have hstep := occ_drop_box I w id m ms hO hmem hbox
    have hbox1 : ((creditSender (setActor w id { (w.st id) with box := ms }) (tname id) m.sender).st id).box = ms := by
      rw [credit_box]
      simp [setActor]
    have hmem1 : id ∈ (creditSender (setActor w id { (w.st id) with box := ms }) (tname id) m.sender).roster := by
      simpa [creditSender, setActor] using hmem
    simpa [drainBox] using ih _ hstep hmem1 hbox1

def countCredited (sender : InstId) : List Parked → Nat
  | [] => 0
  | p :: ps => (if p.msg.sender = sender then 1 else 0) + countCredited sender ps

def drainPark (w : World) (id : InstId) (dst : String) : List Parked → World
  | [] => setActor w id { (w.st id) with parked := [] }
  | p :: ps =>
    drainPark (creditSender (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender) id dst ps

def refundClearPark (w : World) (id : InstId) (dst : String) (ps : List Parked) : World :=
  let wR := refundParked w dst ps
  setActor wR id { (wR.st id) with parked := [] }

theorem meta_refundP (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).failures = w.failures := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp [refundParked, List.foldl_cons]
    exact (ih (creditSender w dst p.msg.sender)).trans (meta_credit w dst p.msg.sender)

theorem meta_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (drainPark w id dst ps).failures = w.failures := by
  induction ps generalizing w with
  | nil => simp [drainPark, setActor]
  | cons p ps ih =>
    simp [drainPark]
    exact (ih (creditSender (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)).trans
      ((meta_credit (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender).trans
        (meta_set w id { (w.st id) with parked := ps }))

theorem meta_clearP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (refundClearPark w id dst ps).failures = w.failures := by
  simp [refundClearPark, setActor, meta_refundP]

theorem refundP_tok (w : World) (dst : String) (ps : List Parked) (i : InstId) (d : String) :
    ((refundParked w dst ps).st i).tokens d =
      (w.st i).tokens d + if d = dst then countCredited i ps else 0 := by
  induction ps generalizing w with
  | nil => simp [refundParked, countCredited]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_tok, countCredited]
    by_cases hd : d = dst
    · by_cases hs : p.msg.sender = i
      · simp [hd, hs, Nat.add_assoc]
      · have hne : i ≠ p.msg.sender := fun h => hs h.symm
        simp [hd, hne, Nat.zero_add]
        exact hs
    · simp [hd]

theorem refundP_box (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_box]

theorem refundP_park (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_park]

theorem refundP_life (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).life = (w.st i).life ∧
      ((refundParked w dst ps).st i).typestate = (w.st i).typestate ∧
      ((refundParked w dst ps).st i).phase = (w.st i).phase ∧
      ((refundParked w dst ps).st i).prio = (w.st i).prio := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold]
    have hc := credit_life w dst p.msg.sender i
    have hi := ih (creditSender w dst p.msg.sender)
    simp [hc] at hi
    exact hi

theorem clearP_tok (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) (d : String) :
    ((refundClearPark w id dst ps).st i).tokens d =
      (w.st i).tokens d + if d = dst then countCredited i ps else 0 := by
  simp [refundClearPark, setActor]
  by_cases hi : i = id <;> simp [hi, refundP_tok]

theorem clearP_box (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).box = (w.st i).box := by
  by_cases hi : i = id
  · simp [refundClearPark, setActor, hi, refundP_box]
  · simp [refundClearPark, setActor, hi, refundP_box]

theorem clearP_park (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).parked = if i = id then [] else (w.st i).parked := by
  by_cases hi : i = id
  · simp [refundClearPark, setActor, hi]
  · simp [refundClearPark, setActor, hi, refundP_park]

theorem clearP_life (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).life = (w.st i).life ∧
      ((refundClearPark w id dst ps).st i).typestate = (w.st i).typestate ∧
      ((refundClearPark w id dst ps).st i).phase = (w.st i).phase ∧
      ((refundClearPark w id dst ps).st i).prio = (w.st i).prio := by
  by_cases hi : i = id
  · simp [refundClearPark, setActor, hi, refundP_life]
  · simp [refundClearPark, setActor, hi, refundP_life]

theorem drainP_tok (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) (d : String) :
    ((drainPark w id dst ps).st i).tokens d =
      (w.st i).tokens d + if d = dst then countCredited i ps else 0 := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor, countCredited]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark, countCredited]
    have hset : ∀ j, ((setActor w id { (w.st id) with parked := ps }).st j).tokens d = (w.st j).tokens d := by
      intro j
      by_cases hj : j = id <;> simp [setActor, hj]
    have hcred := credit_tok (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender i d
    rw [hset] at hcred
    have hih := ih (creditSender (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    rw [hih, hcred]
    by_cases hd : d = dst
    · by_cases hs : p.msg.sender = i
      · simp [hd, hs, Nat.add_assoc]
      · have hne : i ≠ p.msg.sender := fun h => hs h.symm
        simp [hd, hne, Nat.zero_add]
        exact hs
    · simp [hd]

theorem drainP_box (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark]
    have hb : ((setActor w id { (w.st id) with parked := ps }).st i).box = (w.st i).box := by
      by_cases hi : i = id <;> simp [setActor, hi]
    rw [ih, credit_box, hb]

theorem drainP_park (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).parked = if i = id then [] else (w.st i).parked := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark]
    rw [ih, credit_park]
    by_cases hi : i = id <;> simp [setActor, hi]

theorem drainP_life (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).life = (w.st i).life ∧
      ((drainPark w id dst ps).st i).typestate = (w.st i).typestate ∧
      ((drainPark w id dst ps).st i).phase = (w.st i).phase ∧
      ((drainPark w id dst ps).st i).prio = (w.st i).prio := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark]
    have hL : ((setActor w id { (w.st id) with parked := ps }).st i).life = (w.st i).life ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).typestate = (w.st i).typestate ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).phase = (w.st i).phase ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).prio = (w.st i).prio := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := credit_life (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender i
    have hi := ih (creditSender (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    simp [hc, hL] at hi
    exact hi

theorem frame_refundP (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).N = w.N ∧ (refundParked w dst ps).roster = w.roster ∧
      (refundParked w dst ps).nextIx = w.nextIx ∧ (refundParked w dst ps).cell = w.cell ∧
      (refundParked w dst ps).observed = w.observed := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold]
    have hc := frame_credit w dst p.msg.sender
    have hi := ih (creditSender w dst p.msg.sender)
    exact ⟨hi.1.trans hc.1, hi.2.1.trans hc.2.1, hi.2.2.1.trans hc.2.2.1,
      hi.2.2.2.1.trans hc.2.2.2.1, hi.2.2.2.2.trans hc.2.2.2.2⟩

theorem frame_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (drainPark w id dst ps).N = w.N ∧ (drainPark w id dst ps).roster = w.roster ∧
      (drainPark w id dst ps).nextIx = w.nextIx ∧ (drainPark w id dst ps).cell = w.cell ∧
      (drainPark w id dst ps).observed = w.observed := by
  induction ps generalizing w with
  | nil => simp [drainPark, setActor]
  | cons p ps ih =>
    simp [drainPark]
    have hs := frame_set w id { (w.st id) with parked := ps }
    have hc := frame_credit (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender
    have hi := ih (creditSender (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    exact ⟨hi.1.trans (hc.1.trans hs.1), hi.2.1.trans (hc.2.1.trans hs.2.1),
      hi.2.2.1.trans (hc.2.2.1.trans hs.2.2.1), hi.2.2.2.1.trans (hc.2.2.2.1.trans hs.2.2.2.1),
      hi.2.2.2.2.trans (hc.2.2.2.2.trans hs.2.2.2.2)⟩

theorem frame_clearP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (refundClearPark w id dst ps).N = w.N ∧ (refundClearPark w id dst ps).roster = w.roster ∧
      (refundClearPark w id dst ps).nextIx = w.nextIx ∧ (refundClearPark w id dst ps).cell = w.cell ∧
      (refundClearPark w id dst ps).observed = w.observed := by
  simp [refundClearPark, setActor, frame_refundP]

theorem drainP_mid (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).nextMid = (w.st i).nextMid := by
  induction ps generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [drainPark, setActor, hi]
  | cons p ps ih =>
    simp [drainPark]
    have hset : ((setActor w id { (w.st id) with parked := ps }).st i).nextMid = (w.st i).nextMid := by
      by_cases hi : i = id <;> simp [setActor, hi]
    exact (ih _).trans ((credit_mid _ _ _ _).trans hset)

theorem refundP_mid (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).nextMid = (w.st i).nextMid := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    exact (hfold ▸ ih _).trans (credit_mid w dst p.msg.sender i)

theorem clearP_mid (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).nextMid = (w.st i).nextMid := by
  by_cases hi : i = id <;> simp [refundClearPark, setActor, hi, refundP_mid]

theorem drainP_stamps (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((drainPark w id dst ps).st i) (w.st i) := by
  induction ps generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [sameStamps, drainPark, setActor, hi]
  | cons p ps ih =>
    simp [drainPark]
    have hset : sameStamps ((setActor w id { (w.st id) with parked := ps }).st i) (w.st i) := by
      by_cases hi : i = id <;> simp [sameStamps, setActor, hi]
    exact sameStamps_trans (ih _) (sameStamps_trans (credit_stamps _ _ _ _) hset)

theorem refundP_stamps (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((refundParked w dst ps).st i) (w.st i) := by
  induction ps generalizing w with
  | nil => simp [sameStamps, refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditSender w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    exact sameStamps_trans (hfold ▸ ih _) (credit_stamps w dst p.msg.sender i)

theorem clearP_stamps (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((refundClearPark w id dst ps).st i) (w.st i) := by
  have hset : sameStamps ((refundClearPark w id dst ps).st i) ((refundParked w dst ps).st i) := by
    by_cases hi : i = id <;> simp [sameStamps, refundClearPark, setActor, hi]
  exact sameStamps_trans hset (refundP_stamps w dst ps i)

/-- Refunding every parked sender and then clearing that lane is the same world
as dropping each entry and crediting `msg.sender`, including when that sender is `id`. -/
theorem drain_eq_refund_park (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    drainPark w id dst ps = refundClearPark w id dst ps := by
  have hD := frame_drainP w id dst ps
  have hC := frame_clearP w id dst ps
  have hst : (drainPark w id dst ps).st = (refundClearPark w id dst ps).st := by
    funext i
    apply actor_fields
    · exact (drainP_life w id dst ps i).1.trans (clearP_life w id dst ps i).1.symm
    · exact (drainP_life w id dst ps i).2.1.trans (clearP_life w id dst ps i).2.1.symm
    · exact (drainP_life w id dst ps i).2.2.1.trans (clearP_life w id dst ps i).2.2.1.symm
    · exact (drainP_box w id dst ps i).trans (clearP_box w id dst ps i).symm
    · exact (drainP_life w id dst ps i).2.2.2.trans (clearP_life w id dst ps i).2.2.2.symm
    · exact (drainP_park w id dst ps i).trans (clearP_park w id dst ps i).symm
    · intro d
      exact (drainP_tok w id dst ps i d).trans (clearP_tok w id dst ps i d).symm
    · exact (drainP_mid w id dst ps i).trans (clearP_mid w id dst ps i).symm
    · exact (sameStamps_trans (drainP_stamps w id dst ps i) (sameStamps_symm (clearP_stamps w id dst ps i))).1
    · exact (sameStamps_trans (drainP_stamps w id dst ps i) (sameStamps_symm (clearP_stamps w id dst ps i))).2.1
    · exact (sameStamps_trans (drainP_stamps w id dst ps i) (sameStamps_symm (clearP_stamps w id dst ps i))).2.2.1
    · exact (sameStamps_trans (drainP_stamps w id dst ps i) (sameStamps_symm (clearP_stamps w id dst ps i))).2.2.2
  have hM := meta_drainP w id dst ps
  have hMc := meta_clearP w id dst ps
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm) hst (hD.2.2.2.1.trans hC.2.2.2.1.symm)
    (hD.2.2.2.2.trans hC.2.2.2.2.symm) (hM.trans hMc.symm)

theorem occ_drop_park (I : Impl) (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (hO : OccInv I w) (hmem : id ∈ w.roster) (hpark : (w.st id).parked = p :: ps)
    (hmsg : p.sender = p.msg.sender) :
    OccInv I (creditSender (setActor w id { (w.st id) with parked := ps }) (tname id) p.msg.sender) := by
  have hsend : p.msg.sender ∈ w.roster := by
    rw [← hmsg]
    exact hO.parkFrom id p (by rw [hpark]; exact List.Mem.head _)
  let a1 : Actor := { (w.st id) with parked := ps }
  apply occ_consume I w w id p.msg.sender a1 hO (fun _ => rfl) rfl rfl (fun _ => rfl) rfl (fun _ => rfl)
    hmem hsend
  · intro s
    by_cases hs : s = p.msg.sender
    · rw [hs]
      simpa [a1] using owed_drop_park w.st (tname id) p.msg.sender id p ps w.roster hO.nodup hmem rfl
        hmsg hpark
    · have hkeep := owed_keep_park w.st (tname id) s id p ps w.roster hO.nodup hmem rfl
        (fun h => hs (h.symm.trans hmsg)) hpark
      simpa [a1, hs] using hkeep
  · intro d hd s
    exact owed_off w.st id a1 d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro d
    simp [a1, pending]
  · intro m hm
    exact hO.sentFrom id m (by simpa [a1] using hm)
  · intro q hq
    exact hO.parkFrom id q (by
      have hq0 : q ∈ ps := by simpa [a1] using hq
      rw [hpark]
      exact List.mem_cons.mpr (Or.inr hq0))
  · intro q hq
    exact hO.parkMsg id q (by
      have hq0 : q ∈ ps := by simpa [a1] using hq
      rw [hpark]
      exact List.mem_cons.mpr (Or.inr hq0))
  · intro hl1
    have hnil := hO.clear id hl1
    rw [hpark] at hnil
    cases hnil
  · intro m hm
    exact (hO.sameKey id).1 m (by simpa [a1] using hm)
  · intro q hq
    exact (hO.sameKey id).2 q (by
      have hq0 : q ∈ ps := by simpa [a1] using hq
      rw [hpark]
      exact List.mem_cons.mpr (Or.inr hq0))
  · intro hdead
    rcases hdead with hdead | hdead
    · have hempty := (hO.deadEmpty id (Or.inl (by simpa [a1] using hdead))).2
      rw [hpark] at hempty
      simp at hempty
    · have hempty := (hO.deadEmpty id (Or.inr (by simpa [a1] using hdead))).2
      rw [hpark] at hempty
      simp at hempty
  · intro hk m hm
    exact (hO.coreFrom id hk).1 m (by simpa [a1] using hm)
  · intro hk q hq
    have hq0 : q ∈ ps := by simpa [a1] using hq
    exact (hO.coreFrom id hk).2 q (by rw [hpark]; exact List.mem_cons.mpr (Or.inr hq0))

theorem occ_drain_park (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hpark : (w.st id).parked = ps)
    (hmsg : ∀ p ∈ ps, p.sender = p.msg.sender) :
    OccInv I (drainPark w id (tname id) ps) := by
  induction ps generalizing w with
  | nil =>
    have hempty : (w.st id).parked = [] := hpark
    apply occ_keep I w id ({ (w.st id) with parked := [] }) hO rfl rfl (by simp [hempty])
      (fun _ => rfl) rfl
    intro _
    simp [pending]
  | cons p ps ih =>
    have hstep := occ_drop_park I w id p ps hO hmem hpark (hmsg p (List.Mem.head _))
    let w1 := creditSender (setActor w id { (w.st id) with parked := ps }) (tname id) p.msg.sender
    have hpark1 : (w1.st id).parked = ps := by
      rw [credit_park]
      simp [w1, setActor]
    have hmem1 : id ∈ w1.roster := by simpa [w1, creditSender, setActor] using hmem
    have hmsg1 : ∀ q ∈ ps, q.sender = q.msg.sender := fun q hq => hmsg q (List.Mem.tail _ hq)
    simpa [drainPark, w1] using ih w1 hstep hmem1 hpark1 hmsg1

/-- Queues are already empty and this actor owes nothing. Marking it dead
does not change anyone's account. -/
theorem occ_die (I : Impl) (w : World) (id : InstId) (hO : OccInv I w) (hmem : id ∈ w.roster)
    (hbox : (w.st id).box = []) (hpark : (w.st id).parked = [])
    (hquiet : ∀ d, owed w.st d id w.roster ≤ budget I.desc (tname id) d)
    (hstrip : ∀ host m, m ∈ (w.st host).box → m.sender = id → peerKey host = none → peerKey id = none)
    (hstripP : ∀ host p, p ∈ (w.st host).parked → p.sender = id → peerKey host = none →
      peerKey id = none) :
    OccInv I (setActor w id { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }) := by
  let dead : Actor := { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  let w' := setActor w id dead
  suffices OccInv I w' by simpa [w', dead] using this
  have hst : ∀ i, w'.st i = if i = id then dead else w.st i := by
    intro i
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have howed : ∀ d s, owed w'.st d s w.roster = owed w.st d s w.roster := by
    intro d s
    refine owed_mail_eq _ _ _ _ w.roster ?_
    intro i _
    rw [hst i]
    by_cases hi : i = id <;> simp [hi, dead, hbox, hpark]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hO.nodup
  · intro i hl
    rw [hst i] at hl
    by_cases hi : i = id
    · simp [hi, dead] at hl
    · simp [hi] at hl
      exact hO.aliveIn i hl
  · intro template i hi
    exact hO.indexed template i hi
  · intro template ht
    have hc : aliveCount w' template ≤ aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum]
      refine sum_le _ _ w.roster ?_
      intro i _
      by_cases hi : i = id
      · simp [aliveBit, hst, hi, dead]
      · simp [aliveBit, hst, hi]
    exact Nat.le_trans hc (hO.liveOne template ht)
  · intro template ht
    have hc : aliveCount w' template ≤ aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum]
      refine sum_le _ _ w.roster ?_
      intro i _
      by_cases hi : i = id
      · simp [aliveBit, hst, hi, dead]
      · simp [aliveBit, hst, hi]
    exact Nat.le_trans hc (hO.livePeer template ht)
  · intro i hnin
    have hne : i ≠ id := fun heq => hnin (heq ▸ hmem)
    rw [hst i, if_neg hne]
    exact hO.offEmpty i hnin
  · intro i m hm
    rw [hst i] at hm
    by_cases hi : i = id
    · simp [hi, dead] at hm
    · simp [hi] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    rw [hst i] at hp
    by_cases hi : i = id
    · simp [hi, dead] at hp
    · simp [hi] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    rw [hst i] at hp
    by_cases hi : i = id
    · simp [hi, dead] at hp
    · simp [hi] at hp
      exact hO.parkMsg i p hp
  · intro s d hs
    have hrost : w'.roster = w.roster := by simp [w', setActor]
    rw [hrost] at hs ⊢
    have htok : (w'.st s).tokens d = (w.st s).tokens d := by
      rw [hst s]
      by_cases hss : s = id <;> simp [hss, dead]
    rw [howed, htok]
    exact hO.balance s d hs
  · intro s d hs hl
    have hrost : w'.roster = w.roster := by simp [w', setActor]
    rw [hrost] at hs
    rw [hst s] at hl
    by_cases hss : s = id
    · simp [hss, dead] at hl
    · simp [hss] at hl
      have hph : (w'.st s).phase = (w.st s).phase := by rw [hst s]; simp [hss]
      have hty : (w'.st s).typestate = (w.st s).typestate := by rw [hst s]; simp [hss]
      have htok : (w'.st s).tokens d = (w.st s).tokens d := by rw [hst s]; simp [hss]
      have hpend : pending (w'.st s) d = pending (w.st s) d := by simp [pending, hph]
      rw [hpend, hty, htok]
      exact hO.slack s d hs hl
  · intro s d hs hterm
    have hrost : w'.roster = w.roster := by simp [w', setActor]
    rw [hrost] at hs ⊢
    rw [howed]
    exact hO.still s d hs hterm
  · intro s d hs hdead
    have hrost : w'.roster = w.roster := by simp [w', setActor]
    rw [hrost] at hs ⊢
    rw [howed]
    by_cases hss : s = id
    · rw [hss]
      exact hquiet d
    · have hdead0 : (w.st s).life ≠ .alive := by
        rw [hst s] at hdead
        simp [hss] at hdead
        exact hdead
      exact hO.quiet s d hs hdead0
  · intro i hl1
    rw [hst i]
    by_cases hi : i = id
    · simp [hi, dead]
    · simp [hi]
      exact hO.clear i hl1
  · intro i hdead
    rw [hst i] at hdead ⊢
    by_cases hi : i = id
    · simp [hi, dead]
    · simp [hi] at hdead ⊢
      exact hO.deadEmpty i hdead
  · intro host
    refine ⟨fun m hm => ?_, fun p hp => ?_⟩
    · rw [hst host] at hm
      by_cases hi : host = id
      · simp [hi, dead] at hm
      · simp [hi] at hm
        by_cases hs : m.sender = id
        · by_cases hk : peerKey host = none
          · have hpk := hstrip host m hm hs hk
            have hkey := ((hO.sameKey host).1 m hm).1
            exact ⟨hkey, fun _ => Or.inr (hs ▸ hpk)⟩
          · have hkey := ((hO.sameKey host).1 m hm).1
            exact ⟨hkey, fun hnone => absurd hnone hk⟩
        · have hlife : (w'.st m.sender).life = (w.st m.sender).life := by
            rw [hst m.sender]
            simp [hs, dead]
          exact (queueOk_life w w' m.sender host hlife).1 ((hO.sameKey host).1 m hm)
    · rw [hst host] at hp
      by_cases hi : host = id
      · simp [hi, dead] at hp
      · simp [hi] at hp
        by_cases hs : p.sender = id
        · by_cases hk : peerKey host = none
          · have hpk := hstripP host p hp hs hk
            have hkey := ((hO.sameKey host).2 p hp).1
            exact ⟨hkey, fun _ => Or.inr (hs ▸ hpk)⟩
          · have hkey := ((hO.sameKey host).2 p hp).1
            exact ⟨hkey, fun hnone => absurd hnone hk⟩
        · have hlife : (w'.st p.sender).life = (w.st p.sender).life := by
            rw [hst p.sender]
            simp [hs, dead]
          exact (queueOk_life w w' p.sender host hlife).1 ((hO.sameKey host).2 p hp)
  · intro i hi
    exact hO.shaped i (by simp [w', setActor] at hi; exact hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst host] at hm
      by_cases hi : host = id
      · simp [hi, dead] at hm
      · simp [hi] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [hst host] at hp
      by_cases hi : host = id
      · simp [hi, dead] at hp
      · simp [hi] at hp
        exact (hO.coreFrom host hk).2 p hp

theorem call_tail (p : Parked) (ps : List Parked) (h : hasParkedCall (p :: ps) = false) :
    p.isCall = false ∧ ∀ q ∈ ps, q.isCall = false := by
  simp [hasParkedCall, List.any_cons, Bool.or_eq_false_iff] at h
  simpa [hasParkedCall, List.any_eq_false] using h

theorem occ_release (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hO : OccInv I w)
    (hcont : ∀ i, contTy (w.st i)) :
    OccInv I (releaseParked w id ps) ∧ ∀ i, contTy ((releaseParked w id ps).st i) := by
  induction ps generalizing w with
  | nil =>
    simp [releaseParked]
    exact ⟨hO, hcont⟩
  | cons p ps ih =>
    simp only [releaseParked, List.foldl_cons]
    by_cases hcall : p.isCall = true
    · simp [hcall]
      simpa [releaseParked] using ih w hO hcont
    · have hfalse : p.isCall = false := eq_false_of_ne_true hcall
      simp [hfalse]
      by_cases hself : p.sender = id
      · simp [hself]
        simpa [releaseParked] using ih w hO hcont
      · simp [hself]
        have hO1 := occ_resume I w p.sender false id hO (hcont p.sender)
        have hcont1 : ∀ i, contTy ((setActor w p.sender (resumeSender (w.st p.sender) false id)).st i) := by
          intro i
          by_cases hi : i = p.sender
          · rw [hi, setActor_self]
            exact resume_cont (w.st p.sender) false id (hcont p.sender)
          · rw [setActor_other w p.sender i _ hi]
            exact hcont i
        simpa [releaseParked] using
          ih (setActor w p.sender (resumeSender (w.st p.sender) false id)) hO1 hcont1

theorem term_tok (w : World) (id : InstId) (i : InstId) (d : String) :
    let name := tname id
    let ms := (w.st id).box
    let ps := (w.st id).parked
    let drained := drainPark (drainBox w id name ms) id name ps
    let refunded := refundParked (refundMsgs w name ms) name ps
    (drained.st i).tokens d = (refunded.st i).tokens d := by
  intro name ms ps drained refunded
  rw [drainP_tok (drainBox w id name ms) id name ps i d,
    drain_tok w id name ms i d,
    refundP_tok (refundMsgs w name ms) name ps i d,
    refund_tok w name ms i d]

theorem term_actor (w : World) (id i : InstId) :
    let name := tname id
    let ms := (w.st id).box
    let ps := (w.st id).parked
    let drained := drainPark (drainBox w id name ms) id name ps
    let refunded := refundParked (refundMsgs w name ms) name ps
    let died := { (drained.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
    let killed := { (refunded.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
    (setActor drained id died).st i = (setActor refunded id killed).st i := by
  intro name ms ps drained refunded died killed
  by_cases hi : i = id
  · simp [setActor, hi, died, killed]
    constructor
    · exact (drainP_life (drainBox w id name ms) id name ps id).2.1.trans
        ((drain_life w id name ms id).2.1.trans
          ((refund_life w name ms id).2.1.symm.trans
            (refundP_life (refundMsgs w name ms) name ps id).2.1.symm))
    · constructor
      · funext d
        simpa using term_tok w id id d
      · let hs := sameStamps_trans
          (drainP_stamps (drainBox w id name ms) id name ps id)
          (sameStamps_trans (drain_stamps w id name ms id)
            (sameStamps_trans (sameStamps_symm (refund_stamps w name ms id))
              (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps id))))
        refine ⟨?_, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
        exact (drainP_mid (drainBox w id name ms) id name ps id).trans
          ((drain_mid w id name ms id).trans
            ((refund_mid w name ms id).symm.trans
              (refundP_mid (refundMsgs w name ms) name ps id).symm))
  · simp [setActor, hi]
    apply actor_fields
    · have h1 := (drainP_life (drainBox w id name ms) id name ps i).1
      have h2 := (drain_life w id name ms i).1
      have h3 := (refund_life w name ms i).1
      have h4 := (refundP_life (refundMsgs w name ms) name ps i).1
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := (drainP_life (drainBox w id name ms) id name ps i).2.1
      have h2 := (drain_life w id name ms i).2.1
      have h3 := (refund_life w name ms i).2.1
      have h4 := (refundP_life (refundMsgs w name ms) name ps i).2.1
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := (drainP_life (drainBox w id name ms) id name ps i).2.2.1
      have h2 := (drain_life w id name ms i).2.2.1
      have h3 := (refund_life w name ms i).2.2.1
      have h4 := (refundP_life (refundMsgs w name ms) name ps i).2.2.1
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := drainP_box (drainBox w id name ms) id name ps i
      have h2 := drain_box w id name ms i
      have h3 := refund_box w name ms i
      have h4 := refundP_box (refundMsgs w name ms) name ps i
      simp [hi] at h1 h2
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := (drainP_life (drainBox w id name ms) id name ps i).2.2.2
      have h2 := (drain_life w id name ms i).2.2.2
      have h3 := (refund_life w name ms i).2.2.2
      have h4 := (refundP_life (refundMsgs w name ms) name ps i).2.2.2
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := drainP_park (drainBox w id name ms) id name ps i
      have h2 := drain_park w id name ms i
      have h3 := refund_park w name ms i
      have h4 := refundP_park (refundMsgs w name ms) name ps i
      simp [hi] at h1 h2
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · intro d
      simpa using term_tok w id i d
    · exact (drainP_mid (drainBox w id name ms) id name ps i).trans
        ((drain_mid w id name ms i).trans
          ((refund_mid w name ms i).symm.trans
            (refundP_mid (refundMsgs w name ms) name ps i).symm))
    · let hs := sameStamps_trans
        (drainP_stamps (drainBox w id name ms) id name ps i)
        (sameStamps_trans (drain_stamps w id name ms i)
          (sameStamps_trans (sameStamps_symm (refund_stamps w name ms i))
            (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps i))))
      exact hs.1
    · let hs := sameStamps_trans
        (drainP_stamps (drainBox w id name ms) id name ps i)
        (sameStamps_trans (drain_stamps w id name ms i)
          (sameStamps_trans (sameStamps_symm (refund_stamps w name ms i))
            (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps i))))
      exact hs.2.1
    · let hs := sameStamps_trans
        (drainP_stamps (drainBox w id name ms) id name ps i)
        (sameStamps_trans (drain_stamps w id name ms i)
          (sameStamps_trans (sameStamps_symm (refund_stamps w name ms i))
            (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps i))))
      exact hs.2.2.1
    · let hs := sameStamps_trans
        (drainP_stamps (drainBox w id name ms) id name ps i)
        (sameStamps_trans (drain_stamps w id name ms i)
          (sameStamps_trans (sameStamps_symm (refund_stamps w name ms i))
            (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps i))))
      exact hs.2.2.2

theorem occ_term_kill (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hcont : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hterm : terminableB I.desc (tname id) = true)
    (hmsg : ∀ p ∈ (w.st id).parked, p.sender = p.msg.sender) :
    let name := tname id
    let ms := (w.st id).box
    let ps := (w.st id).parked
    let drained := drainPark (drainBox w id name ms) id name ps
    let died := setActor drained id
      { (drained.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
    let killed := setActor (refundParked (refundMsgs w name ms) name ps) id
      { ((refundParked (refundMsgs w name ms) name ps).st id) with
          life := .dead, phase := .idle, prio := [], box := [], parked := [] }
    died = killed ∧ OccInv I (releaseParked killed id ps) ∧
      ∀ i, contTy ((releaseParked killed id ps).st i) := by
  intro name ms ps drained died killed
  have hOb := occ_drain_box I w id ms hO hmem rfl
  have hparkB : ((drainBox w id name ms).st id).parked = ps := by
    have hp := drain_park w id name ms id
    simp [name, ps] at hp
    exact hp
  have hmemB : id ∈ (drainBox w id name ms).roster := by
    simpa [(frame_drain w id name ms).2.1] using hmem
  have hOp := occ_drain_park I (drainBox w id name ms) id ps hOb hmemB hparkB hmsg
  have hmemD : id ∈ drained.roster := by
    simpa [drained, (frame_drainP (drainBox w id name ms) id name ps).2.1] using hmemB
  have hboxD : (drained.st id).box = [] := by
    have hb := drain_box w id name ms id
    have hb2 := drainP_box (drainBox w id name ms) id name ps id
    simp at hb
    exact hb2.trans hb
  have hparkD : (drained.st id).parked = [] := by
    have hp := drainP_park (drainBox w id name ms) id name ps id
    simp [drained, name] at hp
    exact hp
  have hbound : ∀ d, owed drained.st d id drained.roster ≤ budget I.desc (tname id) d := fun d => by
    have hbal := hOp.balance id d hmemD
    have hle : owed drained.st d id drained.roster ≤
        owed drained.st d id drained.roster + (drained.st id).tokens d := Nat.le_add_right _ _
    rwa [hbal] at hle
  have hstrip : ∀ host m, m ∈ (drained.st host).box → m.sender = id →
      peerKey host = none → peerKey id = none := by
    intro host m hm hs hk
    rcases (hOp.coreFrom host hk).1 m hm with hpk | hnt
    · exact hs ▸ hpk
    · rw [hs] at hnt
      rw [hterm] at hnt
      exact Bool.noConfusion hnt
  have hstripP : ∀ host p, p ∈ (drained.st host).parked → p.sender = id →
      peerKey host = none → peerKey id = none := by
    intro host p hp hs hk
    rcases (hOp.coreFrom host hk).2 p hp with hpk | hnt
    · exact hs ▸ hpk
    · rw [hs] at hnt
      rw [hterm] at hnt
      exact Bool.noConfusion hnt
  have hOd := occ_die I drained id hOp hmemD hboxD hparkD hbound hstrip hstripP
  have hcontD : ∀ i, contTy (died.st i) := by
    intro i
    by_cases hi : i = id
    · simp [died, setActor, hi, contTy]
    · have hph : (died.st i).phase = (w.st i).phase := by
        simp [died, setActor, hi]
        exact (drainP_life (drainBox w id name ms) id name ps i).2.2.1.trans (drain_life w id name ms i).2.2.1
      have hty : (died.st i).typestate = (w.st i).typestate := by
        simp [died, setActor, hi]
        exact (drainP_life (drainBox w id name ms) id name ps i).2.1.trans (drain_life w id name ms i).2.1
      exact (contTy_match _ _ hph hty).mpr (hcont i)
  have hrel := occ_release I died id ps hOd hcontD
  have hst : ∀ i, died.st i = killed.st i := fun i => by simpa [died, killed, drained, name, ms, ps] using term_actor w id i
  have heq : died = killed := by
    apply world_eq
    · simp [died, killed, setActor, drained, (frame_drainP (drainBox w id name ms) id name ps).1,
        (frame_drain w id name ms).1, (frame_refundP (refundMsgs w name ms) name ps).1,
        (frame_refund w name ms).1]
    · simp [died, killed, setActor, drained, (frame_drainP (drainBox w id name ms) id name ps).2.1,
        (frame_drain w id name ms).2.1, (frame_refundP (refundMsgs w name ms) name ps).2.1,
        (frame_refund w name ms).2.1]
    · simp [died, killed, setActor, drained, (frame_drainP (drainBox w id name ms) id name ps).2.2.1,
        (frame_drain w id name ms).2.2.1, (frame_refundP (refundMsgs w name ms) name ps).2.2.1,
        (frame_refund w name ms).2.2.1]
    · funext i; exact hst i
    · simp [died, killed, setActor, drained, (frame_drainP (drainBox w id name ms) id name ps).2.2.2.1,
        (frame_drain w id name ms).2.2.2.1, (frame_refundP (refundMsgs w name ms) name ps).2.2.2.1,
        (frame_refund w name ms).2.2.2.1]
    · simp [died, killed, setActor, drained, (frame_drainP (drainBox w id name ms) id name ps).2.2.2.2,
        (frame_drain w id name ms).2.2.2.2, (frame_refundP (refundMsgs w name ms) name ps).2.2.2.2,
        (frame_refund w name ms).2.2.2.2]
    · simp [died, killed, setActor, drained, meta_drainP (drainBox w id name ms) id name ps,
        meta_drain w id name ms, meta_refundP (refundMsgs w name ms) name ps,
        meta_refund w name ms]
  exact ⟨heq, by simpa [heq] using hrel.1, by simpa [heq] using hrel.2⟩


/-! A subtree kill refunds the member's mailbox and fails whoever waited on it.
The two writes commute, so the account is the drain already proved for one
terminable actor, after the waiters have resumed. -/

theorem setActor_shadow (w : World) (id : InstId) (a b : Actor) :
    setActor (setActor w id a) id b = setActor w id b := by
  apply world_eq <;> simp [setActor]
  · funext x
    by_cases hx : x = id
    · simp [hx]
    · simp [setActor, hx]

theorem setActor_comm (w : World) (i j : InstId) (a b : Actor) (hne : i ≠ j) :
    setActor (setActor w i a) j b = setActor (setActor w j b) i a := by
  apply world_eq
  · rfl
  · rfl
  · rfl
  · funext x
    by_cases hxi : x = i
    · rw [hxi]
      rw [setActor_other (setActor w i a) j i b hne, setActor_self, setActor_self]
    · by_cases hxj : x = j
      · rw [hxj] at hxi ⊢
        rw [setActor_self, setActor_other (setActor w j b) i j a hxi, setActor_self]
      · rw [setActor_other (setActor w i a) j x b hxj, setActor_other w i x a hxi,
          setActor_other (setActor w j b) i x a hxi, setActor_other w j x b hxj]
  · rfl
  · rfl
  · rfl

theorem proceed_bump (a : Actor) (k : Cont) (dst : String) :
    proceed (bumpToken a dst (.ofNat 1)) k = bumpToken (proceed a k) dst (.ofNat 1) := by
  cases hk : k.rest with
  | nil => apply actor_fields <;> simp [proceed, bumpToken, hk]
  | cons _ _ => apply actor_fields <;> simp [proceed, bumpToken, hk]

theorem idlePhase_bump (a : Actor) (dst : String) :
    { bumpToken a dst (.ofNat 1) with phase := .idle } =
      bumpToken { a with phase := .idle } dst (.ofNat 1) := by
  apply actor_fields <;> simp [bumpToken]

/-- Updating `i` by `f` commutes with crediting `cred` when `f` commutes with the token bump. -/
theorem credit_update_comm (w : World) (i cred : InstId) (name : String) (f : Actor → Actor)
    (hf : ∀ a, f (bumpToken a name (.ofNat 1)) = bumpToken (f a) name (.ofNat 1)) :
    setActor (creditSender w name cred) i (f ((creditSender w name cred).st i)) =
      creditSender (setActor w i (f (w.st i))) name cred := by
  by_cases h : i = cred
  · subst h
    rw [creditSender, setActor_self, hf, setActor_shadow, creditSender, setActor_self, setActor_shadow]
  · apply world_eq
    · simp [creditSender, setActor]
    · simp [creditSender, setActor]
    · simp [creditSender, setActor]
    · funext x
      by_cases hxi : x = i
      · subst hxi
        simp [creditSender, setActor, h]
      · by_cases hxc : x = cred
        · subst hxc
          simp [creditSender, setActor, hxi]
        · simp [creditSender, setActor, hxi, hxc]
    · simp [creditSender, setActor]
    · simp [creditSender, setActor]
    · simp [creditSender, setActor]

theorem failWaiter_credit_comm (w : World) (dead cred : InstId) (name : String) (i : InstId) :
    failWaiter (creditSender w name cred) dead i =
      creditSender (failWaiter w dead i) name cred := by
  have hL := credit_life w name cred i
  cases hlive : (w.st i).life with
  | absent =>
    have hskip : ((w.st i).life != .alive) = true := by simp [hlive]
    have hskipc : (((creditSender w name cred).st i).life != .alive) = true := by rw [hL.1, hskip]
    simp [failWaiter, hskip, hskipc]
  | dead =>
    have hskip : ((w.st i).life != .alive) = true := by simp [hlive]
    have hskipc : (((creditSender w name cred).st i).life != .alive) = true := by rw [hL.1, hskip]
    simp [failWaiter, hskip, hskipc]
  | alive =>
    have hgo : ((w.st i).life != .alive) = false := by simp [hlive]
    have hgo' : (((creditSender w name cred).st i).life != .alive) = false := by rw [hL.1, hgo]
    cases hph : (w.st i).phase with
    | parked d b k =>
      have hphc : ((creditSender w name cred).st i).phase = .parked d b k := by
        simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hd]
          exact credit_update_comm w i cred name (fun a => proceed a k) fun a => proceed_bump a k name
        · simp [hd]
      | true =>
        simp
    | awaitReply d k =>
      have hphc : ((creditSender w name cred).st i).phase = .awaitReply d k := by
        simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
    | idle =>
      have hphc : ((creditSender w name cred).st i).phase = .idle := by simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
    | run k =>
      have hphc : ((creditSender w name cred).st i).phase = .run k := by simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
    | awaitEffect k =>
      have hphc : ((creditSender w name cred).st i).phase = .awaitEffect k := by
        simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
    | awaitPeer k =>
      have hphc : ((creditSender w name cred).st i).phase = .awaitPeer k := by
        simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]
    | crashed =>
      have hphc : ((creditSender w name cred).st i).phase = .crashed := by simpa [hph] using hL.2.2.1
      simp [failWaiter, hgo, hgo', hph, hphc]

theorem failFold_credit (w : World) (dead : InstId) (ids : List InstId) (name : String) (s : InstId) :
    ids.foldl (fun w i => failWaiter w dead i) (creditSender w name s) =
      creditSender (ids.foldl (fun w i => failWaiter w dead i) w) name s := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [failWaiter_credit_comm]
    exact ih (failWaiter w dead i)

theorem failFold_refundMsgs (w : World) (dead : InstId) (ids : List InstId) (name : String)
    (ms : List Msg) :
    ids.foldl (fun w i => failWaiter w dead i) (refundMsgs w name ms) =
      refundMsgs (ids.foldl (fun w i => failWaiter w dead i) w) name ms := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w name (m :: ms) = refundMsgs (creditSender w name m.sender) name ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, failFold_credit]
    simp [refundMsgs, List.foldl_cons]

theorem failFold_refundParked (w : World) (dead : InstId) (ids : List InstId) (name : String)
    (ps : List Parked) :
    ids.foldl (fun w i => failWaiter w dead i) (refundParked w name ps) =
      refundParked (ids.foldl (fun w i => failWaiter w dead i) w) name ps := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w name (p :: ps) =
        refundParked (creditSender w name p.msg.sender) name ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, failFold_credit]
    simp [refundParked, List.foldl_cons]

theorem failWaiters_refund (w : World) (dead : InstId) (name : String) (ms : List Msg) (ps : List Parked) :
    failWaiters (refundParked (refundMsgs w name ms) name ps) dead =
      refundParked (refundMsgs (failWaiters w dead) name ms) name ps := by
  have hr : (refundParked (refundMsgs w name ms) name ps).roster = w.roster := by
    simpa [(frame_refund w name ms).2.1] using (frame_refundP (refundMsgs w name ms) name ps).2.1
  unfold failWaiters
  rw [hr]
  rw [failFold_refundParked (refundMsgs w name ms) dead w.roster name ps]
  rw [failFold_refundMsgs w dead w.roster name ms]

theorem filter_sender_keep (ps : List Parked) (dead : InstId)
    (h : ∀ p ∈ ps, p.sender ≠ dead) :
    ps.filter (fun p => p.sender != dead) = ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := h p (List.Mem.head _)
    have hbit : (p.sender != dead) = true := by
      cases hbb : p.sender == dead
      · simp [bne, hbb]
      · exact absurd (beq_iff_eq.mp hbb) hp
    simp [hbit, ih fun q hq => h q (List.Mem.tail _ hq)]

theorem forgetStep_noop (w : World) (dead id : InstId)
    (h : ∀ p ∈ (w.st id).parked, p.sender ≠ dead) :
    (let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) = w := by
  simp only
  have hfilt := filter_sender_keep (w.st id).parked dead h
  simp [hfilt]

theorem forgetFold_noop (w : World) (dead : InstId) (ids : List InstId)
    (h : ∀ i ∈ ids, ∀ p ∈ (w.st i).parked, p.sender ≠ dead) :
    ids.foldl (fun w id =>
      let a := w.st id
      let ps := a.parked.filter fun p => p.sender != dead
      if ps == a.parked then w else setActor w id { a with parked := ps }) w = w := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep := forgetStep_noop w dead i (h i (List.Mem.head _))
    rw [hstep]
    exact ih _ fun j hj p hp => h j (List.Mem.tail _ hj) p hp

theorem filter_none {α : Type} (p : α → Bool) (l : List α) (h : ∀ a ∈ l, p a = false) :
    l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (List.Mem.head _)
    simp [List.filter, ha, ih fun b hb => h b (List.Mem.tail _ hb)]

/-- A host with no mail from `dead` is left untouched, box and park alike. -/
theorem forgetHost_quiet (w : World) (dead host : InstId)
    (hbox : ∀ m ∈ (w.st host).box, m.sender ≠ dead)
    (hpark : ∀ p ∈ (w.st host).parked, p.sender ≠ dead) :
    forgetHost w dead host = w := by
  by_cases hself : host = dead
  · simp [forgetHost, hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    have hbox0 := filter_none (fun m : Msg => m.sender == dead) (w.st host).box
      fun m hm => by simpa [beq_iff_eq] using hbox m hm
    have hpark0 := filter_none (fun p : Parked => p.sender == dead) (w.st host).parked
      fun p hp => by simpa [beq_iff_eq] using hpark p hp
    have hz : outboundCount dead (w.st host) = 0 := by simp [outboundCount, hbox0, hpark0]
    have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
    simp [forgetHost, hb, hn]

theorem forgetFold_quiet (w : World) (dead : InstId) (ids : List InstId)
    (h : ∀ i ∈ ids,
      (∀ m ∈ (w.st i).box, m.sender ≠ dead) ∧ (∀ p ∈ (w.st i).parked, p.sender ≠ dead)) :
    ids.foldl (fun w host => forgetHost w dead host) w = w := by
  induction ids generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep := forgetHost_quiet w dead i (h i (List.Mem.head _)).1 (h i (List.Mem.head _)).2
    rw [hstep]
    exact ih _ fun j hj => h j (List.Mem.tail _ hj)

/-- No outbound mail means reclaiming it changes nothing. -/
theorem forget_noop (w : World) (dead : InstId)
    (hbox : ∀ i ∈ w.roster, ∀ m ∈ (w.st i).box, m.sender ≠ dead)
    (hpark : ∀ i ∈ w.roster, ∀ p ∈ (w.st i).parked, p.sender ≠ dead) :
    forgetSender w dead = w := by
  simpa [forgetSender] using
    forgetFold_quiet w dead w.roster fun i hi => ⟨hbox i hi, hpark i hi⟩

/-- Failing a waiter only changes its phase. The mailbox and the token account stay. -/
theorem occ_failWaiter (I : Impl) (w : World) (dead i : InstId) (hO : OccInv I w)
    (hC : ∀ j, contTy (w.st j)) :
    OccInv I (failWaiter w dead i) ∧ ∀ j, contTy ((failWaiter w dead i).st j) := by
  unfold failWaiter
  split
  · exact ⟨hO, hC⟩
  · next hlive =>
    cases hph : (w.st i).phase with
    | parked d b k =>
      simp
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hd]
          have hty : (w.st i).typestate = k.toState := by simpa [contTy, hph] using hC i
          have hO' := occ_keep I w i (proceed (w.st i) k) hO (proceed_life _ _)
            (by cases hk : k.rest <;> simp [proceed, hk])
            (by cases hk : k.rest <;> simp [proceed, hk])
            (by intro d; cases hk : k.rest <;> simp [proceed, hk])
            (by cases hk : k.rest <;> simp [proceed, hk, hty])
            (by intro d; cases hk : k.rest <;> simp [pending, contRest, proceed, hph, hk, sendsTo])
          have hnew : contTy (proceed (w.st i) k) := by
            cases hk : k.rest <;> simp [proceed, contTy, hk, hty]
          exact ⟨hO', cont_after w i _ hC hnew⟩
        · simp [hd]
          exact ⟨hO, hC⟩
      | true =>
        simp
        exact ⟨hO, hC⟩
    | awaitReply _ _ =>
      simp
      exact ⟨hO, hC⟩
    | idle => simp; exact ⟨hO, hC⟩
    | run _ => simp; exact ⟨hO, hC⟩
    | awaitEffect _ => simp; exact ⟨hO, hC⟩
    | awaitPeer _ => simp; exact ⟨hO, hC⟩
    | crashed => simp; exact ⟨hO, hC⟩

/-- Moving one host's blocked sends from `dead` into its box keeps the account.
The target stays alive and still has to handle the mail. -/
theorem occ_admitHost (I : Impl) (w : World) (dead host : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) :
    OccInv I (admitHost w dead host) ∧ ∀ i, contTy ((admitHost w dead host).st i) := by
  by_cases hself : (host == dead) = true
  · simp [admitHost, hself]
    exact ⟨hO, hC⟩
  · have hne : (host == dead) = false := eq_false_of_ne_true hself
    by_cases hempty : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = true
    · simp [admitHost, hne, hempty]
      exact ⟨hO, hC⟩
    · have hfull : ((w.st host).parked.filter fun p => p.sender == dead).isEmpty = false :=
        eq_false_of_ne_true hempty
      let a := admitActor (w.st host) dead
      have hw : admitHost w dead host = setActor w host a := by
        simp [admitHost, hne, hfull, a, admitActor]
      rw [hw]
      have hlifeA : a.life = (w.st host).life := by simp [a, admitActor]
      have hboxA : a.box = (w.st host).box ++
          (((w.st host).parked.filter fun p => p.sender == dead).map (·.msg)) := by
        simp [a, admitActor]
      have hparkA : a.parked = (w.st host).parked.filter fun p => p.sender != dead := by
        simp [a, admitActor]
      have htyA : a.typestate = (w.st host).typestate := by simp [a, admitActor]
      have hphA : a.phase = (w.st host).phase := by simp [a, admitActor]
      have htokA : ∀ d, a.tokens d = (w.st host).tokens d := by intro d; simp [a, admitActor]
      have hmem : host ∈ w.roster := by
        by_cases hnin : host ∈ w.roster
        · exact hnin
        · have hemptyP := (hO.offEmpty host hnin).2
          have hnil : ((w.st host).parked.filter fun p => p.sender == dead) = [] := by simp [hemptyP]
          simp [List.isEmpty, hnil] at hfull
      have hmsg : ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender := fun p hp => hO.parkMsg host p hp
      have hst : (setActor w host a).st = fun i => if i = host then a else w.st i := rfl
      have hr : (setActor w host a).roster = w.roster := rfl
      have hlife (i : InstId) : ((setActor w host a).st i).life = (w.st i).life := by
        by_cases hi : i = host
        · simp [setActor, hi, hlifeA]
        · simp [setActor, hi]
      have hOcc : OccInv I (setActor w host a) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hr]; exact hO.nodup
        · intro i hl
          exact hO.aliveIn i (by rw [← hlife i]; exact hl)
        · intro template i hi
          rw [actor_ix]
          exact hO.indexed template i (by simpa [setActor] using hi)
        · intro template ht
          rw [aliveCount_set_life w host a hlifeA template]
          exact hO.liveOne template ht
        · intro template ht
          rw [aliveCount_set_life w host a hlifeA template]
          exact hO.livePeer template ht
        · intro i hnin
          by_cases hi : i = host
          · exact absurd (hi ▸ hmem) hnin
          · rw [setActor_other w host i a hi]
            exact hO.offEmpty i hnin
        · intro i m hm
          by_cases hi : i = host
          · rw [hi, setActor_self, hboxA] at hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hO.sentFrom host m hm
            · rcases List.mem_map.mp hm with ⟨p, hp, rfl⟩
              have hin : p ∈ (w.st host).parked := (List.mem_filter.mp hp).1
              have hwho : p.sender = dead := beq_iff_eq.mp (List.mem_filter.mp hp).2
              have hpk := hmsg p hin
              simpa [hr, ← hpk, hwho] using hO.parkFrom host p hin
          · rw [setActor_other w host i a hi] at hm
            exact hO.sentFrom i m hm
        · intro i p hp
          by_cases hi : i = host
          · rw [hi, setActor_self, hparkA] at hp
            exact hO.parkFrom host p (List.mem_filter.mp hp).1
          · rw [setActor_other w host i a hi] at hp
            exact hO.parkFrom i p hp
        · intro i p hp
          by_cases hi : i = host
          · rw [hi, setActor_self, hparkA] at hp
            exact hmsg p (List.mem_filter.mp hp).1
          · rw [setActor_other w host i a hi] at hp
            exact hO.parkMsg i p hp
        · intro s d hs
          have howed := admit_owed w.st host dead d s w.roster hO.nodup hmem hmsg
          rw [hr] at hs
          rw [hst, hr, howed]
          by_cases hs' : s = host
          · simp [hs', htokA]
            exact hO.balance host d hmem
          · simp [hs']
            exact hO.balance s d hs
        · intro s d hs hl
          by_cases hs' : s = host
          · rw [hs'] at hl ⊢
            rw [setActor_self] at hl ⊢
            have hl0 : (w.st host).life = .alive := by rw [← hlifeA]; exact hl
            have hold := hO.slack host d hmem hl0
            simpa [pending, hphA, htyA, htokA] using hold
          · have hl0 : (w.st s).life = .alive := by rw [← hlife s]; exact hl
            have hold := hO.slack s d hs hl0
            rw [setActor_other w host s a hs']
            exact hold
        · intro s d hs hterm
          have howed := admit_owed w.st host dead d s w.roster hO.nodup hmem hmsg
          rw [hr] at hs
          rw [hst, hr, howed]
          exact hO.still s d hs hterm
        · intro s d hs hdead
          have howed := admit_owed w.st host dead d s w.roster hO.nodup hmem hmsg
          rw [hr] at hs
          rw [hst, hr, howed]
          by_cases hs' : s = host
          · rw [hs'] at hdead ⊢
            rw [setActor_self] at hdead
            rw [hlifeA] at hdead
            exact hO.quiet host d hmem hdead
          · rw [setActor_other w host s a hs'] at hdead
            exact hO.quiet s d hs hdead
        · intro i hl1
          by_cases hi : i = host
          · rw [hi] at hl1 ⊢
            rw [setActor_self, hparkA]
            have hemptyP := hO.clear host hl1
            simp [hemptyP]
          · rw [setActor_other w host i a hi]
            exact hO.clear i hl1
        · intro i hdead
          by_cases hi : i = host
          · rw [hi] at hdead ⊢
            rw [setActor_self] at hdead ⊢
            rw [hlifeA] at hdead
            have hemptyP := hO.deadEmpty host hdead
            simp [hboxA, hparkA, hemptyP.1, hemptyP.2]
          · rw [setActor_other w host i a hi] at hdead ⊢
            exact hO.deadEmpty i hdead
        · intro mb
          refine ⟨fun m hm => ?_, fun p hp => ?_⟩
          · by_cases hh : mb = host
            · rw [hh] at hm ⊢
              rw [setActor_self, hboxA] at hm
              rcases List.mem_append.mp hm with hm | hm
              · exact (queueOk_life w (setActor w host a) m.sender host (hlife m.sender)).1
                  ((hO.sameKey host).1 m hm)
              · rcases List.mem_map.mp hm with ⟨p, hp, rfl⟩
                have hin : p ∈ (w.st host).parked := (List.mem_filter.mp hp).1
                have hpk := hmsg p hin
                exact (queueOk_life w (setActor w host a) p.msg.sender host (hlife p.msg.sender)).1
                  (by simpa [hpk] using (hO.sameKey host).2 p hin)
            · rw [setActor_other w host mb a hh] at hm
              exact (queueOk_life w (setActor w host a) m.sender mb (hlife m.sender)).1
                ((hO.sameKey mb).1 m hm)
          · by_cases hh : mb = host
            · rw [hh] at hp ⊢
              rw [setActor_self, hparkA] at hp
              have hin : p ∈ (w.st host).parked := (List.mem_filter.mp hp).1
              exact (queueOk_life w (setActor w host a) p.sender host (hlife p.sender)).1
                ((hO.sameKey host).2 p hin)
            · rw [setActor_other w host mb a hh] at hp
              exact (queueOk_life w (setActor w host a) p.sender mb (hlife p.sender)).1
                ((hO.sameKey mb).2 p hp)
        · intro i hi
          exact hO.shaped i (by simpa [hr] using hi)
        · intro mb hk
          refine ⟨?_, ?_⟩
          · intro m hm
            by_cases hh : mb = host
            · rw [hh, setActor_self, hboxA] at hm
              rcases List.mem_append.mp hm with hm | hm
              · exact (hO.coreFrom host (hh ▸ hk)).1 m hm
              · rcases List.mem_map.mp hm with ⟨p, hp, rfl⟩
                have hin : p ∈ (w.st host).parked := (List.mem_filter.mp hp).1
                have hpk := hmsg p hin
                simpa [hpk] using (hO.coreFrom host (hh ▸ hk)).2 p hin
            · rw [setActor_other w host mb a hh] at hm
              exact (hO.coreFrom mb hk).1 m hm
          · intro p hp
            by_cases hh : mb = host
            · rw [hh, setActor_self, hparkA] at hp
              exact (hO.coreFrom host (hh ▸ hk)).2 p (List.mem_filter.mp hp).1
            · rw [setActor_other w host mb a hh] at hp
              exact (hO.coreFrom mb hk).2 p hp
      exact ⟨hOcc, by
        intro i
        by_cases hi : i = host
        · rw [hi, setActor_self]
          exact (contTy_match (w.st host) a hphA htyA).mp (hC host)
        · rw [setActor_other w host i a hi]
          exact hC i⟩

theorem occ_admitFold (I : Impl) (w : World) (dead : InstId) (ids : List InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) :
    OccInv I (ids.foldl (fun w host => admitHost w dead host) w) ∧
      ∀ i, contTy ((ids.foldl (fun w host => admitHost w dead host) w).st i) := by
  induction ids generalizing w with
  | nil => simpa using ⟨hO, hC⟩
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have hstep := occ_admitHost I w dead host hO hC
    exact ih _ hstep.1 hstep.2

theorem releaseParked_roster (w : World) (id : InstId) (ps : List Parked) :
    (releaseParked w id ps).roster = w.roster := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split
    · simpa [releaseParked] using ih w
    · have hih := ih (setActor w p.sender (resumeSender (w.st p.sender) false id))
      simp only [releaseParked, setActor] at hih ⊢
      exact hih

theorem releaseWorld_roster (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).roster = w.roster := by
  simp only [releaseWorld]
  rw [releaseParked_roster]
  simp only [setActor]
  rw [refundParked_roster, refundMsgs_roster, cellsRoster]

theorem admitHost_roster (w : World) (dead host : InstId) :
    (admitHost w dead host).roster = w.roster := by
  unfold admitHost
  split
  · rfl
  · split
    · rfl
    · simp [setActor]

theorem admitFold_roster (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w host => admitHost w dead host) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => simp
  | cons host ids ih =>
    simp only [List.foldl_cons]
    rw [ih, admitHost_roster]

theorem admitDead_roster (w : World) (dead : InstId) :
    (admitDead w dead).roster = w.roster := by
  simpa [admitDead] using admitFold_roster w dead w.roster

theorem abortActor_roster (D : Description) (w : World) (id : InstId) (a : Actor) :
    (abortActor D w id a).roster = w.roster := by
  simp only [abortActor, failWaiters, admitDead]
  rw [admitFold_roster, failWaiters_roster, releaseWorld_roster]

theorem abortDesc_roster (fuel : Nat) (D : Description) (w : World) (parent : InstId) :
    (abortDesc fuel D w parent).roster = w.roster := by
  induction fuel generalizing w parent with
  | zero => simp [abortDesc]
  | succ fuel ih =>
    simp only [abortDesc]
    suffices ∀ (ids : List InstId) (w0 : World),
        (ids.foldl (fun w child =>
          if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
            let w := abortDesc fuel D w child
            abortActor D w child (w.st child)
          else w) w0).roster = w0.roster by
      exact this w.roster w
    intro ids
    induction ids with
    | nil => intro w0; simp
    | cons c ids ihf =>
      intro w0
      simp only [List.foldl_cons]
      split
      · rw [ihf, abortActor_roster, ih]
      · rw [ihf]

theorem childTerminable_b (D : Description) (child : InstId) :
    childTerminable D child = terminableB D (tname child) := by
  simp [childTerminable, terminableB]

/-- Refunding a terminable actor's mailbox and resuming its parked senders
keeps the account. Outbound mail stays where it was. -/
theorem occ_releaseWorld (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hterm : terminableB I.desc (tname id) = true) :
    OccInv I (releaseWorld I.desc w id (w.st id)) ∧
      ∀ i, contTy ((releaseWorld I.desc w id (w.st id)).st i) := by
  let wR := readCells I.desc w id
  have hOR := occ_same I w wR hO (fun i => readCells_st I.desc w id i)
    (read_roster I.desc w id).1 (read_roster I.desc w id).2 (fun n => read_ix I.desc w id n)
  have hcontR : ∀ i, contTy (wR.st i) := by
    intro i
    have hs := readCells_st I.desc w id i
    exact (contTy_match _ _ (congrArg Actor.phase hs) (congrArg Actor.typestate hs)).mpr (hC i)
  have hmemR : id ∈ wR.roster := by
    have hr := (read_roster I.desc w id).1
    simpa [wR, hr] using hmem
  have hst := readCells_st I.desc w id id
  have hgot := occ_term_kill I wR id hOR hcontR hmemR hterm (fun p hp => hOR.parkMsg id p hp)
  rw [← hst]
  simp only [releaseWorld]
  exact ⟨by simpa [wR] using hgot.2.1, by simpa [wR] using hgot.2.2⟩

theorem occ_failFold (I : Impl) (w : World) (dead : InstId) (ids : List InstId) (hO : OccInv I w)
    (hC : ∀ j, contTy (w.st j)) :
    OccInv I (ids.foldl (fun w i => failWaiter w dead i) w) ∧
      ∀ j, contTy ((ids.foldl (fun w i => failWaiter w dead i) w).st j) := by
  induction ids generalizing w with
  | nil => simpa using ⟨hO, hC⟩
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have hstep := occ_failWaiter I w dead i hO hC
    exact ih _ hstep.1 hstep.2

theorem occ_abortActor (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hterm : terminableB I.desc (tname id) = true) :
    OccInv I (abortActor I.desc w id (w.st id)) ∧
      ∀ i, contTy ((abortActor I.desc w id (w.st id)).st i) := by
  have hrel := occ_releaseWorld I w id hO hC hmem hterm
  let released := releaseWorld I.desc w id (w.st id)
  have hfail := occ_failFold I released id released.roster hrel.1 hrel.2
  let failed := released.roster.foldl (fun w i => failWaiter w id i) released
  have hrost : failed.roster = released.roster := by
    simpa [failed, failWaiters] using failWaiters_roster released id released.roster
  have hadmit := occ_admitFold I failed id failed.roster hfail.1 hfail.2
  simpa [abortActor, released, failed, failWaiters, admitDead, hrost] using hadmit

/-- A priority tombstone does not spend bulk credit or change a mailbox. -/
theorem occ_tombstone (I : Impl) (w : World) (child : InstId) (hO : OccInv I w) :
    OccInv I (enqueueTombstone I.desc w child) := by
  cases hsup : supervisorOf I.desc child with
  | none =>
    simp [enqueueTombstone, hsup]
    exact hO
  | some parent =>
    simp [enqueueTombstone, hsup]
    by_cases hlive : (w.st parent).life = .alive
    · simp [hlive]
      apply occ_keep I w parent
          { life := .alive
            typestate := (w.st parent).typestate
            phase := (w.st parent).phase
            box := (w.st parent).box
            prio := (w.st parent).prio ++ [tombstoneMsg (w.st parent) child]
            parked := (w.st parent).parked
            tokens := (w.st parent).tokens
            nextMid := (w.st parent).nextMid + 1
            waitId := (w.st parent).waitId
            nextCall := (w.st parent).nextCall
            oweId := (w.st parent).oweId
            lastCall := (w.st parent).lastCall }
          hO hlive.symm rfl rfl (fun _ => rfl) rfl
      intro d
      simp [pending]
    · simp [hlive]
      exact hO

theorem occ_abortDesc (fuel : Nat) (I : Impl) (w : World) (parent : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) :
    OccInv I (abortDesc fuel I.desc w parent) ∧
      ∀ i, contTy ((abortDesc fuel I.desc w parent).st i) := by
  induction fuel generalizing w parent with
  | zero =>
    simp [abortDesc]
    exact ⟨hO, hC⟩
  | succ fuel ih =>
    simp only [abortDesc]
    suffices ∀ (ids : List InstId) (w0 : World), OccInv I w0 → (∀ i, contTy (w0.st i)) →
        OccInv I (ids.foldl (fun w child =>
          if isChild I.desc parent child && (w.st child).life == .alive &&
              childTerminable I.desc child then
            let w := abortDesc fuel I.desc w child
            abortActor I.desc w child (w.st child)
          else w) w0) ∧
          ∀ i, contTy ((ids.foldl (fun w child =>
            if isChild I.desc parent child && (w.st child).life == .alive &&
                childTerminable I.desc child then
              let w := abortDesc fuel I.desc w child
              abortActor I.desc w child (w.st child)
            else w) w0).st i) by
      exact this w.roster w hO hC
    intro ids
    induction ids with
    | nil =>
      intro w0 hO0 hC0
      simp
      exact ⟨hO0, hC0⟩
    | cons c ids ihf =>
      intro w0 hO0 hC0
      simp only [List.foldl_cons]
      by_cases hgo : (isChild I.desc parent c && (w0.st c).life == .alive &&
          childTerminable I.desc c) = true
      · rw [if_pos hgo]
        have hparts := by simpa [Bool.and_eq_true, beq_iff_eq, childTerminable_b] using hgo
        have hlive : (w0.st c).life = .alive := hparts.1.2
        have hterm : terminableB I.desc (tname c) = true := hparts.2
        have hmem : c ∈ w0.roster := hO0.aliveIn c hlive
        have hdesc := ih w0 c hO0 hC0
        have hmem1 : c ∈ (abortDesc fuel I.desc w0 c).roster := by
          rw [abortDesc_roster]
          exact hmem
        have hab := occ_abortActor I (abortDesc fuel I.desc w0 c) c hdesc.1 hdesc.2 hmem1 hterm
        exact ihf (abortActor I.desc (abortDesc fuel I.desc w0 c) c
          ((abortDesc fuel I.desc w0 c).st c)) hab.1 hab.2
      · rw [if_neg hgo]
        exact ihf w0 hO0 hC0

/-- A committing `terminate` aborts the stage's descendants, then the stage, and
leaves the parent a priority tombstone. Sibling mail stays. -/
theorem occ_terminate (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hterm : terminableB I.desc (tname id) = true) :
    OccInv I (terminateStage I.desc w id (w.st id)) := by
  have hdesc := occ_abortDesc w.roster.length I w id hO hC
  have hmem1 : id ∈ (abortDesc w.roster.length I.desc w id).roster := by
    rw [abortDesc_roster]
    exact hmem
  have hab := occ_abortActor I (abortDesc w.roster.length I.desc w id) id hdesc.1 hdesc.2 hmem1 hterm
  have htomb := occ_tombstone I (abortActor I.desc (abortDesc w.roster.length I.desc w id) id
    ((abortDesc w.roster.length I.desc w id).st id)) id hab.1
  simpa [terminateStage] using htomb


theorem addTokens_at (a : Actor) (name : String) (n : Nat) (d : String) :
    (addTokens a name n).tokens d = a.tokens d + if d = name then n else 0 := by
  unfold addTokens
  by_cases hd : d = name
  · simp [hd]
  · have hb : (d == name) = false := by simpa [beq_iff_eq] using hd
    simp [hd, hb]

theorem slot_outbound (st : InstId → Actor) (dead host : InstId) (dst : String)
    (hname : tname host = dst) :
    slot st dst dead host = outboundCount dead (st host) := by
  have hb : (tname host == dst) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb, outboundCount, countFrom_len, countParked_len]

theorem strip_slot_self (st : InstId → Actor) (dead host : InstId) (dst : String)
    (hname : tname host = dst) :
    slot (fun i => if i = host then stripSender dead (st host) else st i) dst dead host = 0 := by
  have hb : (tname host == dst) = true := by simpa [beq_iff_eq] using hname
  simp [slot, hb, stripSender, countFrom_filter_self, countParked_filter_self]

theorem strip_slot_other (st : InstId → Actor) (dead host sender : InstId) (dst : String)
    (hne : sender ≠ dead) :
    slot (fun i => if i = host then stripSender dead (st host) else st i) dst sender host =
      slot st dst sender host := by
  simp [slot, stripSender, countFrom_filter_other _ _ hne, countParked_filter_other _ _ hne]

/-- Returning one host's outbound slots keeps the credit invariant. -/
theorem occ_forgetHost (I : Impl) (w : World) (dead host : InstId) (hO : OccInv I w)
    (hdead : dead ∈ w.roster) (hhost : host ∈ w.roster) :
    OccInv I (forgetHost w dead host) := by
  by_cases hself : host = dead
  · simp [forgetHost, hself]
    exact hO
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      simp [forgetHost, hb, hn]
      exact hO
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      let n := outboundCount dead (w.st host)
      have hpos : 0 < n := Nat.pos_of_ne_zero hz
      let stripped := stripSender dead (w.st host)
      let mid := setActor w host stripped
      let bumped := addTokens (mid.st dead) (tname host) n
      have hw : forgetHost w dead host = setActor mid dead bumped := by
        simp [forgetHost, hb, hn, mid, bumped, stripped, n]
      rw [hw]
      have hswap : dead ≠ host := fun h => hself h.symm
      have hmidDead : mid.st dead = w.st dead := by
        simpa [mid] using setActor_other w host dead stripped hswap
      have hst : ∀ i, (setActor mid dead bumped).st i =
          if i = dead then bumped else if i = host then stripped else w.st i := by
        intro i
        by_cases hid : i = dead
        · simp [hid, setActor]
        · by_cases hih : i = host
          · simp [hid, hih, setActor, mid]
          · simp [hid, hih, setActor, mid]
      have hr : (setActor mid dead bumped).roster = w.roster := by simp [mid, setActor]
      have hN : (setActor mid dead bumped).N = w.N := by simp [mid, setActor]
      have hix : (setActor mid dead bumped).nextIx = w.nextIx := by simp [mid, setActor]
      have hlife : ∀ i, ((setActor mid dead bumped).st i).life = (w.st i).life := by
        intro i
        simpa [hw] using (forgetHost_stable w dead host i).2.1
      have hboxPark : ∀ i,
          ((setActor mid dead bumped).st i).box =
            (if i = host then stripped else w.st i).box ∧
          ((setActor mid dead bumped).st i).parked =
            (if i = host then stripped else w.st i).parked := by
        intro i
        by_cases hid : i = dead
        · rw [hid, setActor_self]
          constructor
          · simp [hswap, bumped, addTokens, hmidDead]
          · simp [hswap, bumped, addTokens, hmidDead]
        · by_cases hih : i = host
          · rw [hih, setActor_other mid dead host bumped hself]
            simp [mid, setActor]
          · rw [setActor_other mid dead i bumped hid, setActor_other w host i stripped hih]
            simp [hih]
      have htokDead (d : String) : ((setActor mid dead bumped).st dead).tokens d =
          (w.st dead).tokens d + if d = tname host then n else 0 := by
        rw [setActor_self]
        simp [bumped, addTokens_at, hmidDead]
      have htokOther (s : InstId) (d : String) (hsD : s ≠ dead) :
          ((setActor mid dead bumped).st s).tokens d = (w.st s).tokens d := by
        by_cases hsH : s = host
        · rw [hsH] at hsD ⊢
          rw [setActor_other mid dead host bumped hself]
          simp [mid, setActor, stripped, stripSender]
        · rw [setActor_other mid dead s bumped hsD, setActor_other w host s stripped hsH]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hr] using hO.nodup
      · intro i hl
        rw [hr]
        exact hO.aliveIn i (by rw [← hlife i]; exact hl)
      · intro template i hi
        simpa [hix] using hO.indexed template i hi
      · intro template ht
        have hc : aliveCount (setActor mid dead bumped) template = aliveCount w template := by
          rw [aliveCount_sum, aliveCount_sum, hr]
          refine sum_congr _ _ w.roster ?_
          intro i _
          simp [aliveBit, hlife i]
        simpa [hc] using hO.liveOne template ht
      · intro template ht
        have hc : aliveCount (setActor mid dead bumped) template = aliveCount w template := by
          rw [aliveCount_sum, aliveCount_sum, hr]
          refine sum_congr _ _ w.roster ?_
          intro i _
          simp [aliveBit, hlife i]
        simpa [hc, hN] using hO.livePeer template ht
      · intro i hnin
        rw [hr] at hnin
        have hneD : i ≠ dead := fun h => hnin (h ▸ hdead)
        have hneH : i ≠ host := fun h => hnin (h ▸ hhost)
        simpa [hst, hneD, hneH] using hO.offEmpty i hnin
      · intro i m hm
        rw [hboxPark i |>.1] at hm
        rw [hr]
        by_cases hih : i = host
        · simp [hih, stripped, stripSender] at hm
          exact hO.sentFrom host m hm.1
        · simp [hih] at hm
          exact hO.sentFrom i m hm
      · intro i p hp
        rw [hboxPark i |>.2] at hp
        rw [hr]
        by_cases hih : i = host
        · simp [hih, stripped, stripSender] at hp
          exact hO.parkFrom host p hp.1
        · simp [hih] at hp
          exact hO.parkFrom i p hp
      · intro i p hp
        rw [hboxPark i |>.2] at hp
        by_cases hih : i = host
        · simp [hih, stripped, stripSender] at hp
          exact hO.parkMsg host p hp.1
        · simp [hih] at hp
          exact hO.parkMsg i p hp
      · intro s d hs
        rw [hr] at hs ⊢
        let st1 := fun i => if i = host then stripped else w.st i
        have howed1 : owed (setActor mid dead bumped).st d s w.roster = owed st1 d s w.roster := by
          refine owed_mail_eq _ _ _ _ w.roster ?_
          intro i _
          exact ⟨(hboxPark i).1, (hboxPark i).2⟩
        have hrep := owed_replace w.st d s host stripped w.roster hO.nodup hhost
        have hbal := hO.balance s d hs
        by_cases hsD : s = dead
        · by_cases hd : d = tname host
          · have holdS : slot w.st d s host = n := by
              rw [hsD]; exact slot_outbound w.st dead host d hd.symm
            have hnewS : slot st1 d s host = 0 := by
              rw [hsD]; exact strip_slot_self w.st dead host d hd.symm
            have hsum : owed st1 d s w.roster + n = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, holdS, hnewS] at hrep'
              omega
            have htokN : ((setActor mid dead bumped).st s).tokens d = (w.st s).tokens d + n := by
              rw [hsD]; simpa [hd] using htokDead d
            have howedN : owed (setActor mid dead bumped).st d s w.roster + n =
                owed w.st d s w.roster := by simpa [howed1] using hsum
            omega
          · have hb0 : (tname host == d) = false := by simpa [beq_iff_eq] using Ne.symm hd
            have hslot0 : slot w.st d s host = 0 := by rw [hsD]; simp [slot, hb0]
            have hslot1 : slot st1 d s host = 0 := by rw [hsD]; simp [slot, st1, hb0]
            have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, hslot0, hslot1] at hrep'
              omega
            have htok0 : ((setActor mid dead bumped).st s).tokens d = (w.st s).tokens d := by
              rw [hsD]; simpa [hd] using htokDead d
            simpa [howed1, hsame, htok0, hbal]
        · have hslot := strip_slot_other w.st dead host s d hsD
          have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
            have hrep' : owed st1 d s w.roster + slot w.st d s host =
                owed w.st d s w.roster + slot st1 d s host := by simpa [st1] using hrep
            have hslot' : slot st1 d s host = slot w.st d s host := by simpa [st1] using hslot
            rw [hslot'] at hrep'
            omega
          have htok0 := htokOther s d hsD
          simpa [howed1, hsame, htok0, hbal]
      · intro s d hs hlive'
        rw [hr] at hs
        have hlive0 : (w.st s).life = .alive := by rw [← hlife s]; exact hlive'
        have hpend : pending ((setActor mid dead bumped).st s) d = pending (w.st s) d := by
          have hph := by simpa [hw] using (forgetHost_stable w dead host s).1
          have hty := by simpa [hw] using (forgetHost_stable w dead host s).2.2.1
          simp [pending, hph, hty]
        have hfloor : floorState I.desc (tname s) ((setActor mid dead bumped).st s).typestate d =
            floorState I.desc (tname s) (w.st s).typestate d := by
          have hty := by simpa [hw] using (forgetHost_stable w dead host s).2.2.1
          simp [hty]
        have hold := hO.slack s d hs hlive0
        have htokGe : ((setActor mid dead bumped).st s).tokens d ≥ (w.st s).tokens d := by
          by_cases hsD : s = dead
          · rw [hsD]
            have h := htokDead d
            split at h <;> omega
          · rw [htokOther s d hsD]
            exact Nat.le_refl _
        omega
      · intro s d hs hterm
        rw [hr] at hs ⊢
        let st1 := fun i => if i = host then stripped else w.st i
        have howed1 : owed (setActor mid dead bumped).st d s w.roster = owed st1 d s w.roster := by
          refine owed_mail_eq _ _ _ _ w.roster ?_
          intro i _
          exact ⟨(hboxPark i).1, (hboxPark i).2⟩
        have hrep := owed_replace w.st d s host stripped w.roster hO.nodup hhost
        have hzero := hO.still s d hs hterm
        by_cases hsD : s = dead
        · by_cases hd : d = tname host
          · have holdS : slot w.st d s host = n := by
              rw [hsD]; exact slot_outbound w.st dead host d hd.symm
            have hnewS : slot st1 d s host = 0 := by
              rw [hsD]; exact strip_slot_self w.st dead host d hd.symm
            have hsum : owed st1 d s w.roster + n = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, holdS, hnewS] at hrep'
              omega
            exfalso
            omega
          · have hb0 : (tname host == d) = false := by simpa [beq_iff_eq] using Ne.symm hd
            have hslot0 : slot w.st d s host = 0 := by rw [hsD]; simp [slot, hb0]
            have hslot1 : slot st1 d s host = 0 := by rw [hsD]; simp [slot, st1, hb0]
            have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, hslot0, hslot1] at hrep'
              omega
            simpa [howed1, hsame, hzero]
        · have hslot := strip_slot_other w.st dead host s d hsD
          have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
            have hrep' : owed st1 d s w.roster + slot w.st d s host =
                owed w.st d s w.roster + slot st1 d s host := by simpa [st1] using hrep
            have hslot' : slot st1 d s host = slot w.st d s host := by simpa [st1] using hslot
            rw [hslot'] at hrep'
            omega
          simpa [howed1, hsame, hzero]
      · intro s d hs hdeadLife
        rw [hr] at hs ⊢
        have hdead0 : (w.st s).life ≠ .alive := by rw [← hlife s]; exact hdeadLife
        let st1 := fun i => if i = host then stripped else w.st i
        have howed1 : owed (setActor mid dead bumped).st d s w.roster = owed st1 d s w.roster := by
          refine owed_mail_eq _ _ _ _ w.roster ?_
          intro i _
          exact ⟨(hboxPark i).1, (hboxPark i).2⟩
        have hrep := owed_replace w.st d s host stripped w.roster hO.nodup hhost
        have hzero := hO.quiet s d hs hdead0
        by_cases hsD : s = dead
        · by_cases hd : d = tname host
          · have holdS : slot w.st d s host = n := by
              rw [hsD]; exact slot_outbound w.st dead host d hd.symm
            have hnewS : slot st1 d s host = 0 := by
              rw [hsD]; exact strip_slot_self w.st dead host d hd.symm
            have hsum : owed st1 d s w.roster + n = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, holdS, hnewS] at hrep'
              omega
            rw [howed1]
            omega
          · have hb0 : (tname host == d) = false := by simpa [beq_iff_eq] using Ne.symm hd
            have hslot0 : slot w.st d s host = 0 := by rw [hsD]; simp [slot, hb0]
            have hslot1 : slot st1 d s host = 0 := by rw [hsD]; simp [slot, st1, hb0]
            have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
              have hrep' := hrep
              simp [st1, hslot0, hslot1] at hrep'
              omega
            simpa [howed1, hsame, hzero]
        · have hslot := strip_slot_other w.st dead host s d hsD
          have hsame : owed st1 d s w.roster = owed w.st d s w.roster := by
            have hrep' : owed st1 d s w.roster + slot w.st d s host =
                owed w.st d s w.roster + slot st1 d s host := by simpa [st1] using hrep
            have hslot' : slot st1 d s host = slot w.st d s host := by simpa [st1] using hslot
            rw [hslot'] at hrep'
            omega
          simpa [howed1, hsame, hzero]
      · intro i hl1
        by_cases hid : i = dead
        · rw [hid] at hl1 ⊢
          rw [setActor_self]
          simp [bumped, addTokens, hmidDead]
          exact hO.clear dead hl1
        · by_cases hih : i = host
          · rw [hih] at hl1 ⊢
            rw [setActor_other mid dead host bumped hself]
            have hempty := hO.clear host hl1
            simp [mid, setActor, stripped, stripSender, hempty]
          · rw [setActor_other mid dead i bumped hid, setActor_other w host i stripped hih]
            exact hO.clear i hl1
      · intro i hdead
        have hdead0 : (w.st i).life ≠ .alive := by rw [← hlife i]; exact hdead
        rw [hst i]
        by_cases hid : i = dead
        · simp [hid, bumped, addTokens, hmidDead]
          exact hO.deadEmpty dead (by rw [hid] at hdead0; exact hdead0)
        · by_cases hih : i = host
          · rw [hih]
            have hempty := hO.deadEmpty host (by rw [hih] at hdead0; exact hdead0)
            simp [hself, stripped, stripSender, hempty]
          · simp [hid, hih]
            exact hO.deadEmpty i hdead0
      · intro host'
        refine ⟨fun m hm => ?_, fun p hp => ?_⟩
        · rw [hst host'] at hm
          by_cases hid : host' = dead
          · rw [hid] at hm ⊢
            simp [bumped, addTokens, hmidDead] at hm
            exact (queueOk_life w _ m.sender dead (hlife m.sender)).1
              ((hO.sameKey dead).1 m hm)
          · by_cases hih : host' = host
            · rw [hih] at hm ⊢
              simp [hself, stripped, stripSender] at hm
              have hold : m ∈ (w.st host).box := hm.1
              exact (queueOk_life w _ m.sender host (hlife m.sender)).1
                ((hO.sameKey host).1 m hold)
            · simp [hid, hih] at hm
              exact (queueOk_life w _ m.sender host' (hlife m.sender)).1
                ((hO.sameKey host').1 m hm)
        · rw [hst host'] at hp
          by_cases hid : host' = dead
          · rw [hid] at hp ⊢
            simp [bumped, addTokens, hmidDead] at hp
            exact (queueOk_life w _ p.sender dead (hlife p.sender)).1
              ((hO.sameKey dead).2 p hp)
          · by_cases hih : host' = host
            · rw [hih] at hp ⊢
              simp [hself, stripped, stripSender] at hp
              have hold : p ∈ (w.st host).parked := hp.1
              exact (queueOk_life w _ p.sender host (hlife p.sender)).1
                ((hO.sameKey host).2 p hold)
            · simp [hid, hih] at hp
              exact (queueOk_life w _ p.sender host' (hlife p.sender)).1
                ((hO.sameKey host').2 p hp)
      · intro i hi
        exact hO.shaped i (by rw [hr] at hi; exact hi)
      · intro mb hk
        refine ⟨fun m hm => ?_, fun p hp => ?_⟩
        · rw [hst mb] at hm
          by_cases hid : mb = dead
          · simp [hid, bumped, addTokens, hmidDead] at hm
            exact (hO.coreFrom dead (hid ▸ hk)).1 m hm
          · by_cases hih : mb = host
            · rw [hih] at hm
              simp [hself, stripped, stripSender] at hm
              exact (hO.coreFrom host (hih ▸ hk)).1 m hm.1
            · simp [hid, hih] at hm
              exact (hO.coreFrom mb hk).1 m hm
        · rw [hst mb] at hp
          by_cases hid : mb = dead
          · simp [hid, bumped, addTokens, hmidDead] at hp
            exact (hO.coreFrom dead (hid ▸ hk)).2 p hp
          · by_cases hih : mb = host
            · rw [hih] at hp
              simp [hself, stripped, stripSender] at hp
              exact (hO.coreFrom host (hih ▸ hk)).2 p hp.1
            · simp [hid, hih] at hp
              exact (hO.coreFrom mb hk).2 p hp

/-- No roster mailbox holds parked mail from a lone terminable: it never sends. -/
theorem terminable_unsent (I : Impl) (w : World) (hO : OccInv I w) (id : InstId)
    (hmem : id ∈ w.roster) (hterm : loneTerminableName I.desc (tname id)) :
    ∀ i ∈ w.roster, ∀ p ∈ (w.st i).parked, p.sender ≠ id := by
  intro i hi p hp
  have hz := hO.still id (tname i) hmem hterm
  have hle := owed_ge_here w.st (tname i) id i w.roster hO.nodup hi rfl
  have hzero : countParked id (w.st i).parked = 0 := by
    have hle' : countFrom id (w.st i).box + countParked id (w.st i).parked ≤ 0 := by
      simpa [hz] using hle
    omega
  exact countParked_zero_sender id _ hzero p hp

/-- `killOne` is the refund of the victim's own inbox, then the reclaim of its
outbound mail, then the removal. The two credit passes count the same tokens. -/
theorem killOne_eq_account (w : World) (D : Description) (id : InstId) :
    killOne w D id =
      let base := readCells D w id
      let wF := failWaiters base id
      let name := tname id
      let refunded := refundParked (refundMsgs wF name (wF.st id).box) name (wF.st id).parked
      let forgotten := forgetSender refunded id
      setActor forgotten id
        { (forgotten.st id) with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  let w3 := refundParked w2 (tname id) (w.st id).parked
  let w4 := failWaiters w3 id
  let w5 := forgetSender w4 id
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  have hcomm : w4 =
      refundParked (refundMsgs (failWaiters w1 id) (tname id) (w.st id).box) (tname id) (w.st id).parked := by
    simpa [w4, w3, w2, failWaiters] using
      failWaiters_refund w1 id (tname id) (w.st id).box (w.st id).parked
  have hboxF : ((failWaiters w1 id).st id).box = (w.st id).box := by
    have hb := (failFold_mail w1 id id w1.roster).1
    have hs := congrArg (·.box) (readCells_st D w id id)
    simpa [w1, failWaiters] using hb.trans hs
  have hparkF : ((failWaiters w1 id).st id).parked = (w.st id).parked := by
    have hp := (failFold_mail w1 id id w1.roster).2.2
    have hs := congrArg (·.parked) (readCells_st D w id id)
    simpa [w1, failWaiters] using hp.trans hs
  have hw5 : w5 = forgetSender
      (refundParked (refundMsgs (failWaiters w1 id) (tname id) ((failWaiters w1 id).st id).box)
        (tname id) ((failWaiters w1 id).st id).parked) id := by
    rw [← hboxF, ← hparkF] at hcomm
    simpa [w5] using congrArg (fun z => forgetSender z id) hcomm
  rw [hbody, hw5]

theorem forgetHost_keeps_self (w : World) (dead host : InstId) :
    ((forgetHost w dead host).st dead).box = (w.st dead).box ∧
      ((forgetHost w dead host).st dead).parked = (w.st dead).parked := by
  by_cases hself : host = dead
  · simp [forgetHost, hself]
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    by_cases hz : outboundCount dead (w.st host) = 0
    · have hn : (outboundCount dead (w.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      simp [forgetHost, hb, hn]
    · have hn : (outboundCount dead (w.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      let n := outboundCount dead (w.st host)
      let stripped := stripSender dead (w.st host)
      let mid := setActor w host stripped
      let bumped := addTokens (mid.st dead) (tname host) n
      have hw : forgetHost w dead host = setActor mid dead bumped := by
        simp [forgetHost, hb, hn, mid, bumped, stripped, n]
      have hmid : mid.st dead = w.st dead := by
        simpa [mid] using setActor_other w host dead stripped fun h => hself h.symm
      rw [hw, setActor_self]
      simp [bumped, addTokens, hmid]

/-- Reclaiming outbound mail never rewrites the victim's own mailbox. -/
theorem forget_keeps_self (w : World) (dead : InstId) :
    ((forgetSender w dead).st dead).box = (w.st dead).box ∧
      ((forgetSender w dead).st dead).parked = (w.st dead).parked := by
  have hfold : ∀ (ids : List InstId) (w' : World),
      ((ids.foldl (fun w host => forgetHost w dead host) w').st dead).box = (w'.st dead).box ∧
        ((ids.foldl (fun w host => forgetHost w dead host) w').st dead).parked =
          (w'.st dead).parked := by
    intro ids
    induction ids with
    | nil => intro w'; exact ⟨rfl, rfl⟩
    | cons host ids ih =>
      intro w'
      simp only [List.foldl_cons]
      have hstep := forgetHost_keeps_self w' dead host
      have htail := ih (forgetHost w' dead host)
      exact ⟨htail.1.trans hstep.1, htail.2.trans hstep.2⟩
  simpa [forgetSender] using hfold w.roster w

theorem owed_slots_zero (st : InstId → Actor) (dst : String) (sender : InstId) (ids : List InstId)
    (h : ∀ i ∈ ids, slot st dst sender i = 0) : owed st dst sender ids = 0 := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    rw [owed_cons, h i (List.Mem.head _), ih fun j hj => h j (List.Mem.tail _ hj)]

/-- After the reclaim, the victim owes nothing: its own box was already empty and
every other mailbox has lost its messages. -/
theorem forget_slot_zero (w : World) (dead : InstId) (d : String) (i : InstId) (hi : i ∈ w.roster)
    (hbox : (w.st dead).box = []) (hpark : (w.st dead).parked = []) :
    slot (forgetSender w dead).st d dead i = 0 := by
  by_cases hself : i = dead
  · rw [hself]
    have hkeep := forget_keeps_self w dead
    have hb : ((forgetSender w dead).st dead).box = [] := hkeep.1.trans hbox
    have hp : ((forgetSender w dead).st dead).parked = [] := hkeep.2.trans hpark
    simp [slot, hb, hp, countFrom, countParked]
  · have hboxF := forget_box_of_mem w dead i hi hself
    have hparkF := forget_parked_of_mem w dead i hi hself
    by_cases hname : tname i = d
    · have hb : (tname i == d) = true := by simpa [beq_iff_eq] using hname
      simp [slot, hb, hboxF, hparkF, countFrom_filter_self, countParked_filter_self]
    · have hb : (tname i == d) = false := by simpa [beq_iff_eq] using hname
      simp [slot, hb]

theorem occ_forget (I : Impl) (w : World) (dead : InstId) (hO : OccInv I w) (hdead : dead ∈ w.roster) :
    OccInv I (forgetSender w dead) := by
  have hfold : ∀ (ids : List InstId) (w' : World), OccInv I w' → dead ∈ w'.roster →
      (∀ i ∈ ids, i ∈ w'.roster) →
      OccInv I (ids.foldl (fun w host => forgetHost w dead host) w') := by
    intro ids
    induction ids with
    | nil => intro w' hO' _ _; exact hO'
    | cons host ids ih =>
      intro w' hO' hdead' hids
      simp only [List.foldl_cons]
      have hO1 := occ_forgetHost I w' dead host hO' hdead' (hids host (List.Mem.head _))
      have hr := forgetHost_roster w' dead host
      exact ih (forgetHost w' dead host) hO1 (by simpa [hr] using hdead')
        fun i hi => by simpa [hr] using hids i (List.Mem.tail _ hi)
  exact hfold w.roster w hO hdead fun i hi => hi

/-- Draining a mailbox and refunding it credit the same actors, so everyone else
is unchanged and the victim keeps the same tokens. -/
theorem drain_refund_other (w : World) (id i : InstId) (hi : i ≠ id) :
    (drainPark (drainBox w id (tname id) (w.st id).box) id (tname id) (w.st id).parked).st i =
      (refundParked (refundMsgs w (tname id) (w.st id).box) (tname id) (w.st id).parked).st i := by
  have h := term_actor w id i
  simp [setActor, hi] at h
  exact h

theorem drain_refund_kept (w : World) (id : InstId) :
    let drained := drainPark (drainBox w id (tname id) (w.st id).box) id (tname id) (w.st id).parked
    let refunded := refundParked (refundMsgs w (tname id) (w.st id).box) (tname id) (w.st id).parked
    (∀ d, (drained.st id).tokens d = (refunded.st id).tokens d) ∧
      (drained.st id).typestate = (refunded.st id).typestate ∧
      (drained.st id).nextMid = (refunded.st id).nextMid ∧
      sameStamps (drained.st id) (refunded.st id) := by
  have h := term_actor w id id
  simp [setActor] at h
  refine ⟨fun d => congrFun h.2.1 d, h.1, ?_, ?_⟩
  · exact h.2.2.1
  · exact sameStamps_trans
      (drainP_stamps (drainBox w id (tname id) (w.st id).box) id (tname id) (w.st id).parked id)
      (sameStamps_trans (drain_stamps w id (tname id) (w.st id).box id)
        (sameStamps_trans (sameStamps_symm (refund_stamps w (tname id) (w.st id).box id))
          (sameStamps_symm (refundP_stamps (refundMsgs w (tname id) (w.st id).box) (tname id)
            (w.st id).parked id))))

theorem forgetHost_agree (w1 w2 : World) (dead host : InstId)
    (hother : ∀ i, i ≠ dead → w1.st i = w2.st i)
    (htok : ∀ d, (w1.st dead).tokens d = (w2.st dead).tokens d)
    (hty : (w1.st dead).typestate = (w2.st dead).typestate)
    (hmid : (w1.st dead).nextMid = (w2.st dead).nextMid) :
    (∀ i, i ≠ dead → (forgetHost w1 dead host).st i = (forgetHost w2 dead host).st i) ∧
      (∀ d, ((forgetHost w1 dead host).st dead).tokens d =
        ((forgetHost w2 dead host).st dead).tokens d) ∧
      ((forgetHost w1 dead host).st dead).typestate =
        ((forgetHost w2 dead host).st dead).typestate ∧
      ((forgetHost w1 dead host).st dead).nextMid =
        ((forgetHost w2 dead host).st dead).nextMid := by
  by_cases hself : host = dead
  · simp [forgetHost, hself]
    exact ⟨hother, htok, hty, hmid⟩
  · have hb : (host == dead) = false := by simpa [beq_iff_eq] using hself
    have hc : outboundCount dead (w1.st host) = outboundCount dead (w2.st host) := by
      simp [outboundCount, hother host hself]
    by_cases hz : outboundCount dead (w1.st host) = 0
    · have hn : (outboundCount dead (w1.st host) == 0) = true := by simpa [beq_iff_eq] using hz
      have hz2 : outboundCount dead (w2.st host) = 0 := hc.symm.trans hz
      have hn2 : (outboundCount dead (w2.st host) == 0) = true := by simpa [beq_iff_eq] using hz2
      simp [forgetHost, hb, hn, hn2]
      exact ⟨hother, htok, hty, hmid⟩
    · have hn : (outboundCount dead (w1.st host) == 0) = false := by simpa [beq_iff_eq] using hz
      have hz2 : ¬ outboundCount dead (w2.st host) = 0 := fun h => hz (hc.trans h)
      have hn2 : (outboundCount dead (w2.st host) == 0) = false := by simpa [beq_iff_eq] using hz2
      let n := outboundCount dead (w1.st host)
      let mid1 := setActor w1 host (stripSender dead (w1.st host))
      let mid2 := setActor w2 host (stripSender dead (w2.st host))
      let b1 := addTokens (mid1.st dead) (tname host) n
      let b2 := addTokens (mid2.st dead) (tname host) n
      have hw1 : forgetHost w1 dead host = setActor mid1 dead b1 := by
        simp [forgetHost, hb, hn, mid1, b1, n]
      have hw2 : forgetHost w2 dead host = setActor mid2 dead b2 := by
        simp [forgetHost, hb, hn2, mid2, b2, n, hc]
      have hm1 : mid1.st dead = w1.st dead := by
        simpa [mid1] using setActor_other w1 host dead (stripSender dead (w1.st host))
          fun h => hself h.symm
      have hm2 : mid2.st dead = w2.st dead := by
        simpa [mid2] using setActor_other w2 host dead (stripSender dead (w2.st host))
          fun h => hself h.symm
      rw [hw1, hw2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hih : i = host
        · rw [hih, setActor_other mid1 dead host b1 hself, setActor_other mid2 dead host b2 hself]
          simp [mid1, mid2, setActor, stripSender, hother host hself]
        · rw [setActor_other mid1 dead i b1 hi, setActor_other mid2 dead i b2 hi,
            setActor_other w1 host i (stripSender dead (w1.st host)) hih,
            setActor_other w2 host i (stripSender dead (w2.st host)) hih]
          exact hother i hi
      · intro d
        rw [setActor_self, setActor_self]
        simp [b1, b2, addTokens_at, hm1, hm2, htok]
      · rw [setActor_self, setActor_self]
        simp [b1, b2, addTokens, hm1, hm2, hty]
      · rw [setActor_self, setActor_self]
        simp [b1, b2, addTokens, hm1, hm2, hmid]

theorem forget_agree (w1 w2 : World) (dead : InstId) (hr : w1.roster = w2.roster)
    (hother : ∀ i, i ≠ dead → w1.st i = w2.st i)
    (htok : ∀ d, (w1.st dead).tokens d = (w2.st dead).tokens d)
    (hty : (w1.st dead).typestate = (w2.st dead).typestate)
    (hmid : (w1.st dead).nextMid = (w2.st dead).nextMid) :
    (∀ i, i ≠ dead → (forgetSender w1 dead).st i = (forgetSender w2 dead).st i) ∧
      (∀ d, ((forgetSender w1 dead).st dead).tokens d = ((forgetSender w2 dead).st dead).tokens d) ∧
      ((forgetSender w1 dead).st dead).typestate = ((forgetSender w2 dead).st dead).typestate ∧
      ((forgetSender w1 dead).st dead).nextMid = ((forgetSender w2 dead).st dead).nextMid := by
  have hfold : ∀ (ids : List InstId) (w1' w2' : World),
      (∀ i, i ≠ dead → w1'.st i = w2'.st i) →
      (∀ d, (w1'.st dead).tokens d = (w2'.st dead).tokens d) →
      (w1'.st dead).typestate = (w2'.st dead).typestate →
      (w1'.st dead).nextMid = (w2'.st dead).nextMid →
      (∀ i, i ≠ dead →
          (ids.foldl (fun w host => forgetHost w dead host) w1').st i =
            (ids.foldl (fun w host => forgetHost w dead host) w2').st i) ∧
        (∀ d, ((ids.foldl (fun w host => forgetHost w dead host) w1').st dead).tokens d =
          ((ids.foldl (fun w host => forgetHost w dead host) w2').st dead).tokens d) ∧
        ((ids.foldl (fun w host => forgetHost w dead host) w1').st dead).typestate =
          ((ids.foldl (fun w host => forgetHost w dead host) w2').st dead).typestate ∧
        ((ids.foldl (fun w host => forgetHost w dead host) w1').st dead).nextMid =
          ((ids.foldl (fun w host => forgetHost w dead host) w2').st dead).nextMid := by
    intro ids
    induction ids with
    | nil =>
      intro w1' w2' hother' htok' hty' hmid'
      exact ⟨hother', htok', hty', hmid'⟩
    | cons host ids ih =>
      intro w1' w2' hother' htok' hty' hmid'
      simp only [List.foldl_cons]
      have hstep := forgetHost_agree w1' w2' dead host hother' htok' hty' hmid'
      exact ih _ _ hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2
  have h := hfold w1.roster w1 w2 hother htok hty hmid
  simpa [forgetSender, hr] using h

theorem strip_stamps (dead : InstId) (a : Actor) : sameStamps (stripSender dead a) a := by
  simp [sameStamps, stripSender]

theorem addTok_stamps (a : Actor) (name : String) (n : Nat) : sameStamps (addTokens a name n) a := by
  simp [sameStamps, addTokens]

theorem forgetHost_stamps (w : World) (dead host i : InstId) :
    sameStamps ((forgetHost w dead host).st i) (w.st i) := by
  unfold forgetHost
  split
  · simp [sameStamps]
  · next hdiff =>
    have hne : host ≠ dead := by simpa [beq_iff_eq] using hdiff
    split
    · simp [sameStamps]
    · by_cases hi : i = dead
      · rw [hi, setActor_self]
        have hclear : ((setActor w host (stripSender dead (w.st host))).st dead) = (w.st dead) := by
          rw [setActor_other _ host dead _ hne.symm]
        simpa [hclear] using addTok_stamps (w.st dead) (tname host) (outboundCount dead (w.st host))
      · by_cases hh : i = host
        · have hne' : i ≠ dead := by simpa [hh] using hne
          rw [setActor_other _ dead i _ hne', hh, setActor_self]
          exact strip_stamps dead (w.st host)
        · rw [setActor_other _ dead i _ hi, setActor_other _ host i _ hh]
          simp [sameStamps]

theorem forget_stamps (w : World) (dead i : InstId) :
    sameStamps ((forgetSender w dead).st i) (w.st i) := by
  unfold forgetSender
  suffices ∀ (ids : List InstId) (w0 : World),
      sameStamps ((ids.foldl (fun w host => forgetHost w dead host) w0).st i) (w0.st i) from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro w0; simp [sameStamps]
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    exact sameStamps_trans (ih (forgetHost w0 dead host)) (forgetHost_stamps w0 dead host i)

/-- Removing the victim after the reclaim agrees whenever the two worlds agreed
on everyone else and on the victim's account. -/
theorem forget_clear_st (w1 w2 : World) (dead : InstId) (hr : w1.roster = w2.roster)
    (hother : ∀ i, i ≠ dead → w1.st i = w2.st i)
    (htok : ∀ d, (w1.st dead).tokens d = (w2.st dead).tokens d)
    (hty : (w1.st dead).typestate = (w2.st dead).typestate)
    (hmid : (w1.st dead).nextMid = (w2.st dead).nextMid)
    (hstamps : sameStamps (w1.st dead) (w2.st dead)) (i : InstId) :
    (setActor (forgetSender w1 dead) dead
        { (forgetSender w1 dead).st dead with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }).st i =
      (setActor (forgetSender w2 dead) dead
        { (forgetSender w2 dead).st dead with
          life := .dead, phase := .idle, box := [], prio := [], parked := [] }).st i := by
  have h := forget_agree w1 w2 dead hr hother htok hty hmid
  by_cases hi : i = dead
  · rw [hi, setActor_self, setActor_self]
    apply actor_fields
    · rfl
    · exact h.2.2.1
    · rfl
    · rfl
    · rfl
    · rfl
    · exact h.2.1
    · exact h.2.2.2
    · let hs := sameStamps_trans (forget_stamps w1 dead dead)
        (sameStamps_trans hstamps (sameStamps_symm (forget_stamps w2 dead dead)))
      exact hs.1
    · let hs := sameStamps_trans (forget_stamps w1 dead dead)
        (sameStamps_trans hstamps (sameStamps_symm (forget_stamps w2 dead dead)))
      exact hs.2.1
    · let hs := sameStamps_trans (forget_stamps w1 dead dead)
        (sameStamps_trans hstamps (sameStamps_symm (forget_stamps w2 dead dead)))
      exact hs.2.2.1
    · let hs := sameStamps_trans (forget_stamps w1 dead dead)
        (sameStamps_trans hstamps (sameStamps_symm (forget_stamps w2 dead dead)))
      exact hs.2.2.2
  · rw [setActor_other _ dead i _ hi, setActor_other _ dead i _ hi]
    exact h.1 i hi

/-- Killing one subtree member preserves outstanding credit. Outbound mail is
credited back before the member is removed, so a sibling's queue may shrink. -/
theorem occ_killOne (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (id : InstId) (hO : OccInv I w) (hS : SemInv I w)
    (hmem : isMember I.desc id sub key = true) (halive : (w.st id).life = .alive) :
    OccInv I (killOne w I.desc id) := by
  have hroster := hO.aliveIn id halive
  let D := I.desc
  let base := readCells D w id
  have hObase := occ_same I w base hO (fun i => readCells_st D w id i) (read_roster D w id).1
    (read_roster D w id).2 fun n => readCells_nextIx D w id n
  have hCbase : ∀ i, contTy (base.st i) := by
    intro i
    exact (contTy_match _ _ (congrArg Actor.phase (readCells_st D w id i))
      (congrArg Actor.typestate (readCells_st D w id i))).mpr (hS.cont i)
  have hmemB : id ∈ base.roster := by simpa [base, (read_roster D w id).1] using hroster
  let wF := failWaiters base id
  have hFail := occ_failFold I base id base.roster hObase hCbase
  have hOF : OccInv I wF := by simpa [wF, failWaiters] using hFail.1
  have hrF : wF.roster = base.roster := by
    simpa [wF, failWaiters] using failWaiters_roster base id base.roster
  have hmemF : id ∈ wF.roster := by simpa [hrF] using hmemB
  let name := tname id
  let ms := (wF.st id).box
  let ps := (wF.st id).parked
  have hparkEq : (wF.st id).parked = (base.st id).parked := by
    simpa [wF, failWaiters] using (failFold_mail base id id base.roster).2.2
  have hmsg : ∀ p ∈ ps, p.sender = p.msg.sender := by
    intro p hp
    exact hObase.parkMsg id p (by simpa [ps, ← hparkEq] using hp)
  have hDb := occ_drain_box I wF id ms hOF hmemF rfl
  have hparkB : ((drainBox wF id name ms).st id).parked = ps := by
    simpa [ps] using drain_park wF id name ms id
  have hmemD : id ∈ (drainBox wF id name ms).roster := by
    simpa [(frame_drain wF id name ms).2.1] using hmemF
  have hDp := occ_drain_park I (drainBox wF id name ms) id ps hDb hmemD hparkB hmsg
  let drained := drainPark (drainBox wF id name ms) id name ps
  have hmemDr : id ∈ drained.roster := by
    simpa [drained, (frame_drainP (drainBox wF id name ms) id name ps).2.1] using hmemD
  have hboxDr : (drained.st id).box = [] := by
    have hkeep := drainP_box (drainBox wF id name ms) id name ps id
    have hclear := drain_box wF id name ms id
    rw [ite_eq_left rfl] at hclear
    simpa [drained] using hkeep.trans hclear
  have hparkDr : (drained.st id).parked = [] := by
    simpa [drained] using drainP_park (drainBox wF id name ms) id name ps id
  let forgotten := forgetSender drained id
  have hOf := occ_forget I drained id hDp hmemDr
  have hkeep := forget_keeps_self drained id
  have hboxFg : (forgotten.st id).box = [] := by simpa [forgotten, hboxDr] using hkeep.1
  have hparkFg : (forgotten.st id).parked = [] := by simpa [forgotten, hparkDr] using hkeep.2
  have hmemFg : id ∈ forgotten.roster := by simpa [forgotten, forget_roster] using hmemDr
  have hquiet : ∀ d, owed forgotten.st d id forgotten.roster = 0 := by
    intro d
    rw [show forgotten.roster = drained.roster from by simp [forgotten, forget_roster]]
    exact owed_slots_zero _ _ _ _ fun i hi => forget_slot_zero drained id d i hi hboxDr hparkDr
  have hbound : ∀ d, owed forgotten.st d id forgotten.roster ≤ budget I.desc (tname id) d := fun d => by
    rw [hquiet d]
    exact Nat.zero_le _
  have hstrip : ∀ host m, m ∈ (forgotten.st host).box → m.sender = id →
      peerKey host = none → peerKey id = none := by
    intro host m hm hs hk
    by_cases hmemH : host ∈ forgotten.roster
    · have hge := owed_ge_here forgotten.st (tname host) id host forgotten.roster hOf.nodup hmemH rfl
      have hone := mem_countFrom id m (forgotten.st host).box hm hs
      have hzero := hquiet (tname host)
      omega
    · have hempty := (hOf.offEmpty host hmemH).1
      rw [hempty] at hm
      cases hm
  have hstripP : ∀ host p, p ∈ (forgotten.st host).parked → p.sender = id →
      peerKey host = none → peerKey id = none := by
    intro host p hp hs hk
    by_cases hmemH : host ∈ forgotten.roster
    · have hge := owed_ge_here forgotten.st (tname host) id host forgotten.roster hOf.nodup hmemH rfl
      have hone := mem_countParked id p (forgotten.st host).parked hp hs
      have hzero := hquiet (tname host)
      omega
    · have hempty := (hOf.offEmpty host hmemH).2
      rw [hempty] at hp
      cases hp
  have hOd := occ_die I forgotten id hOf hmemFg hboxFg hparkFg hbound hstrip hstripP
  let died := setActor forgotten id
    { (forgotten.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  let refunded := refundParked (refundMsgs wF name ms) name ps
  have hrSame : drained.roster = refunded.roster := by
    have hrDr : drained.roster = wF.roster := by
      simp [drained, (frame_drainP (drainBox wF id name ms) id name ps).2.1,
        (frame_drain wF id name ms).2.1]
    have hrRf : refunded.roster = wF.roster := by
      simp [refunded, (frame_refundP (refundMsgs wF name ms) name ps).2.1,
        (frame_refund wF name ms).2.1]
    exact hrDr.trans hrRf.symm
  have hother : ∀ i, i ≠ id → drained.st i = refunded.st i := by
    intro i hi
    simpa [name, ms, ps, drained, refunded] using drain_refund_other wF id i hi
  have hkept := drain_refund_kept wF id
  have hst : ∀ i, (killOne w D id).st i = died.st i := by
    intro i
    have heq := killOne_eq_account w D id
    have hclear := forget_clear_st drained refunded id hrSame hother
      (by simpa [name, ms, ps, drained, refunded] using hkept.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.2.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.2.2) i
    have hkill : (killOne w D id).st i =
        (setActor (forgetSender refunded id) id
          { (forgetSender refunded id).st id with
            life := .dead, phase := .idle, box := [], prio := [], parked := [] }).st i := by
      simpa [D, base, wF, name, ms, ps, refunded] using congrArg (fun z : World => z.st i) heq
    exact hkill.trans hclear.symm
  have hr : (killOne w D id).roster = died.roster := by
    rw [killOne_roster]
    have hdie : died.roster = drained.roster := by simp [died, setActor, forgotten, forget_roster]
    rw [hdie, (frame_drainP (drainBox wF id name ms) id name ps).2.1,
      (frame_drain wF id name ms).2.1, hrF, (read_roster D w id).1]
  have hN : (killOne w D id).N = died.N := by
    rw [killOne_N]
    have hdie : died.N = drained.N := by simp [died, setActor, forgotten, forget_N]
    have hF : wF.N = base.N := by simpa [wF, failWaiters] using failWaiters_N base id base.roster
    rw [hdie, (frame_drainP (drainBox wF id name ms) id name ps).1,
      (frame_drain wF id name ms).1, hF, (read_roster D w id).2]
  have hix : ∀ n, (killOne w D id).nextIx n = died.nextIx n := by
    intro n
    rw [killOne_nextIx]
    have hdie : died.nextIx n = drained.nextIx n := by
      simp [died, setActor, forgotten, forget_nextIx]
    have hF : wF.nextIx n = base.nextIx n :=
      congrFun (by simpa [wF, failWaiters] using failWaiters_nextIx base id base.roster) n
    rw [hdie, congrFun (frame_drainP (drainBox wF id name ms) id name ps).2.2.1 n,
      congrFun (frame_drain wF id name ms).2.2.1 n, hF, readCells_nextIx]
  exact occ_same I died (killOne w D id) hOd hst hr hN hix

theorem occ_killFold (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (ids : List InstId) (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w) :
    OccInv I (ids.foldl (fun w id =>
      if isMember I.desc id sub key && (w.st id).life == .alive then killOne w I.desc id else w) w) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons id ids ih =>
    simp only [List.foldl_cons]
    split
    · next hcond =>
      have hparts := (Bool.and_eq_true _ _).mp hcond
      have halive : (w.st id).life = .alive := by simpa [beq_iff_eq] using hparts.2
      have hInv := killOne_inv I w sub key id hS hM hSlots hparts.1 halive
      have hOcc := occ_killOne I hG w sub key id hO hS hparts.1 halive
      exact ih _ hOcc hInv.1 hInv.2.1 hInv.2.2
    · exact ih _ hO hS hM hSlots

theorem occ_kill (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w) :
    OccInv I (killSubtree w I.desc sub key) := by
  have hFold := occ_killFold I hG w sub key w.roster hO hS hM hSlots
  have hMembers : OccInv I (killMembers w I.desc sub key) := by simpa [killMembers] using hFold
  exact occ_same I (killMembers w I.desc sub key) (killSubtree w I.desc sub key) hMembers
    (fun i => by simp [killSubtree])
    (by simp [killSubtree, killMembers_roster])
    (by simp [killSubtree, killMembers_N])
    (fun n => by simp [killSubtree, killMembers_nextIx])

theorem occ_exec (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (k : Cont) (hO : OccInv I w) (hT : TyOk I.desc w) (hS : SemInv I w) (hM : MailInv w)
    (hSlots : OpenSlots w) (hph : (w.st id).phase = .run k) (hsender : (w.st id).life = .alive)
    (hbulk : bulkScopeOf I.desc (tname id) k.rest = true) :
    OccInv I (execRun I w id (w.st id) k) := by
  have hty : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hS.cont id
  have hmem := hO.aliveIn id hsender
  cases k with
  | mk rest toState replyTo =>
    cases hrest : rest with
    | nil =>
      simp [execRun, hrest] at hph hty ⊢
      apply occ_keep I w id ({ (w.st id) with phase := .idle, typestate := toState }) hO rfl rfl rfl
        (fun _ => rfl) (by simp [hty])
      intro d
      simp [pending, contRest, sendsTo]
    | cons e es =>
      simp [hrest] at hph hty hbulk
      cases e with
      | send dst label hint =>
        have hnot : ¬ loneTerminableName I.desc (tname id) := by
          intro ⟨t, ht, htv, hsub⟩
          have hnb : noBulkSend (.send dst label hint :: es) = true := by
            simpa [bulkScopeOf, ht, htv, hsub] using hbulk
          simp [noBulkSend] at hnb
        simp [execRun]
        cases hr : route w I.desc id dst with
        | none =>
          simp [hr]
          exact occ_note I w id dst (proceed (w.st id) (afterHead ⟨.send dst label hint :: es, toState, replyTo⟩))
            (occ_advance I w id ⟨.send dst label hint :: es, toState, replyTo⟩ hO hty hph)
        | some dstId =>
          simp [hr]
          have hname := route_tname w I.desc id dst dstId hr
          exact occ_enqueue I hL w id dstId { label := label, sender := id, callFrom := none } false
            ⟨.send dst label hint :: es, toState, replyTo⟩ (.send dst label hint) es label hint hO hT
            hph rfl (Or.inl (by simp [hname])) rfl hty hsender hnot (route_agrees w I.desc id dst dstId hr)
            hbulk
      | trySend dst label hint onFull onGone =>
        have hnot : ¬ loneTerminableName I.desc (tname id) := by
          intro ⟨t, ht, htv, hsub⟩
          have hnb : noBulkSend (.trySend dst label hint onFull onGone :: es) = true := by
            simpa [bulkScopeOf, ht, htv, hsub] using hbulk
          simp [noBulkSend] at hnb
        exact occ_try I hL w id ⟨.trySend dst label hint onFull onGone :: es, toState, replyTo⟩
          dst label hint onFull onGone es hO hT
          hph hty hsender hnot hbulk
      | call dst label hint na to =>
        have hnot : ¬ loneTerminableName I.desc (tname id) := by
          intro ⟨t, ht, htv, hsub⟩
          have hnb : noBulkSend (.call dst label hint na to :: es) = true := by
            simpa [bulkScopeOf, ht, htv, hsub] using hbulk
          simp [noBulkSend] at hnb
        simp [execRun]
        cases hr : resolveId I.desc id dst with
        | none =>
          simp [hr]
          exact occ_note I w id dst (proceed (w.st id) (afterHead ⟨.call dst label hint na to :: es, toState, replyTo⟩))
            (occ_advance I w id ⟨.call dst label hint na to :: es, toState, replyTo⟩ hO hty hph)
        | some dstId =>
          simp [hr]
          by_cases hliveD : (w.st dstId).life = .alive
          · have hroute := route_of_resolve w I.desc id dst dstId hr hliveD
            have hname := route_tname w I.desc id dst dstId hroute
            exact occ_enqueue I hL w id dstId { label := label, sender := id, callFrom := some id } true
              ⟨.call dst label hint na to :: es, toState, replyTo⟩ (.call dst label hint na to) es label hint hO hT
              hph rfl (Or.inr ⟨na, to, by simp [hname]⟩) rfl hty hsender hnot
              (route_agrees w I.desc id dst dstId hroute) hbulk
          · exact occ_enqueue I hL w id dstId
              { label := label, sender := id, callFrom := some id } true
              ⟨.call dst label hint na to :: es, toState, replyTo⟩ (.call dst label hint na to) es label hint hO hT
              hph rfl (Or.inr ⟨na, to, by simp [resolve_tname I.desc id dst dstId hr]⟩) rfl hty hsender hnot
              (resolve_agrees I.desc id dst dstId hr) hbulk
      | reply =>
        exact occ_reply I w id ⟨.reply :: es, toState, replyTo⟩ hO hS hph
      | selfSchedule label =>
        exact occ_schedule I w id (w.st id) ⟨.selfSchedule label :: es, toState, replyTo⟩ label hO rfl hph hty
      | cell dst label value =>
        exact occ_cell I w id ⟨.cell dst label value :: es, toState, replyTo⟩ dst label value hO hph hty
      | internal =>
        simp [execRun]
        apply occ_keep I w id ({ (w.st id) with phase := .awaitEffect ⟨es, toState, replyTo⟩ }) hO
          rfl rfl rfl (fun _ => rfl) rfl
        intro d
        simp [pending, contRest, hph, afterHead, sendsTo]
      | peer =>
        simp [execRun]
        apply occ_keep I w id ({ (w.st id) with phase := .awaitPeer ⟨es, toState, replyTo⟩ }) hO
          rfl rfl rfl (fun _ => rfl) rfl
        intro d
        simp [pending, contRest, hph, afterHead, sendsTo]
      | terminate =>
        simp [execRun]
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp [ht]
          exact hO
        | some t =>
          simp only [ht]
          split
          · next hgo =>
            split
            · next hsub =>
              have hparts : t.terminable = true ∧ hasParkedCall (w.st id).parked = false := by
                rcases hgo with ⟨hterm, hor⟩
                exact ⟨hterm, by simpa [hsub.1] using hor⟩
              have hterm : loneTerminableName I.desc (tname id) := ⟨t, ht, hparts.1, hsub.1⟩
              have hmsg : ∀ p ∈ (w.st id).parked, p.sender = p.msg.sender := fun p hp => hO.parkMsg id p hp
              let wR := readCells I.desc w id
              have hOR := occ_same I w wR hO (fun i => readCells_st I.desc w id i)
                (read_roster I.desc w id).1 (read_roster I.desc w id).2 (fun n => read_ix I.desc w id n)
              have hcontR : ∀ i, contTy (wR.st i) := by
                intro i
                have hs := readCells_st I.desc w id i
                exact (contTy_match _ _ (congrArg Actor.phase hs) (congrArg Actor.typestate hs)).mpr (hS.cont i)
              have hmemR : id ∈ wR.roster := by
                have hr := (read_roster I.desc w id).1
                simpa [wR, hr] using hmem
              have hst := readCells_st I.desc w id id
              have hgot := occ_term_kill I wR id hOR hcontR hmemR
                (by simp [terminableB, ht, hparts.1])
                (by intro p hp; exact hmsg p (by simpa [wR, ← hst] using hp))
              rw [← hst]
              simp only [releaseWorld]
              simpa [wR] using hgot.2.1
            · have htermB : terminableB I.desc (tname id) = true := by
                rcases hgo with ⟨hterm, _⟩
                simp [terminableB, ht, hterm]
              simpa [terminateStage] using
                occ_terminate I w id hO hS.cont hmem htermB
          · exact hO

theorem occ_head (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w w' : World) (id : InstId)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hS : SemInv I w) (hM : MailInv w)
    (hSlots : OpenSlots w) (h : execHead I w id = some w')
    (hbulk : ∀ k, (w.st id).phase = .run k → bulkScopeOf I.desc (tname id) k.rest = true) :
    OccInv I w' := by
  by_cases hlive : (w.st id).life = .alive
  · simp [execHead, hlive] at h
    cases hphase : (w.st id).phase with
    | run k =>
      simp [hphase] at h
      cases h
      exact occ_exec I hL hG w id k hO hT hS hM hSlots hphase hlive (hbulk k hphase)
    | idle => simp [hphase] at h
    | parked _ _ _ => simp [hphase] at h
    | awaitReply _ _ => simp [hphase] at h
    | awaitEffect _ => simp [hphase] at h
    | awaitPeer _ => simp [hphase] at h
    | crashed => simp [hphase] at h
  · simp [execHead, hlive] at h

theorem charge_box (a : Actor) (name : String) : (chargeSender a name).box = a.box := by
  simp [chargeSender, bumpToken]

theorem enqueue_box_mem (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (mb : InstId) (m : Msg)
    (hm : m ∈ ((enqueueOrPark w D sender dst msg isCall k).st mb).box) :
    m ∈ (w.st mb).box ∨
      (mb = dst ∧ m = { msg with mid := (w.st dst).nextMid } ∧ (w.st dst).life = .alive) := by
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
            · simp [chargeSender, bumpToken, hsame] at hm
              exact Or.inr ⟨hmb.trans hsame, hm, hlive⟩
          · simp [setActor, hmb] at hm
            exact Or.inl hm
        · rw [← hsame] at hm
          rw [enqueue_room_self_call w D sender msg k hliveS hparkS hcapS] at hm
          by_cases hmb : mb = sender
          · simp [setActor, hmb, charge_box, List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | hm
            · exact Or.inl (by rw [← hmb] at hm; exact hm)
            · simp [chargeSender, bumpToken, hsame] at hm
              exact Or.inr ⟨hmb.trans hsame, hm, hlive⟩
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
  · cases isCall with
    | false =>
      rw [enqueue_dead w D sender dst msg k hlive] at hm
      by_cases hmb : mb = sender
      · simp [setActor, hmb, proceed_box] at hm
        exact Or.inl (by rw [← hmb] at hm; exact hm)
      · simp [setActor, hmb] at hm
        exact Or.inl hm
    | true =>
      rw [enqueue_miss w D sender dst msg k hlive] at hm
      by_cases hmb : mb = sender
      · simp [setActor, hmb, finishCall, proceed_box, issueCall] at hm
        exact Or.inl (by rw [← hmb] at hm; exact hm)
      · simp [setActor, hmb] at hm
        exact Or.inl hm

/-- A fresh enqueue adds at most the parked entry it was given. -/
theorem enqueue_parked_mem (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (mb : InstId) (p : Parked)
    (hp : p ∈ ((enqueueOrPark w D sender dst msg isCall k).st mb).parked) :
    p ∈ (w.st mb).parked ∨
      (mb = dst ∧ p.sender = sender ∧ p.msg = { msg with mid := (w.st dst).nextMid } ∧
        p.isCall = isCall ∧ (w.st dst).life = .alive) := by
  by_cases hlive : (w.st dst).life = .alive
  · by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hparkS : (w.st sender).parked = [] := by rw [hsame]; exact hroom.1
        have hcapS : (w.st sender).box.length < capBulk D w.N sender := by rw [hsame]; exact hroom.2
        cases isCall
        · rw [← hsame] at hp
          rw [enqueue_room_self_send w D sender msg k hliveS hparkS hcapS] at hp
          by_cases hmb : mb = sender
          · simp [setActor, hmb, proceed_parked, charge_parked] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · simp [setActor, hmb] at hp
            exact Or.inl hp
        · rw [← hsame] at hp
          rw [enqueue_room_self_call w D sender msg k hliveS hparkS hcapS] at hp
          by_cases hmb : mb = sender
          · simp [setActor, hmb, charge_parked] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · simp [setActor, hmb] at hp
            exact Or.inl hp
      · have hflip : ¬ dst = sender := fun h => hsame h.symm
        cases isCall
        · rw [enqueue_room_other_send w D sender dst msg k hlive hsame hroom.1 hroom.2] at hp
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp only [setActor] at hp
            rw [if_neg hne] at hp
            rw [if_pos hmb] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, proceed_parked, charge_parked] at hp
              exact Or.inl (by rw [← hsender] at hp; exact hp)
            · simp [setActor, hmb, hsender, hflip] at hp
              exact Or.inl hp
        · rw [enqueue_room_other_call w D sender dst msg k hlive hsame hroom.1 hroom.2] at hp
          by_cases hmb : mb = dst
          · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
            simp only [setActor] at hp
            rw [if_neg hne] at hp
            rw [if_pos hmb] at hp
            exact Or.inl (by rw [← hmb] at hp; exact hp)
          · by_cases hsender : mb = sender
            · simp [setActor, hmb, hsender, hflip, charge_parked] at hp
              exact Or.inl (by rw [← hsender] at hp; exact hp)
            · simp [setActor, hmb, hsender, hflip] at hp
              exact Or.inl hp
    · by_cases hsame : sender = dst
      · have hliveS : (w.st sender).life = .alive := by rw [hsame]; exact hlive
        have hroomS : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender) := by
          rw [hsame]; exact hroom
        rw [← hsame] at hp
        rw [enqueue_park_self w D sender msg isCall k hliveS hroomS] at hp
        by_cases hmb : mb = sender
        · simp [setActor, hmb, charge_parked] at hp
          cases hp with
          | inl h => exact Or.inl (by rw [← hmb] at h; exact h)
          | inr h =>
            cases h
            refine Or.inr ⟨hmb.trans hsame, rfl, ?_, rfl, hlive⟩
            simp [chargeSender, bumpToken, hsame]
        · simp [setActor, hmb] at hp
          exact Or.inl hp
      · have hflip : ¬ dst = sender := fun h => hsame h.symm
        rw [enqueue_park_other w D sender dst msg isCall k hlive hsame hroom] at hp
        by_cases hmb : mb = dst
        · have hne : ¬ mb = sender := fun h => hsame (h.symm.trans hmb)
          simp [setActor, hmb, hne, hflip] at hp
          cases hp with
          | inl h => exact Or.inl (by rw [← hmb] at h; exact h)
          | inr h =>
            cases h
            exact Or.inr ⟨hmb, rfl, rfl, rfl, hlive⟩
        · by_cases hsender : mb = sender
          · simp [setActor, hmb, hsender, hflip, charge_parked] at hp
            exact Or.inl (by rw [← hsender] at hp; exact hp)
          · simp [setActor, hmb, hsender, hflip] at hp
            exact Or.inl hp
  · cases isCall with
    | false =>
      rw [enqueue_dead w D sender dst msg k hlive] at hp
      by_cases hmb : mb = sender
      · simp [setActor, hmb, proceed_parked] at hp
        exact Or.inl (by rw [← hmb] at hp; exact hp)
      · simp [setActor, hmb] at hp
        exact Or.inl hp
    | true =>
      rw [enqueue_miss w D sender dst msg k hlive] at hp
      by_cases hmb : mb = sender
      · simp [setActor, hmb, finishCall, proceed_parked, issueCall] at hp
        exact Or.inl (by rw [← hmb] at hp; exact hp)
      · simp [setActor, hmb] at hp
        exact Or.inl hp

/-- A phase change that keeps both mail lists does not move a member's message. -/
theorem here_set (D : Description) (w : World) (id : InstId) (a : Actor) (hH : MailHere D w)
    (hb : ∀ m ∈ a.box, m ∈ (w.st id).box) (hp : ∀ p ∈ a.parked, p ∈ (w.st id).parked) :
    MailHere D (setActor w id a) := by
  intro host
  by_cases hh : host = id
  · subst hh
    refine ⟨fun m hm => (hH host).1 m (hb m (by simpa [setActor] using hm)),
      fun p hp' => (hH host).2 p (hp p (by simpa [setActor] using hp'))⟩
  · simp [setActor, hh]
    exact hH host

/-- The same, when every actor's lists are exactly the old ones. -/
theorem here_eq (D : Description) (w w' : World) (hH : MailHere D w)
    (h : ∀ i, (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked) :
    MailHere D w' := by
  intro host
  have hi := h host
  simp [hi.1, hi.2]
  exact hH host

/-- A parked entry records the actor that sent it. -/
def ParkAlign (w : World) : Prop :=
  ∀ host p, p ∈ (w.st host).parked → p.sender = p.msg.sender

theorem align_set (w : World) (id : InstId) (a : Actor) (hP : ParkAlign w)
    (hp : ∀ p ∈ a.parked, p ∈ (w.st id).parked) : ParkAlign (setActor w id a) := by
  intro host p hp'
  by_cases hh : host = id
  · subst hh
    exact hP host p (hp p (by simpa [setActor] using hp'))
  · exact hP host p (by simpa [setActor, hh] using hp')

theorem align_eq (w w' : World) (hP : ParkAlign w)
    (h : ∀ i, (w'.st i).parked = (w.st i).parked) : ParkAlign w' := by
  intro host p hp
  exact hP host p (by simpa [h host] using hp)

theorem resume_mail (a : Actor) (b : Bool) (dst : InstId) :
    (resumeSender a b dst).box = a.box ∧ (resumeSender a b dst).parked = a.parked := by
  unfold resumeSender
  split
  · next _ =>
    split
    · simp
    · exact ⟨proceed_box _ _, proceed_parked _ _⟩
  · exact ⟨rfl, rfl⟩

theorem release_lists (w : World) (id : InstId) (ps : List Parked) (i : InstId) :
    ((releaseParked w id ps).st i).box = (w.st i).box ∧
      ((releaseParked w id ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [releaseParked]
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split
    · exact ih _
    · have hm := resume_mail (w.st p.sender) false id
      let w' := setActor w p.sender (resumeSender (w.st p.sender) false id)
      have ih' := ih w'
      have hbox : (w'.st i).box = (w.st i).box := by
        by_cases hi : i = p.sender
        · simp [w', setActor, hi, hm.1]
        · simp [w', setActor, hi]
      have hpark : (w'.st i).parked = (w.st i).parked := by
        by_cases hi : i = p.sender
        · simp [w', setActor, hi, hm.2]
        · simp [w', setActor, hi]
      rw [← hbox, ← hpark]
      simpa [releaseParked, w'] using ih'

/-- A message a member addresses to itself still sits in that member's subtree. -/
theorem self_member_here (D : Description) (id : InstId) : memberHere D id id none := by
  intro hname
  obtain ⟨t, ht, _, hsub⟩ := hname
  have htree : templateSubtree D (tname id) = t.subtree := by simp [templateSubtree, ht]
  refine ⟨?_, rfl⟩
  simp [sameSubtree, htree, bne, beq_iff_eq, hsub]

theorem member_effect_of_scope (D : Description) (name : String) (e : Eff) (es : List Eff)
    (hmem : subtreeMemberName D name) (h : bulkScopeOf D name (e :: es) = true) :
    memberEffectOk D name e = true := by
  obtain ⟨t, ht, hterm, hsub⟩ := hmem
  have hsubB : (t.subtree == "") = false := by simpa [beq_iff_eq] using hsub
  simp [bulkScopeOf, ht, hterm, hsubB, memberProgramOk, Bool.and_eq_true] at h
  exact h.1

/-- A per-peer route uses the sender's own key. -/
theorem route_per_peer (w : World) (D : Description) (sender : InstId) (dst : String)
    (host : InstId) (k : Nat) (hper : perPeerB D dst = true) (hk : memberKey sender = some k)
    (hr : route w D sender dst = some host) : host = InstId.peer dst k := by
  unfold perPeerB at hper
  cases htmpl : templateOf D dst with
  | none => simp [htmpl] at hper
  | some t =>
    simp [htmpl] at hper
    cases hmul : t.multiplicity with
    | one =>
      have hbad : (Multiplicity.one == Multiplicity.perPeer) = false := rfl
      rw [hmul] at hper
      simp [hbad] at hper
    | perPeer =>
      simp [route, htmpl, hmul, hk] at hr
      exact hr.2.symm

theorem resolve_per_peer (D : Description) (sender : InstId) (dst : String) (host : InstId) (k : Nat)
    (hper : perPeerB D dst = true) (hk : memberKey sender = some k)
    (hr : resolveId D sender dst = some host) : host = InstId.peer dst k := by
  unfold perPeerB at hper
  cases htmpl : templateOf D dst with
  | none => simp [htmpl] at hper
  | some t =>
    simp [htmpl] at hper
    cases hmul : t.multiplicity with
    | one =>
      have hbad : (Multiplicity.one == Multiplicity.perPeer) = false := rfl
      rw [hmul] at hper
      simp [hbad] at hper
    | perPeer =>
      simp [resolveId, htmpl, hmul, hk] at hr
      exact hr.symm

/-- A checked send, try-send, or call from a subtree member lands on its subtree. -/
theorem scoped_lands (w : World) (D : Description) (sender host : InstId) (dst label : String)
    (hint : Nat) (e : Eff) (hname : subtreeMemberName D (tname sender))
    (hok : memberEffectOk D (tname sender) e = true)
    (he : e = .send dst label hint ∨ (∃ full gone, e = .trySend dst label hint full gone) ∨ (∃ na to, e = .call dst label hint na to))
    (hr : route w D sender dst = some host) : memberHere D sender host none := by
  have hscope : (sameSubtree D (tname sender) dst && perPeerB D dst) = true := by
    rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simpa [memberEffectOk] using hok
  simp [Bool.and_eq_true] at hscope
  cases hkey : memberKey sender with
  | none =>
    have hper := hscope.2
    unfold perPeerB at hper
    cases htmpl : templateOf D dst with
    | none => simp [htmpl] at hper
    | some t =>
      simp [htmpl] at hper
      cases hmul : t.multiplicity with
      | one =>
        have hbad : (Multiplicity.one == Multiplicity.perPeer) = false := rfl
        rw [hmul] at hper
        simp [hbad] at hper
      | perPeer => simp [route, htmpl, hmul, hkey] at hr
  | some k =>
    have hhost := route_per_peer w D sender dst host k hscope.2 hkey hr
    intro _
    refine ⟨?_, ?_⟩
    · simpa [hhost, tname] using hscope.1
    · simpa [hhost, memberKey] using hkey

theorem scoped_resolve (D : Description) (sender host : InstId) (dst label : String) (hint : Nat)
    (e : Eff) (hname : subtreeMemberName D (tname sender))
    (hok : memberEffectOk D (tname sender) e = true)
    (he : e = .send dst label hint ∨ (∃ full gone, e = .trySend dst label hint full gone) ∨ (∃ na to, e = .call dst label hint na to))
    (hr : resolveId D sender dst = some host) : memberHere D sender host none := by
  have hscope : (sameSubtree D (tname sender) dst && perPeerB D dst) = true := by
    rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simpa [memberEffectOk] using hok
  simp [Bool.and_eq_true] at hscope
  cases hkey : memberKey sender with
  | none =>
    have hper := hscope.2
    unfold perPeerB at hper
    cases htmpl : templateOf D dst with
    | none => simp [htmpl] at hper
    | some t =>
      simp [htmpl] at hper
      cases hmul : t.multiplicity with
      | one =>
        have hbad : (Multiplicity.one == Multiplicity.perPeer) = false := rfl
        rw [hmul] at hper
        simp [hbad] at hper
      | perPeer => simp [resolveId, htmpl, hmul, hkey] at hr
  | some k =>
    have hhost := resolve_per_peer D sender dst host k hscope.2 hkey hr
    intro _
    refine ⟨?_, ?_⟩
    · simpa [hhost, tname] using hscope.1
    · simpa [hhost, memberKey] using hkey

theorem enqueue_keeps_here (D : Description) (w : World) (hH : MailHere D w) (sender dst : InstId)
    (msg : Msg) (isCall : Bool) (k : Cont) (hfrom : msg.sender = sender)
    (hfresh : subtreeMemberName D (tname sender) → memberHere D sender dst msg.callFrom) :
    MailHere D (enqueueOrPark w D sender dst msg isCall k) := by
  intro host
  refine ⟨?_, ?_⟩
  · intro m hm
    rcases enqueue_box_mem w D sender dst msg isCall k host m hm with hold | ⟨hid, heq, _⟩
    · exact (hH host).1 m hold
    · rw [hid]
      have hwho : m.sender = sender := by simp [heq, hfrom]
      simpa [memberHere, hwho] using hfresh
  · intro p hp
    rcases enqueue_parked_mem w D sender dst msg isCall k host p hp with
      hold | ⟨hid, hs, heq, _, _⟩
    · exact (hH host).2 p hold
    · rw [hid, hs]
      have hwho : p.msg.sender = sender := by simp [heq, hfrom]
      simpa [memberHere, hwho] using hfresh

theorem enqueue_align (D : Description) (w : World) (hP : ParkAlign w) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hfrom : msg.sender = sender) :
    ParkAlign (enqueueOrPark w D sender dst msg isCall k) := by
  intro host p hp
  rcases enqueue_parked_mem w D sender dst msg isCall k host p hp with hold | ⟨_, hs, heq, _, _⟩
  · exact hP host p hold
  · simp [hs, heq, hfrom]

theorem kill_keeps_here (D : Description) (w : World) (hH : MailHere D w) (sub : String) (key : Nat) :
    MailHere D (killSubtree w D sub key) := by
  intro host
  refine ⟨?_, ?_⟩
  · intro m hm
    by_cases hlive : ((killSubtree w D sub key).st host).life = .alive
    · exact (hH host).1 m (List.Sublist.mem hm (killSubtree_if_alive w D sub key host hlive).2.1)
    · by_cases hwas : (w.st host).life = .alive
      · simp [(killSubtree_died w D sub key host hwas hlive).2.2.2.1] at hm
      · exact (hH host).1 m (List.Sublist.mem hm (killSubtree_if_dead w D sub key host hwas).2.1)
  · intro p hp
    by_cases hlive : ((killSubtree w D sub key).st host).life = .alive
    · exact (hH host).2 p
        (List.Sublist.mem hp (killSubtree_if_alive w D sub key host hlive).2.2.2.1)
    · by_cases hwas : (w.st host).life = .alive
      · simp [(killSubtree_died w D sub key host hwas hlive).2.2.2.2.2] at hp
      · exact (hH host).2 p
          (List.Sublist.mem hp (killSubtree_if_dead w D sub key host hwas).2.2.2.1)

theorem kill_align (w : World) (hP : ParkAlign w) (D : Description) (sub : String) (key : Nat) :
    ParkAlign (killSubtree w D sub key) := by
  intro host p hp
  by_cases hlive : ((killSubtree w D sub key).st host).life = .alive
  · exact hP host p (List.Sublist.mem hp (killSubtree_if_alive w D sub key host hlive).2.2.2.1)
  · by_cases hwas : (w.st host).life = .alive
    · simp [(killSubtree_died w D sub key host hwas hlive).2.2.2.2.2] at hp
    · exact hP host p (List.Sublist.mem hp (killSubtree_if_dead w D sub key host hwas).2.2.2.1)

theorem mail_here_init (I : Impl) (N : Nat) : MailHere I.desc (initWorld I N) := by
  intro host
  have hst : ((initWorld I N).st host) =
      if (coreRoster I.desc).contains host then initActor I.desc host else absentActor := by
    simp only [initWorld]
    simpa using reads_keep_st I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } host
  refine ⟨?_, ?_⟩
  · intro m hm
    rw [hst] at hm
    split at hm
    · simp [initActor] at hm
      split at hm <;> simp [withTokens, absentActor] at hm
    · simp [absentActor] at hm
  · intro p hp
    rw [hst] at hp
    split at hp
    · simp [initActor] at hp
      split at hp <;> simp [withTokens, absentActor] at hp
    · simp [absentActor] at hp

theorem align_init (I : Impl) (N : Nat) : ParkAlign (initWorld I N) := by
  intro host p hp
  have hst : ((initWorld I N).st host) =
      if (coreRoster I.desc).contains host then initActor I.desc host else absentActor := by
    simp only [initWorld]
    simpa using reads_keep_st I.desc (coreRoster I.desc)
      { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
        st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
        cell := fun _ _ => cleanCell, observed := fun _ _ => 0 } host
  rw [hst] at hp
  split at hp
  · simp [initActor] at hp
    split at hp <;> simp [withTokens, absentActor] at hp
  · simp [absentActor] at hp

theorem phase_pack (D : Description) (w : World) (id : InstId) (a : Actor) (hH : MailHere D w)
    (hP : ParkAlign w) (hb : a.box = (w.st id).box) (hp : a.parked = (w.st id).parked) :
    MailHere D (setActor w id a) ∧ ParkAlign (setActor w id a) :=
  ⟨here_set D w id a hH (fun m hm => by simpa [hb] using hm) (fun p hp' => by simpa [hp] using hp'),
    align_set w id a hP (fun p hp' => by simpa [hp] using hp')⟩

theorem credit_lists (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).box = (w.st i).box ∧
      ((creditSender w name sender).st i).parked = (w.st i).parked := by
  have h := credit_rest w name sender i
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

theorem refund_lists (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).box = (w.st i).box ∧
      ((refundMsgs w dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    rw [refundMsgs, List.foldl_cons]
    have h := ih (creditSender w dst m.sender)
    have c := credit_lists w dst m.sender i
    exact ⟨h.1.trans c.1, h.2.trans c.2⟩

theorem refundP_lists (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).box = (w.st i).box ∧
      ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    rw [refundParked, List.foldl_cons]
    have h := ih (creditSender w dst p.msg.sender)
    have c := credit_lists w dst p.msg.sender i
    exact ⟨h.1.trans c.1, h.2.trans c.2⟩

/-- A lone release only deletes the victim's mailbox. -/
theorem releaseWorld_sub (D : Description) (w : World) (id : InstId) (a : Actor) (i : InstId) :
    ((releaseWorld D w id a).st i).box.Sublist (w.st i).box ∧
      ((releaseWorld D w id a).st i).parked.Sublist (w.st i).parked := by
  let w1 := readCells D w id
  have h1b : (w1.st i).box = (w.st i).box := congrArg (·.box) (cellsSt D w id i)
  have h1p : (w1.st i).parked = (w.st i).parked := congrArg (·.parked) (cellsSt D w id i)
  let w2 := refundMsgs w1 (tname id) a.box
  have h2 := refund_lists w1 (tname id) a.box i
  let w3 := refundParked w2 (tname id) a.parked
  have h3 := refundP_lists w2 (tname id) a.parked i
  let dead : Actor := { w3.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have hbody : releaseWorld D w id a = releaseParked (setActor w3 id dead) id a.parked := by
    simp [releaseWorld, w1, w2, w3, dead]
  have hrel := release_lists (setActor w3 id dead) id a.parked i
  rw [hbody, hrel.1, hrel.2]
  by_cases hi : i = id
  · subst hi
    simp [setActor]
    exact ⟨List.nil_sublist _, List.nil_sublist _⟩
  · have hbox : (w3.st i).box = (w.st i).box := h3.1.trans (h2.1.trans h1b)
    have hpark : (w3.st i).parked = (w.st i).parked := h3.2.trans (h2.2.trans h1p)
    simp [setActor, hi, hbox, hpark]

theorem release_pack (D : Description) (w : World) (id : InstId) (a : Actor) (hH : MailHere D w)
    (hP : ParkAlign w) : MailHere D (releaseWorld D w id a) ∧ ParkAlign (releaseWorld D w id a) := by
  refine ⟨?_, ?_⟩
  · intro host
    have hsub := releaseWorld_sub D w id a host
    refine ⟨fun m hm => (hH host).1 m (List.Sublist.mem hm hsub.1),
      fun p hp => (hH host).2 p (List.Sublist.mem hp hsub.2)⟩
  · intro host p hp
    exact hP host p (List.Sublist.mem hp (releaseWorld_sub D w id a host).2)

/-- Box and parked lists determine both subtree placement and parked-sender alignment. -/
theorem lists_pack (D : Description) (w w' : World) (hH : MailHere D w) (hP : ParkAlign w)
    (h : ∀ i, (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked) :
    MailHere D w' ∧ ParkAlign w' := by
  refine ⟨?_, ?_⟩
  · intro host
    exact ⟨fun m hm => (hH host).1 m (by simpa [(h host).1] using hm),
      fun p hp => (hH host).2 p (by simpa [(h host).2] using hp)⟩
  · intro host p hp
    exact hP host p (by simpa [(h host).2] using hp)

theorem failWaiter_lists (w : World) (dead i j : InstId) :
    ((failWaiter w dead i).st j).box = (w.st j).box ∧
      ((failWaiter w dead i).st j).parked = (w.st j).parked := by
  unfold failWaiter
  split
  · exact ⟨rfl, rfl⟩
  · cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hph, hd]
          by_cases hj : j = i
          · simp [setActor, hj, proceed_box, proceed_parked]
          · simp [setActor, hj]
        · simp [hph, hd]
      | true => simp [hph]
    | awaitReply _ _ => simp [hph]
    | idle => simp [hph]
    | run _ => simp [hph]
    | awaitEffect _ => simp [hph]
    | awaitPeer _ => simp [hph]
    | crashed => simp [hph]

theorem failWaiters_lists (w : World) (dead j : InstId) :
    ((failWaiters w dead).st j).box = (w.st j).box ∧
      ((failWaiters w dead).st j).parked = (w.st j).parked := by
  unfold failWaiters
  induction w.roster generalizing w with
  | nil => simp
  | cons i ids ih =>
    simp only [List.foldl_cons]
    have h1 := failWaiter_lists w dead i j
    have h2 := ih (failWaiter w dead i)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem failWaiters_pack (D : Description) (w : World) (dead : InstId) (hH : MailHere D w)
    (hP : ParkAlign w) : MailHere D (failWaiters w dead) ∧ ParkAlign (failWaiters w dead) :=
  lists_pack D w (failWaiters w dead) hH hP fun j => failWaiters_lists w dead j

/-- A dead sender's blocked delivery moves into the same host's box. -/
theorem admitHost_pack (D : Description) (w : World) (dead host : InstId) (hH : MailHere D w)
    (hP : ParkAlign w) : MailHere D (admitHost w dead host) ∧ ParkAlign (admitHost w dead host) := by
  unfold admitHost
  split
  · exact ⟨hH, hP⟩
  · split
    · exact ⟨hH, hP⟩
    · refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i = host
        · rw [hi]
          refine ⟨?_, ?_⟩
          · intro m hm
            simp [setActor] at hm
            rcases hm with hm | ⟨p, ⟨hpin, hsend⟩, rfl⟩
            · exact (hH host).1 m hm
            · exact (by simpa [hP host p hpin, hsend] using (hH host).2 p hpin)
          · intro p hp
            simp [setActor] at hp
            exact (hH host).2 p hp.1
        · simp [setActor, hi]
          exact hH i
      · intro i p hp
        by_cases hi : i = host
        · rw [hi] at hp
          simp [setActor] at hp
          exact hP host p hp.1
        · exact hP i p (by simpa [setActor, hi] using hp)

theorem admitDead_pack (D : Description) (w : World) (dead : InstId) (hH : MailHere D w)
    (hP : ParkAlign w) : MailHere D (admitDead w dead) ∧ ParkAlign (admitDead w dead) := by
  unfold admitDead
  induction w.roster generalizing w with
  | nil => simpa using ⟨hH, hP⟩
  | cons host ids ih =>
    simp only [List.foldl_cons]
    exact ih (admitHost w dead host) (admitHost_pack D w dead host hH hP).1
      (admitHost_pack D w dead host hH hP).2

theorem abortActor_pack (D : Description) (w : World) (id : InstId) (a : Actor) (hH : MailHere D w)
    (hP : ParkAlign w) : MailHere D (abortActor D w id a) ∧ ParkAlign (abortActor D w id a) := by
  obtain ⟨hH1, hP1⟩ := release_pack D w id a hH hP
  obtain ⟨hH2, hP2⟩ := failWaiters_pack D (releaseWorld D w id a) id hH1 hP1
  simpa [abortActor] using admitDead_pack D (failWaiters (releaseWorld D w id a) id) id hH2 hP2

theorem enqueueTombstone_lists (D : Description) (w : World) (child i : InstId) :
    ((enqueueTombstone D w child).st i).box = (w.st i).box ∧
      ((enqueueTombstone D w child).st i).parked = (w.st i).parked := by
  cases hsup : supervisorOf D child with
  | none => simp [enqueueTombstone, hsup]
  | some parent =>
    simp only [enqueueTombstone, hsup]
    split <;> by_cases hi : i = parent <;> simp [setActor, hi]

theorem abortDesc_pack (fuel : Nat) (D : Description) (w : World) (parent : InstId)
    (hH : MailHere D w) (hP : ParkAlign w) :
    MailHere D (abortDesc fuel D w parent) ∧ ParkAlign (abortDesc fuel D w parent) := by
  induction fuel generalizing w parent with
  | zero => exact ⟨hH, hP⟩
  | succ fuel ihF =>
    simp only [abortDesc]
    let step (w : World) (child : InstId) : World :=
      if isChild D parent child && (w.st child).life == .alive && childTerminable D child then
        let w := abortDesc fuel D w child
        abortActor D w child (w.st child)
      else w
    have hfold : ∀ (ids : List InstId) (w0 : World),
        MailHere D w0 → ParkAlign w0 →
        MailHere D (ids.foldl step w0) ∧ ParkAlign (ids.foldl step w0) := by
      intro ids
      induction ids with
      | nil =>
        intro w0 hH0 hP0
        exact ⟨hH0, hP0⟩
      | cons child ids ihL =>
        intro w0 hH0 hP0
        simp only [List.foldl_cons, step]
        by_cases hcond : (isChild D parent child && (w0.st child).life == .alive &&
            childTerminable D child) = true
        · simp only [hcond, ite_true]
          obtain ⟨hH1, hP1⟩ := ihF w0 child hH0 hP0
          obtain ⟨hH2, hP2⟩ := abortActor_pack D (abortDesc fuel D w0 child) child
            ((abortDesc fuel D w0 child).st child) hH1 hP1
          exact ihL _ hH2 hP2
        · have hf : (isChild D parent child && (w0.st child).life == .alive &&
              childTerminable D child) = false := by
            cases hb : isChild D parent child && (w0.st child).life == .alive &&
                childTerminable D child with
            | false => rfl
            | true => exact absurd hb hcond
          simp only [hf]
          exact ihL w0 hH0 hP0
    exact hfold w.roster w hH hP

theorem terminateStage_pack (D : Description) (w : World) (id : InstId) (a : Actor)
    (hH : MailHere D w) (hP : ParkAlign w) :
    MailHere D (terminateStage D w id a) ∧ ParkAlign (terminateStage D w id a) := by
  obtain ⟨hH1, hP1⟩ := abortDesc_pack w.roster.length D w id hH hP
  obtain ⟨hH2, hP2⟩ := abortActor_pack D (abortDesc w.roster.length D w id) id
    ((abortDesc w.roster.length D w id).st id) hH1 hP1
  simpa [terminateStage] using lists_pack D
    (abortActor D (abortDesc w.roster.length D w id) id ((abortDesc w.roster.length D w id).st id))
    (enqueueTombstone D
      (abortActor D (abortDesc w.roster.length D w id) id ((abortDesc w.roster.length D w id).st id)) id)
    hH2 hP2 fun i => enqueueTombstone_lists D _ id i

theorem deliver_keeps_mail (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    a1.box = a.box ∧ a1.parked = a.parked ∧ ∀ i, w1.st i = w.st i := by
  unfold deliver at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl, fun i => cellsSt I.desc w id i⟩
    · next _ =>
      split at h
      · cases h
      · cases h
        split
        · exact ⟨rfl, rfl, fun i => cellsSt I.desc w id i⟩
        · exact ⟨rfl, rfl, fun i => cellsSt I.desc w id i⟩

theorem prio_pack (I : Impl) (w w' : World) (id : InstId) (hH : MailHere I.desc w)
    (hP : ParkAlign w) (h : receivePrio I w id = some w') :
    MailHere I.desc w' ∧ ParkAlign w' := by
  simp only [receivePrio] at h
  split at h
  · cases h
  · next m ms =>
    split at h
    · cases h
    · split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        obtain ⟨hb, hpk, hst⟩ := deliver_keeps_mail I w id _ _ w1 a1 hdel
        have hfun : w1.st = w.st := funext hst
        exact phase_pack I.desc w1 id a1
          (here_eq I.desc w w1 hH (fun i => by simp [congrFun hfun i]))
          (align_eq w w1 hP (fun i => by simp [congrFun hfun i]))
          (by simpa [congrFun hfun id] using hb) (by simpa [congrFun hfun id] using hpk)

theorem finish_pack (I : Impl) (w w' : World) (id : InstId) (hH : MailHere I.desc w)
    (hP : ParkAlign w) (h : finishWait I w id = some w') :
    MailHere I.desc w' ∧ ParkAlign w' := by
  obtain ⟨k, _, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  exact phase_pack I.desc w id (proceed (w.st id) k) hH hP (proceed_box _ _) (proceed_parked _ _)

theorem ingress_pack (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (hH : MailHere I.desc w) (hP : ParkAlign w) (h : receiveIngress I w dst label = some w') :
    MailHere I.desc w' ∧ ParkAlign w' := by
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
            refine ⟨?_, ?_⟩
            · intro host
              by_cases hh : host = dst
              · subst hh
                refine ⟨?_, ?_⟩
                · intro m hm
                  simp [setActor, chargeSender, bumpToken, List.mem_append, List.mem_singleton] at hm
                  rcases hm with hm | hm
                  · exact (hH host).1 m hm
                  · simpa [hm] using self_member_here I.desc host
                · intro p hp
                  simp [setActor, chargeSender, bumpToken] at hp
                  exact (hH host).2 p hp
              · simp [setActor, hh]
                exact hH host
            · intro host p hp
              by_cases hh : host = dst
              · subst hh
                simp [setActor, chargeSender, bumpToken] at hp
                exact hP host p hp
              · exact hP host p (by simpa [setActor, hh] using hp)

/-- The roster a successful spawn extends, before the new actor and its cells. -/
def admitPeer (w : World) (template : String) : World :=
  let nid := InstId.peer template (w.nextIx template)
  { w with
    roster := w.roster ++ [nid]
    nextIx := fun n => if n = template then w.nextIx n + 1 else w.nextIx n }

/-- An actor born idle, before its initial tokens. -/
def idleBorn (t : Template) : Actor :=
  { life := .alive
    typestate := t.initial
    phase := .idle
    box := []
    prio := []
    parked := []
    tokens := fun _ => 0 }

theorem spawn_pack (I : Impl) (w w' : World) (template : String) (hH : MailHere I.desc w)
    (hP : ParkAlign w) (h : spawn I w template = some w') :
    MailHere I.desc w' ∧ ParkAlign w' := by
  unfold spawn at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · cases h
      let nid := InstId.peer template (w.nextIx template)
      let wR := admitPeer w template
      let born := withTokens I.desc template (idleBorn t)
      refine ⟨?_, ?_⟩
      · apply here_eq I.desc (setActor wR nid born) _
          (here_set I.desc w nid born hH
            (fun m hm => by simp [born, withTokens, idleBorn] at hm)
            (fun p hp => by simp [born, withTokens, idleBorn] at hp))
        intro i
        have hi := cellsSt I.desc (setActor wR nid born) nid i
        simp [nid, wR, admitPeer, born, idleBorn, spawn] at hi
        simp [hi, nid, wR, admitPeer, born, idleBorn]
      · apply align_eq (setActor wR nid born) _
          (align_set w nid born hP (fun p hp => by simp [born, withTokens, idleBorn] at hp))
        intro i
        have hi := cellsSt I.desc (setActor wR nid born) nid i
        simp [nid, wR, admitPeer, born, idleBorn, spawn] at hi
        simp [hi, nid, wR, admitPeer, born, idleBorn]
    · cases h

theorem try_wake_pack (D : Description) (w : World) (hH : MailHere D w) (hP : ParkAlign w)
    (dstId : InstId) (label : String) (writer : InstId) :
    MailHere D (tryWake D w dstId label writer) ∧ ParkAlign (tryWake D w dstId label writer) := by
  unfold tryWake
  extract_lets
  split
  · exact phase_pack D w dstId
      { (w.st dstId) with
        prio := upsertPrio (w.st dstId).prio
          { label := label, sender := writer, callFrom := none, reliable := false,
            mid := (w.st dstId).nextMid },
        nextMid := (w.st dstId).nextMid + 1 } hH hP rfl rfl
  · exact ⟨hH, hP⟩

theorem wakes_pack (D : Description) (ids : List InstId) (w : World) (hH : MailHere D w)
    (hP : ParkAlign w) (dst label : String) (writer : InstId) :
    MailHere D (ids.foldl (fun w id => tryWake D w id label writer) w) ∧
      ParkAlign (ids.foldl (fun w id => tryWake D w id label writer) w) := by
  induction ids generalizing w with
  | nil => exact ⟨hH, hP⟩
  | cons j js ih =>
    simp only [List.foldl_cons]
    exact ih _ (try_wake_pack D w hH hP j label writer).1 (try_wake_pack D w hH hP j label writer).2

theorem mail_subset (D : Description) (w w' : World) (hH : MailHere D w) (hP : ParkAlign w)
    (hb : ∀ host m, m ∈ (w'.st host).box →
      m ∈ (w.st host).box ∨ ∃ p, p ∈ (w.st host).parked ∧ m = p.msg)
    (hp : ∀ host q, q ∈ (w'.st host).parked → q ∈ (w.st host).parked) :
    MailHere D w' ∧ ParkAlign w' := by
  refine ⟨?_, ?_⟩
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases hb host m hm with hm | ⟨p, hmem, heq⟩
      · exact (hH host).1 m hm
      · have hwho := hP host p hmem
        simpa [memberHere, heq, hwho] using (hH host).2 p hmem
    · intro q hq
      exact (hH host).2 q (hp host q hq)
  · intro host q hq
    exact hP host q (hp host q hq)

theorem bulk_pack (I : Impl) (w w' : World) (id : InstId) (hH : MailHere I.desc w)
    (hP : ParkAlign w) (h : receiveBulk I w id = some w') :
    MailHere I.desc w' ∧ ParkAlign w' := by
  dsimp [receiveBulk] at h
  split at h
  · cases h
  · split at h
    · expose_names
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        obtain ⟨abox, apark, hst⟩ := deliver_keeps_mail I w id _ _ w1 a1 hdel
        refine mail_subset I.desc w _ hH hP ?_ ?_
        · intro host msg hmem
          have hc := (credit_lists (setActor w1 id a1) (tname id) m.sender host).1
          rw [hc] at hmem
          by_cases hh : host = id
          · rw [hh] at hmem ⊢
            rw [setActor_self] at hmem
            rw [abox] at hmem
            have hbox : (w.st id).box = m :: ms := by assumption
            rw [hbox]
            exact Or.inl (List.mem_cons_of_mem m (by simpa using hmem))
          · rw [setActor_other w1 id host a1 hh] at hmem
            rw [show (w1.st host).box = (w.st host).box from congrArg Actor.box (hst host)] at hmem
            exact Or.inl hmem
        · intro host q hq
          have hc := (credit_lists (setActor w1 id a1) (tname id) m.sender host).2
          rw [hc] at hq
          by_cases hh : host = id
          · rw [hh] at hq
            rw [setActor_self] at hq
            rw [apark] at hq
            have hpark : (w.st id).parked = [] := by assumption
            rw [hpark] at hq
            exact (List.not_mem_nil hq).elim
          · rw [setActor_other w1 id host a1 hh] at hq
            rw [show (w1.st host).parked = (w.st host).parked from congrArg Actor.parked (hst host)] at hq
            exact hq
    · expose_names
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        obtain ⟨abox, apark, hst⟩ := deliver_keeps_mail I w id _ _ w1 a1 hdel
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        let wC := creditSender (setActor w1 id admitted) (tname id) m.sender
        let resumed := resumeSender (wC.st p.sender) p.isCall id
        refine mail_subset I.desc w _ hH hP ?_ ?_
        · intro host msg hmem
          have hr := (resume_mail (wC.st p.sender) p.isCall id).1
          have hset : ((setActor wC p.sender resumed).st host).box =
              if host = p.sender then resumed.box else (wC.st host).box := by
            by_cases hs : host = p.sender
            · simp [setActor, hs, resumed]
            · simp [setActor, hs]
          rw [hset] at hmem
          by_cases hs : host = p.sender
          · simp [hs] at hmem
            rw [hr] at hmem
            simp [wC] at hmem
            have hc := (credit_lists (setActor w1 id admitted) (tname id) m.sender p.sender).1
            rw [hc] at hmem
            by_cases hid : host = id
            · have hwho : p.sender = id := by rw [← hs]; exact hid
              simp [setActor, hwho, admitted] at hmem
              rcases hmem with hmem | hmem
              · rw [abox] at hmem
                rw [hid]
                rw [heq]
                exact Or.inl (List.mem_cons_of_mem m (by simpa using hmem))
              · rw [hid]
                rw [heq_1]
                exact Or.inr ⟨p, by simp, hmem⟩
            · rw [← hs] at hmem
              rw [setActor_other w1 id host admitted hid] at hmem
              rw [show (w1.st host).box = (w.st host).box from congrArg Actor.box (hst host)] at hmem
              exact Or.inl hmem
          · simp [hs, wC] at hmem
            have hc := (credit_lists (setActor w1 id admitted) (tname id) m.sender host).1
            rw [hc] at hmem
            by_cases hid : host = id
            · simp [setActor, hid, admitted] at hmem
              rcases hmem with hmem | hmem
              · rw [abox] at hmem
                rw [hid]
                rw [heq]
                exact Or.inl (List.mem_cons_of_mem m (by simpa using hmem))
              · rw [hid]
                rw [heq_1]
                exact Or.inr ⟨p, by simp, hmem⟩
            · rw [setActor_other w1 id host admitted hid] at hmem
              rw [show (w1.st host).box = (w.st host).box from congrArg Actor.box (hst host)] at hmem
              exact Or.inl hmem
        · intro host q hq
          have hr := (resume_mail (wC.st p.sender) p.isCall id).2
          simp [wC, setActor, admitted] at hr
          by_cases hs : host = p.sender
          · simp [setActor, hs, admitted] at hq
            rw [hr] at hq
            have hc := (credit_lists (setActor w1 id admitted) (tname id) m.sender p.sender).2
            simp [setActor, admitted] at hc
            rw [hc] at hq
            by_cases hid : host = id
            · have hwho : p.sender = id := by rw [← hs]; exact hid
              simp [hwho] at hq
              rw [hid]
              rw [heq_1]
              exact List.mem_cons_of_mem p hq
            · have hwho : p.sender ≠ id := by rw [← hs]; exact hid
              simp [hwho] at hq
              rw [← hs] at hq
              rw [show (w1.st host).parked = (w.st host).parked from congrArg Actor.parked (hst host)] at hq
              exact hq
          · simp [setActor, hs, wC, admitted] at hq
            have hc := (credit_lists (setActor w1 id admitted) (tname id) m.sender host).2
            simp [setActor, admitted] at hc
            rw [hc] at hq
            by_cases hid : host = id
            · simp [setActor, hid, admitted] at hq
              rw [hid]
              rw [heq_1]
              exact List.mem_cons_of_mem p hq
            · simp [hid] at hq
              rw [show (w1.st host).parked = (w.st host).parked from congrArg Actor.parked (hst host)] at hq
              exact hq
    · expose_names
      split at h
      · cases h
      · next w1 a1 hdel =>
        cases h
        obtain ⟨abox, apark, hst⟩ := deliver_keeps_mail I w id _ _ w1 a1 hdel
        let wC := creditSender (setActor w1 id a1) (tname id) p.msg.sender
        let resumed := resumeSender (wC.st p.sender) p.isCall id
        refine mail_subset I.desc w _ hH hP ?_ ?_
        · intro host msg hmem
          have hr := (resume_mail (wC.st p.sender) p.isCall id).1
          simp [wC, setActor] at hr
          by_cases hs : host = p.sender
          · simp [setActor, hs] at hmem
            rw [hr] at hmem
            have hc := (credit_lists (setActor w1 id a1) (tname id) p.msg.sender p.sender).1
            simp [setActor] at hc
            rw [hc] at hmem
            by_cases hid : host = id
            · have hwho : p.sender = id := by rw [← hs]; exact hid
              simp [hwho] at hmem
              rw [abox] at hmem
              have hempty : (w.st id).box = [] := by assumption
              rw [hempty] at hmem
              exact (List.not_mem_nil hmem).elim
            · have hwho : p.sender ≠ id := by rw [← hs]; exact hid
              simp [hwho] at hmem
              rw [← hs] at hmem
              rw [show (w1.st host).box = (w.st host).box from congrArg Actor.box (hst host)] at hmem
              exact Or.inl hmem
          · simp [setActor, hs, wC] at hmem
            have hc := (credit_lists (setActor w1 id a1) (tname id) p.msg.sender host).1
            simp [setActor] at hc
            rw [hc] at hmem
            by_cases hid : host = id
            · simp [hid] at hmem
              rw [abox] at hmem
              have hempty : (w.st id).box = [] := by assumption
              rw [hempty] at hmem
              exact (List.not_mem_nil hmem).elim
            · simp [hid] at hmem
              rw [show (w1.st host).box = (w.st host).box from congrArg Actor.box (hst host)] at hmem
              exact Or.inl hmem
        · intro host q hq
          have hr := (resume_mail (wC.st p.sender) p.isCall id).2
          simp [wC, setActor] at hr
          by_cases hs : host = p.sender
          · simp [setActor, hs] at hq
            rw [hr] at hq
            have hc := (credit_lists (setActor w1 id a1) (tname id) p.msg.sender p.sender).2
            simp [setActor] at hc
            rw [hc] at hq
            by_cases hid : host = id
            · have hwho : p.sender = id := by rw [← hs]; exact hid
              simp [hwho] at hq
              rw [apark] at hq
              have hpark : (w.st id).parked = p :: ps := by assumption
              rw [hid]
              rw [hpark]
              exact List.mem_cons_of_mem p hq
            · have hwho : p.sender ≠ id := by rw [← hs]; exact hid
              simp [hwho] at hq
              rw [← hs] at hq
              rw [show (w1.st host).parked = (w.st host).parked from congrArg Actor.parked (hst host)] at hq
              exact hq
          · simp [setActor, hs, wC] at hq
            have hc := (credit_lists (setActor w1 id a1) (tname id) p.msg.sender host).2
            simp [setActor] at hc
            rw [hc] at hq
            by_cases hid : host = id
            · simp [hid] at hq
              rw [apark] at hq
              have hpark : (w.st id).parked = p :: ps := by assumption
              rw [hid]
              rw [hpark]
              exact List.mem_cons_of_mem p hq
            · simp [hid] at hq
              rw [show (w1.st host).parked = (w.st host).parked from congrArg Actor.parked (hst host)] at hq
              exact hq
    · cases h

/-- The actor after a fresh self-schedule label is queued. -/
def withSched (a : Actor) (id : InstId) (label : String) : Actor :=
  { a with
    prio := upsertPrio a.prio
      { label := label, sender := id, callFrom := none, reliable := true, mid := a.nextMid }
    nextMid := a.nextMid + 1 }

/-- The actor a self-schedule overflow crashes. -/
def crashedOf (a : Actor) : Actor :=
  { a with phase := .crashed }

/-- Running one effect keeps subtree mail on the subtree, and parked senders honest. -/
theorem exec_pack (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (ha : a = w.st id) (hH : MailHere I.desc w) (hP : ParkAlign w)
    (hB : subtreeMemberName I.desc (tname id) → bulkScopeOf I.desc (tname id) k.rest = true) :
    MailHere I.desc (execRun I w id a k) ∧ ParkAlign (execRun I w id a k) := by
  cases hrest : k.rest with
  | nil =>
    simp [execRun, hrest, ha]
    exact phase_pack I.desc w id { (w.st id) with phase := .idle, typestate := k.toState } hH hP rfl rfl
  | cons e es =>
    cases e with
    | send dst label hint =>
      simp only [execRun, hrest]
      match hr : route w I.desc id dst with
      | none =>
        simp [hr]
        exact phase_pack I.desc (noteStale w id dst) id (proceed a (afterHead k))
          (by intro host; simpa [noteStale_st] using hH host)
          (by intro host p hp; simpa [noteStale_st] using hP host p hp)
          (by simp [ha, proceed_box, noteStale_st]) (by simp [ha, proceed_parked, noteStale_st])
      | some host =>
        simp [hr]
        refine ⟨enqueue_keeps_here I.desc w hH id host
            { label := label, sender := id, callFrom := none } false (afterHead k) rfl ?_,
          enqueue_align I.desc w hP id host
            { label := label, sender := id, callFrom := none } false (afterHead k) rfl⟩
        intro hname
        have hok := member_effect_of_scope I.desc (tname id) (.send dst label hint) es hname
          (by simpa [hrest] using hB hname)
        simpa [memberHere] using
          scoped_lands w I.desc id host dst label hint (.send dst label hint) hname hok (Or.inl rfl) hr
    | trySend dst label hint onFull onGone =>
      simp only [execRun, hrest]
      match hr : route w I.desc id dst with
      | none =>
        simp [hr]
        exact phase_pack I.desc (noteStale w id dst) id (proceed a (afterHead k))
          (by intro host; simpa [noteStale_st] using hH host)
          (by intro host p hp; simpa [noteStale_st] using hP host p hp)
          (by simp [ha, proceed_box, noteStale_st]) (by simp [ha, proceed_parked, noteStale_st])
      | some host =>
        simp [hr]
        split
        · refine ⟨enqueue_keeps_here I.desc w hH id host
              { label := label, sender := id, callFrom := none, reliable := false } false (afterHead k) rfl ?_,
            enqueue_align I.desc w hP id host
              { label := label, sender := id, callFrom := none, reliable := false } false (afterHead k) rfl⟩
          intro hname
          have hok := member_effect_of_scope I.desc (tname id) (.trySend dst label hint onFull onGone) es hname
            (by simpa [hrest] using hB hname)
          simpa [memberHere] using
            scoped_lands w I.desc id host dst label hint (.trySend dst label hint onFull onGone) hname hok
              (Or.inr (Or.inl ⟨onFull, onGone, rfl⟩)) hr
        · exact phase_pack I.desc w id (proceed a (afterHead k)) hH hP
            (by simp [ha, proceed_box]) (by simp [ha, proceed_parked])
    | call dst label hint na to =>
      simp only [execRun, hrest]
      match hr : resolveId I.desc id dst with
      | none =>
        simp [hr]
        exact phase_pack I.desc (noteStale w id dst) id (proceed a (afterHead k))
          (by intro host; simpa [noteStale_st] using hH host)
          (by intro host p hp; simpa [noteStale_st] using hP host p hp)
          (by simp [ha, proceed_box, noteStale_st]) (by simp [ha, proceed_parked, noteStale_st])
      | some host =>
        simp [hr]
        refine ⟨enqueue_keeps_here I.desc w hH id host
            { label := label, sender := id, callFrom := some id } true (afterHead k) rfl ?_,
          enqueue_align I.desc w hP id host
            { label := label, sender := id, callFrom := some id } true (afterHead k) rfl⟩
        intro hname
        have hok := member_effect_of_scope I.desc (tname id) (.call dst label hint na to) es hname
          (by simpa [hrest] using hB hname)
        simpa [memberHere] using
          scoped_resolve I.desc id host dst label hint (.call dst label hint na to) hname hok
            (Or.inr (Or.inr ⟨na, to, rfl⟩)) hr
    | reply =>
      simp only [execRun, hrest, performReply]
      cases hto : k.replyTo with
      | none =>
        simp [hto]
        exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
          (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
      | some caller =>
        simp [hto]
        cases hphc : (w.st caller).phase with
        | awaitReply dst ck =>
          by_cases hd : dst = id
          · by_cases howe : (w.st id).oweId = some (w.st caller).waitId
            · simp [hphc, hd, howe]
              have h1 := phase_pack I.desc w caller (finishCall (w.st caller) ck .reply) hH hP
                (by cases hr : ck.rest <;> simp [finishCall, proceed, hr])
                (by cases hr : ck.rest <;> simp [finishCall, proceed, hr])
              exact phase_pack I.desc (setActor w caller (finishCall (w.st caller) ck .reply)) id
                (proceed ((setActor w caller (finishCall (w.st caller) ck .reply)).st id) (afterHead k))
                h1.1 h1.2 (proceed_box _ (afterHead k)) (proceed_parked _ (afterHead k))
            · simp [hphc, hd, howe]
              exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
                (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
          · simp [hphc, hd]
            exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
              (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | idle =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | run _ =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | parked _ _ _ =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | awaitEffect _ =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | awaitPeer _ =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
        | crashed =>
          simp [hphc]
          exact phase_pack I.desc w id (proceed (w.st id) (afterHead k)) hH hP
            (proceed_box (w.st id) (afterHead k)) (proceed_parked (w.st id) (afterHead k))
    | selfSchedule label =>
      simp only [execRun, hrest]
      split
      · exact phase_pack I.desc w id (proceed a (afterHead k)) hH hP
          (by simp [ha, proceed_box]) (by simp [ha, proceed_parked])
      · split
        · exact phase_pack I.desc w id (proceed (withSched a id label) (afterHead k)) hH hP
            (by simp [ha, withSched, proceed_box]) (by simp [ha, withSched, proceed_parked])
        · exact phase_pack I.desc w id (crashedOf a) hH hP (by simp [ha, crashedOf]) (by simp [ha, crashedOf])
    | cell dst label value =>
      simp only [execRun, hrest]
      have hcell : MailHere I.desc (setCell w dst label
          { value := max (w.cell dst label).value value, dirty := true }) ∧
          ParkAlign (setCell w dst label { value := max (w.cell dst label).value value, dirty := true }) := by
        simp [setCell]
        exact ⟨hH, hP⟩
      let wC := setCell w dst label { value := max (w.cell dst label).value value, dirty := true }
      have hrun := phase_pack I.desc wC id (proceed (wC.st id) (afterHead k)) hcell.1 hcell.2
        (proceed_box (wC.st id) (afterHead k)) (proceed_parked (wC.st id) (afterHead k))
      let wR := setActor wC id (proceed (wC.st id) (afterHead k))
      by_cases hdirty : (w.cell dst label).dirty = true
      · simp [hdirty]
        exact hrun
      · simp [hdirty, wakeReaders]
        exact wakes_pack I.desc (readersOf wR dst) wR hrun.1 hrun.2 dst label id
    | internal =>
      simp [execRun, hrest]
      exact phase_pack I.desc w id { a with phase := .awaitEffect (afterHead k) } hH hP
        (by simp [ha]) (by simp [ha])
    | peer =>
      simp [execRun, hrest]
      exact phase_pack I.desc w id { a with phase := .awaitPeer (afterHead k) } hH hP
        (by simp [ha]) (by simp [ha])
    | terminate =>
      obtain ⟨rest, sto, rto⟩ := k
      subst hrest
      have hstep := exec_term_step I w id a es sto rto
      generalize hw : execRun I w id a ⟨.terminate :: es, sto, rto⟩ = wR at hstep ⊢
      cases hstep with
      | kept => exact ⟨hH, hP⟩
      | lone t ht hsub htm hpk => exact release_pack I.desc w id a hH hP
      | cascade _ _ _ _ _ =>
        exact terminateStage_pack I.desc w id a hH hP

theorem detachMsg_sender (caller : InstId) (m : Msg) : (detachMsg caller m).sender = m.sender := by
  simp [detachMsg]
  split <;> simp

theorem countFrom_detach (caller sender : InstId) (ms : List Msg) :
    countFrom sender (ms.map (detachMsg caller)) = countFrom sender ms := by
  induction ms with
  | nil => simp [countFrom]
  | cons m ms ih =>
    simp only [List.map_cons, countFrom, detachMsg_sender, ih]

theorem countParked_call_split (caller : InstId) (ps : List Parked) :
    countParked caller (ps.filter fun p => !(p.sender == caller && p.isCall)) +
        (ps.filter fun p => p.sender == caller && p.isCall).length =
      countParked caller ps := by
  induction ps with
  | nil => simp [countParked, List.filter]
  | cons p ps ih =>
    cases hc : (p.sender == caller && p.isCall) with
    | false =>
      have hkeep : (!(p.sender == caller && p.isCall)) = true := by rw [hc]; rfl
      rw [List.filter_cons, hkeep, List.filter_cons, hc]
      simp only [if_true, countParked, Nat.add_assoc]
      rw [if_neg (by decide : ¬ (false = true))]
      exact congrArg (Nat.add (if p.sender = caller then 1 else 0)) ih
    | true =>
      have hdrop : (!(p.sender == caller && p.isCall)) = false := by rw [hc]; rfl
      have hs : p.sender = caller ∧ p.isCall = true := by
        simpa [Bool.and_eq_true, beq_iff_eq] using hc
      rw [List.filter_cons, hdrop, List.filter_cons, hc]
      simp only [if_true, countParked, hs.1, List.length_cons, Nat.add_assoc, Nat.add_left_comm]
      rw [if_neg (by decide : ¬ (false = true))]
      omega

theorem countParked_keep_other (caller sender : InstId) (hne : sender ≠ caller) (ps : List Parked) :
    countParked sender (ps.filter fun p => !(p.sender == caller && p.isCall)) =
      countParked sender ps := by
  induction ps with
  | nil => simp [countParked, List.filter]
  | cons p ps ih =>
    cases hc : (p.sender == caller && p.isCall) with
    | false =>
      have hkeep : (!(p.sender == caller && p.isCall)) = true := by rw [hc]; rfl
      rw [List.filter_cons, hkeep]
      simp only [if_true, countParked, ih]
    | true =>
      have hdrop : (!(p.sender == caller && p.isCall)) = false := by rw [hc]; rfl
      have hs : p.sender = caller ∧ p.isCall = true := by
        simpa [Bool.and_eq_true, beq_iff_eq] using hc
      have hne' : p.sender ≠ sender := by
        rw [hs.1]
        exact hne.symm
      rw [List.filter_cons, hdrop]
      rw [if_neg (by decide : ¬ (false = true))]
      simp only [countParked, if_neg hne', ih, Nat.zero_add]

/-- Replacing one box by the same messages with `callFrom` cleared does not change
what any sender owes. -/
theorem owed_detach (st : InstId → Actor) (id caller : InstId) (a : Actor)
    (hb : a.box = (st id).box.map (detachMsg caller)) (hp : a.parked = (st id).parked)
    (dst : String) (sender : InstId) (ids : List InstId) :
    owed (fun i => if i = id then a else st i) dst sender ids = owed st dst sender ids := by
  induction ids with
  | nil => rfl
  | cons j js ih =>
    simp only [owed, ih]
    by_cases hj : j = id
    · simp [slot, hj, hb, hp, countFrom_detach]
    · simp [slot, hj]

theorem clearReplyPhase_rest (caller : InstId) (ph : Phase) :
    contRest (clearReplyPhase caller ph) = contRest ph := by
  cases ph with
  | idle => simp [clearReplyPhase, contRest]
  | crashed => simp [clearReplyPhase, contRest]
  | run k =>
    simp [clearReplyPhase, contRest, clearReplyCont]
    split <;> simp [contRest]
  | parked d c k =>
    simp [clearReplyPhase, contRest, clearReplyCont]
    split <;> simp [contRest]
  | awaitReply d k =>
    simp [clearReplyPhase, contRest, clearReplyCont]
    split <;> simp [contRest]
  | awaitEffect k =>
    simp [clearReplyPhase, contRest, clearReplyCont]
    split <;> simp [contRest]
  | awaitPeer k =>
    simp [clearReplyPhase, contRest, clearReplyCont]
    split <;> simp [contRest]

theorem detach_box (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).box = a.box.map (detachMsg caller) := by
  simp [detachReply, detachBox]
  split <;> simp

theorem detach_park (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).parked = a.parked := by
  simp [detachReply, detachBox]
  split <;> simp

theorem detach_life (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).life = a.life := by
  simp [detachReply, detachBox]
  split <;> simp

theorem detach_ty (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).typestate = a.typestate := by
  simp [detachReply, detachBox]
  split <;> simp

theorem detach_tok (a : Actor) (caller : InstId) (cid : Nat) (d : String) :
    (detachReply (detachBox a caller) caller cid).tokens d = a.tokens d := by
  simp [detachReply, detachBox]
  split <;> simp

theorem detach_pending (a : Actor) (caller : InstId) (cid : Nat) (d : String) :
    pending (detachReply (detachBox a caller) caller cid) d = pending a d := by
  simp only [pending, detachReply]
  split
  · simp [detachBox, clearReplyPhase_rest]
  · rfl

/-- Scrubbing `callFrom` off one mailbox keeps the account. The messages stay,
so every sender still owes the same number. -/
theorem occ_scrub (I : Impl) (w : World) (id caller : InstId) (a : Actor) (hO : OccInv I w)
    (hlife : a.life = (w.st id).life) (hbox : a.box = (w.st id).box.map (detachMsg caller))
    (hpark : a.parked = (w.st id).parked) (htok : ∀ d, a.tokens d = (w.st id).tokens d)
    (hty : a.typestate = (w.st id).typestate)
    (hpend : ∀ d, pending a d ≤ pending (w.st id) d) : OccInv I (setActor w id a) := by
  have hst : (setActor w id a).st = fun i => if i = id then a else w.st i := rfl
  have hr : (setActor w id a).roster = w.roster := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact hO.nodup
  · intro i hl
    by_cases hi : i = id
    · rw [hi] at hl ⊢
      rw [setActor_self] at hl
      rw [hlife] at hl
      rw [hr]
      exact hO.aliveIn id hl
    · rw [setActor_other w id i a hi] at hl
      exact hO.aliveIn i hl
  · intro template i hi
    rw [actor_ix]
    exact hO.indexed template i (by simpa [setActor] using hi)
  · intro template ht
    rw [aliveCount_set_life w id a hlife template]
    exact hO.liveOne template ht
  · intro template ht
    rw [aliveCount_set_life w id a hlife template]
    exact hO.livePeer template ht
  · intro i hnin
    by_cases hi : i = id
    · rw [hi] at hnin ⊢
      have hold := hO.offEmpty id hnin
      rw [setActor_self, hbox, hpark, hold.1, hold.2]
      simp
    · rw [setActor_other w id i a hi]
      exact hO.offEmpty i hnin
  · intro i m hm
    by_cases hi : i = id
    · rw [hi, setActor_self, hbox] at hm
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      have hmem : m0.sender ∈ (setActor w id a).roster := by
        rw [hr]
        exact hO.sentFrom id m0 hm0
      simpa [detachMsg_sender] using hmem
    · rw [setActor_other w id i a hi] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    by_cases hi : i = id
    · rw [hi, setActor_self, hpark] at hp
      exact hO.parkFrom id p hp
    · rw [setActor_other w id i a hi] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    by_cases hi : i = id
    · rw [hi, setActor_self, hpark] at hp
      exact hO.parkMsg id p hp
    · rw [setActor_other w id i a hi] at hp
      exact hO.parkMsg i p hp
  · intro s d hs
    have howed := owed_detach w.st id caller a hbox hpark d s w.roster
    rw [hr] at hs
    rw [hst, hr, howed]
    by_cases hs' : s = id
    · simp [hs', htok]
      exact hO.balance id d (by simpa [hs'] using hs)
    · simp [hs']
      exact hO.balance s d hs
  · intro s d hs hl
    by_cases hs' : s = id
    · rw [hs'] at hl ⊢
      rw [setActor_self] at hl ⊢
      rw [hty, htok]
      exact Nat.le_trans (Nat.add_le_add_left (hpend d) _) (hO.slack id d (hO.aliveIn id (hlife ▸ hl)) (hlife ▸ hl))
    · have hl' : (w.st s).life = .alive := by
        rw [setActor_other w id s a hs'] at hl
        exact hl
      have hold := hO.slack s d hs hl'
      rw [setActor_other w id s a hs']
      exact hold
  · intro s d hs hterm
    have howed := owed_detach w.st id caller a hbox hpark d s w.roster
    rw [hr] at hs
    rw [hst, hr, howed]
    exact hO.still s d hs hterm
  · intro s d hs hdead
    have howed := owed_detach w.st id caller a hbox hpark d s w.roster
    rw [hr] at hs
    rw [hst, hr, howed]
    by_cases hs' : s = id
    · rw [hs'] at hdead hs ⊢
      rw [setActor_self] at hdead
      rw [hlife] at hdead
      exact hO.quiet id d hs hdead
    · rw [setActor_other w id s a hs'] at hdead
      exact hO.quiet s d hs hdead
  · intro i hl1
    by_cases hi : i = id
    · rw [hi] at hl1 ⊢
      rw [setActor_self, hpark]
      exact hO.clear id hl1
    · rw [setActor_other w id i a hi]
      exact hO.clear i hl1
  · intro i hdead
    by_cases hi : i = id
    · rw [hi] at hdead ⊢
      rw [setActor_self] at hdead ⊢
      rw [hlife] at hdead
      rw [hbox, hpark, (hO.deadEmpty id hdead).1, (hO.deadEmpty id hdead).2]
      simp
    · rw [setActor_other w id i a hi] at hdead ⊢
      exact hO.deadEmpty i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = id
      · rw [hh] at hm ⊢
        rw [setActor_self, hbox] at hm
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
        have hmem := (hO.sameKey id).1 m0 hm0
        have hl : ((setActor w id a).st m0.sender).life = (w.st m0.sender).life := by
          by_cases hs : m0.sender = id
          · rw [hs, setActor_self, hlife]
          · rw [setActor_other w id m0.sender a hs]
        simpa [detachMsg_sender] using (queueOk_life w (setActor w id a) m0.sender id hl).1 hmem
      · rw [setActor_other w id host a hh] at hm
        have hmem := (hO.sameKey host).1 m hm
        have hl : ((setActor w id a).st m.sender).life = (w.st m.sender).life := by
          by_cases hs : m.sender = id
          · rw [hs, setActor_self, hlife]
          · rw [setActor_other w id m.sender a hs]
        exact (queueOk_life w (setActor w id a) m.sender host hl).1 hmem
    · intro p hp
      by_cases hh : host = id
      · rw [hh] at hp ⊢
        rw [setActor_self, hpark] at hp
        have hmem := (hO.sameKey id).2 p hp
        have hl : ((setActor w id a).st p.sender).life = (w.st p.sender).life := by
          by_cases hs : p.sender = id
          · rw [hs, setActor_self, hlife]
          · rw [setActor_other w id p.sender a hs]
        exact (queueOk_life w (setActor w id a) p.sender id hl).1 hmem
      · rw [setActor_other w id host a hh] at hp
        have hmem := (hO.sameKey host).2 p hp
        have hl : ((setActor w id a).st p.sender).life = (w.st p.sender).life := by
          by_cases hs : p.sender = id
          · rw [hs, setActor_self, hlife]
          · rw [setActor_other w id p.sender a hs]
        exact (queueOk_life w (setActor w id a) p.sender host hl).1 hmem
  · intro i hi
    exact hO.shaped i (by simpa [hr] using hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = id
      · rw [hh, setActor_self, hbox] at hm
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
        have hfrom := (hO.coreFrom id (hh ▸ hk)).1 m0 hm0
        simpa [detachMsg_sender] using hfrom
      · rw [setActor_other w id host a hh] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      by_cases hh : host = id
      · rw [hh, setActor_self, hpark] at hp
        exact (hO.coreFrom id (hh ▸ hk)).2 p hp
      · rw [setActor_other w id host a hh] at hp
        exact (hO.coreFrom host hk).2 p hp

theorem slot_filter (st : InstId → Actor) (dst caller s : InstId) (d : String) :
    slot (fun i => if i = dst then
        { st dst with parked := (st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
      else st i) d s dst +
        (if s = caller ∧ d = tname dst then
          ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) =
      slot st d s dst := by
  by_cases hname : (tname dst == d) = true
  · have hd : d = tname dst := (by simpa [beq_iff_eq] using hname : tname dst = d).symm
    simp only [slot, hname, if_pos (rfl : dst = dst), if_true]
    by_cases hs : s = caller
    · have hcount := countParked_call_split caller (st dst).parked
      simp only [hs, hd, true_and, if_true]
      omega
    · have hcount := countParked_keep_other caller s hs (st dst).parked
      simp only [hs, false_and, if_false]
      omega
  · have hd : ¬ d = tname dst := by
      intro h
      exact absurd (by simpa [beq_iff_eq] using h.symm) hname
    simp only [slot]
    repeat rw [if_neg hname]
    simp only [hd, and_false, if_false, Nat.zero_add]

theorem owed_park_filter (st : InstId → Actor) (dst caller s : InstId) (d : String)
    (ids : List InstId) (hnd : ids.Nodup) :
    owed (fun i => if i = dst then
        { st dst with parked := (st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
      else st i) d s ids +
        (if s = caller ∧ d = tname dst ∧ dst ∈ ids then
          ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) =
      owed st d s ids := by
  induction ids with
  | nil => simp [owed]
  | cons j js ih =>
    have hcons := List.nodup_cons.mp hnd
    by_cases hj : j = dst
    · rw [hj] at hcons ⊢
      have hnot : dst ∉ js := hcons.1
      have htail := ih hcons.2
      simp only [owed]
      have hzero : (if s = caller ∧ d = tname dst ∧ dst ∈ js then
          ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) = 0 := by
        simp [hnot]
      rw [hzero, Nat.add_zero] at htail
      have hin : dst ∈ dst :: js := List.Mem.head _
      have hextra : (if s = caller ∧ d = tname dst ∧ dst ∈ dst :: js then
          ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) =
          (if s = caller ∧ d = tname dst then
            ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) := by
        simp [hin]
      rw [hextra, htail]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using slot_filter st dst caller s d
    · have htail := ih hcons.2
      simp only [owed]
      have hslot : slot (fun i => if i = dst then
          { st dst with parked := (st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
        else st i) d s j = slot st d s j := by
        simp only [slot]
        rw [if_neg hj]
      have hextra : (if s = caller ∧ d = tname dst ∧ dst ∈ j :: js then
          ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) =
          (if s = caller ∧ d = tname dst ∧ dst ∈ js then
            ((st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) := by
        by_cases hc : s = caller ∧ d = tname dst ∧ dst ∈ j :: js
        · rcases hc with ⟨hs, hd, hmem⟩
          have hjs : dst ∈ js := by
            rw [List.mem_cons] at hmem
            cases hmem with
            | inl h => exact absurd h.symm hj
            | inr h => exact h
          simp [hs, hd, hmem, hjs]
        · have hjs : ¬ (s = caller ∧ d = tname dst ∧ dst ∈ js) := by
            intro h
            exact hc (by
              rcases h with ⟨hs, hd, hmem⟩
              exact ⟨hs, hd, by simp [List.mem_cons, hmem]⟩)
          rw [if_neg hc, if_neg hjs]
      rw [hslot, hextra, Nat.add_assoc]
      exact congrArg (Nat.add (slot st d s j)) htail

theorem owed_credit_fold (ps : List Parked) (w : World) (name : String) (sender : InstId)
    (d : String) (s : InstId) (ids : List InstId) :
    owed ((ps.foldl (fun w _ => creditSender w name sender) w).st) d s ids = owed w.st d s ids := by
  induction ps generalizing w with
  | nil => rfl
  | cons _ ps ih =>
    simp only [List.foldl_cons]
    rw [ih (creditSender w name sender)]
    simpa [creditSender, setActor] using
      owed_same_queues w.st sender (bumpToken (w.st sender) name (.ofNat 1)) rfl rfl d s ids

theorem refundCall_box (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).box = (w.st i).box := by
  unfold refundParkedCall
  dsimp
  split
  · rfl
  · have hfold : ∀ (ps : List Parked) (w0 : World),
        (∀ j, (w0.st j).box = (w.st j).box) →
          ∀ j, ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st j).box =
            (w.st j).box := by
      intro ps
      induction ps with
      | nil => intro w0 h j; exact h j
      | cons _ ps ih =>
        intro w0 h j
        simp only [List.foldl_cons]
        exact ih _ (fun j => by rw [credit_box]; exact h j) j
    refine hfold _ _ ?_ i
    intro j
    by_cases hj : j = dst <;> simp [setActor, hj]

theorem refundCall_tok (w : World) (caller dst s : InstId) (d : String) :
    ((refundParkedCall w caller dst).st s).tokens d =
      (w.st s).tokens d +
        if s = caller ∧ d = tname dst then
          ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).length
        else 0 := by
  unfold refundParkedCall
  dsimp
  split
  · next hempty =>
    have hnil : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall) = [] := by
      cases hf : (w.st dst).parked.filter fun p => p.sender == caller && p.isCall with
      | nil => rfl
      | cons _ _ => simp [List.isEmpty, hf] at hempty
    simp [hnil, ite_self]
  · have hfold : ∀ (ps : List Parked) (w0 : World) (j : InstId) (e : String),
        ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).st j).tokens e =
          (w0.st j).tokens e + if j = caller ∧ e = tname dst then ps.length else 0 := by
      intro ps
      induction ps with
      | nil =>
        intro w0 j e
        simp [ite_self]
      | cons _ ps ih =>
        intro w0 j e
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        rw [credit_tok]
        by_cases hc : j = caller ∧ e = tname dst <;> simp [hc] <;> omega
    have hstart : ∀ j e, ((setActor w dst { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }).st j).tokens e =
        (w.st j).tokens e := by
      intro j e
      by_cases hj : j = dst <;> simp [setActor, hj]
    rw [hfold]
    rw [hstart]

theorem refundCall_N (w : World) (caller dst : InstId) :
    (refundParkedCall w caller dst).N = w.N := by
  unfold refundParkedCall
  dsimp
  split
  · rfl
  · have hfold : ∀ (ps : List Parked) (w0 : World), w0.N = w.N →
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).N = w.N := by
      intro ps
      induction ps with
      | nil => intro w0 h; exact h
      | cons _ ps ih =>
        intro w0 h
        simp only [List.foldl_cons]
        exact ih _ (by rw [creditSender, setActor]; exact h)
    exact hfold _ _ (by rw [setActor])

theorem refundCall_roster (w : World) (caller dst : InstId) :
    (refundParkedCall w caller dst).roster = w.roster := by
  unfold refundParkedCall
  dsimp
  split
  · rfl
  · have hfold : ∀ (ps : List Parked) (w0 : World), w0.roster = w.roster →
        (ps.foldl (fun w _ => creditSender w (tname dst) caller) w0).roster = w.roster := by
      intro ps
      induction ps with
      | nil => intro w0 h; exact h
      | cons _ ps ih =>
        intro w0 h
        simp only [List.foldl_cons]
        exact ih _ (by rw [creditSender, setActor]; exact h)
    exact hfold _ _ (by rw [setActor])

theorem refund_owed (I : Impl) (w : World) (caller dst s : InstId) (d : String) (hO : OccInv I w) :
    owed (refundParkedCall w caller dst).st d s w.roster +
        (if s = caller ∧ d = tname dst then
          ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).length else 0) =
      owed w.st d s w.roster := by
  let drop := (w.st dst).parked.filter fun p => p.sender == caller && p.isCall
  by_cases hempty : drop.isEmpty = true
  · have hnil : drop = [] := by
      cases hf : drop with
      | nil => rfl
      | cons _ _ => simp [List.isEmpty, hf] at hempty
    simp [refundParkedCall, drop, hempty, hnil, ite_self]
  · have hne : ¬ drop.isEmpty = true := hempty
    have hin : dst ∈ w.roster := by
      by_cases hin : dst ∈ w.roster
      · exact hin
      · have hempty := (hO.offEmpty dst hin).2
        have hnil : ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).isEmpty = true := by
          rw [hempty]
          simp [List.filter, List.isEmpty]
        rw [hnil] at hne
        exact False.elim (hne rfl)
    let drop := (w.st dst).parked.filter fun p => p.sender == caller && p.isCall
    let w1 := setActor w dst { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
    have howedF := owed_credit_fold drop w1 (tname dst) caller d s w.roster
    have howed1 := owed_park_filter w.st dst caller s d w.roster hO.nodup
    rw [show owed (refundParkedCall w caller dst).st d s w.roster =
        owed (drop.foldl (fun w _ => creditSender w (tname dst) caller) w1).st d s w.roster from ?_]
    · rw [howedF]
      have hex : (if s = caller ∧ d = tname dst ∧ dst ∈ w.roster then drop.length else 0) =
          (if s = caller ∧ d = tname dst then drop.length else 0) := by simp [hin]
      rw [← hex]
      have hst : (w1.st) = (fun i => if i = dst then
          { (w.st dst) with parked := (w.st dst).parked.filter fun p => !(p.sender == caller && p.isCall) }
        else w.st i) := by
        funext i
        simp [w1, setActor]
      rw [hst, show drop.length = ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).length from rfl]
      exact howed1
    · have hbit : drop.isEmpty = false := by
        cases hb : drop.isEmpty with
        | false => rfl
        | true => exact absurd hb hne
      unfold refundParkedCall
      simp only [drop, hbit, w1]
      rw [if_neg (by decide : ¬ (false = true))]

/-- Dropping a caller's parked call and returning its slots keeps the account. -/
theorem occ_refund_call (I : Impl) (w : World) (caller dst : InstId) (hO : OccInv I w) :
    OccInv I (refundParkedCall w caller dst) := by
  let w' := refundParkedCall w caller dst
  have hr := refundCall_roster w caller dst
  have hlife : ∀ i, (w'.st i).life = (w.st i).life := fun i => (refundCall_fields w caller dst i).2.1
  have hph : ∀ i, (w'.st i).phase = (w.st i).phase := fun i => (refundCall_fields w caller dst i).1
  have hty : ∀ i, (w'.st i).typestate = (w.st i).typestate := fun i =>
    (refundCall_fields w caller dst i).2.2.1
  have hbox : ∀ i, (w'.st i).box = (w.st i).box := fun i => refundCall_box w caller dst i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [w', hr] using hO.nodup
  · intro i hl
    rw [hr]
    exact hO.aliveIn i (by rw [← hlife i]; exact hl)
  · intro template i hi
    rw [refundCall_ix]
    exact hO.indexed template i (by simpa [w', hr] using hi)
  · intro template ht
    have hcount : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_congr _ _ w.roster ?_
      intro i _
      unfold aliveBit
      simp [w', hlife i]
    rw [hcount]
    exact hO.liveOne template ht
  · intro template ht
    have hcount : aliveCount w' template = aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_congr _ _ w.roster ?_
      intro i _
      unfold aliveBit
      simp [w', hlife i]
    have hN : w'.N = w.N := by simpa [w'] using refundCall_N w caller dst
    rw [hcount, hN]
    exact hO.livePeer template ht
  · intro i hnin
    have hnin' : i ∉ w.roster := by simpa [w', hr] using hnin
    have hold := hO.offEmpty i hnin'
    refine ⟨?_, ?_⟩
    · rw [hbox i]; exact hold.1
    · have hpk := (refundCall_fields w caller dst i).2.2.2
      rw [hpk]
      by_cases hi : i = dst
      · rw [hi] at hold ⊢
        simp [hold.2, List.filter, if_true]
      · simp [hi, hold.2]
  · intro i m hm
    rw [hbox i] at hm
    have hmem := hO.sentFrom i m hm
    simpa [w', hr] using hmem
  · intro i p hp
    have hpk := (refundCall_fields w caller dst i).2.2.2
    rw [hpk] at hp
    have hp' : p ∈ (w.st i).parked := by
      by_cases hi : i = dst
      · rw [hi] at hp ⊢
        rw [if_pos rfl] at hp
        exact (List.mem_filter.mp hp).1
      · simpa [hi] using hp
    simpa [w', hr] using hO.parkFrom i p hp'
  · intro i p hp
    have hpk := (refundCall_fields w caller dst i).2.2.2
    rw [hpk] at hp
    have hp' : p ∈ (w.st i).parked := by
      by_cases hi : i = dst
      · rw [hi] at hp ⊢
        rw [if_pos rfl] at hp
        exact (List.mem_filter.mp hp).1
      · simpa [hi] using hp
    exact hO.parkMsg i p hp'
  · intro s d hs
    rw [hr]
    have howed := refund_owed I w caller dst s d hO
    have htok := refundCall_tok w caller dst s d
    have hbal := hO.balance s d (by simpa [w', hr] using hs)
    calc
      owed w'.st d s w.roster + (w'.st s).tokens d
          = owed w'.st d s w.roster +
            ((w.st s).tokens d +
              if s = caller ∧ d = tname dst then
                ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).length
              else 0) := by rw [htok]
      _ = (owed w'.st d s w.roster +
            if s = caller ∧ d = tname dst then
              ((w.st dst).parked.filter fun p => p.sender == caller && p.isCall).length
            else 0) + (w.st s).tokens d := by omega
      _ = owed w.st d s w.roster + (w.st s).tokens d := by rw [howed]
      _ = budget I.desc (tname s) d := hbal
  · intro s d hs hl
    have hl0 : (w.st s).life = .alive := by rw [← hlife s]; exact hl
    have hold := hO.slack s d (by simpa [w', hr] using hs) hl0
    have hpend : pending (w'.st s) d = pending (w.st s) d := by simp [pending, hph s]
    rw [hty s, hpend, refundCall_tok w caller dst s d]
    exact Nat.le_trans hold (Nat.le_add_right _ _)
  · intro s d hs hterm
    rw [hr]
    have howed := refund_owed I w caller dst s d hO
    have hold := hO.still s d (by simpa [w', hr] using hs) hterm
    rw [hold] at howed
    omega
  · intro s d hs hdead
    rw [hr]
    have hdead0 : (w.st s).life ≠ .alive := by rw [← hlife s]; exact hdead
    have hold := hO.quiet s d (by simpa [w', hr] using hs) hdead0
    have howed := refund_owed I w caller dst s d hO
    omega
  · intro i hl1
    have hpk := (refundCall_fields w caller dst i).2.2.2
    rw [hpk]
    by_cases hi : i = dst
    · rw [hi] at hl1 ⊢
      simp [hO.clear dst hl1, List.filter, if_true]
    · simp [hi, hO.clear i hl1]
  · intro i hdead
    have hdead0 : (w.st i).life ≠ .alive := by rw [← hlife i]; exact hdead
    have hold := hO.deadEmpty i hdead0
    refine ⟨?_, ?_⟩
    · rw [hbox i]; exact hold.1
    · have hpk := (refundCall_fields w caller dst i).2.2.2
      rw [hpk]
      by_cases hi : i = dst
      · rw [hi] at hold ⊢
        simp [hold.2, List.filter, if_true]
      · simp [hi, hold.2]
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hbox host] at hm
      have hmem := (hO.sameKey host).1 m hm
      exact (queueOk_life w w' m.sender host (hlife m.sender)).1 hmem
    · intro p hp
      have hpk := (refundCall_fields w caller dst host).2.2.2
      rw [hpk] at hp
      have hp' : p ∈ (w.st host).parked := by
        by_cases hh : host = dst
        · rw [hh] at hp ⊢
          rw [if_pos rfl] at hp
          exact (List.mem_filter.mp hp).1
        · simpa [hh] using hp
      have hmem := (hO.sameKey host).2 p hp'
      exact (queueOk_life w w' p.sender host (hlife p.sender)).1 hmem
  · intro i hi
    exact hO.shaped i (by simpa [w', hr] using hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hbox host] at hm
      exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      have hpk := (refundCall_fields w caller dst host).2.2.2
      rw [hpk] at hp
      have hp' : p ∈ (w.st host).parked := by
        by_cases hh : host = dst
        · rw [hh] at hp ⊢
          rw [if_pos rfl] at hp
          exact (List.mem_filter.mp hp).1
        · simpa [hh] using hp
      exact (hO.coreFrom host hk).2 p hp'

theorem finish_tok (a : Actor) (k : Cont) (r : CallResult) (d : String) :
    (finishCall a k r).tokens d = a.tokens d := by
  unfold finishCall proceed
  split <;> rfl

theorem finish_pending (a : Actor) (k : Cont) (r : CallResult) (d : String) :
    pending (finishCall a k r) d = pending (proceed a (selectCall k r)) d := by
  unfold finishCall
  cases hr : (selectCall k r).rest <;> simp [proceed, pending, hr]

theorem occ_timeout (I : Impl) (w w' : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (h : callTimeout w id = some w') : OccInv I w' := by
  unfold callTimeout at h
  dsimp only at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hgo : ((w.st id).life != .alive) = false := by simpa [Bool.not_eq_true] using hlive
    simp only [hgo] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      cases h
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hpend : ∀ d, pending host d ≤ pending (w.st dst) d := by
        intro d
        rw [detach_pending (w.st dst) id cid d]
        exact Nat.le_refl _
      have hO1 := occ_scrub I w dst id host hO (detach_life (w.st dst) id cid)
        (detach_box (w.st dst) id cid) (detach_park (w.st dst) id cid)
        (fun d => detach_tok (w.st dst) id cid d) (detach_ty (w.st dst) id cid) hpend
      have htyC : (w1.st id).typestate = k.toState := by
        have hty0 : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hC id
        by_cases hself : id = dst
        · simp [w1, host, hself, setActor_self, detach_ty]
          rw [hself] at hty0
          exact hty0
        · simp [w1, setActor_other w dst id host hself, hty0]
      have hfin := finish_keeps_ty (w1.st id) k .timedOut htyC
      apply occ_keep I w1 id (finishCall (w1.st id) k .timedOut) hO1 hfin.2
        (by unfold finishCall; exact proceed_keeps_box (w1.st id) k)
        (by unfold finishCall; exact proceed_keeps_parked (w1.st id) k)
        (finish_tok (w1.st id) k .timedOut) hfin.1
        (by
          intro d
          rw [finish_pending (w1.st id) k .timedOut d]
          cases hr : k.rest with
          | nil =>
            unfold proceed pending
            simp [hr, sendsTo, contRest]
          | cons _ _ =>
            have hrest : contRest (w1.st id).phase = k.rest := by
              by_cases hself : id = dst
              · rw [hself] at hph ⊢
                by_cases howe : ((w.st dst).oweId == some cid) = true
                · simp only [w1, host, setActor_self, detachReply, detachBox, howe, hph, clearReplyPhase, contRest]
                  exact (clearReplyCont_keeps id k).1
                · have hbit : ((w.st dst).oweId == some cid) = false := by
                    cases hb : (w.st dst).oweId == some cid with
                    | true => exact absurd hb howe
                    | false => rfl
                  simp [w1, host, setActor_self, detachReply, detachBox, hbit, hph, contRest]
              · simp [w1, setActor_other w dst id host hself, hph, contRest]
            have hp : pending (proceed (w1.st id) k) d = sendsTo d k.rest := by
              unfold proceed pending
              simp [hr, contRest]
            rw [hp]
            unfold pending
            rw [hrest]
            exact Nat.le_refl _)
    | parked dst b k =>
      cases b with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        cases h
        have hO1 := occ_refund_call I w id dst hO
        have htyC : ((refundParkedCall w id dst).st id).typestate = k.toState := by
          have hty0 : (w.st id).typestate = k.toState := by simpa [contTy, hph] using hC id
          exact ((refundCall_fields w id dst id).2.2.1).trans hty0
        have hfin := finish_keeps_ty ((refundParkedCall w id dst).st id) k .notAdmitted htyC
        apply occ_keep I (refundParkedCall w id dst) id
          (finishCall ((refundParkedCall w id dst).st id) k .notAdmitted) hO1 hfin.2
          (by unfold finishCall; exact proceed_keeps_box ((refundParkedCall w id dst).st id) k)
          (by
            unfold finishCall
            exact proceed_keeps_parked ((refundParkedCall w id dst).st id) k)
          (finish_tok ((refundParkedCall w id dst).st id) k .notAdmitted) hfin.1
          (by
            intro d
            rw [finish_pending ((refundParkedCall w id dst).st id) k .notAdmitted d]
            have hph1 := (refundCall_fields w id dst id).1
            cases hr : k.rest with
            | nil =>
              unfold proceed pending
              simp [hr, sendsTo, contRest]
            | cons _ _ =>
              have hp : pending (proceed ((refundParkedCall w id dst).st id) k) d = sendsTo d k.rest := by
                unfold proceed pending
                simp [hr, contRest]
              have hold : pending ((refundParkedCall w id dst).st id) d = sendsTo d k.rest := by
                simp [pending, hph1, hph, contRest]
              rw [hp, hold]
              exact Nat.le_refl _)
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem timeout_pack (D : Description) (w : World) (id : InstId) (w' : World) (hH : MailHere D w)
    (hP : ParkAlign w) (h : callTimeout w id = some w') : MailHere D w' ∧ ParkAlign w' := by
  unfold callTimeout at h
  dsimp only at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hgo : ((w.st id).life != .alive) = false := by simpa [Bool.not_eq_true] using hlive
    simp only [hgo, ite_false] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp only [hph] at h
      cases h
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hH1 : MailHere D w1 := by
        intro mb
        by_cases hmb : mb = dst
        · subst hmb
          refine ⟨?_, ?_⟩
          · intro m hm
            simp [w1, setActor, host, detachReply, detachBox] at hm
            split at hm
            · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
              simpa [memberHere, detachMsg_sender] using (hH mb).1 m0 hm0
            · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
              simpa [memberHere, detachMsg_sender] using (hH mb).1 m0 hm0
          · intro p hp
            simp [w1, setActor, host, detachReply, detachBox] at hp
            split at hp
            · exact (hH mb).2 p hp
            · exact (hH mb).2 p hp
        · refine ⟨?_, ?_⟩
          · intro m hm
            simp [w1, setActor, hmb] at hm
            exact (hH mb).1 m hm
          · intro p hp
            simp [w1, setActor, hmb] at hp
            exact (hH mb).2 p hp
      have hP1 : ParkAlign w1 := by
        intro mb p hp
        by_cases hmb : mb = dst
        · subst hmb
          simp [w1, setActor, host, detachReply, detachBox] at hp
          split at hp
          · exact hP mb p hp
          · exact hP mb p hp
        · simp [w1, setActor, hmb] at hp
          exact hP mb p hp
      have hbox : (finishCall (w1.st id) k .timedOut).box = (w1.st id).box := by
        cases hr : k.rest <;> simp [finishCall, proceed, hr]
      have hpark : (finishCall (w1.st id) k .timedOut).parked = (w1.st id).parked := by
        cases hr : k.rest <;> simp [finishCall, proceed, hr]
      exact phase_pack D w1 id (finishCall (w1.st id) k .timedOut) hH1 hP1 hbox hpark
    | parked dst b k =>
      cases b with
      | false => simp [hph] at h
      | true =>
        simp only [hph] at h
        cases h
        let w1 := refundParkedCall w id dst
        have hsub : ∀ i p, p ∈ (w1.st i).parked → p ∈ (w.st i).parked := by
          intro i p hp
          have hf := refundCall_fields w id dst i
          by_cases hi : i = dst
          · subst hi
            have hpk : (w1.st i).parked =
                (w.st i).parked.filter fun q => !(q.sender == id && q.isCall) := by
              simpa using hf.2.2.2
            rw [hpk] at hp
            exact (List.mem_filter.mp hp).1
          · have hpk : (w1.st i).parked = (w.st i).parked := by simpa [hi] using hf.2.2.2
            rw [hpk] at hp
            exact hp
        have hbox0 : ∀ i, (w1.st i).box = (w.st i).box := by
          intro i
          simp [w1, refundParkedCall]
          split
          · rfl
          · have hfold : ∀ (ps : List Parked) (w0 : World),
                (∀ j, (w0.st j).box = (w.st j).box) →
                  ∀ j, ((ps.foldl (fun w _ => creditSender w (tname dst) id) w0).st j).box =
                    (w.st j).box := by
              intro ps
              induction ps with
              | nil =>
                intro w0 h j
                exact h j
              | cons p ps ih =>
                intro w0 h j
                simp only [List.foldl_cons]
                have h1 : ∀ j, ((creditSender w0 (tname dst) id).st j).box = (w.st j).box := by
                  intro j
                  rw [(credit_lists w0 (tname dst) id j).1]
                  exact h j
                exact ih _ h1 j
            refine hfold _ _ ?_ i
            intro j
            by_cases hj : j = dst <;> simp [setActor, hj]
        have hH1 : MailHere D w1 := by
          intro mb
          refine ⟨?_, ?_⟩
          · intro m hm
            exact (hH mb).1 m (by rw [← hbox0 mb]; exact hm)
          · intro p hp
            exact (hH mb).2 p (hsub mb p hp)
        have hP1 : ParkAlign w1 := by
          intro mb p hp
          exact hP mb p (hsub mb p hp)
        have hbox : (finishCall (w1.st id) k .notAdmitted).box = (w1.st id).box := by
          cases hr : k.rest <;> simp [finishCall, proceed, hr]
        have hpark : (finishCall (w1.st id) k .notAdmitted).parked = (w1.st id).parked := by
          cases hr : k.rest <;> simp [finishCall, proceed, hr]
        exact phase_pack D w1 id (finishCall (w1.st id) k .notAdmitted) hH1 hP1 hbox hpark
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

/-- One enabled action keeps subtree mail on the subtree. -/
theorem mail_pack_step (I : Impl) (a : Action) (w w' : World) (hH : MailHere I.desc w)
    (hP : ParkAlign w) (hB : ∀ id, bulkScopeOf I.desc (tname id) (contRest (w.st id).phase) = true)
    (h : apply I a w = some w') : MailHere I.desc w' ∧ ParkAlign w' := by
  cases a with
  | recvBulk s =>
    simp [apply] at h
    exact bulk_pack I w w' s hH hP h
  | recvPrio s =>
    simp [apply] at h
    exact prio_pack I w w' s hH hP h
  | finish s =>
    simp [apply] at h
    exact finish_pack I w w' s hH hP h
  | spawn template =>
    simp [apply] at h
    exact spawn_pack I w w' template hH hP h
  | ingress dst label =>
    simp [apply] at h
    exact ingress_pack I w w' dst label hH hP h
  | callTimeout s =>
    simp [apply] at h
    exact timeout_pack I.desc w s w' hH hP h
  | stutter =>
    cases stutter_unchanged I w w' h
    exact ⟨hH, hP⟩
  | exec s =>
    simp [apply] at h
    unfold execHead at h
    by_cases hlive : (w.st s).life = .alive
    · simp [hlive] at h
      cases hph : (w.st s).phase with
      | run k =>
        simp [hph] at h
        cases h
        exact exec_pack I w s (w.st s) k rfl hH hP
          (fun hname => by simpa [contRest, hph] using hB s)
      | idle => simp [hph] at h
      | parked _ _ _ => simp [hph] at h
      | awaitReply _ _ => simp [hph] at h
      | awaitEffect _ => simp [hph] at h
      | awaitPeer _ => simp [hph] at h
      | crashed => simp [hph] at h
    · simp [hlive] at h

end Deadlock
