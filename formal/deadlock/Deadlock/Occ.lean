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

/-- Who may leave mail in a core. A core, a role that does not terminate, or a
lone terminable per-peer. A subtree member addresses only a per-peer of its
subtree, so its mail is not left in a core. A lone terminable has no subtree:
its try-send or call is charged to its own key, and the message may sit here. -/
def coreSender (D : Description) (sender : InstId) : Prop :=
  peerKey sender = none ∨ terminableB D (tname sender) = false ∨
    loneTerminableB D (tname sender) = true

/-- Empty-subtree roots are allocated from `nextIx`. Every such key already on
the roster is strictly below the counter, so the next birth does not share
a slot with a live generation. -/
def IxFresh (D : Description) (w : World) : Prop :=
  ∀ name k g, InstId.peer name k g ∈ w.roster →
    ∀ t, templateOf D name = some t →
      t.supervisor = none → t.subtree = "" → t.slots = 0 →
        k < w.nextIx name

theorem ixFresh_copy (D : Description) (w w' : World) (h : IxFresh D w)
    (hr : w'.roster = w.roster) (hix : ∀ n, w'.nextIx n = w.nextIx n) : IxFresh D w' := by
  intro name k g hmem t ht hsup hsub hslots
  have hmem0 : InstId.peer name k g ∈ w.roster := by rw [hr] at hmem; exact hmem
  simpa [hix] using h name k g hmem0 t ht hsup hsub hslots

/-- Outstanding credit and queues. A Lemma-1 capacity does not keep the parked
lane empty: a pool has `slots` keys, and a later key still sends while an
earlier key's mail sits in the box. `deadEmpty` and `quiet` are not claimed
of a crashed world: the crash kills the roster and leaves the mail queued. -/
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
  /-- A lone terminable's queued mail is charged to its own budget. A try-send
  or a call may be in flight; it is not a second account. -/
  still : ∀ s d, s ∈ w.roster → loneTerminableName I.desc (tname s) →
    owed w.st d s w.roster ≤ budget I.desc (tname s) d
  /-- A non-alive id, while the world has not crashed, owes at most its budget.
  Tokens left on that id are not part of the bound. -/
  quiet : w.crashed = false →
    ∀ s d, s ∈ w.roster → (w.st s).life ≠ .alive →
      (owed w.st d s w.roster : Int) ≤ (budget I.desc (tname s) d : Int)
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
  /-- Mail in a core comes from a `coreSender`: a core, a role that does not
  terminate, or a lone terminable per-peer. A subtree member does not. -/
  coreFrom : ∀ host, peerKey host = none →
    (∀ m ∈ (w.st host).box, coreSender I.desc m.sender) ∧
    (∀ p ∈ (w.st host).parked, coreSender I.desc p.sender)
  /-- The next empty-subtree root key is unused. -/
  ixFresh : IxFresh I.desc w

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

/-- A bulk effect that is in scope and aimed at a core comes from a `coreSender`.
A multiplicity-one role is that core. A role that does not terminate may send.
A lone terminable per-peer may try-send or call, and the message is charged to
its key. A subtree member's program addresses only a per-peer. -/
theorem core_send_from (I : Impl) (w : World) (hO : OccInv I w) (sender dstId : InstId)
    (e : Eff) (es : List Eff) (hmem : dstId ∈ w.roster) (hsend : sender ∈ w.roster)
    (hbulk : bulkScopeOf I.desc (tname sender) (e :: es) = true)
    (he : ∃ label hint,
      e = .send (tname dstId) label hint ∨ (∃ na to, e = .call (tname dstId) label hint na to) ∨
        (∃ full gone, e = .trySend (tname dstId) label hint full gone))
    (hk : peerKey dstId = none) :
    coreSender I.desc sender := by
  cases ht : templateOf I.desc (tname sender) with
  | none =>
    exact Or.inr (Or.inl (by simp [terminableB, ht]))
  | some t =>
    obtain ⟨tS, htS, hshape⟩ := hO.shaped sender hsend
    have hts : tS = t := by
      rw [ht] at htS
      cases htS
      rfl
    simp only [bulkScopeOf, ht] at hbulk
    by_cases hone : (t.multiplicity == .one) = true
    · have hm : t.multiplicity = .one := by
        cases htmul : t.multiplicity with
        | one => rfl
        | perPeer =>
          have hfalse : (Multiplicity.perPeer == Multiplicity.one) = false := by decide
          rw [htmul] at hone
          exact Bool.noConfusion (hone.symm.trans hfalse)
      rw [← hts] at hm
      simp only [hm] at hshape
      cases hshape
      exact Or.inl rfl
    · have hnot1 : (t.multiplicity == .one) = false := by
        cases hb : (t.multiplicity == .one) with
        | false => rfl
        | true => exact absurd hb hone
      by_cases hterm : t.terminable = true
      · simp only [hnot1, hterm, Bool.or_false, Bool.not_true] at hbulk
        by_cases hsub : (t.subtree == "") = true
        · cases hmul : t.multiplicity with
          | one =>
            rw [hmul] at hnot1
            have htrue : (Multiplicity.one == Multiplicity.one) = true := by decide
            exact Bool.noConfusion (hnot1.symm.trans htrue)
          | perPeer =>
            have hmulB : (t.multiplicity == .perPeer) = true := by
              rw [hmul]
              decide
            exact Or.inr (Or.inr (by simp [loneTerminableB, ht, hmulB, hterm, hsub]))
        · have hsub' : (t.subtree == "") = false := by
            cases hb : (t.subtree == "") with
            | false => rfl
            | true => exact absurd hb hsub
          simp only [hsub', Bool.false_eq_true, ite_false] at hbulk
          have hok := memberProgram_head I.desc (tname sender) e es hbulk
          obtain ⟨label, hint, he⟩ := he
          have htalk : sameSubtree I.desc (tname sender) (tname dstId) = true ∧
              perPeerB I.desc (tname dstId) = true := by
            rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
            · simp [memberEffectOk, subtreeTalk, Bool.and_eq_true] at hok
              exact hok
            · simp [memberEffectOk, subtreeTalk, Bool.and_eq_true] at hok
              exact hok.1.1
            · simp [memberEffectOk, subtreeTalk, Bool.and_eq_true] at hok
              exact hok.1.1
          have hper : perPeerB I.desc (tname dstId) = true := htalk.2
          rcases hO.shaped dstId hmem with ⟨tD, htD, hshapeD⟩
          have hmulD : tD.multiplicity = .perPeer := by
            simp only [perPeerB, htD] at hper
            cases hbb : tD.multiplicity with
            | perPeer => rfl
            | one =>
              have hfalse : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
              simp [hbb, hfalse] at hper
          have hex : ∃ k g, dstId = InstId.peer tD.name k g := by simpa [hmulD] using hshapeD
          obtain ⟨k, g, hid⟩ := hex
          cases dstId with
          | core _ => cases hid
          | peer _ _ _ => simp [peerKey] at hk
      · have hterm' : t.terminable = false := by
          cases hb : t.terminable with
          | false => rfl
          | true => exact absurd hb hterm
        exact Or.inr (Or.inl (by simp [terminableB, ht, hterm']))

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
          exact Or.inr (hsend.trans hkey.symm)

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
      split at h
      · next hsl =>
        have hslots : t.slots ≠ 0 := by simpa [bne, beq_iff_eq] using hsl
        split at h
        · split at h
          · next hfind =>
            cases h
            have hname := (findLive_spec w dst slot id hfind).1
            exact Or.inl (by
              unfold openHost
              rw [hname, ht]
              exact Or.inr hslots)
          · cases h
            exact Or.inl (by
              unfold openHost
              simp [tname, ht]
              exact Or.inr hslots)
        · cases h
      · split at h
        · cases h
        · next k hk =>
          have hsend : peerKey sender = some k := by
            cases sender with
            | core _ => simp [memberKey] at hk
            | peer _ key _ =>
              simp [memberKey] at hk
              simp [peerKey, hk]
          split at h
          · next hfind =>
            cases h
            have hkey : peerKey id = some k := by
              have hp := List.find?_some hfind
              cases id with
              | core _ => simp [findLive] at hp
              | peer _ key _ =>
                simp only [findLive, Bool.and_eq_true, beq_iff_eq] at hp
                obtain ⟨⟨_, hk'⟩, _⟩ := hp
                subst hk'
                rfl
            exact Or.inr (hsend.trans hkey.symm)
          · cases h
            exact Or.inr (by simpa [peerKey] using hsend)

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
    have hex : ∃ k g, s = InstId.peer t.name k g := by simpa [hm] using hmul
    obtain ⟨k, g, hidS⟩ := hex
    cases s with
    | core _ => cases hidS
    | peer _ _ _ => simp [peerKey] at hpk
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
            have hex : ∃ k g, s = InstId.peer t.name k g := by simpa [hm] using hmul
            obtain ⟨k, g, hidS⟩ := hex
            cases s with
            | core _ => cases hidS
            | peer _ _ _ => simp [peerKey] at hk
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

/-- Mail from every generation of one key, on every host of `dst`, is at most
that template's budget. The live generation's tokens are the rest of the same
account, and a live actor's tokens are at least zero. A pool may occupy
`slots` keys at once, so this bound is per key: the sum over keys is not
`capBulk`. -/
theorem key_queued_le (I : Impl) (w : World) (h : OccInv I w) (name : String) (key : Nat)
    (dst : String) : queuedFromKey w name key dst ≤ budget I.desc name dst := by
  cases hlive : findLive w name key with
  | none =>
    exact Int.ofNat_le.mp (h.balance.2 name key dst hlive)
  | some id =>
    have hbal := h.balance.1.1 name key id dst hlive
    have hl : (w.st id).life = .alive := (findLive_spec w name key id hlive).2
    have hS := h.slack id dst hl
    have h0 : (0 : Int) ≤ (w.st id).tokens dst :=
      Int.le_trans (Int.natCast_nonneg _) hS
    have hq : (queuedFromKey w name key dst : Int) ≤ (budget I.desc name dst : Int) := by
      omega
    exact Int.ofNat_le.mp hq


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
  have hmap : subtreeFails D = [] := hG.subtrees
  unfold subtreeFails at hmap
  have hleft : (D.templates.filterMap (subtreeEntry D)) = [] :=
    (List.append_eq_nil_iff.mp hmap).1
  have hent : subtreeEntry D t = none :=
    filterMap_mem_none (subtreeEntry D) D.templates t hleft (templateOf_mem D name t ht).1
  exact subtreeEntry_not_one D t hne hone hent

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
theorem box_filter_snoc (p : Msg → Bool) (ms : List Msg) (m : Msg) :
    ((ms ++ [m]).filter p).length = (ms.filter p).length + if p m = true then 1 else 0 := by
  rw [List.filter_append]
  cases hp : p m <;> simp [List.filter, hp]

theorem park_filter_snoc (p : Parked → Bool) (ps : List Parked) (x : Parked) :
    ((ps ++ [x]).filter p).length = (ps.filter p).length + if p x = true then 1 else 0 := by
  rw [List.filter_append]
  cases hp : p x <;> simp [List.filter, hp]

theorem foldl_add_const (c : InstId → Nat) (e b : Nat) :
    ∀ ids : List InstId,
      List.foldl (fun n h => n + c h) (b + e) ids = List.foldl (fun n h => n + c h) b ids + e := by
  intro ids
  induction ids generalizing b with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons]
    have hsum : b + e + c x = b + c x + e := by omega
    rw [hsum]
    exact ih (b + c x)

theorem foldl_add_agree (c d : InstId → Nat) (b : Nat) :
    ∀ ids : List InstId, (∀ x, x ∈ ids → c x = d x) →
      List.foldl (fun n h => n + c h) b ids = List.foldl (fun n h => n + d h) b ids := by
  intro ids
  induction ids generalizing b with
  | nil =>
    intro _
    rfl
  | cons x t ih =>
    intro h
    simp only [List.foldl_cons]
    rw [h x (List.Mem.head _)]
    exact ih (b + d x) fun y hy => h y (List.Mem.tail _ hy)

theorem foldl_add_once (c d : InstId → Nat) (extra : Nat) (target : InstId)
    (hd : c target = d target + extra) (hs : ∀ x, x ≠ target → c x = d x) :
    ∀ (b : Nat) (ids : List InstId), ids.Nodup →
      List.foldl (fun n h => n + c h) b ids =
        List.foldl (fun n h => n + d h) b ids + if target ∈ ids then extra else 0 := by
  intro b ids
  induction ids generalizing b with
  | nil =>
    intro _
    simp
  | cons x t ih =>
    intro nd
    have hc := List.nodup_cons.mp nd
    simp only [List.foldl_cons]
    by_cases hx : x = target
    · rw [hx]
      rw [hd]
      have hnin : target ∉ t := by simpa [hx] using hc.1
      have hagree :=
        foldl_add_agree c d (b + d target) t fun y hy =>
          hs y (by
            intro he
            exact hnin (he ▸ hy))
      have hconst := foldl_add_const c extra (b + d target) t
      have hsum : b + (d target + extra) = b + d target + extra := by omega
      rw [hsum, hconst, hagree]
      simp [List.mem_cons]
    · rw [hs x hx]
      have hx' : target ≠ x := Ne.symm hx
      simp [List.mem_cons, hx']
      exact ih (b + d x) hc.2

/-- Appending one message adds it to `queuedFromKey` only on the host that
stores it, and only when that host's template is `dst` and the sender is the
named key. Later steps add a count to the running total, so the extra one is
carried through the rest of the roster. -/
theorem queuedFromKey_append (w : World) (id : InstId) (a : Actor) (msg : Msg) (name : String)
    (key : Nat) (dst : String) (nodup : w.roster.Nodup) (hmem : id ∈ w.roster)
    (hbox : a.box = (w.st id).box ++ [msg]) (hpark : a.parked = (w.st id).parked) :
    queuedFromKey (setActor w id a) name key dst =
      queuedFromKey w name key dst +
        if (tname id != dst) = true then 0 else if keyPred name key msg = true then 1 else 0 := by
  let extra := if (tname id != dst) = true then 0 else if keyPred name key msg = true then 1 else 0
  let pred := keyPred name key
  let add (st : InstId → Actor) (host : InstId) : Nat :=
    if (tname host != dst) = true then 0
    else ((st host).box.filter pred).length + ((st host).parked.filter fun (p : Parked) => pred p.msg).length
  let st' : InstId → Actor := fun host => if host = id then a else w.st host
  have hd : add st' id = add w.st id + extra := by
    have hst : st' id = a := by simp [st']
    simp only [add, hst]
    by_cases ht : (tname id != dst) = true
    · simp [ht, extra]
    · have hf : (tname id != dst) = false := by
        cases hbb : tname id != dst with
        | false => rfl
        | true => exact absurd hbb ht
      simp only [ht, hf, Bool.false_eq_true, ite_false]
      rw [hbox, hpark, box_filter_snoc]
      simp only [extra, pred, ht, Bool.false_eq_true, ite_false]
      omega
  have hs : ∀ x, x ≠ id → add st' x = add w.st x := by
    intro x hx
    have hst : st' x = w.st x := by simp [st', hx]
    simp [add, hst]
  unfold queuedFromKey
  simp only [setActor]
  let step (st : InstId → Actor) (n : Nat) (host : InstId) : Nat :=
    if (tname host != dst) = true then n
    else n + ((st host).box.filter pred).length + ((st host).parked.filter fun (p : Parked) => pred p.msg).length
  have hstep (st : InstId → Actor) (n : Nat) (host : InstId) : step st n host = n + add st host := by
    simp only [step, add]
    by_cases ht : (tname host != dst) = true
    · simp [ht]
    · have hf : (tname host != dst) = false := by
        cases hbb : tname host != dst with
        | false => rfl
        | true => exact absurd hbb ht
      simp [ht, hf]
      omega
  have hL := foldl_pointwise (step st') (fun n h => n + add st' h) w.roster 0 fun n host _ => hstep st' n host
  have hR := foldl_pointwise (step w.st) (fun n h => n + add w.st h) w.roster 0 fun n host _ => hstep w.st n host
  have hfold := foldl_add_once (add st') (add w.st) extra id hd hs 0 w.roster nodup
  have hglue (st : InstId → Actor) :
      List.foldl (step st) 0 w.roster =
        List.foldl (fun n host =>
          if (tname host != dst) = true then n
          else n + ((st host).box.filter (fun m =>
            match m.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length +
            ((st host).parked.filter (fun p =>
            match p.msg.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length) 0 w.roster := by
    refine foldl_pointwise _ _ w.roster 0 ?_
    intro n host _
    simp [step, pred, keyPred]
    rfl
  have hLft := hglue st'
  have hRgt := hglue w.st
  dsimp only [st'] at hLft
  exact (hLft.symm.trans (hL.trans (hfold.trans (by
    simp [hmem]
    rw [← hR, hRgt]
    simp only [extra]
    have hbool (n boxN parkN : Nat) (host : InstId) :
        (if (tname host != dst) = true then n else n + boxN + parkN) =
          if tname host = dst then n + boxN + parkN else n := by
      cases hb : tname host == dst
      · have hne : ¬ tname host = dst := by simpa [beq_iff_eq] using hb
        simp [bne, hb, hne]
      · have heq : tname host = dst := by simpa [beq_iff_eq] using hb
        simp [bne, hb, heq]
    have hextra :
        (if (tname id != dst) = true then 0 else if keyPred name key msg = true then 1 else 0) =
          if tname id = dst then if keyPred name key msg = true then 1 else 0 else 0 := by
      cases hb : tname id == dst
      · have hne : (tname id != dst) = true := by simp [bne, hb]
        have hneq : ¬ tname id = dst := by simpa [beq_iff_eq] using hb
        simp [hne, hneq]
      · have hn : (tname id != dst) = false := by simp [bne, hb]
        have heq : tname id = dst := by simpa [beq_iff_eq] using hb
        simp [hn, heq]
    have hfolds := foldl_pointwise
      (fun n host => if (tname host != dst) = true then n else
        n + ((w.st host).box.filter (fun m => match m.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length +
          ((w.st host).parked.filter (fun p => match p.msg.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length)
      (fun n host => if tname host = dst then
        n + ((w.st host).box.filter (fun m => match m.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length +
          ((w.st host).parked.filter (fun p => match p.msg.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length else n)
      w.roster 0 (fun n host _ => hbool n
        ((w.st host).box.filter (fun m => match m.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length
        ((w.st host).parked.filter (fun p => match p.msg.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length host)
    rw [hextra, hfolds]
    rfl))))

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
    · intro name key d _hnone
      have hzero : queuedFromKey (initWorld I N) name key d = 0 := by
        unfold queuedFromKey
        suffices ∀ (ids : List InstId) (n : Nat),
            List.foldl (fun n host =>
              if tname host != d then n
              else n + (((initWorld I N).st host).box.filter fun m =>
                match m.sender with
                | .peer s k _ => s == name && k == key
                | .core _ => false).length +
                (((initWorld I N).st host).parked.filter fun p =>
                  match p.msg.sender with
                  | .peer s k _ => s == name && k == key
                  | .core _ => false).length) n ids = n by
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
    have h0 := owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster
      (fun id _ => init_box I N id)
    rw [h0]
    exact Nat.zero_le _
  · intro _hcrash s d hs _hdead
    rw [owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster (fun id _ => init_box I N id),
      Int.natCast_zero]
    exact Int.natCast_nonneg _
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
  · intro name k g hmem t ht _hsup _hsub _hslots
    have hcore : InstId.peer name k g ∈ coreRoster I.desc := by simpa [init_roster] using hmem
    obtain ⟨_t, _ht, _hone, hid⟩ := core_template I.desc (InstId.peer name k g) hG hcore
    cases hid

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
  · exact ixFresh_copy I.desc w (setActor w id a) hO.ixFresh rfl (fun _ => rfl)

theorem proceed_box (a : Actor) (k : Cont) : (proceed a k).box = a.box := by
  unfold proceed
  cases k.rest <;> rfl

theorem proceed_tokens (a : Actor) (k : Cont) (d : String) : (proceed a k).tokens d = a.tokens d := by
  unfold proceed
  cases k.rest <;> rfl

/-- Finishing a wait does not raise the ingress reserve. The resumed
continuation is one branch of the wait, and an empty tail lands at `toState`,
which is what the empty reserve already counted. -/
theorem tokenHold_proceed (D : Description) (template dst : String) (a : Actor) (k : Cont)
    (h : a.phase = .awaitEffect k ∨ a.phase = .awaitPeer k) :
    tokenHold D template dst (proceed a k) ≤ tokenHold D template dst a := by
  cases hk : k.rest with
  | nil =>
    rcases h with hp | hp
    · simp [proceed, tokenHold, pathReserve, contAt, hk, hp]
    · simp [proceed, tokenHold, pathReserve, contAt, hk, hp]
      exact Nat.le_max_left _ _
  | cons _ _ =>
    rcases h with hp | hp
    · simp [proceed, tokenHold, hk, hp]
    · simp [proceed, tokenHold, hk, hp]
      exact Nat.le_max_left _ _

theorem proceed_pending (a : Actor) (k : Cont) (d : String)
    (h : a.phase = .awaitEffect k ∨ a.phase = .awaitPeer k) :
    pending (proceed a k) d ≤ pending a d := by
  unfold proceed pending
  cases hk : k.rest with
  | nil =>
    rcases h with hp | hp <;> simp [contRest, hk, hp, sendsTo]
  | cons _ _ =>
    rcases h with hp | hp
    · simp [contRest, hk, hp]
    · simp [contRest, hk, hp]
      exact Nat.le_max_left _ _

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
    intro ⟨t, ht, htv, hterm, hsub⟩
    have hsubB : (t.subtree == "") = true := by simpa [beq_iff_eq] using hsub
    have hmulB : (t.multiplicity == .perPeer) = true := by
      rw [htv]
      decide
    have hb : loneTerminableB I.desc name = true := by
      simp [loneTerminableB, name, ht, hmulB, hterm, hsubB]
    rw [hb] at htermB
    cases htermB
  have hone : (1 : Int) ≤ a.tokens name := by
    have hfloor' : (gateHold I.desc name name a : Int) + 1 ≤ a.tokens name := by
      simpa [a, name] using hfloor
    omega
  have hcharge := charge_tokens a name hone
  have hmem : dst ∈ w.roster := hO.aliveIn dst hlive
  have hlife : a'.life = a.life := by simp [a', chargeSender, bumpToken]
  have hbox : a'.box = a.box ++ [msg] := by simp [a', chargeSender, bumpToken]
  have hpark : a'.parked = a.parked := by simp [a', chargeSender, bumpToken]
  have hphase : a'.phase = a.phase := by simp [a', chargeSender, bumpToken]
  have hty : a'.typestate = a.typestate := by simp [a', chargeSender, bumpToken]
  have htok (d : String) : a'.tokens d = a.tokens d - if d = name then 1 else 0 := by
    by_cases hd : d = name
    · have h := hcharge
      simp [a', hd, name] at h ⊢
      omega
    · simp [a', hd, chargeSender, bumpToken]
  have hnameB : (tname dst == name) = true := by simp [name]
  have hown (s : InstId) : owed (setActor w dst a').st name s (setActor w dst a').roster =
      owed w.st name s w.roster + if s = dst then 1 else 0 := by
    have hrost : (setActor w dst a').roster = w.roster := by simp [setActor]
    rw [hrost]
    have hmail : owed (setActor w dst a').st name s w.roster =
        owed (fun i => if i = dst then { a with box := a.box ++ [msg] } else w.st i) name s w.roster := by
      refine owed_mail_eq _ _ _ _ _ ?_
      intro i _
      by_cases hi : i = dst
      · simp [setActor, hi, hbox, hpark]
      · simp [setActor, hi]
    rw [hmail]
    by_cases hs : s = dst
    · have happ := owed_append_msg w.st name dst dst msg w.roster hO.nodup hmem hnameB rfl
      simpa [hs] using happ
    · have hne : msg.sender ≠ s := by
        intro heq
        exact hs heq.symm
      have hother := owed_append_other w.st name s dst msg w.roster hO.nodup hmem (by simp [name]) hne
      simpa [hs] using hother
  have hother (d : String) (hd : d ≠ name) (s : InstId) :
      owed (setActor w dst a').st d s (setActor w dst a').roster = owed w.st d s w.roster := by
    have hrost : (setActor w dst a').roster = w.roster := by simp [setActor]
    rw [hrost]
    have hb : (tname dst == d) = false := by simpa [beq_iff_eq, name] using hd.symm
    have hmail : owed (setActor w dst a').st d s w.roster =
        owed (fun i => if i = dst then { a with box := a.box ++ [msg] } else w.st i) d s w.roster := by
      refine owed_mail_eq _ _ _ _ _ ?_
      intro i _
      by_cases hi : i = dst
      · simp [setActor, hi, hbox, hpark]
      · simp [setActor, hi]
    rw [hmail]
    have hslot : slot (fun i => if i = dst then { a with box := a.box ++ [msg] } else w.st i) d s dst =
        slot w.st d s dst := by simp [slot, hb]
    have hrep := owed_replace w.st d s dst { a with box := a.box ++ [msg] } w.roster hO.nodup hmem
    rw [hslot] at hrep
    exact Nat.add_right_cancel hrep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hO.nodup
  · intro i hl
    have hrost : (setActor w dst a').roster = w.roster := by simp [setActor]
    rw [hrost]
    by_cases hi : i = dst
    · rw [hi] at hl ⊢
      rw [setActor_self, hlife] at hl
      exact hO.aliveIn dst hl
    · rw [setActor_other w dst i a' hi] at hl
      exact hO.aliveIn i hl
  · intro nm k g1 g2 ha hb hla hlb
    have hlife1 : ((setActor w dst a').st (InstId.peer nm k g1)).life =
        (w.st (InstId.peer nm k g1)).life := by
      by_cases hg : InstId.peer nm k g1 = dst
      · rw [hg, setActor_self, hlife]
      · rw [setActor_other w dst _ a' hg]
    have hlife2 : ((setActor w dst a').st (InstId.peer nm k g2)).life =
        (w.st (InstId.peer nm k g2)).life := by
      by_cases hg : InstId.peer nm k g2 = dst
      · rw [hg, setActor_self, hlife]
      · rw [setActor_other w dst _ a' hg]
    apply hO.indexed nm k g1 g2 (by simpa [setActor] using ha) (by simpa [setActor] using hb)
    · simpa [hlife1] using hla
    · simpa [hlife2] using hlb
  · intro template ht
    rw [aliveCount_set_life w dst a' hlife template]
    exact hO.liveOne template ht
  · intro template ht
    rw [aliveCount_set_life w dst a' hlife template]
    exact hO.livePeer template ht
  · intro i hnin
    have hrost : (setActor w dst a').roster = w.roster := by simp [setActor]
    rw [hrost] at hnin
    by_cases hi : i = dst
    · exact absurd (by simpa [hi] using hmem) hnin
    · rw [setActor_other w dst i a' hi]
      exact hO.offEmpty i (by simpa [setActor, hi] using hnin)
  · intro i m hm
    by_cases hi : i = dst
    · rw [hi, setActor_self, hbox] at hm
      simp [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hO.sentFrom dst m hm
      · have hrost : (setActor w dst a').roster = w.roster := by simp [setActor]
        rw [hrost]
        exact hmem
    · rw [setActor_other w dst i a' hi] at hm
      exact hO.sentFrom i m hm
  · intro i p hp
    by_cases hi : i = dst
    · rw [hi, setActor_self, hpark] at hp
      exact hO.parkFrom dst p hp
    · rw [setActor_other w dst i a' hi] at hp
      exact hO.parkFrom i p hp
  · intro i p hp
    by_cases hi : i = dst
    · rw [hi, setActor_self, hpark] at hp
      exact hO.parkMsg dst p hp
    · rw [setActor_other w dst i a' hi] at hp
      exact hO.parkMsg i p hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro nm k live d hfind
      have hfind0 := findLive_set_life w dst a' hlife nm k
      rw [hfind0] at hfind
      have hbal := hO.balance.1.1 nm k live d hfind
      have happ := queuedFromKey_append w dst a' msg nm k d hO.nodup hmem hbox hpark
      have hkey : peerKey live = some k ∧ tname live = nm := by
        unfold findLive at hfind
        have hp := List.find?_some hfind
        cases live with
        | core _ => simp at hp
        | peer n kk g =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          exact ⟨by simp [peerKey, hp.1.2], by simp [tname, hp.1.1]⟩
      by_cases hliveId : live = dst
      · rw [hliveId, setActor_self]
        have hpred : keyPred nm k msg = true := by
          have hpk : peerKey dst = some k := by
            have hk := hkey.1
            rwa [hliveId] at hk
          have htn0 : tname dst = nm := by
            have hn := hkey.2
            rwa [hliveId] at hn
          cases dst with
          | core _ => simp [peerKey] at hpk
          | peer n kk g =>
            simp [peerKey] at hpk
            simp [tname] at htn0
            simp [msg, keyPred, htn0, hpk]
        have htn : tname dst = nm := by
          rw [← hliveId]
          exact hkey.2
        rw [hliveId] at hbal
        by_cases hd : d = nm
        · rw [hd] at hbal ⊢ happ
          have hfalse : (tname dst != nm) = false := by simp [bne, beq_iff_eq, htn]
          have hbitq : queuedFromKey (setActor w dst a') nm k nm = queuedFromKey w nm k nm + 1 := by
            rw [happ, hfalse]
            simp [hpred]
          have hn : name = nm := by simpa [name] using htn
          have htk' : a'.tokens nm = a.tokens nm - 1 := by
            rw [← hn]
            simpa using htok name
          rw [hbitq, htk']
          have hcast : ((queuedFromKey w nm k nm + 1 : Nat) : Int) =
              (queuedFromKey w nm k nm : Int) + 1 := by simp
          rw [hcast]
          have hsub : a.tokens nm - 1 + ((queuedFromKey w nm k nm : Int) + 1) =
              a.tokens nm + (queuedFromKey w nm k nm : Int) := by omega
          rw [hsub]
          exact hbal
        · have hneq : tname dst ≠ d := by
            intro heq
            exact hd (heq.symm.trans htn)
          have ht : (tname dst != d) = true := by simpa [bne, beq_iff_eq] using hneq
          have htk := htok d
          have hname : d ≠ name := by
            intro heq
            have hn : name = nm := by simpa [name] using htn
            exact hd (heq.trans hn)
          simp [ht, hname] at happ htk
          rw [happ, htk]
          exact hbal
      · rw [setActor_other w dst live a' hliveId]
        have hbit : (if (tname dst != d) = true then 0 else if keyPred nm k msg = true then 1 else 0) = 0 := by
          by_cases ht : (tname dst != d) = true
          · simp [ht]
          · have hf : (tname dst != d) = false := by
              cases hbb : tname dst != d with
              | false => rfl
              | true => exact absurd hbb ht
            simp only [ht, hf, Bool.false_eq_true, ite_false]
            by_cases hp : keyPred nm k msg = true
            · exfalso
              unfold keyPred at hp
              cases hsender : msg.sender with
              | core _ => simp [hsender, keyPred] at hp
              | peer n kk g =>
                simp only [hsender, Bool.and_eq_true, beq_iff_eq] at hp
                have hdst : dst = InstId.peer n kk g := by simpa [msg] using hsender
                have hfound := findLive_of_alive w hO.indexed n kk g
                  (by simpa [hdst] using hmem) (by simpa [hdst] using hlive)
                have hsame : findLive w nm k = some dst := by
                  simpa [hdst, hp.1, hp.2] using hfound
                have heq : dst = live := by
                  rw [hsame] at hfind
                  injection hfind
                exact hliveId heq.symm
            · simp [hp]
        rw [happ, hbit, Nat.add_zero]
        exact hbal
    · intro nm d hl hmemC
      have hl0 : (w.st (.core nm)).life = .alive := by
        by_cases hc : InstId.core nm = dst
        · rw [hc] at hl ⊢
          rw [setActor_self, hlife] at hl
          exact hl
        · rw [setActor_other w dst _ a' hc] at hl
          exact hl
      have hmem0 : InstId.core nm ∈ w.roster := by simpa [setActor] using hmemC
      have hbal := hO.balance.1.2 nm d hl0 hmem0
      by_cases hc : InstId.core nm = dst
      · rw [hc, setActor_self]
        rw [hc] at hbal
        by_cases hd : d = name
        · rw [hd] at hbal ⊢
          have hown' : owed (setActor w dst a').st name dst (setActor w dst a').roster =
              owed w.st name dst w.roster + 1 := by
            simpa using hown dst
          have htk : a'.tokens name = a.tokens name - 1 := by simpa using htok name
          rw [hown', htk]
          have hcast : ((owed w.st name dst w.roster + 1 : Nat) : Int) =
              (owed w.st name dst w.roster : Int) + 1 := by simp
          rw [hcast]
          have hsub : a.tokens name - 1 + ((owed w.st name dst w.roster : Int) + 1) =
              a.tokens name + (owed w.st name dst w.roster : Int) := by omega
          rw [hsub]
          exact hbal
        · have hoth := hother d hd dst
          have htk := htok d
          simp [hd] at htk
          rw [hoth, htk]
          exact hbal
      · rw [setActor_other w dst _ a' hc]
        have howed : owed (setActor w dst a').st d (.core nm) (setActor w dst a').roster =
            owed w.st d (.core nm) w.roster := by
          by_cases hd : d = name
          · rw [hd]
            have hown' := hown (.core nm)
            have hne : InstId.core nm ≠ dst := hc
            simp [hne, Nat.add_zero] at hown'
            exact hown'
          · exact hother d hd (.core nm)
        rw [howed]
        exact hbal
    · intro nm k d hnone
      have hnone0 : findLive w nm k = none := by
        have hback := findLive_set_life w dst a' hlife nm k
        exact hback.symm.trans hnone
      have hbal := hO.balance.2 nm k d hnone0
      have happ := queuedFromKey_append w dst a' msg nm k d hO.nodup hmem hbox hpark
      have hbit : (if (tname dst != d) = true then 0 else if keyPred nm k msg = true then 1 else 0) = 0 := by
        by_cases ht : (tname dst != d) = true
        · simp [ht]
        · have hf : (tname dst != d) = false := by
            cases hbb : tname dst != d with
            | false => rfl
            | true => exact absurd hbb ht
          simp only [ht, hf, Bool.false_eq_true, ite_false]
          by_cases hp : keyPred nm k msg = true
          · exfalso
            cases hsender : msg.sender with
            | core _ => simp [keyPred, hsender] at hp
            | peer n kk g =>
              simp only [keyPred, hsender, Bool.and_eq_true, beq_iff_eq] at hp
              have hdst : dst = InstId.peer n kk g := by simpa [msg] using hsender
              have hfound := findLive_of_alive w hO.indexed n kk g
                (by simpa [hdst] using hmem) (by simpa [hdst] using hlive)
              have hsame : findLive w nm k = some dst := by
                simpa [hdst, hp.1, hp.2] using hfound
              simp [hsame] at hnone0
          · simp [hp]
      rw [happ, hbit, Nat.add_zero]
      exact hbal
  · intro s d hl
    by_cases hs : s = dst
    · rw [hs, setActor_self] at hl ⊢
      have hhold : tokenHold I.desc name d a' = tokenHold I.desc name d a := by
        cases hp : a.phase <;> simp [a', tokenHold, chargeSender, bumpToken, hphase, hty, hp, a]
      rw [hhold]
      by_cases hd : d = name
      · rw [hd]
        have htk := htok name
        simp [hd] at htk
        have hfloor' : (gateHold I.desc name name a : Int) + 1 ≤ a.tokens name := by
          simpa [a, name] using hfloor
        have hle : (tokenHold I.desc name name a : Int) ≤ gateHold I.desc name name a :=
          Int.ofNat_le.mpr (tokenHold_le_gate I.desc name name a)
        omega
      · have htk := htok d
        simp [hd] at htk
        have hold := hO.slack dst d hlive
        rw [htk]
        exact hold
    · rw [setActor_other w dst s a' hs] at hl ⊢
      exact hO.slack s d hl
  · intro s d hs hterm
    by_cases hsnd : s = dst
    · exact absurd (by simpa [hsnd, name] using hterm) hnot
    · have h0 := hO.still s d hs hterm
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hsnd, Nat.add_zero] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s]
        exact h0
  · intro hcrash s d hs hdead
    have hc : w.crashed = false := by simpa [setActor] using hcrash
    by_cases hsnd : s = dst
    · rw [hsnd, setActor_self, hlife] at hdead
      exact absurd hlive hdead
    · have hdead0 : (w.st s).life ≠ .alive := by
        rw [setActor_other w dst s a' hsnd] at hdead
        exact hdead
      have hs0 : s ∈ w.roster := by simpa [setActor] using hs
      have h0 := hO.quiet hc s d hs0 hdead0
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hsnd, Nat.add_zero] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s]
        exact h0
  · intro hcrash i hdead
    have hc : w.crashed = false := by simpa [setActor] using hcrash
    by_cases hi : i = dst
    · rw [hi, setActor_self, hlife] at hdead
      rcases hdead with hdead | hdead
      · rw [hdead] at hlive
        cases hlive
      · rw [hdead] at hlive
        cases hlive
    · rw [setActor_other w dst i a' hi] at hdead ⊢
      exact hO.deadEmpty hc i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = dst
      · rw [hh] at hm ⊢
        rw [setActor_self, hbox] at hm
        simp [List.mem_append, List.mem_singleton] at hm
        unfold queueOk
        rcases hm with hm | rfl
        · exact (hO.sameKey dst).1 m hm
        · exact key_refl I.desc dst
      · rw [setActor_other w dst host a' hh] at hm
        unfold queueOk
        exact (hO.sameKey host).1 m hm
    · intro p hp
      by_cases hh : host = dst
      · rw [hh] at hp ⊢
        rw [setActor_self, hpark] at hp
        unfold queueOk
        exact (hO.sameKey dst).2 p hp
      · rw [setActor_other w dst host a' hh] at hp
        unfold queueOk
        exact (hO.sameKey host).2 p hp
  · intro i hi
    exact hO.shaped i (by simpa [setActor] using hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = dst
      · rw [hh] at hm hk
        rw [setActor_self, hbox] at hm
        simp [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact (hO.coreFrom dst hk).1 m hm
        · exact Or.inl (by simpa [msg] using hk)
      · rw [setActor_other w dst host a' hh] at hm
        exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      by_cases hh : host = dst
      · rw [hh] at hp hk
        rw [setActor_self, hpark] at hp
        exact (hO.coreFrom dst hk).2 p hp
      · rw [setActor_other w dst host a' hh] at hp
        exact (hO.coreFrom host hk).2 p hp
  · exact ixFresh_copy I.desc w (setActor w dst a') hO.ixFresh rfl (fun _ => rfl)


/-- `finish` only advances a wait. The typestate is already the continuation's
target, and the remaining sends do not grow. -/
theorem occ_finish (I : Impl) (w w' : World) (id : InstId) (hO : OccInv I w) (_hS : SemInv I w)
    (h : finishWait I w id = some w') : OccInv I w' := by
  cases hph : (w.st id).phase with
  | awaitEffect k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    cases hw
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hold := hO.slack id d (by rw [proceed_life] at hl; exact hl)
        have hle := tokenHold_proceed I.desc (tname id) d (w.st id) k (Or.inl hph)
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Int.le_trans (Int.ofNat_le.mpr (by simpa [a] using hle)) hold)
  | awaitPeer k =>
    simp [finishWait, hph] at h
    rcases h with ⟨_, hw⟩
    cases hw
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hold := hO.slack id d (by rw [proceed_life] at hl; exact hl)
        have hle := tokenHold_proceed I.desc (tname id) d (w.st id) k (Or.inr hph)
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Int.le_trans (Int.ofNat_le.mpr (by simpa [a] using hle)) hold)
  | idle => simp [finishWait, hph] at h
  | run _ => simp [finishWait, hph] at h
  | parked _ _ _ => simp [finishWait, hph] at h
  | awaitReply _ _ => simp [finishWait, hph] at h
  | crashed => simp [finishWait, hph] at h

theorem occ_same (I : Impl) (w w' : World) (hO : OccInv I w) (hst : ∀ i, w'.st i = w.st i)
    (hr : w'.roster = w.roster) (hN : w'.N = w.N) (_hix : ∀ n, w'.nextIx n = w.nextIx n)
    (hcr : w'.crashed = w.crashed) : OccInv I w' := by
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
  · intro nm k g1 g2 ha hb hla hlb
    apply hO.indexed nm k g1 g2 (by rw [hr] at ha; exact ha) (by rw [hr] at hb; exact hb)
    · simpa [hst] using hla
    · simpa [hst] using hlb
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
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro nm k live d hfind
      have hfind0 : findLive w nm k = some live := by
        simpa [findLive, hr, hst] using hfind
      have hbal := hO.balance.1.1 nm k live d hfind0
      have htok : (w'.st live).tokens d = (w.st live).tokens d := by simp [hst]
      have hqk : queuedFromKey w' nm k d = queuedFromKey w nm k d := by
        simp [queuedFromKey, hr, hst]
      rw [htok, hqk]
      exact hbal
    · intro nm d hl hmem
      have hl0 : (w.st (.core nm)).life = .alive := by simpa [hst] using hl
      have hmem0 : InstId.core nm ∈ w.roster := by rw [← hr]; exact hmem
      have hbal := hO.balance.1.2 nm d hl0 hmem0
      have htok : (w'.st (.core nm)).tokens d = (w.st (.core nm)).tokens d := by simp [hst]
      have howed := owed_mail_eq w'.st w.st d (.core nm) w'.roster hq
      rw [htok, howed, hr]
      exact hbal
    · intro nm k d hnone
      have hnone0 : findLive w nm k = none := by
        simpa [findLive, hr, hst] using hnone
      have hbal := hO.balance.2 nm k d hnone0
      have hqk : queuedFromKey w' nm k d = queuedFromKey w nm k d := by
        simp [queuedFromKey, hr, hst]
      rw [hqk]
      exact hbal
  · intro s d hl
    rw [hst] at hl ⊢
    exact hO.slack s d hl
  · intro s d hs hterm
    have howed := owed_mail_eq w'.st w.st d s w'.roster hq
    rw [howed, hr]
    exact hO.still s d (by rw [← hr]; exact hs) hterm
  · intro hcrash s d hs hdead
    have hc : w.crashed = false := hcr.symm.trans hcrash
    have howed := owed_mail_eq w'.st w.st d s w'.roster hq
    have hdead0 : (w.st s).life ≠ .alive := by simpa [hst] using hdead
    rw [howed, hr]
    exact hO.quiet hc s d (by rw [← hr]; exact hs) hdead0
  · intro hcrash i hdead
    have hc : w.crashed = false := hcr.symm.trans hcrash
    rw [hst] at hdead ⊢
    exact hO.deadEmpty hc i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hst] at hm
      unfold queueOk
      exact (hO.sameKey host).1 m hm
    · intro p hp
      rw [hst] at hp
      unfold queueOk
      exact (hO.sameKey host).2 p hp
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
  · exact ixFresh_copy I.desc w w' hO.ixFresh hr _hix


theorem deliver_base (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1 = readCells I.desc w id := by
  simp only [deliver] at h
  split at h
  · cases h
  · split at h
    · cases h
      rfl
    · split at h
      · split at h
        · cases h
        · cases h
          rfl
      · split at h
        · cases h
        · cases h
          rfl

theorem deliver_roster (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1.roster = w.roster := by
  rw [deliver_base I w id a m w1 a1 h]
  exact readCells_roster I.desc w id

theorem deliver_N (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1.N = w.N := by
  rw [deliver_base I w id a m w1 a1 h]
  exact readCells_N I.desc w id

theorem deliver_crashed (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg) (w1 : World)
    (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) : w1.crashed = w.crashed := by
  rw [deliver_base I w id a m w1 a1 h]
  exact readCells_crashed I.desc w id

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
    sendsOk I.desc tr.template tr = true ∧
      effectsOk I.desc tr.template (branchAt tr) tr.program = true := by
  have hok := transitionOk_of_mem I hL tr hm
  unfold transitionOk at hok
  cases ht : templateOf I.desc tr.template with
  | none => simp [ht] at hok
  | some _ =>
    simp only [transitionOk, ht, Bool.and_eq_true] at hok
    exact ⟨hok.1.1.1.1.1.1.2, hok.1.1.1.1.1.2⟩

theorem reserve_named (D : Description) (tr : Transition) (dst : String) (t : Template)
    (h : sendsOk D tr.template tr = true) (ht : templateOf D dst = some t) :
    pathReserve D tr.template dst (branchAt tr) tr.program ≤
      floorState D tr.template tr.fromState dst := by
  have hname := templateOf_name D dst t ht
  unfold sendsOk at h
  have hmem := template_mem D dst t ht
  have hall := (List.all_eq_true _ _).mp h t hmem
  simpa [hname] using hall

private def nestSize : List Eff → Nat
  | [] => 0
  | .trySend _ _ _ f g :: es => 1 + nestSize f + nestSize g + nestSize es
  | .call _ _ _ a b :: es => 1 + nestSize a + nestSize b + nestSize es
  | .peer o :: es => 1 + nestSize o + nestSize es
  | _ :: es => 1 + nestSize es

theorem pathReserve_unknown (D : Description) (hG : GraphOk D) (template dst : String)
    (at_ : BranchAt) (es : List Eff) (hok : effectsOk D template at_ es = true)
    (hdst : templateOf D dst = none) : pathReserve D template dst at_ es = 0 := by
  match es with
  | [] =>
    simpa [pathReserve, landFloor, floorState] using floor_unknown D hG template at_.here dst hdst
  | .send d label n :: es =>
    obtain ⟨hedge, htail⟩ := head_send D template d label at_ n es hok
    obtain ⟨edge, he, _, _, hd, _, _, _⟩ :=
      hasEdge_mem D template at_.here d .send .blocking label hedge
    have hne : d ≠ dst := fun heq => no_edge_unknown D hG dst hdst edge he (heq ▸ hd)
    have hb : (d == dst) = false := by
      cases hbb : d == dst with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hne
    have htail0 := pathReserve_unknown D hG template dst at_ es htail hdst
    simp [pathReserve, effReserve, hb, htail0]
  | .trySend d label n onFull onGone :: es =>
    have hsplit := by
      simp only [effectsOk, effectOk, Bool.and_eq_true] at hok
      exact hok
    obtain ⟨edge, he, _, _, hd, _, _, _⟩ :=
      hasEdge_mem D template at_.here d .trySend .nonBlocking label hsplit.1.1.1.1
    have hne : d ≠ dst := fun heq => no_edge_unknown D hG dst hdst edge he (heq ▸ hd)
    have hb : (d == dst) = false := by
      cases hbb : d == dst with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hne
    have hfull0 := pathReserve_unknown D hG template dst (focus at_ at_.full) onFull hsplit.1.1.2 hdst
    have hgone0 := pathReserve_unknown D hG template dst (focus at_ at_.gone) onGone hsplit.1.2 hdst
    have htail0 := pathReserve_unknown D hG template dst at_ es hsplit.2 hdst
    simp [pathReserve, effReserve, hb, hfull0, hgone0, htail0]
  | .call d label n onNotAdmitted onTimedOut :: es =>
    obtain ⟨hedge, hna, hto, htail⟩ := head_call D template d label at_ n onNotAdmitted onTimedOut es hok
    obtain ⟨edge, he, _, _, hd, _, _, _⟩ :=
      hasEdge_mem D template at_.here d .call .blocking label hedge
    have hne : d ≠ dst := fun heq => no_edge_unknown D hG dst hdst edge he (heq ▸ hd)
    have hb : (d == dst) = false := by
      cases hbb : d == dst with
      | false => rfl
      | true => exact absurd ((beq_iff_eq).mp hbb) hne
    have hna0 :=
      pathReserve_unknown D hG template dst (focus at_ at_.notAdmitted) onNotAdmitted hna hdst
    have hto0 := pathReserve_unknown D hG template dst (focus at_ at_.timedOut) onTimedOut hto hdst
    have htail0 := pathReserve_unknown D hG template dst at_ es htail hdst
    simp [pathReserve, effReserve, hb, hna0, hto0, htail0]
  | .peer onTimeout :: es =>
    obtain ⟨hto, htail⟩ := head_peer D template at_ onTimeout es hok
    have hto0 := pathReserve_unknown D hG template dst (focus at_ at_.timeout) onTimeout hto hdst
    have htail0 := pathReserve_unknown D hG template dst at_ es htail hdst
    simp [pathReserve, effReserve, hto0, htail0]
  | .cell d label value :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ (.cell d label value) es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .reply :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ .reply es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .selfSchedule label :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ (.selfSchedule label) es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .internal :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ .internal es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .abort :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ .abort es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .terminate :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ .terminate es hok) hdst
    simp [pathReserve, effReserve, htail0]
  | .spawn child :: es =>
    have htail0 := pathReserve_unknown D hG template dst at_ es
      (head_rest D template at_ (.spawn child) es hok) hdst
    simp [pathReserve, effReserve, htail0]
termination_by nestSize es
decreasing_by
  all_goals simp [nestSize]
  all_goals omega

theorem reserve_le (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (tr : Transition)
    (hm : tr ∈ I.transitions) (dst : String) :
    pathReserve I.desc tr.template dst (branchAt tr) tr.program ≤
      floorState I.desc tr.template tr.fromState dst := by
  obtain ⟨hs, he⟩ := tr_prog I hL tr hm
  cases ht : templateOf I.desc dst with
  | some t => exact reserve_named I.desc tr dst t hs ht
  | none =>
    have hz := pathReserve_unknown I.desc hG tr.template dst (branchAt tr) tr.program he ht
    have hfrom := floor_unknown I.desc hG tr.template tr.fromState dst ht
    simp [hz, hfrom]

theorem deliver_account (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (a : Actor) (m : Msg) (w1 : World) (a1 : Actor) (halive : a.life = .alive) (hph : a.phase = .idle)
    (h : deliver I w id a m = some (w1, a1)) :
    a1.life = a.life ∧ a1.box = a.box ∧ a1.parked = a.parked ∧ (∀ d, a1.tokens d = a.tokens d) ∧
      ∀ d, tokenHold I.desc (tname id) d a1 ≤ tokenHold I.desc (tname id) d a := by
  unfold deliver at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · injection h with hpair
      cases hpair
      refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_⟩
      intro d
      simp [tokenHold, hph]
    · split at h
      · split at h
        · cases h
        · injection h with hpair
          cases hpair
          refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_⟩
          intro d
          simp [tokenHold, hph]
      · split at h
        · cases h
        · rename_i tr hfind _
          injection h with hpair
          cases hpair
          have hmem := findDeliver_mem I (tname id) a.typestate m tr hfind
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · cases hp : tr.program.isEmpty <;> simp [hp]
          · cases hp : tr.program.isEmpty <;> simp [hp]
          · cases hp : tr.program.isEmpty <;> simp [hp]
          · intro d
            cases hp : tr.program.isEmpty <;> simp [hp]
          · intro d
            have hres := reserve_le I hL hG tr hmem.1 d
            rw [hmem.2.1, hmem.2.2] at hres
            cases hp : tr.program.isEmpty with
            | true =>
              have hempty : tr.program = [] := list_isEmpty_nil _ hp
              simp [tokenHold, hph, pathReserve, branchAt, contAt, landFloor, floorState, hempty] at hres ⊢
              exact hres
            | false =>
              simp [tokenHold, hph, pathReserve, branchAt, contAt, landFloor, floorState, hp] at hres ⊢
              exact hres

theorem occ_prio (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId) (w' : World)
    (hO : OccInv I w) (h : receivePrio I w id = some w') : OccInv I w' := by
  obtain ⟨m, pre, suf, w1, a1, hlife, hidle, _hprio, _hwait, hdel, hw'⟩ :=
    receivePrio_spec I w w' id h
  let a0 : Actor := { (w.st id) with prio := pre ++ suf }
  have hacc := deliver_account I hL hG w id a0 m w1 a1 hlife (by simp [a0, hidle]) hdel
  obtain ⟨hl, hbox, hpark, htok, hhold⟩ := hacc
  have hO1 := occ_same I w w1 hO (fun i => deliver_st I w id a0 m w1 a1 i hdel)
    (deliver_roster I w id a0 m w1 a1 hdel) (deliver_N I w id a0 m w1 a1 hdel)
    (fun n => by
      rw [deliver_base I w id a0 m w1 a1 hdel]
      exact readCells_nextIx I.desc w id n)
    (deliver_crashed I w id a0 m w1 a1 hdel)
  rw [hw']
  exact occ_set I w1 id a1 hO1
    (by rw [deliver_st I w id a0 m w1 a1 id hdel, hl])
    (by rw [deliver_st I w id a0 m w1 a1 id hdel, hbox])
    (by rw [deliver_st I w id a0 m w1 a1 id hdel, hpark])
    (by
      intro d
      rw [deliver_st I w id a0 m w1 a1 id hdel, htok d])
    (by
      intro d _hlive
      have hold := hO.slack id d hlife
      have htok0 : a0.tokens d = (w.st id).tokens d := by simp [a0]
      have hsame : tokenHold I.desc (tname id) d a0 = tokenHold I.desc (tname id) d (w.st id) := by
        simp [tokenHold, a0, hidle]
      have hstep : (tokenHold I.desc (tname id) d a1 : Int) ≤ tokenHold I.desc (tname id) d a0 :=
        Int.ofNat_le.mpr (hhold d)
      rw [hsame] at hstep
      rw [htok d, htok0]
      exact Int.le_trans hstep hold)

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

/-- One, when `sender` is a generation of `name` at `key`. A core drops nothing
from a per-peer queue. -/
def keyDrop (sender : InstId) (name : String) (key : Nat) : Int :=
  match sender with
  | .peer n k _ => if n = name ∧ k = key then 1 else 0
  | .core _ => 0

/-- The queue change at destination `dst` when one message from `sender` leaves
a host of template `d`. -/
def queueDrop (sender : InstId) (name : String) (key : Nat) (d dst : String) : Int :=
  if d = dst then keyDrop sender name key else 0

theorem findLive_life (w w' : World) (hr : w'.roster = w.roster)
    (hl : ∀ i, (w'.st i).life = (w.st i).life) (name : String) (key : Nat) :
    findLive w' name key = findLive w name key := by
  unfold findLive
  rw [hr]
  congr 1
  funext i
  cases i with
  | core _ => rfl
  | peer _ _ _ => simp [hl]

theorem findLive_copy (w w' : World) (hr : w'.roster = w.roster) (hst : ∀ i, w'.st i = w.st i)
    (name : String) (key : Nat) : findLive w' name key = findLive w name key := by
  unfold findLive
  simp only [hr]
  congr 1
  funext i
  cases i <;> simp [hst]

/-- The token returned to the live holder is the message that left the key's queue. -/
theorem credit_matches_drop (w : World) (sender live : InstId) (name : String) (key : Nat)
    (d dst : String) (hfind : findLive w name key = some live) :
    (if live = budgetHolder w sender then if d = dst then (1 : Int) else 0 else 0) =
      queueDrop sender name key d dst := by
  cases sender with
  | core c =>
    have hne : live ≠ InstId.core c := findLive_not_core w name key live hfind c
    unfold budgetHolder queueDrop keyDrop
    have hif : (if live = InstId.core c then if d = dst then (1 : Int) else 0 else 0) = 0 := by
      by_cases h : live = InstId.core c
      · exact absurd h hne
      · simp [h]
    rw [hif]
    by_cases hd : d = dst <;> simp [hd]
  | peer n k g =>
    by_cases hkey : n = name ∧ k = key
    · rcases hkey with ⟨hn, hk⟩
      subst hn
      subst hk
      simp [budgetHolder, queueDrop, keyDrop, hfind]
    · have hne : live ≠ budgetHolder w (InstId.peer n k g) := by
        intro heq
        simp only [budgetHolder] at heq
        cases hfl : findLive w n k with
        | some idf =>
          rw [hfl] at heq
          obtain ⟨_g1, hid⟩ := findLive_peer w n k idf hfl
          obtain ⟨_g2, hl⟩ := findLive_peer w name key live hfind
          rw [hid, hl] at heq
          injection heq with hn hk
          exact hkey ⟨hn.symm, hk.symm⟩
        | none =>
          rw [hfl] at heq
          obtain ⟨_g2, hl⟩ := findLive_peer w name key live hfind
          rw [hl] at heq
          injection heq with hn hk
          exact hkey ⟨hn.symm, hk.symm⟩
      unfold budgetHolder queueDrop keyDrop
      have hif : (if live = budgetHolder w (InstId.peer n k g) then if d = dst then (1 : Int) else 0 else 0) = 0 := by
        by_cases h : live = budgetHolder w (InstId.peer n k g)
        · exact absurd h hne
        · simp [h]
      rw [hif]
      by_cases hd : d = dst <;> simp [hd, hkey]

theorem queuedFromKey_credit (w : World) (dst : String) (s : InstId) (name : String) (key : Nat)
    (d : String) :
    queuedFromKey (creditSender w dst s) name key d = queuedFromKey w name key d := by
  unfold queuedFromKey
  simp only [creditSender, setActor]
  refine foldl_pointwise _ _ w.roster 0 ?_
  intro n host _
  by_cases hh : host = s
  · simp [hh, bumpToken]
  · simp [hh]

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
      rw [hid, setActor_self, htok, ite_eq_right hne, Int.add_zero]
    · rw [setActor_other w1 id s a1 hid, hst, ite_eq_right hs, Int.add_zero]

/-- Install `a1` for `id` and return one token to the live holder of `sender`'s
key. `a1` keeps life. At `tname id` it owes `sender` one message less; every
other account is unchanged. The new `tokenHold` fits in the old one. -/
theorem occ_consume (I : Impl) (w w1 : World) (id sender : InstId) (a1 : Actor) (hO : OccInv I w)
    (hst : ∀ i, w1.st i = w.st i) (hr : w1.roster = w.roster) (hN : w1.N = w.N)
    (hix : ∀ n, w1.nextIx n = w.nextIx n) (hcr : w1.crashed = w.crashed)
    (hlife : a1.life = (w.st id).life)
    (htok : ∀ d, a1.tokens d = (w.st id).tokens d) (hmem : id ∈ w.roster) (hsend : sender ∈ w.roster)
    (hown : ∀ s, owed (fun i => if i = id then a1 else w.st i) (tname id) s w.roster +
        (if s = sender then 1 else 0) = owed w.st (tname id) s w.roster)
    (hother : ∀ d, d ≠ tname id → ∀ s,
      owed (fun i => if i = id then a1 else w.st i) d s w.roster = owed w.st d s w.roster)
    (hq : ∀ name key d,
      (queuedFromKey (setActor w1 id a1) name key d : Int) =
        (queuedFromKey w name key d : Int) - queueDrop sender name key d (tname id))
    (hhold : ∀ d, tokenHold I.desc (tname id) d a1 ≤ tokenHold I.desc (tname id) d (w.st id))
    (hboxFrom : ∀ m ∈ a1.box, m.sender ∈ w.roster)
    (hparkFrom : ∀ p ∈ a1.parked, p.sender ∈ w.roster)
    (hparkMsg : ∀ p ∈ a1.parked, p.sender = p.msg.sender)
    (hkeyB : ∀ m ∈ a1.box, queueOk I.desc w m.sender id)
    (hkeyP : ∀ p ∈ a1.parked, queueOk I.desc w p.sender id)
    (hdeadQ : a1.life ≠ .alive → a1.box = [] ∧ a1.parked = [])
    (hfromB : peerKey id = none → ∀ m ∈ a1.box, coreSender I.desc m.sender)
    (hfromP : peerKey id = none → ∀ p ∈ a1.parked, coreSender I.desc p.sender) :
    OccInv I (creditLive (setActor w1 id a1) (tname id) sender) := by
  let wA := setActor w1 id a1
  let holder := budgetHolder wA sender
  let wF := creditLive wA (tname id) sender
  suffices OccInv I wF by simpa [wF] using this
  have hrost : wF.roster = w.roster := by simp [wF, wA, creditLive, creditSender, setActor, hr]
  have hNf : wF.N = w.N := by simp [wF, wA, creditLive, creditSender, setActor, hN]
  have hixf : ∀ n, wF.nextIx n = w.nextIx n := by
    intro n; simp [wF, wA, creditLive, creditSender, setActor, hix]
  have hlifeF : ∀ s, (wF.st s).life = (w.st s).life := by
    intro s
    rw [consume_pick (·.life) (by intro a tmpl; simp [bumpToken]) w w1 id holder a1 s hst]
    by_cases hid : s = id <;> simp [hid, hlife]
  have hboxF : ∀ s, (wF.st s).box = if s = id then a1.box else (w.st s).box :=
    fun s => consume_pick (·.box) (by intro a tmpl; simp [bumpToken]) w w1 id holder a1 s hst
  have hparkF : ∀ s, (wF.st s).parked = if s = id then a1.parked else (w.st s).parked :=
    fun s => consume_pick (·.parked) (by intro a tmpl; simp [bumpToken]) w w1 id holder a1 s hst
  have htyF : ∀ s, (wF.st s).typestate = if s = id then a1.typestate else (w.st s).typestate :=
    fun s => consume_pick (·.typestate) (by intro a tmpl; simp [bumpToken]) w w1 id holder a1 s hst
  have hphF : ∀ s, (wF.st s).phase = if s = id then a1.phase else (w.st s).phase :=
    fun s => consume_pick (·.phase) (by intro a tmpl; simp [bumpToken]) w w1 id holder a1 s hst
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
    have hcred := owed_bump wA.st holder (tname id) d s w.roster
    simp only [wF, wA, holder, creditLive, creditSender, setActor]
    exact hcred.trans hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrost]; exact hO.nodup
  · intro s hl
    rw [hlifeF] at hl
    rw [hrost]
    exact hO.aliveIn s hl
  · intro nm k g1 g2 ha hb hla hlb
    apply hO.indexed nm k g1 g2 (by rw [hrost] at ha; exact ha) (by rw [hrost] at hb; exact hb)
    · simpa [hlifeF] using hla
    · simpa [hlifeF] using hlb
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
    rw [hboxF, hparkF]
    simp [hne]
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
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key live d hfind
      have hfind0 : findLive w name key = some live := by
        simpa [findLive, hrost, hlifeF] using hfind
      have hlife1 : a1.life = (w1.st id).life := by rw [hst]; exact hlife
      have hfindA : findLive wA name key = findLive w name key :=
        (findLive_set_life w1 id a1 hlife1 name key).trans (findLive_copy w w1 hr hst name key)
      have hbal := hO.balance.1.1 name key live d hfind0
      have htokRaw := consume_tokens w w1 id holder a1 live d hst htok
      have htokF : (wF.st live).tokens d =
          (w.st live).tokens d + if live = holder then if d = tname id then 1 else 0 else 0 := by
        simpa [wF, wA, creditLive, holder] using htokRaw
      have hqF : (queuedFromKey wF name key d : Int) = (queuedFromKey wA name key d : Int) := by
        simpa [wF, wA, creditLive, holder] using
          congrArg Int.ofNat (queuedFromKey_credit wA (tname id) holder name key d)
      have hbit := credit_matches_drop w sender live name key d (tname id) hfind0
      have hholdB : holder = budgetHolder w sender := by
        cases sender with
        | core _ => simp [holder, budgetHolder]
        | peer n k _ =>
          simp only [holder, budgetHolder]
          have hcopy : findLive wA n k = findLive w n k :=
            (findLive_set_life w1 id a1 hlife1 n k).trans (findLive_copy w w1 hr hst n k)
          rw [hcopy]
      rw [htokF, hqF, hq, hholdB, hbit]
      omega
    · intro name d hl hmemc
      have hl0 : (w.st (InstId.core name)).life = .alive := by simpa [hlifeF] using hl
      have hmem0 : InstId.core name ∈ w.roster := by
        rw [hrost] at hmemc
        exact hmemc
      have hbal := hO.balance.1.2 name d hl0 hmem0
      have htokRaw := consume_tokens w w1 id holder a1 (InstId.core name) d hst htok
      have htokF : (wF.st (InstId.core name)).tokens d =
          (w.st (InstId.core name)).tokens d +
            if InstId.core name = holder then if d = tname id then 1 else 0 else 0 := by
        simpa [wF, wA, creditLive, holder] using htokRaw
      have how := howed d (InstId.core name)
      cases sender with
      | peer n k g =>
        have hne : InstId.core name ≠ holder := by
          intro heq
          simp only [holder, budgetHolder] at heq
          cases hfl : findLive wA n k with
          | some idf =>
            rw [hfl] at heq
            obtain ⟨_, hid⟩ := findLive_peer wA n k idf hfl
            rw [hid] at heq
            cases heq
          | none =>
            rw [hfl] at heq
            cases heq
        rw [hrost]
        rw [htokF, how]
        simp [hne]
        by_cases hd : d = tname id
        · rw [hd] at hbal ⊢
          have hown' := hown (InstId.core name)
          simp at hown'
          rw [hown']
          exact hbal
        · rw [hother d hd]
          exact hbal
      | core c =>
        by_cases hc : c = name
        · have hholdEq : holder = InstId.core c := by simp [holder, budgetHolder]
          rw [hc] at hholdEq hown
          rw [hrost]
          rw [htokF, how, hholdEq]
          simp
          by_cases hd : d = tname id
          · rw [hd] at hbal ⊢
            simp
            have hown' := hown (InstId.core name)
            simp at hown'
            rw [← hown'] at hbal
            rw [Int.natCast_add] at hbal
            omega
          · rw [hother d hd]
            simp [hd]
            exact hbal
        · have hne : InstId.core name ≠ holder := by
            intro heq
            simp only [holder, budgetHolder] at heq
            injection heq with hc'
            exact hc hc'.symm
          rw [hrost]
          rw [htokF, how]
          simp [hne]
          by_cases hd : d = tname id
          · rw [hd] at hbal ⊢
            have hneq : InstId.core name ≠ InstId.core c := by
              intro heq
              injection heq with hn
              exact hc hn.symm
            have hown' := hown (InstId.core name)
            simp [hneq] at hown'
            rw [hown']
            exact hbal
          · rw [hother d hd]
            exact hbal
    · intro name key d hnone
      have hnone0 : findLive w name key = none := by
        simpa [findLive, hrost, hlifeF] using hnone
      have hbal := hO.balance.2 name key d hnone0
      have hqF : (queuedFromKey wF name key d : Int) = (queuedFromKey wA name key d : Int) := by
        simpa [wF, wA, creditLive, holder] using
          congrArg Int.ofNat (queuedFromKey_credit wA (tname id) holder name key d)
      rw [hqF, hq]
      have hdrop : (0 : Int) ≤ queueDrop sender name key d (tname id) := by
        unfold queueDrop keyDrop
        by_cases hd : d = tname id
        · simp [hd]
          cases sender with
          | core _ => simp
          | peer n k _ =>
            by_cases hkey : n = name ∧ k = key <;> simp [hkey]
        · simp [hd]
      omega
  · intro s d hl
    have hl0 : (w.st s).life = .alive := by simpa [hlifeF] using hl
    have hold := hO.slack s d hl0
    have htokRaw := consume_tokens w w1 id holder a1 s d hst htok
    have htokF : (wF.st s).tokens d =
        (w.st s).tokens d + if s = holder then if d = tname id then 1 else 0 else 0 := by
      simpa [wF, wA, creditLive, holder] using htokRaw
    have hge : (w.st s).tokens d ≤
        (w.st s).tokens d + if s = holder then if d = tname id then 1 else 0 else 0 := by
      by_cases hs : s = holder <;> by_cases hd : d = tname id <;> simp [hs, hd] <;> omega
    by_cases hid : s = id
    · have hph : (wF.st id).phase = a1.phase := by rw [hphF]; simp
      have hty : (wF.st id).typestate = a1.typestate := by rw [htyF]; simp
      rw [hid] at htokF hge hold ⊢
      have hsame : tokenHold I.desc (tname id) d (wF.st id) = tokenHold I.desc (tname id) d a1 := by
        simp [tokenHold, hph, hty]
      rw [hsame, htokF]
      exact Int.le_trans (Int.ofNat_le.mpr (hhold d)) (Int.le_trans hold hge)
    · have hph : (wF.st s).phase = (w.st s).phase := by rw [hphF]; simp [hid]
      have hty : (wF.st s).typestate = (w.st s).typestate := by rw [htyF]; simp [hid]
      have hsame : tokenHold I.desc (tname s) d (wF.st s) =
          tokenHold I.desc (tname s) d (w.st s) := by
        simp [tokenHold, hph, hty]
      rw [hsame, htokF]
      exact Int.le_trans hold hge
  · intro s d hs hterm
    rw [hrost] at hs ⊢
    have h0 := hO.still s d hs hterm
    rw [howed]
    by_cases hd : d = tname id
    · rw [hd] at h0 ⊢
      by_cases hss : s = sender
      · simp [hss] at h0 ⊢
        have hown' := hown sender
        simp at hown'
        have hle : owed (fun i => if i = id then a1 else w.st i) (tname id) sender w.roster ≤
            owed w.st (tname id) sender w.roster := by omega
        exact Nat.le_trans hle h0
      · have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
    · rw [hother d hd s]
      exact h0
  · intro hcrash s d hs hdead
    have hc : w.crashed = false := hcr.symm.trans
      (by simpa [wF, wA, creditLive, creditSender, setActor] using hcrash)
    rw [hrost] at hs ⊢
    have hdead0 : (w.st s).life ≠ .alive := by simpa [hlifeF] using hdead
    have h0 := hO.quiet hc s d hs hdead0
    rw [howed]
    by_cases hd : d = tname id
    · rw [hd] at h0 ⊢
      by_cases hss : s = sender
      · rw [hss] at h0 ⊢
        have hown' := hown sender
        simp at hown'
        have hle : (owed (fun i => if i = id then a1 else w.st i) (tname id) sender w.roster : Int) ≤
            (owed w.st (tname id) sender w.roster : Int) := by
          have hnat : owed (fun i => if i = id then a1 else w.st i) (tname id) sender w.roster ≤
              owed w.st (tname id) sender w.roster := by omega
          exact Int.ofNat_le.mpr hnat
        exact Int.le_trans hle h0
      · have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
    · rw [hother d hd s]
      exact h0
  · intro hcrash i hdead
    have hc : w.crashed = false := hcr.symm.trans
      (by simpa [wF, wA, creditLive, creditSender, setActor] using hcrash)
    have hdead0 : (w.st i).life = .absent ∨ (w.st i).life = .dead := by
      simpa [hlifeF] using hdead
    by_cases hi : i = id
    · subst hi
      rw [hboxF, hparkF]
      simp
      rcases hdead0 with hdead0 | hdead0
      · exact hdeadQ (by rw [hlife, hdead0]; intro h; cases h)
      · exact hdeadQ (by rw [hlife, hdead0]; intro h; cases h)
    · rw [hboxF, hparkF]
      simp [hi]
      exact hO.deadEmpty hc i hdead0

  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [hboxF] at hm
      by_cases hh : host = id
      · simp [hh] at hm ⊢
        unfold queueOk at hkeyB ⊢
        exact hkeyB m hm
      · simp [hh] at hm
        unfold queueOk
        exact (hO.sameKey host).1 m hm
    · intro p hp
      rw [hparkF] at hp
      by_cases hh : host = id
      · simp [hh] at hp ⊢
        unfold queueOk at hkeyP ⊢
        exact hkeyP p hp
      · simp [hh] at hp
        unfold queueOk
        exact (hO.sameKey host).2 p hp
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
  · exact ixFresh_copy I.desc w wF hO.ixFresh hrost hixf

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

/-- Resuming does not raise the reserve. A call resume of a non-call park is
not a step this account is asked to keep: the parked flag and the resume flag
agree while the sender is alive. -/
theorem tokenHold_resume (D : Description) (template dstName : String) (a : Actor) (isCall : Bool)
    (dst : InstId) (hc : contTy a)
    (hsafe : isCall = true → ∀ p k, a.phase = .parked p false k → False) :
    tokenHold D template dstName (resumeSender a isCall dst) ≤ tokenHold D template dstName a := by
  cases h : a.phase with
  | parked p c k =>
    have hty : a.typestate = k.toState := by simpa [contTy, h] using hc
    cases isCall with
    | false =>
      cases hk : k.rest with
      | nil =>
        cases c <;>
          simp [resumeSender, h, proceed, tokenHold, pathReserve, contAt, hk, hty, Nat.le_max_left]
      | cons _ _ =>
        cases c <;> simp [resumeSender, h, proceed, tokenHold, hk, hty, Nat.le_max_left]
    | true =>
      cases c with
      | false => exact (hsafe rfl p k h).elim
      | true =>
        simp [resumeSender, h, tokenHold]
        apply Nat.max_le.mpr
        refine ⟨Nat.le_max_left _ _, ?_⟩
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  | idle => simp [resumeSender, h]
  | run _ => simp [resumeSender, h]
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
    (hO : OccInv I w) (hc : contTy (w.st sender))
    (hsafe : (w.st sender).life = .alive → isCall = true →
      ∀ p k, (w.st sender).phase = .parked p false k → False) :
    OccInv I (setActor w sender (resumeSender (w.st sender) isCall dst)) := by
  let a := resumeSender (w.st sender) isCall dst
  exact occ_set I w sender a hO (by simp [a, resume_keeps (w.st sender) isCall dst hc])
    (by simp [a, resume_box]) (by simp [a, resume_park]) (by intro d; simp [a, resume_tokens]) (by
      intro d hl
      have hl0 : (w.st sender).life = .alive := by
        have hlife := (resume_keeps (w.st sender) isCall dst hc).2
        rw [← hlife]
        simpa [a] using hl
      have hold := hO.slack sender d hl0
      have hle := tokenHold_resume I.desc (tname sender) d (w.st sender) isCall dst hc
        (by intro hcall p k hph; exact hsafe hl0 hcall p k hph)
      have htok := resume_tokens (w.st sender) isCall dst d
      simp [a] at hle htok ⊢
      rw [htok]
      exact Int.le_trans (Int.ofNat_le.mpr hle) hold)

theorem queuedFromKey_agree (w w' : World) (hr : w'.roster = w.roster)
    (hb : ∀ i, (w'.st i).box = (w.st i).box) (hp : ∀ i, (w'.st i).parked = (w.st i).parked)
    (name : String) (key : Nat) (dst : String) :
    queuedFromKey w' name key dst = queuedFromKey w name key dst := by
  unfold queuedFromKey
  simp only [hr]
  refine foldl_pointwise _ _ w.roster 0 ?_
  intro n host _
  simp [hb, hp]

/-- Replacing one host's queue changes `queuedFromKey` by the filter-length
difference, and only when that host's template is the destination. -/
theorem queuedFromKey_replace (w : World) (id : InstId) (a : Actor) (name : String) (key : Nat)
    (dst : String) (extra : Nat) (nodup : w.roster.Nodup) (hmem : id ∈ w.roster)
    (hdelta :
      ((w.st id).box.filter (keyPred name key)).length +
        ((w.st id).parked.filter fun p => keyPred name key p.msg).length =
      (a.box.filter (keyPred name key)).length +
        (a.parked.filter fun p => keyPred name key p.msg).length + extra) :
    queuedFromKey w name key dst =
      queuedFromKey (setActor w id a) name key dst + if tname id = dst then extra else 0 := by
  let bit := if tname id = dst then extra else 0
  let pred := keyPred name key
  let add (st : InstId → Actor) (host : InstId) : Nat :=
    if (tname host != dst) = true then 0
    else ((st host).box.filter pred).length + ((st host).parked.filter fun (p : Parked) => pred p.msg).length
  let st' : InstId → Actor := fun host => if host = id then a else w.st host
  have hd : add w.st id = add st' id + bit := by
    have hst : st' id = a := by simp [st']
    cases hbb : tname id != dst with
    | false =>
      have ht : tname id = dst := by simpa [bne, beq_iff_eq] using hbb
      simp only [add, hst, hbb, ht, bit]
      simp
      exact hdelta
    | true =>
      have ht : ¬ tname id = dst := by
        intro heq
        simp [bne, heq] at hbb
      simp [add, hst, hbb, ht, bit]
  have hs : ∀ x, x ≠ id → add w.st x = add st' x := by
    intro x hx
    simp [add, st', hx]
  unfold queuedFromKey
  simp only [setActor]
  let step (st : InstId → Actor) (n : Nat) (host : InstId) : Nat :=
    if (tname host != dst) = true then n
    else n + ((st host).box.filter pred).length + ((st host).parked.filter fun (p : Parked) => pred p.msg).length
  have hstep (st : InstId → Actor) (n : Nat) (host : InstId) : step st n host = n + add st host := by
    simp only [step, add]
    by_cases ht : (tname host != dst) = true
    · simp [ht]
    · have hf : (tname host != dst) = false := by
        cases hbb : tname host != dst with
        | false => rfl
        | true => exact absurd hbb ht
      simp [ht, hf]
      omega
  have hOld := foldl_pointwise (step w.st) (fun n h => n + add w.st h) w.roster 0 fun n host _ => hstep w.st n host
  have hNew := foldl_pointwise (step st') (fun n h => n + add st' h) w.roster 0 fun n host _ => hstep st' n host
  have hfold := foldl_add_once (add w.st) (add st') bit id hd hs 0 w.roster nodup
  simp [hmem] at hfold
  show List.foldl (step w.st) 0 w.roster = List.foldl (step st') 0 w.roster + bit
  calc
    List.foldl (step w.st) 0 w.roster = List.foldl (fun n h => n + add w.st h) 0 w.roster := hOld
    _ = List.foldl (fun n h => n + add st' h) 0 w.roster + bit := hfold
    _ = List.foldl (step st') 0 w.roster + bit := by rw [← hNew]

/-- Parking one message counts like appending it: the queue total does not care
which of the host's two lists holds the message. -/
theorem queuedFromKey_park (w : World) (id : InstId) (a : Actor) (p : Parked) (name : String)
    (key : Nat) (dst : String) (nodup : w.roster.Nodup) (hmem : id ∈ w.roster)
    (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked ++ [p]) :
    queuedFromKey (setActor w id a) name key dst =
      queuedFromKey w name key dst +
        if (tname id != dst) = true then 0 else if keyPred name key p.msg = true then 1 else 0 := by
  let wA := setActor w id a
  let extra := if keyPred name key p.msg = true then 1 else 0
  have hst : wA.st id = a := by simp [wA, setActor]
  have hdelta :
      ((wA.st id).box.filter (keyPred name key)).length +
        ((wA.st id).parked.filter fun q => keyPred name key q.msg).length =
      ((w.st id).box.filter (keyPred name key)).length +
        ((w.st id).parked.filter fun q => keyPred name key q.msg).length + extra := by
    rw [hst, hbox, hpark, park_filter_snoc]
    simp only [extra]
    omega
  have hrep := queuedFromKey_replace wA id (w.st id) name key dst extra
    (by simpa [wA, setActor] using nodup) (by simpa [wA, setActor] using hmem) hdelta
  have hback : queuedFromKey (setActor wA id (w.st id)) name key dst = queuedFromKey w name key dst := by
    refine queuedFromKey_agree _ _ ?_ ?_ ?_ name key dst
    · simp [wA, setActor]
    · intro i
      by_cases hi : i = id <;> simp [wA, setActor, hi]
    · intro i
      by_cases hi : i = id <;> simp [wA, setActor, hi]
  rw [hrep, hback]
  have hbit :
      (if tname id = dst then extra else 0) =
        if (tname id != dst) = true then 0 else extra := by
    by_cases ht : tname id = dst
    · have hn : (tname id != dst) = false := by simp [bne, ht]
      simp [ht, hn]
    · have hn : (tname id != dst) = true := by
        cases hbb : tname id != dst with
        | true => rfl
        | false =>
          exact absurd (beq_iff_eq.mp (by simpa [bne] using hbb)) ht
      simp [ht, hn]
  rw [hbit]

theorem cast_keybit (host dst : String) (pred : Bool) :
    ((if host = dst then if pred = true then 1 else 0 else 0 : Nat) : Int) =
      if dst = host then if pred = true then (1 : Int) else 0 else 0 := by
  by_cases ht : host = dst
  · subst ht
    by_cases hp : pred = true <;> simp [hp]
  · have hflip : ¬ dst = host := fun h => ht h.symm
    by_cases hp : pred = true <;> simp [ht, hflip, hp]

theorem queueDrop_msg (sender : InstId) (m : Msg) (name : String) (key : Nat) (d dst : String)
    (hs : m.sender = sender) :
    (if d = dst then if keyPred name key m = true then (1 : Int) else 0 else 0) =
      queueDrop sender name key d dst := by
  cases hsender : sender with
  | core c =>
    have hm : m.sender = InstId.core c := by rw [hs, hsender]
    simp [queueDrop, keyDrop, keyPred, hm]
  | peer n k g =>
    have hm : m.sender = InstId.peer n k g := by rw [hs, hsender]
    simp [queueDrop, keyDrop, keyPred, hm]

theorem occ_bulk_box (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (m : Msg) (ms : List Msg) (w1 : World) (a1 : Actor) (hO : OccInv I w)
    (hbox : (w.st id).box = m :: ms) (hpark : (w.st id).parked = [])
    (halive : (w.st id).life = .alive) (hidle : (w.st id).phase = .idle)
    (hd : deliver I w id {(w.st id) with box := ms} m = some (w1, a1)) :
    OccInv I (creditLive (setActor w1 id a1) (tname id) m.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with box := ms} m w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  have hmem := hO.aliveIn id halive
  have hsend := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  apply occ_consume I w w1 id m.sender a1 hO
      (fun i => deliver_st I w id _ m w1 a1 i hd)
      (deliver_roster I w id _ m w1 a1 hd) (deliver_N I w id _ m w1 a1 hd)
      (fun n => by
        rw [deliver_base I w id _ m w1 a1 hd]
        exact readCells_nextIx I.desc w id n)
      (deliver_crashed I w id _ m w1 a1 hd)
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
  · intro name key d
    have hdelta :
        ((w.st id).box.filter (keyPred name key)).length +
          ((w.st id).parked.filter fun p => keyPred name key p.msg).length =
        (a1.box.filter (keyPred name key)).length +
          (a1.parked.filter fun p => keyPred name key p.msg).length +
          (if keyPred name key m = true then 1 else 0) := by
      simp [hbox, hb, hpark, hparkA, List.filter]
      cases hk : keyPred name key m <;> simp [hk]
    have hrep := queuedFromKey_replace w id a1 name key d
      (if keyPred name key m = true then 1 else 0) hO.nodup hmem hdelta
    have hagree := queuedFromKey_agree (setActor w id a1) (setActor w1 id a1)
      (by simp [setActor, deliver_roster I w id _ m w1 a1 hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ m w1 a1 i hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ m w1 a1 i hd])
      name key d
    rw [← hagree] at hrep
    rw [hrep, Int.natCast_add, cast_keybit (tname id) d (keyPred name key m),
      queueDrop_msg m.sender m name key d (tname id) rfl]
    omega
  · intro d
    have hsame : tokenHold I.desc (tname id) d {(w.st id) with box := ms} =
        tokenHold I.desc (tname id) d (w.st id) := by simp [tokenHold]
    simpa [hsame] using hfl d
  · intro msg hm
    rw [hb] at hm
    exact hO.sentFrom id msg (by rw [hbox]; exact List.Mem.tail _ hm)
  · intro p hp
    rw [hparkA, hpark] at hp
    cases hp
  · intro p hp
    rw [hparkA, hpark] at hp
    cases hp
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
    OccInv I (creditLive (setActor w1 id a1) (tname id) p.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with parked := ps} p.msg w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  have hmem := hO.aliveIn id halive
  have hsend := hO.parkFrom id p (by rw [hpark]; exact List.Mem.head _)
  apply occ_consume I w w1 id p.sender a1 hO
      (fun i => deliver_st I w id _ p.msg w1 a1 i hd)
      (deliver_roster I w id _ p.msg w1 a1 hd) (deliver_N I w id _ p.msg w1 a1 hd)
      (fun n => by
        rw [deliver_base I w id _ p.msg w1 a1 hd]
        exact readCells_nextIx I.desc w id n)
      (deliver_crashed I w id _ p.msg w1 a1 hd)
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
  · intro name key d
    have hdelta :
        ((w.st id).box.filter (keyPred name key)).length +
          ((w.st id).parked.filter fun q => keyPred name key q.msg).length =
        (a1.box.filter (keyPred name key)).length +
          (a1.parked.filter fun q => keyPred name key q.msg).length +
          (if keyPred name key p.msg = true then 1 else 0) := by
      simp [hbox, hb, hpark, hparkA, List.filter]
      cases hk : keyPred name key p.msg <;> simp [hk]
    have hrep := queuedFromKey_replace w id a1 name key d
      (if keyPred name key p.msg = true then 1 else 0) hO.nodup hmem hdelta
    have hagree := queuedFromKey_agree (setActor w id a1) (setActor w1 id a1)
      (by simp [setActor, deliver_roster I w id _ p.msg w1 a1 hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ p.msg w1 a1 i hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ p.msg w1 a1 i hd])
      name key d
    rw [← hagree] at hrep
    rw [hrep, Int.natCast_add, cast_keybit (tname id) d (keyPred name key p.msg),
      queueDrop_msg p.sender p.msg name key d (tname id) hsame.symm]
    omega
  · intro d
    have hsameT : tokenHold I.desc (tname id) d {(w.st id) with parked := ps} =
        tokenHold I.desc (tname id) d (w.st id) := by simp [tokenHold]
    simpa [hsameT] using hfl d
  · intro msg hm
    rw [hb, hbox] at hm
    cases hm
  · intro q hq
    rw [hparkA] at hq
    exact hO.parkFrom id q (by rw [hpark]; exact List.Mem.tail _ hq)
  · intro q hq
    rw [hparkA] at hq
    exact hO.parkMsg id q (by rw [hpark]; exact List.Mem.tail _ hq)
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
    OccInv I (creditLive (setActor w1 id { a1 with box := a1.box ++ [p.msg], parked := ps }) (tname id) m.sender) := by
  have hacc := deliver_account I hL hG w id {(w.st id) with box := ms} m w1 a1
    (by simp [halive]) (by simp [hidle]) hd
  obtain ⟨hl, hb, hparkA, htokA, hfl⟩ := hacc
  let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
  have hmem := hO.aliveIn id halive
  have hsend := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  apply occ_consume I w w1 id m.sender admitted hO
      (fun i => deliver_st I w id _ m w1 a1 i hd)
      (deliver_roster I w id _ m w1 a1 hd) (deliver_N I w id _ m w1 a1 hd)
      (fun n => by
        rw [deliver_base I w id _ m w1 a1 hd]
        exact readCells_nextIx I.desc w id n)
      (deliver_crashed I w id _ m w1 a1 hd)
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
  · intro name key d
    have hdelta :
        ((w.st id).box.filter (keyPred name key)).length +
          ((w.st id).parked.filter fun q => keyPred name key q.msg).length =
        (admitted.box.filter (keyPred name key)).length +
          (admitted.parked.filter fun q => keyPred name key q.msg).length +
          (if keyPred name key m = true then 1 else 0) := by
      simp [admitted, hbox, hb, hpark, List.filter, List.filter_append]
      cases hkm : keyPred name key m <;> cases hkp : keyPred name key p.msg <;> simp [hkm, hkp] <;> omega
    have hrep := queuedFromKey_replace w id admitted name key d
      (if keyPred name key m = true then 1 else 0) hO.nodup hmem hdelta
    have hagree := queuedFromKey_agree (setActor w id admitted) (setActor w1 id admitted)
      (by simp [setActor, deliver_roster I w id _ m w1 a1 hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ m w1 a1 i hd])
      (by intro i; by_cases hi : i = id <;> simp [setActor, hi, deliver_st I w id _ m w1 a1 i hd])
      name key d
    rw [← hagree] at hrep
    rw [hrep, Int.natCast_add, cast_keybit (tname id) d (keyPred name key m),
      queueDrop_msg m.sender m name key d (tname id) rfl]
    omega
  · intro d
    have hphase : tokenHold I.desc (tname id) d admitted = tokenHold I.desc (tname id) d a1 := by
      simp [admitted, tokenHold]
    have hsame : tokenHold I.desc (tname id) d {(w.st id) with box := ms} =
        tokenHold I.desc (tname id) d (w.st id) := by simp [tokenHold]
    simpa [hphase, hsame] using hfl d
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

theorem resume_flag (w : World) (hM : MailInv w) (mb : InstId) (p : Parked)
    (hmem : p ∈ (w.st mb).parked) :
    (w.st p.sender).life = .alive → p.isCall = true →
      ∀ q k, (w.st p.sender).phase = .parked q false k → False := by
  intro hl hcall q k hph
  rcases hM.fwd mb p hmem with ⟨_k', hk'⟩ | hdead
  · rw [hph] at hk'
    injection hk' with _hq hflag
    rw [← hflag] at hcall
    cases hcall
  · rw [hdead] at hl
    cases hl

theorem receive_ready (I : Impl) (w w' : World) (id : InstId)
    (h : receiveBulk I w id = some w') :
    (w.st id).life = .alive ∧ (w.st id).phase = .idle := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · refine ⟨?_, ?_⟩
    · cases hlife : (w.st id).life with
      | alive => rfl
      | absent => exact absurd (Or.inl (by rw [hlife]; intro he; cases he)) hready
      | dead => exact absurd (Or.inl (by rw [hlife]; intro he; cases he)) hready
    · cases hph : (w.st id).phase with
      | idle => rfl
      | run _ => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready
      | parked _ _ _ => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready
      | awaitReply _ _ => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready
      | awaitEffect _ => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready
      | awaitPeer _ => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready
      | crashed => exact absurd (Or.inr (by rw [hph]; intro he; cases he)) hready

theorem occ_bulk (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId) (w' : World)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (h : receiveBulk I w id = some w') :
    OccInv I w' := by
  have halive : (w.st id).life = .alive := (receive_ready I w w' id h).1
  have hidle : (w.st id).phase = .idle := (receive_ready I w w' id h).2
  unfold receiveBulk at h
  by_cases hguard : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hguard] at h
  simp [hguard] at h
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
          not_queued w id hM (by simp [notParked, hidle]) halive id p
            (by rw [hpk]; exact List.Mem.head _)
        have hd' : deliver I w id {(w.st id) with parked := ps} p.msg = some (w1, a1) := by
          simpa [halive, hidle, hbox] using hd
        have hO1 := occ_bulk_park I hL hG w id p ps w1 a1 hO hpk hbox halive hidle hmsg hd'
        let wA := setActor w1 id a1
        let wC := creditLive wA (tname id) p.sender
        have hph : (wC.st p.sender).phase = (w.st p.sender).phase := by
          simp only [wC, creditLive]
          rw [(credit_phase_life wA (tname id) (budgetHolder wA p.sender) p.sender).1,
            setActor_other w1 id p.sender a1 hne, deliver_st I w id _ p.msg w1 a1 p.sender hd']
        have hlfe : (wC.st p.sender).life = (w.st p.sender).life := by
          simp only [wC, creditLive]
          rw [(credit_phase_life wA (tname id) (budgetHolder wA p.sender) p.sender).2,
            setActor_other w1 id p.sender a1 hne, deliver_st I w id _ p.msg w1 a1 p.sender hd']
        have hty : (wC.st p.sender).typestate = (w.st p.sender).typestate := by
          simp only [wC, creditLive]
          rw [(credit_keeps_ty wA (tname id) (budgetHolder wA p.sender) p.sender).2,
            setActor_other w1 id p.sender a1 hne, deliver_st I w id _ p.msg w1 a1 p.sender hd']
        have hc : contTy (wC.st p.sender) := (contTy_match _ _ hph hty).mpr (hS.cont p.sender)
        have hflag := resume_flag w hM id p (by rw [hpk]; exact List.Mem.head _)
        simpa [wC, hmsg] using occ_resume I wC p.sender p.isCall id hO1 hc (by
          intro hl hcall q k hbad
          exact hflag (by rw [← hlfe]; exact hl) hcall q k (by rw [← hph]; exact hbad))
  | cons m ms =>
    cases hpk : (w.st id).parked with
    | nil =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hd' : deliver I w id {(w.st id) with box := ms} m = some (w1, a1) := by
          simpa [halive, hidle, hpk] using hd
        simpa using occ_bulk_box I hL hG w id m ms w1 a1 hO hbox hpk halive hidle hd'
    | cons p ps =>
      simp [hbox, hpk] at h
      split at h
      · cases h
      · next w1 a1 hd =>
        cases h
        have hmsg := hO.parkMsg id p (by rw [hpk]; exact List.Mem.head _)
        have hne : p.sender ≠ id :=
          not_queued w id hM (by simp [notParked, hidle]) halive id p
            (by rw [hpk]; exact List.Mem.head _)
        let admitted : Actor := { a1 with box := a1.box ++ [p.msg], parked := ps }
        have hd' : deliver I w id {(w.st id) with box := ms} m = some (w1, a1) := by
          simpa [halive, hidle, hpk] using hd
        have hO1 := occ_bulk_both I hL hG w id m ms p ps w1 a1 hO hbox hpk halive hidle hmsg hd'
        let wA := setActor w1 id admitted
        let wC := creditLive wA (tname id) m.sender
        have hph : (wC.st p.sender).phase = (w.st p.sender).phase := by
          simp only [wC, creditLive]
          rw [(credit_phase_life wA (tname id) (budgetHolder wA m.sender) p.sender).1,
            setActor_other w1 id p.sender admitted hne, deliver_st I w id _ m w1 a1 p.sender hd']
        have hlfe : (wC.st p.sender).life = (w.st p.sender).life := by
          simp only [wC, creditLive]
          rw [(credit_phase_life wA (tname id) (budgetHolder wA m.sender) p.sender).2,
            setActor_other w1 id p.sender admitted hne, deliver_st I w id _ m w1 a1 p.sender hd']
        have hty : (wC.st p.sender).typestate = (w.st p.sender).typestate := by
          simp only [wC, creditLive]
          rw [(credit_keeps_ty wA (tname id) (budgetHolder wA m.sender) p.sender).2,
            setActor_other w1 id p.sender admitted hne, deliver_st I w id _ m w1 a1 p.sender hd']
        have hc : contTy (wC.st p.sender) := (contTy_match _ _ hph hty).mpr (hS.cont p.sender)
        have hflag := resume_flag w hM id p (by rw [hpk]; exact List.Mem.head _)
        simpa [wC, admitted] using occ_resume I wC p.sender p.isCall id hO1 hc (by
          intro hl hcall q k hbad
          exact hflag (by rw [← hlfe]; exact hl) hcall q k (by rw [← hph]; exact hbad))

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
  exact Int.le_trans (hhold d hl) (by rw [htok d]; exact hO.slack id d hl0)

theorem effSends_ge (dst : String) (e : Eff) (tailN : Nat) : tailN ≤ effSends dst e tailN := by
  cases e with
  | send _ _ _ => simp [effSends]
  | trySend _ _ _ _ _ =>
    simp [effSends]
    exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  | call _ _ _ _ _ =>
    simp [effSends]
    exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  | peer _ =>
    simp [effSends]
    exact Nat.le_max_left _ _
  | reply => simp [effSends]
  | selfSchedule _ => simp [effSends]
  | cell _ _ _ => simp [effSends]
  | internal => simp [effSends]
  | abort => simp [effSends]
  | terminate => simp [effSends]
  | spawn _ => simp [effSends]

theorem sendsTo_tail (dst : String) (es : List Eff) : sendsTo dst es.tail ≤ sendsTo dst es := by
  cases es with
  | nil => simp [sendsTo]
  | cons e es =>
    simp [List.tail_cons, sendsTo]
    exact effSends_ge dst e (sendsTo dst es)

theorem proceed_tail (a : Actor) (k : Cont) (d : String) (hty : a.typestate = k.toState)
    (hrest : contRest a.phase = k.rest) :
    pending (proceed a (afterHead k)) d ≤ pending a d ∧
      (proceed a (afterHead k)).typestate = a.typestate := by
  constructor
  · have hdrop : sendsTo d k.rest.tail ≤ sendsTo d k.rest := sendsTo_tail d k.rest
    have hpend : sendsTo d k.rest ≤ pending a d := by
      cases hph : a.phase with
      | run k' =>
        have hr : k'.rest = k.rest := by simpa [contRest, hph] using hrest
        simp [pending, hph, hr]
      | awaitEffect k' =>
        have hr : k'.rest = k.rest := by simpa [contRest, hph] using hrest
        simp [pending, hph, hr]
      | parked _ c k' =>
        have hr : k'.rest = k.rest := by simpa [contRest, hph] using hrest
        cases c with
        | false => simp [pending, hph, hr]
        | true =>
          simp [pending, hph, hr]
          exact Nat.le_max_left _ _
      | awaitReply _ k' =>
        have hr : k'.rest = k.rest := by simpa [contRest, hph] using hrest
        simp [pending, hph, hr]
        exact Nat.le_max_left _ _
      | awaitPeer k' =>
        have hr : k'.rest = k.rest := by simpa [contRest, hph] using hrest
        simp [pending, hph, hr]
        exact Nat.le_max_left _ _
      | idle =>
        have hr : k.rest = [] := by simpa [contRest, hph] using hrest.symm
        simp [pending, sendsTo, hph, hr]
      | crashed =>
        have hr : k.rest = [] := by simpa [contRest, hph] using hrest.symm
        simp [pending, sendsTo, hph, hr]
    cases htail : k.rest.tail with
    | nil => simp [afterHead, proceed, pending, htail]
    | cons _ _ =>
      simp [afterHead, proceed, pending, htail]
      exact Nat.le_trans (by simpa [htail] using hdrop) (by simpa [pending] using hpend)
  · cases htail : k.rest.tail <;> simp [afterHead, proceed, htail, hty]

theorem occ_cell_st (w : World) (dst label : String) (c : Cell) (i : InstId) :
    (setCell w dst label c).st i = w.st i := by
  simp [setCell]

theorem occ_cell_roster (w : World) (dst label : String) (c : Cell) :
    (setCell w dst label c).roster = w.roster ∧ (setCell w dst label c).N = w.N := by
  simp [setCell]

theorem occ_cell_ix (w : World) (dst label : String) (c : Cell) (n : String) :
    (setCell w dst label c).nextIx n = w.nextIx n := by
  simp [setCell]

theorem crash_box (w : World) (i : InstId) :
    ((crashWorld w).st i).box = (w.st i).box ∧ ((crashWorld w).st i).parked = (w.st i).parked ∧
      ((crashWorld w).st i).tokens = (w.st i).tokens := by
  by_cases hm : i ∈ w.roster
  · rw [crash_at w i hm]
    by_cases ha : (w.st i).life = .alive
    · rw [crash_go ha]
      simp
    · rw [crash_stay ha]
      exact ⟨rfl, rfl, rfl⟩
  · rw [crash_off w i hm]
    simp

theorem crash_dead (w : World) (i : InstId) (hm : i ∈ w.roster) :
    ((crashWorld w).st i).life ≠ .alive := by
  rw [crash_at w i hm]
  by_cases ha : (w.st i).life = .alive
  · rw [crash_go ha]
    intro h
    cases h
  · rw [crash_stay ha]
    exact ha

theorem findLive_alive (w : World) (name : String) (key : Nat) (id : InstId)
    (h : findLive w name key = some id) : (w.st id).life = .alive := by
  have hp := List.find?_some h
  cases id with
  | core _ => simp [findLive] at hp
  | peer _ _ _ =>
    simp only [findLive, Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.2

theorem findLive_crash (w : World) (name : String) (key : Nat) :
    findLive (crashWorld w) name key = none := by
  unfold findLive
  rw [List.find?_eq_none]
  intro i hmem
  cases i with
  | core _ => simp
  | peer n k g =>
    intro hp
    have hd := crash_dead w (InstId.peer n k g) (by simpa [crashWorld] using hmem)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact hd hp.2

theorem crash_aliveCount (w : World) (template : String) :
    aliveCount (crashWorld w) template = 0 := by
  have hr : (crashWorld w).roster = w.roster := by simp [crashWorld]
  rw [aliveCount_sum, hr]
  refine (sum_congr _ _ w.roster ?_).trans (sum_zero _)
  intro i hi
  unfold aliveBit
  have hd := crash_dead w i hi
  cases hbb : ((crashWorld w).st i).life == .alive with
  | false => simp [hbb]
  | true => exact absurd ((beq_iff_eq).mp hbb) hd

/-- A crash kills every roster actor and leaves the mail where it is. The
per-key equation survives because a live holder had nonnegative tokens, so the
mail that stays queued is still within the budget. `quiet` and `deadEmpty`
are not claimed once `crashed` is set. -/
theorem occ_crash (I : Impl) (w : World) (hO : OccInv I w) : OccInv I (crashWorld w) := by
  have hr : (crashWorld w).roster = w.roster := by simp [crashWorld]
  have hN : (crashWorld w).N = w.N := by simp [crashWorld]
  have hcr : (crashWorld w).crashed = true := by simp [crashWorld]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact hO.nodup
  · intro i hl
    by_cases hm : i ∈ w.roster
    · exact absurd hl (crash_dead w i hm)
    · rw [hr]
      rw [crash_off w i hm] at hl
      exact hO.aliveIn i hl
  · intro name key g1 g2 h1 h2 hl1 _
    rw [hr] at h1
    exact absurd hl1 (crash_dead w _ h1)
  · intro template _
    rw [crash_aliveCount w template]
    exact Nat.zero_le _
  · intro template _
    rw [crash_aliveCount w template, hN]
    exact Nat.zero_le _
  · intro i hnin
    have hnin' : i ∉ w.roster := by rw [hr] at hnin; exact hnin
    rw [crash_off w i hnin']
    exact hO.offEmpty i hnin'
  · intro i m hm
    rw [(crash_box w i).1] at hm
    rw [hr]
    exact hO.sentFrom i m hm
  · intro i p hp
    rw [(crash_box w i).2.1] at hp
    rw [hr]
    exact hO.parkFrom i p hp
  · intro i p hp
    rw [(crash_box w i).2.1] at hp
    exact hO.parkMsg i p hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key live d hfind
      rw [findLive_crash w name key] at hfind
      cases hfind
    · intro name d hl hmem
      rw [hr] at hmem
      exact absurd hl (crash_dead w (InstId.core name) hmem)
    · intro name key d _
      have hq := queuedFromKey_agree w (crashWorld w) hr (fun i => (crash_box w i).1)
        (fun i => (crash_box w i).2.1) name key d
      rw [hq]
      cases hfl : findLive w name key with
      | none => exact hO.balance.2 name key d hfl
      | some live =>
        have hl := findLive_alive w name key live hfl
        have hbal := hO.balance.1.1 name key live d hfl
        have hnn : (0 : Int) ≤ (w.st live).tokens d :=
          Int.le_trans (Int.natCast_nonneg _) (hO.slack live d hl)
        omega
  · intro i d hl
    by_cases hm : i ∈ w.roster
    · exact absurd hl (crash_dead w i hm)
    · rw [crash_off w i hm] at hl
      exact absurd (hO.aliveIn i hl) hm
  · intro s d hs hterm
    rw [hr] at hs ⊢
    have how := owed_mail_eq (crashWorld w).st w.st d s w.roster
      (fun i _ => ⟨(crash_box w i).1, (crash_box w i).2.1⟩)
    rw [how]
    exact hO.still s d hs hterm
  · intro hcrash
    simp [hcr] at hcrash
  · intro hcrash
    simp [hcr] at hcrash
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [(crash_box w host).1] at hm
      unfold queueOk
      exact (hO.sameKey host).1 m hm
    · intro p hp
      rw [(crash_box w host).2.1] at hp
      unfold queueOk
      exact (hO.sameKey host).2 p hp
  · intro i hi
    exact hO.shaped i (by rw [hr] at hi; exact hi)
  · intro host hk
    refine ⟨?_, ?_⟩
    · intro m hm
      rw [(crash_box w host).1] at hm
      exact (hO.coreFrom host hk).1 m hm
    · intro p hp
      rw [(crash_box w host).2.1] at hp
      exact (hO.coreFrom host hk).2 p hp
  · exact ixFresh_copy I.desc w (crashWorld w) hO.ixFresh (by simp [crashWorld])
      (fun _ => by simp [crashWorld])

theorem occ_offer (I : Impl) (w : World) (host : InstId) (msg : Msg) (hO : OccInv I w) :
    OccInv I (offerPrio I.desc w host msg) := by
  unfold offerPrio
  dsimp only
  split
  · exact occ_crash I w hO
  · exact occ_keep I w host _ hO rfl rfl rfl (fun _ => rfl) (fun _ _ => by simp [tokenHold])

theorem occ_try_wake (I : Impl) (w : World) (dstId : InstId) (label : String) (writer : InstId)
    (hO : OccInv I w) : OccInv I (tryWake I.desc w dstId label writer) := by
  unfold tryWake
  dsimp only
  split
  · exact hO
  · exact occ_offer I w dstId _ hO

theorem occ_wakes (I : Impl) (ids : List InstId) (w : World) (dst label : String) (writer : InstId)
    (hO : OccInv I w) :
    OccInv I ((ids.foldl (fun w id => tryWake I.desc w id label writer) w)) := by
  induction ids generalizing w with
  | nil => simpa using hO
  | cons id ids ih =>
    rw [List.foldl_cons]
    exact ih _ (occ_try_wake I w id label writer hO)

theorem effReserve_ge (D : Description) (template dst : String) (at_ : BranchAt) (e : Eff) (tail : Nat) :
    tail ≤ effReserve D template dst at_ e tail := by
  cases e with
  | send _ _ _ => simp [effReserve]
  | trySend _ _ _ _ _ =>
    simp [effReserve]
    exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  | call _ _ _ _ _ =>
    simp [effReserve]
    exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  | peer _ =>
    simp [effReserve]
    exact Nat.le_max_left _ _
  | reply => simp [effReserve]
  | selfSchedule _ => simp [effReserve]
  | cell _ _ _ => simp [effReserve]
  | internal => simp [effReserve]
  | abort => simp [effReserve]
  | terminate => simp [effReserve]
  | spawn _ => simp [effReserve]

theorem tokenHold_advance (D : Description) (template dst : String) (a : Actor) (k : Cont)
    (hph : a.phase = .run k) :
    tokenHold D template dst (proceed a (afterHead k)) ≤ tokenHold D template dst a := by
  cases hk : k.rest with
  | nil => simp [afterHead, proceed, tokenHold, pathReserve, contAt, hk, hph]
  | cons _ es =>
    cases es with
    | nil =>
      simp [afterHead, List.tail_cons, proceed, tokenHold, pathReserve, contAt, hk, hph]
      exact effReserve_ge D template dst (contAt k) _ _
    | cons _ _ =>
      simp [afterHead, List.tail_cons, proceed, tokenHold, pathReserve, contAt, hk, hph]
      exact effReserve_ge D template dst (contAt k) _ _

theorem tokenHold_finish_reply (D : Description) (template name : String) (a : Actor)
    (dstId : InstId) (k : Cont) (hph : a.phase = .awaitReply dstId k) :
    tokenHold D template name (finishCall a k .reply) ≤ tokenHold D template name a := by
  cases hk : k.rest with
  | nil =>
    simp [finishCall, selectCall, proceed, tokenHold, pathReserve, contAt, hk, hph]
    exact Nat.le_max_left _ _
  | cons _ _ =>
    simp [finishCall, selectCall, proceed, tokenHold, pathReserve, contAt, hk, hph]
    exact Nat.le_max_left _ _

theorem occ_advance (I : Impl) (w : World) (id : InstId) (k : Cont) (hO : OccInv I w)
    (_hty : (w.st id).typestate = k.toState) (hph : (w.st id).phase = .run k) :
    OccInv I (setActor w id (proceed (w.st id) (afterHead k))) := by
  apply occ_keep I w id (proceed (w.st id) (afterHead k)) hO (proceed_life _ _) (proceed_box _ _)
    (proceed_parked _ _) (proceed_tokens _ _)
  intro d _
  exact Int.ofNat_le.mpr (tokenHold_advance I.desc (tname id) d (w.st id) k hph)

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
        · have hO1 := occ_keep I w caller (finishCall (w.st caller) ck .reply) hO
            (finishCall_life _ _ _)
            (by simpa [finishCall] using proceed_box (w.st caller) (selectCall ck .reply))
            (by simpa [finishCall] using proceed_parked (w.st caller) (selectCall ck .reply))
            (by intro d; simpa [finishCall] using proceed_tokens (w.st caller) (selectCall ck .reply) d)
            (by
              intro d _
              exact Int.ofNat_le.mpr
                (tokenHold_finish_reply I.desc (tname caller) d (w.st caller) dst ck hcall))
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
Every other account is unchanged. A lone terminable may be the sender: the
message is charged to its own live slot, and that slot still covers the debt. -/
theorem occ_pay (I : Impl) (w w' : World) (sender : InstId) (name : String) (hO : OccInv I w)
    (hrost : w'.roster = w.roster) (hN : w'.N = w.N) (hix : ∀ n, w'.nextIx n = w.nextIx n)
    (hlife : ∀ i, (w'.st i).life = (w.st i).life)
    (hSty : (w'.st sender).typestate = (w.st sender).typestate)
    (htyO : ∀ i, i ≠ sender → (w'.st i).typestate = (w.st i).typestate)
    (hphO : ∀ i, i ≠ sender → (w'.st i).phase = (w.st i).phase)
    (htok : ∀ d, (w'.st sender).tokens d + (if d = name then 1 else 0) = (w.st sender).tokens d)
    (htokO : ∀ i, i ≠ sender → ∀ d, (w'.st i).tokens d = (w.st i).tokens d)
    (hown : ∀ s, owed w'.st name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s, owed w'.st d s w.roster = owed w.st d s w.roster)
    (hbox : ∀ i m, m ∈ (w'.st i).box → m.sender ∈ w.roster)
    (hpark : ∀ i p, p ∈ (w'.st i).parked → p.sender ∈ w.roster)
    (hpm : ∀ i p, p ∈ (w'.st i).parked → p.sender = p.msg.sender)
    (hoff : ∀ i, i ∉ w.roster → (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked)
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hdeadE : w'.crashed = false →
      ∀ i, (w'.st i).life ≠ .alive → (w'.st i).box = [] ∧ (w'.st i).parked = [])
    (hkey : ∀ host,
      (∀ m ∈ (w'.st host).box, queueOk I.desc w m.sender host) ∧
      (∀ p ∈ (w'.st host).parked, queueOk I.desc w p.sender host))
    (hfrom : ∀ host, peerKey host = none →
      (∀ m ∈ (w'.st host).box, coreSender I.desc m.sender) ∧
      (∀ p ∈ (w'.st host).parked, coreSender I.desc p.sender))
    (hcr : w'.crashed = w.crashed)
    (hq : ∀ nm k d,
      (queuedFromKey w' nm k d : Int) =
        (queuedFromKey w nm k d : Int) + queueDrop sender nm k d name)
    (hhold : ∀ d, (tokenHold I.desc (tname sender) d (w'.st sender) : Int) +
        (if d = name then (1 : Int) else 0) ≤
      (tokenHold I.desc (tname sender) d (w.st sender) : Int)) :
    OccInv I w' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrost]; exact hO.nodup
  · intro i hl
    rw [hlife] at hl
    rw [hrost]
    exact hO.aliveIn i hl
  · intro nm k g1 g2 h1 h2 hl1 hl2
    apply hO.indexed nm k g1 g2 (by rw [hrost] at h1; exact h1) (by rw [hrost] at h2; exact h2)
    · rw [hlife] at hl1; exact hl1
    · rw [hlife] at hl2; exact hl2
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
    have hmail := hoff i hnin'
    rw [hmail.1, hmail.2]
    exact hold
  · intro i m hm
    rw [hrost]
    exact hbox i m hm
  · intro i p hp
    rw [hrost]
    exact hpark i p hp
  · intro i p hp
    exact hpm i p hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro nm k live d hfind
      have hfind0 : findLive w nm k = some live := by
        rw [findLive_life w w' hrost hlife nm k] at hfind
        exact hfind
      have hbal := hO.balance.1.1 nm k live d hfind0
      rw [hq nm k d]
      by_cases hs : live = sender
      · have hbit : queueDrop sender nm k d name = if d = name then (1 : Int) else 0 := by
          obtain ⟨g, hid⟩ := findLive_peer w nm k live hfind0
          rw [hs] at hid
          simp [queueDrop, keyDrop, hid]
        rw [hs] at hbal ⊢
        rw [hbit]
        have htk := htok d
        by_cases hd : d = name <;> simp [hd] at hbal htk ⊢ <;> omega
      · rw [htokO live hs d]
        have hzero : queueDrop sender nm k d name = 0 := by
          cases hsid : sender with
          | core _ => simp [queueDrop, keyDrop]
          | peer n kk g =>
            by_cases hk : n = nm ∧ kk = k
            · have hfl := findLive_of_alive w hO.indexed n kk g
                (by rw [← hsid]; exact hsend) (by rw [← hsid]; exact hsender)
              rw [hk.1, hk.2] at hfl hsid
              rw [hfl] at hfind0
              injection hfind0 with heq
              exact absurd (hsid.trans heq) (Ne.symm hs)
            · simp [queueDrop, keyDrop, hk]
        rw [hzero]
        exact hbal
    · intro nm d hl hmem
      have hl0 : (w.st (InstId.core nm)).life = .alive := by rw [hlife] at hl; exact hl
      have hmem0 : InstId.core nm ∈ w.roster := by rw [hrost] at hmem; exact hmem
      have hbal := hO.balance.1.2 nm d hl0 hmem0
      rw [hrost]
      by_cases hs : InstId.core nm = sender
      · rw [hs] at hbal ⊢
        have htk := htok d
        by_cases hd : d = name
        · rw [hd] at hbal htk ⊢
          simp at htk
          have hownc := hown sender
          simp at hownc
          rw [hownc, Int.natCast_add]
          omega
        · rw [hother d hd sender]
          simp [hd] at htk
          rw [htk]
          exact hbal
      · rw [htokO (InstId.core nm) hs d]
        by_cases hd : d = name
        · have hown' := hown (InstId.core nm)
          simp [hs] at hown'
          rw [hd] at hbal ⊢
          rw [hown']
          exact hbal
        · rw [hother d hd (InstId.core nm)]
          exact hbal
    · intro nm k d hnone
      have hnone0 : findLive w nm k = none := by
        rw [findLive_life w w' hrost hlife nm k] at hnone
        exact hnone
      rw [hq nm k d]
      have hzero : queueDrop sender nm k d name = 0 := by
        cases hsid : sender with
          | core _ => simp [queueDrop, keyDrop]
          | peer n kk g =>
            by_cases hk : n = nm ∧ kk = k
            · have hfl := findLive_of_alive w hO.indexed n kk g
                (by rw [← hsid]; exact hsend) (by rw [← hsid]; exact hsender)
              rw [hk.1, hk.2] at hfl
              rw [hfl] at hnone0
              cases hnone0
            · simp [queueDrop, keyDrop, hk]
      rw [hzero]
      exact hO.balance.2 nm k d hnone0
  · intro s d hl
    have hl0 : (w.st s).life = .alive := by rw [hlife] at hl; exact hl
    by_cases hs : s = sender
    · rw [hs] at hl ⊢
      have hold := hO.slack sender d hsender
      have hle := hhold d
      have htk := htok d
      omega
    · have hph : (w'.st s).phase = (w.st s).phase := hphO s hs
      have hty : (w'.st s).typestate = (w.st s).typestate := htyO s hs
      have htk := htokO s hs d
      rw [htk]
      have hsame : tokenHold I.desc (tname s) d (w'.st s) = tokenHold I.desc (tname s) d (w.st s) := by
        simp [tokenHold, hph, hty]
      rw [hsame]
      exact hO.slack s d hl0
  · intro s d hs hterm
    rw [hrost] at hs ⊢
    by_cases hss : s = sender
    · rw [hss] at hs ⊢
      by_cases hd : d = name
      · rw [hd]
        have htermS : loneTerminableName I.desc (tname sender) := by
          rw [← hss]; exact hterm
        obtain ⟨t, ht, hmul, _, _⟩ := htermS
        obtain ⟨u, hu, hsh⟩ := hO.shaped sender hs
        have hu' : templateOf I.desc (tname sender) = some u := hu
        rw [ht] at hu'
        cases hu'
        simp only [hmul] at hsh
        obtain ⟨k, g, hid0⟩ := hsh
        have hnm : t.name = tname sender := templateOf_name I.desc (tname sender) t ht
        have hid : sender = InstId.peer (tname sender) k g := by rw [hnm] at hid0; exact hid0
        have hsP : InstId.peer (tname sender) k g ∈ w.roster := by rw [← hid]; exact hs
        have hlP : (w.st (InstId.peer (tname sender) k g)).life = .alive := by
          rw [← hid]; exact hsender
        have hlive := findLive_of_alive w hO.indexed (tname sender) k g hsP hlP
        have hfind : findLive w (tname sender) k = some sender := by rw [← hid] at hlive; exact hlive
        have hbal := hO.balance.1.1 (tname sender) k sender name hfind
        have howed : owed w.st name sender w.roster ≤ queuedFromKey w (tname sender) k name := by
          rw [hid]; exact owed_peer_le_queued w (tname sender) k g name hO.parkMsg
        have hown' : owed w'.st name sender w.roster = owed w.st name sender w.roster + 1 := by
          simpa using hown sender
        have htk : (w'.st sender).tokens name + 1 = (w.st sender).tokens name := by
          simpa using htok name
        have hold := hO.slack sender name hsender
        have hhold1 : (tokenHold I.desc (tname sender) name (w'.st sender) : Int) + 1 ≤
            (tokenHold I.desc (tname sender) name (w.st sender) : Int) := by
          simpa using hhold name
        have hone : (1 : Int) ≤ (w.st sender).tokens name := by
          have hnn : (0 : Int) ≤ (tokenHold I.desc (tname sender) name (w'.st sender) : Int) :=
            Int.natCast_nonneg _
          omega
        have hqle : (queuedFromKey w (tname sender) k name : Int) + 1 ≤
            (budget I.desc (tname sender) name : Int) := by
          omega
        rw [hown']
        apply Int.ofNat_le.mp
        rw [Int.natCast_add (owed w.st name sender w.roster) 1]
        have howI : (owed w.st name sender w.roster : Int) ≤
            (queuedFromKey w (tname sender) k name : Int) := Int.ofNat_le.mpr howed
        omega
      · have htermS : loneTerminableName I.desc (tname sender) := by
          rw [← hss]; exact hterm
        have h0 := hO.still sender d hs htermS
        rw [hother d hd sender]
        exact h0
    · have h0 := hO.still s d hs hterm
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s]
        exact h0
  · intro hcrash s d hs hdead
    have hc : w.crashed = false := hcr.symm.trans hcrash
    rw [hrost] at hs ⊢
    have hdead0 : (w.st s).life ≠ .alive := by rw [hlife] at hdead; exact hdead
    by_cases hss : s = sender
    · rw [hss] at hdead0
      exact absurd hsender hdead0
    · have h0 := hO.quiet hc s d hs hdead0
      by_cases hd : d = name
      · rw [hd] at h0 ⊢
        have hown' := hown s
        simp [hss] at hown'
        rw [hown']
        exact h0
      · rw [hother d hd s]
        exact h0
  · intro hcrash i hdead
    have hne : (w'.st i).life ≠ .alive := by
      rcases hdead with h | h
      · rw [h]; intro he; cases he
      · rw [h]; intro he; cases he
    exact hdeadE hcrash i hne
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      have hk := (hkey host).1 m hm
      unfold queueOk at hk ⊢
      exact hk
    · intro p hp
      have hk := (hkey host).2 p hp
      unfold queueOk at hk ⊢
      exact hk
  · intro i hi
    exact hO.shaped i (by rw [hrost] at hi; exact hi)
  · exact hfrom
  · exact ixFresh_copy I.desc w w' hO.ixFresh hrost hix

theorem charge_keeps (a : Actor) (dst : String) :
    (chargeSender a dst).life = a.life ∧ (chargeSender a dst).typestate = a.typestate ∧
      (chargeSender a dst).phase = a.phase ∧ (chargeSender a dst).box = a.box ∧
      (chargeSender a dst).parked = a.parked := by
  simp [chargeSender, bumpToken]

/-- The continuation a call actually waits on. The step stores that call's
outcome lists, not the ones the outer continuation was carrying. -/
def callWait (k : Cont) : Eff → Cont
  | .call _ _ _ na to => { afterHead k with onNotAdmitted := na, onTimedOut := to }
  | _ => afterHead k

/-- A parked call's tight reserve, plus the token already charged, fits under
the running call. `NotAdmitted` is one slot lower while that token is out. -/
theorem reserve_park (tail na timed own : Nat) :
    max tail (max (na - own) timed) + own ≤ max (own + tail) (max na (own + timed)) := by
  omega

/-- Waiting keeps the tail and the call's own timeout, and the spent token is
the same `own` the effect's reserve already added on both of those paths. -/
theorem reserve_wait (tail timed admitted own : Nat) :
    max tail timed + own ≤ max (own + tail) (max admitted (own + timed)) := by
  cases Nat.le_total tail timed with
  | inl hle =>
    rw [Nat.max_eq_right hle, Nat.add_comm timed own]
    exact Nat.le_trans (Nat.le_max_right admitted (own + timed))
      (Nat.le_max_right (own + tail) _)
  | inr hle =>
    rw [Nat.max_eq_left hle, Nat.add_comm tail own]
    exact Nat.le_max_left (own + tail) _

theorem reserve_wait_one (tail timed admitted : Nat) :
    max tail timed + 1 ≤ max (1 + tail) (max admitted (1 + timed)) :=
  reserve_wait tail timed admitted 1

theorem reserve_wait_zero (tail timed admitted : Nat) :
    max tail timed ≤ max tail (max admitted timed) := by
  simpa using reserve_wait tail timed admitted 0

theorem tokenHold_call_wait (D : Description) (template dst name : String) (a : Actor) (k : Cont)
    (target : InstId) (na to : List Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k) (hk : k.rest = .call name label hint na to :: es) :
    tokenHold D template dst
        { a with phase := .awaitReply target (callWait k (.call name label hint na to)) } +
      (if dst = name then 1 else 0) ≤ tokenHold D template dst a := by
  simp [tokenHold, callWait, hph, afterHead, hk, pathReserve, effReserve, contAt, focus]
  by_cases hd : name = dst
  · have hb : (name == dst) = true := beq_iff_eq.mpr hd
    simp [hb, hd]
    exact reserve_wait_one _ _ _
  · have hne : ¬ dst = name := fun h => hd h.symm
    have hb : (name == dst) = false := by
      cases hbb : name == dst with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hbb) hd
    simp [hb, hd, hne]
    exact reserve_wait_zero _ _ _

theorem hold_ge_effect (D : Description) (template name : String) (a : Actor) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨
      (∃ full gone, e = .trySend name label hint full gone)) :
    1 ≤ tokenHold D template name a := by
  simp [tokenHold, pathReserve, hph, hk]
  have hb : (name == name) = true := beq_iff_eq.mpr rfl
  rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp [effReserve, hb]
  · simp [effReserve, hb]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)
  · simp [effReserve, hb]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)

theorem charge_tok (a : Actor) (name d : String) (h : 1 ≤ a.tokens name) :
    (chargeSender a name).tokens d + (if d = name then 1 else 0) = a.tokens d := by
  by_cases hd : d = name
  · simp [hd, charge_at a name h]
  · simp [hd, charge_skip a name d hd]

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
            [{ msg with
               mid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid,
               callId := some (issueCall (chargeSender (w.st sender) (tname sender))).waitId }],
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
        box := (w.st dst).box ++ [{ msg with
          mid := (w.st dst).nextMid,
          callId := some (issueCall (chargeSender (w.st sender) (tname dst))).waitId }],
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
                   else chargeSender (w.st sender) (tname sender)).nextMid,
                 callId := if isCall then
                   some (issueCall (chargeSender (w.st sender) (tname sender))).waitId
                 else msg.callId },
               isCall := isCall }],
          nextMid := (if isCall then issueCall (chargeSender (w.st sender) (tname sender))
            else chargeSender (w.st sender) (tname sender)).nextMid + 1,
          phase := .parked sender isCall k } := by
  by_cases hp : (w.st sender).parked = []
  · by_cases hc : (w.st sender).box.length < capBulk D w.N sender
    · exact (hroom ⟨hp, hc⟩).elim
    · have hdec : decide ((w.st sender).box.length < capBulk D w.N sender) = false := by
        cases h : decide ((w.st sender).box.length < capBulk D w.N sender) with
        | true => exact absurd (of_decide_eq_true h) hc
        | false => rfl
      cases isCall <;> simp [enqueueOrPark, issueCall, hlive, hp, hdec]
  · have hdec : decide ((w.st sender).parked = []) = false := by
      cases h : decide ((w.st sender).parked = []) with
      | true => exact absurd (of_decide_eq_true h) hp
      | false => rfl
    cases isCall <;> simp [enqueueOrPark, issueCall, hlive, hdec]

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
                 msg := { msg with
                   mid := (w.st dst).nextMid,
                   callId := if isCall then
                     some (issueCall (chargeSender (w.st sender) (tname dst))).waitId
                   else msg.callId },
                 isCall := isCall }],
            nextMid := (w.st dst).nextMid + 1 })
        sender
        { (if isCall then issueCall (chargeSender (w.st sender) (tname dst))
            else chargeSender (w.st sender) (tname dst)) with phase := .parked dst isCall k } := by
  by_cases hp : (w.st dst).parked = []
  · by_cases hc : (w.st dst).box.length < capBulk D w.N dst
    · exact (hroom ⟨hp, hc⟩).elim
    · have hdec : decide ((w.st dst).box.length < capBulk D w.N dst) = false := by
        cases h : decide ((w.st dst).box.length < capBulk D w.N dst) with
        | true => exact absurd (of_decide_eq_true h) hc
        | false => rfl
      cases isCall <;> simp [enqueueOrPark, issueCall, hlive, hne, hp, hdec]
  · have hdec : decide ((w.st dst).parked = []) = false := by
      cases h : decide ((w.st dst).parked = []) with
      | true => exact absurd (of_decide_eq_true h) hp
      | false => rfl
    cases isCall <;> simp [enqueueOrPark, issueCall, hlive, hne, hdec]

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
    (hown : ∀ s, owed (fun i => if i = sender then aS else w.st i) name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s,
      owed (fun i => if i = sender then aS else w.st i) d s w.roster = owed w.st d s w.roster)
    (hbox : ∀ m ∈ aS.box, m.sender ∈ w.roster) (hpark : ∀ p ∈ aS.parked, p.sender ∈ w.roster)
    (hpm : ∀ p ∈ aS.parked, p.sender = p.msg.sender)
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hkeyB : ∀ m ∈ aS.box, queueOk I.desc w m.sender sender)
    (hkeyP : ∀ p ∈ aS.parked, queueOk I.desc w p.sender sender)
    (hdeadA : aS.life ≠ .alive → aS.box = [] ∧ aS.parked = [])
    (hfromB : peerKey sender = none → ∀ m ∈ aS.box, coreSender I.desc m.sender)
    (hfromP : peerKey sender = none → ∀ p ∈ aS.parked, coreSender I.desc p.sender)
    (hq : ∀ nm k d,
      (queuedFromKey (setActor w sender aS) nm k d : Int) =
        (queuedFromKey w nm k d : Int) + queueDrop sender nm k d name)
    (hhold : ∀ d, (tokenHold I.desc (tname sender) d aS : Int) +
        (if d = name then (1 : Int) else 0) ≤
      (tokenHold I.desc (tname sender) d (w.st sender) : Int)) :
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
  · intro i hnin
    have hne : i ≠ sender := fun heq => hnin (heq ▸ hsend)
    rw [hst i]
    simp [hne]
  · exact hsend
  · exact hsender
  · intro hcrash i hdead
    rw [hst i] at hdead ⊢
    by_cases hs : i = sender
    · simp [hs] at hdead ⊢
      exact hdeadA hdead
    · simp [hs] at hdead ⊢
      have hc : w.crashed = false := by simpa [w', setActor] using hcrash
      have hor : (w.st i).life = .absent ∨ (w.st i).life = .dead := by
        cases hL : (w.st i).life
        · exact Or.inl rfl
        · exact absurd hL hdead
        · exact Or.inr rfl
      exact hO.deadEmpty hc i hor
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
  · simp [w', setActor]
  · intro nm k d
    simpa [w', setActor] using hq nm k d
  · intro d
    have hs : w'.st sender = aS := by simp [w', setActor]
    simpa [hs] using hhold d

theorem occ_self_call (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : ∃ na to, e = .call (tname sender) label hint na to)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg true (callWait k e)) := by
  obtain ⟨na, to, hc⟩ := he
  have hmem := hO.aliveIn sender hsender
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname sender) (w.st sender) k e es label hint hph hk
      (Or.inr (Or.inl ⟨na, to, hc⟩))
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_room_self_call w I.desc sender msg (callWait k e) hsender hpark hcap]
  let issued : Msg :=
    { msg with
      mid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid,
      callId := some (issueCall (chargeSender (w.st sender) (tname sender))).waitId }
  let aS : Actor :=
    { issueCall (chargeSender (w.st sender) (tname sender)) with
      box := (issueCall (chargeSender (w.st sender) (tname sender))).box ++ [issued],
      nextMid := (issueCall (chargeSender (w.st sender) (tname sender))).nextMid + 1,
      phase := .awaitReply sender (callWait k e) }
  suffices OccInv I (setActor w sender aS) by simpa [aS, issued] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, hcl]
  · simp [aS, hcty]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname sender)).tokens d := by simp [aS]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro s
    exact owed_self_box w.st (tname sender) sender aS issued
      w.roster hO.nodup hmem rfl (by simpa [issued] using hmsg)
      (by simp [aS, issued, hcb]) (by simp [aS, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++ [issued] := by
      simpa [aS, issued, hcb] using hm
    simp [List.mem_append, List.mem_singleton] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom sender m h
    | inr h => simpa [h, issued, hmsg] using hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkMsg sender p hp'
  · exact hmem
  · exact hsender
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++ [issued] := by
      simpa [aS, issued, hcb] using hm
    simp [List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey sender).1 m hm'
    · simp [hm', issued, hmsg]
      exact queueOk_alive w sender sender (key_refl I.desc sender) hsender
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro hdead
    exact absurd (by simp [aS, hcl]; exact hsender) hdead
  · intro hk m hm
    have hm' : m ∈ (w.st sender).box ++ [issued] := by
      simpa [aS, issued, hcb] using hm
    simp [List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.coreFrom sender hk).1 m hm'
    · exact Or.inl (by simpa [hm', issued, hmsg] using hk)
  · intro hk p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.coreFrom sender hk).2 p hp'
  · intro nm key d
    have hbox : aS.box = (w.st sender).box ++ [issued] := by simp [aS, issued, hcb]
    have hparkA : aS.parked = (w.st sender).parked := by simp [aS, hcp]
    have happ := queuedFromKey_append w sender aS issued nm key d hO.nodup hmem hbox hparkA
    rw [happ, Int.natCast_add]
    have hcast :
        ((if (tname sender != d) = true then 0
          else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname sender) := by
      have hswap :
          ((if (tname sender != d) = true then 0
            else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
            if d = tname sender then if keyPred nm key issued = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname sender = d
        · by_cases hk' : keyPred nm key issued = true <;> simp [ht, hk', bne]
        · have hne : ¬ d = tname sender := fun h => ht h.symm
          by_cases hk' : keyPred nm key issued = true <;> simp [ht, hne, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender issued nm key d (tname sender) (by simp [issued, hmsg])
    rw [hcast]
  · intro d
    have hk' : k.rest = .call (tname sender) label hint na to :: es := by rw [hc] at hk; exact hk
    have hwait := tokenHold_call_wait I.desc (tname sender) d (tname sender) (w.st sender) k sender na to es
      label hint hph hk'
    have hphase : aS.phase = .awaitReply sender (callWait k e) := by simp [aS]
    have hsame : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d { (w.st sender) with phase := aS.phase } := by
      simp [tokenHold, aS, hphase]
    rw [hsame, hphase, hc, callWait]
    have hcast : ((if d = tname sender then 1 else 0 : Nat) : Int) =
        if d = tname sender then (1 : Int) else 0 := by
      by_cases hd : d = tname sender <;> simp [hd]
    have hle := Int.ofNat_le.mpr hwait
    rw [Int.natCast_add, hcast] at hle
    exact hle

/-- A head send, call, or try-send reserves at least the token it spends plus
the tail that `proceed` keeps. -/
theorem effReserve_ge_send (D : Description) (template dst name : String) (at_ : BranchAt)
    (e : Eff) (tail : Nat) (label : String) (hint : Nat)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨
      (∃ full gone, e = .trySend name label hint full gone)) :
    (if dst = name then 1 else 0) + tail ≤ effReserve D template dst at_ e tail := by
  have hbit : (if dst = name then 1 else 0) = (if name == dst then 1 else 0) := by
    by_cases hd : name = dst
    · have hb : (name == dst) = true := beq_iff_eq.mpr hd
      simp [hd.symm, hb]
    · have hne : ¬ dst = name := fun h => hd h.symm
      have hb : (name == dst) = false := by
        cases hbb : name == dst with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hbb) hd
      simp [hd, hne, hb]
  rw [hbit]
  rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp [effReserve]
  · simp [effReserve]
    exact Nat.le_max_left _ _
  · simp [effReserve]
    exact Nat.le_max_left _ _

theorem tokenHold_proceed_head (D : Description) (template dst name : String) (a : Actor) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨
      (∃ full gone, e = .trySend name label hint full gone)) :
    tokenHold D template dst (proceed a (afterHead k)) + (if dst = name then 1 else 0) ≤
      tokenHold D template dst a := by
  have hrest : (afterHead k).rest = es := by simp [afterHead, hk]
  have hat : contAt (afterHead k) = contAt k := by simp [contAt, afterHead]
  have hto : (afterHead k).toState = k.toState := by simp [afterHead]
  have hnew : tokenHold D template dst (proceed a (afterHead k)) =
      pathReserve D template dst (contAt k) es := by
    cases es with
    | nil =>
      simp [proceed, tokenHold, hrest, pathReserve, landFloor, hat, hto, contAt]
    | cons _ _ =>
      simp [proceed, tokenHold, hrest, hat]
  have hold : tokenHold D template dst a =
      effReserve D template dst (contAt k) e (pathReserve D template dst (contAt k) es) := by
    simp [tokenHold, hph, hk, pathReserve]
  rw [hnew, hold, Nat.add_comm]
  exact effReserve_ge_send D template dst name (contAt k) e
    (pathReserve D template dst (contAt k) es) label hint he

/-- A non-call park keeps the tail and drops the head, the same split `proceed`
uses. The parked phase does not recount the message: the charge did. -/
theorem tokenHold_park_false (D : Description) (template dst name : String) (a : Actor) (k : Cont)
    (target : InstId) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send name label hint ∨ (∃ na to, e = .call name label hint na to) ∨
      (∃ full gone, e = .trySend name label hint full gone)) :
    tokenHold D template dst { a with phase := .parked target false (afterHead k) } +
      (if dst = name then 1 else 0) ≤ tokenHold D template dst a := by
  have hrest : (afterHead k).rest = es := by simp [afterHead, hk]
  have hat : contAt (afterHead k) = contAt k := by simp [contAt, afterHead]
  have hnew : tokenHold D template dst { a with phase := .parked target false (afterHead k) } =
      pathReserve D template dst (contAt k) es := by
    simp [tokenHold, hrest, hat]
  have hold : tokenHold D template dst a =
      effReserve D template dst (contAt k) e (pathReserve D template dst (contAt k) es) := by
    simp [tokenHold, hph, hk, pathReserve]
  rw [hnew, hold, Nat.add_comm]
  exact effReserve_ge_send D template dst name (contAt k) e
    (pathReserve D template dst (contAt k) es) label hint he

/-- A parked call spends the token the running reserve already held. The
phase does not count that message again, drops a stale peer timeout, and
lowers `NotAdmitted` by the refund that precedes it. -/
theorem tokenHold_park_call (D : Description) (template slot name : String) (a : Actor) (k : Cont)
    (target : InstId) (na to : List Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k) (hk : k.rest = .call name label hint na to :: es)
    (ht : tname target = name) :
    tokenHold D template slot
        { a with phase := .parked target true (callWait k (.call name label hint na to)) } +
      (if slot = name then 1 else 0) ≤
      tokenHold D template slot a := by
  simp [tokenHold, callWait, hph, afterHead, hk, pathReserve, effReserve, contAt, focus, ht]
  by_cases hd : name = slot
  · have hb : (name == slot) = true := beq_iff_eq.mpr hd
    simp [hb, hd]
    exact reserve_park _ _ _ 1
  · have hne : ¬ slot = name := fun h => hd h.symm
    have hb : (name == slot) = false := by
      cases hbb : name == slot with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hbb) hd
    simp [hb, hd, hne]

/-- One arm of a `trySend` lands in the typestate that arm's reserve checked. -/
theorem tokenHold_try_arm (D : Description) (template slot name : String) (a : Actor) (k : Cont)
    (label : String) (hint : Nat) (onFull onGone arm : List Eff) (toArm : String) (es : List Eff)
    (hph : a.phase = .run k)
    (hk : k.rest = .trySend name label hint onFull onGone :: es)
    (hwhich : (arm = onFull ∧ toArm = k.toFull) ∨ (arm = onGone ∧ toArm = k.toGone)) :
    tokenHold D template slot
        (proceed a { afterHead k with rest := arm, toState := pickState (afterHead k).toState toArm }) ≤
      tokenHold D template slot a := by
  let kA := { afterHead k with rest := arm, toState := pickState (afterHead k).toState toArm }
  have hfocus : contAt kA = focus (contAt k) toArm := by
    rcases hwhich with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [kA, contAt, afterHead, focus, pickState]
  have hold : tokenHold D template slot a =
      effReserve D template slot (contAt k) (.trySend name label hint onFull onGone)
        (pathReserve D template slot (contAt k) es) := by
    simp [tokenHold, hph, hk, pathReserve]
  rw [hold]
  rcases hwhich with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases harm : arm with
    | nil =>
      simp [tokenHold, proceed, kA, harm, pathReserve, effReserve, contAt, focus, pickState,
        afterHead, landFloor, hfocus]
      omega
    | cons _ _ =>
      simp [tokenHold, proceed, kA, harm, pathReserve, effReserve, contAt, focus, pickState,
        afterHead, hfocus]
      omega
  · cases harm : arm with
    | nil =>
      simp [tokenHold, proceed, kA, harm, pathReserve, effReserve, contAt, focus, pickState,
        afterHead, landFloor, hfocus]
      omega
    | cons _ _ =>
      simp [tokenHold, proceed, kA, harm, pathReserve, effReserve, contAt, focus, pickState,
        afterHead, hfocus]
      omega

theorem tokenHold_internal (D : Description) (template dst : String) (a : Actor) (k : Cont)
    (es : List Eff) (hph : a.phase = .run k) (hk : k.rest = .internal :: es) :
    tokenHold D template dst { a with phase := .awaitEffect (afterHead k) } ≤
      tokenHold D template dst a := by
  simp [tokenHold, afterHead, hk, pathReserve, effReserve, contAt, hph]

theorem tokenHold_peer (D : Description) (template dst : String) (a : Actor) (k : Cont)
    (onTimeout es : List Eff) (hph : a.phase = .run k) (hk : k.rest = .peer onTimeout :: es) :
    tokenHold D template dst
        { a with phase := .awaitPeer { afterHead k with onTimeout := onTimeout } } ≤
      tokenHold D template dst a := by
  simp [tokenHold, afterHead, hk, pathReserve, effReserve, contAt, focus, hph]

/-- The continuation a missed call actually runs. `selectCall` lands in the
typestate the reserve already checked for `NotAdmitted`. -/
theorem contAt_not_admitted (k : Cont) (na to : List Eff) :
    contAt (selectCall { afterHead k with onNotAdmitted := na, onTimedOut := to } .notAdmitted) =
      focus (contAt k) k.toNotAdmitted := by
  simp [contAt, selectCall, focus, pickState, afterHead]

/-- A call that is not admitted spends no token and runs only `onNotAdmitted`.
That path is one branch of the call's reserve. -/
theorem tokenHold_miss (D : Description) (template dst name : String) (a : Actor) (k : Cont)
    (na to : List Eff) (es : List Eff) (label : String) (hint : Nat)
    (hph : a.phase = .run k)
    (hk : k.rest = .call name label hint na to :: es) :
    tokenHold D template dst
        (finishCall (issueCall a) (callWait k (.call name label hint na to)) .notAdmitted) ≤
      tokenHold D template dst a := by
  have hct :
      contAt (selectCall (callWait k (.call name label hint na to)) .notAdmitted) =
        focus (contAt k) k.toNotAdmitted := by
    simp [callWait, hk, contAt_not_admitted]
  have hrest :
      (selectCall (callWait k (.call name label hint na to)) .notAdmitted).rest = na := by
    simp [selectCall, callWait, hk]
  have hnew :
      tokenHold D template dst
          (finishCall (issueCall a) (callWait k (.call name label hint na to)) .notAdmitted) =
        pathReserve D template dst (focus (contAt k) k.toNotAdmitted) na := by
    cases na with
    | nil =>
      simp [finishCall, issueCall, proceed, tokenHold, pathReserve, hrest, hct, selectCall, callWait,
        hk, afterHead, contAt, focus, pickState]
    | cons _ _ =>
      simp [finishCall, issueCall, proceed, tokenHold, hrest, hct]
  have hold :
      tokenHold D template dst a =
        effReserve D template dst (contAt k) (.call name label hint na to)
          (pathReserve D template dst (contAt k) es) := by
    simp [tokenHold, hph, hk, pathReserve]
  rw [hnew, hold]
  simp [effReserve, contAt]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem occ_self_send (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ (∃ na to, e = .call (tname sender) label hint na to) ∨
      (∃ full gone, e = .trySend (tname sender) label hint full gone))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname sender) (w.st sender) k e es label hint
      hph hk he
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
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
  · exact hmem
  · exact hsender
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++
        [{ msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }] := by
      simpa [aS, base, proceed_box, hcb] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey sender).1 m hm'
    · rw [hm', hmsg]
      exact queueOk_alive w sender sender (key_refl I.desc sender) hsender
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
  · intro nm key d
    let issued : Msg := { msg with mid := (chargeSender (w.st sender) (tname sender)).nextMid }
    have hbox : aS.box = (w.st sender).box ++ [issued] := by
      simp [aS, base, proceed_box, hcb, issued]
    have hparkA : aS.parked = (w.st sender).parked := by
      simp [aS, base, proceed_parked, hcp]
    have happ := queuedFromKey_append w sender aS issued nm key d hO.nodup hmem hbox hparkA
    rw [happ, Int.natCast_add]
    have hcast :
        ((if (tname sender != d) = true then 0
          else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname sender) := by
      have hswap :
          ((if (tname sender != d) = true then 0
            else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
            if d = tname sender then if keyPred nm key issued = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname sender = d
        · by_cases hk' : keyPred nm key issued = true <;> simp [ht, hk', bne]
        · have hne : ¬ d = tname sender := fun h => ht h.symm
          by_cases hk' : keyPred nm key issued = true <;> simp [ht, hne, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender issued nm key d (tname sender) (by simp [issued, hmsg])
    rw [hcast]
  · intro d
    have hsame : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d (proceed (w.st sender) (afterHead k)) := by
      cases hrest : (afterHead k).rest with
      | nil => simp [tokenHold, aS, base, proceed, hrest]
      | cons _ _ => simp [tokenHold, aS, base, proceed, hrest]
    rw [hsame]
    have hNat := tokenHold_proceed_head I.desc (tname sender) d (tname sender) (w.st sender) k e es
      label hint hph hk he
    have hcast : ((if d = tname sender then 1 else 0 : Nat) : Int) =
        if d = tname sender then (1 : Int) else 0 := by
      by_cases hd : d = tname sender <;> simp [hd]
    have hle := Int.ofNat_le.mpr hNat
    rw [Int.natCast_add, hcast] at hle
    exact hle

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
    (hown : ∀ s, owed (fun i => if i = sender then aS else if i = dst then aD else w.st i) name s w.roster =
      owed w.st name s w.roster + if s = sender then 1 else 0)
    (hother : ∀ d, d ≠ name → ∀ s,
      owed (fun i => if i = sender then aS else if i = dst then aD else w.st i) d s w.roster =
        owed w.st d s w.roster)
    (hboxS : ∀ m ∈ aS.box, m.sender ∈ w.roster) (hboxD : ∀ m ∈ aD.box, m.sender ∈ w.roster)
    (hparkS : ∀ p ∈ aS.parked, p.sender ∈ w.roster) (hparkD : ∀ p ∈ aD.parked, p.sender ∈ w.roster)
    (hpmS : ∀ p ∈ aS.parked, p.sender = p.msg.sender) (hpmD : ∀ p ∈ aD.parked, p.sender = p.msg.sender)
    (hsend : sender ∈ w.roster) (hdst : dst ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hkeyBS : ∀ m ∈ aS.box, queueOk I.desc w m.sender sender)
    (hkeyPS : ∀ p ∈ aS.parked, queueOk I.desc w p.sender sender)
    (hkeyBD : ∀ m ∈ aD.box, queueOk I.desc w m.sender dst)
    (hkeyPD : ∀ p ∈ aD.parked, queueOk I.desc w p.sender dst)
    (hdeadS : aS.life ≠ .alive → aS.box = [] ∧ aS.parked = [])
    (hdeadD : aD.life ≠ .alive → aD.box = [] ∧ aD.parked = [])
    (hfromS : peerKey sender = none →
      (∀ m ∈ aS.box, coreSender I.desc m.sender) ∧
      (∀ p ∈ aS.parked, coreSender I.desc p.sender))
    (hfromD : peerKey dst = none →
      (∀ m ∈ aD.box, coreSender I.desc m.sender) ∧
      (∀ p ∈ aD.parked, coreSender I.desc p.sender))
    (hq : ∀ nm k d,
      (queuedFromKey (setActor (setActor w dst aD) sender aS) nm k d : Int) =
        (queuedFromKey w nm k d : Int) + queueDrop sender nm k d name)
    (hhold : ∀ d, (tokenHold I.desc (tname sender) d aS : Int) +
        (if d = name then (1 : Int) else 0) ≤
      (tokenHold I.desc (tname sender) d (w.st sender) : Int)) :
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
  · intro i hnin
    have hneS : i ≠ sender := fun heq => hnin (heq ▸ hsend)
    have hneD : i ≠ dst := fun heq => hnin (heq ▸ hdst)
    rw [hst i]
    simp [hneS, hneD]
  · exact hsend
  · exact hsender
  · intro hcrash i hdead
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
        have hc : w.crashed = false := by simpa [w', setActor] using hcrash
        have hor : (w.st i).life = .absent ∨ (w.st i).life = .dead := by
          cases hL : (w.st i).life
          · exact Or.inl rfl
          · exact absurd hL hdead
          · exact Or.inr rfl
        exact hO.deadEmpty hc i hor
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
  · simp [w', setActor]
  · intro nm k d
    simpa [w', setActor] using hq nm k d
  · intro d
    have hs : w'.st sender = aS := by simp [w', setActor]
    simpa [hs] using hhold d

/-- A full self mailbox parks the message. The phase is `kP`: the tail for a
send, the call's own outcomes for a call. The caller shows that spending the
token keeps `tokenHold` under the reserve the running phase already held. -/
theorem occ_self_park (I : Impl) (_hL : LocalOk I) (w : World) (sender : InstId) (msg : Msg)
    (isCall : Bool) (k kP : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (_hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ (∃ na to, e = .call (tname sender) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hroom : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk I.desc w.N sender))
    (hhold : ∀ d,
      tokenHold I.desc (tname sender) d
          { (w.st sender) with phase := .parked sender isCall kP } +
        (if d = tname sender then 1 else 0) ≤
        tokenHold I.desc (tname sender) d (w.st sender)) :
    OccInv I (enqueueOrPark w I.desc sender sender msg isCall kP) := by
  have hmem := hO.aliveIn sender hsender
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname sender) (w.st sender) k e es label hint
      hph hk (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_park_self w I.desc sender msg isCall kP hsender hroom]
  let charged := chargeSender (w.st sender) (tname sender)
  let base := if isCall then issueCall charged else charged
  let issued : Msg :=
    { msg with mid := base.nextMid, callId := if isCall then some base.waitId else msg.callId }
  let entry : Parked := { sender := sender, msg := issued, isCall := isCall }
  let aS : Actor :=
    { base with
        parked := base.parked ++ [entry]
        nextMid := base.nextMid + 1
        phase := Phase.parked sender isCall kP }
  have hbl : base.life = charged.life := by cases isCall <;> simp [base, issueCall]
  have hbty : base.typestate = charged.typestate := by cases isCall <;> simp [base, issueCall]
  have hbbox : base.box = charged.box := by cases isCall <;> simp [base, issueCall]
  have hbpark : base.parked = charged.parked := by cases isCall <;> simp [base, issueCall]
  have hbtok : ∀ d, base.tokens d = charged.tokens d := by
    intro d; cases isCall <;> simp [base, issueCall]
  suffices OccInv I (setActor w sender aS) by
    cases isCall <;> simpa [aS, base, charged, entry, issued, issueCall] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, hbl, hcl, charged]
  · simp [aS, hbty, hcty, charged]
  · intro d
    have htk : aS.tokens d = charged.tokens d := by simp [aS, hbtok]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro s
    exact owed_self_park w.st (tname sender) sender aS entry w.roster hO.nodup hmem rfl rfl
      (by simp [aS, hbbox, hcb, charged]) (by simp [aS, hbpark, hcp, charged]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
    exact hO.sentFrom sender m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hbpark, hcp, charged] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom sender p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hbpark, hcp, charged] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkMsg sender p h
    | inr h => simp [h, entry, issued, hmsg]
  · exact hmem
  · exact hsender
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hbpark, hcp, charged] using hp
    simp [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact (hO.sameKey sender).2 p hp'
    · simp [hp', entry]
      exact queueOk_alive w sender sender (key_refl I.desc sender) hsender
  · intro hdead
    exact absurd (by simp [aS, hbl, hcl, charged]; exact hsender) hdead
  · intro hk m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
    exact (hO.coreFrom sender hk).1 m hm'
  · intro hk p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hbpark, hcp, charged] using hp
    simp [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact (hO.coreFrom sender hk).2 p hp'
    · exact Or.inl (by simp [hp', entry, hmsg, hk])
  · intro nm key d
    have hbox : aS.box = (w.st sender).box := by simp [aS, hbbox, hcb, charged]
    have hparkA : aS.parked = (w.st sender).parked ++ [entry] := by
      simp [aS, hbpark, hcp, charged]
    have happ := queuedFromKey_park w sender aS entry nm key d hO.nodup hmem hbox hparkA
    rw [happ, Int.natCast_add]
    have hcast :
        ((if (tname sender != d) = true then 0
          else if keyPred nm key entry.msg = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname sender) := by
      have hswap :
          ((if (tname sender != d) = true then 0
            else if keyPred nm key entry.msg = true then 1 else 0 : Nat) : Int) =
            if d = tname sender then if keyPred nm key entry.msg = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname sender = d
        · by_cases hk' : keyPred nm key entry.msg = true <;> simp [ht, hk', bne]
        · have hne : ¬ d = tname sender := fun h => ht h.symm
          by_cases hk' : keyPred nm key entry.msg = true <;> simp [ht, hne, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender entry.msg nm key d (tname sender) (by simp [entry, issued, hmsg])
    rw [hcast]
  · intro d
    have hsame : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d
          { (w.st sender) with phase := .parked sender isCall kP } := by
      cases isCall <;> simp [tokenHold, aS, hbty, hcty]
    rw [hsame]
    have hNat := hhold d
    have hbit : ((if d = tname sender then 1 else 0 : Nat) : Int) =
        if d = tname sender then (1 : Int) else 0 := by
      by_cases hd : d = tname sender <;> simp [hd]
    have hle := Int.ofNat_le.mpr hNat
    rw [Int.natCast_add, hbit] at hle
    exact hle

theorem occ_other_call (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : ∃ na to, e = .call (tname dst) label hint na to)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst)
    (hagree : keyAgrees I.desc sender dst)
    (hcore : peerKey dst = none → coreSender I.desc sender) :
    OccInv I (enqueueOrPark w I.desc sender dst msg true (callWait k e)) := by
  obtain ⟨na, to, hc⟩ := he
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname dst) (w.st sender) k e es label hint
      hph hk (Or.inr (Or.inl ⟨na, to, hc⟩))
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_room_other_call w I.desc sender dst msg (callWait k e) hlive hne hpark hcap]
  let issued : Msg :=
    { msg with mid := (w.st dst).nextMid, callId := some (issueCall (chargeSender (w.st sender) (tname dst))).waitId }
  let aD : Actor :=
    { (w.st dst) with box := (w.st dst).box ++ [issued], nextMid := (w.st dst).nextMid + 1 }
  let aS : Actor :=
    { issueCall (chargeSender (w.st sender) (tname dst)) with
      phase := .awaitReply dst (callWait k e) }
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by
    simpa [aS, aD, issued] using this
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
  · intro s
    exact owed_other_box w.st (tname dst) sender dst aS aD issued
      w.roster hO.nodup hdst hmem hne rfl (by simp [issued, hmsg])
      (by simp [aS, hcb]) (by simp [aS, hcp]) (by simp [aD, issued]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [issued] := by simpa [aD, issued] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom dst m h
    | inr h => simpa [h, issued, hmsg] using hmem
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
  · exact hmem
  · exact hdst
  · exact hsender
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact (hO.sameKey sender).2 p hp'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [issued] := by simpa [aD, issued] using hm
    simp [List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · exact (hO.sameKey dst).1 m hm'
    · simp [hm', issued, hmsg]
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
      have hm' : m ∈ (w.st dst).box ++ [issued] := by simpa [aD, issued] using hm
      simp [List.mem_append] at hm'
      rcases hm' with hm' | hm'
      · exact (hO.coreFrom dst hk).1 m hm'
      · simpa [hm', issued, hmsg] using hcore hk
    · intro p hp
      have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
      exact (hO.coreFrom dst hk).2 p hp'
  · intro nm key d
    let w1 := setActor w dst aD
    have hboxD : aD.box = (w.st dst).box ++ [issued] := by simp [aD, issued]
    have hparkD : aD.parked = (w.st dst).parked := by simp [aD]
    have happ := queuedFromKey_append w dst aD issued nm key d hO.nodup hdst hboxD hparkD
    have hboxS : aS.box = (w1.st sender).box := by simp [aS, w1, setActor, hne, issueCall, hcb]
    have hparkS : aS.parked = (w1.st sender).parked := by simp [aS, w1, setActor, hne, issueCall, hcp]
    have hset := queuedFromKey_set w1 sender aS hboxS hparkS nm key d
    rw [hset, happ, Int.natCast_add]
    have hcast :
        ((if (tname dst != d) = true then 0
          else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname dst) := by
      have hswap :
          ((if (tname dst != d) = true then 0
            else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
            if d = tname dst then if keyPred nm key issued = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname dst = d
        · by_cases hk' : keyPred nm key issued = true <;> simp [ht, hk', bne]
        · have hneD : ¬ d = tname dst := fun h => ht h.symm
          by_cases hk' : keyPred nm key issued = true <;> simp [ht, hneD, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender issued nm key d (tname dst) (by simp [issued, hmsg])
    rw [hcast]
  · intro d
    have hk' : k.rest = .call (tname dst) label hint na to :: es := by rw [hc] at hk; exact hk
    have hwait := tokenHold_call_wait I.desc (tname sender) d (tname dst) (w.st sender) k dst na to es
      label hint hph hk'
    have hphase : aS.phase = .awaitReply dst (callWait k e) := by simp [aS]
    have hsameP : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d { (w.st sender) with phase := aS.phase } := by
      simp [tokenHold, aS, hphase]
    rw [hsameP, hphase, hc, callWait]
    have hbit : ((if d = tname dst then 1 else 0 : Nat) : Int) =
        if d = tname dst then (1 : Int) else 0 := by
      by_cases hd : d = tname dst <;> simp [hd]
    have hle := Int.ofNat_le.mpr hwait
    rw [Int.natCast_add, hbit] at hle
    exact hle

theorem occ_other_send (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to) ∨
      (∃ full gone, e = .trySend (tname dst) label hint full gone))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive)
    (hne : sender ≠ dst) (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst)
    (hagree : keyAgrees I.desc sender dst)
    (hcore : peerKey dst = none → coreSender I.desc sender) :
    OccInv I (enqueueOrPark w I.desc sender dst msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname dst) (w.st sender) k e es label hint
      hph hk he
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
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
  · exact hmem
  · exact hdst
  · exact hsender
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
      · simpa [hm', hmsg] using hcore hk
    · intro p hp
      have hp' : p ∈ (w.st dst).parked := by simpa [aD] using hp
      exact (hO.coreFrom dst hk).2 p hp'
  · intro nm key d
    let w1 := setActor w dst aD
    let issued : Msg := { msg with mid := (w.st dst).nextMid }
    have hboxD : aD.box = (w.st dst).box ++ [issued] := by simp [aD, issued]
    have hparkD : aD.parked = (w.st dst).parked := by simp [aD]
    have happ := queuedFromKey_append w dst aD issued nm key d hO.nodup hdst hboxD hparkD
    have hboxS : aS.box = (w1.st sender).box := by
      simp [aS, w1, setActor, hne, charged, proceed_box, hcb]
    have hparkS : aS.parked = (w1.st sender).parked := by
      simp [aS, w1, setActor, hne, charged, proceed_parked, hcp]
    have hset := queuedFromKey_set w1 sender aS hboxS hparkS nm key d
    rw [hset, happ, Int.natCast_add]
    have hcast :
        ((if (tname dst != d) = true then 0
          else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname dst) := by
      have hswap :
          ((if (tname dst != d) = true then 0
            else if keyPred nm key issued = true then 1 else 0 : Nat) : Int) =
            if d = tname dst then if keyPred nm key issued = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname dst = d
        · by_cases hk' : keyPred nm key issued = true <;> simp [ht, hk', bne]
        · have hneD : ¬ d = tname dst := fun h => ht h.symm
          by_cases hk' : keyPred nm key issued = true <;> simp [ht, hneD, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender issued nm key d (tname dst) (by simp [issued, hmsg])
    rw [hcast]
  · intro d
    have hsame : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d (proceed (w.st sender) (afterHead k)) := by
      cases hrest : (afterHead k).rest with
      | nil => simp [tokenHold, aS, charged, proceed, hrest]
      | cons _ _ => simp [tokenHold, aS, charged, proceed, hrest]
    rw [hsame]
    have hNat := tokenHold_proceed_head I.desc (tname sender) d (tname dst) (w.st sender) k e es
      label hint hph hk he
    have hbit : ((if d = tname dst then 1 else 0 : Nat) : Int) =
        if d = tname dst then (1 : Int) else 0 := by
      by_cases hd : d = tname dst <;> simp [hd]
    have hle := Int.ofNat_le.mpr hNat
    rw [Int.natCast_add, hbit] at hle
    exact hle

theorem occ_other_park (I : Impl) (_hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k kP : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (_hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to))
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive) (hagree : keyAgrees I.desc sender dst)
    (hroom : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst))
    (hcore : peerKey dst = none → coreSender I.desc sender)
    (hhold : ∀ d,
      tokenHold I.desc (tname sender) d
          { (w.st sender) with phase := .parked dst isCall kP } +
        (if d = tname dst then 1 else 0) ≤
        tokenHold I.desc (tname sender) d (w.st sender)) :
    OccInv I (enqueueOrPark w I.desc sender dst msg isCall kP) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hsender
    have hge := hold_ge_effect I.desc (tname sender) (tname dst) (w.st sender) k e es label hint
      hph hk (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    exact Int.le_trans (Int.ofNat_le.mpr hge) hS
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_park_other w I.desc sender dst msg isCall kP hlive hne hroom]
  let charged := chargeSender (w.st sender) (tname dst)
  let base := if isCall then issueCall charged else charged
  let issued : Msg := { msg with mid := (w.st dst).nextMid, callId := if isCall then some (issueCall charged).waitId else msg.callId }
  let entry : Parked := { sender := sender, msg := issued, isCall := isCall }
  let aD : Actor := { (w.st dst) with parked := (w.st dst).parked ++ [entry], nextMid := (w.st dst).nextMid + 1 }
  let aS : Actor := { base with phase := .parked dst isCall kP }
  have hbl : base.life = charged.life := by cases isCall <;> simp [base, issueCall]
  have hbty : base.typestate = charged.typestate := by cases isCall <;> simp [base, issueCall]
  have hbbox : base.box = charged.box := by cases isCall <;> simp [base, issueCall]
  have hbpark : base.parked = charged.parked := by cases isCall <;> simp [base, issueCall]
  have hbtok : ∀ d, base.tokens d = charged.tokens d := by
    intro d; cases isCall <;> simp [base, issueCall]
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by
    cases isCall <;> simpa [aS, aD, entry, issued, charged, base, issueCall] using this
  apply occ_two I w sender dst aS aD (tname dst) hO hne
  · simp [aS, hbl, hcl, charged]
  · simp [aD]
  · simp [aS, hbty, hcty, charged]
  · simp [aD]
  · simp [aD]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname dst)).tokens d := by simp [aS, hbtok, charged]
    rw [htk]
    exact charge_tok (w.st sender) (tname dst) d htok1
  · intro d; simp [aD]
  · intro s
    exact owed_other_park w.st (tname dst) sender dst aS aD entry w.roster hO.nodup hdst hmem hne rfl rfl
      (by simp [aS, hbbox, hcb, charged]) (by simp [aS, hbpark, hcp, charged]) (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, hbbox, hcb, charged]) (by simp [aS, hbpark, hcp, charged]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box := by simpa [aD] using hm
    exact hO.sentFrom dst m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hbpark, hcp, charged] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom dst p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hbpark, hcp, charged] using hp
    exact hO.parkMsg sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkMsg dst p h
    | inr h => simp [h, entry, issued, hmsg]
  · exact hmem
  · exact hdst
  · exact hsender
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
    exact (hO.sameKey sender).1 m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hbpark, hcp, charged] using hp
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
    exact absurd (by simp [aS, hbl, hcl, charged]; exact hsender) hdead
  · intro hdead
    exact absurd (by simp [aD]; exact hlive) hdead
  · intro hk
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm' : m ∈ (w.st sender).box := by simpa [aS, hbbox, hcb, charged] using hm
      exact (hO.coreFrom sender hk).1 m hm'
    · intro p hp
      have hp' : p ∈ (w.st sender).parked := by simpa [aS, hbpark, hcp, charged] using hp
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
      · simpa [hp', entry, issued, hmsg] using hcore hk
  · intro nm key d
    let w1 := setActor w dst aD
    have hboxD : aD.box = (w.st dst).box := by simp [aD]
    have hparkD : aD.parked = (w.st dst).parked ++ [entry] := by simp [aD]
    have happ := queuedFromKey_park w dst aD entry nm key d hO.nodup hdst hboxD hparkD
    have hboxS : aS.box = (w1.st sender).box := by
      simp [aS, w1, setActor, hne, hbbox, hcb, charged]
    have hparkS : aS.parked = (w1.st sender).parked := by
      simp [aS, w1, setActor, hne, hbpark, hcp, charged]
    have hset := queuedFromKey_set w1 sender aS hboxS hparkS nm key d
    rw [hset, happ, Int.natCast_add]
    have hcast :
        ((if (tname dst != d) = true then 0
          else if keyPred nm key entry.msg = true then 1 else 0 : Nat) : Int) =
          queueDrop sender nm key d (tname dst) := by
      have hswap :
          ((if (tname dst != d) = true then 0
            else if keyPred nm key entry.msg = true then 1 else 0 : Nat) : Int) =
            if d = tname dst then if keyPred nm key entry.msg = true then (1 : Int) else 0 else 0 := by
        by_cases ht : tname dst = d
        · by_cases hk' : keyPred nm key entry.msg = true <;> simp [ht, hk', bne]
        · have hneD : ¬ d = tname dst := fun h => ht h.symm
          by_cases hk' : keyPred nm key entry.msg = true <;> simp [ht, hneD, hk', bne]
      rw [hswap]
      exact queueDrop_msg sender entry.msg nm key d (tname dst) (by simp [entry, issued, hmsg])
    rw [hcast]
  · intro d
    have hsame : tokenHold I.desc (tname sender) d aS =
        tokenHold I.desc (tname sender) d
          { (w.st sender) with phase := .parked dst isCall kP } := by
      cases isCall <;> simp [tokenHold, aS, hbty, hcty]
    rw [hsame]
    have hNat := hhold d
    have hbit : ((if d = tname dst then 1 else 0 : Nat) : Int) =
        if d = tname dst then (1 : Int) else 0 := by
      by_cases hd : d = tname dst <;> simp [hd]
    have hle := Int.ofNat_le.mpr hNat
    rw [Int.natCast_add, hbit] at hle
    exact hle

/-- A blocking send or call. The target is charged for when it is alive.
A non-call park keeps the tail. A parked call uses the tight reserve: the
charged message is not counted again, and `NotAdmitted` is one slot lower. -/
theorem occ_enqueue (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k)
    (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ (∃ na to, e = .call (tname dst) label hint na to))
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive)
    (hagree : keyAgrees I.desc sender dst)
    (hbulk : bulkScopeOf I.desc (tname sender) (e :: es) = true)
    (hflag : isCall = true → ∃ na to, e = .call (tname dst) label hint na to) :
    OccInv I (enqueueOrPark w I.desc sender dst msg isCall
      (if isCall then callWait k e else afterHead k)) := by
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
            hmsg hty hsender hroom.1 hroom.2
        | true =>
          obtain ⟨na, to, hc⟩ := hflag rfl
          exact occ_self_call I w sender msg k e es label hint hO hph hk ⟨na, to, hc⟩ hmsg hsender
            hroom.1 hroom.2
      · cases isCall with
        | false =>
          exact occ_other_send I w sender dst msg k e es label hint hO hph hk
            (by
              rcases he with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h))
            hmsg hty hsender hsame hlive hroom.1 hroom.2 hagree
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive)
              (hO.aliveIn sender hsender) hbulk
              ⟨label, hint, by
                rcases he with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)⟩ hk)
        | true =>
          obtain ⟨na, to, hc⟩ := hflag rfl
          exact occ_other_call I w sender dst msg k e es label hint hO hph hk ⟨na, to, hc⟩ hmsg hsender
            hsame hlive hroom.1 hroom.2 hagree
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive)
              (hO.aliveIn sender hsender) hbulk
              ⟨label, hint, Or.inr (Or.inl ⟨na, to, hc⟩)⟩ hk)
    · by_cases hsame : sender = dst
      · subst hsame
        cases isCall with
        | false =>
          rw [ite_eq_right (by decide : ¬ false = true)]
          exact occ_self_park I hL w sender msg false k (afterHead k) e es label hint hO hT hph hk he
            hmsg hsender hroom (fun d =>
              tokenHold_park_false I.desc (tname sender) d (tname sender) (w.st sender) k sender e es
                label hint hph hk (by
                  rcases he with h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)))
        | true =>
          obtain ⟨na, to, hc⟩ := hflag rfl
          rw [ite_eq_left (by decide : true = true)]
          exact occ_self_park I hL w sender msg true k (callWait k e) e es label hint hO hT hph hk
            (Or.inr ⟨na, to, hc⟩) hmsg hsender hroom (fun d => by
              have hk' : k.rest = .call (tname sender) label hint na to :: es := by
                simpa [hc] using hk
              simpa [hc] using tokenHold_park_call I.desc (tname sender) d (tname sender)
                (w.st sender) k sender na to es label hint hph hk' rfl)
      · cases isCall with
        | false =>
          rw [ite_eq_right (by decide : ¬ false = true)]
          exact occ_other_park I hL w sender dst msg false k (afterHead k) e es label hint hO hT hph hk
            he hmsg hsender hsame hlive hagree hroom
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive)
              (hO.aliveIn sender hsender) hbulk
              ⟨label, hint, by
                rcases he with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)⟩ hk)
            (fun d => tokenHold_park_false I.desc (tname sender) d (tname dst) (w.st sender) k dst e es
              label hint hph hk (by
                rcases he with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)))
        | true =>
          obtain ⟨na, to, hc⟩ := hflag rfl
          rw [ite_eq_left (by decide : true = true)]
          exact occ_other_park I hL w sender dst msg true k (callWait k e) e es label hint hO hT hph hk
            (Or.inr ⟨na, to, hc⟩) hmsg hsender hsame hlive hagree hroom
            (fun hk => core_send_from I w hO sender dst e es (hO.aliveIn dst hlive)
              (hO.aliveIn sender hsender) hbulk
              ⟨label, hint, Or.inr (Or.inl ⟨na, to, hc⟩)⟩ hk)
            (fun d => by
              have hk' : k.rest = .call (tname dst) label hint na to :: es := by
                simpa [hc] using hk
              simpa [hc] using tokenHold_park_call I.desc (tname sender) d (tname dst)
                (w.st sender) k dst na to es label hint hph hk' rfl)
  · cases isCall with
    | false =>
      rw [ite_eq_right (by decide : ¬ false = true)]
      rw [enqueue_dead w I.desc sender dst msg (afterHead k) hlive]
      exact occ_advance I w sender k hO hty hph
    | true =>
      obtain ⟨na, to, hc⟩ := hflag rfl
      rw [ite_eq_left (by decide : true = true)]
      rw [enqueue_miss w I.desc sender dst msg (callWait k e) hlive]
      apply occ_keep I w sender
          (finishCall (issueCall (w.st sender)) (callWait k e) .notAdmitted) hO
        (by simpa [issueCall] using
          finishCall_life (issueCall (w.st sender)) (callWait k e) .notAdmitted)
        (by simpa [finishCall, issueCall] using
          proceed_box (issueCall (w.st sender)) (selectCall (callWait k e) .notAdmitted))
        (by simpa [finishCall, issueCall] using
          proceed_parked (issueCall (w.st sender)) (selectCall (callWait k e) .notAdmitted))
        (by
          intro d
          simpa [finishCall, issueCall] using
            proceed_tokens (issueCall (w.st sender)) (selectCall (callWait k e) .notAdmitted) d)
        (by
          intro d _
          have hk' : k.rest = .call (tname dst) label hint na to :: es := by rw [hc] at hk; exact hk
          have hle := tokenHold_miss I.desc (tname sender) d (tname dst) (w.st sender) k na to es
            label hint hph hk'
          simpa [hc] using Int.ofNat_le.mpr hle)

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
      else crashWorld w) := by
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
      · intro d _
        have hphB : base.phase = .run k := by simp [base, hph]
        have hle := tokenHold_advance I.desc (tname id) d base k hphB
        have hsame : tokenHold I.desc (tname id) d base =
            tokenHold I.desc (tname id) d (w.st id) := by
          simp [tokenHold, base, ha, hph]
        simpa [aS, hsame] using Int.ofNat_le.mpr hle
    · simp [hb, hlen]
      exact occ_crash I w hO

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
    (by simp [w1, setCell])
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

theorem filter_bool_zero {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = false) → (xs.filter p).length = 0
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (List.Mem.head _)
    have ht := filter_bool_zero p xs (fun y hy => h y (List.Mem.tail _ hy))
    rw [List.filter_cons]
    simp [hx, ht]

theorem pred_false_sender (name : String) (key : Nat) (m : Msg)
    (h : ∀ g, m.sender ≠ InstId.peer name key g) : keyPred name key m = false := by
  cases hsend : m.sender with
  | core _ => simp [keyPred, hsend]
  | peer s k g =>
    simp only [keyPred, hsend]
    by_cases hp : (s == name && k == key) = true
    · exfalso
      have ⟨hs, hk⟩ : s = name ∧ k = key := by simpa [Bool.and_eq_true, beq_iff_eq] using hp
      exact h g (by simp [hsend, hs, hk])
    · cases hbb : s == name && k == key
      · rfl
      · exact absurd hbb hp

theorem key_len (I : Impl) (w : World) (hO : OccInv I w) (name : String) (key : Nat)
    (habs : ∀ g, InstId.peer name key g ∉ w.roster) (host : InstId) :
    ((w.st host).box.filter (fun m => keyPred name key m)).length = 0 ∧
      ((w.st host).parked.filter (fun p => keyPred name key p.msg)).length = 0 := by
  refine ⟨?_, ?_⟩
  · refine filter_bool_zero _ _ ?_
    intro m hm
    exact pred_false_sender name key m (fun g heq =>
      habs g (by simpa [heq] using hO.sentFrom host m hm))
  · refine filter_bool_zero _ _ ?_
    intro p hp
    exact pred_false_sender name key p.msg (fun g heq =>
      habs g (by
        have hwho := hO.parkMsg host p hp
        have : p.sender = InstId.peer name key g := by rw [hwho, heq]
        exact this ▸ hO.parkFrom host p hp))

theorem queued_fold_zero (st : InstId → Actor) (name : String) (key : Nat) (dst : String) :
    ∀ (ids : List InstId) (n : Nat),
      (∀ host ∈ ids,
        ((st host).box.filter (fun m => keyPred name key m)).length = 0 ∧
          ((st host).parked.filter (fun p => keyPred name key p.msg)).length = 0) →
        ids.foldl (fun n host =>
          if tname host != dst then n
          else n + ((st host).box.filter (fun m => keyPred name key m)).length +
            ((st host).parked.filter (fun p => keyPred name key p.msg)).length) n = n
  | [], _, _ => rfl
  | host :: ids, n, h => by
    simp only [List.foldl_cons]
    have hh := h host (List.Mem.head _)
    simp only [hh.1, hh.2, Nat.add_zero, ite_self]
    exact queued_fold_zero st name key dst ids n (fun i hi => h i (List.Mem.tail _ hi))

/-- No generation of this key is on the roster, so none of its mail is queued. -/
theorem queued_absent (I : Impl) (w : World) (hO : OccInv I w) (name : String) (key : Nat)
    (habs : ∀ g, InstId.peer name key g ∉ w.roster) (dst : String) :
    queuedFromKey w name key dst = 0 := by
  unfold queuedFromKey
  dsimp
  exact queued_fold_zero w.st name key dst w.roster 0
    (fun host _ => key_len I w hO name key habs host)

theorem queued_fold_born (w : World) (id : InstId) (a : Actor) (name : String) (key : Nat)
    (dst : String) (hb : a.box = []) (hp : a.parked = []) (hf : id ∉ w.roster) :
    (w.roster ++ [id]).foldl (fun n host =>
      if tname host != dst then n
      else n + (((if host = id then a else w.st host).box.filter (fun m => keyPred name key m)).length) +
        (((if host = id then a else w.st host).parked.filter
          (fun p => keyPred name key p.msg)).length)) 0 =
      w.roster.foldl (fun n host =>
        if tname host != dst then n
        else n + ((w.st host).box.filter (fun m => keyPred name key m)).length +
          ((w.st host).parked.filter (fun p => keyPred name key p.msg)).length) 0 := by
  have hagree :
      w.roster.foldl (fun n host =>
        if tname host != dst then n
        else n + (((if host = id then a else w.st host).box.filter (fun m => keyPred name key m)).length) +
          (((if host = id then a else w.st host).parked.filter
            (fun p => keyPred name key p.msg)).length)) 0 =
        w.roster.foldl (fun n host =>
          if tname host != dst then n
          else n + ((w.st host).box.filter (fun m => keyPred name key m)).length +
            ((w.st host).parked.filter (fun p => keyPred name key p.msg)).length) 0 := by
    refine foldl_pointwise _ _ w.roster 0 ?_
    intro n host hhost
    have hne : host ≠ id := fun h => hf (by simpa [h] using hhost)
    rw [if_neg hne]
  rw [List.foldl_append, hagree]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hd : (tname id != dst) = true
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd]
    simp [hb, hp, Nat.add_zero]

/-- An empty newcomer does not change how much mail any key already has queued. -/
theorem queuedFromKey_born (w w' : World) (id : InstId) (a : Actor)
    (hst : ∀ i, w'.st i = if i = id then a else w.st i)
    (hr : w'.roster = w.roster ++ [id]) (hb : a.box = []) (hp : a.parked = [])
    (hf : id ∉ w.roster) (name : String) (key : Nat) (dst : String) :
    queuedFromKey w' name key dst = queuedFromKey w name key dst := by
  unfold queuedFromKey
  dsimp
  rw [hr, funext hst]
  exact queued_fold_born w id a name key dst hb hp hf

theorem find_snoc_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (a : α), p a = false → (xs ++ [a]).find? p = xs.find? p
  | [], a, hp => by simp [hp]
  | x :: xs, a, hp => by
    simp only [List.cons_append, List.find?_cons]
    by_cases hx : p x = true
    · simp [hx]
    · cases hbb : p x
      · simp [hbb, find_snoc_false p xs a hp]
      · exact absurd hbb hx

theorem find_agree {α : Type} (p q : α → Bool) :
    ∀ (xs : List α), (∀ a ∈ xs, p a = q a) → xs.find? p = xs.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons]
    have hx : p x = q x := h x (List.Mem.head _)
    rw [hx]
    cases hbb : q x
    · simp [hbb, find_agree p q xs (fun a ha => h a (List.Mem.tail _ ha))]
    · simp [hbb]

theorem findLive_born (w w' : World) (id : InstId) (a : Actor) (name : String) (key : Nat)
    (hst : ∀ i, w'.st i = if i = id then a else w.st i) (hr : w'.roster = w.roster ++ [id])
    (hf : id ∉ w.roster)
    (hmiss : match id with
      | .peer n k _ => (n == name && k == key && a.life == .alive) = false
      | .core _ => True) :
    findLive w' name key = findLive w name key := by
  unfold findLive
  rw [hr]
  refine (find_snoc_false _ w.roster id ?_).trans (find_agree _ _ w.roster ?_)
  · cases id with
    | core _ => rfl
    | peer n k g =>
      have hs : w'.st (InstId.peer n k g) = a := by
        rw [hst (InstId.peer n k g), ite_eq_left rfl]
      rw [hs]
      exact hmiss
  · intro i hi
    have hne : i ≠ id := fun h => hf (by rw [h] at hi; exact hi)
    cases i with
    | core _ => rfl
    | peer n k g =>
      rw [hst (InstId.peer n k g), ite_eq_right hne]

theorem born_one (w w' : World) (id : InstId) (a : Actor) (template : String) (k : Nat)
    (hst : ∀ i, w'.st i = if i = id then a else w.st i) (hr : w'.roster = w.roster ++ [id])
    (hid : id = InstId.peer template k (maxGen w template k))
    (hkey : ∀ g, InstId.peer template k g ∉ w.roster) (h1 : oneLiveGen w) : oneLiveGen w' := by
  intro name key g1 g2 hm1 hm2 _hl1 _hl2
  by_cases hA : InstId.peer name key g1 = id
  · have heq : InstId.peer name key g1 = InstId.peer template k (maxGen w template k) := by
      simpa [hid] using hA
    injection heq with hn hk hg1
    have hm2' : InstId.peer template k g2 ∈ w'.roster := by simpa [hn, hk] using hm2
    rw [hr] at hm2'
    rcases List.mem_append.mp hm2' with hm2' | hm2'
    · exact absurd hm2' (hkey g2)
    · simp [List.mem_singleton] at hm2'
      have heq2 : InstId.peer template k g2 =
          InstId.peer template k (maxGen w template k) := by simpa [hid] using hm2'
      injection heq2 with _ _ hg2
      exact hg1.trans hg2.symm
  · by_cases hB : InstId.peer name key g2 = id
    · have heq : InstId.peer name key g2 = InstId.peer template k (maxGen w template k) := by
        simpa [hid] using hB
      injection heq with hn hk hg2
      have hm1' : InstId.peer template k g1 ∈ w'.roster := by simpa [hn, hk] using hm1
      rw [hr] at hm1'
      rcases List.mem_append.mp hm1' with hm1' | hm1'
      · exact absurd hm1' (hkey g1)
      · simp [List.mem_singleton] at hm1'
        have heq1 : InstId.peer template k g1 =
            InstId.peer template k (maxGen w template k) := by simpa [hid] using hm1'
        injection heq1 with _ _ hg1
        exact hg1.trans hg2.symm
    · have hm1o : InstId.peer name key g1 ∈ w.roster := by
        rw [hr] at hm1
        rcases List.mem_append.mp hm1 with hmem | hmem
        · exact hmem
        · exact absurd (List.mem_singleton.mp hmem) hA
      have hm2o : InstId.peer name key g2 ∈ w.roster := by
        rw [hr] at hm2
        rcases List.mem_append.mp hm2 with hmem | hmem
        · exact hmem
        · exact absurd (List.mem_singleton.mp hmem) hB
      have hl1o : (w.st (InstId.peer name key g1)).life = .alive := by
        have hs := hst (InstId.peer name key g1)
        rw [if_neg hA] at hs
        simpa [hs] using _hl1
      have hl2o : (w.st (InstId.peer name key g2)).life = .alive := by
        have hs := hst (InstId.peer name key g2)
        rw [if_neg hB] at hs
        simpa [hs] using _hl2
      exact h1 name key g1 g2 hm1o hm2o hl1o hl2o

theorem alive_extend (w w' : World) (id : InstId) (a : Actor) (template : String)
    (hst : ∀ i, w'.st i = if i = id then a else w.st i) (hr : w'.roster = w.roster ++ [id])
    (hf : id ∉ w.roster) (hl : a.life = .alive) (hn : tname id = template) :
    aliveCount w' template = aliveCount w template + 1 := by
  rw [aliveCount_sum, aliveCount_sum, hr, sum_snoc]
  have hcong : sumFold (aliveBit w'.st template) w.roster =
      sumFold (aliveBit w.st template) w.roster := by
    refine sum_congr _ _ _ ?_
    intro i hi
    have hne : i ≠ id := fun h => hf (by simpa [h] using hi)
    unfold aliveBit
    have hs := hst i
    rw [if_neg hne] at hs
    simp [hs]
  rw [hcong]
  unfold aliveBit
  simp [hst id, if_pos rfl, hl, hn, beq_iff_eq]

theorem alive_same (w w' : World) (id : InstId) (a : Actor) (template : String)
    (hst : ∀ i, w'.st i = if i = id then a else w.st i) (hr : w'.roster = w.roster ++ [id])
    (hf : id ∉ w.roster) (hne : tname id ≠ template) :
    aliveCount w' template = aliveCount w template := by
  rw [aliveCount_sum, aliveCount_sum, hr, sum_snoc]
  have hcong : sumFold (aliveBit w'.st template) w.roster =
      sumFold (aliveBit w.st template) w.roster := by
    refine sum_congr _ _ _ ?_
    intro i hi
    have hneI : i ≠ id := fun h => hf (by simpa [h] using hi)
    unfold aliveBit
    have hs := hst i
    rw [if_neg hneI] at hs
    simp [hs]
  rw [hcong]
  unfold aliveBit
  have hb : (tname id == template) = false := by
    cases hbb : tname id == template with
    | false => rfl
    | true => exact absurd (by simpa [beq_iff_eq] using hbb) hne
  simp [hst id, if_pos rfl, hb, Nat.add_zero]

theorem shape_peer (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hmul : t.multiplicity = .perPeer) (id : InstId)
    (hid : id ∈ w.roster) (hname : tname id = template) : ∃ k g, id = InstId.peer template k g := by
  obtain ⟨u, hu, hsh⟩ := hO.shaped id hid
  have hu' : templateOf I.desc template = some u := by simpa [hname] using hu
  rw [ht] at hu'
  cases hu'
  simp only [hmul] at hsh
  obtain ⟨k, g, hid⟩ := hsh
  have hnm : t.name = template := (templateOf_mem I.desc template t ht).2
  exact ⟨k, g, by simpa [hnm] using hid⟩

def markBit (w : World) (template : String) (mark : Nat → Bool) (id : InstId) : Nat :=
  match id with
  | .peer child k _ =>
    if child == template && ((w.st id).life == .alive || mark k) then 1 else 0
  | .core _ => 0

theorem mark_sum (w : World) (template : String) (mark : Nat → Bool) :
    ∀ (ids : List InstId) (acc : Nat),
      ids.foldl (fun n id =>
        match id with
        | .peer child k _ =>
          if child == template && ((w.st id).life == .alive || mark k) then n + 1 else n
        | .core _ => n) acc = acc + sumFold (markBit w template mark) ids
  | [], acc => by simp [sumFold]
  | id :: ids, acc => by
    rw [List.foldl_cons, sumFold]
    cases id with
    | core _ =>
      simp only [markBit]
      rw [mark_sum w template mark ids acc]
      omega
    | peer child k g =>
      by_cases hc : (child == template &&
          ((w.st (InstId.peer child k g)).life == .alive || mark k)) = true
      · simp only [hc, ite_true, markBit]
        rw [mark_sum w template mark ids (acc + 1)]
        omega
      · have hf : (child == template &&
            ((w.st (InstId.peer child k g)).life == .alive || mark k)) = false := by
          cases hbb : child == template &&
              ((w.st (InstId.peer child k g)).life == .alive || mark k)
          · rfl
          · exact absurd hbb hc
        simp only [hf, markBit]
        repeat rw [ite_eq_right (by decide : ¬ false = true)]
        rw [mark_sum w template mark ids acc]
        omega

theorem alive_le_bit (w : World) (template : String) (mark : Nat → Bool) (id : InstId)
    (hshape : tname id = template → ∃ k g, id = InstId.peer template k g) :
    aliveBit w.st template id ≤ markBit w template mark id := by
  cases id with
  | core name =>
    unfold aliveBit markBit
    have hf : (tname (InstId.core name) == template &&
        (w.st (InstId.core name)).life == .alive) = false := by
      by_cases ht : (tname (InstId.core name) == template) = true
      · have hname : tname (InstId.core name) = template := by simpa [beq_iff_eq] using ht
        obtain ⟨_k, _g, hid⟩ := hshape hname
        cases hid
      · cases hbb : tname (InstId.core name) == template
        · simp [hbb]
        · exact absurd hbb ht
    simp [hf]
  | peer child k g =>
    unfold aliveBit markBit
    by_cases hhit : (child == template &&
        (w.st (InstId.peer child k g)).life == .alive) = true
    · have hhitP := hhit
      simp only [Bool.and_eq_true] at hhit
      obtain ⟨hc, hl⟩ := hhit
      have hor : ((w.st (InstId.peer child k g)).life == .alive || mark k) = true := by
        simp [hl, Bool.true_or]
      have hcond : (child == template &&
          ((w.st (InstId.peer child k g)).life == .alive || mark k)) = true := by
        simp [hc, hor]
      simp [tname, hhitP, hcond]
    · have hf : (child == template &&
          (w.st (InstId.peer child k g)).life == .alive) = false := by
        cases hbb : child == template && (w.st (InstId.peer child k g)).life == .alive
        · rfl
        · exact absurd hbb hhit
      simp [tname, hf]

theorem alive_le_mark (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hmul : t.multiplicity = .perPeer)
    (mark : Nat → Bool) :
    aliveCount w template ≤
      w.roster.foldl (fun n id =>
        match id with
        | .peer child k _ =>
          if child == template && ((w.st id).life == .alive || mark k) then n + 1 else n
        | .core _ => n) 0 := by
  rw [aliveCount_sum, mark_sum w template mark w.roster 0, Nat.zero_add]
  refine sum_le _ _ _ ?_
  intro id hid
  exact alive_le_bit w template mark id
    (fun hname => shape_peer I w hO template t ht hmul id hid hname)

theorem alive_le_lone (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hmul : t.multiplicity = .perPeer) :
    aliveCount w template ≤ loneOutstanding I.desc w template := by
  unfold loneOutstanding
  exact alive_le_mark I w hO template t ht hmul
    (fun k => slotMailHeld I.desc w template k)

theorem alive_le_root (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hmul : t.multiplicity = .perPeer)
    (supervisor : String) :
    aliveCount w template ≤ rootOutstanding I.desc w supervisor template := by
  unfold rootOutstanding
  exact alive_le_mark I w hO template t ht hmul
    (fun k => slotTombstoneQueued w (InstId.core supervisor) template k)

theorem may_peer (D : Description) (w : World) (template : String) (t : Template)
    (hmay : maySpawnRoot D w template t = true) : t.multiplicity = .perPeer ∧ t.slots = 0 := by
  simp only [maySpawnRoot] at hmay
  repeat rw [Bool.and_eq_true] at hmay
  obtain ⟨⟨⟨⟨hmul, hslots⟩, _⟩, _⟩, _⟩ := hmay
  refine ⟨?_, ?_⟩
  · cases hm : t.multiplicity with
    | perPeer => rfl
    | one =>
      rw [hm] at hmul
      rw [show (Multiplicity.one == Multiplicity.perPeer) = false from rfl] at hmul
      exact Bool.noConfusion hmul
  · simpa [beq_iff_eq] using hslots

theorem may_lone_lt (D : Description) (w : World) (template : String) (t : Template)
    (hmay : maySpawnRoot D w template t = true) (hsup : t.supervisor = none) :
    loneOutstanding D w template < w.N := by
  simp only [maySpawnRoot, hsup, Bool.and_eq_true, decide_eq_true_iff] at hmay
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hlt⟩ := hmay
  exact hlt

theorem may_root_lt (D : Description) (w : World) (template : String) (t : Template)
    (hmay : maySpawnRoot D w template t = true) (name : String) (hsup : t.supervisor = some name) :
    rootOutstanding D w name template < w.N := by
  simp only [maySpawnRoot, hsup, Bool.and_eq_true, decide_eq_true_iff] at hmay
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hlt⟩ := hmay
  exact hlt

/-- A supervisor on an empty subtree is rejected by the checker. -/
theorem supervised_subtree (D : Description) (hG : GraphOk D) (template : String) (t : Template)
    (ht : templateOf D template = some t) (hslots : t.slots = 0) (name : String)
    (hsup : t.supervisor = some name) : t.subtree ≠ "" := by
  have hmap : D.templates.filterMap (subtreeEntry D) = [] := by
    have hfail : subtreeFails D = [] := hG.subtrees
    simp only [subtreeFails] at hfail
    exact (List.append_eq_nil_iff.mp hfail).1
  have hent : subtreeEntry D t = none :=
    filterMap_mem_none (subtreeEntry D) D.templates t hmap (templateOf_mem D template t ht).1
  intro heq
  have hslotsB : (t.slots != 0) = false := by simp [hslots, bne]
  have hsubB : (t.subtree == "") = true := by simpa [beq_iff_eq] using heq
  have hsome : t.supervisor.isSome = true := by simp [hsup]
  unfold subtreeEntry at hent
  have hpool : (t.slots != 0 && (t.multiplicity != .perPeer || t.supervisor.isNone)) = false := by
    simp [hslotsB]
  rw [hpool] at hent
  rw [ite_eq_right (by decide : ¬ false = true)] at hent
  rw [hslotsB] at hent
  rw [ite_eq_right (by decide : ¬ false = true)] at hent
  rw [hsubB] at hent
  rw [ite_eq_left (by decide : true = true)] at hent
  rw [hsome] at hent
  rw [ite_eq_left (by decide : true = true)] at hent
  cases hent

theorem freshFold_ge (D : Description) (sub : String) :
    ∀ (ids : List InstId) (start : Nat),
      start ≤ ids.foldl (fun m id =>
        match id with
        | .peer n k _ =>
          if sub != "" && templateSubtree D n == sub then max m (k + 1) else m
        | .core _ => m) start
  | [], start => Nat.le_refl _
  | id :: ids, start => by
    rw [List.foldl_cons]
    cases id with
    | core _ => exact freshFold_ge D sub ids start
    | peer n k _ =>
      by_cases hbit : (sub != "" && templateSubtree D n == sub) = true
      · simp only [hbit, ite_true]
        exact Nat.le_trans (Nat.le_max_left start (k + 1))
          (freshFold_ge D sub ids (max start (k + 1)))
      · simp only [hbit, ite_false]
        exact freshFold_ge D sub ids start

theorem fresh_below (D : Description) (w : World) (sub n : String) (k g : Nat)
    (hsub : sub ≠ "") (htree : templateSubtree D n = sub)
    (hmem : InstId.peer n k g ∈ w.roster) : k < freshKey D w sub := by
  have hbit : (sub != "") = true := by simpa [bne, beq_iff_eq] using hsub
  have htreeB : (templateSubtree D n == sub) = true := by simpa [beq_iff_eq] using htree
  have hcond : (sub != "" && templateSubtree D n == sub) = true := by simp [hbit, htreeB]
  have hgen : ∀ (ids : List InstId) (start : Nat), InstId.peer n k g ∈ ids →
      k + 1 ≤ ids.foldl (fun m id =>
        match id with
        | .peer n' k' _ =>
          if sub != "" && templateSubtree D n' == sub then max m (k' + 1) else m
        | .core _ => m) start := by
    intro ids
    induction ids with
    | nil =>
      intro _ hbad
      cases hbad
    | cons id ids ih =>
      intro start hmem'
      rw [List.foldl_cons]
      cases List.mem_cons.mp hmem' with
      | inl heq =>
        cases heq
        simp only [hcond, ite_true]
        exact Nat.le_trans (Nat.le_max_right start (k + 1))
          (freshFold_ge D sub ids (max start (k + 1)))
      | inr htail =>
        cases id with
        | core _ => exact ih start htail
        | peer n' k' _ =>
          by_cases hif : (sub != "" && templateSubtree D n' == sub) = true
          · simp only [hif, ite_true]
            exact ih (max start (k' + 1)) htail
          · simp only [hif, ite_false]
            exact ih start htail
  have hle : k + 1 ≤ freshKey D w sub := by
    unfold freshKey
    exact hgen w.roster (w.nextKey sub) hmem
  omega

theorem place_roster (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (hrB : ∀ u, (bump u).roster = u.roster) :
    (placePeer I w template k initial parent bump).roster =
      w.roster ++ [InstId.peer template k (maxGen w template k)] := by
  delta placePeer
  dsimp
  rw [cellsRoster]
  simp [setActor, hrB]

theorem place_nextIx (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (n : String) :
    (placePeer I w template k initial parent bump).nextIx n =
      (bump { w with roster := w.roster ++ [InstId.peer template k (maxGen w template k)] }).nextIx n := by
  delta placePeer
  dsimp
  rw [readCells_nextIx]
  simp [setActor]

theorem place_st (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (hstB : ∀ u i, (bump u).st i = u.st i)
    (i : InstId) :
    (placePeer I w template k initial parent bump).st i =
      if i = InstId.peer template k (maxGen w template k) then
        { bornActor I.desc w template k initial with parent := parent }
      else w.st i := by
  delta placePeer
  dsimp
  rw [cellsSt]
  by_cases hi : i = InstId.peer template k (maxGen w template k)
  · simp [setActor, hi]
  · simp [setActor, hi, hstB]

theorem place_N (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (hNB : ∀ u, (bump u).N = u.N) :
    (placePeer I w template k initial parent bump).N = w.N := by
  delta placePeer
  dsimp
  rw [cellsN]
  simp [setActor, hNB]

theorem place_crashed (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (hcrB : ∀ u, (bump u).crashed = u.crashed) :
    (placePeer I w template k initial parent bump).crashed = w.crashed := by
  delta placePeer
  dsimp
  rw [readCells_crashed]
  simp [setActor, hcrB]

theorem ix_kept (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (k : Nat) (id : InstId)
    (hid : id = InstId.peer template k (maxGen w template k)) (w' : World)
    (hr : w'.roster = w.roster ++ [id]) (hixn : ∀ n, w'.nextIx n = w.nextIx n)
    (hskip : t.supervisor ≠ none ∨ t.subtree ≠ "") : IxFresh I.desc w' := by
  intro name k' g hmem t' ht' hsup' hsub' _hslots'
  rw [hr] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · simpa [hixn] using hO.ixFresh name k' g hmem t' ht' hsup' hsub' _hslots'
  · simp [List.mem_singleton] at hmem
    have heq : InstId.peer name k' g = InstId.peer template k (maxGen w template k) := by
      simpa [hid] using hmem
    injection heq with hname _ _
    have htEq : t' = t := by
      have hboth : templateOf I.desc template = some t' := by simpa [hname] using ht'
      rw [ht] at hboth
      cases hboth
      rfl
    cases hskip with
    | inl hsup => exact False.elim (hsup (htEq ▸ hsup'))
    | inr hsub => exact False.elim (hsub (htEq ▸ hsub'))

theorem ix_bumped (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hsup0 : t.supervisor = none) (hsub0 : t.subtree = "")
    (hslots0 : t.slots = 0) (k : Nat) (hk : k = w.nextIx template) (id : InstId)
    (hid : id = InstId.peer template k (maxGen w template k)) (w' : World)
    (hr : w'.roster = w.roster ++ [id])
    (hixn : ∀ n, w'.nextIx n = if n = template then k + 1 else w.nextIx n) : IxFresh I.desc w' := by
  intro name k' g hmem t' ht' hsup' hsub' hslots'
  rw [hr] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · have hlt := hO.ixFresh name k' g hmem t' ht' hsup' hsub' hslots'
    by_cases hn : name = template
    · rw [hixn name, if_pos hn]
      have hk0 : w.nextIx name = k := by simpa [hn] using hk.symm
      omega
    · rw [hixn name, if_neg hn]
      exact hlt
  · simp [List.mem_singleton] at hmem
    have heq : InstId.peer name k' g = InstId.peer template k (maxGen w template k) := by
      simpa [hid] using hmem
    injection heq with hname hk' _
    rw [hixn name, if_pos hname, hk']
    exact Nat.lt_succ_self k

theorem occ_born (I : Impl) (w : World) (hO : OccInv I w) (template : String) (t : Template)
    (ht : templateOf I.desc template = some t) (hmul : t.multiplicity = .perPeer) (k : Nat)
    (parent : Option InstId) (bump : World → World)
    (hkey : ∀ g, InstId.peer template k g ∉ w.roster) (hcount : aliveCount w template < w.N)
    (hix : IxFresh I.desc (placePeer I w template k t.initial parent bump))
    (hstB : ∀ u i, (bump u).st i = u.st i) (hrB : ∀ u, (bump u).roster = u.roster)
    (hNB : ∀ u, (bump u).N = u.N) (hcrB : ∀ u, (bump u).crashed = u.crashed) :
    OccInv I (placePeer I w template k t.initial parent bump) := by
  let id := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k t.initial with parent := parent }
  let wP := placePeer I w template k t.initial parent bump
  have hid : id = InstId.peer template k (maxGen w template k) := rfl
  have hfresh : id ∉ w.roster := fun hin => hkey _ (by simpa [hid] using hin)
  have hst : ∀ i, wP.st i = if i = id then born else w.st i := by
    intro i
    simpa [id, born, wP] using place_st I w template k t.initial parent bump hstB i
  have hr : wP.roster = w.roster ++ [id] := by
    simpa [id, wP] using place_roster I w template k t.initial parent bump hrB
  have hN : wP.N = w.N := by
    simpa [wP] using place_N I w template k t.initial parent bump hNB
  have hcrash : wP.crashed = w.crashed := by
    simpa [wP] using place_crashed I w template k t.initial parent bump hcrB
  have hlife : born.life = .alive := by simp [born, bornActor, withKeyTokens]
  have hbox : born.box = [] := by simp [born, bornActor, withKeyTokens]
  have hpark : born.parked = [] := by simp [born, bornActor, withKeyTokens]
  have hphase : born.phase = .idle := by simp [born, bornActor, withKeyTokens]
  have hty : born.typestate = t.initial := by simp [born, bornActor, withKeyTokens]
  have htok0 : ∀ d, born.tokens d =
      (budget I.desc template d : Int) - (queuedFromKey w template k d : Int) := by
    intro d
    simp [born, bornActor, withKeyTokens]
  have hq0 : ∀ d, queuedFromKey w template k d = 0 :=
    fun d => queued_absent I w hO template k hkey d
  have htokB : ∀ d, born.tokens d = (budget I.desc template d : Int) := by
    intro d
    rw [htok0 d, hq0 d, Int.natCast_zero, Int.sub_zero]
  have hself : wP.st id = born := by rw [hst id, if_pos rfl]
  have hqSame : ∀ name key dst, queuedFromKey wP name key dst = queuedFromKey w name key dst :=
    fun name key dst => queuedFromKey_born w wP id born hst hr hbox hpark hfresh name key dst
  have h1 : oneLiveGen wP := born_one w wP id born template k hst hr hid hkey hO.indexed
  have howed (dstName : String) (sender : InstId) :
      owed wP.st dstName sender wP.roster = owed w.st dstName sender w.roster := by
    rw [hr, owed_snoc_blank wP.st dstName sender w.roster id (by simp [hself, hbox])
      (by simp [hself, hpark])]
    refine owed_mail_eq wP.st w.st dstName sender w.roster ?_
    intro j hj
    have hne : j ≠ id := fun h => hfresh (by simpa [h] using hj)
    have hs := hst j
    rw [if_neg hne] at hs
    simp [hs]
  change OccInv I wP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact nodup_snoc hO.nodup hfresh
  · intro i hl
    rw [hr]
    by_cases hi : i = id
    · exact List.mem_append.mpr (Or.inr (by simpa [hi, List.mem_singleton]))
    · have hs := hst i
      rw [if_neg hi] at hs
      rw [hs] at hl
      exact List.mem_append.mpr (Or.inl (hO.aliveIn i hl))
  · exact h1
  · intro u ⟨tmpl, hu, hone⟩
    have hne : tname id ≠ u := by
      intro heq
      have hu' : templateOf I.desc u = some t := by
        have htn : tname id = template := by simp [hid, tname]
        rw [← heq, htn]
        exact ht
      rw [hu] at hu'
      cases hu'
      rw [hmul] at hone
      cases hone
    rw [alive_same w wP id born u hst hr hfresh hne]
    exact hO.liveOne u ⟨tmpl, hu, hone⟩
  · intro u ⟨tmpl, hu, hpeer⟩
    by_cases heq : tname id = u
    · rw [alive_extend w wP id born u hst hr hfresh hlife heq, hN]
      have hn : template = u := by simpa [hid, tname] using heq
      rw [hn] at hcount
      exact Nat.succ_le_of_lt hcount
    · rw [alive_same w wP id born u hst hr hfresh heq, hN]
      exact hO.livePeer u ⟨tmpl, hu, hpeer⟩
  · intro i hnin
    have hne : i ≠ id := by
      intro heq
      apply hnin
      rw [hr, heq]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    have hold : i ∉ w.roster := by
      intro hin
      apply hnin
      rw [hr]
      exact List.mem_append.mpr (Or.inl hin)
    have hs := hst i
    rw [if_neg hne] at hs
    rw [hs]
    exact hO.offEmpty i hold
  · intro i m hm
    by_cases hi : i = id
    · simp [hst i, if_pos hi, hbox] at hm
    · have hm0 : m ∈ (w.st i).box := by
        have hs := hst i
        rw [if_neg hi] at hs
        simpa [hs] using hm
      rw [hr]
      exact List.mem_append.mpr (Or.inl (hO.sentFrom i m hm0))
  · intro i p hp
    by_cases hi : i = id
    · simp [hst i, if_pos hi, hpark] at hp
    · have hp0 : p ∈ (w.st i).parked := by
        have hs := hst i
        rw [if_neg hi] at hs
        simpa [hs] using hp
      rw [hr]
      exact List.mem_append.mpr (Or.inl (hO.parkFrom i p hp0))
  · intro i p hp
    by_cases hi : i = id
    · simp [hst i, if_pos hi, hpark] at hp
    · have hp0 : p ∈ (w.st i).parked := by
        have hs := hst i
        rw [if_neg hi] at hs
        simpa [hs] using hp
      exact hO.parkMsg i p hp0
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key id' d hlive
      by_cases hslot : name = template ∧ key = k
      · obtain ⟨hn, hk⟩ := hslot
        rw [hn, hk] at hlive ⊢
        have hmemId : InstId.peer template k (maxGen w template k) ∈ wP.roster := by
          simpa [hid] using (by
            rw [hr]
            exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)) : id ∈ wP.roster)
        have hlId : (wP.st (InstId.peer template k (maxGen w template k))).life = .alive := by
          rw [← hid, hself]
          exact hlife
        have hfound := findLive_of_alive wP h1 template k (maxGen w template k) hmemId hlId
        have hid' : id' = id := by
          rw [hfound] at hlive
          injection hlive with heq
          simpa [hid] using heq.symm
        rw [hid', hself, htokB d, hqSame template k d, hq0 d, Int.natCast_zero, Int.add_zero]
      · have hnk : (template == name && k == key) = false := by
          by_cases hb : (template == name && k == key) = true
          · have hand : template = name ∧ k = key := by
              simpa [Bool.and_eq_true, beq_iff_eq] using hb
            exact absurd (And.intro hand.1.symm hand.2.symm) hslot
          · cases hbb : template == name && k == key
            · rfl
            · exact absurd hbb hb
        have hmiss : (match id with
            | .peer n kk _ => (n == name && kk == key && born.life == .alive) = false
            | .core _ => True) :=
          show (match InstId.peer template k (maxGen w template k) with
            | .peer n kk _ => (n == name && kk == key && born.life == .alive) = false
            | .core _ => True) from by
            simp [hnk, Bool.false_and]
        have hfeq := findLive_born w wP id born name key hst hr hfresh hmiss
        rw [hfeq] at hlive
        have hne : id' ≠ id := by
          intro heq
          exact hfresh (by simpa [heq] using findLive_mem w name key id' hlive)
        have htok : (wP.st id').tokens d = (w.st id').tokens d := by
          have hs := hst id'
          rw [if_neg hne] at hs
          simp [hs]
        rw [htok, hqSame name key d]
        exact hO.balance.1.1 name key id' d hlive
    · intro name d hl hmem
      have hne : InstId.core name ≠ id := by
        intro h
        rw [hid] at h
        cases h
      have hl0 : (w.st (InstId.core name)).life = .alive := by
        have hs := hst (InstId.core name)
        rw [if_neg hne] at hs
        simpa [hs] using hl
      have hmem0 : InstId.core name ∈ w.roster := by
        rw [hr] at hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hmem
        · have heq := List.mem_singleton.mp hmem
          rw [hid] at heq
          cases heq
      have htok : (wP.st (InstId.core name)).tokens d = (w.st (InstId.core name)).tokens d := by
        have hs := hst (InstId.core name)
        rw [if_neg hne] at hs
        simp [hs]
      rw [howed d (InstId.core name), htok]
      exact hO.balance.1.2 name d hl0 hmem0
    · intro name key d hnone
      by_cases hslot : name = template ∧ key = k
      · obtain ⟨hn, hk⟩ := hslot
        rw [hn, hk] at hnone ⊢
        have hmemId : InstId.peer template k (maxGen w template k) ∈ wP.roster := by
          simpa [hid] using (by
            rw [hr]
            exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)) : id ∈ wP.roster)
        have hlId : (wP.st (InstId.peer template k (maxGen w template k))).life = .alive := by
          rw [← hid, hself]
          exact hlife
        have hfound := findLive_of_alive wP h1 template k (maxGen w template k) hmemId hlId
        rw [hfound] at hnone
        cases hnone
      · have hnk : (template == name && k == key) = false := by
          by_cases hb : (template == name && k == key) = true
          · have hand : template = name ∧ k = key := by
              simpa [Bool.and_eq_true, beq_iff_eq] using hb
            exact absurd (And.intro hand.1.symm hand.2.symm) hslot
          · cases hbb : template == name && k == key
            · rfl
            · exact absurd hbb hb
        have hmiss : (match id with
            | .peer n kk _ => (n == name && kk == key && born.life == .alive) = false
            | .core _ => True) :=
          show (match InstId.peer template k (maxGen w template k) with
            | .peer n kk _ => (n == name && kk == key && born.life == .alive) = false
            | .core _ => True) from by
            simp [hnk, Bool.false_and]
        have hfeq := findLive_born w wP id born name key hst hr hfresh hmiss
        have hnone0 : findLive w name key = none := by simpa [hfeq] using hnone
        simpa [hqSame name key d] using hO.balance.2 name key d hnone0
  · intro i d hl
    by_cases hi : i = id
    · rw [hi]
      have htn : tname id = template := by simp [hid, tname]
      rw [hself, htokB d, htn]
      have hhold : tokenHold I.desc template d born = landFloor I.desc template t.initial d := by
        simp [tokenHold, hphase, hty]
      rw [hhold]
      exact Int.ofNat_le.mpr (Nat.sub_le (budget I.desc template d) (debt I.desc template t.initial d))
    · have hs := hst i
      rw [if_neg hi] at hs
      rw [hs] at hl ⊢
      exact hO.slack i d hl
  · intro s d hs hterm
    rw [hr] at hs
    rcases List.mem_append.mp hs with hs | hs
    · rw [howed d s]
      exact hO.still s d hs hterm
    · simp [List.mem_singleton] at hs
      subst hs
      have h0 : owed w.st d id w.roster = 0 :=
        owed_out w.st d id w.roster (fun host hhost =>
          ⟨fun m hm heq => hfresh (by simpa [heq] using hO.sentFrom host m hm),
            fun p hp heq => hfresh (by simpa [heq] using hO.parkFrom host p hp)⟩)
      rw [howed d id, h0]
      exact Nat.zero_le _
  · intro hcr s d hs hdead
    have hcr0 : w.crashed = false := by simpa [hcrash] using hcr
    rw [hr] at hs
    rcases List.mem_append.mp hs with hs | hs
    · rw [howed d s]
      have hdead0 : (w.st s).life ≠ .alive := by
        have hne : s ≠ id := fun h => hfresh (by simpa [h] using hs)
        have hss := hst s
        rw [if_neg hne] at hss
        simpa [hss] using hdead
      exact hO.quiet hcr0 s d hs hdead0
    · simp [List.mem_singleton] at hs
      subst hs
      exact absurd (by simpa [hself] using hlife) hdead
  · intro hcr i hdead
    have hcr0 : w.crashed = false := by simpa [hcrash] using hcr
    by_cases hi : i = id
    · subst hi
      have hl : (wP.st id).life = .alive := by simpa [hself] using hlife
      rcases hdead with h | h
      · simp [hl] at h
      · simp [hl] at h
    · have hs := hst i
      rw [if_neg hi] at hs
      rw [hs] at hdead ⊢
      exact hO.deadEmpty hcr0 i hdead
  · intro host
    refine ⟨?_, ?_⟩
    · intro m hm
      by_cases hh : host = id
      · simp [hst host, if_pos hh, hbox] at hm
      · have hm0 : m ∈ (w.st host).box := by
          have hs := hst host
          rw [if_neg hh] at hs
          simpa [hs] using hm
        exact (hO.sameKey host).1 m hm0
    · intro p hp
      by_cases hh : host = id
      · simp [hst host, if_pos hh, hpark] at hp
      · have hp0 : p ∈ (w.st host).parked := by
          have hs := hst host
          rw [if_neg hh] at hs
          simpa [hs] using hp
        exact (hO.sameKey host).2 p hp0
  · intro i hi
    rw [hr] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hO.shaped i hi
    · simp [List.mem_singleton] at hi
      subst hi
      refine ⟨t, ?_, ?_⟩
      · simpa [hid, tname] using ht
      · simp only [hmul]
        have hnm : t.name = template := (templateOf_mem I.desc template t ht).2
        exact ⟨k, maxGen w template k, by simp [hid, hnm]⟩
  · intro host hk
    have hne : host ≠ id := by
      intro heq
      have : peerKey id = none := by simpa [heq] using hk
      simp [hid, peerKey] at this
    refine ⟨?_, ?_⟩
    · intro m hm
      have hm0 : m ∈ (w.st host).box := by
        have hs := hst host
        rw [if_neg hne] at hs
        simpa [hs] using hm
      exact (hO.coreFrom host hk).1 m hm0
    · intro p hp
      have hp0 : p ∈ (w.st host).parked := by
        have hs := hst host
        rw [if_neg hne] at hs
        simpa [hs] using hp
      exact (hO.coreFrom host hk).2 p hp0
  · exact hix

theorem occ_spawn (I : Impl) (hG : GraphOk I.desc) (w w' : World) (template : String)
    (hO : OccInv I w) (h : spawn I w template = some w') : OccInv I w' := by
  unfold spawn at h
  cases htmpl : templateOf I.desc template with
  | none => simp [htmpl] at h
  | some t =>
    simp only [htmpl] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · have ⟨hmul, hslots⟩ := may_peer I.desc w template t hmay
      rw [hmay] at h
      rw [ite_eq_left (by decide : true = true)] at h
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at h
        dsimp at h
        let k := freshKey I.desc w t.subtree
        let parent : Option InstId := some (InstId.core name)
        let bump : World → World := fun u =>
          { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
        let id := InstId.peer template k (maxGen w template k)
        have hid : id = InstId.peer template k (maxGen w template k) := rfl
        have hsubNe : t.subtree ≠ "" := supervised_subtree I.desc hG template t htmpl hslots name hsup
        have htree : templateSubtree I.desc template = t.subtree := by simp [templateSubtree, htmpl]
        have hkey : ∀ g, InstId.peer template k g ∉ w.roster := by
          intro g hg
          exact Nat.lt_irrefl _ (fresh_below I.desc w t.subtree template k g hsubNe htree hg)
        have hcount : aliveCount w template < w.N :=
          Nat.lt_of_le_of_lt (alive_le_root I w hO template t htmpl hmul name)
            (may_root_lt I.desc w template t hmay name hsup)
        have hrP := place_roster I w template k t.initial parent bump (fun _ => rfl)
        have hixn : ∀ n, (placePeer I w template k t.initial parent bump).nextIx n = w.nextIx n := by
          intro n
          rw [place_nextIx I w template k t.initial parent bump n]
        have hix := ix_kept I w hO template t htmpl k id hid
          (placePeer I w template k t.initial parent bump) hrP hixn
          (Or.inl (by
            intro hnone
            rw [hsup] at hnone
            cases hnone))
        injection h with hw
        subst hw
        exact occ_born I w hO template t htmpl hmul k parent bump hkey hcount hix
          (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      | none =>
        rw [hsup] at h
        dsimp at h
        by_cases hsub : (t.subtree == "") = true
        · rw [hsub] at h
          rw [ite_eq_left (by decide : true = true)] at h
          let k := w.nextIx template
          let parent : Option InstId := none
          let bump : World → World := fun u =>
            { u with nextIx := fun n => if n = template then k + 1 else u.nextIx n }
          let id := InstId.peer template k (maxGen w template k)
          have hid : id = InstId.peer template k (maxGen w template k) := rfl
          have hsubE : t.subtree = "" := by simpa [beq_iff_eq] using hsub
          have hkey : ∀ g, InstId.peer template k g ∉ w.roster := by
            intro g hg
            exact Nat.lt_irrefl _ (hO.ixFresh template k g hg t htmpl hsup hsubE hslots)
          have hcount : aliveCount w template < w.N :=
            Nat.lt_of_le_of_lt (alive_le_lone I w hO template t htmpl hmul)
              (may_lone_lt I.desc w template t hmay hsup)
          have hrP := place_roster I w template k t.initial parent bump (fun _ => rfl)
          have hixn : ∀ n, (placePeer I w template k t.initial parent bump).nextIx n =
              if n = template then k + 1 else w.nextIx n := by
            intro n
            rw [place_nextIx I w template k t.initial parent bump n]
          have hix := ix_bumped I w hO template t htmpl hsup hsubE hslots k rfl id hid
            (placePeer I w template k t.initial parent bump) hrP hixn
          injection h with hw
          subst hw
          exact occ_born I w hO template t htmpl hmul k parent bump hkey hcount hix
            (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        · have hf : (t.subtree == "") = false := by
            cases hbb : t.subtree == ""
            · rfl
            · exact absurd hbb hsub
          rw [hf] at h
          rw [ite_eq_right (by decide : ¬ false = true)] at h
          let k := freshKey I.desc w t.subtree
          let parent : Option InstId := none
          let bump : World → World := fun u =>
            { u with nextKey := fun s => if s = t.subtree then k + 1 else u.nextKey s }
          let id := InstId.peer template k (maxGen w template k)
          have hid : id = InstId.peer template k (maxGen w template k) := rfl
          have hsubNe : t.subtree ≠ "" := by
            intro heq
            simp [beq_iff_eq, heq] at hf
          have htree : templateSubtree I.desc template = t.subtree := by simp [templateSubtree, htmpl]
          have hkey : ∀ g, InstId.peer template k g ∉ w.roster := by
            intro g hg
            exact Nat.lt_irrefl _ (fresh_below I.desc w t.subtree template k g hsubNe htree hg)
          have hcount : aliveCount w template < w.N :=
            Nat.lt_of_le_of_lt (alive_le_lone I w hO template t htmpl hmul)
              (may_lone_lt I.desc w template t hmay hsup)
          have hrP := place_roster I w template k t.initial parent bump (fun _ => rfl)
          have hixn : ∀ n, (placePeer I w template k t.initial parent bump).nextIx n = w.nextIx n := by
            intro n
            rw [place_nextIx I w template k t.initial parent bump n]
          have hix := ix_kept I w hO template t htmpl k id hid
            (placePeer I w template k t.initial parent bump) hrP hixn (Or.inr hsubNe)
          injection h with hw
          subst hw
          exact occ_born I w hO template t htmpl hmul k parent bump hkey hcount hix
            (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    · have hf : maySpawnRoot I.desc w template t = false := by
        cases hbb : maySpawnRoot I.desc w template t
        · rfl
        · exact absurd hbb hmay
      rw [hf] at h
      rw [ite_eq_right (by decide : ¬ false = true)] at h
      cases h
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

/-- Occupancy talks about the roster and actor map. Failures do not. -/
theorem occ_of_core (I : Impl) (w1 w2 : World) (hN : w1.N = w2.N) (hr : w1.roster = w2.roster)
    (hix : w1.nextIx = w2.nextIx) (hst : w1.st = w2.st) (hcr : w1.crashed = w2.crashed)
    (h : OccInv I w1) : OccInv I w2 := by
  exact occ_same I w1 w2 h (fun i => (congrFun hst i).symm) hr.symm hN.symm
    (fun n => (congrFun hix n).symm) hcr.symm

theorem occ_note (I : Impl) (w : World) (id : InstId) (dst : String) (a : Actor)
    (h : OccInv I (setActor w id a)) : OccInv I (setActor (noteStale w id dst) id a) := by
  apply occ_of_core I (setActor w id a) (setActor (noteStale w id dst) id a) _ _ _ _ _ h
  · simp [setActor, noteStale]
  · simp [setActor, noteStale]
  · simp [setActor, noteStale]
  · funext i
    simp [setActor, noteStale]
  · simp [setActor, noteStale]

/-- A `trySend` that fits spends one token and stores the message.
A miss, a dead target, or a full mailbox continues on the arm the reserve
already counted, and spends nothing. A lone terminable may be the sender. -/
theorem occ_try (I : Impl) (_hL : LocalOk I) (w : World) (id : InstId) (k : Cont)
    (dstName label : String) (hint : Nat) (onFull onGone es : List Eff) (hO : OccInv I w)
    (_hT : TyOk I.desc w) (hph : (w.st id).phase = .run k)
    (hk : k.rest = .trySend dstName label hint onFull onGone :: es)
    (hty : (w.st id).typestate = k.toState) (hsender : (w.st id).life = .alive)
    (hbulk : bulkScopeOf I.desc (tname id) k.rest = true) :
    OccInv I (execRun I w id (w.st id) k) := by
  have hb : ((w.st id).life == .alive) = true := beq_iff_eq.mpr hsender
  simp only [execRun, hb, hk]
  let gone : Cont :=
    { afterHead k with rest := onGone, toState := pickState (afterHead k).toState k.toGone }
  let full : Cont :=
    { afterHead k with rest := onFull, toState := pickState (afterHead k).toState k.toFull }
  cases hr : route w I.desc id dstName hint with
  | none =>
    simp only [hr]
    apply occ_note I w id dstName (proceed (w.st id) gone)
    apply occ_keep I w id (proceed (w.st id) gone) hO (proceed_life _ _) (proceed_box _ _)
      (proceed_parked _ _) (proceed_tokens _ _)
    intro d _
    exact Int.ofNat_le.mpr (tokenHold_try_arm I.desc (tname id) d dstName (w.st id) k
      label hint onFull onGone onGone k.toGone es hph hk (Or.inr ⟨rfl, rfl⟩))
  | some dstId =>
    simp only [hr]
    have hname := route_tname w I.desc id dstName hint dstId hr
    by_cases hlive : (w.st dstId).life = .alive
    · by_cases hpark : (w.st dstId).parked = []
      · by_cases hcap : (w.st dstId).box.length < capBulk I.desc w.N dstId
        · have hgo :
              (((w.st dstId).life == .alive) && decide ((w.st dstId).parked = []) &&
                decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true := by
            simp [beq_iff_eq.mpr hlive, hpark, hcap]
          simp only [hgo]
          by_cases hsame : id = dstId
          · subst hsame
            have hk' : k.rest = .trySend (tname id) label hint onFull onGone :: es := by
              simpa [hname] using hk
            exact occ_self_send I w id
              { label := label, sender := id, callFrom := none, reliable := false }
              k (.trySend (tname id) label hint onFull onGone) es label hint hO hph hk'
              (Or.inr (Or.inr ⟨onFull, onGone, rfl⟩)) rfl hty hsender hpark hcap
          · have hk' : k.rest = .trySend (tname dstId) label hint onFull onGone :: es := by
              simpa [hname] using hk
            have hbulk' : bulkScopeOf I.desc (tname id)
                (.trySend (tname dstId) label hint onFull onGone :: es) = true := by
              simpa [hk'] using hbulk
            exact occ_other_send I w id dstId
              { label := label, sender := id, callFrom := none, reliable := false }
              k (.trySend (tname dstId) label hint onFull onGone) es label hint hO hph hk'
              (Or.inr (Or.inr ⟨onFull, onGone, rfl⟩)) rfl hty hsender (fun h => hsame h)
              hlive hpark hcap (route_agrees w I.desc id dstName hint dstId hr)
              (fun hpk => core_send_from I w hO id dstId
                (.trySend (tname dstId) label hint onFull onGone) es
                (hO.aliveIn dstId hlive) (hO.aliveIn id hsender) hbulk'
                ⟨label, hint, Or.inr (Or.inr ⟨onFull, onGone, rfl⟩)⟩ hpk)
        · have hliveB : ((w.st dstId).life == .alive) = true := beq_iff_eq.mpr hlive
          have hbad :
              ((true && decide ((w.st dstId).parked = []) &&
                decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true) = False := by
            simp [hcap]
          simp only [hliveB, hbad]
          apply occ_keep I w id (proceed (w.st id) full) hO (proceed_life _ _) (proceed_box _ _)
            (proceed_parked _ _) (proceed_tokens _ _)
          intro d _
          exact Int.ofNat_le.mpr (tokenHold_try_arm I.desc (tname id) d dstName (w.st id) k
            label hint onFull onGone onFull k.toFull es hph hk (Or.inl ⟨rfl, rfl⟩))
      · have hliveB : ((w.st dstId).life == .alive) = true := beq_iff_eq.mpr hlive
        have hbad :
            ((true && decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true) = False := by
          simp [hpark]
        simp only [hliveB, hbad]
        apply occ_keep I w id (proceed (w.st id) full) hO (proceed_life _ _) (proceed_box _ _)
          (proceed_parked _ _) (proceed_tokens _ _)
        intro d _
        exact Int.ofNat_le.mpr (tokenHold_try_arm I.desc (tname id) d dstName (w.st id) k
          label hint onFull onGone onFull k.toFull es hph hk (Or.inl ⟨rfl, rfl⟩))
    · have hliveB : ((w.st dstId).life == .alive) = false := by
        cases hbb : (w.st dstId).life == .alive with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hbb) hlive
      have hstop :
          (((w.st dstId).life == .alive) && decide ((w.st dstId).parked = []) &&
            decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = false := by
        simp [hliveB]
      simp only [hstop, hliveB]
      apply occ_keep I w id (proceed (w.st id) gone) hO (proceed_life _ _) (proceed_box _ _)
        (proceed_parked _ _) (proceed_tokens _ _)
      intro d _
      exact Int.ofNat_le.mpr (tokenHold_try_arm I.desc (tname id) d dstName (w.st id) k
        label hint onFull onGone onGone k.toGone es hph hk (Or.inr ⟨rfl, rfl⟩))

def drainBox (w : World) (id : InstId) (dst : String) : List Msg → World
  | [] => setActor w id { (w.st id) with box := [] }
  | m :: ms =>
    drainBox (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender) id dst ms

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

/-- Messages whose refund lands on `holder`: the live generation of the key, or
the sender itself when nobody of that key is alive. -/
def liveCount (w : World) (holder : InstId) : List Msg → Nat
  | [] => 0
  | m :: ms => (if holder = budgetHolder w m.sender then 1 else 0) + liveCount w holder ms

theorem findLive_credit (w : World) (dst : String) (s : InstId) (name : String) (key : Nat) :
    findLive (creditLive w dst s) name key = findLive w name key := by
  unfold creditLive creditSender
  exact findLive_set_life w (budgetHolder w s)
    (bumpToken (w.st (budgetHolder w s)) dst (.ofNat 1)) (by simp [bumpToken]) name key

theorem holder_credit (w : World) (dst : String) (s sender : InstId) :
    budgetHolder (creditLive w dst s) sender = budgetHolder w sender := by
  cases sender with
  | core _ => rfl
  | peer name key _ =>
    simp only [budgetHolder, findLive_credit]

theorem findLive_boxset (w : World) (id : InstId) (ms : List Msg) (name : String) (key : Nat) :
    findLive (setActor w id { (w.st id) with box := ms }) name key = findLive w name key :=
  findLive_set_life w id { (w.st id) with box := ms } (by simp) name key

theorem holder_boxset (w : World) (id : InstId) (ms : List Msg) (sender : InstId) :
    budgetHolder (setActor w id { (w.st id) with box := ms }) sender = budgetHolder w sender := by
  cases sender with
  | core _ => rfl
  | peer name key _ => simp only [budgetHolder, findLive_boxset]

theorem liveCount_boxset (w : World) (id : InstId) (box : List Msg) (holder : InstId) :
    ∀ ms, liveCount (setActor w id { (w.st id) with box := box }) holder ms = liveCount w holder ms
  | [] => rfl
  | m :: ms => by
    simp only [liveCount, holder_boxset, liveCount_boxset w id box holder ms]

theorem liveCount_credit (w : World) (dst : String) (s holder : InstId) :
    ∀ ms, liveCount (creditLive w dst s) holder ms = liveCount w holder ms
  | [] => rfl
  | m :: ms => by
    simp only [liveCount, holder_credit, liveCount_credit w dst s holder ms]

theorem credit_live_tok (w : World) (dst : String) (sender i : InstId) (d : String) :
    ((creditLive w dst sender).st i).tokens d =
      (w.st i).tokens d + if i = budgetHolder w sender ∧ d = dst then 1 else 0 := by
  simp [creditLive, credit_tok]

theorem refund_tok (w : World) (dst : String) (ms : List Msg) (i : InstId) (d : String) :
    ((refundMsgs w dst ms).st i).tokens d =
      (w.st i).tokens d + if d = dst then liveCount w i ms else 0 := by
  induction ms generalizing w with
  | nil => simp [refundMsgs, liveCount]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_live_tok, liveCount_credit w dst m.sender i ms, liveCount]
    by_cases hd : d = dst
    · by_cases hs : i = budgetHolder w m.sender
      · simp [hd, hs]
        rw [Int.add_assoc]
      · simp [hd, hs, Int.zero_add]
    · simp [hd]

theorem refund_box (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).box = (w.st i).box := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, credit_box]

theorem refund_park (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
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
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold]
    have hc := credit_life w dst (budgetHolder w m.sender) i
    have hi := ih (creditLive w dst m.sender)
    simp [hc] at hi
    exact hi

theorem clear_tok (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) (d : String) :
    ((refundClearBox w id dst ms).st i).tokens d =
      (w.st i).tokens d + if d = dst then liveCount w i ms else 0 := by
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
      (w.st i).tokens d + if d = dst then liveCount w i ms else 0 := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor, liveCount]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox, liveCount]
    have hset : ∀ j, ((setActor w id { (w.st id) with box := ms }).st j).tokens d = (w.st j).tokens d := by
      intro j
      by_cases hj : j = id <;> simp [setActor, hj]
    have hcred := credit_live_tok (setActor w id { (w.st id) with box := ms }) dst m.sender i d
    rw [hset] at hcred
    have hih := ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)
    rw [hih, hcred, liveCount_credit, liveCount_boxset w id ms i ms, holder_boxset w id ms m.sender]
    by_cases hd : d = dst
    · by_cases hs : i = budgetHolder w m.sender
      · simp [hd, hs]
        rw [Int.add_assoc]
      · simp [hd, hs, Int.zero_add]
    · simp [hd]

theorem drain_box (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).box = if i = id then [] else (w.st i).box := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox, creditLive]
    have hbox0 : ((setActor w id { (w.st id) with box := ms }).st i).box =
        if i = id then ms else (w.st i).box := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hcred := credit_box (setActor w id { (w.st id) with box := ms }) dst
      (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender) i
    rw [ih, hcred, hbox0]
    by_cases hi : i = id <;> simp [hi]

theorem drain_park (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).parked = (w.st i).parked := by
  induction ms generalizing w with
  | nil =>
    simp [drainBox, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons m ms ih =>
    simp [drainBox, creditLive]
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
    simp [drainBox, creditLive]
    have hL : ((setActor w id { (w.st id) with box := ms }).st i).life = (w.st i).life ∧
        ((setActor w id { (w.st id) with box := ms }).st i).typestate = (w.st i).typestate ∧
        ((setActor w id { (w.st id) with box := ms }).st i).phase = (w.st i).phase ∧
        ((setActor w id { (w.st id) with box := ms }).st i).prio = (w.st i).prio := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := credit_life (setActor w id { (w.st id) with box := ms }) dst
      (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender) i
    have hi := ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)
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
    simp [drainBox, creditLive]
    have hset : ((setActor w id { (w.st id) with box := ms }).st i).nextMid = (w.st i).nextMid := by
      by_cases hi : i = id <;> simp [setActor, hi]
    exact (ih _).trans ((credit_mid _ _ _ _).trans hset)

theorem refund_mid (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).nextMid = (w.st i).nextMid := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    exact (hfold ▸ ih _).trans (credit_mid w dst (budgetHolder w m.sender) i)

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
    simp [drainBox, creditLive]
    have hset : sameStamps ((setActor w id { (w.st id) with box := ms }).st i) (w.st i) := by
      by_cases hi : i = id <;> simp [sameStamps, setActor, hi]
    exact sameStamps_trans (ih _) (sameStamps_trans (credit_stamps _ _ _ _) hset)

theorem refund_stamps (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    sameStamps ((refundMsgs w dst ms).st i) (w.st i) := by
  induction ms generalizing w with
  | nil => simp [sameStamps, refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    exact sameStamps_trans (hfold ▸ ih _) (credit_stamps w dst (budgetHolder w m.sender) i)

theorem clear_stamps (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    sameStamps ((refundClearBox w id dst ms).st i) (w.st i) := by
  have hset : sameStamps ((refundClearBox w id dst ms).st i) ((refundMsgs w dst ms).st i) := by
    by_cases hi : i = id <;> simp [sameStamps, refundClearBox, setActor, hi]
  exact sameStamps_trans hset (refund_stamps w dst ms i)

theorem actor_fields (a b : Actor) (hl : a.life = b.life) (ht : a.typestate = b.typestate)
    (hp : a.phase = b.phase) (hb : a.box = b.box) (hpr : a.prio = b.prio) (hpk : a.parked = b.parked)
    (htk : ∀ d, a.tokens d = b.tokens d) (hm : a.nextMid = b.nextMid)
    (hw : a.waitId = b.waitId) (hn : a.nextCall = b.nextCall) (ho : a.oweId = b.oweId)
    (hc : a.lastCall = b.lastCall) (hpend : a.pendingTombstone = b.pendingTombstone)
    (hpar : a.parent = b.parent) : a = b := by
  cases a
  cases b
  congr
  funext d
  simpa using (htk d)

theorem creditWorld (w : World) (dst : String) (s : InstId) :
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
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold]
    have hc := creditWorld w dst (budgetHolder w m.sender)
    have hi := ih (creditLive w dst m.sender)
    exact ⟨hi.1.trans hc.1, hi.2.1.trans hc.2.1, hi.2.2.1.trans hc.2.2.1,
      hi.2.2.2.1.trans hc.2.2.2.1, hi.2.2.2.2.trans hc.2.2.2.2⟩

theorem setWorld (w : World) (id : InstId) (a : Actor) :
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
    simp [drainBox, creditLive]
    have hs := setWorld w id { (w.st id) with box := ms }
    have hc := creditWorld (setActor w id { (w.st id) with box := ms }) dst
      (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender)
    have hi := ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)
    exact ⟨hi.1.trans (hc.1.trans hs.1), hi.2.1.trans (hc.2.1.trans hs.2.1),
      hi.2.2.1.trans (hc.2.2.1.trans hs.2.2.1), hi.2.2.2.1.trans (hc.2.2.2.1.trans hs.2.2.2.1),
      hi.2.2.2.2.trans (hc.2.2.2.2.trans hs.2.2.2.2)⟩

theorem frame_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (refundClearBox w id dst ms).N = w.N ∧ (refundClearBox w id dst ms).roster = w.roster ∧
      (refundClearBox w id dst ms).nextIx = w.nextIx ∧ (refundClearBox w id dst ms).cell = w.cell ∧
      (refundClearBox w id dst ms).observed = w.observed := by
  simp [refundClearBox, setActor, frame_refund]

theorem world_eq (w1 w2 : World) (hN : w1.N = w2.N) (hr : w1.roster = w2.roster)
    (hix : w1.nextIx = w2.nextIx) (hkey : w1.nextKey = w2.nextKey) (hst : w1.st = w2.st)
    (hc : w1.cell = w2.cell) (ho : w1.observed = w2.observed) (hf : w1.failures = w2.failures)
    (hcr : w1.crashed = w2.crashed) : w1 = w2 := by
  cases w1
  cases w2
  cases hN
  cases hr
  cases hix
  cases hkey
  cases hst
  cases hc
  cases ho
  cases hf
  cases hcr
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
    exact (ih (creditLive w dst m.sender)).trans (meta_credit w dst (budgetHolder w m.sender))

theorem meta_drain (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (drainBox w id dst ms).failures = w.failures := by
  induction ms generalizing w with
  | nil => simp [drainBox, setActor]
  | cons m ms ih =>
    simp [drainBox, creditLive]
    exact (ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)).trans
      ((meta_credit (setActor w id { (w.st id) with box := ms }) dst
        (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender)).trans
        (meta_set w id { (w.st id) with box := ms }))

theorem meta_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (refundClearBox w id dst ms).failures = w.failures := by
  simp [refundClearBox, setActor, meta_refund]

theorem kept_credit (w : World) (dst : String) (s : InstId) :
    (creditSender w dst s).nextKey = w.nextKey ∧ (creditSender w dst s).crashed = w.crashed := by
  simp [creditSender, setActor]

theorem kept_set (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).nextKey = w.nextKey ∧ (setActor w id a).crashed = w.crashed := by
  simp [setActor]

theorem kept_refund (w : World) (dst : String) (ms : List Msg) :
    (refundMsgs w dst ms).nextKey = w.nextKey ∧ (refundMsgs w dst ms).crashed = w.crashed := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    have hc := kept_credit w dst (budgetHolder w m.sender)
    have hi := hfold ▸ ih (creditLive w dst m.sender)
    exact ⟨hi.1.trans hc.1, hi.2.trans hc.2⟩

theorem kept_drain (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (drainBox w id dst ms).nextKey = w.nextKey ∧ (drainBox w id dst ms).crashed = w.crashed := by
  induction ms generalizing w with
  | nil => simp [drainBox, setActor]
  | cons m ms ih =>
    simp [drainBox, creditLive]
    have hs := kept_set w id { (w.st id) with box := ms }
    have hc := kept_credit (setActor w id { (w.st id) with box := ms }) dst
      (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender)
    have hi := ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)
    exact ⟨hi.1.trans (hc.1.trans hs.1), hi.2.trans (hc.2.trans hs.2)⟩

theorem kept_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) :
    (refundClearBox w id dst ms).nextKey = w.nextKey ∧
      (refundClearBox w id dst ms).crashed = w.crashed := by
  simp [refundClearBox, setActor, kept_refund]

theorem actor_kept_credit (w : World) (dst : String) (s i : InstId) :
    ((creditSender w dst s).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((creditSender w dst s).st i).parent = (w.st i).parent := by
  by_cases hi : i = s <;> simp [creditSender, setActor, bumpToken, hi]

theorem actor_kept_refund (w : World) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundMsgs w dst ms).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((refundMsgs w dst ms).st i).parent = (w.st i).parent := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    have hc := actor_kept_credit w dst (budgetHolder w m.sender) i
    have hi := hfold ▸ ih (creditLive w dst m.sender)
    exact ⟨hi.1.trans hc.1, hi.2.trans hc.2⟩

theorem actor_kept_drain (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((drainBox w id dst ms).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((drainBox w id dst ms).st i).parent = (w.st i).parent := by
  induction ms generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [drainBox, setActor, hi]
  | cons m ms ih =>
    simp [drainBox, creditLive]
    have hset : ((setActor w id { (w.st id) with box := ms }).st i).pendingTombstone =
          (w.st i).pendingTombstone ∧
        ((setActor w id { (w.st id) with box := ms }).st i).parent = (w.st i).parent := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := actor_kept_credit (setActor w id { (w.st id) with box := ms }) dst
      (budgetHolder (setActor w id { (w.st id) with box := ms }) m.sender) i
    have hi := ih (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender)
    exact ⟨hi.1.trans (hc.1.trans hset.1), hi.2.trans (hc.2.trans hset.2)⟩

theorem actor_kept_clear (w : World) (id : InstId) (dst : String) (ms : List Msg) (i : InstId) :
    ((refundClearBox w id dst ms).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((refundClearBox w id dst ms).st i).parent = (w.st i).parent := by
  have hR := actor_kept_refund w dst ms i
  by_cases hi : i = id
  · subst hi
    simp [refundClearBox, setActor]
    exact hR
  · simp [refundClearBox, setActor, hi]
    exact hR

/-- Refunding every message and then clearing the box is the same as dropping
each message and crediting the live holder of its key. -/
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
    · exact (actor_kept_drain w id dst ms i).1.trans (actor_kept_clear w id dst ms i).1.symm
    · exact (actor_kept_drain w id dst ms i).2.trans (actor_kept_clear w id dst ms i).2.symm
  have hM := meta_drain w id dst ms
  have hMc := meta_clear w id dst ms
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm)
    ((kept_drain w id dst ms).1.trans (kept_clear w id dst ms).1.symm) hst
    (hD.2.2.2.1.trans hC.2.2.2.1.symm) (hD.2.2.2.2.trans hC.2.2.2.2.symm)
    (hM.trans hMc.symm) ((kept_drain w id dst ms).2.trans (kept_clear w id dst ms).2.symm)

theorem occ_drop_box (I : Impl) (w : World) (id : InstId) (m : Msg) (ms : List Msg) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hbox : (w.st id).box = m :: ms) (hcr : w.crashed = false) :
    OccInv I (creditLive (setActor w id { (w.st id) with box := ms }) (tname id) m.sender) := by
  have hsend : m.sender ∈ w.roster := hO.sentFrom id m (by rw [hbox]; exact List.Mem.head _)
  let a1 : Actor := { (w.st id) with box := ms }
  apply occ_consume I w w id m.sender a1 hO (fun _ => rfl) rfl rfl (fun _ => rfl) rfl
    (by simp [a1]) (fun _ => rfl) hmem hsend
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
  · intro name key d
    have hdelta :
        ((w.st id).box.filter (keyPred name key)).length +
          ((w.st id).parked.filter fun p => keyPred name key p.msg).length =
        (a1.box.filter (keyPred name key)).length +
          (a1.parked.filter fun p => keyPred name key p.msg).length +
          (if keyPred name key m = true then 1 else 0) := by
      simp [a1, hbox, List.filter]
      cases hk : keyPred name key m <;> simp [hk] <;> omega
    have hrep := queuedFromKey_replace w id a1 name key d
      (if keyPred name key m = true then 1 else 0) hO.nodup hmem hdelta
    rw [hrep, Int.natCast_add, cast_keybit (tname id) d (keyPred name key m),
      queueDrop_msg m.sender m name key d (tname id) rfl]
    omega
  · intro d
    have hsame : tokenHold I.desc (tname id) d a1 = tokenHold I.desc (tname id) d (w.st id) := by
      simp [a1, tokenHold]
    exact Nat.le_of_eq hsame
  · intro m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact hO.sentFrom id m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro p hp
    exact hO.parkFrom id p (by simpa [a1] using hp)
  · intro p hp
    exact hO.parkMsg id p (by simpa [a1] using hp)
  · intro m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact (hO.sameKey id).1 m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro p hp
    exact (hO.sameKey id).2 p (by simpa [a1] using hp)
  · intro hdead
    simp [a1] at hdead
    have hlife : (w.st id).life = .absent ∨ (w.st id).life = .dead := by
      cases h : (w.st id).life
      · exact Or.inl rfl
      · exact absurd h hdead
      · exact Or.inr rfl
    have hempty := (hO.deadEmpty hcr id hlife).1
    rw [hbox] at hempty
    simp at hempty
  · intro hk m' hm'
    have hm0 : m' ∈ ms := by simpa [a1] using hm'
    exact (hO.coreFrom id hk).1 m' (by rw [hbox]; exact List.mem_cons.mpr (Or.inr hm0))
  · intro hk p hp
    exact (hO.coreFrom id hk).2 p (by simpa [a1] using hp)

theorem occ_drain_box (I : Impl) (w : World) (id : InstId) (ms : List Msg) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hbox : (w.st id).box = ms) (hcr : w.crashed = false) :
    OccInv I (drainBox w id (tname id) ms) := by
  induction ms generalizing w with
  | nil =>
    have hempty : (w.st id).box = [] := hbox
    apply occ_keep I w id ({ (w.st id) with box := [] }) hO rfl (by simp [hempty]) rfl (fun _ => rfl)
    intro d _
    simp [tokenHold]
  | cons m ms ih =>
    have hstep := occ_drop_box I w id m ms hO hmem hbox hcr
    have hbox1 : ((creditLive (setActor w id { (w.st id) with box := ms }) (tname id) m.sender).st id).box = ms := by
      rw [creditLive, credit_box]
      simp [setActor]
    have hmem1 : id ∈ (creditLive (setActor w id { (w.st id) with box := ms }) (tname id) m.sender).roster := by
      simpa [creditLive, creditSender, setActor] using hmem
    have hcr1 : (creditLive (setActor w id { (w.st id) with box := ms }) (tname id) m.sender).crashed =
        w.crashed := by simp [creditLive, creditSender, setActor]
    simpa [drainBox] using ih _ hstep hmem1 hbox1 (hcr1.trans hcr)

def countCredited (sender : InstId) : List Parked → Nat
  | [] => 0
  | p :: ps => (if p.msg.sender = sender then 1 else 0) + countCredited sender ps

def drainPark (w : World) (id : InstId) (dst : String) : List Parked → World
  | [] => setActor w id { (w.st id) with parked := [] }
  | p :: ps =>
    drainPark (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender) id dst ps

def refundClearPark (w : World) (id : InstId) (dst : String) (ps : List Parked) : World :=
  let wR := refundParked w dst ps
  setActor wR id { (wR.st id) with parked := [] }

theorem meta_refundP (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).failures = w.failures := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    simp [refundParked, List.foldl_cons]
    exact (ih (creditLive w dst p.msg.sender)).trans (meta_credit w dst (budgetHolder w p.msg.sender))

theorem meta_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (drainPark w id dst ps).failures = w.failures := by
  induction ps generalizing w with
  | nil => simp [drainPark, setActor]
  | cons p ps ih =>
    simp [drainPark, creditLive]
    exact (ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)).trans
      ((meta_credit (setActor w id { (w.st id) with parked := ps }) dst
        (budgetHolder (setActor w id { (w.st id) with parked := ps }) p.msg.sender)).trans
        (meta_set w id { (w.st id) with parked := ps }))

theorem meta_clearP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (refundClearPark w id dst ps).failures = w.failures := by
  simp [refundClearPark, setActor, meta_refundP]

/-- Parked messages whose refund lands on `holder`. -/
def livePark (w : World) (holder : InstId) : List Parked → Nat
  | [] => 0
  | p :: ps => (if holder = budgetHolder w p.msg.sender then 1 else 0) + livePark w holder ps

theorem findLive_parkset (w : World) (id : InstId) (ps : List Parked) (name : String) (key : Nat) :
    findLive (setActor w id { (w.st id) with parked := ps }) name key = findLive w name key :=
  findLive_set_life w id { (w.st id) with parked := ps } (by simp) name key

theorem holder_parkset (w : World) (id : InstId) (ps : List Parked) (sender : InstId) :
    budgetHolder (setActor w id { (w.st id) with parked := ps }) sender = budgetHolder w sender := by
  cases sender with
  | core _ => rfl
  | peer name key _ => simp only [budgetHolder, findLive_parkset]

theorem livePark_boxset (w : World) (id : InstId) (box : List Msg) (holder : InstId) :
    ∀ ps, livePark (setActor w id { (w.st id) with box := box }) holder ps = livePark w holder ps
  | [] => rfl
  | p :: ps => by
    simp only [livePark, holder_boxset, livePark_boxset w id box holder ps]

theorem livePark_parkset (w : World) (id : InstId) (parked : List Parked) (holder : InstId) :
    ∀ ps, livePark (setActor w id { (w.st id) with parked := parked }) holder ps = livePark w holder ps
  | [] => rfl
  | p :: ps => by
    simp only [livePark, holder_parkset, livePark_parkset w id parked holder ps]

theorem livePark_credit (w : World) (dst : String) (s holder : InstId) :
    ∀ ps, livePark (creditLive w dst s) holder ps = livePark w holder ps
  | [] => rfl
  | p :: ps => by
    simp only [livePark, holder_credit, livePark_credit w dst s holder ps]

theorem livePark_drain (w : World) (id : InstId) (dst : String) (holder : InstId) :
    ∀ ms ps, livePark (drainBox w id dst ms) holder ps = livePark w holder ps
  | [], ps => livePark_boxset w id [] holder ps
  | m :: ms, ps => by
    simp only [drainBox]
    have hbox := livePark_boxset w id ms holder ps
    have hcred := livePark_credit (setActor w id { (w.st id) with box := ms }) dst m.sender holder ps
    have hih := livePark_drain
      (creditLive (setActor w id { (w.st id) with box := ms }) dst m.sender) id dst holder ms ps
    exact hih.trans (hcred.trans hbox)

theorem livePark_refund (w : World) (dst : String) (holder : InstId) :
    ∀ ms ps, livePark (refundMsgs w dst ms) holder ps = livePark w holder ps
  | [], ps => by simp [refundMsgs]
  | m :: ms, ps => by
    have hfold : refundMsgs w dst (m :: ms) = refundMsgs (creditLive w dst m.sender) dst ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, livePark_refund (creditLive w dst m.sender) dst holder ms ps,
      livePark_credit w dst m.sender holder ps]

theorem refundP_tok (w : World) (dst : String) (ps : List Parked) (i : InstId) (d : String) :
    ((refundParked w dst ps).st i).tokens d =
      (w.st i).tokens d + if d = dst then livePark w i ps else 0 := by
  induction ps generalizing w with
  | nil => simp [refundParked, livePark]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_live_tok, livePark_credit w dst p.msg.sender i ps, livePark]
    by_cases hd : d = dst
    · by_cases hs : i = budgetHolder w p.msg.sender
      · simp [hd, hs]
        rw [Int.add_assoc]
      · simp [hd, hs, Int.zero_add]
    · simp [hd]

theorem refundP_box (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, credit_box]

theorem refundP_park (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
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
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold]
    have hc := credit_life w dst (budgetHolder w p.msg.sender) i
    have hi := ih (creditLive w dst p.msg.sender)
    simp [hc] at hi
    exact hi

theorem clearP_tok (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) (d : String) :
    ((refundClearPark w id dst ps).st i).tokens d =
      (w.st i).tokens d + if d = dst then livePark w i ps else 0 := by
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
      (w.st i).tokens d + if d = dst then livePark w i ps else 0 := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor, livePark]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark, livePark]
    have hset : ∀ j, ((setActor w id { (w.st id) with parked := ps }).st j).tokens d = (w.st j).tokens d := by
      intro j
      by_cases hj : j = id <;> simp [setActor, hj]
    have hcred := credit_live_tok (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender i d
    rw [hset] at hcred
    have hih := ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    rw [hih, hcred, livePark_credit, livePark_parkset w id ps i ps, holder_parkset w id ps p.msg.sender]
    by_cases hd : d = dst
    · by_cases hs : i = budgetHolder w p.msg.sender
      · simp [hd, hs]
        rw [Int.add_assoc]
      · simp [hd, hs, Int.zero_add]
    · simp [hd]

theorem drainP_box (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil =>
    simp [drainPark, setActor]
    by_cases hi : i = id <;> simp [hi]
  | cons p ps ih =>
    simp [drainPark, creditLive]
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
    simp [drainPark, creditLive]
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
    simp [drainPark, creditLive]
    have hL : ((setActor w id { (w.st id) with parked := ps }).st i).life = (w.st i).life ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).typestate = (w.st i).typestate ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).phase = (w.st i).phase ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).prio = (w.st i).prio := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := credit_life (setActor w id { (w.st id) with parked := ps }) dst
      (budgetHolder (setActor w id { (w.st id) with parked := ps }) p.msg.sender) i
    have hi := ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    simp [hc, hL] at hi
    exact hi

theorem frame_refundP (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).N = w.N ∧ (refundParked w dst ps).roster = w.roster ∧
      (refundParked w dst ps).nextIx = w.nextIx ∧ (refundParked w dst ps).cell = w.cell ∧
      (refundParked w dst ps).observed = w.observed := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold]
    have hc := creditWorld w dst (budgetHolder w p.msg.sender)
    have hi := ih (creditLive w dst p.msg.sender)
    exact ⟨hi.1.trans hc.1, hi.2.1.trans hc.2.1, hi.2.2.1.trans hc.2.2.1,
      hi.2.2.2.1.trans hc.2.2.2.1, hi.2.2.2.2.trans hc.2.2.2.2⟩

theorem frame_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (drainPark w id dst ps).N = w.N ∧ (drainPark w id dst ps).roster = w.roster ∧
      (drainPark w id dst ps).nextIx = w.nextIx ∧ (drainPark w id dst ps).cell = w.cell ∧
      (drainPark w id dst ps).observed = w.observed := by
  induction ps generalizing w with
  | nil => simp [drainPark, setActor]
  | cons p ps ih =>
    simp [drainPark, creditLive]
    have hs := setWorld w id { (w.st id) with parked := ps }
    have hc := creditWorld (setActor w id { (w.st id) with parked := ps }) dst
      (budgetHolder (setActor w id { (w.st id) with parked := ps }) p.msg.sender)
    have hi := ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
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
    simp [drainPark, creditLive]
    have hset : ((setActor w id { (w.st id) with parked := ps }).st i).nextMid = (w.st i).nextMid := by
      by_cases hi : i = id <;> simp [setActor, hi]
    exact (ih _).trans ((credit_mid _ _ _ _).trans hset)

theorem refundP_mid (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).nextMid = (w.st i).nextMid := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    exact (hfold ▸ ih _).trans (credit_mid w dst (budgetHolder w p.msg.sender) i)

theorem clearP_mid (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).nextMid = (w.st i).nextMid := by
  by_cases hi : i = id <;> simp [refundClearPark, setActor, hi, refundP_mid]

theorem drainP_stamps (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((drainPark w id dst ps).st i) (w.st i) := by
  induction ps generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [sameStamps, drainPark, setActor, hi]
  | cons p ps ih =>
    simp [drainPark, creditLive]
    have hset : sameStamps ((setActor w id { (w.st id) with parked := ps }).st i) (w.st i) := by
      by_cases hi : i = id <;> simp [sameStamps, setActor, hi]
    exact sameStamps_trans (ih _) (sameStamps_trans (credit_stamps _ _ _ _) hset)

theorem refundP_stamps (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((refundParked w dst ps).st i) (w.st i) := by
  induction ps generalizing w with
  | nil => simp [sameStamps, refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    exact sameStamps_trans (hfold ▸ ih _) (credit_stamps w dst (budgetHolder w p.msg.sender) i)

theorem clearP_stamps (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    sameStamps ((refundClearPark w id dst ps).st i) (w.st i) := by
  have hset : sameStamps ((refundClearPark w id dst ps).st i) ((refundParked w dst ps).st i) := by
    by_cases hi : i = id <;> simp [sameStamps, refundClearPark, setActor, hi]
  exact sameStamps_trans hset (refundP_stamps w dst ps i)

theorem kept_refundP (w : World) (dst : String) (ps : List Parked) :
    (refundParked w dst ps).nextKey = w.nextKey ∧ (refundParked w dst ps).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    have hc := kept_credit w dst (budgetHolder w p.msg.sender)
    have hi := hfold ▸ ih (creditLive w dst p.msg.sender)
    exact ⟨hi.1.trans hc.1, hi.2.trans hc.2⟩

theorem kept_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (drainPark w id dst ps).nextKey = w.nextKey ∧ (drainPark w id dst ps).crashed = w.crashed := by
  induction ps generalizing w with
  | nil => simp [drainPark, setActor]
  | cons p ps ih =>
    simp [drainPark, creditLive]
    have hs := kept_set w id { (w.st id) with parked := ps }
    have hc := kept_credit (setActor w id { (w.st id) with parked := ps }) dst
      (budgetHolder (setActor w id { (w.st id) with parked := ps }) p.msg.sender)
    have hi := ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    exact ⟨hi.1.trans (hc.1.trans hs.1), hi.2.trans (hc.2.trans hs.2)⟩

theorem kept_clearP (w : World) (id : InstId) (dst : String) (ps : List Parked) :
    (refundClearPark w id dst ps).nextKey = w.nextKey ∧
      (refundClearPark w id dst ps).crashed = w.crashed := by
  simp [refundClearPark, setActor, kept_refundP]

theorem actor_kept_refundP (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((refundParked w dst ps).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w dst (p :: ps) = refundParked (creditLive w dst p.msg.sender) dst ps := by
      simp [refundParked, List.foldl_cons]
    have hc := actor_kept_credit w dst (budgetHolder w p.msg.sender) i
    have hi := hfold ▸ ih (creditLive w dst p.msg.sender)
    exact ⟨hi.1.trans hc.1, hi.2.trans hc.2⟩

theorem actor_kept_drainP (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((drainPark w id dst ps).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((drainPark w id dst ps).st i).parent = (w.st i).parent := by
  induction ps generalizing w with
  | nil =>
    by_cases hi : i = id <;> simp [drainPark, setActor, hi]
  | cons p ps ih =>
    simp [drainPark, creditLive]
    have hset : ((setActor w id { (w.st id) with parked := ps }).st i).pendingTombstone =
          (w.st i).pendingTombstone ∧
        ((setActor w id { (w.st id) with parked := ps }).st i).parent = (w.st i).parent := by
      by_cases hi : i = id <;> simp [setActor, hi]
    have hc := actor_kept_credit (setActor w id { (w.st id) with parked := ps }) dst
      (budgetHolder (setActor w id { (w.st id) with parked := ps }) p.msg.sender) i
    have hi := ih (creditLive (setActor w id { (w.st id) with parked := ps }) dst p.msg.sender)
    exact ⟨hi.1.trans (hc.1.trans hset.1), hi.2.trans (hc.2.trans hset.2)⟩

theorem actor_kept_clearP (w : World) (id : InstId) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundClearPark w id dst ps).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((refundClearPark w id dst ps).st i).parent = (w.st i).parent := by
  have hR := actor_kept_refundP w dst ps i
  by_cases hi : i = id
  · subst hi
    simp [refundClearPark, setActor]
    exact hR
  · simp [refundClearPark, setActor, hi]
    exact hR

/-- Refunding every parked message and then clearing that lane is the same world
as dropping each entry and crediting the live holder of its key. -/
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
    · exact (actor_kept_drainP w id dst ps i).1.trans (actor_kept_clearP w id dst ps i).1.symm
    · exact (actor_kept_drainP w id dst ps i).2.trans (actor_kept_clearP w id dst ps i).2.symm
  have hM := meta_drainP w id dst ps
  have hMc := meta_clearP w id dst ps
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm)
    ((kept_drainP w id dst ps).1.trans (kept_clearP w id dst ps).1.symm) hst
    (hD.2.2.2.1.trans hC.2.2.2.1.symm) (hD.2.2.2.2.trans hC.2.2.2.2.symm)
    (hM.trans hMc.symm) ((kept_drainP w id dst ps).2.trans (kept_clearP w id dst ps).2.symm)

theorem occ_drop_park (I : Impl) (w : World) (id : InstId) (p : Parked) (ps : List Parked)
    (hO : OccInv I w) (hmem : id ∈ w.roster) (hpark : (w.st id).parked = p :: ps)
    (hmsg : p.sender = p.msg.sender) (hcr : w.crashed = false) :
    OccInv I (creditLive (setActor w id { (w.st id) with parked := ps }) (tname id) p.msg.sender) := by
  have hsend : p.msg.sender ∈ w.roster := by
    rw [← hmsg]
    exact hO.parkFrom id p (by rw [hpark]; exact List.Mem.head _)
  let a1 : Actor := { (w.st id) with parked := ps }
  apply occ_consume I w w id p.msg.sender a1 hO (fun _ => rfl) rfl rfl (fun _ => rfl) rfl
    (by simp [a1]) (fun _ => rfl) hmem hsend
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
  · intro name key d
    have hdelta :
        ((w.st id).box.filter (keyPred name key)).length +
          ((w.st id).parked.filter fun q => keyPred name key q.msg).length =
        (a1.box.filter (keyPred name key)).length +
          (a1.parked.filter fun q => keyPred name key q.msg).length +
          (if keyPred name key p.msg = true then 1 else 0) := by
      simp [a1, hpark, List.filter]
      cases hk : keyPred name key p.msg <;> simp [hk] <;> omega
    have hrep := queuedFromKey_replace w id a1 name key d
      (if keyPred name key p.msg = true then 1 else 0) hO.nodup hmem hdelta
    rw [hrep, Int.natCast_add, cast_keybit (tname id) d (keyPred name key p.msg),
      queueDrop_msg p.msg.sender p.msg name key d (tname id) rfl]
    omega
  · intro d
    have hsame : tokenHold I.desc (tname id) d a1 = tokenHold I.desc (tname id) d (w.st id) := by
      simp [a1, tokenHold]
    exact Nat.le_of_eq hsame
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
  · intro m hm
    exact (hO.sameKey id).1 m (by simpa [a1] using hm)
  · intro q hq
    exact (hO.sameKey id).2 q (by
      have hq0 : q ∈ ps := by simpa [a1] using hq
      rw [hpark]
      exact List.mem_cons.mpr (Or.inr hq0))
  · intro hdead
    simp [a1] at hdead
    have hlife : (w.st id).life = .absent ∨ (w.st id).life = .dead := by
      cases h : (w.st id).life
      · exact Or.inl rfl
      · exact absurd h hdead
      · exact Or.inr rfl
    have hempty := (hO.deadEmpty hcr id hlife).2
    rw [hpark] at hempty
    simp at hempty
  · intro hk m hm
    exact (hO.coreFrom id hk).1 m (by simpa [a1] using hm)
  · intro hk q hq
    have hq0 : q ∈ ps := by simpa [a1] using hq
    exact (hO.coreFrom id hk).2 q (by rw [hpark]; exact List.mem_cons.mpr (Or.inr hq0))

theorem occ_drain_park (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hO : OccInv I w)
    (hmem : id ∈ w.roster) (hpark : (w.st id).parked = ps)
    (hmsg : ∀ p ∈ ps, p.sender = p.msg.sender) (hcr : w.crashed = false) :
    OccInv I (drainPark w id (tname id) ps) := by
  induction ps generalizing w with
  | nil =>
    have hempty : (w.st id).parked = [] := hpark
    apply occ_keep I w id ({ (w.st id) with parked := [] }) hO rfl rfl (by simp [hempty])
      (fun _ => rfl)
    intro _ _
    simp [tokenHold]
  | cons p ps ih =>
    have hstep := occ_drop_park I w id p ps hO hmem hpark (hmsg p (List.Mem.head _)) hcr
    let w1 := creditLive (setActor w id { (w.st id) with parked := ps }) (tname id) p.msg.sender
    have hpark1 : (w1.st id).parked = ps := by
      simp [w1, creditLive, credit_park, setActor]
    have hmem1 : id ∈ w1.roster := by simpa [w1, creditLive, creditSender, setActor] using hmem
    have hmsg1 : ∀ q ∈ ps, q.sender = q.msg.sender := fun q hq => hmsg q (List.Mem.tail _ hq)
    have hcr1 : w1.crashed = w.crashed := by simp [w1, creditLive, creditSender, setActor]
    simpa [drainPark, w1] using ih w1 hstep hmem1 hpark1 hmsg1 (hcr1.trans hcr)

/-- `find?` after one element stops matching. A hit on `dead` becomes a miss,
and every other hit is unchanged. -/
theorem find_mark {α : Type} [DecidableEq α] (p q : α → Bool) (l : List α) (dead : α)
    (hq : ∀ x, x ≠ dead → q x = p x) (hdead : q dead = false)
    (hunique : p dead = true → ∀ x, x ∈ l → p x = true → x = dead) :
    l.find? q =
      match l.find? p with
      | some live => if live = dead then none else some live
      | none => none := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    have ih := ih (fun hp x hxmem hpx => hunique hp x (List.Mem.tail _ hxmem) hpx)
    rw [List.find?_cons, List.find?_cons]
    by_cases hx : head = dead
    · have hqh : q head = false := by rw [hx]; exact hdead
      simp only [hqh, ite_false]
      by_cases hp : p head = true
      · simp only [hp, ite_true, if_pos hx]
        rw [List.find?_eq_none]
        intro y hy hqy
        have hne : y ≠ dead := by
          intro heq
          have hqdead : q y = false := by rw [heq]; exact hdead
          simp [hqdead] at hqy
        have hpy : p y = true := by rw [← hq y hne]; exact hqy
        exact hne (hunique (by rw [← hx]; exact hp) y (List.Mem.tail _ hy) hpy)
      · have hpf : p head = false := by
          cases hb : p head with
          | false => rfl
          | true => exact absurd hb hp
        simp only [hpf, ite_false]
        exact ih
    · have hqh : q head = p head := hq head hx
      simp only [hqh]
      by_cases hph : p head = true
      · simp only [hph, ite_true, if_neg hx]
      · have hpf : p head = false := by
          cases hb : p head with
          | false => rfl
          | true => exact absurd hb hph
        simp only [hpf, ite_false]
        exact ih

/-- Killing `id` removes it from `findLive` and leaves every other holder. -/
theorem findLive_mark_dead (w : World) (id : InstId) (h1 : oneLiveGen w) (hmem : id ∈ w.roster)
    (name : String) (key : Nat) :
    findLive
        (setActor w id
          { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] })
        name key =
      match findLive w name key with
      | some live => if live = id then none else some live
      | none => none := by
  let dead : Actor :=
    { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  let w' := setActor w id dead
  let p : InstId → Bool := fun i =>
    match i with
    | .peer n k _ => n == name && k == key && (w.st i).life == .alive
    | .core _ => false
  let q : InstId → Bool := fun i =>
    match i with
    | .peer n k _ => n == name && k == key && (w'.st i).life == .alive
    | .core _ => false
  have hq : ∀ x, x ≠ id → q x = p x := by
    intro x hx
    cases x with
    | core _ => simp [p, q]
    | peer _ _ _ => simp [p, q, w', setActor, hx]
  have hdead : q id = false := by
    cases id with
    | core _ => simp [q]
    | peer _ _ _ => simp [q, w', setActor, dead]
  have hunique : p id = true → ∀ x, x ∈ w.roster → p x = true → x = id := by
    intro hp x hxmem hpx
    cases id with
    | core _ => simp [p] at hp
    | peer n k g =>
      simp only [p, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨hn, hk⟩, hl⟩ := hp
      cases x with
      | core _ => simp [p] at hpx
      | peer n' k' g' =>
        simp only [p, Bool.and_eq_true, beq_iff_eq] at hpx
        obtain ⟨⟨hn', hk'⟩, hl'⟩ := hpx
        have hl1 : (w.st (InstId.peer name key g')).life = .alive := by
          simpa [hn', hk'] using hl'
        have hl0 : (w.st (InstId.peer name key g)).life = .alive := by
          simpa [hn, hk] using hl
        have hg : g' = g :=
          h1 name key g' g
            (by simpa [hn', hk', hn, hk] using hxmem)
            (by simpa [hn, hk] using hmem)
            hl1 hl0
        simp [hn, hk, hn', hk', hg]
  have hmark := find_mark p q w.roster id hq hdead hunique
  have hrp : findLive w name key = w.roster.find? p := by
    unfold findLive p
    rfl
  have hrq : findLive w' name key = w.roster.find? q := by
    have hrost : w'.roster = w.roster := by simp [w', setActor]
    unfold findLive
    rw [hrost]
    rfl
  have hww :
      setActor w id { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] } = w' :=
    rfl
  rw [hww]
  cases hfl : findLive w name key with
  | none =>
    rw [← hrp] at hmark
    simp only [hfl] at hmark
    rw [hrq]
    simp only [hfl]
    exact hmark
  | some live =>
    by_cases heq : live = id
    · rw [← hrp] at hmark
      simp only [hfl, heq] at hmark
      rw [hrq]
      simp only [hfl, heq]
      exact hmark
    · rw [← hrp] at hmark
      simp only [hfl] at hmark
      rw [if_neg heq] at hmark
      rw [hrq]
      simp only [hfl]
      rw [if_neg heq]
      exact hmark

/-- An actor owes at most its budget. A live core or peer spends the slot
equation and the fact that tokens are nonnegative. A non-alive actor, while
the world has not crashed, is bounded by `quiet`. -/
theorem owed_within (I : Impl) (w : World) (h : OccInv I w) (s : InstId) (hs : s ∈ w.roster)
    (hcr : w.crashed = false) (d : String) :
    owed w.st d s w.roster ≤ budget I.desc (tname s) d := by
  by_cases hl : (w.st s).life = .alive
  · cases s with
    | core name =>
      have hbal := h.balance.1.2 name d hl hs
      have hnn : (0 : Int) ≤ (w.st (InstId.core name)).tokens d :=
        Int.le_trans (Int.natCast_nonneg _) (h.slack (InstId.core name) d hl)
      have hle : (owed w.st d (InstId.core name) w.roster : Int) ≤ (budget I.desc name d : Int) := by
        omega
      exact Int.ofNat_le.mp hle
    | peer name key gen =>
      have hlive := findLive_of_alive w h.indexed name key gen hs hl
      have hbal := h.balance.1.1 name key (InstId.peer name key gen) d hlive
      have howed := owed_peer_le_queued w name key gen d h.parkMsg
      have hnn : (0 : Int) ≤ (w.st (InstId.peer name key gen)).tokens d :=
        Int.le_trans (Int.natCast_nonneg _) (h.slack (InstId.peer name key gen) d hl)
      have hle : (queuedFromKey w name key d : Int) ≤ (budget I.desc name d : Int) := by
        omega
      exact Nat.le_trans howed (Int.ofNat_le.mp hle)
  · exact Int.ofNat_le.mp (h.quiet hcr s d hs hl)

/-- The mailbox is already empty. Marking `id` dead removes that generation
from the live account. If it held the key, nonnegative tokens turn the slot
equation into the queued inequality. -/
theorem occ_die (I : Impl) (w : World) (id : InstId) (hO : OccInv I w) (hmem : id ∈ w.roster)
    (hbox : (w.st id).box = []) (hpark : (w.st id).parked = [])
    (hquiet : ∀ d, owed w.st d id w.roster ≤ budget I.desc (tname id) d) :
    OccInv I (setActor w id { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }) := by
  let dead : Actor := { (w.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  let w' := setActor w id dead
  suffices OccInv I w' by simpa [w', dead] using this
  have hr : w'.roster = w.roster := by simp [w', setActor]
  have hst : ∀ i, w'.st i = if i = id then dead else w.st i := by
    intro i
    by_cases hi : i = id <;> simp [w', setActor, hi]
  have hboxeq : ∀ i, (w'.st i).box = (w.st i).box := by
    intro i
    by_cases hi : i = id <;> simp [w', setActor, hi, dead, hbox]
  have hparkeq : ∀ i, (w'.st i).parked = (w.st i).parked := by
    intro i
    by_cases hi : i = id <;> simp [w', setActor, hi, dead, hpark]
  have howed : ∀ d s, owed w'.st d s w.roster = owed w.st d s w.roster := by
    intro d s
    refine owed_mail_eq _ _ _ _ w.roster ?_
    intro i _
    exact ⟨hboxeq i, hparkeq i⟩
  have hcrw : w'.crashed = w.crashed := by simp [w', setActor]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hO.nodup
  · intro i hl
    rw [hst i] at hl
    by_cases hi : i = id
    · simp [hi, dead] at hl
    · simp [hi] at hl
      exact hO.aliveIn i hl
  · intro name key g1 g2 h1 h2 hl1 hl2
    rw [hr] at h1 h2
    have hne1 : InstId.peer name key g1 ≠ id := by
      intro heq
      rw [heq] at hl1
      simp [w', setActor, dead] at hl1
    have hne2 : InstId.peer name key g2 ≠ id := by
      intro heq
      rw [heq] at hl2
      simp [w', setActor, dead] at hl2
    have hl1' : (w.st (InstId.peer name key g1)).life = .alive := by
      simp [w', setActor, hne1] at hl1
      exact hl1
    have hl2' : (w.st (InstId.peer name key g2)).life = .alive := by
      simp [w', setActor, hne2] at hl2
      exact hl2
    exact hO.indexed name key g1 g2 h1 h2 hl1' hl2'
  · intro template ht
    have hc : aliveCount w' template ≤ aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_le _ _ w.roster ?_
      intro i _
      by_cases hi : i = id
      · simp [aliveBit, hst, hi, dead]
      · simp [aliveBit, hst, hi]
    exact Nat.le_trans hc (hO.liveOne template ht)
  · intro template ht
    have hc : aliveCount w' template ≤ aliveCount w template := by
      rw [aliveCount_sum, aliveCount_sum, hr]
      refine sum_le _ _ w.roster ?_
      intro i _
      by_cases hi : i = id
      · simp [aliveBit, hst, hi, dead]
      · simp [aliveBit, hst, hi]
    exact Nat.le_trans hc (hO.livePeer template ht)
  · intro i hnin
    have hne : i ≠ id := by
      intro heq
      subst heq
      exact hnin (by simpa [hr] using hmem)
    rw [hst i, if_neg hne]
    exact hO.offEmpty i (by rw [hr] at hnin; exact hnin)
  · intro i m hm
    rw [hboxeq i] at hm
    rw [hr]
    exact hO.sentFrom i m hm
  · intro i p hp
    rw [hparkeq i] at hp
    rw [hr]
    exact hO.parkFrom i p hp
  · intro i p hp
    rw [hparkeq i] at hp
    exact hO.parkMsg i p hp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro name key live d hfind
      have hm := findLive_mark_dead w id hO.indexed hmem name key
      simp [w', dead] at hm
      rw [hm] at hfind
      cases hfl : findLive w name key with
      | none => simp [hfl] at hfind
      | some old =>
        by_cases heq : old = id
        · simp [hfl, heq] at hfind
        · simp [hfl, heq] at hfind
          cases hfind
          have htok : (w'.st live).tokens d = (w.st live).tokens d := by
            rw [hst live]
            simp [heq]
          have hqeq := queuedFromKey_agree w w' hr hboxeq hparkeq name key d
          rw [htok, hqeq]
          exact hO.balance.1.1 name key live d hfl
    · intro name d hl hmemc
      by_cases hid : InstId.core name = id
      · rw [hid] at hl
        rw [hst id, if_pos rfl] at hl
        simp [dead] at hl
      · have hst' : w'.st (InstId.core name) = w.st (InstId.core name) := by
          rw [hst (InstId.core name)]
          simp [hid]
        rw [hr] at hmemc ⊢
        rw [hst'] at hl ⊢
        rw [howed d (InstId.core name)]
        exact hO.balance.1.2 name d hl hmemc
    · intro name key d hnone
      have hm := findLive_mark_dead w id hO.indexed hmem name key
      simp [w', dead] at hm
      rw [hm] at hnone
      cases hfl : findLive w name key with
      | none =>
        simp [hfl] at hnone
        have hq := queuedFromKey_agree w w' hr hboxeq hparkeq name key d
        rw [hq]
        exact hO.balance.2 name key d hfl
      | some live =>
        by_cases heq : live = id
        · simp [hfl, heq] at hnone
          have hbal := hO.balance.1.1 name key live d hfl
          have hl := findLive_alive w name key live hfl
          have hnn : (0 : Int) ≤ (w.st live).tokens d :=
            Int.le_trans (Int.natCast_nonneg _) (hO.slack live d hl)
          have hq := queuedFromKey_agree w w' hr hboxeq hparkeq name key d
          rw [hq]
          omega
        · simp [hfl, heq] at hnone
  · intro s d hl
    rw [hst s] at hl
    by_cases hss : s = id
    · simp [hss, dead] at hl
    · have hst' : w'.st s = w.st s := by
        rw [hst s]
        simp [hss]
      simp [hss] at hl
      rw [hst']
      exact hO.slack s d hl
  · intro s d hs hterm
    rw [hr] at hs ⊢
    rw [howed]
    exact hO.still s d hs hterm
  · intro hcrash s d hs hdead
    rw [hcrw] at hcrash
    rw [hr] at hs ⊢
    rw [howed]
    by_cases hss : s = id
    · rw [hss]
      exact Int.ofNat_le.mpr (hquiet d)
    · have hdead0 : (w.st s).life ≠ .alive := by
        rw [hst s] at hdead
        simp [hss] at hdead
        exact hdead
      exact hO.quiet hcrash s d hs hdead0
  · intro hcrash i hlife
    rw [hcrw] at hcrash
    rw [hst i] at hlife ⊢
    by_cases hi : i = id
    · simp [hi, dead]
    · simp [hi] at hlife ⊢
      exact hO.deadEmpty hcrash i hlife
  · intro host
    refine ⟨fun m hm => ?_, fun p hp => ?_⟩
    · rw [hboxeq host] at hm
      exact (hO.sameKey host).1 m hm
    · rw [hparkeq host] at hp
      exact (hO.sameKey host).2 p hp
  · intro i hi
    exact hO.shaped i (by rw [hr] at hi; exact hi)
  · intro host hk
    refine ⟨fun m hm => ?_, fun p hp => ?_⟩
    · rw [hboxeq host] at hm
      exact (hO.coreFrom host hk).1 m hm
    · rw [hparkeq host] at hp
      exact (hO.coreFrom host hk).2 p hp
  · exact ixFresh_copy I.desc w w' hO.ixFresh hr (fun _ => by simp [w', setActor])


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
          (by intro _ hcall; cases hcall)
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
    refund_tok w name ms i d,
    livePark_drain w id name i ms ps,
    livePark_refund w name i ms ps]

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
        refine ⟨?_, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_, ?_⟩
        · exact (drainP_mid (drainBox w id name ms) id name ps id).trans
            ((drain_mid w id name ms id).trans
              ((refund_mid w name ms id).symm.trans
                (refundP_mid (refundMsgs w name ms) name ps id).symm))
        · exact (actor_kept_drainP (drainBox w id name ms) id name ps id).1.trans
            ((actor_kept_drain w id name ms id).1.trans
              ((actor_kept_refund w name ms id).1.symm.trans
                (actor_kept_refundP (refundMsgs w name ms) name ps id).1.symm))
        · exact (actor_kept_drainP (drainBox w id name ms) id name ps id).2.trans
            ((actor_kept_drain w id name ms id).2.trans
              ((actor_kept_refund w name ms id).2.symm.trans
                (actor_kept_refundP (refundMsgs w name ms) name ps id).2.symm))
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
    · have h1 := (actor_kept_drainP (drainBox w id name ms) id name ps i).1
      have h2 := (actor_kept_drain w id name ms i).1
      have h3 := (actor_kept_refund w name ms i).1
      have h4 := (actor_kept_refundP (refundMsgs w name ms) name ps i).1
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))
    · have h1 := (actor_kept_drainP (drainBox w id name ms) id name ps i).2
      have h2 := (actor_kept_drain w id name ms i).2
      have h3 := (actor_kept_refund w name ms i).2
      have h4 := (actor_kept_refundP (refundMsgs w name ms) name ps i).2
      exact h1.trans (h2.trans (h3.symm.trans h4.symm))

theorem occ_term_kill (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hcont : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (_hterm : terminableB I.desc (tname id) = true)
    (hmsg : ∀ p ∈ (w.st id).parked, p.sender = p.msg.sender)
    (hcr : w.crashed = false) :
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
  have hOb := occ_drain_box I w id ms hO hmem rfl hcr
  have hparkB : ((drainBox w id name ms).st id).parked = ps := by
    have hp := drain_park w id name ms id
    simp [name, ps] at hp
    exact hp
  have hmemB : id ∈ (drainBox w id name ms).roster := by
    simpa [(frame_drain w id name ms).2.1] using hmem
  have hcrB : (drainBox w id name ms).crashed = false := (kept_drain w id name ms).2.trans hcr
  have hOp := occ_drain_park I (drainBox w id name ms) id ps hOb hmemB hparkB hmsg hcrB
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
  have hcrD : drained.crashed = false :=
    ((kept_drainP (drainBox w id name ms) id name ps).2.trans hcrB)
  have hbound : ∀ d, owed drained.st d id drained.roster ≤ budget I.desc (tname id) d :=
    fun d => owed_within I drained hOp id hmemD hcrD d
  have hOd := occ_die I drained id hOp hmemD hboxD hparkD hbound
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
    · simp [died, killed, setActor, drained, (kept_drainP (drainBox w id name ms) id name ps).1,
        (kept_drain w id name ms).1, (kept_refundP (refundMsgs w name ms) name ps).1,
        (kept_refund w name ms).1]
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
    · simp [died, killed, setActor, drained, (kept_drainP (drainBox w id name ms) id name ps).2,
        (kept_drain w id name ms).2, (kept_refundP (refundMsgs w name ms) name ps).2,
        (kept_refund w name ms).2]
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

theorem failWaiter_findLive (w : World) (dead i : InstId) (name : String) (key : Nat) :
    findLive (failWaiter w dead i) name key = findLive w name key := by
  cases hlive : (w.st i).life with
  | absent => simp [failWaiter, hlive]
  | dead => simp [failWaiter, hlive]
  | alive =>
    cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [failWaiter, hlive, hph, hd]
          exact findLive_set_life w i (proceed (w.st i) k) (proceed_life _ _) name key
        · simp [failWaiter, hlive, hph, hd]
      | true => simp [failWaiter, hlive, hph]
    | awaitReply _ _ => simp [failWaiter, hlive, hph]
    | idle => simp [failWaiter, hlive, hph]
    | run _ => simp [failWaiter, hlive, hph]
    | awaitEffect _ => simp [failWaiter, hlive, hph]
    | awaitPeer _ => simp [failWaiter, hlive, hph]
    | crashed => simp [failWaiter, hlive, hph]

theorem failWaiter_holder (w : World) (dead i sender : InstId) :
    budgetHolder (failWaiter w dead i) sender = budgetHolder w sender := by
  cases sender with
  | core _ => rfl
  | peer name key _ => simp only [budgetHolder, failWaiter_findLive]

theorem failFold_holder (w : World) (dead : InstId) (ids : List InstId) (sender : InstId) :
    budgetHolder (ids.foldl (fun w i => failWaiter w dead i) w) sender = budgetHolder w sender := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.foldl_cons]
    rw [ih (failWaiter w dead i), failWaiter_holder]

/-- Failing waiters does not move a live generation, so a refund still lands
on the holder it would have reached before the failures. -/
theorem failFold_live (w : World) (dead : InstId) (ids : List InstId) (name : String) (s : InstId) :
    ids.foldl (fun w i => failWaiter w dead i) (creditLive w name s) =
      creditLive (ids.foldl (fun w i => failWaiter w dead i) w) name s := by
  unfold creditLive
  rw [failFold_credit]
  rw [← failFold_holder w dead ids s]

theorem failFold_refundMsgs (w : World) (dead : InstId) (ids : List InstId) (name : String)
    (ms : List Msg) :
    ids.foldl (fun w i => failWaiter w dead i) (refundMsgs w name ms) =
      refundMsgs (ids.foldl (fun w i => failWaiter w dead i) w) name ms := by
  induction ms generalizing w with
  | nil => simp [refundMsgs]
  | cons m ms ih =>
    have hfold : refundMsgs w name (m :: ms) = refundMsgs (creditLive w name m.sender) name ms := by
      simp [refundMsgs, List.foldl_cons]
    rw [hfold, ih, failFold_live]
    simp [refundMsgs, List.foldl_cons]

theorem failFold_refundParked (w : World) (dead : InstId) (ids : List InstId) (name : String)
    (ps : List Parked) :
    ids.foldl (fun w i => failWaiter w dead i) (refundParked w name ps) =
      refundParked (ids.foldl (fun w i => failWaiter w dead i) w) name ps := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    have hfold : refundParked w name (p :: ps) =
        refundParked (creditLive w name p.msg.sender) name ps := by
      simp [refundParked, List.foldl_cons]
    rw [hfold, ih, failFold_live]
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
            (by
              intro d _
              cases hk : k.rest with
              | nil => simp [tokenHold, proceed, hk, hph, pathReserve, contAt, landFloor]
              | cons _ _ => simp [tokenHold, proceed, hk, hph])
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
  unfold releaseWorld
  rw [releaseParked_roster]
  simp only [setActor]
  rw [(releaseOutbound_fields _ _ id).1, refundParked_roster, refundMsgs_roster, cellsRoster]


/-- One host in `releaseOutbound`. Parked mail from `dead` is dropped and the
same number of slots is returned to `dead`, which is still the live holder. -/
def dropOutbound (w : World) (dead host : InstId) : World :=
  if host == dead then w
  else
    let dropped := (w.st host).parked.filter fun p => p.sender == dead
    if dropped.isEmpty then w
    else
      let cleared := setActor w host
        { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != dead }
      setActor cleared dead (addTokens (cleared.st dead) (tname host) dropped.length)

theorem releaseOutbound_fold (w : World) (dead : InstId) :
    releaseOutbound w dead = w.roster.foldl (fun acc host => dropOutbound acc dead host) w := by
  unfold releaseOutbound dropOutbound
  rfl

theorem tokenHold_phase (D : Description) (template dst : String) (a b : Actor)
    (hp : a.phase = b.phase) (ht : a.typestate = b.typestate) :
    tokenHold D template dst a = tokenHold D template dst b := by
  cases h : a.phase <;> simp [tokenHold, h, show b.phase = a.phase from hp.symm, ht]

theorem filter_count_split (mark keep : Parked → Bool) (l : List Parked) :
    (l.filter keep).length =
      ((l.filter fun p => !mark p).filter keep).length + ((l.filter mark).filter keep).length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    cases hm : mark p <;> cases hk : keep p <;>
      simp [hm, hk, ih, Bool.not_eq_true', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem dropped_all_key (dead : InstId) (ps : List Parked) (name : String) (key g : Nat)
    (hmsg : ∀ p ∈ ps, p.sender = p.msg.sender) (hdead : dead = InstId.peer name key g) :
    ((ps.filter fun p => p.sender == dead).filter fun p => keyPred name key p.msg).length =
      (ps.filter fun p => p.sender == dead).length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hmsgp : p.sender = p.msg.sender := hmsg p (by simp)
    have hmsgt : ∀ q ∈ ps, q.sender = q.msg.sender := fun q hq => hmsg q (by simp [hq])
    have ih' := ih hmsgt
    simp only [List.filter_filter] at ih'
    cases hm : (p.sender == dead)
    · simp only [List.filter_filter] at *
      simpa [hm] using ih'
    · have hs : p.sender = dead := by simpa [beq_iff_eq] using hm
      have hk : keyPred name key p.msg = true := by
        simp only [keyPred]
        rw [← hmsgp, hs, hdead]
        simp
      simp only [List.filter_filter] at *
      simpa [hm, hk] using ih'

theorem dropped_miss (dead : InstId) (ps : List Parked) (name : String) (key : Nat)
    (hmsg : ∀ p ∈ ps, p.sender = p.msg.sender) (hnot : ∀ g, dead ≠ InstId.peer name key g) :
    ((ps.filter fun p => p.sender == dead).filter fun p => keyPred name key p.msg).length = 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hmsgp : p.sender = p.msg.sender := hmsg p (by simp)
    have hmsgt : ∀ q ∈ ps, q.sender = q.msg.sender := fun q hq => hmsg q (by simp [hq])
    have ih' := ih hmsgt
    simp only [List.filter_filter] at ih'
    cases hm : (p.sender == dead)
    · simp only [List.filter_filter] at *
      simpa [hm] using ih'
    · have hs : p.sender = dead := by simpa [beq_iff_eq] using hm
      have hk : keyPred name key p.msg = false := by
        simp only [keyPred]
        rw [← hmsgp, hs]
        cases dead with
        | core _ => rfl
        | peer n k g =>
          by_cases hn : n = name <;> by_cases hk' : k = key <;> simp [hn, hk', beq_iff_eq]
          · have hbad := hnot g
            rw [hn, hk'] at hbad
            exact hbad rfl
      simp only [List.filter_filter] at *
      simpa [hm, hk] using ih'

theorem filter_count_split_msg (mark keep : Msg → Bool) (l : List Msg) :
    (l.filter keep).length =
      ((l.filter fun m => !mark m).filter keep).length +
        ((l.filter mark).filter keep).length := by
  induction l with
  | nil => simp
  | cons m l ih =>
    cases hm : mark m <;> cases hk : keep m <;>
      simp [hm, hk, ih, Bool.not_eq_true', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem box_all_key (dead : InstId) (ms : List Msg) (name : String) (key g : Nat)
    (hdead : dead = InstId.peer name key g) :
    ((ms.filter fun m => m.sender == dead).filter (keyPred name key)).length =
      (ms.filter fun m => m.sender == dead).length := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.filter_filter] at *
    cases hm : (m.sender == dead)
    · simpa [hm] using ih
    · have hs : m.sender = dead := by simpa [beq_iff_eq] using hm
      have hk : keyPred name key m = true := by
        simp only [keyPred]
        rw [hs, hdead]
        simp
      simpa [hm, hk] using ih

theorem box_miss (dead : InstId) (ms : List Msg) (name : String) (key : Nat)
    (hnot : ∀ g, dead ≠ InstId.peer name key g) :
    ((ms.filter fun m => m.sender == dead).filter (keyPred name key)).length = 0 := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.filter_filter] at *
    cases hm : (m.sender == dead)
    · simpa [hm] using ih
    · have hs : m.sender = dead := by simpa [beq_iff_eq] using hm
      have hk : keyPred name key m = false := by
        simp only [keyPred]
        rw [hs]
        cases dead with
        | core _ => rfl
        | peer n k g =>
          by_cases hn : n = name <;> by_cases hk' : k = key <;> simp [hn, hk', beq_iff_eq]
          · have hbad := hnot g
            rw [hn, hk'] at hbad
            exact hbad rfl
      simpa [hm, hk] using ih

theorem occ_dropHost (I : Impl) (w : World) (dead host : InstId) (hO : OccInv I w)
    (hdead : dead ∈ w.roster) (hhost : host ∈ w.roster) (hlive : (w.st dead).life = .alive) :
    OccInv I (dropOutbound w dead host) := by
  unfold dropOutbound
  split
  · exact hO
  · dsimp only
    split
    · exact hO
    · let dropped := (w.st host).parked.filter fun p => p.sender == dead
      let stripped := { (w.st host) with
        parked := (w.st host).parked.filter fun p => p.sender != dead }
      let w1 := setActor w host stripped
      let n := dropped.length
      let bumped := addTokens (w1.st dead) (tname host) n
      let w2 := setActor w1 dead bumped
      have hself : host ≠ dead := by
        intro h
        simp [h] at *
      have hswap : dead ≠ host := fun h => hself h.symm
      have hmid : w1.st dead = w.st dead := by
        simpa [w1] using setActor_other w host dead stripped hswap
      have hr : w2.roster = w.roster := by simp [w2, w1, setActor]
      have hN : w2.N = w.N := by simp [w2, w1, setActor]
      have hix : ∀ name, w2.nextIx name = w.nextIx name := by intro _; simp [w2, w1, setActor]
      have hlife : ∀ i, (w2.st i).life = (w.st i).life := by
        intro i
        by_cases hid : i = dead
        · simp [w2, hid, setActor, bumped, addTokens, hmid]
        · by_cases hih : i = host
          · simp [w2, w1, hid, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have hph : ∀ i, (w2.st i).phase = (w.st i).phase := by
        intro i
        by_cases hid : i = dead
        · simp [w2, hid, setActor, bumped, addTokens, hmid]
        · by_cases hih : i = host
          · simp [w2, w1, hid, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have hty : ∀ i, (w2.st i).typestate = (w.st i).typestate := by
        intro i
        by_cases hid : i = dead
        · simp [w2, hid, setActor, bumped, addTokens, hmid]
        · by_cases hih : i = host
          · simp [w2, w1, hid, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have hbox : ∀ i, (w2.st i).box = (w.st i).box := by
        intro i
        by_cases hid : i = dead
        · simp [w2, hid, setActor, bumped, addTokens, hmid]
        · by_cases hih : i = host
          · simp [w2, w1, hid, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have hpark : ∀ i, (w2.st i).parked =
          if i = host then (w.st host).parked.filter fun p => p.sender != dead else (w.st i).parked := by
        intro i
        by_cases hid : i = dead
        · have hnot : ¬ i = host := by rw [hid]; exact hswap
          simp [w2, hid, hnot, setActor, bumped, addTokens, hmid, if_neg hswap]
        · by_cases hih : i = host
          · simp [w2, w1, hid, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have htok (i : InstId) (d : String) : (w2.st i).tokens d =
          (w.st i).tokens d + if i = dead ∧ d = tname host then n else 0 := by
        by_cases hid : i = dead
        · rw [hid]
          simp [w2, setActor, bumped, addTokens, hmid]
          by_cases hd : d = tname host
          · simp [hd]
          · have hb : (d == tname host) = false := by simpa [beq_iff_eq] using hd
            simp [hd, hb]
        · simp [hid]
          by_cases hih : i = host
          · simp [w2, w1, hih, setActor, stripped, hself]
          · simp [w2, w1, hid, hih, setActor]
      have howed_le : ∀ dst sender, owed w2.st dst sender w.roster ≤ owed w.st dst sender w.roster := by
        intro dst sender
        let st1 := fun i => if i = host then stripped else w.st i
        have hmail : ∀ i, (w2.st i).box = (st1 i).box ∧ (w2.st i).parked = (st1 i).parked := by
          intro i
          constructor
          · by_cases hih : i = host
            · simp [hbox, st1, hih, stripped]
            · simp [hbox, st1, hih]
          · by_cases hih : i = host
            · simp [hpark, st1, hih, stripped]
            · simp [hpark, st1, hih]
        have hsames : owed w2.st dst sender w.roster = owed st1 dst sender w.roster := by
          refine owed_mail_eq _ _ _ _ w.roster ?_
          intro i _
          exact hmail i
        have hrep := owed_replace w.st dst sender host stripped w.roster hO.nodup hhost
        have hslot : slot st1 dst sender host ≤ slot w.st dst sender host := by
          simp only [slot, st1]
          by_cases ht : (tname host == dst) = true
          · simp [ht, stripped]
            have hparkLe : countParked sender ((w.st host).parked.filter fun p => p.sender != dead) ≤
                countParked sender (w.st host).parked := by
              by_cases hs : sender = dead
              · rw [hs, countParked_filter_self]
                exact Nat.zero_le _
              · rw [countParked_filter_other sender dead hs]
                exact Nat.le_refl _
            omega
          · simp [ht]
        rw [hsames]
        have hrep' : owed st1 dst sender w.roster + slot w.st dst sender host =
            owed w.st dst sender w.roster + slot st1 dst sender host := by
          simpa [st1] using hrep
        omega
      suffices hdone : OccInv I w2 by
        simpa [w2, w1, bumped, n, stripped] using hdone
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hr] using hO.nodup
      · intro i hl
        exact hO.aliveIn i (by rw [← hlife i]; exact hl) |> fun h => by simpa [hr] using h
      · intro name key g1 g2 ha hb hla hlb
        apply hO.indexed name key g1 g2 (by simpa [hr] using ha) (by simpa [hr] using hb)
        · simpa [hlife] using hla
        · simpa [hlife] using hlb
      · intro template ht
        have hc : aliveCount w2 template = aliveCount w template := by
          rw [aliveCount_sum, aliveCount_sum, hr]
          refine sum_congr _ _ w.roster ?_
          intro i _
          simp [aliveBit, hlife i]
        simpa [hc] using hO.liveOne template ht
      · intro template ht
        have hc : aliveCount w2 template = aliveCount w template := by
          rw [aliveCount_sum, aliveCount_sum, hr]
          refine sum_congr _ _ w.roster ?_
          intro i _
          simp [aliveBit, hlife i]
        simpa [hc, hN] using hO.livePeer template ht
      · intro i hnin
        have hnin0 : i ∉ w.roster := by simpa [hr] using hnin
        have hneD : i ≠ dead := fun h => hnin0 (h ▸ hdead)
        have hneH : i ≠ host := fun h => hnin0 (h ▸ hhost)
        simpa [hbox, hpark, hneH] using hO.offEmpty i hnin0
      · intro i m hm
        rw [hbox i] at hm
        exact hO.sentFrom i m hm |> fun h => by simpa [hr] using h
      · intro i p hp
        rw [hpark i] at hp
        by_cases hih : i = host
        · simp [hih] at hp
          exact hO.parkFrom host p hp.1 |> fun h => by simpa [hr] using h
        · simp [hih] at hp
          exact hO.parkFrom i p hp |> fun h => by simpa [hr] using h
      · intro i p hp
        rw [hpark i] at hp
        by_cases hih : i = host
        · simp [hih] at hp
          exact hO.parkMsg host p hp.1
        · simp [hih] at hp
          exact hO.parkMsg i p hp
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro name key id d hfind
          have hfindEq : findLive w2 name key = findLive w name key := by
            have hs1 : stripped.life = (w.st host).life := by simp [stripped]
            have hs2 : bumped.life = (w1.st dead).life := by simp [bumped, addTokens]
            have h1 := findLive_set_life w host stripped hs1 name key
            have h2 := findLive_set_life w1 dead bumped hs2 name key
            simpa [w2, w1] using h2.trans h1
          have hfind0 : findLive w name key = some id := by rw [hfindEq] at hfind; exact hfind
          have hmsg : ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender :=
            fun p hp => hO.parkMsg host p hp
          have hnotEq : (fun p : Parked => p.sender != dead) = fun p => !(p.sender == dead) := by
            funext p; simp [bne]
          have hsplit := filter_count_split (fun p => p.sender == dead)
            (fun p => keyPred name key p.msg) (w.st host).parked
          have hboxA : stripped.box = (w.st host).box := by simp [stripped]
          have hdelta : ((w.st host).box.filter (keyPred name key)).length +
              ((w.st host).parked.filter fun p => keyPred name key p.msg).length =
              (stripped.box.filter (keyPred name key)).length +
                (stripped.parked.filter fun p => keyPred name key p.msg).length +
                ((dropped.filter fun p => keyPred name key p.msg).length) := by
            simp only [hboxA]
            have hp : stripped.parked =
                (w.st host).parked.filter fun p => !(p.sender == dead) := by
              simp [stripped, hnotEq]
            rw [hp, hsplit, Nat.add_assoc]
          have hq := queuedFromKey_replace w host stripped name key d
            ((dropped.filter fun p => keyPred name key p.msg).length) hO.nodup hhost hdelta
          have hq2 : queuedFromKey w2 name key d = queuedFromKey w1 name key d := by
            refine queuedFromKey_set w1 dead bumped ?_ ?_ name key d
            · simp [bumped, addTokens]
            · simp [bumped, addTokens]
          have hbit : (queuedFromKey w name key d : Int) =
              (queuedFromKey w2 name key d : Int) +
                if tname host = d then
                  ((dropped.filter fun p => keyPred name key p.msg).length : Int) else 0 := by
            have hq' : queuedFromKey w name key d =
                queuedFromKey w1 name key d +
                  if tname host = d then
                    ((dropped.filter fun p => keyPred name key p.msg).length) else 0 := by
              simpa [w1] using hq
            rw [hq2, hq']
            by_cases htd : tname host = d <;> simp [htd, Int.natCast_add]
          have hbal := hO.balance.1.1 name key id d hfind0
          by_cases hwho : id = dead
          · have hpeer : ∃ g, dead = InstId.peer name key g := by
              rw [← hwho]
              exact findLive_peer w name key id hfind0
            obtain ⟨g, hdeadP⟩ := hpeer
            have hall := dropped_all_key dead (w.st host).parked name key g hmsg hdeadP
            have htk := htok id d
            rw [hwho] at htk
            simp only [eq_self_iff_true, true_and] at htk
            have htk' : (w2.st id).tokens d =
                (w.st id).tokens d + (if tname host = d then (n : Int) else 0) := by
              rw [hwho]
              by_cases htd : tname host = d
              · rw [if_pos htd]
                have hflip : d = tname host := htd.symm
                rw [if_pos hflip] at htk
                exact htk
              · rw [if_neg htd]
                have hflip : ¬ d = tname host := fun h => htd h.symm
                rw [if_neg hflip] at htk
                exact htk
            have hall' : ((dropped.filter fun p => keyPred name key p.msg).length) = n := by
              simpa [dropped, n] using hall
            rw [hall'] at hbit
            have hbit' : (queuedFromKey w name key d : Int) =
                (queuedFromKey w2 name key d : Int) + (if tname host = d then (n : Int) else 0) := by
              by_cases htd : tname host = d
              · rw [if_pos htd] at hbit ⊢
                exact hbit
              · rw [if_neg htd] at hbit ⊢
                exact hbit
            rw [htk']
            have hjoin : (w.st id).tokens d + (queuedFromKey w name key d : Int) =
                ((w.st id).tokens d + (if tname host = d then (n : Int) else 0)) +
                  (queuedFromKey w2 name key d : Int) := by
              rw [hbit']
              ac_rfl
            rw [← hjoin, hbal]
          · have hextra : ((dropped.filter fun p => keyPred name key p.msg).length) = 0 := by
              apply dropped_miss dead (w.st host).parked name key hmsg
              intro g hdeadP
              have hliveD : findLive w name key = some dead := by
                simpa [← hdeadP] using
                  findLive_of_alive w hO.indexed name key g
                    (by simpa [hdeadP] using hdead) (by simpa [hdeadP] using hlive)
              have : id = dead := by rw [hfind0] at hliveD; cases hliveD; rfl
              exact hwho this
            have htk := htok id d
            have htk' : (w2.st id).tokens d = (w.st id).tokens d := by
              simpa [hwho] using htk
            rw [hextra] at hbit
            have hbit' : (queuedFromKey w name key d : Int) = queuedFromKey w2 name key d := by
              by_cases htd : tname host = d <;> simp [htd, Int.natCast_zero] at hbit ⊢ <;> exact hbit
            rw [htk', ← hbit', hbal]
        · intro name d hlifeC hmemC
          rw [hr] at hmemC ⊢
          have hlife0 : (w.st (InstId.core name)).life = .alive := by simpa [hlife] using hlifeC
          have hbal := hO.balance.1.2 name d hlife0 hmemC
          by_cases hwho : InstId.core name = dead
          · let st1 := fun i => if i = host then stripped else w.st i
            have hrep := owed_replace w.st d (InstId.core name) host stripped w.roster hO.nodup hhost
            have howed2 : owed w2.st d (InstId.core name) w.roster = owed st1 d (InstId.core name) w.roster := by
              refine owed_mail_eq _ _ _ _ w.roster ?_
              intro i _
              constructor
              · by_cases hih : i = host
                · simp [hbox, st1, hih, stripped]
                · simp [hbox, st1, hih]
              · by_cases hih : i = host
                · simp [hpark, st1, hih, stripped]
                · simp [hpark, st1, hih]
            have hslot : slot w.st d (InstId.core name) host =
                slot st1 d (InstId.core name) host +
                  if tname host = d then n else 0 := by
              simp only [slot, st1]
              by_cases ht : (tname host == d) = true
              · have htP : tname host = d := by simpa [beq_iff_eq] using ht
                simp [ht, stripped, htP, n]
                rw [countParked_len (InstId.core name) (w.st host).parked,
                  hwho, countParked_filter_self]
                simp [dropped]
              · have htP : ¬ tname host = d := by
                  intro heq
                  simp [beq_iff_eq, heq] at ht
                simp [ht, htP]
            have htk := htok (InstId.core name) d
            rw [hwho] at htk
            simp only [eq_self_iff_true, true_and] at htk
            rw [howed2]
            have hrep' : owed st1 d (InstId.core name) w.roster + slot w.st d (InstId.core name) host =
                owed w.st d (InstId.core name) w.roster + slot st1 d (InstId.core name) host := by
              simpa [st1] using hrep
            have htk' : (w2.st (InstId.core name)).tokens d =
                (w.st (InstId.core name)).tokens d + (if tname host = d then (n : Int) else 0) := by
              rw [hwho]
              by_cases htd : tname host = d
              · rw [if_pos htd]
                have hflip : d = tname host := htd.symm
                rw [if_pos hflip] at htk
                exact htk
              · rw [if_neg htd]
                have hflip : ¬ d = tname host := fun h => htd h.symm
                rw [if_neg hflip] at htk
                exact htk
            have howed' : (owed st1 d (InstId.core name) w.roster : Int) +
                (if tname host = d then (n : Int) else 0) =
                (owed w.st d (InstId.core name) w.roster : Int) := by
              have hslotI : (slot w.st d (InstId.core name) host : Int) =
                  (slot st1 d (InstId.core name) host : Int) +
                    (if tname host = d then (n : Int) else 0) := by
                by_cases htd : tname host = d
                · have h := hslot
                  simp [htd] at h
                  have hcast := congrArg (fun k : Nat => (k : Int)) h
                  rw [Int.natCast_add] at hcast
                  simpa [htd] using hcast
                · have h := hslot
                  simp [htd] at h
                  simpa [htd] using congrArg (fun k : Nat => (k : Int)) h
              have hrepI : (owed st1 d (InstId.core name) w.roster : Int) +
                  (slot w.st d (InstId.core name) host : Int) =
                  (owed w.st d (InstId.core name) w.roster : Int) +
                    (slot st1 d (InstId.core name) host : Int) := by
                rw [← Int.natCast_add, ← Int.natCast_add, hrep']
              omega
            rw [htk']
            have hcomm : ((w.st (InstId.core name)).tokens d +
                (if tname host = d then (n : Int) else 0)) +
                (owed st1 d (InstId.core name) w.roster : Int) =
                (w.st (InstId.core name)).tokens d +
                  ((owed st1 d (InstId.core name) w.roster : Int) +
                    (if tname host = d then (n : Int) else 0)) := by
              ac_rfl
            rw [hcomm, howed', hbal]
          · have htk := htok (InstId.core name) d
            simp [hwho] at htk
            have hslotEq : slot (fun i => if i = host then stripped else w.st i) d (InstId.core name) host =
                slot w.st d (InstId.core name) host := by
              simp only [slot]
              by_cases ht : (tname host == d) = true
              · simp [ht, stripped]
                rw [countParked_filter_other (InstId.core name) dead (by simpa using hwho)]
              · simp [ht]
            let st1 := fun i => if i = host then stripped else w.st i
            have hrep := owed_replace w.st d (InstId.core name) host stripped w.roster hO.nodup hhost
            have howed2 : owed w2.st d (InstId.core name) w.roster = owed st1 d (InstId.core name) w.roster := by
              refine owed_mail_eq _ _ _ _ w.roster ?_
              intro i _
              constructor
              · by_cases hih : i = host
                · simp [hbox, st1, hih, stripped]
                · simp [hbox, st1, hih]
              · by_cases hih : i = host
                · simp [hpark, st1, hih, stripped]
                · simp [hpark, st1, hih]
            rw [howed2, htk]
            have hrep' : owed st1 d (InstId.core name) w.roster + slot w.st d (InstId.core name) host =
                owed w.st d (InstId.core name) w.roster + slot st1 d (InstId.core name) host := by
              simpa [st1] using hrep
            have hs : slot st1 d (InstId.core name) host = slot w.st d (InstId.core name) host := by
              simpa [st1] using hslotEq
            have howedEq : owed st1 d (InstId.core name) w.roster =
                owed w.st d (InstId.core name) w.roster := by
              omega
            rw [howedEq, hbal]
        · intro name key d hnone
          have hfindEq : findLive w2 name key = findLive w name key := by
            have hs1 : stripped.life = (w.st host).life := by simp [stripped]
            have hs2 : bumped.life = (w1.st dead).life := by simp [bumped, addTokens]
            have h1 := findLive_set_life w host stripped hs1 name key
            have h2 := findLive_set_life w1 dead bumped hs2 name key
            simpa [w2, w1] using h2.trans h1
          have hnone0 : findLive w name key = none := by rw [hfindEq] at hnone; exact hnone
          have hmsg : ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender :=
            fun p hp => hO.parkMsg host p hp
          have hnotEq : (fun p : Parked => p.sender != dead) = fun p => !(p.sender == dead) := by
            funext p; simp [bne]
          have hsplit := filter_count_split (fun p => p.sender == dead)
            (fun p => keyPred name key p.msg) (w.st host).parked
          have hboxA : stripped.box = (w.st host).box := by simp [stripped]
          have hdelta : ((w.st host).box.filter (keyPred name key)).length +
              ((w.st host).parked.filter fun p => keyPred name key p.msg).length =
              (stripped.box.filter (keyPred name key)).length +
                (stripped.parked.filter fun p => keyPred name key p.msg).length +
                ((dropped.filter fun p => keyPred name key p.msg).length) := by
            simp only [hboxA]
            have hp : stripped.parked =
                (w.st host).parked.filter fun p => !(p.sender == dead) := by
              simp [stripped, hnotEq]
            rw [hp, hsplit, Nat.add_assoc]
          have hq := queuedFromKey_replace w host stripped name key d
            ((dropped.filter fun p => keyPred name key p.msg).length) hO.nodup hhost hdelta
          have hq2 : queuedFromKey w2 name key d = queuedFromKey w1 name key d := by
            refine queuedFromKey_set w1 dead bumped ?_ ?_ name key d
            · simp [bumped, addTokens]
            · simp [bumped, addTokens]
          have hle : queuedFromKey w2 name key d ≤ queuedFromKey w name key d := by
            have hq' : queuedFromKey w name key d =
                queuedFromKey w1 name key d +
                  if tname host = d then
                    ((dropped.filter fun p => keyPred name key p.msg).length) else 0 := by
              simpa [w1] using hq
            rw [hq2, hq']
            omega
          have hold := hO.balance.2 name key d hnone0
          omega
      · intro s d hl
        have hold := hO.slack s d (by simpa [hlife] using hl)
        have hth := tokenHold_phase I.desc (tname s) d (w2.st s) (w.st s) (hph s) (hty s)
        have htk := htok s d
        rw [hth]
        have hnn : (0 : Int) ≤ if s = dead ∧ d = tname host then n else 0 := by
          by_cases hsd : s = dead ∧ d = tname host <;> simp [hsd, Int.natCast_nonneg]
        omega
      · intro s d hs hterm
        exact Nat.le_trans (howed_le d s) (hO.still s d (by simpa [hr] using hs) hterm)
      · intro hcr s d hs hdeadS
        have hle : (owed w2.st d s w.roster : Int) ≤ (owed w.st d s w.roster : Int) :=
          Int.ofNat_le.mpr (howed_le d s)
        exact Int.le_trans hle
          (hO.quiet (by simpa [w2, w1, setActor] using hcr) s d (by simpa [hr] using hs)
            (by simpa [hlife] using hdeadS))
      · intro hcr i hdeadL
        have hempty := hO.deadEmpty (by simpa [w2, w1, setActor] using hcr) i
          (by simpa [hlife] using hdeadL)
        rw [hbox i]
        by_cases hih : i = host
        · rw [hih] at hempty ⊢
          refine ⟨hempty.1, ?_⟩
          rw [hpark]
          simp [hempty.2]
        · rw [hpark, ite_eq_right hih]
          simp [hempty]
      · intro host'
        refine ⟨?_, ?_⟩
        · intro m hm
          rw [hbox host'] at hm
          exact (hO.sameKey host').1 m hm
        · intro p hp
          rw [hpark host'] at hp
          by_cases hih : host' = host
          · rw [hih] at hp ⊢
            simp at hp
            simpa [queueOk] using (hO.sameKey host).2 p hp.1
          · simp [hih] at hp
            exact (hO.sameKey host').2 p hp
      · intro i hi
        exact hO.shaped i (by simpa [hr] using hi)
      · intro host' hk
        refine ⟨?_, ?_⟩
        · intro m hm
          rw [hbox host'] at hm
          exact (hO.coreFrom host' hk).1 m hm
        · intro p hp
          rw [hpark host'] at hp
          by_cases hih : host' = host
          · rw [hih] at hp hk
            simp at hp
            exact (hO.coreFrom host hk).2 p hp.1
          · simp [hih] at hp
            exact (hO.coreFrom host' hk).2 p hp
      · exact ixFresh_copy I.desc w w2 hO.ixFresh hr hix

theorem dropOutbound_roster (w : World) (dead host : InstId) :
    (dropOutbound w dead host).roster = w.roster := by
  unfold dropOutbound
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp [setActor]

theorem dropOutbound_life (w : World) (dead host i : InstId) :
    ((dropOutbound w dead host).st i).life = (w.st i).life := by
  unfold dropOutbound
  split
  · rfl
  · rename_i hneB
    dsimp only
    split
    · rfl
    · have hne : host ≠ dead := by
        intro h
        simp [h] at hneB
      by_cases hid : i = dead
      · simp [setActor, addTokens, hid, if_neg (Ne.symm hne)]
      · by_cases hih : i = host
        · simp [setActor, addTokens, hid, hih, hne, if_neg hne]
        · simp [setActor, addTokens, hid, hih]

theorem occ_releaseOutbound (I : Impl) (w : World) (dead : InstId) (hO : OccInv I w)
    (hdead : dead ∈ w.roster) (hlive : (w.st dead).life = .alive) :
    OccInv I (releaseOutbound w dead) := by
  rw [releaseOutbound_fold]
  suffices ∀ (ids : List InstId) (w0 : World), OccInv I w0 → dead ∈ w0.roster →
      (w0.st dead).life = .alive → (∀ host, host ∈ ids → host ∈ w0.roster) →
      OccInv I (ids.foldl (fun acc host => dropOutbound acc dead host) w0) by
    exact this w.roster w hO hdead hlive (fun _ h => h)
  intro ids
  induction ids with
  | nil =>
    intro w0 hO0 _ _ _
    simpa using hO0
  | cons host ids ih =>
    intro w0 hO0 hdead0 hlive0 hsub
    simp only [List.foldl_cons]
    have hstep := occ_dropHost I w0 dead host hO0 hdead0 (hsub host (by simp)) hlive0
    have hr := dropOutbound_roster w0 dead host
    have hl := dropOutbound_life w0 dead host dead
    exact ih (dropOutbound w0 dead host) hstep (by simpa [hr] using hdead0)
      (hl.trans hlive0) (fun h hm => by simpa [hr] using hsub h (by simp [hm]))

theorem dropOutbound_box (w : World) (dead host i : InstId) :
    ((dropOutbound w dead host).st i).box = (w.st i).box := by
  unfold dropOutbound
  split
  · rfl
  · rename_i hneB
    dsimp only
    split
    · rfl
    · have hne : host ≠ dead := by
        intro h
        simp [h] at hneB
      by_cases hid : i = dead
      · simp [setActor, addTokens, hid, ite_eq_right (Ne.symm hne)]
      · by_cases hih : i = host
        · simp [setActor, addTokens, hid, hih, hne, ite_eq_right hne]
        · simp [setActor, addTokens, hid, hih]

theorem dropOutbound_crashed (w : World) (dead host : InstId) :
    (dropOutbound w dead host).crashed = w.crashed := by
  unfold dropOutbound
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp [setActor]

theorem releaseOutbound_box (w : World) (dead i : InstId) :
    ((releaseOutbound w dead).st i).box = (w.st i).box := by
  rw [releaseOutbound_fold]
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun acc host => dropOutbound acc dead host) w0).st i).box = (w0.st i).box from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro _; rfl
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    exact (ih (dropOutbound w0 dead host)).trans (dropOutbound_box w0 dead host i)

/-- Two worlds that agree everywhere except the mailbox and parked lane of `id`.
`releaseOutbound` never reads those two fields: it skips `id` itself. -/
structure SameSlot (id : InstId) (w1 w2 : World) : Prop where
  N : w1.N = w2.N
  roster : w1.roster = w2.roster
  nextIx : w1.nextIx = w2.nextIx
  nextKey : w1.nextKey = w2.nextKey
  cell : w1.cell = w2.cell
  observed : w1.observed = w2.observed
  failures : w1.failures = w2.failures
  crashed : w1.crashed = w2.crashed
  other : ∀ i, i ≠ id → w1.st i = w2.st i
  life : (w1.st id).life = (w2.st id).life
  ty : (w1.st id).typestate = (w2.st id).typestate
  phase : (w1.st id).phase = (w2.st id).phase
  prio : (w1.st id).prio = (w2.st id).prio
  tokens : ∀ d, (w1.st id).tokens d = (w2.st id).tokens d
  mid : (w1.st id).nextMid = (w2.st id).nextMid
  waitId : (w1.st id).waitId = (w2.st id).waitId
  nextCall : (w1.st id).nextCall = (w2.st id).nextCall
  oweId : (w1.st id).oweId = (w2.st id).oweId
  lastCall : (w1.st id).lastCall = (w2.st id).lastCall
  pending : (w1.st id).pendingTombstone = (w2.st id).pendingTombstone
  parent : (w1.st id).parent = (w2.st id).parent

theorem dropOutbound_frame (w : World) (id host : InstId) :
    (dropOutbound w id host).N = w.N ∧ (dropOutbound w id host).roster = w.roster ∧
      (dropOutbound w id host).nextIx = w.nextIx ∧ (dropOutbound w id host).nextKey = w.nextKey ∧
      (dropOutbound w id host).cell = w.cell ∧ (dropOutbound w id host).observed = w.observed ∧
      (dropOutbound w id host).failures = w.failures ∧ (dropOutbound w id host).crashed = w.crashed := by
  unfold dropOutbound
  split
  · simp
  · dsimp only
    split
    · simp
    · simp [setActor]

theorem dropOutbound_st (w : World) (id host i : InstId) (hne : host ≠ id)
    (hgo : ((w.st host).parked.filter fun p => p.sender == id).isEmpty = false) :
    let dropped := (w.st host).parked.filter fun p => p.sender == id
    (dropOutbound w id host).st i =
      if i = host then { (w.st host) with parked := (w.st host).parked.filter fun p => p.sender != id }
      else if i = id then addTokens (w.st id) (tname host) dropped.length
      else w.st i := by
  intro dropped
  unfold dropOutbound
  have hb : (host == id) = false := by simpa [beq_iff_eq] using hne
  simp only [hb, Bool.false_eq_true, ite_false]
  have hempty : dropped.isEmpty = false := hgo
  simp only [dropped, hempty, Bool.false_eq_true, ite_false]
  by_cases hih : i = host
  · simp [setActor, addTokens, hih, hne]
  · by_cases hid : i = id
    · simp [setActor, addTokens, hih, hid, ite_eq_right (Ne.symm hne)]
    · simp [setActor, addTokens, hih, hid]

theorem sameSlot_drop (id host : InstId) (w1 w2 : World) (h : SameSlot id w1 w2) :
    SameSlot id (dropOutbound w1 id host) (dropOutbound w2 id host) := by
  by_cases hhost : host = id
  · have hb : (host == id) = true := by simpa [beq_iff_eq] using hhost
    simp [dropOutbound, hb]
    exact h
  · have hactor : w1.st host = w2.st host := h.other host hhost
    let dropped := (w1.st host).parked.filter fun p => p.sender == id
    by_cases hempty : dropped.isEmpty = true
    · unfold dropOutbound
      have hb : (host == id) = false := by simpa [beq_iff_eq] using hhost
      simp only [hb, Bool.false_eq_true, ite_false]
      simp only [dropped] at hempty
      rw [hactor] at hempty ⊢
      rw [hempty]
      simp only [ite_true]
      exact h
    · have hgo : dropped.isEmpty = false := by
        cases hbool : dropped.isEmpty
        · rfl
        · exact (hempty hbool).elim
      have hst1 := dropOutbound_st w1 id host
      have hst2 := dropOutbound_st w2 id host
      have hgo2 : ((w2.st host).parked.filter fun p => p.sender == id).isEmpty = false := by
        rw [← hactor]
        exact hgo
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (dropOutbound_frame w1 id host).1.trans
          (h.N.trans (dropOutbound_frame w2 id host).1.symm)
      · exact (dropOutbound_frame w1 id host).2.1.trans
          (h.roster.trans (dropOutbound_frame w2 id host).2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.1.trans
          (h.nextIx.trans (dropOutbound_frame w2 id host).2.2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.2.1.trans
          (h.nextKey.trans (dropOutbound_frame w2 id host).2.2.2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.2.2.1.trans
          (h.cell.trans (dropOutbound_frame w2 id host).2.2.2.2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.2.2.2.1.trans
          (h.observed.trans (dropOutbound_frame w2 id host).2.2.2.2.2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.2.2.2.2.1.trans
          (h.failures.trans (dropOutbound_frame w2 id host).2.2.2.2.2.2.1.symm)
      · exact (dropOutbound_frame w1 id host).2.2.2.2.2.2.2.trans
          (h.crashed.trans (dropOutbound_frame w2 id host).2.2.2.2.2.2.2.symm)
      · intro i hi
        rw [hst1 i hhost hgo, hst2 i hhost hgo2]
        by_cases hih : i = host
        · simp [hih, hactor]
        · simp [hih, hi, h.other i hi]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.life]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.ty]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.phase]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.prio]
      · intro d
        rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, hactor, h.tokens d]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.mid]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.waitId]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.nextCall]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.oweId]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.lastCall]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.pending]
      · rw [hst1 id hhost hgo, hst2 id hhost hgo2]
        simp only [ite_eq_right (Ne.symm hhost), ite_true, addTokens, h.parent]

theorem sameSlot_outbound (id : InstId) (w1 w2 : World) (h : SameSlot id w1 w2) :
    SameSlot id (releaseOutbound w1 id) (releaseOutbound w2 id) := by
  rw [releaseOutbound_fold, releaseOutbound_fold, h.roster]
  suffices ∀ (ids : List InstId) (w1 w2 : World), SameSlot id w1 w2 →
      SameSlot id (ids.foldl (fun acc host => dropOutbound acc id host) w1)
        (ids.foldl (fun acc host => dropOutbound acc id host) w2) by
    exact this w2.roster w1 w2 h
  intro ids
  induction ids with
  | nil =>
    intro w1 w2 h
    simpa using h
  | cons host ids ih =>
    intro w1 w2 h
    simp only [List.foldl_cons]
    exact ih _ _ (sameSlot_drop id host w1 w2 h)

theorem sameSlot_seal (id : InstId) (w1 w2 : World) (h : SameSlot id w1 w2) :
    setActor w1 id { (w1.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] } =
      setActor w2 id { (w2.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] } := by
  let dead1 : Actor := { (w1.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  let dead2 : Actor := { (w2.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  have hdead : dead1 = dead2 := by
    apply actor_fields
    · rfl
    · simpa [dead1, dead2] using h.ty
    · rfl
    · rfl
    · rfl
    · rfl
    · intro d; simpa [dead1, dead2] using h.tokens d
    · simpa [dead1, dead2] using h.mid
    · simpa [dead1, dead2] using h.waitId
    · simpa [dead1, dead2] using h.nextCall
    · simpa [dead1, dead2] using h.oweId
    · simpa [dead1, dead2] using h.lastCall
    · simpa [dead1, dead2] using h.pending
    · simpa [dead1, dead2] using h.parent
  apply world_eq
  · exact h.N
  · exact h.roster
  · exact h.nextIx
  · exact h.nextKey
  · funext i
    by_cases hi : i = id
    · simp [setActor, hi, dead1, dead2, hdead]
    · simp [setActor, hi, h.other i hi]
  · exact h.cell
  · exact h.observed
  · exact h.failures
  · exact h.crashed

/-- Draining a mailbox is the refund followed by clearing that actor, and the
clear does not change any field `releaseOutbound` reads. The two worlds
therefore agree except on the cleared mailbox. -/
theorem drain_refund_same (w : World) (id : InstId) :
    let name := tname id
    let ms := (w.st id).box
    let ps := (w.st id).parked
    let drained := drainPark (drainBox w id name ms) id name ps
    let refunded := refundParked (refundMsgs w name ms) name ps
    SameSlot id drained refunded := by
  intro name ms ps drained refunded
  have hfD := frame_drainP (drainBox w id name ms) id name ps
  have hfB := frame_drain w id name ms
  have hfR := frame_refundP (refundMsgs w name ms) name ps
  have hfM := frame_refund w name ms
  have hkD := kept_drainP (drainBox w id name ms) id name ps
  have hkB := kept_drain w id name ms
  have hkR := kept_refundP (refundMsgs w name ms) name ps
  have hkM := kept_refund w name ms
  have hmD := meta_drainP (drainBox w id name ms) id name ps
  have hmB := meta_drain w id name ms
  have hmR := meta_refundP (refundMsgs w name ms) name ps
  have hmM := meta_refund w name ms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfD.1.trans (hfB.1.trans (hfM.1.symm.trans hfR.1.symm))
  · exact hfD.2.1.trans (hfB.2.1.trans (hfM.2.1.symm.trans hfR.2.1.symm))
  · exact hfD.2.2.1.trans (hfB.2.2.1.trans (hfM.2.2.1.symm.trans hfR.2.2.1.symm))
  · exact hkD.1.trans (hkB.1.trans (hkM.1.symm.trans hkR.1.symm))
  · exact hfD.2.2.2.1.trans (hfB.2.2.2.1.trans (hfM.2.2.2.1.symm.trans hfR.2.2.2.1.symm))
  · exact hfD.2.2.2.2.trans (hfB.2.2.2.2.trans (hfM.2.2.2.2.symm.trans hfR.2.2.2.2.symm))
  · exact hmD.trans (hmB.trans (hmM.symm.trans hmR.symm))
  · exact hkD.2.trans (hkB.2.trans (hkM.2.symm.trans hkR.2.symm))
  · intro i hi
    have hterm := term_actor w id i
    simp only [setActor, hi] at hterm
    exact hterm
  · exact (drainP_life (drainBox w id name ms) id name ps id).1.trans
      ((drain_life w id name ms id).1.trans
        ((refund_life w name ms id).1.symm.trans
          (refundP_life (refundMsgs w name ms) name ps id).1.symm))
  · exact (drainP_life (drainBox w id name ms) id name ps id).2.1.trans
      ((drain_life w id name ms id).2.1.trans
        ((refund_life w name ms id).2.1.symm.trans
          (refundP_life (refundMsgs w name ms) name ps id).2.1.symm))
  · exact (drainP_life (drainBox w id name ms) id name ps id).2.2.1.trans
      ((drain_life w id name ms id).2.2.1.trans
        ((refund_life w name ms id).2.2.1.symm.trans
          (refundP_life (refundMsgs w name ms) name ps id).2.2.1.symm))
  · exact (drainP_life (drainBox w id name ms) id name ps id).2.2.2.trans
      ((drain_life w id name ms id).2.2.2.trans
        ((refund_life w name ms id).2.2.2.symm.trans
          (refundP_life (refundMsgs w name ms) name ps id).2.2.2.symm))
  · intro d
    simpa using term_tok w id id d
  · exact (drainP_mid (drainBox w id name ms) id name ps id).trans
      ((drain_mid w id name ms id).trans
        ((refund_mid w name ms id).symm.trans
          (refundP_mid (refundMsgs w name ms) name ps id).symm))
  · exact (sameStamps_trans (drainP_stamps (drainBox w id name ms) id name ps id)
      (sameStamps_trans (drain_stamps w id name ms id)
        (sameStamps_trans (sameStamps_symm (refund_stamps w name ms id))
          (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps id))))).1
  · exact (sameStamps_trans (drainP_stamps (drainBox w id name ms) id name ps id)
      (sameStamps_trans (drain_stamps w id name ms id)
        (sameStamps_trans (sameStamps_symm (refund_stamps w name ms id))
          (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps id))))).2.1
  · exact (sameStamps_trans (drainP_stamps (drainBox w id name ms) id name ps id)
      (sameStamps_trans (drain_stamps w id name ms id)
        (sameStamps_trans (sameStamps_symm (refund_stamps w name ms id))
          (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps id))))).2.2.1
  · exact (sameStamps_trans (drainP_stamps (drainBox w id name ms) id name ps id)
      (sameStamps_trans (drain_stamps w id name ms id)
        (sameStamps_trans (sameStamps_symm (refund_stamps w name ms id))
          (sameStamps_symm (refundP_stamps (refundMsgs w name ms) name ps id))))).2.2.2
  · exact (actor_kept_drainP (drainBox w id name ms) id name ps id).1.trans
      ((actor_kept_drain w id name ms id).1.trans
        ((actor_kept_refund w name ms id).1.symm.trans
          (actor_kept_refundP (refundMsgs w name ms) name ps id).1.symm))
  · exact (actor_kept_drainP (drainBox w id name ms) id name ps id).2.trans
      ((actor_kept_drain w id name ms id).2.trans
        ((actor_kept_refund w name ms id).2.symm.trans
          (actor_kept_refundP (refundMsgs w name ms) name ps id).2.symm))

theorem releaseWorld_eq_drain (D : Description) (w : World) (id : InstId) :
    let wR := readCells D w id
    let name := tname id
    let ms := (w.st id).box
    let ps := (w.st id).parked
    let drained := drainPark (drainBox wR id name ms) id name ps
    let out := releaseOutbound drained id
    let dead := { (out.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
    releaseWorld D w id (w.st id) = releaseParked (setActor out id dead) id ps := by
  intro wR name ms ps drained out dead
  have hst : (wR.st id).box = ms ∧ (wR.st id).parked = ps := by
    have hs := readCells_st D w id id
    exact ⟨congrArg Actor.box hs, congrArg Actor.parked hs⟩
  have hsame : SameSlot id drained (refundParked (refundMsgs wR name ms) name ps) := by
    simpa [drained, name, ms, ps, hst.1, hst.2] using drain_refund_same wR id
  have hout := sameSlot_outbound id _ _ hsame
  have hseal := sameSlot_seal id _ _ hout
  unfold releaseWorld
  simp only [wR, name, ms, ps]
  exact congrArg (fun world => releaseParked world id ps) hseal.symm

/-- Refunding a terminable actor's mailbox, returning its outbound parked slots,
and resuming the senders parked on it keeps the account. The actor is alive, so
the returned slots are credited to the live holder. -/
theorem occ_releaseWorld (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hlive : (w.st id).life = .alive) (hcr : w.crashed = false) :
    OccInv I (releaseWorld I.desc w id (w.st id)) ∧
      ∀ i, contTy ((releaseWorld I.desc w id (w.st id)).st i) := by
  rw [releaseWorld_eq_drain]
  let name := tname id
  let ms := (w.st id).box
  let ps := (w.st id).parked
  let wR := readCells I.desc w id
  have hOR := occ_same I w wR hO (fun i => readCells_st I.desc w id i)
    (read_roster I.desc w id).1 (read_roster I.desc w id).2 (fun n => readCells_nextIx I.desc w id n)
    (readCells_crashed I.desc w id)
  have hCR : ∀ i, contTy (wR.st i) := by
    intro i
    have hs := readCells_st I.desc w id i
    exact (contTy_match _ _ (congrArg Actor.phase hs) (congrArg Actor.typestate hs)).mpr (hC i)
  have hmemR : id ∈ wR.roster := by
    rw [(read_roster I.desc w id).1]
    exact hmem
  have hcrR : wR.crashed = false := (readCells_crashed I.desc w id).trans hcr
  have hliveR : (wR.st id).life = .alive := by
    rw [congrArg Actor.life (readCells_st I.desc w id id)]
    exact hlive
  have hboxR : (wR.st id).box = ms := congrArg Actor.box (readCells_st I.desc w id id)
  have hparkR : (wR.st id).parked = ps := congrArg Actor.parked (readCells_st I.desc w id id)
  have hOB := occ_drain_box I wR id ms hOR hmemR hboxR hcrR
  let wB := drainBox wR id name ms
  have hmemB : id ∈ wB.roster := by simpa [wB, (frame_drain wR id name ms).2.1] using hmemR
  have hcrB : wB.crashed = false := (kept_drain wR id name ms).2.trans hcrR
  have hparkB : (wB.st id).parked = ps := by simpa [wB, hparkR] using drain_park wR id name ms id
  have hmsg : ∀ p ∈ ps, p.sender = p.msg.sender := fun p hp => hOR.parkMsg id p (hparkR ▸ hp)
  have hOP := occ_drain_park I wB id ps hOB hmemB hparkB hmsg hcrB
  let wP := drainPark wB id name ps
  have hmemP : id ∈ wP.roster := by
    simpa [wP, (frame_drainP wB id name ps).2.1] using hmemB
  have hliveP : (wP.st id).life = .alive := by
    simpa [wP, hliveR] using
      (drainP_life wB id name ps id).1.trans (drain_life wR id name ms id).1
  have hOO := occ_releaseOutbound I wP id hOP hmemP hliveP
  let wO := releaseOutbound wP id
  have hemptyB : (wO.st id).box = [] := by
    rw [releaseOutbound_box]
    simpa [wP] using (drainP_box wB id name ps id).trans (drain_box wR id name ms id)
  have hemptyP : (wO.st id).parked = [] := by
    have hf := (releaseOutbound_fields wP id id).2.2.2.2
    simp only [hmemP] at hf
    simpa [wO, hf] using (drainP_park wB id name ps id)
  have hcrO : wO.crashed = false := (releaseOutbound_crashed wP id).trans
    ((kept_drainP wB id name ps).2.trans hcrB)
  have hmemO : id ∈ wO.roster := by simpa [wO, (releaseOutbound_fields wP id id).1] using hmemP
  have hbound : ∀ d, owed wO.st d id wO.roster ≤ budget I.desc name d :=
    fun d => owed_within I wO hOO id hmemO hcrO d
  have hOD := occ_die I wO id hOO hmemO hemptyB hemptyP hbound
  let dead : Actor := { (wO.st id) with life := .dead, phase := .idle, prio := [], box := [], parked := [] }
  have hCD : ∀ i, contTy ((setActor wO id dead).st i) := by
    intro i
    by_cases hi : i = id
    · simp [setActor, hi, dead, contTy]
    · have hph : ((setActor wO id dead).st i).phase = (wO.st i).phase := by simp [setActor, hi]
      have hty : ((setActor wO id dead).st i).typestate = (wO.st i).typestate := by simp [setActor, hi]
      have hpre : contTy (wO.st i) := by
        have hph0 : (wO.st i).phase = (wP.st i).phase := (releaseOutbound_fields wP id i).2.2.2.1
        have hty0 : (wO.st i).typestate = (wP.st i).typestate := (releaseOutbound_fields wP id i).2.2.1
        have hph1 : (wP.st i).phase = (wR.st i).phase :=
          (drainP_life wB id name ps i).2.2.1.trans (drain_life wR id name ms i).2.2.1
        have hty1 : (wP.st i).typestate = (wR.st i).typestate :=
          (drainP_life wB id name ps i).2.1.trans (drain_life wR id name ms i).2.1
        exact (contTy_match _ _ (hph0.trans hph1) (hty0.trans hty1)).mpr (hCR i)
      exact (contTy_match _ _ hph hty).mpr hpre
  have hrel := occ_release I (setActor wO id dead) id ps hOD hCD
  simpa [name, ms, ps, wR, wB, wP, wO, dead] using hrel

theorem failWaiter_crashed (w : World) (dead i : InstId) :
    (failWaiter w dead i).crashed = w.crashed := by
  unfold failWaiter
  split
  · rfl
  · split
    · split
      · exact setActor_crashed _ _ _
      · rfl
    · rfl

theorem failFold_crashed (w : World) (dead : InstId) (ids : List InstId) :
    (ids.foldl (fun w i => failWaiter w dead i) w).crashed = w.crashed := by
  induction ids generalizing w with
  | nil => rfl
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact (ih (failWaiter w dead i)).trans (failWaiter_crashed w dead i)

theorem forgetHost_crashed (w : World) (dead host : InstId) :
    (forgetHost w dead host).crashed = w.crashed := by
  unfold forgetHost
  split
  · rfl
  · split
    · rfl
    · simp [setActor]

theorem forget_crashed (w : World) (dead : InstId) :
    (forgetSender w dead).crashed = w.crashed := by
  unfold forgetSender
  suffices ∀ (ids : List InstId) (w0 : World),
      (ids.foldl (fun w host => forgetHost w dead host) w0).crashed = w0.crashed from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro w0; rfl
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    exact (ih (forgetHost w0 dead host)).trans (forgetHost_crashed w0 dead host)

/-- `killOne` refunds, fails waiters, and reclaims outbound mail. None of those
steps sets the crashed flag. -/
theorem killOne_crashed (w : World) (D : Description) (id : InstId) :
    (killOne w D id).crashed = w.crashed := by
  unfold killOne
  simp only [setActor]
  rw [forget_crashed, failWaiters, failFold_crashed, refundParked_crashed, refundMsgs_crashed,
    readCells_crashed]

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

/-- A tombstone is a priority offer. A full lane or an empty label crashes the
roster, which keeps the account. A parent that is not alive drops it. A fit
appends one priority message and does not touch the token reserve. -/
theorem occ_tombstone (I : Impl) (w : World) (child : InstId) (hO : OccInv I w) :
    OccInv I (enqueueTombstone I.desc w child) := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none =>
    simp [hpar]
    exact hO
  | some parent =>
    simp only [hpar]
    by_cases hdead : ((w.st parent).life != .alive) = true
    · rw [hdead]
      simp only [ite_true]
      exact hO
    · rw [ite_eq_right hdead]
      by_cases hlab : ((tombstoneMsg I.desc (w.st parent) child).label == "") = true
      · rw [hlab]
        simp only [ite_true]
        exact occ_crash I w hO
      · rw [ite_eq_right hlab]
        by_cases hfull : decide (prioLoad (w.st parent).prio ≥ capPrio I.desc w.N parent) = true
        · rw [offerPrio, hfull]
          simp only [ite_true]
          exact occ_crash I w hO
        · rw [offerPrio, ite_eq_right hfull]
          let a := { (w.st parent) with
            prio := (w.st parent).prio ++ [tombstoneMsg I.desc (w.st parent) child]
            nextMid := (w.st parent).nextMid + 1 }
          refine occ_keep I w parent a hO rfl rfl rfl (fun _ => rfl) ?_
          intro d _
          have hsame : tokenHold I.desc (tname parent) d a =
              tokenHold I.desc (tname parent) d (w.st parent) := by
            cases hph : (w.st parent).phase <;> simp [tokenHold, a, hph]
          rw [hsame]
          omega

/-- Sealing a branch refunds each live descendant and then the actor itself.
A life that is not alive is left in place. Crashed stays false: this step does
not offer a tombstone. -/
theorem occ_sealBranch (fuel : Nat) (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hcr : w.crashed = false) :
    (OccInv I (sealBranch fuel I.desc w id) ∧ ∀ i, contTy ((sealBranch fuel I.desc w id).st i)) ∧
      (sealBranch fuel I.desc w id).crashed = false ∧
      (sealBranch fuel I.desc w id).roster = w.roster := by
  induction fuel generalizing w id with
  | zero =>
    unfold sealBranch
    exact ⟨⟨hO, hC⟩, ⟨hcr, rfl⟩⟩
  | succ fuel ih =>
    simp only [sealBranch]
    have hfold : ∀ (ids : List InstId) (w0 : World), OccInv I w0 → (∀ i, contTy (w0.st i)) →
        w0.crashed = false → w0.roster = w.roster →
        let sealed := ids.foldl (fun acc child =>
          if isChild acc id child then sealBranch fuel I.desc acc child else acc) w0
        (OccInv I sealed ∧ ∀ i, contTy (sealed.st i)) ∧ sealed.crashed = false ∧
          sealed.roster = w.roster := by
      intro ids
      induction ids with
      | nil =>
        intro w0 hO0 hC0 hcr0 hr0
        rw [List.foldl_nil]
        exact ⟨⟨hO0, hC0⟩, ⟨hcr0, hr0⟩⟩
      | cons c ids ihf =>
        intro w0 hO0 hC0 hcr0 hr0
        simp only [List.foldl_cons]
        by_cases hgo : isChild w0 id c = true
        · rw [if_pos hgo]
          have hstep := ih w0 c hO0 hC0 hcr0
          exact ihf _ hstep.1.1 hstep.1.2 hstep.2.1 (hstep.2.2.trans hr0)
        · rw [if_neg hgo]
          exact ihf _ hO0 hC0 hcr0 hr0
    have hsealed := hfold w.roster w hO hC hcr rfl
    let sealed := w.roster.foldl (fun acc child =>
      if isChild acc id child then sealBranch fuel I.desc acc child else acc) w
    by_cases hlive : ((sealed.st id).life == .alive) = true
    · have hliveP : (sealed.st id).life = .alive := by simpa [beq_iff_eq] using hlive
      have hmem : id ∈ sealed.roster := hsealed.1.1.aliveIn _ hliveP
      rw [hlive]
      simp only [ite_true]
      have hrel := occ_releaseWorld I sealed id hsealed.1.1 hsealed.1.2 hmem hliveP hsealed.2.1
      refine And.intro hrel (And.intro ?_ ?_)
      · exact (releaseWorld_crashed I.desc sealed id (sealed.st id)).trans hsealed.2.1
      · exact (releaseWorld_roster I.desc sealed id (sealed.st id)).trans hsealed.2.2
    · rw [ite_eq_right hlive]
      exact hsealed

/-- Proper descendants are sealed, and the stage itself stays for its tombstone. -/
theorem occ_dropDesc (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hcr : w.crashed = false) :
    (OccInv I (dropDescendants I.desc w id) ∧ ∀ i, contTy ((dropDescendants I.desc w id).st i)) ∧
      (dropDescendants I.desc w id).crashed = false ∧
      (dropDescendants I.desc w id).roster = w.roster := by
  unfold dropDescendants
  suffices ∀ (ids : List InstId) (w0 : World), OccInv I w0 → (∀ i, contTy (w0.st i)) →
      w0.crashed = false → w0.roster = w.roster →
      let sealed := ids.foldl (fun acc child =>
        if isChild acc id child then sealBranch w.roster.length I.desc acc child else acc) w0
      (OccInv I sealed ∧ ∀ i, contTy (sealed.st i)) ∧ sealed.crashed = false ∧
        sealed.roster = w.roster by
    exact this w.roster w hO hC hcr rfl
  intro ids
  induction ids with
  | nil =>
    intro w0 hO0 hC0 hcr0 hr0
    rw [List.foldl_nil]
    exact ⟨⟨hO0, hC0⟩, ⟨hcr0, hr0⟩⟩
  | cons c ids ih =>
    intro w0 hO0 hC0 hcr0 hr0
    simp only [List.foldl_cons]
    by_cases hgo : isChild w0 id c = true
    · rw [if_pos hgo]
      have hstep := occ_sealBranch w.roster.length I w0 c hO0 hC0 hcr0
      exact ih _ hstep.1.1 hstep.1.2 hstep.2.1 (hstep.2.2.trans hr0)
    · rw [if_neg hgo]
      exact ih _ hO0 hC0 hcr0 hr0

/-- A stage terminates by sealing its descendants and then itself. The stage's
tombstone is offered to its parent. A life that is not alive is left alone. -/
theorem occ_terminate (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hC : ∀ i, contTy (w.st i)) (hcr : w.crashed = false) :
    OccInv I (terminateStage I.desc w id (w.st id)) := by
  unfold terminateStage shutdownActor
  have hdesc := occ_dropDesc I w id hO hC hcr
  let dropped := dropDescendants I.desc w id
  by_cases hlive : ((dropped.st id).life == .alive) = true
  · have hliveP : (dropped.st id).life = .alive := by simpa [beq_iff_eq] using hlive
    have hmem : id ∈ dropped.roster := hdesc.1.1.aliveIn _ hliveP
    rw [hlive]
    simp only [ite_true, sealActor]
    have hrel := occ_releaseWorld I dropped id hdesc.1.1 hdesc.1.2 hmem hliveP hdesc.2.1
    exact occ_tombstone I (releaseWorld I.desc dropped id (dropped.st id)) id hrel.1
  · rw [ite_eq_right hlive]
    exact hdesc.1.1


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
    (hdead : dead ∈ w.roster) (hhost : host ∈ w.roster) (hlive : (w.st dead).life = .alive) :
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
      · intro name key g1 g2 h1 h2 ha1 ha2
        rw [hr] at h1 h2
        rw [hlife] at ha1 ha2
        exact hO.indexed name key g1 g2 h1 h2 ha1 ha2
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
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro name key id d hfind
          have hfindEq : findLive (setActor mid dead bumped) name key = findLive w name key := by
            have hs1 : stripped.life = (w.st host).life := by simp [stripped, stripSender]
            have hs2 : bumped.life = (mid.st dead).life := by simp [bumped, addTokens]
            have h1 := findLive_set_life w host stripped hs1 name key
            have h2 := findLive_set_life mid dead bumped hs2 name key
            simpa [mid] using h2.trans h1
          have hfind0 : findLive w name key = some id := by rw [hfindEq] at hfind; exact hfind
          have hmsg : ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender :=
            fun p hp => hO.parkMsg host p hp
          let extra :=
            (((w.st host).box.filter fun m => m.sender == dead).filter (keyPred name key)).length +
              (((w.st host).parked.filter fun p => p.sender == dead).filter
                fun p => keyPred name key p.msg).length
          have hnotB : (fun m : Msg => m.sender != dead) = fun m => !(m.sender == dead) := by
            funext m; simp [bne]
          have hnotP : (fun p : Parked => p.sender != dead) = fun p => !(p.sender == dead) := by
            funext p; simp [bne]
          have hsplitB := filter_count_split_msg (fun m => m.sender == dead)
            (keyPred name key) (w.st host).box
          have hsplitP := filter_count_split (fun p => p.sender == dead)
            (fun p => keyPred name key p.msg) (w.st host).parked
          have hdelta :
              ((w.st host).box.filter (keyPred name key)).length +
                ((w.st host).parked.filter fun p => keyPred name key p.msg).length =
              (stripped.box.filter (keyPred name key)).length +
                (stripped.parked.filter fun p => keyPred name key p.msg).length + extra := by
            have hboxS : stripped.box =
                (w.st host).box.filter fun m => !(m.sender == dead) := by
              simp [stripped, stripSender, hnotB]
            have hparkS : stripped.parked =
                (w.st host).parked.filter fun p => !(p.sender == dead) := by
              simp [stripped, stripSender, hnotP]
            rw [hboxS, hparkS, hsplitB, hsplitP]
            simp only [extra]
            omega
          have hq := queuedFromKey_replace w host stripped name key d extra hO.nodup hhost hdelta
          have hq2 : queuedFromKey (setActor mid dead bumped) name key d =
              queuedFromKey mid name key d := by
            refine queuedFromKey_set mid dead bumped ?_ ?_ name key d
            · simp [bumped, addTokens]
            · simp [bumped, addTokens]
          have hbit : (queuedFromKey w name key d : Int) =
              (queuedFromKey (setActor mid dead bumped) name key d : Int) +
                if tname host = d then (extra : Int) else 0 := by
            have hq' : queuedFromKey w name key d =
                queuedFromKey mid name key d + if tname host = d then extra else 0 := by
              simpa [mid] using hq
            rw [hq2, hq']
            by_cases htd : tname host = d <;> simp [htd, Int.natCast_add]
          have hbal := hO.balance.1.1 name key id d hfind0
          by_cases hwho : id = dead
          · have hpeer : ∃ g, dead = InstId.peer name key g := by
              rw [← hwho]
              exact findLive_peer w name key id hfind0
            obtain ⟨g, hdeadP⟩ := hpeer
            have hallB := box_all_key dead (w.st host).box name key g hdeadP
            have hallP := dropped_all_key dead (w.st host).parked name key g hmsg hdeadP
            have hall : extra = n := by
              have hboth : extra =
                  ((w.st host).box.filter fun m => m.sender == dead).length +
                    ((w.st host).parked.filter fun p => p.sender == dead).length := by
                simp only [extra, hallB, hallP]
              simpa [n, outboundCount] using hboth
            have htk := htokDead d
            have htk' : ((setActor mid dead bumped).st id).tokens d =
                (w.st id).tokens d + (if tname host = d then (n : Int) else 0) := by
              rw [hwho]
              by_cases htd : tname host = d
              · simp [htd, htk]
              · have hflip : ¬ d = tname host := fun h => htd h.symm
                simp [htd, hflip, htk]
            rw [hall] at hbit
            rw [htk']
            have hjoin : (w.st id).tokens d + (queuedFromKey w name key d : Int) =
                ((w.st id).tokens d + (if tname host = d then (n : Int) else 0)) +
                  (queuedFromKey (setActor mid dead bumped) name key d : Int) := by
              rw [hbit]
              ac_rfl
            rw [← hjoin, hbal]
          · have hnot : ∀ g, dead ≠ InstId.peer name key g := by
              intro g hdeadP
              have hliveD : findLive w name key = some dead := by
                simpa [← hdeadP] using
                  findLive_of_alive w hO.indexed name key g
                    (by simpa [hdeadP] using hdead) (by simpa [hdeadP] using hlive)
              have : id = dead := by rw [hfind0] at hliveD; cases hliveD; rfl
              exact hwho this
            have hextra : extra = 0 := by
              have hb0 := box_miss dead (w.st host).box name key hnot
              have hp0 := dropped_miss dead (w.st host).parked name key hmsg hnot
              simp only [extra, hb0, hp0]
            have htk' : ((setActor mid dead bumped).st id).tokens d = (w.st id).tokens d := by
              simpa [hwho] using htokOther id d hwho
            rw [hextra] at hbit
            have hbit' : (queuedFromKey w name key d : Int) =
                queuedFromKey (setActor mid dead bumped) name key d := by
              by_cases htd : tname host = d <;> simp [htd] at hbit ⊢ <;> exact hbit
            rw [htk', ← hbit', hbal]
        · intro name d hlifeC hmemC
          rw [hr] at hmemC ⊢
          have hlife0 : (w.st (InstId.core name)).life = .alive := by
            simpa [hlife] using hlifeC
          have hbal := hO.balance.1.2 name d hlife0 hmemC
          let st1 := fun i => if i = host then stripped else w.st i
          have howed2 : owed (setActor mid dead bumped).st d (InstId.core name) w.roster =
              owed st1 d (InstId.core name) w.roster := by
            refine owed_mail_eq _ _ _ _ w.roster ?_
            intro i _
            exact ⟨(hboxPark i).1, (hboxPark i).2⟩
          have hrep := owed_replace w.st d (InstId.core name) host stripped w.roster hO.nodup hhost
          by_cases hwho : InstId.core name = dead
          · have hslot : slot w.st d (InstId.core name) host =
                slot st1 d (InstId.core name) host + if tname host = d then n else 0 := by
              by_cases htd : tname host = d
              · have holdS : slot w.st d (InstId.core name) host = n := by
                  rw [hwho]; exact slot_outbound w.st dead host d htd
                have hnewS : slot st1 d (InstId.core name) host = 0 := by
                  rw [hwho]; exact strip_slot_self w.st dead host d htd
                simp [htd, holdS, hnewS]
              · have hslot0 : slot w.st d (InstId.core name) host = 0 := by
                  have hb0 : (tname host == d) = false := by simpa [beq_iff_eq] using htd
                  simp [slot, hb0]
                have hslot1 : slot st1 d (InstId.core name) host = 0 := by
                  have hb0 : (tname host == d) = false := by simpa [beq_iff_eq] using htd
                  simp [slot, st1, hb0]
                simp [htd, hslot0, hslot1]
            have htk := htokDead d
            rw [howed2]
            have hrep' : owed st1 d (InstId.core name) w.roster +
                slot w.st d (InstId.core name) host =
                owed w.st d (InstId.core name) w.roster +
                  slot st1 d (InstId.core name) host := by
              simpa [st1] using hrep
            have htk' : ((setActor mid dead bumped).st (InstId.core name)).tokens d =
                (w.st (InstId.core name)).tokens d +
                  (if tname host = d then (n : Int) else 0) := by
              rw [hwho]
              by_cases htd : tname host = d
              · simp [htd, htk]
              · have hflip : ¬ d = tname host := fun h => htd h.symm
                simp [htd, hflip, htk]
            have howed' : (owed st1 d (InstId.core name) w.roster : Int) +
                (if tname host = d then (n : Int) else 0) =
                (owed w.st d (InstId.core name) w.roster : Int) := by
              have hslotI : (slot w.st d (InstId.core name) host : Int) =
                  (slot st1 d (InstId.core name) host : Int) +
                    (if tname host = d then (n : Int) else 0) := by
                by_cases htd : tname host = d
                · have h := hslot
                  simp [htd] at h
                  have hcast := congrArg (fun k : Nat => (k : Int)) h
                  rw [Int.natCast_add] at hcast
                  simpa [htd] using hcast
                · have h := hslot
                  simp [htd] at h
                  simpa [htd] using congrArg (fun k : Nat => (k : Int)) h
              have hrepI : (owed st1 d (InstId.core name) w.roster : Int) +
                  (slot w.st d (InstId.core name) host : Int) =
                  (owed w.st d (InstId.core name) w.roster : Int) +
                    (slot st1 d (InstId.core name) host : Int) := by
                rw [← Int.natCast_add, ← Int.natCast_add, hrep']
              omega
            rw [htk']
            have hcomm : ((w.st (InstId.core name)).tokens d +
                (if tname host = d then (n : Int) else 0)) +
                (owed st1 d (InstId.core name) w.roster : Int) =
                (w.st (InstId.core name)).tokens d +
                  ((owed st1 d (InstId.core name) w.roster : Int) +
                    (if tname host = d then (n : Int) else 0)) := by
              ac_rfl
            rw [hcomm, howed', hbal]
          · have hslotEq := strip_slot_other w.st dead host (InstId.core name) d
              (by simpa using hwho)
            have htk' : ((setActor mid dead bumped).st (InstId.core name)).tokens d =
                (w.st (InstId.core name)).tokens d := by
              simpa [hwho] using htokOther (InstId.core name) d hwho
            rw [howed2, htk']
            have hrep' : owed st1 d (InstId.core name) w.roster +
                slot w.st d (InstId.core name) host =
                owed w.st d (InstId.core name) w.roster +
                  slot st1 d (InstId.core name) host := by
              simpa [st1] using hrep
            have hs : slot st1 d (InstId.core name) host =
                slot w.st d (InstId.core name) host := by
              simpa [st1] using hslotEq
            have howedEq : owed st1 d (InstId.core name) w.roster =
                owed w.st d (InstId.core name) w.roster := by
              omega
            rw [howedEq, hbal]
        · intro name key d hnone
          have hfindEq : findLive (setActor mid dead bumped) name key = findLive w name key := by
            have hs1 : stripped.life = (w.st host).life := by simp [stripped, stripSender]
            have hs2 : bumped.life = (mid.st dead).life := by simp [bumped, addTokens]
            have h1 := findLive_set_life w host stripped hs1 name key
            have h2 := findLive_set_life mid dead bumped hs2 name key
            simpa [mid] using h2.trans h1
          have hnone0 : findLive w name key = none := by rw [hfindEq] at hnone; exact hnone
          have hmsg : ∀ p ∈ (w.st host).parked, p.sender = p.msg.sender :=
            fun p hp => hO.parkMsg host p hp
          let extra :=
            (((w.st host).box.filter fun m => m.sender == dead).filter (keyPred name key)).length +
              (((w.st host).parked.filter fun p => p.sender == dead).filter
                fun p => keyPred name key p.msg).length
          have hnotB : (fun m : Msg => m.sender != dead) = fun m => !(m.sender == dead) := by
            funext m; simp [bne]
          have hnotP : (fun p : Parked => p.sender != dead) = fun p => !(p.sender == dead) := by
            funext p; simp [bne]
          have hsplitB := filter_count_split_msg (fun m => m.sender == dead)
            (keyPred name key) (w.st host).box
          have hsplitP := filter_count_split (fun p => p.sender == dead)
            (fun p => keyPred name key p.msg) (w.st host).parked
          have hdelta :
              ((w.st host).box.filter (keyPred name key)).length +
                ((w.st host).parked.filter fun p => keyPred name key p.msg).length =
              (stripped.box.filter (keyPred name key)).length +
                (stripped.parked.filter fun p => keyPred name key p.msg).length + extra := by
            have hboxS : stripped.box =
                (w.st host).box.filter fun m => !(m.sender == dead) := by
              simp [stripped, stripSender, hnotB]
            have hparkS : stripped.parked =
                (w.st host).parked.filter fun p => !(p.sender == dead) := by
              simp [stripped, stripSender, hnotP]
            rw [hboxS, hparkS, hsplitB, hsplitP]
            simp only [extra]
            omega
          have hq := queuedFromKey_replace w host stripped name key d extra hO.nodup hhost hdelta
          have hq2 : queuedFromKey (setActor mid dead bumped) name key d =
              queuedFromKey mid name key d := by
            refine queuedFromKey_set mid dead bumped ?_ ?_ name key d
            · simp [bumped, addTokens]
            · simp [bumped, addTokens]
          have hle : queuedFromKey (setActor mid dead bumped) name key d ≤
              queuedFromKey w name key d := by
            have hq' : queuedFromKey w name key d =
                queuedFromKey mid name key d + if tname host = d then extra else 0 := by
              simpa [mid] using hq
            rw [hq2, hq']
            omega
          have hold := hO.balance.2 name key d hnone0
          omega
      · intro s d hlive'
        have hlive0 : (w.st s).life = .alive := by rw [← hlife s]; exact hlive'
        have hph : ((setActor mid dead bumped).st s).phase = (w.st s).phase := by
          simpa [hw] using (forgetHost_stable w dead host s).1
        have hty : ((setActor mid dead bumped).st s).typestate = (w.st s).typestate := by
          simpa [hw] using (forgetHost_stable w dead host s).2.2.1
        have hth := tokenHold_phase I.desc (tname s) d _ _ hph hty
        have hold := hO.slack s d hlive0
        rw [hth]
        by_cases hsD : s = dead
        · rw [hsD] at hold ⊢
          have htk := htokDead d
          have hnn : (0 : Int) ≤ if d = tname host then (n : Int) else 0 := by
            by_cases hd : d = tname host <;> simp [hd]
          omega
        · rw [htokOther s d hsD]
          exact hold
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
      · intro hcr s d hs hdeadLife
        rw [hr] at hs ⊢
        have hcr0 : w.crashed = false := by simpa [hw, mid, setActor] using hcr
        have hdead0 : (w.st s).life ≠ .alive := by rw [← hlife s]; exact hdeadLife
        let st1 := fun i => if i = host then stripped else w.st i
        have howed1 : owed (setActor mid dead bumped).st d s w.roster = owed st1 d s w.roster := by
          refine owed_mail_eq _ _ _ _ w.roster ?_
          intro i _
          exact ⟨(hboxPark i).1, (hboxPark i).2⟩
        have hrep := owed_replace w.st d s host stripped w.roster hO.nodup hhost
        have hzero := hO.quiet hcr0 s d hs hdead0
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
      · intro hcr i hdeadL
        have hcr0 : w.crashed = false := by simpa [hw, mid, setActor] using hcr
        have hdead0 : (w.st i).life = .absent ∨ (w.st i).life = .dead := by
          rw [hlife i] at hdeadL
          exact hdeadL
        have hempty := hO.deadEmpty hcr0 i hdead0
        rw [hst i]
        by_cases hid : i = dead
        · rw [hid] at hempty
          simp [hid, bumped, addTokens, hmidDead]
          exact hempty
        · by_cases hih : i = host
          · rw [hih] at hempty
            simp [hih, ite_eq_right hself, stripped, stripSender, hempty]
          · simp [hid, hih, hempty]
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
      · exact ixFresh_copy I.desc w (setActor mid dead bumped) hO.ixFresh hr
          (fun n => by simpa [mid, setActor] using congrFun hix n)

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

theorem occ_forget (I : Impl) (w : World) (dead : InstId) (hO : OccInv I w)
    (hdead : dead ∈ w.roster) (hlive : (w.st dead).life = .alive) :
    OccInv I (forgetSender w dead) := by
  have hfold : ∀ (ids : List InstId) (w' : World), OccInv I w' → dead ∈ w'.roster →
      (w'.st dead).life = .alive → (∀ i ∈ ids, i ∈ w'.roster) →
      OccInv I (ids.foldl (fun w host => forgetHost w dead host) w') := by
    intro ids
    induction ids with
    | nil => intro w' hO' _ _ _; exact hO'
    | cons host ids ih =>
      intro w' hO' hdead' hlive' hids
      simp only [List.foldl_cons]
      have hO1 := occ_forgetHost I w' dead host hO' hdead' (hids host (List.Mem.head _)) hlive'
      have hr := forgetHost_roster w' dead host
      have hlive1 : ((forgetHost w' dead host).st dead).life = .alive := by
        rw [(forgetHost_stable w' dead host dead).2.1]
        exact hlive'
      exact ih (forgetHost w' dead host) hO1 (by simpa [hr] using hdead') hlive1
        fun i hi => by simpa [hr] using hids i (List.Mem.tail _ hi)
  exact hfold w.roster w hO hdead hlive fun i hi => hi

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

theorem forgetHost_rest (w : World) (dead host i : InstId) :
    ((forgetHost w dead host).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((forgetHost w dead host).st i).parent = (w.st i).parent := by
  unfold forgetHost
  split
  · exact ⟨rfl, rfl⟩
  · next hdiff =>
    have hne : host ≠ dead := by simpa [beq_iff_eq] using hdiff
    split
    · exact ⟨rfl, rfl⟩
    · by_cases hi : i = dead
      · rw [hi, setActor_self]
        have hclear : (setActor w host (stripSender dead (w.st host))).st dead = w.st dead := by
          rw [setActor_other _ host dead _ hne.symm]
        simp [addTokens, hclear]
      · by_cases hh : i = host
        · have hne' : i ≠ dead := by simpa [hh] using hne
          rw [setActor_other _ dead i _ hne', hh, setActor_self]
          simp [stripSender]
        · rw [setActor_other _ dead i _ hi, setActor_other _ host i _ hh]
          exact ⟨rfl, rfl⟩

theorem forget_rest (w : World) (dead i : InstId) :
    ((forgetSender w dead).st i).pendingTombstone = (w.st i).pendingTombstone ∧
      ((forgetSender w dead).st i).parent = (w.st i).parent := by
  unfold forgetSender
  suffices ∀ (ids : List InstId) (w0 : World),
      ((ids.foldl (fun w host => forgetHost w dead host) w0).st i).pendingTombstone =
        (w0.st i).pendingTombstone ∧
        ((ids.foldl (fun w host => forgetHost w dead host) w0).st i).parent =
          (w0.st i).parent from
    this w.roster w
  intro ids
  induction ids with
  | nil => intro w0; exact ⟨rfl, rfl⟩
  | cons host ids ih =>
    intro w0
    simp only [List.foldl_cons]
    have hstep := forgetHost_rest w0 dead host i
    have htail := ih (forgetHost w0 dead host)
    exact ⟨htail.1.trans hstep.1, htail.2.trans hstep.2⟩

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
    (hstamps : sameStamps (w1.st dead) (w2.st dead))
    (hpend : (w1.st dead).pendingTombstone = (w2.st dead).pendingTombstone)
    (hpar : (w1.st dead).parent = (w2.st dead).parent) (i : InstId) :
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
    · exact (forget_rest w1 dead dead).1.trans (hpend.trans (forget_rest w2 dead dead).1.symm)
    · exact (forget_rest w1 dead dead).2.trans (hpar.trans (forget_rest w2 dead dead).2.symm)
  · rw [setActor_other _ dead i _ hi, setActor_other _ dead i _ hi]
    exact h.1 i hi

/-- Killing one subtree member preserves outstanding credit. Outbound mail is
credited back before the member is removed, so a sibling's queue may shrink. -/
theorem occ_killOne (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (id : InstId) (hO : OccInv I w) (hS : SemInv I w)
    (hmem : isMember I.desc id sub key = true) (halive : (w.st id).life = .alive)
    (hcr : w.crashed = false) :
    OccInv I (killOne w I.desc id) := by
  have hroster := hO.aliveIn id halive
  let D := I.desc
  let base := readCells D w id
  have hObase := occ_same I w base hO (fun i => readCells_st D w id i) (read_roster D w id).1
    (read_roster D w id).2 (fun n => readCells_nextIx D w id n) (readCells_crashed D w id)
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
  have hcrB : base.crashed = false := (readCells_crashed D w id).trans hcr
  have hcrF : wF.crashed = false := by
    simpa [wF, failWaiters] using (failFold_crashed base id base.roster).trans hcrB
  have hDb := occ_drain_box I wF id ms hOF hmemF rfl hcrF
  have hparkB : ((drainBox wF id name ms).st id).parked = ps := by
    simpa [ps] using drain_park wF id name ms id
  have hmemD : id ∈ (drainBox wF id name ms).roster := by
    simpa [(frame_drain wF id name ms).2.1] using hmemF
  have hcrD : (drainBox wF id name ms).crashed = false := (kept_drain wF id name ms).2.trans hcrF
  have hDp := occ_drain_park I (drainBox wF id name ms) id ps hDb hmemD hparkB hmsg hcrD
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
  have hliveDr : (drained.st id).life = .alive := by
    have hliveF : (wF.st id).life = .alive := by
      have hb : (base.st id).life = (w.st id).life :=
        congrArg Actor.life (readCells_st D w id id)
      rw [failWaiters_life base id, hb]
      exact halive
    have hliveBox : ((drainBox wF id name ms).st id).life = .alive := by
      rw [(drain_life wF id name ms id).1]
      exact hliveF
    rw [(drainP_life (drainBox wF id name ms) id name ps id).1]
    exact hliveBox
  have hOf := occ_forget I drained id hDp hmemDr hliveDr
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
  have hOd := occ_die I forgotten id hOf hmemFg hboxFg hparkFg hbound
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
    have hpend0 : (drained.st id).pendingTombstone = (refunded.st id).pendingTombstone := by
      have hd := (actor_kept_drainP (drainBox wF id name ms) id name ps id).1.trans
        (actor_kept_drain wF id name ms id).1
      have hrw := (actor_kept_refundP (refundMsgs wF name ms) name ps id).1.trans
        (actor_kept_refund wF name ms id).1
      exact hd.trans hrw.symm
    have hpar0 : (drained.st id).parent = (refunded.st id).parent := by
      have hd := (actor_kept_drainP (drainBox wF id name ms) id name ps id).2.trans
        (actor_kept_drain wF id name ms id).2
      have hrw := (actor_kept_refundP (refundMsgs wF name ms) name ps id).2.trans
        (actor_kept_refund wF name ms id).2
      exact hd.trans hrw.symm
    have hclear := forget_clear_st drained refunded id hrSame hother
      (by simpa [name, ms, ps, drained, refunded] using hkept.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.2.1)
      (by simpa [name, ms, ps, drained, refunded] using hkept.2.2.2)
      (by simpa [name, ms, ps, drained, refunded] using hpend0)
      (by simpa [name, ms, ps, drained, refunded] using hpar0) i
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
  exact occ_same I died (killOne w D id) hOd hst hr hN hix (by
    have hdie : died.crashed = w.crashed := by
      simp only [died, setActor]
      have hfor : forgotten.crashed = drained.crashed := by
        simpa [forgotten] using forget_crashed drained id
      exact hfor.trans (((kept_drainP (drainBox wF id name ms) id name ps).2).trans
        (((kept_drain wF id name ms).2).trans
          (((by simpa [wF, failWaiters] using failFold_crashed base id base.roster :
              wF.crashed = base.crashed)).trans
            (readCells_crashed D w id))))
    exact (killOne_crashed w D id).trans hdie.symm)

/-- Crediting the live holder is `creditSender` on `budgetHolder`. -/
theorem refundMsgs_sem (I : Impl) (w : World) (name : String) (ms : List Msg) (hS : SemInv I w) :
    SemInv I (refundMsgs w name ms) := by
  induction ms generalizing w with
  | nil => simpa [refundMsgs] using hS
  | cons m ms ih =>
    simp only [refundMsgs, List.foldl_cons]
    exact ih _ (credit_sem I w name (budgetHolder w m.sender) hS)

theorem refundParked_sem (I : Impl) (w : World) (name : String) (ps : List Parked) (hS : SemInv I w) :
    SemInv I (refundParked w name ps) := by
  induction ps generalizing w with
  | nil => simpa [refundParked] using hS
  | cons p ps ih =>
    simp only [refundParked, List.foldl_cons]
    exact ih _ (credit_sem I w name (budgetHolder w p.msg.sender) hS)

/-- A waiter that fires runs `proceed`. Every other arm is the same world. -/
theorem failWaiter_sem (I : Impl) (w : World) (dead i : InstId) (hS : SemInv I w) :
    SemInv I (failWaiter w dead i) := by
  unfold failWaiter
  split
  · exact hS
  · next hskip =>
    have halive : (w.st i).life = .alive :=
      Classical.byContradiction fun hne => hskip (bne_iff_ne.mpr hne)
    cases hph : (w.st i).phase with
    | parked d b k =>
      cases b with
      | false =>
        by_cases hd : d = dead
        · simp [hph, hd]
          have hty : (w.st i).typestate = k.toState := by simpa [contTy, hph] using hS.cont i
          have hprog : effectsOk I.desc (tname i) (contAt k) k.rest = true := by
            simpa [programOk, hph] using hS.prog i
          exact sem_proceed I w i (w.st i) k hS rfl rfl hty hprog halive
        · simp [hph, hd]
          exact hS
      | true =>
        simp [hph]
        exact hS
    | idle =>
      simp [hph]
      exact hS
    | run _ =>
      simp [hph]
      exact hS
    | awaitReply _ _ =>
      simp [hph]
      exact hS
    | awaitEffect _ =>
      simp [hph]
      exact hS
    | awaitPeer _ =>
      simp [hph]
      exact hS
    | crashed =>
      simp [hph]
      exact hS

theorem failFold_sem (I : Impl) (w : World) (dead : InstId) (ids : List InstId) (hS : SemInv I w) :
    SemInv I (ids.foldl (fun w i => failWaiter w dead i) w) := by
  induction ids generalizing w with
  | nil => exact hS
  | cons i ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (failWaiter_sem I w dead i hS)

/-- Stripping one host's copy of `dead` keeps the semantic invariant: the host is
on the roster, and the returned tokens do not change `dead`'s phase. -/
theorem forgetHost_sem (I : Impl) (w : World) (dead host : InstId) (hS : SemInv I w)
    (hhost : host ∈ w.roster) : SemInv I (forgetHost w dead host) := by
  by_cases hself : (host == dead) = true
  · rw [forgetHost, ite_eq_left hself]
    exact hS
  · rw [forgetHost, ite_eq_right hself]
    by_cases hempty : (outboundCount dead (w.st host) == 0) = true
    · rw [ite_eq_left hempty]
      exact hS
    · rw [ite_eq_right hempty]
      let stripped := stripSender dead (w.st host)
      have hS1 :=
        sem_set I w host stripped hS rfl rfl (hS.cont host) (hS.prog host) (hS.waited host)
          (idleOff_same I w hS host stripped rfl rfl) (Or.inr hhost)
      exact sem_set I (setActor w host stripped) dead
        (addTokens ((setActor w host stripped).st dead) (tname host) (outboundCount dead (w.st host)))
        hS1 rfl rfl (hS1.cont dead) (hS1.prog dead) (hS1.waited dead)
        (idleOff_same I _ hS1 dead _ rfl rfl) (Or.inl rfl)

theorem forgetFold_sem (I : Impl) (dead : InstId) (ids : List InstId) (w : World) (hS : SemInv I w)
    (hsub : ∀ host ∈ ids, host ∈ w.roster) :
    SemInv I (ids.foldl (fun w host => forgetHost w dead host) w) := by
  induction ids generalizing w with
  | nil => exact hS
  | cons host ids ih =>
    simp only [List.foldl_cons]
    have hS1 := forgetHost_sem I w dead host hS (hsub host (List.Mem.head (a := host) ids))
    have hr := forgetHost_roster w dead host
    exact ih _ hS1 (fun i hi => by
      rw [hr]
      exact hsub i (List.Mem.tail host hi))

theorem forget_sem (I : Impl) (w : World) (dead : InstId) (hS : SemInv I w) :
    SemInv I (forgetSender w dead) := by
  simpa [forgetSender] using forgetFold_sem I dead w.roster w hS (fun _ h => h)

/-- `proceed` never produces a park, so a parked phase after `failWaiter` was already there. -/
theorem failWaiter_park_src (w : World) (dead i s dst : InstId) (c : Bool) (k : Cont)
    (h : ((failWaiter w dead i).st s).phase = .parked dst c k) :
    (w.st s).phase = .parked dst c k := by
  by_cases hs : s = i
  · rw [hs] at h ⊢
    unfold failWaiter at h
    split at h
    · exact h
    · cases hph : (w.st i).phase with
      | parked d b k0 =>
        cases b with
        | false =>
          by_cases hd : d = dead
          · have hb : (d == dead) = true := by simpa [beq_iff_eq] using hd
            simp only [hph, hb] at h
            rw [ite_true, setActor_self, proceed_resumed] at h
            cases hk : k0.rest with
            | nil =>
              simp only [resumed, hk] at h
              cases h
            | cons _ _ =>
              simp only [resumed, hk] at h
              cases h
          · have hb : (d == dead) = false := by
              cases hbeq : d == dead with
              | true => exact absurd (beq_iff_eq.mp hbeq) hd
              | false => rfl
            simp only [hph, hb] at h
            rw [ite_eq_right (by decide : ¬ false = true), hph] at h
            exact h
        | true =>
          simp only [hph] at h
          exact h
      | idle =>
        simp only [hph] at h
        exact h
      | run _ =>
        simp only [hph] at h
        exact h
      | awaitReply _ _ =>
        simp only [hph] at h
        exact h
      | awaitEffect _ =>
        simp only [hph] at h
        exact h
      | awaitPeer _ =>
        simp only [hph] at h
        exact h
      | crashed =>
        simp only [hph] at h
        exact h
  · rw [failWaiter_other w dead i s hs] at h
    exact h

theorem failFold_park_src (w : World) (dead s dst : InstId) (c : Bool) (k : Cont) (ids : List InstId)
    (h : ((ids.foldl (fun w i => failWaiter w dead i) w).st s).phase = .parked dst c k) :
    (w.st s).phase = .parked dst c k := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons i ids ih =>
    simp only [List.foldl_cons] at h
    exact failWaiter_park_src w dead i s dst c k (ih _ h)

theorem killOne_park_src (w : World) (D : Description) (id s dst : InstId) (c : Bool) (k : Cont)
    (hne : s ≠ id) (h : ((killOne w D id).st s).phase = .parked dst c k) :
    (w.st s).phase = .parked dst c k := by
  let w1 := readCells D w id
  have hst1 : w1.st s = w.st s := cellsSt D w id s
  let w2 := refundMsgs w1 (tname id) (w.st id).box
  have h2 := refundMsgs_rest w1 (tname id) (w.st id).box s
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have h3 := refundParked_rest w2 (tname id) (w.st id).parked s
  let w4 := failWaiters w3 id
  let w5 := forgetSender w4 id
  have hstab := forget_stable w4 id s
  have hbody : killOne w D id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, w1, w2, w3, w4, w5, failWaiters, forgetSender]
  rw [hbody, setActor_other _ _ _ _ hne] at h
  have h4 : (w4.st s).phase = .parked dst c k := by
    rw [← hstab.1]
    exact h
  have h3ph : (w3.st s).phase = .parked dst c k := by
    simpa [w4, failWaiters] using failFold_park_src w3 id s dst c k w3.roster h4
  rw [h3.1, h2.1] at h3ph
  rw [← congrArg (·.phase) hst1]
  exact h3ph

theorem killOne_sem (I : Impl) (w : World) (id : InstId) (hS : SemInv I w)
    (halive : (w.st id).life = .alive) : SemInv I (killOne w I.desc id) := by
  let base := readCells I.desc w id
  have hSb := cells_sem I w id hS
  let w2 := refundMsgs base (tname id) (w.st id).box
  have hS2 := refundMsgs_sem I base (tname id) (w.st id).box hSb
  let w3 := refundParked w2 (tname id) (w.st id).parked
  have hS3 := refundParked_sem I w2 (tname id) (w.st id).parked hS2
  let w4 := failWaiters w3 id
  have hS4 : SemInv I w4 := by simpa [w4, failWaiters] using failFold_sem I w3 id w3.roster hS3
  let w5 := forgetSender w4 id
  have hS5 := forget_sem I w4 id hS4
  have hmem : id ∈ w5.roster := by
    have h4r : w4.roster = w3.roster := by
      simpa [w4, failWaiters] using failWaiters_roster w3 id w3.roster
    have hr : w5.roster = w.roster :=
      (forget_roster w4 id).trans (h4r.trans
        ((refundParked_roster w2 (tname id) (w.st id).parked).trans
          ((refundMsgs_roster base (tname id) (w.st id).box).trans (cellsRoster I.desc w id))))
    rw [hr]
    exact hS.rostered id halive
  have hbody : killOne w I.desc id =
      setActor w5 id { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] } := by
    simp [killOne, base, w2, w3, w4, w5, failWaiters, forgetSender]
  exact hbody ▸ sem_seal I w5 id
    { w5.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
    hS5 rfl rfl rfl hmem

theorem killOne_mail (I : Impl) (w : World) (id : InstId) (hS : SemInv I w) (hM : MailInv w)
    (_halive : (w.st id).life = .alive) : MailInv (killOne w I.desc id) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro mb p hp
    by_cases hmb : mb = id
    · rw [hmb, (killOne_self w I.desc id).2.2.2.2] at hp
      cases hp
    · rcases killOne_parked_fate w I.desc id mb hmb with hsame | hfilter
      · have hp0 : p ∈ (w.st mb).parked := by
          rw [hsame] at hp
          exact hp
        by_cases hsend : p.sender = id
        · exact Or.inr (by rw [hsend]; exact (killOne_self w I.desc id).1)
        · rcases hM.fwd mb p hp0 with ⟨k, hph⟩ | hh
          · exact Or.inl ⟨k, killOne_keeps_park w I.desc id p.sender mb p.isCall k hsend hmb hph⟩
          · exact Or.inr (by rw [(killOne_other_rest w I.desc id p.sender hsend).2.2]; exact hh)
      · rw [hfilter] at hp
        have hp0 : p ∈ (w.st mb).parked := (List.mem_filter.mp hp).1
        have hsend : p.sender ≠ id := (bne_iff_ne).mp (List.mem_filter.mp hp).2
        rcases hM.fwd mb p hp0 with ⟨k, hph⟩ | hh
        · exact Or.inl ⟨k, killOne_keeps_park w I.desc id p.sender mb p.isCall k hsend hmb hph⟩
        · exact Or.inr (by rw [(killOne_other_rest w I.desc id p.sender hsend).2.2]; exact hh)
  · intro s dst c k hph
    by_cases hne : s = id
    · rw [hne, (killOne_self w I.desc id).2.1] at hph
      cases hph
    · have hprev := killOne_park_src w I.desc id s dst c k hne hph
      by_cases hdst : dst = id
      · cases c with
        | true => exact Or.inr ⟨rfl, by rw [hdst]; exact (killOne_self w I.desc id).1⟩
        | false =>
          have hl : (w.st s).life = .alive := Classical.byContradiction fun hnot => by
            rcases hS.idleOff s hnot with hi | hc
            · rw [hi] at hprev
              cases hprev
            · rw [hc] at hprev
              cases hprev
          have hprevId : (w.st s).phase = .parked id false k := by
            rw [← hdst]
            exact hprev
          have hres := killOne_resumes_plain w I.desc id s k hne (hS.rostered s hl) hl hprevId
          rw [hres] at hph
          cases hk : k.rest <;> simp [resumed, hk] at hph
      · rcases hM.bwd s dst c k hprev with ⟨p, hp, hsnd, hcall⟩ | ⟨hcall, hdead⟩
        · have hp' : p ∈ ((killOne w I.desc id).st dst).parked := by
            rcases killOne_parked_fate w I.desc id dst hdst with hsame | hfilter
            · rw [hsame]
              exact hp
            · rw [hfilter]
              exact List.mem_filter.mpr ⟨hp, bne_iff_ne.mpr (hsnd.symm ▸ hne)⟩
          exact Or.inl ⟨p, hp', hsnd, hcall⟩
        · exact Or.inr ⟨hcall, (killOne_other_rest w I.desc id dst hdst).2.2.trans hdead⟩
  · intro mb1 mb2 p1 p2 hp1 hp2 hsnd
    exact hM.uniq mb1 mb2 p1 p2 ((killOne_parked_sub w I.desc id mb1).mem hp1)
      ((killOne_parked_sub w I.desc id mb2).mem hp2) hsnd
  · intro mb
    exact (killOne_parked_sub w I.desc id mb).nodup (hM.once mb)

theorem killOne_slots (w : World) (D : Description) (id : InstId) (hSlots : OpenSlots w)
    (hmem : id ∈ w.roster) : OpenSlots (killOne w D id) := by
  intro i hnot
  rw [killOne_roster]
  by_cases hi : i = id
  · rw [hi]
    exact hmem
  · rw [(killOne_other_rest w D id i hi).2.2] at hnot
    exact hSlots i hnot

/-- Killing one live member preserves the three step invariants. A non-call parked
on the victim is resumed, so the cleared mailbox does not lose a `MailInv` backward
edge; a parked call stays and the dead target is the allowed exception. -/
theorem killOne_inv (I : Impl) (w : World) (_sub : String) (_key : Nat) (id : InstId)
    (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w)
    (_hmem : isMember I.desc id _sub _key = true) (halive : (w.st id).life = .alive) :
    SemInv I (killOne w I.desc id) ∧ MailInv (killOne w I.desc id) ∧
      OpenSlots (killOne w I.desc id) :=
  ⟨killOne_sem I w id hS halive, killOne_mail I w id hS hM halive,
    killOne_slots w I.desc id hSlots (hS.rostered id halive)⟩

theorem occ_killFold (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (ids : List InstId)     (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w)
    (hcr : w.crashed = false) :
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
      have hOcc := occ_killOne I hG w sub key id hO hS hparts.1 halive hcr
      have hcr1 : (killOne w I.desc id).crashed = false :=
        (killOne_crashed w I.desc id).trans hcr
      exact ih _ hOcc hInv.1 hInv.2.1 hInv.2.2 hcr1
    · exact ih _ hO hS hM hSlots hcr

theorem occ_kill (I : Impl) (hG : GraphOk I.desc) (w : World) (sub : String) (key : Nat)
    (hO : OccInv I w) (hS : SemInv I w) (hM : MailInv w) (hSlots : OpenSlots w)
    (hcr : w.crashed = false) :
    OccInv I (killSubtree w I.desc sub key) := by
  have hFold := occ_killFold I hG w sub key w.roster hO hS hM hSlots hcr
  have hMembers : OccInv I (killMembers w I.desc sub key) := by simpa [killMembers] using hFold
  exact occ_same I (killMembers w I.desc sub key) (killSubtree w I.desc sub key) hMembers
    (fun i => by simp [killSubtree])
    (by simp [killSubtree, killMembers_roster])
    (by simp [killSubtree, killMembers_N])
    (fun n => by simp [killSubtree, killMembers_nextIx]) rfl

theorem occ_exec (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World) (id : InstId)
    (k : Cont) (hO : OccInv I w) (hT : TyOk I.desc w) (hS : SemInv I w) (hM : MailInv w)
    (hSlots : OpenSlots w) (hph : (w.st id).phase = .run k) (hsender : (w.st id).life = .alive)
    (hbulk : bulkScopeOf I.desc (tname id) k.rest = true) (hcr : w.crashed = false) :
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
                (readCells_crashed I.desc w id)
              have hcontR : ∀ i, contTy (wR.st i) := by
                intro i
                have hs := readCells_st I.desc w id i
                exact (contTy_match _ _ (congrArg Actor.phase hs) (congrArg Actor.typestate hs)).mpr (hS.cont i)
              have hmemR : id ∈ wR.roster := by
                have hr := (read_roster I.desc w id).1
                simpa [wR, hr] using hmem
              have hst := readCells_st I.desc w id id
              have hcrR : wR.crashed = false := (readCells_crashed I.desc w id).trans hcr
              have hgot := occ_term_kill I wR id hOR hcontR hmemR
                (by simp [terminableB, ht, hparts.1])
                (by intro p hp; exact hmsg p (by simpa [wR, ← hst] using hp))
                hcrR
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
    (hbulk : ∀ k, (w.st id).phase = .run k → bulkScopeOf I.desc (tname id) k.rest = true)
    (hcr : w.crashed = false) :
    OccInv I w' := by
  by_cases hlive : (w.st id).life = .alive
  · simp [execHead, hlive] at h
    cases hphase : (w.st id).phase with
    | run k =>
      simp [hphase] at h
      cases h
      exact occ_exec I hL hG w id k hO hT hS hM hSlots hphase hlive (hbulk k hphase) hcr
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
    have h := ih (creditLive w dst m.sender)
    have c := credit_lists w dst (budgetHolder w m.sender) i
    exact ⟨h.1.trans c.1, h.2.trans c.2⟩

theorem refundP_lists (w : World) (dst : String) (ps : List Parked) (i : InstId) :
    ((refundParked w dst ps).st i).box = (w.st i).box ∧
      ((refundParked w dst ps).st i).parked = (w.st i).parked := by
  induction ps generalizing w with
  | nil => simp [refundParked]
  | cons p ps ih =>
    rw [refundParked, List.foldl_cons]
    have h := ih (creditLive w dst p.msg.sender)
    have c := credit_lists w dst (budgetHolder w p.msg.sender) i
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
