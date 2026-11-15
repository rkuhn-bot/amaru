import Deadlock.Projects
import Deadlock.Safety

set_option autoImplicit false

namespace Deadlock

/-! Per-producer outstanding is the account already on each actor.
`owed` counts that sender's messages in bulk boxes and parked lists.
`tokens dst` is what that producer has not yet spent. Their sum is the
budget of the producer's template. While the producer is alive,
`tokens` covers the floor of the current typestate plus the bulk sends
still in the continuation, so outstanding is at most the debt of that
typestate. Lemma 1 sums those debts into `capBulk`, which makes the
park branch of a blocking send unreachable. -/

def contRest : Phase → List Eff
  | .run k => k.rest
  | .parked _ _ k => k.rest
  | .awaitReply _ k => k.rest
  | .awaitEffect k => k.rest
  | .awaitPeer k => k.rest
  | _ => []

def pending (a : Actor) (dst : String) : Nat := sendsTo dst (contRest a.phase)

def terminableName (D : Description) (name : String) : Prop :=
  ∃ t, templateOf D name = some t ∧ t.terminable = true

theorem sends_drop_bulk (dst d : String) (es : List Eff) (label : String) (n : Nat) (e : Eff)
    (h : e = .send d label n ∨ e = .trySend d label n ∨ e = .call d label n) :
    sendsTo dst (e :: es) = (if d == dst then 1 else 0) + sendsTo dst es := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem sends_drop_other (dst : String) (e : Eff) (es : List Eff)
    (h : ∀ d label n, e ≠ .send d label n ∧ e ≠ .trySend d label n ∧ e ≠ .call d label n) :
    sendsTo dst (e :: es) = sendsTo dst es := by
  cases e <;> simp [sendsTo] at h ⊢

theorem noBulk_sends (es : List Eff) (h : noBulkSend es = true) (dst : String) : sendsTo dst es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp [noBulkSend, sendsTo] at h ⊢ <;> exact ih h

theorem noBulk_tail (e : Eff) (es : List Eff) (h : noBulkSend (e :: es) = true) : noBulkSend es = true := by
  cases e <;> simp [noBulkSend] at h ⊢ <;> exact h

/-- Outstanding credit, queues, and the Lemma-1 promise that nothing is parked. -/
structure OccInv (I : Impl) (w : World) : Prop where
  nodup : w.roster.Nodup
  aliveIn : ∀ id, (w.st id).life = .alive → id ∈ w.roster
  indexed : ∀ t i, InstId.peer t i ∈ w.roster → i < w.nextIx t
  liveOne : ∀ t, (∃ tmpl, templateOf I.desc t = some tmpl ∧ tmpl.multiplicity = .one) →
    aliveCount w t ≤ 1
  livePeer : ∀ t, (∃ tmpl, templateOf I.desc t = some tmpl ∧ tmpl.multiplicity = .perPeer) →
    aliveCount w t ≤ w.N
  offEmpty : ∀ id, id ∉ w.roster → (w.st id).box = [] ∧ (w.st id).parked = []
  sentFrom : ∀ id m, m ∈ (w.st id).box → m.sender ∈ w.roster
  parkFrom : ∀ id p, p ∈ (w.st id).parked → p.sender ∈ w.roster
  parkMsg : ∀ id p, p ∈ (w.st id).parked → p.sender = p.msg.sender
  balance : ∀ s d, s ∈ w.roster →
    owed w.st d s w.roster + (w.st s).tokens d = budget I.desc (tname s) d
  slack : ∀ s d, s ∈ w.roster → (w.st s).life = .alive →
    floorState I.desc (tname s) (w.st s).typestate d + pending (w.st s) d ≤ (w.st s).tokens d
  still : ∀ s d, s ∈ w.roster → terminableName I.desc (tname s) → owed w.st d s w.roster = 0
  quiet : ∀ s d, s ∈ w.roster → (w.st s).life ≠ .alive → owed w.st d s w.roster = 0
  clear : ∀ id, l1 I.desc (tname id) = true → (w.st id).parked = []

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

theorem owed_one_le (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String)
    (s : InstId) (hs : s ∈ w.roster) :
    owed w.st dst s w.roster ≤
      if (w.st s).life = .alive then debt I.desc (tname s) (w.st s).typestate dst else 0 := by
  by_cases hl : (w.st s).life = .alive
  · simp [hl]
    have hS := h.slack s dst hs hl
    have hB := h.balance s dst hs
    cases ht : templateOf I.desc (tname s) with
    | none =>
      have hele := hT s hl
      simp [statesOf, ht, List.elem] at hele
    | some t =>
      have hele := hT s hl
      have hst : (w.st s).typestate ∈ t.states := by
        simpa [statesOf, ht, List.elem_iff] using hele
      have hF := floor_add_debt I.desc (tname s) (w.st s).typestate dst ⟨t, ht, hst⟩
      have hle := owed_le_debt _ _ _ _ _ _ hB hS hF
      omega
  · simp [hl]
    exact h.quiet s dst hs hl

theorem sumOwed_le_live (I : Impl) (w : World) (h : OccInv I w) (hT : TyOk I.desc w) (dst : String) :
    sumOwed w.st dst w.roster ≤ liveDebt I.desc w.st dst w.roster := by
  rw [liveDebt_sum]
  unfold sumOwed
  refine sum_le _ _ w.roster ?_
  intro s hs
  exact owed_one_le I w h hT dst s hs

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

/-- A Lemma-1 mailbox holds at most `capBulk` messages, counting the parked lane. -/
theorem l1_fit (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w) (hT : TyOk I.desc w)
    (id : InstId) (hl1 : l1 I.desc (tname id) = true) :
    (w.st id).box.length + (w.st id).parked.length ≤ capBulk I.desc w.N id := by
  by_cases hmem : id ∈ w.roster
  · have hmail := mail_le_owed w.st (tname id) id w.roster hO.nodup hmem rfl
      (fun m hm => hO.sentFrom id m hm) (fun p hp => hO.parkFrom id p hp)
    have hsum := sumOwed_le_live I w hO hT (tname id)
    have hlive := live_le_occ I hL w hO (tname id)
    have hcap := cap_of_l1 I.desc id w.N hl1
    unfold sumOwed at hsum
    exact Nat.le_trans hmail (Nat.le_trans hsum (Nat.le_trans hlive hcap))
  · have hempty := hO.offEmpty id hmem
    rw [hempty.1, hempty.2, List.length_nil, Nat.zero_add]
    exact Nat.zero_le _

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

/-- The park branch of `enqueueOrPark` is unreachable for a Lemma-1 mailbox.
The sender still has the send in its continuation, so its outstanding is
strictly below the typestate debt, and `clear` keeps the parked lane empty. -/
theorem l1_park_unreachable (I : Impl) (hL : LocalOk I) (w : World) (hO : OccInv I w)
    (hT : TyOk I.desc w) (sender dst : InstId) (hlive : (w.st dst).life = .alive)
    (hsend : sender ∈ w.roster) (hsender : (w.st sender).life = .alive)
    (hpend : 1 ≤ pending (w.st sender) (tname dst)) (hl1 : l1 I.desc (tname dst) = true) :
    (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst := by
  have hpark := hO.clear dst hl1
  have hmem : dst ∈ w.roster := hO.aliveIn dst hlive
  have hmail := mail_le_owed w.st (tname dst) dst w.roster hO.nodup hmem rfl
    (fun m hm => hO.sentFrom dst m hm) (fun p hp => hO.parkFrom dst p hp)
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
  have hsum : sumOwed w.st (tname dst) w.roster + 1 ≤ liveDebt I.desc w.st (tname dst) w.roster := by
    rw [liveDebt_sum]
    unfold sumOwed
    refine sum_one_slack _ _ w.roster sender hsend hO.nodup ?_ ?_
    · intro s hs
      exact owed_one_le I w hO hT (tname dst) s hs
    · simp only [hsender, ite_true]
      exact hdebt
  have hlive := live_le_occ I hL w hO (tname dst)
  have hcap := cap_of_l1 I.desc dst w.N hl1
  have hbox : (w.st dst).box.length + 1 ≤ capBulk I.desc w.N dst := by
    rw [hpark, List.length_nil, Nat.add_zero] at hmail
    exact Nat.le_trans (Nat.add_le_add_right hmail 1)
      (Nat.le_trans hsum (Nat.le_trans hlive hcap))
  refine ⟨hpark, ?_⟩
  exact Nat.lt_of_succ_le hbox

theorem name_lines (D : Description) (hG : GraphOk D) : nameFails D = [] := by
  have h := hG.struct
  unfold structLines at h
  exact append_nil_left (append_nil_left (append_nil_left (append_nil_left
    (append_nil_left (append_nil_left (append_nil_left (append_nil_left h)))))))

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

theorem init_roster (I : Impl) (N : Nat) : (initWorld I N).roster = coreRoster I.desc := by
  unfold initWorld
  simpa using fold_read_roster I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

theorem init_N (I : Impl) (N : Nat) : (initWorld I N).N = N := by
  unfold initWorld
  simpa using fold_read_N I.desc (coreRoster I.desc)
    { N := N, roster := coreRoster I.desc, nextIx := fun _ => 0,
      st := fun id => if (coreRoster I.desc).contains id then initActor I.desc id else absentActor,
      cell := fun _ _ => cleanCell, observed := fun _ _ => 0 }

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
    ((initWorld I N).st id).tokens d = budget I.desc (tname id) d := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [init_roster] using coreRoster_nodup I.desc hG
  · intro id hl
    rw [init_base_st] at hl
    simp only [List.contains_iff_mem] at hl
    by_cases hmem : id ∈ coreRoster I.desc
    · simpa [init_roster] using hmem
    · rw [ite_eq_right hmem] at hl
      simp [absentActor] at hl
  · intro template i hi
    have hmem : InstId.peer template i ∈ coreRoster I.desc := by simpa [init_roster] using hi
    have hcont := List.contains_iff_mem.mpr hmem
    rw [peer_not_roster] at hcont
    cases hcont
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
  · intro s d hs
    have hzero := owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster
      (fun id _ => init_box I N id)
    rw [hzero, Nat.zero_add]
    exact init_tokens I hG N s hs d
  · intro s d hs _hl
    have hph := init_phase I N s
    have hpend : pending ((initWorld I N).st s) d = 0 := by
      simp [pending, contRest, hph, sendsTo]
    rw [hpend, Nat.add_zero, init_tokens I hG N s hs]
    exact floor_le_budget I.desc (tname s) ((initWorld I N).st s).typestate d
  · intro s d hs _hterm
    exact owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster (fun id _ => init_box I N id)
  · intro s d hs _hdead
    exact owed_zero_of_empty (initWorld I N).st d s (initWorld I N).roster (fun id _ => init_box I N id)
  · intro id _hl1
    exact (init_box I N id).2

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

/-- Replacing one actor without touching its life, queues, or token vector.
The new typestate's floor plus the new continuation must still fit in the tokens. -/
theorem occ_set (I : Impl) (w : World) (id : InstId) (a : Actor) (hO : OccInv I w)
    (hlife : a.life = (w.st id).life) (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked)
    (htok : ∀ d, a.tokens d = (w.st id).tokens d)
    (hslack : ∀ d, a.life = .alive →
      floorState I.desc (tname id) a.typestate d + pending a d ≤ a.tokens d) :
    OccInv I (setActor w id a) := by
  have hst : (setActor w id a).st = fun i => if i = id then a else w.st i := rfl
  have hr : (setActor w id a).roster = w.roster := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro s d hs
    have howed := owed_same_queues w.st id a hbox hpark d s w.roster
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
      exact hslack d hl
    · have hl' : (w.st s).life = .alive := by
        rw [setActor_other w id s a hs'] at hl
        exact hl
      have hold := hO.slack s d hs hl'
      rw [setActor_other w id s a hs']
      exact hold
  · intro s d hs hterm
    have howed := owed_same_queues w.st id a hbox hpark d s w.roster
    rw [hr] at hs
    rw [hst, hr, howed]
    exact hO.still s d hs hterm
  · intro s d hs hdead
    have howed := owed_same_queues w.st id a hbox hpark d s w.roster
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

/-- `finish` only advances a wait. The typestate is already the continuation's
target, and the remaining sends do not grow. -/
theorem occ_finish (I : Impl) (w w' : World) (id : InstId) (hO : OccInv I w) (hS : SemInv I w)
    (h : finishWait w id = some w') : OccInv I w' := by
  unfold finishWait at h
  split at h
  · next k heq =>
    cases h
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, heq] using hS.cont id
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hmem := hO.aliveIn id (by rw [proceed_life] at hl; exact hl)
        have hold := hO.slack id d hmem (by rw [proceed_life] at hl; exact hl)
        have hty' := proceed_keeps_ty (w.st id) k hty
        have hpend := proceed_pending (w.st id) k d (Or.inl heq)
        rw [hty']
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Nat.le_trans (Nat.add_le_add_left hpend _) hold)
  · next k heq =>
    cases h
    have hty : (w.st id).typestate = k.toState := by simpa [contTy, heq] using hS.cont id
    let a := proceed (w.st id) k
    exact occ_set I w id a hO (proceed_life _ _) (proceed_box _ _) (proceed_parked _ _)
      (proceed_tokens _ _) (by
        intro d hl
        have hmem := hO.aliveIn id (by rw [proceed_life] at hl; exact hl)
        have hold := hO.slack id d hmem (by rw [proceed_life] at hl; exact hl)
        have hty' := proceed_keeps_ty (w.st id) k hty
        have hpend := proceed_pending (w.st id) k d (Or.inr heq)
        rw [hty']
        have htok := proceed_tokens (w.st id) k d
        rw [htok]
        exact Nat.le_trans (Nat.add_le_add_left hpend _) hold)
  · cases h

theorem occ_same (I : Impl) (w w' : World) (hO : OccInv I w) (hst : ∀ i, w'.st i = w.st i)
    (hr : w'.roster = w.roster) (hN : w'.N = w.N) (hix : ∀ n, w'.nextIx n = w.nextIx n) :
    OccInv I w' := by
  have hq : ∀ i ∈ w'.roster, (w'.st i).box = (w.st i).box ∧ (w'.st i).parked = (w.st i).parked := by
    intro i _
    rw [hst]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (append_nil_left (append_nil_left (append_nil_left h))))))

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
    | trySend d label n =>
      simp [effectsOk, sendsTo, Bool.and_eq_true] at hok ⊢
      have ⟨edge, he, _, _, hdst, _, _, _⟩ :=
        hasEdge_mem D template state d .trySend .nonBlocking label hok.1
      have hne : d ≠ dst := fun heq => hno edge he (by rw [← heq]; exact hdst)
      have hb : (d == dst) = false := by
        cases hbb : d == dst with
        | false => rfl
        | true => exact absurd ((beq_iff_eq).mp hbb) hne
      simp [hne]
      exact ih hok.2
    | call d label n =>
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
          parked := (w.st id).parked, tokens := (w.st id).tokens }
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
    (hclear : l1 I.desc (tname id) = true → a1.parked = []) :
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · rw [hother d hd sender, h0]
    · by_cases hd : d = tname id
      · subst hd
        have hown' := hown s
        simp [hss] at hown'
        rw [hown', h0]
      · rw [hother d hd s, h0]
  · intro s hl1
    by_cases hs : s = id
    · rw [hs] at hl1 ⊢
      rw [hparkF id]
      simp
      exact hclear hl1
    · rw [hparkF, if_neg hs]
      exact hO.clear s hl1

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

theorem sends_drop_le (d : String) (e : Eff) (es : List Eff) : sendsTo d es ≤ sendsTo d (e :: es) := by
  cases e <;> simp [sendsTo] <;> omega

theorem occ_keep (I : Impl) (w : World) (id : InstId) (a : Actor) (hO : OccInv I w)
    (hlife : a.life = (w.st id).life) (hbox : a.box = (w.st id).box) (hpark : a.parked = (w.st id).parked)
    (htok : ∀ d, a.tokens d = (w.st id).tokens d) (hty : a.typestate = (w.st id).typestate)
    (hpend : ∀ d, pending a d ≤ pending (w.st id) d) : OccInv I (setActor w id a) := by
  apply occ_set I w id a hO hlife hbox hpark htok
  intro d hl
  have hl0 : (w.st id).life = .alive := by rw [← hlife]; exact hl
  have hold := hO.slack id d (hO.aliveIn id hl0) hl0
  rw [hty]
  have htokd := htok d
  rw [htokd]
  exact Nat.le_trans (Nat.add_le_add_left (hpend d) _) hold

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
  by_cases hif : ((w.st dstId).life == .alive && (w.st dstId).prio.length < capPrio I.desc w.N dstId &&
      !((w.st dstId).prio.any (fun p => p.label == label))) = true
  · rw [if_pos hif]
    let wake : Msg := ⟨label, writer, none⟩
    have ha : ({ (w.st dstId) with prio := upsertPrio (w.st dstId).prio wake } : Actor) =
        { (w.st dstId) with prio := upsertPrio (w.st dstId).prio wake } := rfl
    exact occ_keep I w dstId ({ (w.st dstId) with prio := upsertPrio (w.st dstId).prio wake }) hO
      rfl rfl rfl (fun _ => rfl) rfl (fun _ => Nat.le_refl _)
  · rw [if_neg hif]
    exact hO

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
      · have htyC : (w.st caller).typestate = ck.toState := by
          simpa [contTy, hcall] using hS.cont caller
        have hO1 := occ_keep I w caller (proceed (w.st caller) ck) hO (proceed_life _ _)
          (proceed_box _ _) (proceed_parked _ _) (proceed_tokens _ _)
          (by
            unfold proceed
            cases hk : ck.rest <;> simp [hk, htyC])
          (by
            intro d
            unfold proceed pending
            cases hk : ck.rest <;> simp [contRest, hcall, hk])
        have hne : caller ≠ id := by
          intro hc
          rw [hc] at hcall
          rw [hcall] at hph
          cases hph
        have hstep := occ_advance I (setActor w caller (proceed (w.st caller) ck)) id k hO1
          (by rw [setActor_other w caller id _ (fun h => hne h.symm), hty])
          (by rw [setActor_other w caller id _ (fun h => hne h.symm), hph])
        simpa [hd] using hstep
      · simpa [hd] using occ_advance I w id k hO hty hph
    | idle => exact occ_advance I w id k hO hty hph
    | run _ => exact occ_advance I w id k hO hty hph
    | parked _ _ _ => exact occ_advance I w id k hO hty hph
    | awaitEffect _ => exact occ_advance I w id k hO hty hph
    | awaitPeer _ => exact occ_advance I w id k hO hty hph
    | crashed => exact occ_advance I w id k hO hty hph

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
    (hnot : ¬ terminableName I.desc (tname sender)) :
    OccInv I w' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · rw [hother d hd s, h0]
  · intro i hl1
    exact hclear i hl1

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
    (he : e = .send name label hint ∨ e = .call name label hint ∨ e = .trySend name label hint) :
    sendsTo d es + (if d = name then 1 else 0) ≤ sendsTo d (e :: es) := by
  rcases he with rfl | rfl | rfl <;> (
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

theorem enqueue_dead (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (h : (w.st dst).life ≠ .alive) :
    enqueueOrPark w D sender dst msg isCall k = setActor w sender (proceed (w.st sender) k) := by
  simp [enqueueOrPark, h]

theorem enqueue_room_self_call (w : World) (D : Description) (sender : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk D w.N sender) :
    enqueueOrPark w D sender sender msg true k =
      setActor w sender
        { chargeSender (w.st sender) (tname sender) with
          box := (chargeSender (w.st sender) (tname sender)).box ++ [msg],
          phase := .awaitReply sender k } := by
  simp [enqueueOrPark, hlive, hpark, hcap]

theorem enqueue_room_self_send (w : World) (D : Description) (sender : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk D w.N sender) :
    enqueueOrPark w D sender sender msg false k =
      setActor w sender
        (proceed { chargeSender (w.st sender) (tname sender) with
          box := (chargeSender (w.st sender) (tname sender)).box ++ [msg] } k) := by
  simp [enqueueOrPark, hlive, hpark, hcap]

theorem enqueue_room_other_call (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk D w.N dst) :
    enqueueOrPark w D sender dst msg true k =
      setActor (setActor w dst { (w.st dst) with box := (w.st dst).box ++ [msg] }) sender
        { chargeSender (w.st sender) (tname dst) with phase := .awaitReply dst k } := by
  simp [enqueueOrPark, hlive, hne, hpark, hcap]

theorem enqueue_room_other_send (w : World) (D : Description) (sender dst : InstId) (msg : Msg) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk D w.N dst) :
    enqueueOrPark w D sender dst msg false k =
      setActor (setActor w dst { (w.st dst) with box := (w.st dst).box ++ [msg] }) sender
        (proceed (chargeSender (w.st sender) (tname dst)) k) := by
  simp [enqueueOrPark, hlive, hne, hpark, hcap]

theorem enqueue_park_self (w : World) (D : Description) (sender : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont)
    (hlive : (w.st sender).life = .alive)
    (hroom : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk D w.N sender)) :
    enqueueOrPark w D sender sender msg isCall k =
      setActor w sender
        { chargeSender (w.st sender) (tname sender) with
          parked := (chargeSender (w.st sender) (tname sender)).parked ++
            [{ sender := sender, msg := msg, isCall := isCall }],
          phase := .parked sender isCall k } := by
  simp [enqueueOrPark, hlive, hroom]

theorem enqueue_park_other (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont)
    (hlive : (w.st dst).life = .alive) (hne : sender ≠ dst)
    (hroom : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst)) :
    enqueueOrPark w D sender dst msg isCall k =
      setActor (setActor w dst { (w.st dst) with parked := (w.st dst).parked ++
          [{ sender := sender, msg := msg, isCall := isCall }] }) sender
        { chargeSender (w.st sender) (tname dst) with phase := .parked dst isCall k } := by
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
    (he : e = .send name label hint ∨ e = .call name label hint ∨ e = .trySend name label hint)
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
    (hnot : ¬ terminableName I.desc (tname sender)) :
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

theorem occ_self_call (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ e = .call (tname sender) label hint)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ terminableName I.desc (tname sender))
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg true (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_room_self_call w I.desc sender msg (afterHead k) hsender hpark hcap]
  let aS : Actor :=
    { chargeSender (w.st sender) (tname sender) with
      box := (chargeSender (w.st sender) (tname sender)).box ++ [msg],
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
    exact owed_self_box w.st (tname sender) sender aS msg w.roster hO.nodup hmem rfl hmsg
      (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++ [msg] := by simpa [aS, hcb] using hm
    simp [List.mem_append, List.mem_singleton] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom sender m h
    | inr h => rw [h, hmsg]; exact hmem
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

theorem occ_self_send (I : Impl) (w : World) (sender : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ e = .call (tname sender) label hint ∨
      e = .trySend (tname sender) label hint)
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ terminableName I.desc (tname sender))
    (hpark : (w.st sender).parked = [])
    (hcap : (w.st sender).box.length < capBulk I.desc w.N sender) :
    OccInv I (enqueueOrPark w I.desc sender sender msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_room_self_send w I.desc sender msg (afterHead k) hsender hpark hcap]
  let base : Actor :=
    { chargeSender (w.st sender) (tname sender) with
      box := (chargeSender (w.st sender) (tname sender)).box ++ [msg] }
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
    exact owed_self_box w.st (tname sender) sender aS msg w.roster hO.nodup hmem rfl hmsg
      (by simp [aS, base, proceed_box, hcb]) (by simp [aS, base, proceed_parked, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box ++ [msg] := by simpa [aS, base, proceed_box, hcb] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom sender m h
    | inr h => rw [h, hmsg]; exact hmem
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
    (hnot : ¬ terminableName I.desc (tname sender)) :
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

theorem occ_self_park (I : Impl) (hL : LocalOk I) (w : World) (sender : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname sender) label hint ∨ e = .call (tname sender) label hint)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ terminableName I.desc (tname sender))
    (hroom : ¬ ((w.st sender).parked = [] ∧ (w.st sender).box.length < capBulk I.desc w.N sender)) :
    OccInv I (enqueueOrPark w I.desc sender sender msg isCall (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hpend1 : 1 ≤ pending (w.st sender) (tname sender) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname sender) := by
    have hS := hO.slack sender (tname sender) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname sender)
  rw [enqueue_park_self w I.desc sender msg isCall (afterHead k) hsender hroom]
  let entry : Parked := { sender := sender, msg := msg, isCall := isCall }
  let aS : Actor :=
    { chargeSender (w.st sender) (tname sender) with
      parked := (chargeSender (w.st sender) (tname sender)).parked ++ [entry],
      phase := .parked sender isCall (afterHead k) }
  suffices OccInv I (setActor w sender aS) by simpa [aS, entry] using this
  apply occ_one I w sender aS (tname sender) hO
  · simp [aS, hcl]
  · simp [aS, hcty]
  · intro d
    have htk : aS.tokens d = (chargeSender (w.st sender) (tname sender)).tokens d := by simp [aS]
    rw [htk]
    exact charge_tok (w.st sender) (tname sender) d htok1
  · intro d
    have hp : pending aS d = sendsTo d es := by
      apply pending_stored aS sender isCall (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inl (by simp [aS]))
    exact pending_drop (w.st sender) aS k e es (tname sender) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_self_park w.st (tname sender) sender aS entry w.roster hO.nodup hmem rfl rfl
      (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro d hd s
    exact owed_off w.st sender aS d s w.roster hO.nodup hmem (fun h => hd h.symm)
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hcp] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom sender p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked ++ [entry] := by simpa [aS, hcp] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkMsg sender p h
    | inr h => simp [h, entry, hmsg]
  · intro i hl1
    by_cases hs : i = sender
    · rw [hs] at hl1
      exact absurd (l1_park_unreachable I hL w hO hT sender sender hsender hmem hsender hpend1 hl1) hroom
    · simp [hs]
      exact hO.clear i hl1
  · exact hmem
  · exact hsender
  · exact hnot

theorem occ_other_call (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ e = .call (tname dst) label hint)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ terminableName I.desc (tname sender)) (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst) :
    OccInv I (enqueueOrPark w I.desc sender dst msg true (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_room_other_call w I.desc sender dst msg (afterHead k) hlive hne hpark hcap]
  let aD : Actor := { (w.st dst) with box := (w.st dst).box ++ [msg] }
  let aS : Actor :=
    { chargeSender (w.st sender) (tname dst) with phase := .awaitReply dst (afterHead k) }
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
    exact owed_other_box w.st (tname dst) sender dst aS aD msg w.roster hO.nodup hdst hmem hne rfl hmsg
      (by simp [aS, hcb]) (by simp [aS, hcp]) (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box ++ [msg] := by simpa [aD] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom dst m h
    | inr h => rw [h, hmsg]; exact hmem
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

theorem occ_other_send (I : Impl) (w : World) (sender dst : InstId) (msg : Msg) (k : Cont)
    (e : Eff) (es : List Eff) (label : String) (hint : Nat) (hO : OccInv I w)
    (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ e = .call (tname dst) label hint ∨
      e = .trySend (tname dst) label hint)
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ terminableName I.desc (tname sender))
    (hne : sender ≠ dst) (hlive : (w.st dst).life = .alive) (hpark : (w.st dst).parked = [])
    (hcap : (w.st dst).box.length < capBulk I.desc w.N dst) :
    OccInv I (enqueueOrPark w I.desc sender dst msg false (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_room_other_send w I.desc sender dst msg (afterHead k) hlive hne hpark hcap]
  let charged : Actor := chargeSender (w.st sender) (tname dst)
  let aD : Actor := { (w.st dst) with box := (w.st dst).box ++ [msg] }
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
    exact owed_other_box w.st (tname dst) sender dst aS aD msg w.roster hO.nodup hdst hmem hne rfl hmsg
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
    have hm' : m ∈ (w.st dst).box ++ [msg] := by simpa [aD] using hm
    simp [List.mem_append] at hm'
    cases hm' with
    | inl h => exact hO.sentFrom dst m h
    | inr h => rw [h, hmsg]; exact hmem
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

theorem occ_other_park (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k) (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ e = .call (tname dst) label hint)
    (hmsg : msg.sender = sender) (hsender : (w.st sender).life = .alive)
    (hnot : ¬ terminableName I.desc (tname sender)) (hne : sender ≠ dst)
    (hlive : (w.st dst).life = .alive)
    (hroom : ¬ ((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk I.desc w.N dst)) :
    OccInv I (enqueueOrPark w I.desc sender dst msg isCall (afterHead k)) := by
  have hmem := hO.aliveIn sender hsender
  have hdst := hO.aliveIn dst hlive
  have hpend1 : 1 ≤ pending (w.st sender) (tname dst) := by
    simp [pending, contRest, hph, hk]
    rcases he with rfl | rfl <;> simp [sendsTo]
  have htok1 : 1 ≤ (w.st sender).tokens (tname dst) := by
    have hS := hO.slack sender (tname dst) hmem hsender
    omega
  have ⟨hcl, hcty, _, hcb, hcp⟩ := charge_keeps (w.st sender) (tname dst)
  rw [enqueue_park_other w I.desc sender dst msg isCall (afterHead k) hlive hne hroom]
  let entry : Parked := { sender := sender, msg := msg, isCall := isCall }
  let aD : Actor := { (w.st dst) with parked := (w.st dst).parked ++ [entry] }
  let aS : Actor :=
    { chargeSender (w.st sender) (tname dst) with phase := .parked dst isCall (afterHead k) }
  suffices OccInv I (setActor (setActor w dst aD) sender aS) by simpa [aS, aD, entry] using this
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
      apply pending_stored aS dst isCall (afterHead k) es d
      · simp [afterHead, hk, List.tail_cons]
      · exact Or.inr (Or.inl (by simp [aS]))
    exact pending_drop (w.st sender) aS k e es (tname dst) label hint d hph hk
      (by
        rcases he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) hp
  · intro s
    exact owed_other_park w.st (tname dst) sender dst aS aD entry w.roster hO.nodup hdst hmem hne rfl rfl
      (by simp [aS, hcb]) (by simp [aS, hcp]) (by simp [aD]) (by simp [aD]) s
  · intro d hd s
    exact owed_other_skip w.st sender dst aS aD d w.roster hO.nodup hdst hmem hne
      (fun h => hd h.symm) (by simp [aS, hcb]) (by simp [aS, hcp]) s
  · intro m hm
    have hm' : m ∈ (w.st sender).box := by simpa [aS, hcb] using hm
    exact hO.sentFrom sender m hm'
  · intro m hm
    have hm' : m ∈ (w.st dst).box := by simpa [aD] using hm
    exact hO.sentFrom dst m hm'
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
    exact hO.parkFrom sender p hp'
  · intro p hp
    have hp' : p ∈ (w.st dst).parked ++ [entry] := by simpa [aD] using hp
    simp [List.mem_append] at hp'
    cases hp' with
    | inl h => exact hO.parkFrom dst p h
    | inr h => rw [h]; exact hmem
  · intro p hp
    have hp' : p ∈ (w.st sender).parked := by simpa [aS, hcp] using hp
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
      simp [aS, hcp]
      exact hO.clear sender hl1
    · by_cases hd : i = dst
      · rw [hd] at hl1
        exact absurd (l1_park_unreachable I hL w hO hT sender dst hlive hmem hsender hpend1 hl1) hroom
      · simp [hs, hd]
        exact hO.clear i hl1
  · exact hmem
  · exact hdst
  · exact hsender
  · exact hnot

/-- A blocking send or call. The target is charged for when it is alive.
On a Lemma-1 mailbox the park branch contradicts the occupancy invariant. -/
theorem occ_enqueue (I : Impl) (hL : LocalOk I) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (e : Eff) (es : List Eff) (label : String) (hint : Nat)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hph : (w.st sender).phase = .run k)
    (hk : k.rest = e :: es)
    (he : e = .send (tname dst) label hint ∨ e = .call (tname dst) label hint)
    (hmsg : msg.sender = sender) (hty : (w.st sender).typestate = k.toState)
    (hsender : (w.st sender).life = .alive) (hnot : ¬ terminableName I.desc (tname sender)) :
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
            hmsg hty hsender hnot hsame hlive hroom.1 hroom.2
        | true =>
          exact occ_other_call I w sender dst msg k e es label hint hO hph hk he hmsg hsender hnot
            hsame hlive hroom.1 hroom.2
    · by_cases hsame : sender = dst
      · subst hsame
        exact occ_self_park I hL w sender msg isCall k e es label hint hO hT hph hk he hmsg hsender hnot
          hroom
      · exact occ_other_park I hL w sender dst msg isCall k e es label hint hO hT hph hk he hmsg
          hsender hnot hsame hlive hroom
  · rw [enqueue_dead w I.desc sender dst msg isCall (afterHead k) hlive]
    exact occ_advance I w sender k hO hty hph

theorem occ_schedule (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) (label : String)
    (hO : OccInv I w) (ha : a = w.st id) (hph : a.phase = .run k) (hty : a.typestate = k.toState) :
    OccInv I
      (let cap := capPrio I.desc w.N id
      let msg : Msg := { label := label, sender := id, callFrom := none }
      let k' := afterHead k
      if a.prio.any (fun p => p.label == label) then setActor w id (proceed a k')
      else if a.prio.length < cap then
        setActor w id (proceed { a with prio := upsertPrio a.prio msg } k')
      else setActor w id { a with phase := .crashed }) := by
  let msg : Msg := { label := label, sender := id, callFrom := none }
  cases hb : a.prio.any (fun p => p.label == label) with
  | true =>
    simp [hb, ha]
    exact occ_advance I w id k hO (by simpa [ha] using hty) (by simpa [ha] using hph)
  | false =>
    by_cases hlen : a.prio.length < capPrio I.desc w.N id
    · simp [hb, hlen]
      let base : Actor := { a with prio := upsertPrio a.prio msg }
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

theorem countFrom_out (sender : InstId) : ∀ ms : List Msg, (∀ m ∈ ms, m.sender ≠ sender) → countFrom sender ms = 0
  | [], _ => rfl
  | m :: ms, h => by
    have hm : m.sender ≠ sender := h m (List.Mem.head _)
    have ht := countFrom_out sender ms (fun m' hm' => h m' (List.Mem.tail _ hm'))
    simp [countFrom, hm, ht]

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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          rw [howed, h0]
      · intro i hl1
        by_cases hi : i = pid
        · rw [hi]
          rw [hst pid]
          simp [hborn]
        · rw [hst i]
          simp [hi]
          exact hO.clear i hl1
    · simp [hif] at h

theorem try_fit_self (w : World) (id : InstId) (msg : Msg) (k : Cont) :
    let a' := chargeSender (w.st id) (tname id)
    let w1 := setActor w id a'
    let stored := { (w1.st id) with box := (w1.st id).box ++ [msg] }
    setActor (setActor w1 id stored) id (proceed ((setActor w1 id stored).st id) k) =
      setActor w id (proceed { a' with box := a'.box ++ [msg] } k) := by
  simp only [setActor]
  congr 1
  funext i
  by_cases hi : i = id <;> simp [hi]

theorem try_fit_other (w : World) (id dst : InstId) (msg : Msg) (k : Cont) (hne : id ≠ dst) :
    let a' := chargeSender (w.st id) (tname dst)
    let w1 := setActor w id a'
    let stored := { (w1.st dst) with box := (w1.st dst).box ++ [msg] }
    setActor (setActor w1 dst stored) id (proceed ((setActor w1 dst stored).st id) k) =
      setActor (setActor w dst { (w.st dst) with box := (w.st dst).box ++ [msg] }) id (proceed a' k) := by
  simp only [setActor, hne]
  congr 1
  funext i
  by_cases hi : i = id
  · simp [hi]
  · have hne' : dst ≠ id := fun h => hne h.symm
    simp [hi, hne']

/-- A `trySend` that fits spends one token and stores the message.
A miss, a dead target, or a full mailbox continues without a charge. -/
theorem occ_try (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (k : Cont)
    (dstName label : String) (hint : Nat) (es : List Eff) (hO : OccInv I w) (hT : TyOk I.desc w)
    (hph : (w.st id).phase = .run { k with rest := .trySend dstName label hint :: es })
    (hty : (w.st id).typestate = k.toState) (hsender : (w.st id).life = .alive)
    (hnot : ¬ terminableName I.desc (tname id)) :
    OccInv I (execRun I w id (w.st id) { k with rest := .trySend dstName label hint :: es }) := by
  let cont : Cont := { k with rest := .trySend dstName label hint :: es }
  have hph' : (w.st id).phase = .run cont := by simpa [cont] using hph
  have hty' : (w.st id).typestate = cont.toState := by simpa [cont] using hty
  simp [execRun, cont]
  cases hr : route w I.desc dstName hint with
  | none =>
    simp [hr]
    exact occ_advance I w id cont hO hty' hph'
  | some dst =>
    simp [hr]
    have hname := route_tname w I.desc dstName hint dst hr
    split
    · next hcond =>
      have hlive : (w.st dst).life = .alive := hcond.1.1
      have hpark : (w.st dst).parked = [] := hcond.1.2
      have hcap : (w.st dst).box.length < capBulk I.desc w.N dst := hcond.2
      let msg : Msg := { label := label, sender := id, callFrom := none }
      have he : Eff.trySend dstName label hint = Eff.trySend (tname dst) label hint := by rw [hname]
      by_cases hsame : id = dst
      · subst hsame
        have hocc := occ_self_send I w id msg cont (.trySend dstName label hint) es label hint hO
          hph' rfl (Or.inr (Or.inr he)) rfl hty' hsender hnot hpark hcap
        rw [enqueue_room_self_send w I.desc id msg (afterHead cont) hsender hpark hcap] at hocc
        simpa [msg, try_fit_self, cont] using hocc
      · have hocc := occ_other_send I w id dst msg cont (.trySend dstName label hint) es label hint hO
          hph' rfl (Or.inr (Or.inr he)) rfl hty' hsender hnot hsame hlive hpark hcap
        rw [enqueue_room_other_send w I.desc id dst msg (afterHead cont) hlive hsame hpark hcap] at hocc
        simpa [msg, try_fit_other w id dst msg (afterHead cont) hsame, cont] using hocc
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

theorem actor_fields (a b : Actor) (hl : a.life = b.life) (ht : a.typestate = b.typestate)
    (hp : a.phase = b.phase) (hb : a.box = b.box) (hpr : a.prio = b.prio) (hpk : a.parked = b.parked)
    (htk : ∀ d, a.tokens d = b.tokens d) : a = b := by
  cases a
  cases b
  cases hl
  cases ht
  cases hp
  cases hb
  cases hpr
  cases hpk
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
    (ho : w1.observed = w2.observed) : w1 = w2 := by
  cases w1
  cases w2
  cases hN
  cases hr
  cases hix
  cases hst
  cases hc
  cases ho
  rfl

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
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm) hst (hD.2.2.2.1.trans hC.2.2.2.1.symm)
    (hD.2.2.2.2.trans hC.2.2.2.2.symm)

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
  exact world_eq _ _ (hD.1.trans hC.1.symm) (hD.2.1.trans hC.2.1.symm)
    (hD.2.2.1.trans hC.2.2.1.symm) hst (hD.2.2.2.1.trans hC.2.2.2.1.symm)
    (hD.2.2.2.2.trans hC.2.2.2.2.symm)

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
    (hquiet : ∀ d, owed w.st d id w.roster = 0) :
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem call_tail (p : Parked) (ps : List Parked) (h : hasParkedCall (p :: ps) = false) :
    p.isCall = false ∧ ∀ q ∈ ps, q.isCall = false := by
  simp [hasParkedCall, List.any_cons, Bool.or_eq_false_iff] at h
  simpa [hasParkedCall, List.any_eq_false] using h

theorem occ_release (I : Impl) (w : World) (id : InstId) (ps : List Parked) (hO : OccInv I w)
    (hcont : ∀ i, contTy (w.st i)) (hnocall : hasParkedCall ps = false) :
    OccInv I (releaseParked w id ps) ∧ ∀ i, contTy ((releaseParked w id ps).st i) := by
  induction ps generalizing w with
  | nil =>
    simp [releaseParked]
    exact ⟨hO, hcont⟩
  | cons p ps ih =>
    have hct := call_tail p ps hnocall
    have htail : hasParkedCall ps = false := by simpa [hasParkedCall, List.any_eq_false] using hct.2
    simp [releaseParked, List.foldl_cons, hct.1]
    by_cases hself : p.sender = id
    · simp [hself]
      simpa [releaseParked] using ih w hO hcont htail
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
        ih (setActor w p.sender (resumeSender (w.st p.sender) false id)) hO1 hcont1 htail

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
    · funext d
      simpa using term_tok w id id d
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

theorem occ_term_kill (I : Impl) (w : World) (id : InstId) (hO : OccInv I w)
    (hcont : ∀ i, contTy (w.st i)) (hmem : id ∈ w.roster)
    (hterm : terminableName I.desc (tname id)) (hnocall : hasParkedCall (w.st id).parked = false)
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
    died = killed ∧ OccInv I (releaseParked killed id ps) := by
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
  have hquiet : ∀ d, owed drained.st d id drained.roster = 0 := fun d => hOp.still id d hmemD hterm
  have hOd := occ_die I drained id hOp hmemD hboxD hparkD hquiet
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
  have hrel := (occ_release I died id ps hOd hcontD hnocall).1
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
  exact ⟨heq, by simpa [heq] using hrel⟩

theorem occ_exec (I : Impl) (hL : LocalOk I) (w : World) (id : InstId) (k : Cont)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hS : SemInv I w)
    (hph : (w.st id).phase = .run k) (hsender : (w.st id).life = .alive)
    (hbulk : terminableName I.desc (tname id) → noBulkSend k.rest = true) :
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
        have hnot : ¬ terminableName I.desc (tname id) := by
          intro ht
          simp [noBulkSend] at hbulk
          exact absurd (hbulk ht) (by decide)
        simp [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr]
          exact occ_advance I w id ⟨.send dst label hint :: es, toState, replyTo⟩ hO hty hph
        | some dstId =>
          simp [hr]
          have hname := route_tname w I.desc dst hint dstId hr
          exact occ_enqueue I hL w id dstId ⟨label, id, none⟩ false
            ⟨.send dst label hint :: es, toState, replyTo⟩ (.send dst label hint) es label hint hO hT
            hph rfl (Or.inl (by simp [hname])) rfl hty hsender hnot
      | trySend dst label hint =>
        have hnot : ¬ terminableName I.desc (tname id) := by
          intro ht
          simp [noBulkSend] at hbulk
          exact absurd (hbulk ht) (by decide)
        exact occ_try I hL w id ⟨.trySend dst label hint :: es, toState, replyTo⟩ dst label hint es hO hT
          hph hty hsender hnot
      | call dst label hint =>
        have hnot : ¬ terminableName I.desc (tname id) := by
          intro ht
          simp [noBulkSend] at hbulk
          exact absurd (hbulk ht) (by decide)
        simp [execRun]
        cases hr : route w I.desc dst hint with
        | none =>
          simp [hr]
          exact occ_advance I w id ⟨.call dst label hint :: es, toState, replyTo⟩ hO hty hph
        | some dstId =>
          simp [hr]
          have hname := route_tname w I.desc dst hint dstId hr
          exact occ_enqueue I hL w id dstId ⟨label, id, some id⟩ true
            ⟨.call dst label hint :: es, toState, replyTo⟩ (.call dst label hint) es label hint hO hT
            hph rfl (Or.inr (by simp [hname])) rfl hty hsender hnot
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
          by_cases hkill : t.terminable = true ∧ hasParkedCall (w.st id).parked = false
          · simp [hkill]
            have hterm : terminableName I.desc (tname id) := ⟨t, ht, hkill.1⟩
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
            have hgot := occ_term_kill I wR id hOR hcontR hmemR hterm
              (by simpa [wR, hst] using hkill.2)
              (by intro p hp; exact hmsg p (by simpa [wR, ← hst] using hp))
            rw [← hst]
            simpa [wR] using hgot.2
          · simp [hkill]
            exact hO

theorem occ_head (I : Impl) (hL : LocalOk I) (w w' : World) (id : InstId)
    (hO : OccInv I w) (hT : TyOk I.desc w) (hS : SemInv I w)
    (h : execHead I w id = some w')
    (hbulk : ∀ k, (w.st id).phase = .run k →
      terminableName I.desc (tname id) → noBulkSend k.rest = true) :
    OccInv I w' := by
  by_cases hlive : (w.st id).life = .alive
  · simp [execHead, hlive] at h
    cases hphase : (w.st id).phase with
    | run k =>
      simp [hphase] at h
      cases h
      exact occ_exec I hL w id k hO hT hS hphase hlive (hbulk k hphase)
    | idle => simp [hphase] at h
    | parked _ _ _ => simp [hphase] at h
    | awaitReply _ _ => simp [hphase] at h
    | awaitEffect _ => simp [hphase] at h
    | awaitPeer _ => simp [hphase] at h
    | crashed => simp [hphase] at h
  · simp [execHead, hlive] at h

end Deadlock

