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

end Deadlock
