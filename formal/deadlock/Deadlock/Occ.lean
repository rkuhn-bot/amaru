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

end Deadlock
