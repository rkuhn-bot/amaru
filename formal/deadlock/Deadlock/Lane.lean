/-
A Lemma-1 mailbox has room for one more message from a sender that still holds
a token, so the parked lane stays empty.

`popFactor` is `N` for a per-peer template and `1` for a core. The sum of those
factors times each template's budget fits in `totalOcc.eval N`, which Lemma 1
puts under `capBulk`.
-/
import Deadlock.Birth
import Deadlock.Occ

set_option autoImplicit false

namespace Deadlock

def popFactor (n : Nat) (t : Template) : Nat :=
  if t.multiplicity == .perPeer then n else 1

theorem factor_le (t : Template) (occ : Affine) (n : Nat) (hn : 1 ≤ n)
    (ha : t.multiplicity = .one → occ.a = 0) (hb : t.multiplicity = .perPeer → occ.b = 0) :
    popFactor n t * perInstance t.multiplicity occ ≤ occ.eval n := by
  cases hm : t.multiplicity with
  | one =>
    have h0 := ha hm
    have hne : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
    simp [popFactor, hm, hne, perInstance, Affine.eval, h0, Nat.one_mul]
  | perPeer =>
    have h0 := hb hm
    have hbeq : (Multiplicity.perPeer == Multiplicity.perPeer) = true := by decide
    simp [popFactor, hm, hbeq, perInstance, Affine.eval, h0, Nat.mul_comm]

theorem src_factor_go (I : Impl) (hL : LocalOk I) (dst name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (n : Nat) (hn : 1 ≤ n) :
    ∀ es, (∀ e ∈ es, e ∈ I.desc.edges) →
      popFactor n t * srcFold I.desc dst name es ≤ evalSrc dst name n es := by
  intro es hes
  induction es with
  | nil => simp [srcFold, evalSrc]
  | cons e es ih =>
    have ih' := ih (fun e' he' => hes e' (List.Mem.tail _ he'))
    by_cases hhit : e.dst = dst ∧ e.src = name
    · rcases hhit with ⟨hd, hs⟩
      have hdb : (e.dst == dst) = true := by simpa [beq_iff_eq] using hd
      have hsb : (e.src == name) = true := by simpa [beq_iff_eq] using hs
      obtain ⟨t', ht', ha, hb⟩ := occShape_edge I hL e (hes e (List.Mem.head _))
      have htname : templateOf I.desc e.src = some t := by simpa [hs] using ht
      have hteq : t' = t := by
        injection ht'.symm.trans htname
      rw [hteq] at ha hb
      have hinst : edgeInst I.desc e = perInstance t.multiplicity e.occupancy := by
        simp [edgeInst, htname]
      have hedge := factor_le t e.occupancy n hn ha hb
      have hmul := Nat.mul_add (popFactor n t) (edgeInst I.desc e) (srcFold I.desc dst name es)
      have hboth : (e.dst == dst && e.src == name) = true := by simp [hdb, hsb]
      simp [srcFold, evalSrc, hboth]
      rw [hmul]
      exact Nat.add_le_add (by simpa [hinst] using hedge) ih'
    · have hiff : ¬ ((e.dst == dst) = true ∧ (e.src == name) = true) := by
        intro hboth
        exact hhit ⟨by simpa [beq_iff_eq] using hboth.1, by simpa [beq_iff_eq] using hboth.2⟩
      cases hdb : e.dst == dst <;> cases hsb : e.src == name
      · simp [srcFold, evalSrc, hdb, hsb, ih']
      · simp [srcFold, evalSrc, hdb, hsb, ih']
      · simp [srcFold, evalSrc, hdb, hsb, ih']
      · exact absurd ⟨hdb, hsb⟩ hiff

def evalAllow (dst : String) (n : Nat) (banned : List String) : List Edge → Nat
  | [] => 0
  | e :: es =>
    (if e.dst == dst && allowed banned e.src then e.occupancy.eval n else 0) +
      evalAllow dst n banned es

theorem allowed_head (name : String) (banned : List String) :
    allowed (name :: banned) name = false := by
  simp [allowed, List.elem_iff, List.mem_cons]

theorem allowed_skip (a b : String) (banned : List String) (hne : a ≠ b)
    (h : allowed banned b = true) : allowed (a :: banned) b = true := by
  simp [allowed, List.mem_cons] at h ⊢
  exact ⟨fun heq => hne heq.symm, h⟩

theorem eval_split (dst name : String) (banned : List String) (n : Nat)
    (h : allowed banned name = true) :
    ∀ es, evalAllow dst n banned es =
      evalSrc dst name n es + evalAllow dst n (name :: banned) es := by
  intro es
  induction es with
  | nil => simp [evalAllow, evalSrc]
  | cons e es ih =>
    cases hdb : e.dst == dst <;> cases hsb : e.src == name
    · simp [evalAllow, evalSrc, hdb, hsb, ih]
    · have hname : e.src = name := by simpa [beq_iff_eq] using hsb
      have hok : allowed banned e.src = true := by simpa [hname] using h
      have hban : allowed (name :: banned) e.src = false := by
        simpa [hname] using allowed_head name banned
      simp [evalAllow, evalSrc, hdb, hsb, hok, hban, ih]
    · have hne : e.src ≠ name := by simpa [beq_iff_eq] using hsb
      have hiff : e.src ∈ name :: banned ↔ e.src ∈ banned := by
        simp [List.mem_cons, hne]
      have hallow : allowed (name :: banned) e.src = allowed banned e.src := by
        simp [allowed, List.elem_iff, hiff]
      simp [evalAllow, evalSrc, hdb, hsb, hallow, ih]
      omega
    · have hname : e.src = name := by simpa [beq_iff_eq] using hsb
      have hok : allowed banned e.src = true := by simpa [hname] using h
      have hban : allowed (name :: banned) e.src = false := by
        simpa [hname] using allowed_head name banned
      simp [evalAllow, evalSrc, hdb, hsb, hok, hban, ih]
      omega

theorem allowed_nil (src : String) : allowed [] src = true := by
  simp [allowed, List.elem]

theorem evalAllow_dst (dst : String) (n : Nat) :
    ∀ es, evalAllow dst n [] es = evalDst dst n es := by
  intro es
  induction es with
  | nil => simp [evalAllow, evalDst]
  | cons e es ih =>
    have hallow : allowed [] e.src = true := allowed_nil e.src
    simp [evalAllow, evalDst, hallow, ih]

def nameCover (D : Description) (dst : String) (n : Nat) : List String → Nat
  | [] => 0
  | name :: names =>
    (match templateOf D name with
      | none => 0
      | some t => popFactor n t * budget D name dst) +
      nameCover D dst n names

theorem cover_go (I : Impl) (hL : LocalOk I) (dst : String) (n : Nat) (hn : 1 ≤ n) :
    ∀ (names : List String) (banned : List String),
      names.Nodup → (∀ name ∈ names, allowed banned name = true) →
        (∀ name ∈ names, ∃ t, templateOf I.desc name = some t) →
          nameCover I.desc dst n names ≤ evalAllow dst n banned I.desc.edges := by
  intro names
  induction names with
  | nil =>
    intro _ _ _ _
    simp [nameCover]
  | cons name names ih =>
    intro banned hnd hallow hex
    have hcons := (List.nodup_cons).mp hnd
    have ⟨t, ht⟩ := hex name (List.Mem.head _)
    have hbud := budget_le_srcFold I.desc name dst
    have hsrc := src_factor_go I hL dst name t ht n hn I.desc.edges (fun _ h => h)
    have hfac : popFactor n t * budget I.desc name dst ≤ evalSrc dst name n I.desc.edges :=
      Nat.le_trans (Nat.mul_le_mul_left _ hbud) hsrc
    have hsplit := eval_split dst name banned n (hallow name (List.Mem.head _)) I.desc.edges
    have htailAllow : ∀ name' ∈ names, allowed (name :: banned) name' = true := by
      intro name' hmem
      have hdiff : name' ≠ name := by
        intro hsame
        exact hcons.1 (by simpa [hsame] using hmem)
      have hne : name ≠ name' := fun hsame => hdiff hsame.symm
      exact allowed_skip name name' banned hne (hallow name' (List.Mem.tail _ hmem))
    have htail := ih (name :: banned) hcons.2 htailAllow
      (fun name' hmem => hex name' (List.Mem.tail _ hmem))
    simp only [nameCover, ht]
    rw [hsplit]
    exact Nat.add_le_add hfac htail

theorem name_cover_le (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (dst : String) (n : Nat)
    (hn : 1 ≤ n) :
    nameCover I.desc dst n (I.desc.templates.map (·.name)) ≤ (totalOcc I.desc dst).eval n := by
  have hnd := birth_names I.desc hG
  have hself : ∀ name ∈ I.desc.templates.map (·.name), ∃ t, templateOf I.desc name = some t := by
    intro name hmem
    obtain ⟨t, ht, hname⟩ := List.mem_map.mp hmem
    refine ⟨t, ?_⟩
    simpa [templateOf, hname] using birth_find_named I.desc.templates t ht hnd
  have hle := cover_go I hL dst n hn (I.desc.templates.map (·.name)) [] hnd
    (fun name _ => allowed_nil name) hself
  simpa [evalAllow_dst, evalDst_total] using hle

theorem factor_pos (t : Template) (n : Nat) (hn : 1 ≤ n) : 1 ≤ popFactor n t := by
  cases hm : t.multiplicity with
  | one =>
    have hne : (Multiplicity.one == Multiplicity.perPeer) = false := by decide
    simp [popFactor, hm, hne]
  | perPeer =>
    have hbeq : (Multiplicity.perPeer == Multiplicity.perPeer) = true := by decide
    simp [popFactor, hm, hbeq, hn]

theorem budget_le_pop (D : Description) (name dst : String) (t : Template) (n : Nat)
    (ht : templateOf D name = some t) (hn : 1 ≤ n) :
    budget D name dst ≤ popFactor n t * budget D name dst := by
  have hpos := factor_pos t n hn
  have hmul : popFactor n t * budget D name dst ≥ 1 * budget D name dst :=
    Nat.mul_le_mul_right _ hpos
  simpa [Nat.one_mul] using hmul

def fromName (name : String) (m : Msg) : Bool :=
  match m.sender with
  | .peer n _ _ => n == name
  | .core _ => false

def nameLen (name : String) (ms : List Msg) : Nat :=
  (ms.filter (fromName name)).length

def sumName (names : List String) (ms : List Msg) : Nat :=
  names.foldl (fun acc name => acc + nameLen name ms) 0

def sumBudget (D : Description) (dst : String) : List String → Nat
  | [] => 0
  | name :: names => budget D name dst + sumBudget D dst names

theorem nameLen_yes (name : String) (m : Msg) (ms : List Msg) (h : fromName name m = true) :
    nameLen name (m :: ms) = nameLen name ms + 1 := by
  simp [nameLen, List.filter, h, Nat.add_comm]

theorem nameLen_no (name : String) (m : Msg) (ms : List Msg) (h : fromName name m = false) :
    nameLen name (m :: ms) = nameLen name ms := by
  simp [nameLen, List.filter, h]

theorem sumName_nil (ms : List Msg) : sumName [] ms = 0 := by
  simp [sumName]

theorem sumName_acc (names : List String) (ms : List Msg) :
    ∀ acc, names.foldl (fun n name => n + nameLen name ms) acc =
      acc + names.foldl (fun n name => n + nameLen name ms) 0 := by
  intro acc
  induction names generalizing acc with
  | nil => simp
  | cons name names ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + nameLen name ms), ih (nameLen name ms)]
    omega

theorem sumName_cons (name : String) (names : List String) (ms : List Msg) :
    sumName (name :: names) ms = nameLen name ms + sumName names ms := by
  simpa [sumName] using sumName_acc names ms (nameLen name ms)

theorem sumName_skip (names : List String) (m : Msg) (ms : List Msg)
    (hno : ∀ name ∈ names, fromName name m = false) :
    sumName names (m :: ms) = sumName names ms := by
  induction names with
  | nil => simp [sumName]
  | cons name names ih =>
    rw [sumName_cons, sumName_cons, nameLen_no name m ms (hno name (List.Mem.head _))]
    rw [ih (fun name' hmem => hno name' (List.Mem.tail _ hmem))]

theorem sumName_step (names : List String) (name : String) (m : Msg) (ms : List Msg)
    (hmem : name ∈ names) (hnd : names.Nodup) (hyes : fromName name m = true)
    (hno : ∀ name' ∈ names, name' ≠ name → fromName name' m = false) :
    sumName names (m :: ms) = sumName names ms + 1 := by
  induction names with
  | nil => cases hmem
  | cons head tail ih =>
    have hcons := (List.nodup_cons).mp hnd
    rcases List.mem_cons.mp hmem with rfl | htail
    · rw [sumName_cons, sumName_cons, nameLen_yes name m ms hyes]
      rw [sumName_skip tail m ms (fun name' hmem' =>
        hno name' (List.Mem.tail _ hmem') (fun hsame => hcons.1 (by simpa [hsame] using hmem')))]
      omega
    · have hhead : fromName head m = false :=
        hno head (List.Mem.head _) (fun hsame => hcons.1 (by simpa [hsame] using htail))
      rw [sumName_cons, sumName_cons, nameLen_no head m ms hhead]
      rw [ih htail hcons.2 (fun name' hmem' hne => hno name' (List.Mem.tail _ hmem') hne)]
      omega

theorem length_le_names (names : List String) (ms : List Msg) (hnd : names.Nodup)
    (hmem : ∀ m ∈ ms, ∃ name ∈ names, fromName name m = true)
    (hno : ∀ m ∈ ms, ∀ name' ∈ names, ∀ name ∈ names, fromName name m = true →
      name' ≠ name → fromName name' m = false) :
    ms.length ≤ sumName names ms := by
  induction ms with
  | nil => simp [sumName]
  | cons m ms ih =>
    obtain ⟨name, hname, hyes⟩ := hmem m (List.Mem.head _)
    have hstep := sumName_step names name m ms hname hnd hyes
      (fun name' hmem' hne => hno m (List.Mem.head _) name' hmem' name hname hyes hne)
    have htail := ih
      (fun m' hm' => hmem m' (List.Mem.tail _ hm'))
      (fun m' hm' => hno m' (List.Mem.tail _ hm'))
    have hlen : (m :: ms).length = ms.length + 1 := by simp
    rw [hstep, hlen]
    exact Nat.add_le_add_right htail 1

theorem sumBudget_cons (D : Description) (dst name : String) (names : List String) :
    sumBudget D dst (name :: names) = budget D name dst + sumBudget D dst names := rfl

theorem sumName_le_budget (D : Description) (dst : String) (names : List String) (ms : List Msg)
    (hle : ∀ name ∈ names, nameLen name ms ≤ budget D name dst) :
    sumName names ms ≤ sumBudget D dst names := by
  induction names with
  | nil => simp [sumName, sumBudget]
  | cons name names ih =>
    rw [sumName_cons, sumBudget_cons]
    exact Nat.add_le_add (hle name (List.Mem.head _))
      (ih (fun name' hmem => hle name' (List.Mem.tail _ hmem)))

theorem sumName_slack (D : Description) (dst : String) (names : List String) (ms : List Msg)
    (s : String) (hs : s ∈ names) (hnd : names.Nodup)
    (hle : ∀ name ∈ names, nameLen name ms ≤ budget D name dst)
    (hextra : nameLen s ms + 1 ≤ budget D s dst) :
    sumName names ms + 1 ≤ sumBudget D dst names := by
  induction names with
  | nil => cases hs
  | cons name names ih =>
    have hcons := (List.nodup_cons).mp hnd
    rw [sumName_cons, sumBudget_cons]
    rcases List.mem_cons.mp hs with rfl | htail
    · have htail := sumName_le_budget D dst names ms
        (fun name' hmem => hle name' (List.Mem.tail _ hmem))
      omega
    · have ih' := ih htail hcons.2 (fun name' hmem => hle name' (List.Mem.tail _ hmem))
      have hhead := hle name (List.Mem.head _)
      omega

theorem sumBudget_le_cover (D : Description) (dst : String) (n : Nat) (hn : 1 ≤ n) :
    ∀ names, (∀ name ∈ names, ∃ t, templateOf D name = some t) →
      sumBudget D dst names ≤ nameCover D dst n names := by
  intro names hself
  induction names with
  | nil => simp [sumBudget, nameCover]
  | cons name names ih =>
    obtain ⟨t, ht⟩ := hself name (List.Mem.head _)
    rw [sumBudget_cons]
    have hpop := budget_le_pop D name dst t n ht hn
    have htail := ih (fun name' hmem => hself name' (List.Mem.tail _ hmem))
    simp [nameCover, ht]
    exact Nat.add_le_add hpop htail

/-- A keyed host accepts only a peer of its own key. -/
theorem keyed_peer (D : Description) (w : World) (host : InstId) (k : Nat) (m : Msg)
    (hk : peerKey host = some k) (hok : queueOk D w m.sender host) :
    ∃ name gen, m.sender = InstId.peer name k gen := by
  cases host with
  | core _ => simp [peerKey] at hk
  | peer _ hkey _ =>
    simp [peerKey] at hk
    cases hk
    cases hsend : m.sender with
    | core _ => simp [queueOk, keyAgrees, openHost, peerKey, hsend] at hok
    | peer n key g =>
      simp [queueOk, keyAgrees, openHost, peerKey, hsend] at hok
      cases hok
      exact ⟨n, g, rfl⟩

theorem key_filter_len (name : String) (key : Nat) :
    ∀ (ms : List Msg), (ms.filter (keyPred name key)).length =
      (ms.filter (fun m =>
        match m.sender with
        | .peer s k _ => s == name && k == key
        | .core _ => false)).length := by
  intro ms
  induction ms with
  | nil => simp
  | cons m ms ih =>
    cases hm : m.sender with
    | core _ => simp [keyPred, List.filter, hm, ih]
    | peer n k g =>
      cases hb : (n == name && k == key) <;> simp [keyPred, List.filter, hm, hb, ih]

theorem fold_ge_acc (dst : String) (box park : InstId → Nat) :
    ∀ (ids : List InstId) (acc : Nat),
      acc ≤ ids.foldl (fun n i => if tname i = dst then n + box i + park i else n) acc := by
  intro ids
  induction ids with
  | nil =>
    intro acc
    simp
  | cons i ids ih =>
    intro acc
    simp only [List.foldl_cons]
    by_cases hd : tname i = dst
    · simp [hd]
      have hgrow : acc ≤ acc + box i + park i := by omega
      exact Nat.le_trans hgrow (ih (acc + box i + park i))
    · simp [hd]
      exact ih acc

theorem fold_mono (dst : String) (box park : InstId → Nat) :
    ∀ (ids : List InstId) (acc acc' : Nat), acc ≤ acc' →
      ids.foldl (fun n i => if tname i = dst then n + box i + park i else n) acc ≤
        ids.foldl (fun n i => if tname i = dst then n + box i + park i else n) acc' := by
  intro ids
  induction ids with
  | nil =>
    intro acc acc' h
    exact h
  | cons i ids ih =>
    intro acc acc' h
    simp only [List.foldl_cons]
    by_cases hd : tname i = dst
    · simp [hd]
      exact ih _ _ (by omega)
    · simp [hd]
      exact ih _ _ h

theorem share_ge_box (w : World) (name : String) (key : Nat) (dst : String) (host : InstId)
    (hmem : host ∈ w.roster) (hnd : w.roster.Nodup) (hdst : tname host = dst) :
    ((w.st host).box.filter (keyPred name key)).length ≤ queuedFromKey w name key dst := by
  rw [key_filter_len]
  unfold queuedFromKey
  revert hnd hmem
  generalize hr : w.roster = ids
  intro hmem hnd
  clear hr
  induction ids with
  | nil => cases hmem
  | cons i ids ih =>
    have hcons := (List.nodup_cons).mp hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · have hb : (tname host != dst) = false := by simp [hdst, bne]
      simp [hb]
      exact Nat.le_trans (Nat.le_add_right _ ((w.st host).parked.filter (fun p =>
          match p.msg.sender with
          | .peer s k _ => s == name && k == key
          | .core _ => false)).length)
        (fold_ge_acc dst
          (fun i => ((w.st i).box.filter (fun m =>
            match m.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length)
          (fun i => ((w.st i).parked.filter (fun p =>
            match p.msg.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length)
          ids _)
    · have htail := ih hmem hcons.2
      cases hif : (tname i != dst) <;> simp [hif] at htail ⊢
      · exact Nat.le_trans htail (fold_mono dst
          (fun j => ((w.st j).box.filter (fun m =>
            match m.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length)
          (fun j => ((w.st j).parked.filter (fun p =>
            match p.msg.sender with
            | .peer s k _ => s == name && k == key
            | .core _ => false)).length)
          ids 0 _ (Nat.zero_le _))
      · exact htail

theorem nameLen_at_key (name : String) (k : Nat) :
    ∀ (ms : List Msg), (∀ m ∈ ms, ∃ n g, m.sender = InstId.peer n k g) →
      nameLen name ms = (ms.filter (keyPred name k)).length := by
  intro ms h
  induction ms with
  | nil => simp [nameLen]
  | cons m ms ih =>
    obtain ⟨n, g, hs⟩ := h m (List.Mem.head _)
    have htail := ih (fun m' hm' => h m' (List.Mem.tail _ hm'))
    cases hb : n == name
    · simp [nameLen, fromName, keyPred, List.filter, hs, hb]
      simpa [nameLen] using htail
    · simp [nameLen, fromName, keyPred, List.filter, hs, hb]
      simpa [nameLen] using htail

theorem fromName_only (m : Msg) (name name' : String) (hyes : fromName name m = true)
    (hne : name' ≠ name) : fromName name' m = false := by
  cases hsend : m.sender with
  | core _ => simp [fromName, hsend] at hyes
  | peer n _ _ =>
    simp [fromName, hsend] at hyes
    have hdiff : (n == name') = false := by
      cases hbb : n == name' <;> simp_all [beq_iff_eq]
    simp [fromName, hsend, hdiff]

/-- One more message from a sender that still holds a token fits in a keyed
Lemma-1 mailbox. Every queued message is from this host's key, so each
template is charged once. -/
theorem keyed_box_room (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (w : World)
    (hO : OccInv I w) (host : InstId) (k : Nat) (senderName : String)
    (hk : peerKey host = some k) (hlive : (w.st host).life = .alive)
    (hl1 : l1 I.desc (tname host) = true) (hN : 1 ≤ w.N)
    (hgap : queuedFromKey w senderName k (tname host) + 1 ≤ budget I.desc senderName (tname host))
    (hname : senderName ∈ I.desc.templates.map (·.name)) :
    (w.st host).box.length + 1 ≤ capBulk I.desc w.N host := by
  have hmemH := hO.aliveIn host hlive
  have hnd := birth_names I.desc hG
  have hkey : ∀ m ∈ (w.st host).box, ∃ n g, m.sender = InstId.peer n k g := by
    intro m hm
    exact keyed_peer I.desc w host k m hk ((hO.sameKey host).1 m hm)
  have hpick : ∀ m ∈ (w.st host).box, ∃ name ∈ I.desc.templates.map (·.name),
      fromName name m = true := by
    intro m hm
    obtain ⟨n, g, hs⟩ := hkey m hm
    have hsend := hO.sentFrom host m hm
    obtain ⟨t, ht, hshape⟩ := hO.shaped m.sender hsend
    have htin := (templateOf_mem I.desc (tname m.sender) t ht).1
    have htname := (templateOf_mem I.desc (tname m.sender) t ht).2
    refine ⟨t.name, List.mem_map.mpr ⟨t, htin, rfl⟩, ?_⟩
    cases hmul : t.multiplicity with
    | one =>
      simp [hmul] at hshape
      simp [hs] at hshape
    | perPeer =>
      simp [hmul] at hshape
      obtain ⟨_, _, hid⟩ := hshape
      have heq := hid.symm.trans hs
      injection heq with hn _ _
      simp [fromName, hs, hn]
  have honly : ∀ m ∈ (w.st host).box, ∀ name' ∈ I.desc.templates.map (·.name),
      ∀ name ∈ I.desc.templates.map (·.name), fromName name m = true → name' ≠ name →
        fromName name' m = false := by
    intro m _ name' _ name _ hyes hne
    exact fromName_only m name name' hyes hne
  have hlen := length_le_names (I.desc.templates.map (·.name)) (w.st host).box hnd hpick honly
  have hle : ∀ name ∈ I.desc.templates.map (·.name),
      nameLen name (w.st host).box ≤ budget I.desc name (tname host) := by
    intro name hname'
    rw [nameLen_at_key name k (w.st host).box hkey]
    exact Nat.le_trans (share_ge_box w name k (tname host) host hmemH hO.nodup rfl)
      (key_queued_le I w hO name k (tname host))
  have hextra : nameLen senderName (w.st host).box + 1 ≤ budget I.desc senderName (tname host) := by
    rw [nameLen_at_key senderName k (w.st host).box hkey]
    exact Nat.le_trans (Nat.add_le_add_right
      (share_ge_box w senderName k (tname host) host hmemH hO.nodup rfl) 1) hgap
  have hsum := sumName_slack I.desc (tname host) (I.desc.templates.map (·.name)) (w.st host).box
    senderName hname hnd hle hextra
  have hself : ∀ name ∈ I.desc.templates.map (·.name), ∃ t, templateOf I.desc name = some t := by
    intro name hmem
    obtain ⟨t, ht, hn⟩ := List.mem_map.mp hmem
    exact ⟨t, by simpa [templateOf, hn] using birth_find_named I.desc.templates t ht hnd⟩
  have hcover := sumBudget_le_cover I.desc (tname host) w.N hN _ hself
  have hocc := name_cover_le I hL hG (tname host) w.N hN
  have hcap := cap_of_l1 I.desc host w.N hl1
  omega

/-- `name` at `k` is alive, or its mail is still held. One slot, however many
generations share the key. -/
def heldAt (D : Description) (w : World) (name : String) (k : Nat) : Bool :=
  w.roster.any fun id =>
    match id with
    | .peer n key _ =>
      n == name && key == k && ((w.st id).life == .alive || slotMailHeld D w name k)
    | .core _ => false

def heldKeys (D : Description) (w : World) (name : String) : List Nat :=
  w.roster.foldl (fun acc id =>
    match id with
    | .peer n k _ =>
      if n == name && heldAt D w name k && !acc.elem k then acc ++ [k] else acc
    | .core _ => acc) []

/-- This generation occupies the slot: it is alive, or the slot's mail is held.
`loneOutstanding` adds one per such generation. `heldKeys` adds the key once. -/
def loneBit (D : Description) (w : World) (name : String) (id : InstId) : Bool :=
  match id with
  | .peer child k _ => child == name && ((w.st id).life == .alive || slotMailHeld D w name k)
  | .core _ => false

def bitKey (name : String) (id : InstId) : Nat :=
  match id with
  | .peer _ k _ => k
  | .core _ => 0

def pushKey (acc : List Nat) (k : Nat) : List Nat :=
  if acc.elem k = true then acc else acc ++ [k]

theorem pushKey_len (acc : List Nat) (k : Nat) (h : acc.Nodup) :
    (pushKey acc k).length ≤ acc.length + 1 ∧ (pushKey acc k).Nodup := by
  unfold pushKey
  by_cases hseen : acc.elem k = true
  · rw [if_pos hseen]
    exact And.intro (Nat.le_add_right _ _) h
  · rw [if_neg hseen]
    refine And.intro ?_ ?_
    · rw [List.length_append, List.length_singleton]
      exact Nat.le_refl _
    · have hne : k ∉ acc := by
        intro hk
        have : acc.elem k = true := by simpa [List.elem_iff] using hk
        exact hseen this
      have htail : ([k] : List Nat).Nodup := by simp
      have hdis : ∀ a ∈ acc, ∀ b ∈ [k], a ≠ b := by
        intro a ha b hb
        simp at hb
        subst hb
        intro heq
        exact hne (heq ▸ ha)
      exact List.nodup_append.mpr (And.intro h (And.intro htail hdis))

theorem step_shift (bit : InstId → Bool) :
    ∀ (ids : List InstId) (start extra : Nat),
      ids.foldl (fun n id => if bit id = true then n + 1 else n) (start + extra) =
        ids.foldl (fun n id => if bit id = true then n + 1 else n) start + extra := by
  intro ids
  induction ids with
  | nil =>
    intro start extra
    simp
  | cons id ids ih =>
    intro start extra
    simp only [List.foldl_cons]
    cases hb : bit id with
    | false =>
      simp
      exact ih start extra
    | true =>
      simp
      rw [Nat.add_right_comm start extra 1]
      exact ih (start + 1) extra

theorem card_go (bit : InstId → Bool) (key : InstId → Nat) :
    ∀ (ids : List InstId) (acc : List Nat), acc.Nodup →
      (ids.foldl (fun acc id => if bit id = true then pushKey acc (key id) else acc) acc).length ≤
        acc.length + ids.foldl (fun n id => if bit id = true then n + 1 else n) 0 := by
  intro ids
  induction ids with
  | nil =>
    intro acc _
    simp
  | cons id ids ih =>
    intro acc hnd
    simp only [List.foldl_cons]
    cases hb : bit id with
    | false =>
      simp
      simpa using ih acc hnd
    | true =>
      simp
      have hpush := pushKey_len acc (key id) hnd
      have htail := ih (pushKey acc (key id)) hpush.2
      have hshift := step_shift bit ids 0 1
      have hshift' :
          ids.foldl (fun n id => if bit id = true then n + 1 else n) 1 =
            ids.foldl (fun n id => if bit id = true then n + 1 else n) 0 + 1 := by
        simpa using hshift
      rw [hshift']
      omega

theorem loneBit_match (D : Description) (w : World) (name : String) (id : InstId) :
    loneBit D w name id =
      match id with
      | .peer child k _ => child == name && ((w.st id).life == .alive || slotMailHeld D w name k)
      | .core _ => false := by
  cases id <;> rfl

theorem lone_sum (D : Description) (w : World) (name : String) :
    ∀ (ids : List InstId) (n : Nat),
      ids.foldl (fun n id => if loneBit D w name id = true then n + 1 else n) n =
        ids.foldl (fun n id =>
          match id with
          | .peer child k _ =>
            if child == name && ((w.st id).life == .alive || slotMailHeld D w name k) then n + 1
            else n
          | .core _ => n) n := by
  intro ids
  induction ids with
  | nil =>
    intro _
    rfl
  | cons id ids ih =>
    intro n
    simp only [List.foldl_cons]
    cases id with
    | core c =>
      have hb : loneBit D w name (.core c) = false := rfl
      rw [hb]
      exact ih n
    | peer child k g =>
      have hb : loneBit D w name (.peer child k g) =
          (child == name && ((w.st (.peer child k g)).life == .alive || slotMailHeld D w name k)) := rfl
      rw [hb]
      exact ih _

/-- One entry per key that has a live generation or held mail. A later
generation of that key does not append again. -/
def bitKeys (D : Description) (w : World) (name : String) : List Nat :=
  w.roster.foldl (fun acc id =>
    if loneBit D w name id = true then pushKey acc (bitKey name id) else acc) []

/-- Distinct held keys are at most the generation count. A second generation of
a key that already holds mail increments `loneOutstanding` and not the key. -/
theorem bitKeys_le_lone (D : Description) (w : World) (name : String) :
    (bitKeys D w name).length ≤ loneOutstanding D w name := by
  have hcard := card_go (loneBit D w name) (bitKey name) w.roster [] (by simp)
  have hsum := lone_sum D w name w.roster 0
  have hfold : loneOutstanding D w name =
      w.roster.foldl (fun n id => if loneBit D w name id = true then n + 1 else n) 0 := by
    unfold loneOutstanding
    exact hsum.symm
  simpa [bitKeys, hfold, Nat.zero_add] using hcard

theorem push_mem (acc : List Nat) (k x : Nat) : x ∈ pushKey acc k ↔ x ∈ acc ∨ x = k := by
  unfold pushKey
  by_cases h : acc.elem k = true
  · rw [ite_eq_left h]
    constructor
    · intro hx
      exact Or.inl hx
    · intro hx
      cases hx with
      | inl hx => exact hx
      | inr hx =>
        rw [hx]
        exact (List.elem_iff).mp h
  · rw [ite_eq_right h]
    simp [List.mem_append]

theorem fold_push_mem (bit : InstId → Bool) (key : InstId → Nat) :
    ∀ (ids : List InstId) (acc : List Nat) (k : Nat),
      k ∈ ids.foldl (fun acc id => if bit id = true then pushKey acc (key id) else acc) acc ↔
        k ∈ acc ∨ ∃ id, id ∈ ids ∧ bit id = true ∧ key id = k := by
  intro ids
  induction ids with
  | nil =>
    intro acc k
    simp [List.mem_nil_iff]
  | cons id ids ih =>
    intro acc k
    simp only [List.foldl_cons]
    by_cases hb : bit id = true
    · rw [ite_eq_left hb, ih, push_mem]
      constructor
      · intro hk
        cases hk with
        | inl hk =>
          cases hk with
          | inl hk => exact Or.inl hk
          | inr hk => exact Or.inr ⟨id, List.Mem.head _, hb, hk.symm⟩
        | inr hk =>
          obtain ⟨id', hmem, hbit, hkey⟩ := hk
          exact Or.inr ⟨id', List.Mem.tail _ hmem, hbit, hkey⟩
      · intro hk
        cases hk with
        | inl hk => exact Or.inl (Or.inl hk)
        | inr hk =>
          obtain ⟨id', hid, hbit, hkey⟩ := hk
          cases hid with
          | head => exact Or.inl (Or.inr hkey.symm)
          | tail _ hmem => exact Or.inr ⟨id', hmem, hbit, hkey⟩
    · rw [ite_eq_right hb, ih]
      constructor
      · intro hk
        cases hk with
        | inl hk => exact Or.inl hk
        | inr hk =>
          obtain ⟨id', hmem, hbit, hkey⟩ := hk
          exact Or.inr ⟨id', List.Mem.tail _ hmem, hbit, hkey⟩
      · intro hk
        cases hk with
        | inl hk => exact Or.inl hk
        | inr hk =>
          obtain ⟨id', hid, hbit, hkey⟩ := hk
          cases hid with
          | head => exact absurd hbit hb
          | tail _ hmem => exact Or.inr ⟨id', hmem, hbit, hkey⟩

theorem bitKeys_mem (D : Description) (w : World) (name : String) (k : Nat) :
    k ∈ bitKeys D w name ↔ ∃ id, id ∈ w.roster ∧ loneBit D w name id = true ∧ bitKey name id = k := by
  simpa [bitKeys] using fold_push_mem (loneBit D w name) (bitKey name) w.roster [] k

theorem heldAt_bit (D : Description) (w : World) (name : String) (k : Nat) :
    heldAt D w name k = true ↔ ∃ id, id ∈ w.roster ∧ loneBit D w name id = true ∧ bitKey name id = k := by
  unfold heldAt
  constructor
  · intro h
    obtain ⟨id, hid, hb⟩ := _root_.List.any_eq_true.mp h
    cases id with
    | core _ => simp at hb
    | peer n key g =>
      simp only [Bool.and_eq_true] at hb
      have hname : (n == name) = true := hb.1.1
      have hkey : (key == k) = true := hb.1.2
      have hlive : ((w.st (.peer n key g)).life == .alive || slotMailHeld D w name k) = true := hb.2
      have hk : key = k := by simpa [beq_iff_eq] using hkey
      refine ⟨.peer n key g, hid, ?_, ?_⟩
      · simp only [loneBit, hname, Bool.true_and]
        rw [hk] at hlive ⊢
        exact hlive
      · exact hk
  · intro ⟨id, hid, hbit, hkey⟩
    apply _root_.List.any_eq_true.mpr
    refine ⟨id, hid, ?_⟩
    cases id with
    | core _ => simp [loneBit] at hbit
    | peer n key g =>
      simp only [loneBit, Bool.and_eq_true] at hbit
      simp only [bitKey] at hkey
      rw [hkey] at hbit
      simp [hbit.1, hkey, hbit.2, Bool.and_true]

theorem nodup_sub_len (l1 l2 : List Nat) (h1 : l1.Nodup)
    (hsub : ∀ k, k ∈ l1 → k ∈ l2) : l1.length ≤ l2.length := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons a l1 ih =>
    have hnd := (List.nodup_cons).mp h1
    have ha : a ∈ l2 := hsub a (List.Mem.head _)
    have htail := ih (l2.erase a) hnd.2 (fun k hk => by
      have hk2 := hsub k (List.Mem.tail _ hk)
      have hne : k ≠ a := by
        intro heq
        exact hnd.1 (heq ▸ hk)
      exact (List.mem_erase_of_ne hne).mpr hk2)
    have herase := List.length_erase_of_mem ha
    have hpos := List.length_pos_of_mem ha
    have hlen : (a :: l1).length = l1.length + 1 := by simp
    rw [hlen]
    have hle : l1.length ≤ l2.length - 1 := by
      rw [← herase]
      exact htail
    omega

def heldBit (D : Description) (w : World) (name : String) (id : InstId) : Bool :=
  match id with
  | .peer n k _ => n == name && heldAt D w name k
  | .core _ => false

theorem fold_push_nodup (bit : InstId → Bool) (key : InstId → Nat) :
    ∀ (ids : List InstId) (acc : List Nat), acc.Nodup →
      (ids.foldl (fun acc id => if bit id = true then pushKey acc (key id) else acc) acc).Nodup := by
  intro ids
  induction ids with
  | nil =>
    intro acc h
    exact h
  | cons id ids ih =>
    intro acc h
    simp only [List.foldl_cons]
    by_cases hb : bit id = true
    · rw [ite_eq_left hb]
      exact ih _ (pushKey_len acc (key id) h).2
    · rw [ite_eq_right hb]
      exact ih acc h

theorem held_step_push (D : Description) (w : World) (name : String) (acc : List Nat) (id : InstId) :
    (match id with
      | .peer n k _ =>
        if n == name && heldAt D w name k && !acc.elem k then acc ++ [k] else acc
      | .core _ => acc) =
      (match id with
        | .peer n k _ => if n == name && heldAt D w name k = true then pushKey acc k else acc
        | .core _ => acc) := by
  cases id with
  | core _ => rfl
  | peer n k _ =>
    by_cases hbit : (n == name && heldAt D w name k) = true
    · have hname : (n == name) = true := by
        simp only [Bool.and_eq_true] at hbit
        exact hbit.1
      have hheld : heldAt D w name k = true := by
        simp only [Bool.and_eq_true] at hbit
        exact hbit.2
      cases hseen : acc.elem k with
      | true =>
        simp [hname, hheld, hseen, pushKey, Bool.and_true, Bool.true_and]
      | false =>
        simp [hname, hheld, hseen, pushKey]
    · have hnot : ¬ (n == name && heldAt D w name k) = true := hbit
      cases hn : (n == name) with
      | false => simp [hn, pushKey]
      | true =>
        cases hh : heldAt D w name k with
        | false => simp [hn, hh, pushKey]
        | true =>
          have : (n == name && heldAt D w name k) = true := by simp [hn, hh]
          exact absurd this hnot

theorem held_push_bit (D : Description) (w : World) (name : String) (acc : List Nat) (id : InstId) :
    (match id with
      | .peer n k _ => if n == name && heldAt D w name k = true then pushKey acc k else acc
      | .core _ => acc) =
      (if heldBit D w name id = true then pushKey acc (bitKey name id) else acc) := by
  cases id with
  | core _ =>
    simp [heldBit]
  | peer _ _ _ =>
    simp [heldBit, bitKey]

theorem held_fold_push (D : Description) (w : World) (name : String) :
    ∀ (ids : List InstId) (acc : List Nat),
      ids.foldl (fun acc id =>
        match id with
        | .peer n k _ =>
          if n == name && heldAt D w name k && !acc.elem k then acc ++ [k] else acc
        | .core _ => acc) acc =
        ids.foldl (fun acc id =>
          if heldBit D w name id = true then pushKey acc (bitKey name id) else acc) acc := by
  intro ids
  induction ids with
  | nil =>
    intro _
    rfl
  | cons id ids ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [held_step_push D w name acc id, held_push_bit D w name acc id]
    exact ih _

theorem heldKeys_mem (D : Description) (w : World) (name : String) (k : Nat) :
    k ∈ heldKeys D w name ↔
      ∃ id, id ∈ w.roster ∧ heldBit D w name id = true ∧ bitKey name id = k := by
  have hfold := held_fold_push D w name w.roster []
  have hmem := fold_push_mem (heldBit D w name) (bitKey name) w.roster [] k
  unfold heldKeys
  rw [hfold]
  constructor
  · intro hk
    cases hmem.mp hk with
    | inl hempty => simp at hempty
    | inr h => exact h
  · intro h
    exact hmem.mpr (Or.inr h)

/-- `heldKeys` and `bitKeys` record the same keys: a key is held exactly when
some generation of it is alive or the slot's mail is still queued. -/
theorem held_mem_bit (D : Description) (w : World) (name : String) (k : Nat) :
    k ∈ heldKeys D w name ↔ k ∈ bitKeys D w name := by
  rw [heldKeys_mem, bitKeys_mem]
  constructor
  · intro ⟨id, hid, hbit, hkey⟩
    cases id with
    | core _ => simp [heldBit] at hbit
    | peer n key g =>
      simp only [heldBit, Bool.and_eq_true] at hbit
      simp only [bitKey] at hkey
      have hheld : heldAt D w name k = true := by simpa [hkey] using hbit.2
      exact (heldAt_bit D w name k).mp hheld
  · intro ⟨id, hid, hbit, hkey⟩
    have hheld : heldAt D w name k = true := (heldAt_bit D w name k).mpr ⟨id, hid, hbit, hkey⟩
    cases id with
    | core _ => simp [loneBit] at hbit
    | peer n key g =>
      simp only [loneBit, Bool.and_eq_true] at hbit
      simp only [bitKey] at hkey
      refine ⟨.peer n key g, hid, ?_, hkey⟩
      simp only [heldBit, hbit.1, hkey, hheld, Bool.and_true, Bool.true_and]

theorem heldKeys_nodup (D : Description) (w : World) (name : String) :
    (heldKeys D w name).Nodup := by
  have hfold := held_fold_push D w name w.roster []
  have hnd := fold_push_nodup (heldBit D w name) (bitKey name) w.roster [] (by simp)
  unfold heldKeys
  rw [hfold]
  exact hnd

theorem bitKeys_nodup (D : Description) (w : World) (name : String) :
    (bitKeys D w name).Nodup := by
  simpa [bitKeys] using fold_push_nodup (loneBit D w name) (bitKey name) w.roster [] (by simp)

theorem held_le_bit (D : Description) (w : World) (name : String) :
    (heldKeys D w name).length ≤ (bitKeys D w name).length := by
  exact nodup_sub_len _ _ (heldKeys_nodup D w name)
    (fun k hk => (held_mem_bit D w name k).mp hk)

theorem held_le_lone (D : Description) (w : World) (name : String) :
    (heldKeys D w name).length ≤ loneOutstanding D w name :=
  Nat.le_trans (held_le_bit D w name) (bitKeys_le_lone D w name)

/-- A birth appends one empty alive actor and leaves every earlier actor. A
held key afterwards was held before, or it is the new key. -/
theorem held_extend (D : Description) (w w' : World) (name : String) (id : InstId) (k g : Nat)
    (hros : w'.roster = w.roster ++ [id])
    (hid : id = InstId.peer name k g)
    (hst : ∀ i, i ≠ id → w'.st i = w.st i)
    (hempty : (w'.st id).box = [] ∧ (w'.st id).prio = [] ∧ (w'.st id).parked = [])
    (hmail : ∀ key, slotMailHeld D w' name key = true → slotMailHeld D w name key = true) :
    ∀ key, key ∈ heldKeys D w' name → key ∈ heldKeys D w name ∨ key = k := by
  intro key hk
  rw [held_mem_bit, bitKeys_mem] at hk
  obtain ⟨wit, hwit, hbit, hwk⟩ := hk
  by_cases hnew : wit = id
  · cases wit with
    | core _ => simp [loneBit] at hbit
    | peer n key' g' =>
      have hwk' : key' = key := by simpa [bitKey] using hwk
      have hid' : InstId.peer n key' g' = InstId.peer name k g := by
        rw [hnew]
        exact hid
      cases hid'
      exact Or.inr hwk'.symm
  · have hmem : wit ∈ w.roster := by
      have hmem' : wit ∈ w.roster ++ [id] := by rw [← hros]; exact hwit
      simp [List.mem_append] at hmem'
      cases hmem' with
      | inl h => exact h
      | inr h =>
        have : wit = id := by simpa [List.mem_singleton] using h
        exact absurd this hnew
    have hst' := hst wit hnew
    rw [held_mem_bit, bitKeys_mem]
    refine Or.inl ⟨wit, hmem, ?_, ?_⟩
    · cases wit with
      | core _ => simp [loneBit] at hbit
      | peer n key' g' =>
        simp only [loneBit, Bool.and_eq_true] at hbit
        have hnameb : (n == name) = true := hbit.1
        have hflag := hbit.2
        simp only [loneBit, hnameb, Bool.true_and]
        rw [← hst']
        by_cases hlive : (w'.st (.peer n key' g')).life = .alive
        · have hb : ((w'.st (.peer n key' g')).life == .alive) = true := by
            simpa [beq_iff_eq] using hlive
          simp [hb]
        · have hslot : slotMailHeld D w' name key' = true := by
            cases hbb : (w'.st (.peer n key' g')).life == .alive with
            | true =>
              exact absurd (beq_iff_eq.mp hbb) hlive
            | false =>
              rw [hbb, Bool.false_or] at hflag
              exact hflag
          have hold := hmail key' hslot
          simp [hold]
    · exact hwk

theorem held_extend_len (D : Description) (w w' : World) (name : String) (id : InstId) (k g : Nat)
    (hros : w'.roster = w.roster ++ [id])
    (hid : id = InstId.peer name k g)
    (hst : ∀ i, i ≠ id → w'.st i = w.st i)
    (hempty : (w'.st id).box = [] ∧ (w'.st id).prio = [] ∧ (w'.st id).parked = [])
    (hmail : ∀ key, slotMailHeld D w' name key = true → slotMailHeld D w name key = true) :
    (heldKeys D w' name).length ≤ (heldKeys D w name).length + 1 := by
  have hsub := held_extend D w w' name id k g hros hid hst hempty hmail
  have hlen := nodup_sub_len _ (heldKeys D w name ++ [k]) (heldKeys_nodup D w' name) (fun key hk => by
    cases hsub key hk with
    | inl hold => exact List.mem_append_left _ hold
    | inr heq =>
      rw [heq]
      exact List.mem_append_right _ (List.Mem.head _))
  simpa [List.length_append] using hlen

/-- A key held after a step that births nobody of `name`, resurrects nobody,
and only queues mail from a generation that was already alive, was held before. -/
theorem held_sub (D : Description) (w w' : World) (name : String)
    (hros : ∀ id, id ∈ w'.roster → tname id = name → id ∈ w.roster)
    (hlife : ∀ id, id ∈ w.roster → (w'.st id).life = .alive → (w.st id).life = .alive)
    (hmail : ∀ k, slotMailHeld D w' name k = true →
      slotMailHeld D w name k = true ∨
        ∃ id, id ∈ w.roster ∧ fromSlot name k id = true ∧ (w.st id).life = .alive) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  intro k hk
  rw [held_mem_bit] at hk ⊢
  rw [bitKeys_mem] at hk ⊢
  obtain ⟨id, hid, hbit, hkey⟩ := hk
  have hname : tname id = name := by
    cases id with
    | core _ => simp [loneBit] at hbit
    | peer n _ _ =>
      simp only [loneBit, Bool.and_eq_true] at hbit
      simp [tname, beq_iff_eq.mp hbit.1]
  have hold := hros id hid hname
  cases id with
  | core _ => simp [loneBit] at hbit
  | peer n key g =>
    simp only [loneBit, Bool.and_eq_true] at hbit
    simp only [bitKey] at hkey
    have hnameb : (n == name) = true := hbit.1
    have hflag : ((w'.st (.peer n key g)).life == .alive || slotMailHeld D w' name key) = true := hbit.2
    by_cases hlive : (w'.st (.peer n key g)).life = .alive
    · have holdLive := hlife _ hold hlive
      refine ⟨.peer n key g, hold, ?_, hkey⟩
      simp only [loneBit, hnameb, Bool.true_and]
      rw [hkey] at holdLive ⊢
      have hb : ((w.st (.peer n k g)).life == .alive) = true := by
        simpa [beq_iff_eq] using holdLive
      simp [hb]
    · have hmailK : slotMailHeld D w' name key = true := by
        cases hbb : (w'.st (.peer n key g)).life == .alive with
        | true =>
          have : (w'.st (.peer n key g)).life = .alive := by simpa [beq_iff_eq] using hbb
          exact absurd this hlive
        | false =>
          rw [hbb, Bool.false_or] at hflag
          exact hflag
      rw [hkey] at hmailK
      cases hmail k hmailK with
      | inl holdMail =>
        refine ⟨.peer n key g, hold, ?_, hkey⟩
        simp only [loneBit, hnameb, Bool.true_and]
        rw [hkey]
        simp [holdMail]
      | inr hwho =>
        obtain ⟨id', hid', hfrom, halive⟩ := hwho
        cases id' with
        | core _ => simp [fromSlot] at hfrom
        | peer n' key' g' =>
          simp only [fromSlot, Bool.and_eq_true] at hfrom
          have hn' : n' = name := by simpa [beq_iff_eq] using hfrom.1
          have hk' : key' = k := by simpa [beq_iff_eq] using hfrom.2
          refine ⟨.peer n' key' g', hid', ?_, hk'⟩
          simp only [loneBit]
          rw [hn', hk'] at halive ⊢
          have hb : ((w.st (.peer name k g')).life == .alive) = true := by
            simpa [beq_iff_eq] using halive
          simp [hb]

/-! A root tombstone waits on descendant mail, and that mail is what the
parent's slot count sees. -/

/-- `sealedTogether` is true of an actor and itself, so a root's own mail is the
base of the descendant test. -/
theorem sealed_self (w : World) (id : InstId) : sealedTogether w id id = true := by
  simp [sealedTogether]

/-- Receiving a root tombstone tests `mailInFlight` of its sender. That test is
`sealedTogether`: the sender of the queued message is the root, or a descendant
the parent chain records. Descendant mail and the root's own mail are the same
test. -/
theorem tomb_waits_on_descendant (w : World) (root host : InstId) (m : Msg)
    (hhost : host ∈ w.roster) (hlive : (w.st host).life = .alive)
    (ht : m.tombstone = false) (hs : sealedTogether w root m.sender = true)
    (hm : m ∈ (w.st host).box ∨ m ∈ (w.st host).prio) :
    mailInFlight w root = true :=
  flight_of_msg w root host m hhost hlive ht hs hm

/-- Mail in flight at a descendant is mail in flight at every recorded ancestor. -/
theorem flight_strict (w : World) (hF : ParentForest w) {desc anc : InstId}
    (h : StrictAncestor w desc anc) (hf : mailInFlight w desc = true) :
    mailInFlight w anc = true := by
  induction h with
  | edge he => exact flight_ancestor w hF _ _ he.1 hf
  | tail he _ ih => exact ih (flight_ancestor w hF _ _ he.1 hf)

/-- A live descendant has a live ancestor. A dead parent has no live child. -/
theorem ancestor_alive (w : World) (hKids : DeadChildless w) (hcr : w.crashed = false)
    {desc anc : InstId} (h : StrictAncestor w desc anc)
    (hlive : (w.st desc).life = .alive) : (w.st anc).life = .alive := by
  induction h with
  | edge he => exact kids_alive w hKids hcr _ _ hlive he.1
  | tail he _ ih => exact ih (kids_alive w hKids hcr _ _ hlive he.1)

/-- A dead root whose mail is still in flight has its tombstone on the live parent.
The parent-dead branch of `TombChain` contradicts the parent being alive. -/
theorem dead_flight_tomb (w : World) (hChain : TombChain w) (hcr : w.crashed = false)
    (root parent : InstId) (hdead : (w.st root).life = .dead)
    (hpar : (w.st root).parent = some parent) (hlive : (w.st parent).life = .alive)
    (hf : mailInFlight w root = true) : HoldsTomb w parent root := by
  have hstep := hChain root hcr hdead hf
  rw [hpar] at hstep
  rcases hstep with hliveH | hdeadP
  · exact hliveH.2
  · exact absurd hlive hdeadP.1

/-- Program mail from the root, or from a recorded descendant, keeps that tombstone
queued. Parked mail is not a second path: this hypothesis is `mailInFlight`, which
only reads live boxes and priority lanes. -/
theorem descendant_mail_tomb (w : World) (hChain : TombChain w) (hF : ParentForest w)
    (hcr : w.crashed = false) (root parent sender : InstId)
    (hdead : (w.st root).life = .dead) (hpar : (w.st root).parent = some parent)
    (hlive : (w.st parent).life = .alive)
    (hwho : sender = root ∨ StrictAncestor w sender root)
    (hf : mailInFlight w sender = true) : HoldsTomb w parent root := by
  have hroot : mailInFlight w root = true := by
    rcases hwho with hwho | hwho
    · simpa [hwho] using hf
    · exact flight_strict w hF hwho hf
  exact dead_flight_tomb w hChain hcr root parent hdead hpar hlive hroot

/-- A live host does not park mail from a dead sender. `ParkedFromLive` is the
negative; a seal also drops those entries, so a held slot's remaining mail is
program mail in a box or a priority lane. -/
theorem parked_sender_not_dead (w : World) (hPark : ParkedFromLive w)
    (host : InstId) (p : Parked) (hlive : (w.st host).life = .alive)
    (hp : p ∈ (w.st host).parked) : (w.st p.sender).life ≠ .dead :=
  hPark host p hlive hp

/-! One root actor per subtree key. A second scheduler root takes a fresh key,
and a child birth is not a root. -/

/-- Root actors of one nonempty subtree use distinct keys. -/
def OneCohort (D : Description) (roster : List InstId) : Prop :=
  ∀ sub k n1 g1 n2 g2 t1 t2,
    sub ≠ "" →
    templateOf D n1 = some t1 → templateOf D n2 = some t2 →
    t1.subtree = sub → t2.subtree = sub →
    rootOf D t1 = true → rootOf D t2 = true →
    InstId.peer n1 k g1 ∈ roster → InstId.peer n2 k g2 ∈ roster →
    n1 = n2 ∧ g1 = g2

theorem oneCohort_same (D : Description) {r r' : List InstId} (h : r' = r) (hc : OneCohort D r) :
    OneCohort D r' := by
  simpa [h] using hc

/-- The id a birth appends is not an old root at its own key. -/
theorem oneCohort_snoc (D : Description) (roster : List InstId) (id : InstId)
    (h : OneCohort D roster)
    (hdis : ∀ n k g t, id = InstId.peer n k g →
      templateOf D n = some t → rootOf D t = true → t.subtree ≠ "" →
      ∀ n2 g2, InstId.peer n2 k g2 ∈ roster → templateSubtree D n2 = t.subtree → False) :
    OneCohort D (roster ++ [id]) := by
  intro sub k n1 g1 n2 g2 t1 t2 hsub ht1 ht2 hs1 hs2 hr1 hr2 hm1 hm2
  rcases List.mem_append.mp hm1 with hm1 | hm1
  · rcases List.mem_append.mp hm2 with hm2 | hm2
    · exact h sub k n1 g1 n2 g2 t1 t2 hsub ht1 ht2 hs1 hs2 hr1 hr2 hm1 hm2
    · simp only [List.mem_singleton] at hm2
      exact False.elim (hdis n2 k g2 t2 hm2.symm ht2 hr2 (by rw [hs2]; exact hsub) n1 g1 hm1
        (by simp [templateSubtree, ht1, hs1, hs2]))
  · simp only [List.mem_singleton] at hm1
    rcases List.mem_append.mp hm2 with hm2 | hm2
    · exact False.elim (hdis n1 k g1 t1 hm1.symm ht1 hr1 (by rw [hs1]; exact hsub) n2 g2 hm2
        (by simp [templateSubtree, ht2, hs1, hs2]))
    · simp only [List.mem_singleton] at hm2
      have hids : InstId.peer n1 k g1 = InstId.peer n2 k g2 := hm1.trans hm2.symm
      cases hids
      exact ⟨rfl, rfl⟩

theorem coreRoster_peer (D : Description) (name : String) (k g : Nat) :
    InstId.peer name k g ∉ coreRoster D := by
  intro h
  unfold coreRoster at h
  obtain ⟨t, _, hif⟩ := List.mem_filterMap.mp h
  by_cases hone : (t.multiplicity == .one) = true
  · simp [hone] at hif
  · simp [hone] at hif

theorem oneCohort_init (I : Impl) (N : Nat) : OneCohort I.desc (initWorld I N).roster := by
  intro sub k n1 g1 n2 g2 t1 t2 _ _ _ _ _ _ _ hm1 _
  rw [init_roster] at hm1
  exact absurd hm1 (coreRoster_peer I.desc n1 k g1)

theorem setActor_roster (w : World) (id : InstId) (a : Actor) :
    (setActor w id a).roster = w.roster := rfl

theorem crashWorld_roster (w : World) : (crashWorld w).roster = w.roster := rfl

theorem commit_roster (w : World) (id : InstId) (next : Actor) :
    (commitCont w id next).roster = w.roster := by
  unfold commitCont
  split
  · rfl
  · exact setActor_roster _ _ _

theorem offer_roster (D : Description) (w : World) (host : InstId) (msg : Msg) :
    (offerPrio D w host msg).roster = w.roster := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio >= capPrio D w.N host) = true
  · simp [hfull, crashWorld_roster]
  · simp [hfull, setActor_roster]

theorem tryWake_roster (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer : InstId) : (tryWake D w dstId label writer).roster = w.roster := by
  unfold tryWake
  by_cases hskip :
      ((w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip]
  · simp [hskip, offer_roster]

theorem wake_roster (D : Description) (ids : List InstId) (w : World) (dst label : String)
    (writer : InstId) :
    (ids.foldl (fun w id => tryWake D w id label writer) w).roster = w.roster := by
  induction ids generalizing w with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, ih, tryWake_roster]

theorem wakeReaders_roster (D : Description) (w : World) (dst label : String) (writer : InstId) :
    (wakeReaders D w dst label writer).roster = w.roster := by
  unfold wakeReaders readersOf
  exact wake_roster D _ w dst label writer

theorem reply_roster (w : World) (sender : InstId) (k : Cont) :
    (performReply w sender k).roster = w.roster := by
  unfold performReply
  split
  · exact setActor_roster _ _ _
  · split
    · split
      · exact setActor_roster _ _ _
      · exact setActor_roster _ _ _
    · exact setActor_roster _ _ _

theorem abortChildren_roster (D : Description) (w : World) (parent : InstId) :
    (abortChildren D w parent).roster = w.roster := by
  unfold abortChildren
  have hfold : ∀ (ids : List InstId) (w0 : World),
      (ids.foldl (fun acc c =>
        if isChild acc parent c && (acc.st c).life == .alive then
          shutdownActor D (dropDescendants D acc c) c
        else acc) w0).roster = w0.roster := by
    intro ids
    induction ids with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro w0
      rw [List.foldl_cons]
      by_cases hgo : (isChild w0 parent c && (w0.st c).life == .alive) = true
      · simp only [hgo, ite_true]
        have hsh : (shutdownActor D (dropDescendants D w0 c) c).roster = w0.roster :=
          (shutdown_roster D (dropDescendants D w0 c) c).trans (drop_roster D w0 c)
        exact (ih _).trans hsh
      · simp only [hgo, ite_false]
        exact ih w0
  exact hfold w.roster w

theorem admit_roster (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).roster = w.roster ++ [id] := by
  unfold admitBorn
  rw [readCells_roster]
  exact setActor_roster _ _ _

end Deadlock
