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

end Deadlock
