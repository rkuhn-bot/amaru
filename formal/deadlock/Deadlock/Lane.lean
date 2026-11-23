/-
A Lemma-1 mailbox has room for one more message from a sender that still holds
a token, so the parked lane stays empty.

`popFactor` is `N` for a per-peer template and `1` for a core. The sum of those
factors times each template's budget fits in `totalOcc.eval N`, which Lemma 1
puts under `capBulk`.
-/
import Deadlock.Birth
import Deadlock.ChildBirth
import Deadlock.Occ
import Deadlock.Step

set_option autoImplicit false

namespace Deadlock

def popFactor (n : Nat) (t : Template) : Nat :=
  if t.multiplicity == .perPeer then n else 1

theorem factor_le (t : Template) (occ : Affine) (n : Nat)
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
    (ht : templateOf I.desc name = some t) (n : Nat) :
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
      have hedge := factor_le t e.occupancy n ha hb
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

theorem cover_go (I : Impl) (hL : LocalOk I) (dst : String) (n : Nat) :
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
    have hsrc := src_factor_go I hL dst name t ht n I.desc.edges (fun _ h => h)
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

theorem name_cover_le (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (dst : String) (n : Nat) :
    nameCover I.desc dst n (I.desc.templates.map (·.name)) ≤ (totalOcc I.desc dst).eval n := by
  have hnd := birth_names I.desc hG
  have hself : ∀ name ∈ I.desc.templates.map (·.name), ∃ t, templateOf I.desc name = some t := by
    intro name hmem
    obtain ⟨t, ht, hname⟩ := List.mem_map.mp hmem
    refine ⟨t, ?_⟩
    simpa [templateOf, hname] using birth_find_named I.desc.templates t ht hnd
  have hle := cover_go I hL dst n (I.desc.templates.map (·.name)) [] hnd
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
  have hocc := name_cover_le I hL hG (tname host) w.N
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

/-- What a step does to the roster. A scheduler spawn appends one root at a
fresh key. A per-peer parent appends one child at its own key. Every other
step keeps the roster. -/
inductive RosterGrow (I : Impl) (w : World) : World → Prop where
  | keep (w' : World) : w'.roster = w.roster → RosterGrow I w w'
  | root (w' : World) (template : String) (k g : Nat) (t : Template) :
      templateOf I.desc template = some t →
      rootOf I.desc t = true →
      w'.roster = w.roster ++ [InstId.peer template k g] →
      (∀ n2 g2, InstId.peer n2 k g2 ∈ w.roster → templateSubtree I.desc n2 = t.subtree →
        t.subtree ≠ "" → False) →
      RosterGrow I w w'
  | child (w' : World) (child : String) (k g : Nat) (t : Template) (parent : InstId) :
      templateOf I.desc child = some t →
      t.supervisor = some (tname parent) →
      parent ∈ w.roster →
      (∃ g0, parent = InstId.peer (tname parent) k g0) →
      w'.roster = w.roster ++ [InstId.peer child k g] →
      RosterGrow I w w'

theorem maySpawn_root (D : Description) (w : World) (template : String) (t : Template)
    (h : maySpawnRoot D w template t = true) : rootOf D t = true := by
  unfold maySpawnRoot at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- A child of a per-peer stage is not a scheduler root. -/
theorem child_not_root (D : Description) (child parent : String) (t s : Template)
    (ht : templateOf D child = some t) (hs : templateOf D parent = some s)
    (hsup : t.supervisor = some parent) (hper : s.multiplicity = .perPeer) :
    rootOf D t = false := by
  unfold rootOf
  simp [hsup, hs, hper]
  decide

theorem spawn_grow (I : Impl) (w w' : World) (template : String)
    (h : spawn I w template = some w') : RosterGrow I w w' := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · have hroot : rootOf I.desc t = true := maySpawn_root I.desc w template t hmay
      simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at h
        cases h
        exact RosterGrow.root (placePeer I w template (freshKey I.desc w t.subtree) t.initial
            (some (InstId.core name)) (fun u =>
              { u with nextKey := fun s =>
                  if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s }))
          template (freshKey I.desc w t.subtree)
          (maxGen w template (freshKey I.desc w t.subtree)) t ht hroot
          (place_roster I w template (freshKey I.desc w t.subtree) t.initial
            (some (InstId.core name)) (fun u =>
              { u with nextKey := fun s =>
                  if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            (fun _ => rfl))
          (by
            intro n2 g2 hmem htree hne
            exact Nat.lt_irrefl _ (freshKey_gt I.desc w t.subtree n2
              (freshKey I.desc w t.subtree) g2 hne htree hmem))
      | none =>
        rw [hsup] at h
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at h
          cases h
          exact RosterGrow.root (placePeer I w template (w.nextIx template) t.initial none
              (fun u => { u with nextIx := fun n =>
                  if n = template then w.nextIx template + 1 else u.nextIx n }))
            template (w.nextIx template) (maxGen w template (w.nextIx template)) t ht hroot
            (place_roster I w template (w.nextIx template) t.initial none
              (fun u => { u with nextIx := fun n =>
                  if n = template then w.nextIx template + 1 else u.nextIx n })
              (fun _ => rfl))
            (by
              intro _ _ _ _ hne
              exact hne (by simpa [beq_iff_eq] using hempty))
        · have hf : (t.subtree == "") = false := by
            cases hb : t.subtree == "" with
            | false => rfl
            | true => exact absurd hb hempty
          rw [hf] at h
          cases h
          exact RosterGrow.root (placePeer I w template (freshKey I.desc w t.subtree) t.initial none
              (fun u => { u with nextKey := fun s =>
                  if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s }))
            template (freshKey I.desc w t.subtree)
            (maxGen w template (freshKey I.desc w t.subtree)) t ht hroot
            (place_roster I w template (freshKey I.desc w t.subtree) t.initial none
              (fun u => { u with nextKey := fun s =>
                  if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
              (fun _ => rfl))
            (by
              intro n2 g2 hmem htree hne
              exact Nat.lt_irrefl _ (freshKey_gt I.desc w t.subtree n2
                (freshKey I.desc w t.subtree) g2 hne htree hmem))
    · simp [hmay] at h

theorem spawnChild_grow (I : Impl) (w : World) (parent : InstId) (child : String) (w' : World)
    (hid : parent ∈ w.roster) (h : spawnChild I w parent child = some w') :
    RosterGrow I w w' := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = true
    · simp only [hgo, ite_true] at h
      cases parent with
      | core _ => simp at h
      | peer pn pk pg =>
        by_cases hblk : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = true
        · simp [hblk] at h
          cases h
          exact RosterGrow.keep w rfl
        · have hf : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblk
          simp only [hf, ite_false] at h
          cases h
          have hsup : t.supervisor = some pn := by
            have hgo' := hgo
            simp only [Bool.and_eq_true] at hgo'
            have hnamed : supNamed t.supervisor pn = true := by
              simpa [tname] using hgo'.1.2
            cases hsv : t.supervisor with
            | none => simp [supNamed, hsv] at hnamed
            | some n =>
              simp [supNamed, hsv, beq_iff_eq] at hnamed
              rw [hnamed]
          exact RosterGrow.child (admitBorn I w (InstId.peer child pk (maxGen w child pk))
              { bornActor I.desc w child pk t.initial with parent := some (InstId.peer pn pk pg) })
            child pk (maxGen w child pk) t (InstId.peer pn pk pg) ht
            (by simpa [tname] using hsup) hid ⟨pg, rfl⟩
            (admit_roster I w (InstId.peer child pk (maxGen w child pk)) _)
    · have hf :
          (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf, ite_false] at h
      by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hstay, ite_true] at h
        cases h
        exact RosterGrow.keep w rfl
      · have hstayF :
            (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hstay
        simp [hstayF] at h

theorem receiveBulk_roster (I : Impl) (w w' : World) (id : InstId)
    (h : receiveBulk I w id = some w') : w'.roster = w.roster := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [setActor_roster, creditLive_roster, setActor_roster]
          rw [← hbox] at hdel
          exact deliver_roster I w id { (w.st id) with parked := ps } p.msg w1 a1 hdel
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [creditLive_roster, setActor_roster]
          rw [← hpark] at hdel
          exact deliver_roster I w id { (w.st id) with box := ms } m w1 a1 hdel
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [setActor_roster, creditLive_roster, setActor_roster]
          rw [← hpark] at hdel
          exact deliver_roster I w id { (w.st id) with box := ms } m w1 a1 hdel

theorem receivePrio_roster (I : Impl) (w w' : World) (id : InstId)
    (h : receivePrio I w id = some w') : w'.roster = w.roster := by
  obtain ⟨m, pre, suf, w1, a1, _, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  rw [hw', setActor_roster]
  exact deliver_roster I w id { (w.st id) with prio := pre ++ suf } m w1 a1 hdel

theorem finish_roster (I : Impl) (w w' : World) (id : InstId)
    (h : finishWait I w id = some w') : w'.roster = w.roster := by
  unfold finishWait at h
  by_cases hlive : (w.st id).life ≠ .alive
  · simp [hlive] at h
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | awaitEffect _ =>
      simp [hph] at h
      cases h
      exact setActor_roster _ _ _
    | awaitPeer _ =>
      simp [hph] at h
      cases h
      exact setActor_roster _ _ _
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem call_roster (w w' : World) (id : InstId) (h : callTimeout w id = some w') :
    w'.roster = w.roster := by
  unfold callTimeout at h
  dsimp at h
  split at h
  · simp at h
  · split at h
    · cases h
      exact setActor_roster _ _ _
    · cases h
      exact (setActor_roster _ _ _).trans (refund_call_roster w id _)
    · cases h
      exact setActor_roster _ _ _
    · simp at h

theorem execRun_grow (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (hid : id ∈ w.roster) : RosterGrow I w (execRun I w id a k) := by
  cases hbit : a.life == .alive with
  | false =>
    simp [execRun, hbit]
    exact RosterGrow.keep _ rfl
  | true =>
    cases hk : k.rest with
    | nil =>
      simp [execRun, hbit, hk]
      exact RosterGrow.keep _ (setActor_roster _ _ _)
    | cons e es =>
      cases e with
      | send dst label hint =>
        simp only [execRun, hbit, hk]
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr]
          exact RosterGrow.keep _ (by simp [noteStale_roster, setActor_roster])
        | some dstId =>
          simp only [hr]
          exact RosterGrow.keep _ (enqueue_roster w I.desc id dstId _ false _)
      | trySend dst label hint onFull onGone =>
        simp only [execRun, hbit, hk]
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr]
          exact RosterGrow.keep _ (by simp [noteStale_roster, setActor_roster])
        | some dstId =>
          simp
          by_cases hroom :
              ((w.st dstId).life = .alive ∧ (w.st dstId).parked = []) ∧
                (w.st dstId).box.length < capBulk I.desc w.N dstId
          · simp [hroom]
            exact RosterGrow.keep _ (enqueue_roster w I.desc id dstId
              { label := label, sender := id, callFrom := none, reliable := false } false (afterHead k))
          · simp [hroom]
            by_cases hliveT : (w.st dstId).life = .alive
            · simp [hliveT]
              exact RosterGrow.keep _ (setActor_roster _ _ _)
            · simp [hliveT]
              exact RosterGrow.keep _ (setActor_roster _ _ _)
      | call dst label hint onNotAdmitted onTimedOut =>
        simp only [execRun, hbit, hk]
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp only [hr]
          exact RosterGrow.keep _ (by simp [noteStale_roster, setActor_roster])
        | some dstId =>
          simp only [hr]
          exact RosterGrow.keep _ (enqueue_roster w I.desc id dstId _ true _)
      | reply =>
        simp only [execRun, hbit, hk]
        exact RosterGrow.keep _ (reply_roster w id k)
      | selfSchedule label =>
        simp only [execRun, hbit, hk]
        by_cases hhas : (a.prio.any (fun p => p.label == label)) = true
        · rw [hhas]
          exact RosterGrow.keep _ (setActor_roster _ _ _)
        · have hhasF : (a.prio.any (fun p => p.label == label)) = false := by
            cases hb : a.prio.any (fun p => p.label == label) with
            | false => rfl
            | true => exact absurd hb hhas
          rw [hhasF]
          by_cases hfit : prioLoad a.prio < capPrio I.desc w.N id
          · rw [if_pos hfit]
            exact RosterGrow.keep _ (setActor_roster _ _ _)
          · rw [if_neg hfit]
            exact RosterGrow.keep _ (crashWorld_roster _)
      | cell dst label value =>
        simp only [execRun, hbit, hk]
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp [hdirty]
          exact RosterGrow.keep _ (by simp [setCell, setActor_roster])
        · have hdirtyF : (w.cell dst label).dirty = false := by
            cases hb : (w.cell dst label).dirty with
            | false => rfl
            | true => exact absurd hb hdirty
          simp [hdirtyF]
          exact RosterGrow.keep _ (by simp [wakeReaders_roster, setCell, setActor_roster])
      | internal =>
        simp only [execRun, hbit, hk]
        exact RosterGrow.keep _ (setActor_roster _ _ _)
      | peer _ =>
        simp only [execRun, hbit, hk]
        exact RosterGrow.keep _ (setActor_roster _ _ _)
      | abort =>
        simp only [execRun, hbit, hk]
        exact RosterGrow.keep _ ((commit_roster _ _ _).trans (abortChildren_roster I.desc w id))
      | spawn child =>
        simp only [execRun, hbit, hk]
        cases hs : spawnChild I w id child with
        | none =>
          simp
          exact RosterGrow.keep _ (crashWorld_roster _)
        | some wB =>
          simp
          have hg := spawnChild_grow I w id child wB hid hs
          have hc := commit_roster wB id (proceed (wB.st id) (afterHead k))
          cases hg with
          | keep hr => exact RosterGrow.keep _ (hc.trans hr)
          | root template k0 g0 t ht hroot hros hfresh =>
            exact RosterGrow.root _ template k0 g0 t ht hroot (hc.trans hros) hfresh
          | child childName k0 g0 t parent ht hsup hmem hpeer hros =>
            exact RosterGrow.child _ childName k0 g0 t parent ht hsup hmem hpeer (hc.trans hros)
      | terminate =>
        simp only [execRun, hbit, hk]
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp
          exact RosterGrow.keep _ (crashWorld_roster _)
        | some t =>
          simp
          by_cases hcore : (t.multiplicity == .one) = true
          · rw [hcore]
            exact RosterGrow.keep _ (crashWorld_roster _)
          · have hcoreF : (t.multiplicity == .one) = false := by
              cases hb : t.multiplicity == .one with
              | false => rfl
              | true => exact absurd hb hcore
            simp [hcoreF]
            by_cases htree : (t.multiplicity == .perPeer) = true ∧ ¬ t.subtree = ""
            · simp [htree]
              exact RosterGrow.keep _
                ((shutdown_roster I.desc (dropDescendants I.desc w id) id).trans
                  (drop_roster I.desc w id))
            · simp [htree]
              by_cases hlone :
                  ((t.terminable = true ∧ t.subtree = "") ∧ hasParkedCall a.parked = false) ∧
                    hasChild I.desc w id = false
              · simp [hlone]
                exact RosterGrow.keep _ (shutdown_roster I.desc w id)
              · simp [hlone]
                by_cases hcasc :
                    ((t.terminable = true ∧ t.subtree = "") ∧ hasParkedCall a.parked = false) ∧
                      hasChild I.desc w id = true
                · simp [hcasc]
                  exact RosterGrow.keep _
                    ((shutdown_roster I.desc (dropDescendants I.desc w id) id).trans
                      (drop_roster I.desc w id))
                · simp [hcasc]
                  exact RosterGrow.keep _ (crashWorld_roster _)

theorem exec_grow (I : Impl) (w w' : World) (id : InstId) (hH : Hold I w)
    (h : execHead I w id = some w') : RosterGrow I w w' := by
  unfold execHead at h
  by_cases hlive : (w.st id).life ≠ .alive
  · simp [hlive] at h
  · simp [hlive] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      have hlife : (w.st id).life = .alive :=
        Classical.byContradiction fun hne => hlive hne
      have hid := hH.rostered id (by rw [hlife]; intro hbad; cases hbad)
      exact execRun_grow I w id (w.st id) k hid
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem step_grow (I : Impl) (w w' : World) (a : Action) (hH : Hold I w)
    (h : stepWorld I a w = some w') : RosterGrow I w w' := by
  cases a with
  | stutter =>
    simp only [stepWorld] at h
    split at h
    · simp at h
    · cases h
      exact RosterGrow.keep _ rfl
  | spawn template =>
    simp only [stepWorld] at h
    exact spawn_grow I w w' template h
  | exec id =>
    simp only [stepWorld] at h
    exact exec_grow I w w' id hH h
  | recvBulk id =>
    simp only [stepWorld] at h
    exact RosterGrow.keep _ (receiveBulk_roster I w w' id h)
  | recvPrio id =>
    simp only [stepWorld] at h
    exact RosterGrow.keep _ (receivePrio_roster I w w' id h)
  | finish id =>
    simp only [stepWorld] at h
    exact RosterGrow.keep _ (finish_roster I w w' id h)
  | ingress dst label =>
    simp only [stepWorld] at h
    exact RosterGrow.keep _ (ingress_phase I w w' dst label dst h).2.2.2.2.1
  | callTimeout id =>
    simp only [stepWorld] at h
    exact RosterGrow.keep _ (call_roster w w' id h)

/-- A step keeps one root actor per nonempty subtree key. A new root takes a
fresh key. A child of a per-peer stage is not a root. -/
theorem oneCohort_of_grow (I : Impl) (w w' : World) (hH : Hold I w)
    (h : OneCohort I.desc w.roster) (hg : RosterGrow I w w') :
    OneCohort I.desc w'.roster := by
  cases hg with
  | keep hr => exact oneCohort_same I.desc hr h
  | root template k g t ht _ hros hfresh =>
    rw [hros]
    refine oneCohort_snoc I.desc w.roster (InstId.peer template k g) h ?_
    intro n k' g' t' hid ht' _ hsub n2 g2 hmem htree
    have hids : InstId.peer template k g = InstId.peer n k' g' := hid
    cases hids
    have hteq : t' = t := by
      injection ht'.symm.trans ht
    rw [hteq] at htree hsub
    exact hfresh n2 g2 hmem htree hsub
  | child childName k g t parent ht hsup hmem hpeer hros =>
    rw [hros]
    refine oneCohort_snoc I.desc w.roster (InstId.peer childName k g) h ?_
    intro n k' g' t' hid ht' hr _ _ _ _ _
    have hids : InstId.peer childName k g = InstId.peer n k' g' := hid
    cases hids
    have hteq : t' = t := by
      injection ht'.symm.trans ht
    rw [hteq] at hr
    obtain ⟨s, hs, hmul⟩ := hH.role parent hmem
    have hper : s.multiplicity = .perPeer := by
      cases parent with
      | core _ =>
        rcases hpeer with ⟨_, hp⟩
        cases hp
      | peer _ _ _ =>
        simpa [tmb_role] using hmul
    have hrootF := child_not_root I.desc childName (tname parent) t s ht hs hsup hper
    rw [hrootF] at hr
    exact False.elim (by simp at hr)

theorem oneCohort_reachable (I : Impl) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : OneCohort I.desc w.roster := by
  induction hR with
  | init => exact oneCohort_init I N
  | step w w' a hprev ha ih =>
    have ⟨_, hstep⟩ := apply_step I a w w' ha
    exact oneCohort_of_grow I w w' (hold_reach I N w hG hprev) ih
      (step_grow I w w' a (hold_reach I N w hG hprev) hstep)

/-! A subtree member at one key walks its parent chain to that key's root. -/

/-- `isMember` names a per-peer template of that subtree. -/
theorem member_template (D : Description) (id : InstId) (sub : String) (k : Nat)
    (hsub : sub ≠ "") (hm : isMember D id sub k = true) :
    ∃ role g t, id = InstId.peer role k g ∧ templateOf D role = some t ∧ t.subtree = sub := by
  cases id with
  | core _ => simp [isMember] at hm
  | peer role ix g =>
    simp only [isMember, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hm
    rcases hm with ⟨⟨hk, _⟩, htree⟩
    subst hk
    unfold templateSubtree at htree
    cases ht : templateOf D role with
    | none =>
      simp [ht] at htree
      exact absurd htree hsub
    | some t =>
      simp only [ht] at htree
      exact ⟨role, g, t, rfl, ht, htree⟩

/-- A checked template of a nonempty subtree is per-peer. -/
theorem entry_of_graph (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) : subtreeEntry D t = none := by
  have hmap : D.templates.filterMap (subtreeEntry D) = [] :=
    (List.append_eq_nil_iff.mp (by simpa only [subtreeFails_entry] using hG.subtrees)).1
  exact filterMap_none (subtreeEntry D) D.templates hmap t (templateOf_mem D name t ht).1

theorem member_per (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hsub : t.subtree ≠ "") : t.multiplicity = .perPeer := by
  have hent := entry_of_graph D hG name t ht
  cases hmul : t.multiplicity with
  | perPeer => rfl
  | one => exact False.elim (subtreeEntry_not_one D t hsub hmul hent)

/-- A member that is not the subtree root names a per-peer supervisor in the
same subtree. A missing supervisor template fails `supervisorInSubtree`, and a
multiplicity-one supervisor would make this template the root. -/
theorem member_sup (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hsub : t.subtree ≠ "")
    (hrootF : rootOf D t = false) :
    ∃ supName ts, t.supervisor = some supName ∧ templateOf D supName = some ts ∧
      ts.multiplicity = .perPeer ∧ ts.subtree = t.subtree ∧ ts.name ≠ t.name := by
  have hmul := member_per D hG name t ht hsub
  have hent := entry_of_graph D hG name t ht
  cases hsup : t.supervisor with
  | none =>
    unfold rootOf at hrootF
    rw [hsup] at hrootF
    cases hrootF
  | some supName =>
    cases hts : templateOf D supName with
    | none =>
      have hsi := entry_sup_in D t hent hsub hmul (by simp [hsup])
      unfold supervisorInSubtree at hsi
      simp [hsup, hts] at hsi
    | some ts =>
      have hone : (ts.multiplicity == .one) = false := by
        simpa [rootOf, hsup, hts] using hrootF
      have hper : ts.multiplicity = .perPeer := by
        cases hmul : ts.multiplicity with
        | perPeer => rfl
        | one =>
          have hb : (ts.multiplicity == .one) = true := by
            rw [hmul]
            decide
          rw [hb] at hone
          cases hone
      obtain ⟨hsame, hdiff⟩ := per_sup_same D hG name t ht hmul supName hsup ts hts hper
      exact ⟨supName, ts, rfl, hts, hper, hsame, hdiff⟩

/-- Following the recorded parent reaches the one root of this subtree key.
The step is well-founded because a parent is not its child. -/
theorem member_ancestor (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w) (hH : Hold I w)
    (sub : String) (k : Nat) (id : InstId) (hsub : sub ≠ "")
    (hid : id ∈ w.roster) (hm : isMember I.desc id sub k = true) :
    ∃ root, root ∈ w.roster ∧ isMember I.desc root sub k = true ∧
      (∃ t, templateOf I.desc (tname root) = some t ∧ rootOf I.desc t = true) ∧
      (id = root ∨ StrictAncestor w id root) := by
  let D := I.desc
  let C : InstId → Prop := fun id =>
    id ∈ w.roster → isMember D id sub k = true →
      ∃ root, root ∈ w.roster ∧ isMember D root sub k = true ∧
        (∃ t, templateOf D (tname root) = some t ∧ rootOf D t = true) ∧
        (id = root ∨ StrictAncestor w id root)
  have hstep : ∀ id, (∀ parent, ParentEdge w id parent → C parent) → C id := by
    intro id ih hid hm
    obtain ⟨role, g, t, hidEq, ht, htree⟩ := member_template D id sub k hsub hm
    by_cases hroot : rootOf D t = true
    · refine ⟨id, hid, hm, ⟨t, ?_, hroot⟩, Or.inl rfl⟩
      rw [hidEq]
      simpa [tname] using ht
    · have hrootF : rootOf D t = false := by
        cases hbb : rootOf D t
        · rfl
        · exact absurd hbb hroot
      have hsubT : t.subtree ≠ "" := by rwa [← htree] at hsub
      obtain ⟨supName, ts, hsup, hts, hper, hsame, _⟩ :=
        member_sup D hG role t ht hsubT hrootF
      have hwired := hP id t hid (by rw [hidEq]; simpa [tname] using ht)
      rw [hsup] at hwired
      obtain ⟨p, hpar, hname, hkeyp⟩ := hwired
      have hhosted := hF.hosted id p hpar
      have hne : id ≠ p := by
        intro heq
        apply hSelf id
        rw [hpar, heq]
      cases p with
      | core cname =>
        obtain ⟨s, hs, hmul⟩ := hH.role (InstId.core cname) hhosted
        rw [hname] at hs
        have htsEq : s = ts := by
          injection hs.symm.trans hts
        rw [htsEq, hper] at hmul
        simp [tmb_role] at hmul
      | peer n pk pg =>
        have hn : n = supName := by simpa [tname] using hname
        have hkeyId : memberKey id = some k := by
          rw [hidEq]
          simp [memberKey]
        have hk : pk = k := by
          rw [hkeyId] at hkeyp
          injection hkeyp with hk
          exact hk.symm
        rw [hk] at hpar hhosted hne
        let parent := InstId.peer n k pg
        have hsubS : ts.subtree = sub := hsame.trans htree
        have htsN : templateOf D n = some ts := by
          simpa [hn] using hts
        have htreeP : templateSubtree D n = sub := by
          simp [templateSubtree, htsN, hsubS]
        have hneB : (sub != "") = true := by simp [bne_iff_ne, hsub]
        have hmP : isMember D parent sub k = true := by
          simp [isMember, parent, htreeP, hneB]
        have hparent := ih parent ⟨hpar, hne⟩ hhosted hmP
        obtain ⟨root, hmemR, hmR, hpack, hanc⟩ := hparent
        refine ⟨root, hmemR, hmR, hpack, ?_⟩
        cases hanc with
        | inl heq =>
          exact Or.inr (by simpa [heq] using
            (StrictAncestor.edge ⟨hpar, hne⟩ : StrictAncestor w id parent))
        | inr htail =>
          exact Or.inr (StrictAncestor.tail ⟨hpar, hne⟩ htail)
  exact (hF.wf).fix hstep id hid hm

/-- The root `member_ancestor` finds is the one root actor of that key. -/
theorem member_root_id (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hrootMem : InstId.peer name k g ∈ w.roster)
    (id : InstId) (hid : id ∈ w.roster) (hm : isMember I.desc id t.subtree k = true) :
    id = InstId.peer name k g ∨ StrictAncestor w id (InstId.peer name k g) := by
  obtain ⟨root, hmemR, hmR, ⟨tr, htr, hrootR⟩, hanc⟩ :=
    member_ancestor I hG w hF hP hSelf hH t.subtree k id hsub hid hm
  obtain ⟨roleR, gR, tr', hrEq, htr', hsubR⟩ :=
    member_template I.desc root t.subtree k hsub hmR
  have htrR : templateOf I.desc roleR = some tr := by
    simpa [hrEq, tname] using htr
  have hteq : tr' = tr := by
    injection htr'.symm.trans htrR
  rw [hteq] at hsubR
  obtain ⟨hn, hg⟩ := hOne t.subtree k name g roleR gR t tr hsub ht htrR rfl hsubR hroot hrootR
    hrootMem (by simpa [hrEq] using hmemR)
  have hrootId : root = InstId.peer name k g := by
    rw [hrEq, ← hn, ← hg]
  cases hanc with
  | inl heq =>
    exact Or.inl (heq.trans hrootId)
  | inr hs =>
    exact Or.inr (by simpa [hrootId] using hs)

/-- A subtree member is sealed with the root of its key. `sealedTogether` is the
test `mailInFlight` uses, so a root tombstone waits on this member's mail by
the same test as the root's own mail (`tomb_waits_on_descendant`). -/
theorem member_sealed (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hrootMem : InstId.peer name k g ∈ w.roster)
    (id : InstId) (hid : id ∈ w.roster) (hm : isMember I.desc id t.subtree k = true) :
    sealedTogether w (InstId.peer name k g) id = true := by
  cases member_root_id I hG w hF hP hSelf hH hOne name k g t ht hroot hsub hrootMem id hid hm with
  | inl heq =>
    simpa [sealedTogether, heq]
  | inr hs =>
    have hd := descends_of_strict w hF hs
    simp [sealedTogether, hd]

/-- Program mail from a subtree member keeps the dead root's tombstone on the
live parent. The member is the root or a recorded descendant, and
`descendant_mail_tomb` is `TombChain` on that chain. The queued tombstone is
what `slotTombstoneQueued` counts. -/
theorem member_mail_tomb (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hChain : TombChain w)
    (hcr : w.crashed = false) (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hrootMem : InstId.peer name k g ∈ w.roster)
    (hdead : (w.st (InstId.peer name k g)).life = .dead) (parent : InstId)
    (hpar : (w.st (InstId.peer name k g)).parent = some parent)
    (hlive : (w.st parent).life = .alive) (id : InstId) (hid : id ∈ w.roster)
    (hm : isMember I.desc id t.subtree k = true) (hf : mailInFlight w id = true) :
    slotTombstoneQueued w parent name k = true := by
  have hwho :=
    member_root_id I hG w hF hP hSelf hH hOne name k g t ht hroot hsub hrootMem id hid hm
  obtain ⟨m, hmPrio, htom, hs⟩ :=
    descendant_mail_tomb w hChain hF hcr (InstId.peer name k g) parent id hdead hpar hlive hwho hf
  exact slot_sees_tomb w parent name k g m hmPrio htom hs

/-- Workaround `lane_birth`: `birth_reachable` is stated where `Inv2` is proved,
and this file cannot import that. The induction is the same one. -/
theorem lane_birth (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) : BirthInv I.desc w := by
  induction hR with
  | init => exact birth_init I hG N
  | step w w' a prev ha ih =>
    exact birth_apply I hG a w w' ih (inv_reachable I N w hL prev).2.2.1
      (peer_role_reachable I hG N w prev) (core_reachable I hG N w prev) ha

/-- In a reachable world the parent chain is the one `TombChain` reads, so held
descendant mail of a dead root is a counted tombstone on the live parent. -/
theorem member_mail_tomb_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hcr : w.crashed = false)
    (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hrootMem : InstId.peer name k g ∈ w.roster)
    (hdead : (w.st (InstId.peer name k g)).life = .dead) (parent : InstId)
    (hpar : (w.st (InstId.peer name k g)).parent = some parent)
    (hlive : (w.st parent).life = .alive) (id : InstId) (hid : id ∈ w.roster)
    (hm : isMember I.desc id t.subtree k = true) (hf : mailInFlight w id = true) :
    slotTombstoneQueued w parent name k = true := by
  have hB := lane_birth I hL hG N w hR
  have hI := inv_reachable I N w hL hR
  exact member_mail_tomb I hG w hI.forest hB.parented hB.noSelf (hold_reach I N w hG hR)
    (oneCohort_reachable I hG N w hR) hI.seal.chain hcr name k g t ht hroot hsub hrootMem
    hdead parent hpar hlive id hid hm hf

/-! No step brings a roster actor back to life. A birth writes `.alive` on a fresh id. -/

theorem set_same_prev (w : World) (id i : InstId) (next : Actor)
    (hl : next.life = (w.st id).life) (h : ((setActor w id next).st i).life = .alive) :
    (w.st i).life = .alive :=
  (setActor_keeps_life w id i next hl).symm.trans h

theorem commit_prev (w : World) (id i : InstId) (next : Actor)
    (hl : next.life = (w.st id).life) (h : ((commitCont w id next).st i).life = .alive) :
    (w.st i).life = .alive := by
  unfold commitCont at h
  cases hcr : w.crashed with
  | true =>
    simp only [hcr, ite_true] at h
    exact h
  | false =>
    simp only [hcr, ite_false] at h
    exact set_same_prev w id i next hl h

theorem reply_prev (w : World) (sender : InstId) (k : Cont) (i : InstId)
    (h : ((performReply w sender k).st i).life = .alive) : (w.st i).life = .alive := by
  unfold performReply at h
  dsimp only at h
  cases hr : k.replyTo with
  | none =>
    simp only [hr] at h
    exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
  | some caller =>
    simp only [hr] at h
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      simp only [hph] at h
      split at h
      · have h1 := setActor_keeps_life w caller i (finishCall (w.st caller) ck .reply) (finishCall_life _ _ _)
        have h2 := setActor_keeps_life _ sender i
          (proceed ((setActor w caller (finishCall (w.st caller) ck .reply)).st sender) (afterHead k))
          (proceed_keeps_life _ _)
        exact (h2.trans h1).symm.trans h
      · exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | idle =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | run _ =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | parked _ _ _ =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | awaitEffect _ =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | awaitPeer _ =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h
    | crashed =>
      simp only [hph] at h
      exact set_same_prev w sender i _ (proceed_keeps_life _ _) h

theorem place_old_life (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hnext : ∀ u j, (next u).st j = u.st j) (i : InstId) (hi : i ∈ w.roster)
    (hlive : ((placePeer I w template k initial parent next).st i).life = .alive) :
    (w.st i).life = .alive := by
  let bornId := InstId.peer template k (maxGen w template k)
  have hne : i ≠ bornId := by
    intro heq
    rw [heq] at hi
    exact maxGen_notin w template k (by simpa [bornId] using hi)
  unfold placePeer at hlive
  rw [readCells_st] at hlive
  rw [setActor_other _ bornId i _ hne] at hlive
  rw [hnext] at hlive
  simpa using hlive

theorem spawnChild_old_life (I : Impl) (w : World) (parent : InstId) (child : String) (w' : World)
    (i : InstId) (hi : i ∈ w.roster) (h : spawnChild I w parent child = some w')
    (hlive : (w'.st i).life = .alive) : (w.st i).life = .alive := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = true
    · simp only [hgo, ite_true] at h
      cases parent with
      | core _ => simp at h
      | peer pn pk pg =>
        by_cases hblk : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = true
        · simp [hblk] at h
          cases h
          exact hlive
        · have hf : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblk
          simp only [hf, ite_false] at h
          cases h
          let bornId := InstId.peer child pk (maxGen w child pk)
          have hne : i ≠ bornId := by
            intro heq
            rw [heq] at hi
            exact maxGen_notin w child pk (by simpa [bornId] using hi)
          have hEq : ((admitBorn I w bornId
              { bornActor I.desc w child pk t.initial with parent := some (InstId.peer pn pk pg) }).st i).life =
              (w.st i).life := by
            simp [admitBorn, setActor, cellsSt, hne]
          exact hEq.symm.trans hlive
    · have hf :
          (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf, ite_false] at h
      by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hstay, ite_true] at h
        cases h
        exact hlive
      · have hstayF :
            (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hstay
        simp [hstayF] at h

theorem execRun_old_life (I : Impl) (w : World) (id : InstId) (k : Cont) (i : InstId)
    (hi : i ∈ w.roster) (h : ((execRun I w id (w.st id) k).st i).life = .alive) :
    (w.st i).life = .alive := by
  cases hbit : (w.st id).life == .alive with
  | false =>
    simp [execRun, hbit] at h
    exact h
  | true =>
    cases hk : k.rest with
    | nil =>
      simp [execRun, hbit, hk] at h
      exact set_same_prev w id i _ (by simp) h
    | cons e es =>
      cases e with
      | send dst label hint =>
        simp only [execRun, hbit, hk] at h
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr, noteStale_st] at h
          exact set_same_prev _ id i _ (by simp [proceed_keeps_life, noteStale_st]) h
        | some dstId =>
          simp only [hr] at h
          exact (enqueue_life w I.desc id dstId _ false _ i).symm.trans h
      | trySend dst label hint onFull onGone =>
        simp only [execRun, hbit, hk] at h
        cases hr : route w I.desc id dst with
        | none =>
          simp only [hr, noteStale_st] at h
          exact set_same_prev _ id i _ (by simp [proceed_keeps_life, noteStale_st]) h
        | some dstId =>
          simp only [hr] at h
          by_cases hroom :
              ((w.st dstId).life = .alive ∧ (w.st dstId).parked = []) ∧
                (w.st dstId).box.length < capBulk I.desc w.N dstId
          · simp [hroom] at h
            exact (enqueue_life w I.desc id dstId _ false _ i).symm.trans h
          · simp [hroom] at h
            by_cases hliveT : (w.st dstId).life = .alive
            · simp [hliveT] at h
              exact set_same_prev w id i _ (proceed_keeps_life _ _) h
            · simp [hliveT] at h
              exact set_same_prev w id i _ (proceed_keeps_life _ _) h
      | call dst label hint onNotAdmitted onTimedOut =>
        simp only [execRun, hbit, hk] at h
        cases hr : resolveId I.desc w id dst with
        | none =>
          simp only [hr, noteStale_st] at h
          exact set_same_prev _ id i _ (by simp [finishCall_life, issueCall, proceed_keeps_life, noteStale_st]) h
        | some dstId =>
          simp only [hr] at h
          exact (enqueue_life w I.desc id dstId _ true _ i).symm.trans h
      | reply =>
        simp only [execRun, hbit, hk] at h
        exact reply_prev w id k i h
      | selfSchedule label =>
        simp only [execRun, hbit, hk] at h
        by_cases hhas : ((w.st id).prio.any (fun p => p.label == label)) = true
        · simp [hhas] at h
          exact set_same_prev w id i _ (proceed_keeps_life _ _) h
        · have hhasF : ((w.st id).prio.any (fun p => p.label == label)) = false := by
            cases hb : (w.st id).prio.any (fun p => p.label == label) with
            | false => rfl
            | true => exact absurd hb hhas
          simp [hhasF] at h
          by_cases hfit : prioLoad (w.st id).prio < capPrio I.desc w.N id
          · simp [hfit] at h
            exact set_same_prev w id i _ (by simp [proceed_keeps_life]) h
          · simp [hfit] at h
            exact crashWorld_prev w i h
      | cell dst label value =>
        simp only [execRun, hbit, hk] at h
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp [hdirty] at h
          exact set_same_prev _ id i _ (by simp [setCell, proceed_keeps_life]) h
        · have hdirtyF : (w.cell dst label).dirty = false := by
            cases hb : (w.cell dst label).dirty with
            | false => rfl
            | true => exact absurd hb hdirty
          simp [hdirtyF] at h
          let written : Cell := { value := max (w.cell dst label).value value, dirty := true }
          let base := setActor (setCell w dst label written) id
            (proceed ((setCell w dst label written).st id) (afterHead k))
          have hw := wake_id_life I.desc base dst label id i (by simpa [base, written] using h)
          have hpre := set_same_prev (setCell w dst label written) id i
            (proceed ((setCell w dst label written).st id) (afterHead k))
            (by simp [setCell, proceed_keeps_life]) hw
          simpa [setCell, written] using hpre
      | internal =>
        simp only [execRun, hbit, hk] at h
        exact set_same_prev w id i _ (by simp) h
      | peer _ =>
        simp only [execRun, hbit, hk] at h
        exact set_same_prev w id i _ (by simp) h
      | abort =>
        simp only [execRun, hbit, hk] at h
        exact abortChildren_prev I.desc w id i
          (commit_prev _ id i _ (proceed_keeps_life _ _) h)
      | spawn child =>
        simp only [execRun, hbit, hk] at h
        cases hs : spawnChild I w id child with
        | none =>
          simp only [hs] at h
          exact crashWorld_prev w i h
        | some wB =>
          simp only [hs] at h
          exact spawnChild_old_life I w id child wB i hi hs
            (commit_prev wB id i _ (proceed_keeps_life _ _) h)
      | terminate =>
        simp only [execRun, hbit, hk] at h
        cases ht : templateOf I.desc (tname id) with
        | none =>
          simp only [ht] at h
          exact crashWorld_prev w i h
        | some t =>
          simp only [ht] at h
          by_cases hcore : (t.multiplicity == .one) = true
          · simp [hcore] at h
            exact crashWorld_prev w i h
          · have hcoreF : (t.multiplicity == .one) = false := by
              cases hb : t.multiplicity == .one with
              | false => rfl
              | true => exact absurd hb hcore
            simp [hcoreF] at h
            by_cases htree : (t.multiplicity == .perPeer) = true ∧ ¬ t.subtree = ""
            · simp [htree] at h
              exact terminate_prev I.desc w id (w.st id) i h
            · simp [htree] at h
              by_cases hlone :
                  ((t.terminable = true ∧ t.subtree = "") ∧ hasParkedCall (w.st id).parked = false) ∧
                    hasChild I.desc w id = false
              · simp [hlone] at h
                exact shutdownActor_prev I.desc w id i h
              · simp [hlone] at h
                by_cases hcasc :
                    ((t.terminable = true ∧ t.subtree = "") ∧ hasParkedCall (w.st id).parked = false) ∧
                      hasChild I.desc w id = true
                · simp [hcasc] at h
                  exact terminate_prev I.desc w id (w.st id) i h
                · simp [hcasc] at h
                  exact crashWorld_prev w i h

theorem exec_old_life (I : Impl) (w w' : World) (id i : InstId) (hi : i ∈ w.roster)
    (h : execHead I w id = some w') (hlive : (w'.st i).life = .alive) :
    (w.st i).life = .alive := by
  unfold execHead at h
  by_cases hnot : (w.st id).life ≠ .alive
  · simp [hnot] at h
  · simp [hnot] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact execRun_old_life I w id k i hi hlive
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem finish_old_life (I : Impl) (w w' : World) (id i : InstId)
    (h : finishWait I w id = some w') (hlive : (w'.st i).life = .alive) :
    (w.st i).life = .alive := by
  obtain ⟨k, _, hw⟩ := finish_proceed I w w' id h
  rw [hw] at hlive
  exact set_same_prev w id i _ (proceed_keeps_life _ _) hlive

theorem spawn_old_life (I : Impl) (w w' : World) (template : String) (i : InstId)
    (hi : i ∈ w.roster) (h : spawn I w template = some w')
    (hlive : (w'.st i).life = .alive) : (w.st i).life = .alive := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at h
        cases h
        exact place_old_life I w template (freshKey I.desc w t.subtree) t.initial
          (some (InstId.core name))
          (fun u => { u with nextKey := fun s =>
              if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
          (fun _ _ => rfl) i hi hlive
      | none =>
        rw [hsup] at h
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at h
          cases h
          exact place_old_life I w template (w.nextIx template) t.initial none
            (fun u => { u with nextIx := fun n =>
                if n = template then w.nextIx template + 1 else u.nextIx n })
            (fun _ _ => rfl) i hi hlive
        · have hf : (t.subtree == "") = false := by
            cases hb : t.subtree == "" with
            | false => rfl
            | true => exact absurd hb hempty
          rw [hf] at h
          cases h
          exact place_old_life I w template (freshKey I.desc w t.subtree) t.initial none
            (fun u => { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            (fun _ _ => rfl) i hi hlive
    · simp [hmay] at h

/-- An actor already on the roster is not born by the step. Alive afterwards
means alive before, which is `held_sub`'s life hypothesis. -/
theorem step_old_life (I : Impl) (w w' : World) (a : Action) (i : InstId)
    (hi : i ∈ w.roster) (h : stepWorld I a w = some w')
    (hlive : (w'.st i).life = .alive) : (w.st i).life = .alive := by
  cases a with
  | stutter =>
    simp only [stepWorld] at h
    split at h
    · simp at h
    · cases h
      exact hlive
  | spawn template =>
    simp only [stepWorld] at h
    exact spawn_old_life I w w' template i hi h hlive
  | exec id =>
    simp only [stepWorld] at h
    exact exec_old_life I w w' id i hi h hlive
  | recvBulk id =>
    simp only [stepWorld] at h
    exact (receiveBulk_keeps_life I w w' id i h).symm.trans hlive
  | recvPrio id =>
    simp only [stepWorld] at h
    exact (receivePrio_keeps_life I w w' id i h).symm.trans hlive
  | finish id =>
    simp only [stepWorld] at h
    exact finish_old_life I w w' id i h hlive
  | ingress dst label =>
    simp only [stepWorld] at h
    exact ((ingress_phase I w w' dst label i h).2.1).symm.trans hlive
  | callTimeout id =>
    simp only [stepWorld] at h
    exact (callTimeout_life w w' id i h).symm.trans hlive

/-- Parent links are all `descends` reads, so the same links give the same answer. -/
theorem descends_st (w w' : World) (fuel : Nat) (anc desc : InstId)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent) :
    descends fuel w' anc desc = descends fuel w anc desc := by
  induction fuel generalizing desc with
  | zero => rfl
  | succ fuel ih =>
    simp only [descends]
    by_cases heq : desc = anc
    · simp [heq]
    · have hbeq : (desc == anc) = false := by
        simpa [beq_iff_eq] using heq
      simp [hbeq]
      rw [hp desc]
      cases hpdesc : (w.st desc).parent with
      | none => rfl
      | some p =>
        by_cases hanc : p = anc
        · simp [hanc]
        · by_cases hself : p = desc
          · simp [hanc, hself]
          · simp [hanc, hself]
            exact ih p

theorem sealed_st (w w' : World) (sender host : InstId)
    (hros : w'.roster = w.roster) (hp : ∀ i, (w'.st i).parent = (w.st i).parent) :
    sealedTogether w' sender host = sealedTogether w sender host := by
  simp only [sealedTogether, hros]
  exact congrArg (fun b => (sender == host) || b) (descends_st w w' w.roster.length sender host hp)

theorem survives_st (w w' : World) (sender host : InstId)
    (hros : w'.roster = w.roster) (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : (w'.st host).life = (w.st host).life) :
    survivesSender w' sender host = survivesSender w sender host := by
  simp only [survivesSender, hlife, sealed_st w w' sender host hros hp]

theorem actor_holds_st (D : Description) (w w' : World) (host : InstId) (sub : String) (k : Nat)
    (a a' : Actor) (hros : w'.roster = w.roster)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : (w'.st host).life = (w.st host).life)
    (hbox : a'.box = a.box) (hprio : a'.prio = a.prio) (hpark : a'.parked = a.parked) :
    actorHoldsSubtreeMail D w' host sub k a' = actorHoldsSubtreeMail D w host sub k a := by
  simp only [actorHoldsSubtreeMail, hbox, hprio, hpark]
  have hsurv : ∀ sender, survivesSender w' sender host = survivesSender w sender host :=
    fun sender => survives_st w w' sender host hros hp hlife
  simp [hsurv]

theorem slot_mail_st (D : Description) (w w' : World) (name : String) (k : Nat)
    (hros : w'.roster = w.roster)
    (hst : ∀ i, (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (w'.st i).box = (w.st i).box ∧ (w'.st i).prio = (w.st i).prio ∧
      (w'.st i).parked = (w.st i).parked) :
    slotMailHeld D w' name k = slotMailHeld D w name k := by
  have hp : ∀ i, (w'.st i).parent = (w.st i).parent := fun i => (hst i).2.1
  let sub := templateSubtree D name
  unfold slotMailHeld
  have hsubMail : subtreeCoreMail D w' sub k = subtreeCoreMail D w sub k := by
    unfold subtreeCoreMail
    have hany : ∀ ids : List InstId,
        ids.any (fun host => actorHoldsSubtreeMail D w' host sub k (w'.st host)) =
        ids.any (fun host => actorHoldsSubtreeMail D w host sub k (w.st host)) := by
      intro ids
      induction ids with
      | nil => rfl
      | cons host ids ih =>
        simp only [List.any_cons, Bool.or_eq_true]
        have hh := actor_holds_st D w w' host sub k (w.st host) (w'.st host) hros hp (hst host).1
          (hst host).2.2.1 (hst host).2.2.2.1 (hst host).2.2.2.2
        rw [hh, ih]
    simpa [hros] using hany w.roster
  have hcore : slotCoreMail w' name k = slotCoreMail w name k := by
    unfold slotCoreMail actorHoldsSlotMail
    have hany : ∀ ids : List InstId,
        ids.any (fun host =>
          ((w'.st host).box.any (fun m => fromSlot name k m.sender && survivesSender w' m.sender host) ||
            (w'.st host).prio.any (fun m => fromSlot name k m.sender && survivesSender w' m.sender host) ||
            (w'.st host).parked.any (fun p =>
              (fromSlot name k p.sender && survivesSender w' p.sender host) ||
                (fromSlot name k p.msg.sender && survivesSender w' p.msg.sender host)))) =
        ids.any (fun host =>
          ((w.st host).box.any (fun m => fromSlot name k m.sender && survivesSender w m.sender host) ||
            (w.st host).prio.any (fun m => fromSlot name k m.sender && survivesSender w m.sender host) ||
            (w.st host).parked.any (fun p =>
              (fromSlot name k p.sender && survivesSender w p.sender host) ||
                (fromSlot name k p.msg.sender && survivesSender w p.msg.sender host)))) := by
      intro ids
      induction ids with
      | nil => rfl
      | cons host ids ih =>
        simp only [List.any_cons]
        have hsurv : ∀ s, survivesSender w' s host = survivesSender w s host :=
          fun s => survives_st w w' s host hros hp (hst host).1
        simp [hsurv, (hst host).2.2.1, (hst host).2.2.2.1, (hst host).2.2.2.2, ih]
    simpa [hros] using hany w.roster
  simp [sub, hsubMail, hcore]

/-- `held_sub` for a step that keeps the roster and every life, parent, and queue.
`finish` and `stutter` are such steps. A later send is not: it adds mail. -/
theorem held_of_fields (D : Description) (w w' : World) (name : String)
    (hros : w'.roster = w.roster)
    (hst : ∀ i, (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (w'.st i).box = (w.st i).box ∧ (w'.st i).prio = (w.st i).prio ∧
      (w'.st i).parked = (w.st i).parked) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  refine held_sub D w w' name ?_ ?_ ?_
  · intro id hid _
    simpa [hros] using hid
  · intro id _ hlive
    exact ((hst id).1).symm.trans hlive
  · intro k hmail
    exact Or.inl ((slot_mail_st D w w' name k hros hst).symm.trans hmail)

theorem held_stutter (I : Impl) (w w' : World) (name : String)
    (h : stepWorld I .stutter w = some w') :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  simp only [stepWorld] at h
  split at h
  · simp at h
  · cases h
    exact held_of_fields I.desc w w name (by rfl) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem held_finish (I : Impl) (w w' : World) (id : InstId) (name : String)
    (h : stepWorld I (.finish id) w = some w') :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  simp only [stepWorld] at h
  obtain ⟨k, _, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  refine held_of_fields I.desc w _ name (setActor_roster _ _ _) ?_
  intro i
  by_cases hi : i = id
  · subst hi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [setActor, proceed_keeps_life]
    · have hp : (proceed (w.st i) k).parent = (w.st i).parent := by
        unfold proceed; split <;> rfl
      simp [setActor, hp]
    · have hb : (proceed (w.st i) k).box = (w.st i).box := by
        unfold proceed; split <;> rfl
      simp [setActor, hb]
    · have hpr : (proceed (w.st i) k).prio = (w.st i).prio := by
        unfold proceed; split <;> rfl
      simp [setActor, hpr]
    · have hkpark : (proceed (w.st i) k).parked = (w.st i).parked := by
        unfold proceed; split <;> rfl
      simp [setActor, hkpark]
  · simp [setActor, hi]

/-! A receive or a timeout deletes mail, or moves one parked message into the
box. The sender does not change, and a host that survives afterwards survived
before, so a slot held afterwards was held before. -/

/-- Messages, priority messages, and parked entries whose sender satisfies
`pred` at a host that `surv` still counts. -/
def queuesHold (pred surv : InstId → Bool) (a : Actor) : Bool :=
  a.box.any (fun m => pred m.sender && surv m.sender) ||
    a.prio.any (fun m => pred m.sender && surv m.sender) ||
    a.parked.any (fun p =>
      (pred p.sender && surv p.sender) || (pred p.msg.sender && surv p.msg.sender))

theorem subtree_queues (D : Description) (w : World) (host : InstId) (sub : String) (k : Nat)
    (a : Actor) :
    actorHoldsSubtreeMail D w host sub k a =
      queuesHold (fromSubtree D sub k) (fun s => survivesSender w s host) a := by
  unfold actorHoldsSubtreeMail queuesHold
  rfl

theorem core_queues (w : World) (name : String) (k : Nat) (host : InstId) (a : Actor) :
    actorHoldsSlotMail w host name k a =
      queuesHold (fromSlot name k) (fun s => survivesSender w s host) a := by
  unfold actorHoldsSlotMail queuesHold
  rfl

theorem mem_any {α : Type} (p : α → Bool) (l : List α) (x : α) (hx : x ∈ l) (hp : p x = true) :
    l.any p = true :=
  _root_.List.any_eq_true.mpr ⟨x, hx, hp⟩

theorem any_imp (ids : List InstId) (p q : InstId → Bool)
    (h : ∀ i, i ∈ ids → p i = true → q i = true) (hp : ids.any p = true) : ids.any q = true := by
  induction ids with
  | nil => simp at hp
  | cons i ids ih =>
    simp only [List.any_cons, Bool.or_eq_true] at hp ⊢
    cases hp with
    | inl hi => exact Or.inl (h i (List.Mem.head _) hi)
    | inr ht => exact Or.inr (ih (fun j hj => h j (List.Mem.tail _ hj)) ht)

/-- A sender in the new box was in the old box, or was parked there. -/
theorem box_prev (held : InstId → Bool) (oldB : List Msg) (oldP : List Parked) (newB : List Msg)
    (h : ∀ m, m ∈ newB →
      (∃ m0, m0 ∈ oldB ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ oldP ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)))
    (hany : newB.any (fun m => held m.sender) = true) :
    oldB.any (fun m => held m.sender) = true ∨
      oldP.any (fun p => held p.sender || held p.msg.sender) = true := by
  obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hany
  rcases h m hm with ⟨m0, hm0, hs⟩ | ⟨p, hp, hs⟩
  · exact Or.inl (mem_any _ _ m0 hm0 (by simpa [hs] using hh))
  · apply Or.inr
    cases hs with
    | inl hps =>
      exact mem_any _ _ p hp (by
        have : held p.sender = true := by simpa [hps] using hh
        simp [this])
    | inr hpm =>
      exact mem_any _ _ p hp (by
        have : held p.msg.sender = true := by simpa [hpm] using hh
        simp [this])

theorem prio_prev (held : InstId → Bool) (oldP newP : List Msg)
    (h : ∀ m, m ∈ newP → ∃ m0, m0 ∈ oldP ∧ m0.sender = m.sender)
    (hany : newP.any (fun m => held m.sender) = true) :
    oldP.any (fun m => held m.sender) = true := by
  obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hany
  obtain ⟨m0, hm0, hs⟩ := h m hm
  exact mem_any _ _ m0 hm0 (by simpa [hs] using hh)

theorem park_prev (held : InstId → Bool) (oldP newP : List Parked)
    (h : ∀ p, p ∈ newP →
      (∃ q, q ∈ oldP ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∧
        (∃ q, q ∈ oldP ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)))
    (hany : newP.any (fun p => held p.sender || held p.msg.sender) = true) :
    oldP.any (fun q => held q.sender || held q.msg.sender) = true := by
  obtain ⟨p, hp, hh⟩ := _root_.List.any_eq_true.mp hany
  rcases h p hp with ⟨⟨q1, hq1, hwho1⟩, ⟨q2, hq2, hwho2⟩⟩
  simp only [Bool.or_eq_true] at hh
  cases hh with
  | inl hs =>
    cases hwho1 with
    | inl heq =>
      exact mem_any _ _ q1 hq1 (by
        have : held q1.sender = true := by simpa [heq] using hs
        simp [this])
    | inr heq =>
      exact mem_any _ _ q1 hq1 (by
        have : held q1.msg.sender = true := by simpa [heq] using hs
        simp [this])
  | inr hs =>
    cases hwho2 with
    | inl heq =>
      exact mem_any _ _ q2 hq2 (by
        have : held q2.sender = true := by simpa [heq] using hs
        simp [this])
    | inr heq =>
      exact mem_any _ _ q2 hq2 (by
        have : held q2.msg.sender = true := by simpa [heq] using hs
        simp [this])

theorem queues_prev (pred surv surv' : InstId → Bool) (a a' : Actor)
    (hsurv : ∀ s, surv' s = true → surv s = true)
    (hbox : ∀ m, m ∈ a'.box →
      (∃ m0, m0 ∈ a.box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ a.parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)))
    (hprio : ∀ m, m ∈ a'.prio → ∃ m0, m0 ∈ a.prio ∧ m0.sender = m.sender)
    (hpark : ∀ p, p ∈ a'.parked →
      (∃ q, q ∈ a.parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∧
        (∃ q, q ∈ a.parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)))
    (h : queuesHold pred surv' a' = true) : queuesHold pred surv a = true := by
  have hback : ∀ s, (pred s && surv' s) = true → (pred s && surv s) = true := by
    intro s hs
    simp only [Bool.and_eq_true] at hs
    simp [hs.1, hsurv s hs.2]
  unfold queuesHold at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (hboxA | hprioA) | hparkA
  · have hboxH : a'.box.any (fun m => pred m.sender && surv m.sender) = true := by
      obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hboxA
      exact mem_any _ _ m hm (hback _ hh)
    rcases box_prev (fun s => pred s && surv s) a.box a.parked a'.box hbox hboxH with hB | hP
    · exact Or.inl (Or.inl hB)
    · exact Or.inr hP
  · have hprioH : a'.prio.any (fun m => pred m.sender && surv m.sender) = true := by
      obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hprioA
      exact mem_any _ _ m hm (hback _ hh)
    exact Or.inl (Or.inr (prio_prev (fun s => pred s && surv s) a.prio a'.prio hprio hprioH))
  · have hparkH :
        a'.parked.any (fun p =>
          (pred p.sender && surv p.sender) || (pred p.msg.sender && surv p.msg.sender)) = true := by
      obtain ⟨p, hp, hh⟩ := _root_.List.any_eq_true.mp hparkA
      simp only [Bool.or_eq_true] at hh
      cases hh with
      | inl hs => exact mem_any _ _ p hp (by simp [hback _ hs])
      | inr hs => exact mem_any _ _ p hp (by simp [hback _ hs])
    exact Or.inr (park_prev (fun s => pred s && surv s) a.parked a'.parked hpark hparkH)

theorem slot_mail_prev (D : Description) (w w' : World) (name : String) (k : Nat)
    (hros : w'.roster = w.roster)
    (hst : ∀ i, (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent)
    (hbox : ∀ i m, m ∈ (w'.st i).box →
      (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)))
    (hprio : ∀ i m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender)
    (hpark : ∀ i p, p ∈ (w'.st i).parked →
      (∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∧
        (∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender))) :
    slotMailHeld D w' name k = true → slotMailHeld D w name k = true := by
  intro hmail
  have hp : ∀ i, (w'.st i).parent = (w.st i).parent := fun i => (hst i).2
  have hlife : ∀ i, (w'.st i).life = (w.st i).life := fun i => (hst i).1
  unfold slotMailHeld at hmail ⊢
  by_cases hempty : (templateSubtree D name == "") = true
  · simp only [hempty, ite_true] at hmail ⊢
    unfold slotCoreMail at hmail ⊢
    simp only [core_queues] at hmail ⊢
    rw [hros] at hmail
    refine any_imp w.roster _ _ ?_ hmail
    intro host _ hh
    exact queues_prev (fromSlot name k) (fun s => survivesSender w s host)
      (fun s => survivesSender w' s host) (w.st host) (w'.st host)
      (fun s hs => by simpa [survives_st w w' s host hros hp (hlife host)] using hs)
      (hbox host) (hprio host) (hpark host) hh
  · have hne : (templateSubtree D name == "") = false := by
      cases hb : templateSubtree D name == "" with
      | false => rfl
      | true => exact absurd hb hempty
    simp only [hne] at hmail ⊢
    unfold subtreeCoreMail at hmail ⊢
    simp only [subtree_queues] at hmail ⊢
    rw [hros] at hmail
    refine any_imp w.roster _ _ ?_ hmail
    intro host _ hh
    exact queues_prev (fromSubtree D (templateSubtree D name) k)
      (fun s => survivesSender w s host) (fun s => survivesSender w' s host)
      (w.st host) (w'.st host)
      (fun s hs => by simpa [survives_st w w' s host hros hp (hlife host)] using hs)
      (hbox host) (hprio host) (hpark host) hh

/-- `held_sub` when the roster, every life, and every parent stay, and every
sender queued afterwards was already queued on that host. -/
theorem held_of_mail (D : Description) (w w' : World) (name : String)
    (hros : w'.roster = w.roster)
    (hst : ∀ i, (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent)
    (hbox : ∀ i m, m ∈ (w'.st i).box →
      (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)))
    (hprio : ∀ i m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender)
    (hpark : ∀ i p, p ∈ (w'.st i).parked →
      (∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∧
        (∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender))) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  refine held_sub D w w' name ?_ ?_ ?_
  · intro id hid _
    simpa [hros] using hid
  · intro id _ hlive
    exact ((hst id).1).symm.trans hlive
  · intro k hm
    exact Or.inl (slot_mail_prev D w w' name k hros hst hbox hprio hpark hm)

theorem deliver_queues (I : Impl) (w : World) (id : InstId) (a : Actor) (m : Msg)
    (w1 : World) (a1 : Actor) (h : deliver I w id a m = some (w1, a1)) :
    a1.box = a.box ∧ a1.prio = a.prio ∧ a1.parked = a.parked ∧
      a1.life = a.life ∧ a1.parent = a.parent ∧ ∀ i, w1.st i = w.st i := by
  by_cases hl : a.life = .alive
  · have hne : (a.life ≠ .alive) = false := by simpa [hl]
    by_cases hnew : (m.tombstone && newerGeneration (readCells I.desc w id) m) = true
    · simp [deliver, hne, hnew] at h
      rcases h with ⟨hw, ha⟩
      subst hw
      subst ha
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun i => cellsSt I.desc w id i⟩
    · have hnewF : (m.tombstone && newerGeneration (readCells I.desc w id) m) = false := by
        cases hb : m.tombstone && newerGeneration (readCells I.desc w id) m with
        | false => rfl
        | true => exact absurd hb hnew
      simp [deliver, hne, hnewF] at h
      cases hf : findDeliver I (tname id) a.typestate m with
      | none =>
        simp only [hf] at h
        by_cases hkeep : m.callFrom.isSome = true ∨ m.tombstone = true
        · simp [hkeep] at h
        · simp [hkeep] at h
          rcases h with ⟨hw, ha⟩
          subst hw
          subst ha
          exact ⟨rfl, rfl, rfl, rfl, rfl, fun i => cellsSt I.desc w id i⟩
      | some tr =>
        simp only [hf] at h
        by_cases hacc : m.callFrom.isSome = true ∧ tr.acceptsCall = false
        · simp [hacc] at h
        · simp [hacc] at h
          rcases h with ⟨hw, ha⟩
          subst hw
          refine ⟨?_, ?_, ?_, ?_, ?_, fun i => cellsSt I.desc w id i⟩
          · rw [← ha]; split <;> rfl
          · rw [← ha]; split <;> rfl
          · rw [← ha]; split <;> rfl
          · rw [← ha]; split <;> rfl
          · rw [← ha]; split <;> rfl
  · have hne : (a.life ≠ .alive) = true := by simp [hl]
    simp [deliver, hne] at h

theorem creditLive_fields (w : World) (name : String) (sender i : InstId) :
    ((creditLive w name sender).st i).box = (w.st i).box ∧
      ((creditLive w name sender).st i).prio = (w.st i).prio ∧
      ((creditLive w name sender).st i).parked = (w.st i).parked ∧
      ((creditLive w name sender).st i).life = (w.st i).life ∧
      ((creditLive w name sender).st i).parent = (w.st i).parent := by
  unfold creditLive creditSender
  by_cases h : i = budgetHolder w sender
  · subst h
    simp [setActor, bumpToken]
  · simp [setActor, h, bumpToken]

theorem resume_fields (a : Actor) (c : Bool) (dst : InstId) :
    (resumeSender a c dst).box = a.box ∧ (resumeSender a c dst).prio = a.prio ∧
      (resumeSender a c dst).parked = a.parked ∧ (resumeSender a c dst).life = a.life ∧
      (resumeSender a c dst).parent = a.parent := by
  unfold resumeSender
  split
  · split
    · simp
    · unfold proceed
      split <;> simp
  · simp

/-- Crediting the live generation and resuming the parked sender do not move a
queue, a life, or a parent. -/
theorem resume_set_fields (w : World) (id : InstId) (c : Bool) (dst i : InstId) :
    ((setActor w id (resumeSender (w.st id) c dst)).st i).box = (w.st i).box ∧
      ((setActor w id (resumeSender (w.st id) c dst)).st i).prio = (w.st i).prio ∧
      ((setActor w id (resumeSender (w.st id) c dst)).st i).parked = (w.st i).parked ∧
      ((setActor w id (resumeSender (w.st id) c dst)).st i).life = (w.st i).life ∧
      ((setActor w id (resumeSender (w.st id) c dst)).st i).parent = (w.st i).parent := by
  by_cases h : i = id
  · subst h
    simp [setActor]
    exact resume_fields (w.st i) c dst
  · simp [setActor, h]

theorem eq_view (a b : Actor)
    (hl : b.life = a.life) (hp : b.parent = a.parent) (hpr : b.prio = a.prio)
    (hpa : b.parked = a.parked) (hb : b.box = a.box) :
    b.life = a.life ∧ b.parent = a.parent ∧
      (∀ m, m ∈ b.prio → ∃ m0, m0 ∈ a.prio ∧ m0.sender = m.sender) ∧
      (∀ p, p ∈ b.parked → p ∈ a.parked) ∧
      (∀ m, m ∈ b.box →
        (∃ m0, m0 ∈ a.box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ a.parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender))) := by
  refine ⟨hl, hp, ?_, ?_, ?_⟩
  · intro m hm
    exact ⟨m, by simpa [hpr] using hm, rfl⟩
  · intro p hpm
    simpa [hpa] using hpm
  · intro m hm
    exact Or.inl ⟨m, by simpa [hb] using hm, rfl⟩

theorem held_from_view (D : Description) (w w' : World) (name : String)
    (hros : w'.roster = w.roster)
    (hv : ∀ i,
      (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
        (∀ m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∧
        (∀ p, p ∈ (w'.st i).parked → p ∈ (w.st i).parked) ∧
        (∀ m, m ∈ (w'.st i).box →
          (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
            (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)))) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  refine held_of_mail D w w' name hros ?_ ?_ ?_ ?_
  · intro i
    exact ⟨(hv i).1, (hv i).2.1⟩
  · intro i m hm
    exact (hv i).2.2.2.2 m hm
  · intro i m hm
    exact (hv i).2.2.1 m hm
  · intro i p hp
    have hmem := (hv i).2.2.2.1 p hp
    exact ⟨⟨p, hmem, Or.inl rfl⟩, ⟨p, hmem, Or.inr rfl⟩⟩

theorem mem_skip_mid (m x : Msg) (pre suf : List Msg) (hx : x ∈ pre ++ suf) :
    x ∈ pre ++ m :: suf := by
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inr hx)

/-- A bulk receive deletes the delivered message or moves one parked message
into the box. Crediting and resuming do not touch a queue. -/
theorem bulk_view (I : Impl) (w w' : World) (id i : InstId)
    (h : receiveBulk I w id = some w') :
    (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (∀ m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∧
      (∀ p, p ∈ (w'.st i).parked → p ∈ (w.st i).parked) ∧
      (∀ m, m ∈ (w'.st i).box →
        (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender))) := by
  unfold receiveBulk at h
  by_cases hready : (w.st id).life ≠ .alive ∨ (w.st id).phase ≠ .idle
  · simp [hready] at h
  · simp [hready] at h
    cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [← hbox] at hdel
          have hq := deliver_queues I w id { (w.st id) with parked := ps } p.msg w1 a1 hdel
          have hres := resume_set_fields
            (creditLive (setActor w1 id a1) (tname id) p.msg.sender) p.sender p.isCall id i
          have hcred := creditLive_fields (setActor w1 id a1) (tname id) p.msg.sender i
          rcases hres with ⟨rb, rpr, rpa, rl, rpar⟩
          rcases hcred with ⟨cb, cpr, cpa, cl, cpar⟩
          rw [rl, rpar, rpr, rpa, rb, cl, cpar, cpr, cpa, cb]
          by_cases hi : i = id
          · subst hi
            simp [setActor]
            rcases hq with ⟨ab, apr, apa, al, apar, _⟩
            refine ⟨al, apar, ?_, ?_, ?_⟩
            · intro m hm
              exact ⟨m, by simpa [apr] using hm, rfl⟩
            · intro q hqmem
              rw [apa] at hqmem
              rw [hpark]
              exact List.mem_cons_of_mem p hqmem
            · intro m hm
              rw [ab] at hm
              exact Or.inl ⟨m, hm, rfl⟩
          · simp [setActor, hi]
            have hst := hq.2.2.2.2.2 i
            exact eq_view (w.st i) (w1.st i) (congrArg Actor.life hst) (congrArg Actor.parent hst)
              (congrArg Actor.prio hst) (congrArg Actor.parked hst) (congrArg Actor.box hst)
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [← hpark] at hdel
          have hq := deliver_queues I w id { (w.st id) with box := ms } m w1 a1 hdel
          have hcred := creditLive_fields (setActor w1 id a1) (tname id) m.sender i
          rcases hcred with ⟨cb, cpr, cpa, cl, cpar⟩
          rw [cl, cpar, cpr, cpa, cb]
          by_cases hi : i = id
          · subst hi
            simp [setActor]
            rcases hq with ⟨ab, apr, apa, al, apar, _⟩
            refine ⟨al, apar, ?_, ?_, ?_⟩
            · intro x hx
              exact ⟨x, by simpa [apr] using hx, rfl⟩
            · intro q hqmem
              rw [apa, hpark] at hqmem
              cases hqmem
            · intro x hx
              rw [ab] at hx
              exact Or.inl ⟨x, by rw [hbox]; exact List.mem_cons_of_mem m hx, rfl⟩
          · simp [setActor, hi]
            have hst := hq.2.2.2.2.2 i
            exact eq_view (w.st i) (w1.st i) (congrArg Actor.life hst) (congrArg Actor.parent hst)
              (congrArg Actor.prio hst) (congrArg Actor.parked hst) (congrArg Actor.box hst)
      | cons p ps =>
        simp [hbox, hpark] at h
        split at h
        · cases h
        · next w1 a1 hdel =>
          cases h
          rw [← hpark] at hdel
          have hq := deliver_queues I w id { (w.st id) with box := ms } m w1 a1 hdel
          let admitted := { a1 with box := a1.box ++ [p.msg], parked := ps }
          have hres := resume_set_fields
            (creditLive (setActor w1 id admitted) (tname id) m.sender) p.sender p.isCall id i
          have hcred := creditLive_fields (setActor w1 id admitted) (tname id) m.sender i
          rcases hres with ⟨rb, rpr, rpa, rl, rpar⟩
          rcases hcred with ⟨cb, cpr, cpa, cl, cpar⟩
          rw [rl, rpar, rpr, rpa, rb, cl, cpar, cpr, cpa, cb]
          by_cases hi : i = id
          · subst hi
            simp [setActor, admitted]
            rcases hq with ⟨ab, apr, apa, al, apar, _⟩
            refine ⟨al, apar, ?_, ?_, ?_⟩
            · intro x hx
              exact ⟨x, by simpa [apr] using hx, rfl⟩
            · intro q hqmem
              rw [hpark]
              exact List.mem_cons_of_mem p hqmem
            · intro x hx
              rw [ab] at hx
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx
              · exact Or.inl ⟨x, by rw [hbox]; exact List.mem_cons_of_mem m hx, rfl⟩
              · subst hx
                exact Or.inr ⟨p, by rw [hpark]; exact List.Mem.head _, Or.inr rfl⟩
          · simp [setActor, hi]
            have hst := hq.2.2.2.2.2 i
            exact eq_view (w.st i) (w1.st i) (congrArg Actor.life hst) (congrArg Actor.parent hst)
              (congrArg Actor.prio hst) (congrArg Actor.parked hst) (congrArg Actor.box hst)

theorem held_receive (I : Impl) (w w' : World) (id : InstId) (name : String)
    (h : stepWorld I (.recvBulk id) w = some w') :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  simp only [stepWorld] at h
  exact held_from_view I.desc w w' name (receiveBulk_roster I w w' id h)
    (fun i => bulk_view I w w' id i h)

theorem prio_view (I : Impl) (w w' : World) (id i : InstId)
    (h : receivePrio I w id = some w') :
    (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (∀ m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∧
      (∀ p, p ∈ (w'.st i).parked → p ∈ (w.st i).parked) ∧
      (∀ m, m ∈ (w'.st i).box →
        (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender))) := by
  obtain ⟨m, pre, suf, w1, a1, _, _, hprio, _, hdel, hw⟩ := receivePrio_spec I w w' id h
  have hq := deliver_queues I w id { (w.st id) with prio := pre ++ suf } m w1 a1 hdel
  rw [hw]
  by_cases hi : i = id
  · subst hi
    simp [setActor]
    rcases hq with ⟨ab, apr, apa, al, apar, _⟩
    refine ⟨al, apar, ?_, ?_, ?_⟩
    · intro x hx
      rw [apr] at hx
      exact ⟨x, by rw [hprio]; exact mem_skip_mid m x pre suf hx, rfl⟩
    · intro q hqmem
      rw [apa] at hqmem
      exact hqmem
    · intro x hx
      rw [ab] at hx
      exact Or.inl ⟨x, hx, rfl⟩
  · simp [setActor, hi]
    have hst := hq.2.2.2.2.2 i
    exact eq_view (w.st i) (w1.st i) (congrArg Actor.life hst) (congrArg Actor.parent hst)
      (congrArg Actor.prio hst) (congrArg Actor.parked hst) (congrArg Actor.box hst)

theorem held_prio (I : Impl) (w w' : World) (id : InstId) (name : String)
    (h : stepWorld I (.recvPrio id) w = some w') :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  simp only [stepWorld] at h
  exact held_from_view I.desc w w' name (receivePrio_roster I w w' id h)
    (fun i => prio_view I w w' id i h)

theorem detachBox_sender (a : Actor) (caller : InstId) (m : Msg) (hm : m ∈ (detachBox a caller).box) :
    ∃ m0, m0 ∈ a.box ∧ m0.sender = m.sender := by
  unfold detachBox at hm
  obtain ⟨m0, hm0, heq⟩ := _root_.List.mem_map.mp hm
  exact ⟨m0, hm0, by simpa [heq] using (detachMsg_sender caller m0).symm⟩

theorem detach_fields (a : Actor) (caller : InstId) (cid : Nat) :
    (detachReply (detachBox a caller) caller cid).life = a.life ∧
      (detachReply (detachBox a caller) caller cid).parent = a.parent ∧
      (detachReply (detachBox a caller) caller cid).prio = a.prio ∧
      (detachReply (detachBox a caller) caller cid).parked = a.parked ∧
      (∀ m, m ∈ (detachReply (detachBox a caller) caller cid).box →
        ∃ m0, m0 ∈ a.box ∧ m0.sender = m.sender) := by
  unfold detachReply
  split
  · refine ⟨by simp [detachBox], by simp [detachBox], by simp [detachBox], by simp [detachBox], ?_⟩
    intro m hm
    exact detachBox_sender a caller m (by simpa [detachBox] using hm)
  · refine ⟨by simp [detachBox], by simp [detachBox], by simp [detachBox], by simp [detachBox], ?_⟩
    intro m hm
    exact detachBox_sender a caller m hm

theorem finishCall_fields (a : Actor) (k : Cont) (r : CallResult) :
    (finishCall a k r).life = a.life ∧ (finishCall a k r).parent = a.parent ∧
      (finishCall a k r).prio = a.prio ∧ (finishCall a k r).parked = a.parked ∧
      (finishCall a k r).box = a.box := by
  unfold finishCall proceed
  split <;> simp

theorem proceed_fields (a : Actor) (k : Cont) :
    (proceed a k).life = a.life ∧ (proceed a k).parent = a.parent ∧
      (proceed a k).prio = a.prio ∧ (proceed a k).parked = a.parked ∧
      (proceed a k).box = a.box := by
  unfold proceed
  split <;> simp

theorem creditSender_fields (w : World) (name : String) (sender i : InstId) :
    ((creditSender w name sender).st i).box = (w.st i).box ∧
      ((creditSender w name sender).st i).prio = (w.st i).prio ∧
      ((creditSender w name sender).st i).parked = (w.st i).parked ∧
      ((creditSender w name sender).st i).life = (w.st i).life ∧
      ((creditSender w name sender).st i).parent = (w.st i).parent := by
  unfold creditSender
  by_cases h : i = sender
  · subst h
    simp [setActor, bumpToken]
  · simp [setActor, h, bumpToken]

theorem credit_fold_fields (w : World) (dst caller : InstId) (ps : List Parked) (i : InstId) :
    ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w).st i).life = (w.st i).life ∧
      ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w).st i).parent = (w.st i).parent ∧
      ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w).st i).prio = (w.st i).prio ∧
      ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w).st i).parked = (w.st i).parked ∧
      ((ps.foldl (fun w _ => creditSender w (tname dst) caller) w).st i).box = (w.st i).box := by
  induction ps generalizing w with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hc := creditSender_fields w (tname dst) caller i
    have h := ih (creditSender w (tname dst) caller)
    exact ⟨h.1.trans hc.2.2.2.1, h.2.1.trans hc.2.2.2.2, h.2.2.1.trans hc.2.1,
      h.2.2.2.1.trans hc.2.2.1, h.2.2.2.2.trans hc.1⟩

theorem refund_fields (w : World) (caller dst i : InstId) :
    ((refundParkedCall w caller dst).st i).life = (w.st i).life ∧
      ((refundParkedCall w caller dst).st i).parent = (w.st i).parent ∧
      ((refundParkedCall w caller dst).st i).prio = (w.st i).prio ∧
      ((refundParkedCall w caller dst).st i).box = (w.st i).box ∧
      (∀ p, p ∈ ((refundParkedCall w caller dst).st i).parked → p ∈ (w.st i).parked) := by
  have hlife := (refundCall_fields w caller dst i).2.1
  have hprio := (refund_call_frame w caller dst i).2.1
  have hpar := refund_call_parent w caller dst i
  have hbox := refundCall_box w caller dst i
  have hpark := (refundCall_fields w caller dst i).2.2.2
  refine ⟨hlife, hpar, hprio, hbox, ?_⟩
  intro p hp
  rw [hpark] at hp
  by_cases hi : i = dst
  · simp [hi] at hp
    simpa [hi] using hp.1
  · simp [hi] at hp
    exact hp

/-- A call timeout detaches the callee's box or deletes the parked call.
Neither step adds a sender. -/
theorem timeout_view (w w' : World) (id i : InstId) (h : callTimeout w id = some w') :
    (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (∀ m, m ∈ (w'.st i).prio → ∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∧
      (∀ p, p ∈ (w'.st i).parked → p ∈ (w.st i).parked) ∧
      (∀ m, m ∈ (w'.st i).box →
        (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender))) := by
  unfold callTimeout at h
  by_cases hlive : ((w.st id).life != .alive) = true
  · simp [hlive] at h
  · have hliveF : ((w.st id).life != .alive) = false := by
      cases hb : (w.st id).life != .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [hliveF] at h
    cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp [hph] at h
      cases h
      let cid := (w.st id).waitId
      let host := detachReply (detachBox (w.st dst) id) id cid
      let w1 := setActor w dst host
      have hd := detach_fields (w.st dst) id cid
      have hf := finishCall_fields (w1.st id) k .timedOut
      by_cases hi : i = id
      · simp [setActor, hi]
        by_cases heq : id = dst
        · simp [w1, host, setActor, heq, cid] at hd hf ⊢
          rcases hd with ⟨dl, dpar, dpr, dpa, dbox⟩
          rcases hf with ⟨fl, fpar, fpr, fpa, fb⟩
          refine ⟨fl.trans dl, fpar.trans dpar, ?_, ?_, ?_⟩
          · intro m hm
            rw [fpr, dpr] at hm
            exact ⟨m, hm, rfl⟩
          · intro p hp
            rw [fpa, dpa] at hp
            exact hp
          · intro m hm
            rw [fb] at hm
            exact Or.inl (dbox m hm)
        · simp [w1, setActor, heq] at hf ⊢
          exact eq_view (w.st id) (finishCall (w.st id) k .timedOut) hf.1 hf.2.1 hf.2.2.1
            hf.2.2.2.1 hf.2.2.2.2
      · simp [setActor, hi]
        by_cases hdst : i = dst
        · simp [w1, host, setActor, hdst]
          rcases hd with ⟨dl, dpar, dpr, dpa, dbox⟩
          refine ⟨dl, dpar, ?_, ?_, ?_⟩
          · intro m hm
            rw [dpr] at hm
            exact ⟨m, hm, rfl⟩
          · intro p hp
            rw [dpa] at hp
            exact hp
          · intro m hm
            exact Or.inl (dbox m hm)
        · simp [w1, setActor, hdst]
          exact ⟨fun m hm => ⟨m, hm, rfl⟩, fun m hm => Or.inl ⟨m, hm, rfl⟩⟩
    | parked dst c k =>
      by_cases hc : c = true
      · simp [hph, hc] at h
        cases h
        have hr := refund_fields w id dst i
        have hf := finishCall_fields ((refundParkedCall w id dst).st id) k .notAdmitted
        by_cases hi : i = id
        · simp [setActor, hi] at hr ⊢
          rcases hr with ⟨rl, rpar, rpr, rb, rpa⟩
          rcases hf with ⟨fl, fpar, fpr, fpa, fb⟩
          refine ⟨fl.trans rl, fpar.trans rpar, ?_, ?_, ?_⟩
          · intro m hm
            rw [fpr, rpr] at hm
            exact ⟨m, hm, rfl⟩
          · intro p hp
            rw [fpa] at hp
            exact rpa p hp
          · intro m hm
            rw [fb, rb] at hm
            exact Or.inl ⟨m, hm, rfl⟩
        · simp [setActor, hi]
          rcases hr with ⟨rl, rpar, rpr, rb, rpa⟩
          refine ⟨rl, rpar, ?_, rpa, ?_⟩
          · intro m hm
            rw [rpr] at hm
            exact ⟨m, hm, rfl⟩
          · intro m hm
            rw [rb] at hm
            exact Or.inl ⟨m, hm, rfl⟩
      · simp [hph, hc] at h
    | awaitPeer k =>
      simp [hph] at h
      cases h
      by_cases hi : i = id
      · simp [setActor, hi]
        have hp := proceed_fields (w.st id)
          { k with rest := k.onTimeout, toState := pickState k.toState k.toTimeout }
        exact eq_view (w.st id) _ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      · simp [setActor, hi]
        exact ⟨fun m hm => ⟨m, hm, rfl⟩, fun m hm => Or.inl ⟨m, hm, rfl⟩⟩
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem held_timeout (I : Impl) (w w' : World) (id : InstId) (name : String)
    (h : stepWorld I (.callTimeout id) w = some w') :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  simp only [stepWorld] at h
  exact held_from_view I.desc w w' name (call_roster w w' id h) (fun i => timeout_view w w' id i h)

/-! Ingress and an effect enqueue mail from the actor the guard already required
to be alive. `held_sub` asks for an alive generation of the template whose slot
the new message holds. That generation is the sender when the template has no
subtree, and the subtree's root when the sender is a member of a root template.
A child template that shares a nonempty subtree is not this fact: a sibling's
message holds that child's slot while every generation of the child is dead,
and the alive generation is the root of a different name. -/

/-- The sender test `slotMailHeld` uses for `name` at `k`. -/
def slotPred (D : Description) (name : String) (k : Nat) (id : InstId) : Bool :=
  let sub := templateSubtree D name
  if sub == "" then fromSlot name k id else fromSubtree D sub k id

theorem slotPred_empty (D : Description) (name : String) (k : Nat) (id : InstId)
    (hempty : templateSubtree D name = "") : slotPred D name k id = fromSlot name k id := by
  unfold slotPred
  have hb : (templateSubtree D name == "") = true := by simpa [beq_iff_eq] using hempty
  simp [hb]

theorem slotPred_root (D : Description) (name : String) (k : Nat) (id : InstId) (t : Template)
    (ht : templateOf D name = some t) (hsub : t.subtree ≠ "") :
    slotPred D name k id = isMember D id t.subtree k := by
  have htree : templateSubtree D name = t.subtree := by simp [templateSubtree, ht]
  unfold slotPred fromSubtree
  rw [htree]
  have hne : (t.subtree == "") = false := by
    cases hb : t.subtree == "" with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp hb) hsub
  simp [hne]

/-- A host that still survives a sender survived it before, when parents are
unchanged and a life that is alive afterwards was alive before. -/
theorem survives_back (w w' : World) (sender host : InstId)
    (hros : w'.roster = w.roster) (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : (w'.st host).life = .alive → (w.st host).life = .alive)
    (h : survivesSender w' sender host = true) : survivesSender w sender host = true := by
  simp only [survivesSender, Bool.and_eq_true] at h ⊢
  have hlive' : (w'.st host).life = .alive := by simpa [beq_iff_eq] using h.1
  refine ⟨by simpa [beq_iff_eq] using hlife hlive', ?_⟩
  have hseal := sealed_st w w' sender host hros hp
  rw [← hseal]
  cases hsb : sealedTogether w' sender host with
  | false => simp
  | true => simp [hsb] at h

theorem box_split (pred : InstId → Bool) (senders : InstId → Prop)
    (oldB : List Msg) (oldP : List Parked) (newB : List Msg)
    (h : ∀ m, m ∈ newB →
      (∃ m0, m0 ∈ oldB ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ oldP ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
        senders m.sender)
    (hany : newB.any (fun m => pred m.sender) = true) :
    oldB.any (fun m => pred m.sender) = true ∨
      oldP.any (fun p => pred p.sender || pred p.msg.sender) = true ∨
        ∃ s, senders s ∧ pred s = true := by
  obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hany
  rcases h m hm with ⟨m0, hm0, hs⟩ | ⟨p, hp, hs⟩ | hsend
  · exact Or.inl (mem_any _ _ m0 hm0 (by simpa [hs] using hh))
  · apply Or.inr ∘ Or.inl
    cases hs with
    | inl hps =>
      exact mem_any _ _ p hp (by
        have : pred p.sender = true := by simpa [hps] using hh
        simp [this])
    | inr hpm =>
      exact mem_any _ _ p hp (by
        have : pred p.msg.sender = true := by simpa [hpm] using hh
        simp [this])
  · exact Or.inr (Or.inr ⟨m.sender, hsend, hh⟩)

theorem prio_split (pred : InstId → Bool) (senders : InstId → Prop)
    (oldP newP : List Msg)
    (h : ∀ m, m ∈ newP → (∃ m0, m0 ∈ oldP ∧ m0.sender = m.sender) ∨ senders m.sender)
    (hany : newP.any (fun m => pred m.sender) = true) :
    oldP.any (fun m => pred m.sender) = true ∨ ∃ s, senders s ∧ pred s = true := by
  obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hany
  rcases h m hm with ⟨m0, hm0, hs⟩ | hsend
  · exact Or.inl (mem_any _ _ m0 hm0 (by simpa [hs] using hh))
  · exact Or.inr ⟨m.sender, hsend, hh⟩

theorem park_split (pred : InstId → Bool) (senders : InstId → Prop)
    (oldP newP : List Parked)
    (h : ∀ p, p ∈ newP →
      ((∃ q, q ∈ oldP ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨ senders p.sender) ∧
        ((∃ q, q ∈ oldP ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
          senders p.msg.sender))
    (hany : newP.any (fun p => pred p.sender || pred p.msg.sender) = true) :
    oldP.any (fun q => pred q.sender || pred q.msg.sender) = true ∨
      ∃ s, senders s ∧ pred s = true := by
  obtain ⟨p, hp, hh⟩ := _root_.List.any_eq_true.mp hany
  rcases h p hp with ⟨h1, h2⟩
  simp only [Bool.or_eq_true] at hh
  cases hh with
  | inl hs =>
    rcases h1 with ⟨q, hq, hwho⟩ | hsend
    · cases hwho with
      | inl heq =>
        exact Or.inl (mem_any _ _ q hq (by
          have : pred q.sender = true := by simpa [heq] using hs
          simp [this]))
      | inr heq =>
        exact Or.inl (mem_any _ _ q hq (by
          have : pred q.msg.sender = true := by simpa [heq] using hs
          simp [this]))
    · exact Or.inr ⟨p.sender, hsend, hs⟩
  | inr hs =>
    rcases h2 with ⟨q, hq, hwho⟩ | hsend
    · cases hwho with
      | inl heq =>
        exact Or.inl (mem_any _ _ q hq (by
          have : pred q.sender = true := by simpa [heq] using hs
          simp [this]))
      | inr heq =>
        exact Or.inl (mem_any _ _ q hq (by
          have : pred q.msg.sender = true := by simpa [heq] using hs
          simp [this]))
    · exact Or.inr ⟨p.msg.sender, hsend, hs⟩

/-- A queue held afterwards was held before, or one of `senders` satisfies `pred`. -/
theorem queues_split (pred surv surv' : InstId → Bool) (senders : InstId → Prop)
    (a a' : Actor) (hsurv : ∀ s, surv' s = true → surv s = true)
    (hbox : ∀ m, m ∈ a'.box →
      (∃ m0, m0 ∈ a.box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ a.parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
        senders m.sender)
    (hprio : ∀ m, m ∈ a'.prio →
      (∃ m0, m0 ∈ a.prio ∧ m0.sender = m.sender) ∨ senders m.sender)
    (hpark : ∀ p, p ∈ a'.parked →
      ((∃ q, q ∈ a.parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨
        senders p.sender) ∧
        ((∃ q, q ∈ a.parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
          senders p.msg.sender))
    (h : queuesHold pred surv' a' = true) :
    queuesHold pred surv a = true ∨ ∃ s, senders s ∧ pred s = true := by
  have hback : ∀ s, (pred s && surv' s) = true → (pred s && surv s) = true := by
    intro s hs
    simp only [Bool.and_eq_true] at hs
    simp [hs.1, hsurv s hs.2]
  unfold queuesHold at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (hboxA | hprioA) | hparkA
  · have hboxH : a'.box.any (fun m => pred m.sender && surv m.sender) = true := by
      obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hboxA
      exact mem_any _ _ m hm (hback _ hh)
    rcases box_split (fun s => pred s && surv s) senders a.box a.parked a'.box hbox hboxH with
      hB | hP | hS
    · exact Or.inl (Or.inl (Or.inl hB))
    · exact Or.inl (Or.inr hP)
    · obtain ⟨s, hs, hp⟩ := hS
      simp only [Bool.and_eq_true] at hp
      exact Or.inr ⟨s, hs, hp.1⟩
  · have hprioH : a'.prio.any (fun m => pred m.sender && surv m.sender) = true := by
      obtain ⟨m, hm, hh⟩ := _root_.List.any_eq_true.mp hprioA
      exact mem_any _ _ m hm (hback _ hh)
    rcases prio_split (fun s => pred s && surv s) senders a.prio a'.prio hprio hprioH with hP | hS
    · exact Or.inl (Or.inl (Or.inr hP))
    · obtain ⟨s, hs, hp⟩ := hS
      simp only [Bool.and_eq_true] at hp
      exact Or.inr ⟨s, hs, hp.1⟩
  · have hparkH :
        a'.parked.any (fun p =>
          (pred p.sender && surv p.sender) || (pred p.msg.sender && surv p.msg.sender)) = true := by
      obtain ⟨p, hp, hh⟩ := _root_.List.any_eq_true.mp hparkA
      simp only [Bool.or_eq_true] at hh
      cases hh with
      | inl hs => exact mem_any _ _ p hp (by simp [hback _ hs])
      | inr hs => exact mem_any _ _ p hp (by simp [hback _ hs])
    rcases park_split (fun s => pred s && surv s) senders a.parked a'.parked hpark hparkH with
      hP | hS
    · exact Or.inl (Or.inr hP)
    · obtain ⟨s, hs, hp⟩ := hS
      simp only [Bool.and_eq_true] at hp
      exact Or.inr ⟨s, hs, hp.1⟩

theorem any_split (ids : List InstId) (p q : InstId → Bool) (r : InstId → Prop)
    (h : ∀ i, i ∈ ids → p i = true → q i = true ∨ r i) (hp : ids.any p = true) :
    ids.any q = true ∨ ∃ i, i ∈ ids ∧ r i := by
  induction ids with
  | nil => simp at hp
  | cons i ids ih =>
    simp only [List.any_cons, Bool.or_eq_true] at hp ⊢
    cases hp with
    | inl hi =>
      cases h i (List.Mem.head _) hi with
      | inl hq => exact Or.inl (Or.inl hq)
      | inr hr => exact Or.inr ⟨i, List.Mem.head _, hr⟩
    | inr ht =>
      cases ih (fun j hj => h j (List.Mem.tail _ hj)) ht with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr =>
        obtain ⟨j, hj, hr⟩ := hr
        exact Or.inr ⟨j, List.Mem.tail _ hj, hr⟩

/-- Slot mail that appears after a step was already held, or a new sender
satisfies the slot's predicate. Parents are unchanged, and a host that is
alive afterwards was alive before. -/
theorem slot_split (D : Description) (w w' : World) (name : String) (k : Nat)
    (senders : InstId → Prop) (hros : w'.roster = w.roster)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : ∀ i, (w'.st i).life = .alive → (w.st i).life = .alive)
    (hbox : ∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).box →
      (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
        senders m.sender)
    (hprio : ∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).prio →
      (∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∨ senders m.sender)
    (hpark : ∀ i, i ∈ w.roster → ∀ p, p ∈ (w'.st i).parked →
      ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨
        senders p.sender) ∧
        ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
          senders p.msg.sender))
    (hmail : slotMailHeld D w' name k = true) :
    slotMailHeld D w name k = true ∨ ∃ s, senders s ∧ slotPred D name k s = true := by
  unfold slotMailHeld at hmail ⊢
  by_cases hempty : (templateSubtree D name == "") = true
  · simp only [hempty, ite_true] at hmail ⊢
    unfold slotCoreMail at hmail ⊢
    simp only [core_queues] at hmail ⊢
    rw [hros] at hmail
    have hsplit := any_split w.roster _ _ (fun _ => ∃ s, senders s ∧ fromSlot name k s = true)
      (fun host hhost hh => by
        have hsurv : ∀ s, survivesSender w' s host = true → survivesSender w s host = true :=
          fun s hs => survives_back w w' s host hros hp (hlife host) hs
        rcases queues_split (fromSlot name k) (fun s => survivesSender w s host)
            (fun s => survivesSender w' s host) senders (w.st host) (w'.st host) hsurv
            (hbox host hhost) (hprio host hhost) (hpark host hhost) hh with
          hold | ⟨s, hs, hp⟩
        · exact Or.inl hold
        · exact Or.inr ⟨s, hs, hp⟩) hmail
    rcases hsplit with hold | ⟨_, _, ⟨s, hs, hp⟩⟩
    · exact Or.inl hold
    · exact Or.inr ⟨s, hs, by
        unfold slotPred
        simp [hempty, hp]⟩
  · have hne : (templateSubtree D name == "") = false := by
      cases hb : templateSubtree D name == "" with
      | false => rfl
      | true => exact absurd hb hempty
    simp only [hne] at hmail ⊢
    unfold subtreeCoreMail at hmail ⊢
    simp only [subtree_queues] at hmail ⊢
    rw [hros] at hmail
    have hsplit := any_split w.roster _ _ (fun _ =>
        ∃ s, senders s ∧ fromSubtree D (templateSubtree D name) k s = true)
      (fun host hhost hh => by
        have hsurv : ∀ s, survivesSender w' s host = true → survivesSender w s host = true :=
          fun s hs => survives_back w w' s host hros hp (hlife host) hs
        rcases queues_split (fromSubtree D (templateSubtree D name) k)
            (fun s => survivesSender w s host) (fun s => survivesSender w' s host) senders
            (w.st host) (w'.st host) hsurv (hbox host hhost) (hprio host hhost)
            (hpark host hhost) hh with
          hold | ⟨s, hs, hp⟩
        · exact Or.inl hold
        · exact Or.inr ⟨s, hs, hp⟩) hmail
    rcases hsplit with hold | ⟨_, _, ⟨s, hs, hp⟩⟩
    · exact Or.inl hold
    · exact Or.inr ⟨s, hs, by
        unfold slotPred
        simp [hne, hp]⟩

/-- The conclusion of `held_sub`, for a step whose new mail comes from
`senders`. The alive generation is required only at a key that already has a
generation of `name` on the roster: that is the key `heldKeys` can record. -/
theorem held_kept (D : Description) (w w' : World) (name : String)
    (senders : InstId → Prop) (hros : w'.roster = w.roster)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : ∀ i, (w'.st i).life = .alive → (w.st i).life = .alive)
    (hbox : ∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).box →
      (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
        (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
        senders m.sender)
    (hprio : ∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).prio →
      (∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∨ senders m.sender)
    (hpark : ∀ i, i ∈ w.roster → ∀ p, p ∈ (w'.st i).parked →
      ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨
        senders p.sender) ∧
        ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
          senders p.msg.sender))
    (hwit : ∀ k g s, InstId.peer name k g ∈ w.roster → senders s →
      slotPred D name k s = true →
      ∃ id, id ∈ w.roster ∧ fromSlot name k id = true ∧ (w.st id).life = .alive) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  intro k hk
  rw [held_mem_bit] at hk ⊢
  rw [bitKeys_mem] at hk ⊢
  obtain ⟨id, hid, hbit, hkey⟩ := hk
  have hold : id ∈ w.roster := by simpa [hros] using hid
  cases id with
  | core _ => simp [loneBit] at hbit
  | peer n key g =>
    simp only [loneBit, Bool.and_eq_true] at hbit
    simp only [bitKey] at hkey
    have hnameb : (n == name) = true := hbit.1
    have hflag : ((w'.st (.peer n key g)).life == .alive || slotMailHeld D w' name key) = true :=
      hbit.2
    by_cases hpre : (w.st (.peer n key g)).life = .alive
    · refine ⟨.peer n key g, hold, ?_, hkey⟩
      simp only [loneBit, hnameb, Bool.true_and]
      rw [hkey] at hpre ⊢
      have hb : ((w.st (.peer n k g)).life == .alive) = true := by
        simpa [beq_iff_eq] using hpre
      simp [hb]
    · have hlive' : (w'.st (.peer n key g)).life ≠ .alive := by
        intro h
        exact hpre (hlife _ h)
      have hmailK : slotMailHeld D w' name key = true := by
        cases hbb : (w'.st (.peer n key g)).life == .alive with
        | true =>
          have : (w'.st (.peer n key g)).life = .alive := by simpa [beq_iff_eq] using hbb
          exact absurd this hlive'
        | false =>
          rw [hbb, Bool.false_or] at hflag
          exact hflag
      rw [hkey] at hmailK
      have hn : n = name := by simpa [beq_iff_eq] using hnameb
      have hgen : InstId.peer name k g ∈ w.roster := by simpa [hn, hkey] using hold
      rcases slot_split D w w' name k senders hros hp hlife hbox hprio hpark hmailK with
        holdMail | ⟨s, hs, hpred⟩
      · refine ⟨.peer n key g, hold, ?_, hkey⟩
        simp only [loneBit, hnameb, Bool.true_and]
        rw [hkey]
        simp [holdMail]
      · obtain ⟨id', hid', hfrom, halive⟩ := hwit k g s hgen hs hpred
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

/-- A live member of a root template's subtree has that root's generation alive.
The executing actor is the member. `member_root_id` names the one root of the
key, and `ancestor_alive` keeps it alive. -/
theorem root_sender_slot (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hrootMem : InstId.peer name k g ∈ w.roster)
    (s : InstId) (hs : s ∈ w.roster) (hlive : (w.st s).life = .alive)
    (hm : isMember I.desc s t.subtree k = true) :
    ∃ id, id ∈ w.roster ∧ fromSlot name k id = true ∧ (w.st id).life = .alive := by
  have hwho :=
    member_root_id I hG w hF hP hSelf hH hOne name k g t ht hroot hsub hrootMem s hs hm
  have halive : (w.st (InstId.peer name k g)).life = .alive := by
    cases hwho with
    | inl heq => simpa [heq] using hlive
    | inr hanc => exact ancestor_alive w hKids hcr hanc hlive
  refine ⟨InstId.peer name k g, hrootMem, ?_, halive⟩
  simp [fromSlot]

/-- Ingress keeps every parent, life, priority queue and parked queue, and the
only new box message is from the target. -/
theorem ingress_view (I : Impl) (w w' : World) (dst : InstId) (label : String) (i : InstId)
    (h : receiveIngress I w dst label = some w') :
    (w'.st i).life = (w.st i).life ∧ (w'.st i).parent = (w.st i).parent ∧
      (w'.st i).prio = (w.st i).prio ∧ (w'.st i).parked = (w.st i).parked ∧
      (∀ m, m ∈ (w'.st i).box → m ∈ (w.st i).box ∨ (i = dst ∧ m.sender = dst)) := by
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
            if hi : i = dst then
              subst hi
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp [setActor, chargeSender, bumpToken]
              · simp [setActor, chargeSender, bumpToken]
              · simp [setActor, chargeSender, bumpToken]
              · simp [setActor, chargeSender, bumpToken]
              · intro m hm
                simp [setActor, chargeSender, bumpToken, List.mem_append] at hm
                rcases hm with hm | hm
                · exact Or.inl hm
                · exact Or.inr ⟨rfl, by simp [hm]⟩
            else
              simp [setActor, hi]

/-- The target of a successful ingress is alive. That is the only sender the
step enqueues. -/
theorem ingress_sender (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') : (w.st dst).life = .alive :=
  (ingress_ready I w w' dst label h).1

private theorem ingress_cover (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') :
    w'.roster = w.roster ∧
      (∀ i, (w'.st i).parent = (w.st i).parent) ∧
      (∀ i, (w'.st i).life = .alive → (w.st i).life = .alive) ∧
      (∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).box →
        (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
          (m.sender = dst ∧ dst ∈ w.roster)) ∧
      (∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).prio →
        (∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∨ (m.sender = dst ∧ dst ∈ w.roster)) ∧
      (∀ i, i ∈ w.roster → ∀ p, p ∈ (w'.st i).parked →
        ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨
          (p.sender = dst ∧ dst ∈ w.roster)) ∧
          ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
            (p.msg.sender = dst ∧ dst ∈ w.roster))) := by
  refine ⟨(ingress_phase I w w' dst label dst h).2.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ingress_view I w w' dst label i h).2.1
  · intro i hlive
    exact ((ingress_view I w w' dst label i h).1).symm.trans hlive
  · intro i hi m hm
    rcases (ingress_view I w w' dst label i h).2.2.2.2 m hm with h0 | ⟨heq, hs⟩
    · exact Or.inl ⟨m, h0, rfl⟩
    · exact Or.inr (Or.inr ⟨hs, heq ▸ hi⟩)
  · intro i _ m hm
    exact Or.inl ⟨m, by simpa [(ingress_view I w w' dst label i h).2.2.1] using hm, rfl⟩
  · intro i _ p hp
    have hmem : p ∈ (w.st i).parked := by
      simpa [(ingress_view I w w' dst label i h).2.2.2.1] using hp
    exact ⟨Or.inl ⟨p, hmem, Or.inl rfl⟩, Or.inl ⟨p, hmem, Or.inr rfl⟩⟩

/-- Ingress does not grow the held keys of a template with no subtree. The new
message counts only when its sender, the live target, is a generation of that
template. -/
theorem held_ingress_empty (I : Impl) (w w' : World) (dst : InstId) (label name : String)
    (h : receiveIngress I w dst label = some w') (hempty : templateSubtree I.desc name = "") :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  rcases ingress_cover I w w' dst label h with ⟨hros, hp, hlife, hbox, hprio, hpark⟩
  refine held_kept I.desc w w' name (fun s => s = dst ∧ dst ∈ w.roster) hros hp hlife hbox hprio
    hpark ?_
  intro k _ s _ hs hpred
  rcases hs with ⟨hs, hmem⟩
  have hmemS : s ∈ w.roster := by rw [hs]; exact hmem
  have hfrom : fromSlot name k s = true := by
    rwa [slotPred_empty I.desc name k s hempty] at hpred
  have hlive : (w.st s).life = .alive := by
    rw [hs]
    exact ingress_sender I w w' dst label h
  exact ⟨s, hmemS, hfrom, hlive⟩

/-- Ingress does not grow the held keys of a root template. The target is
alive, and a member of the subtree is that key's root or one of its descendants,
so the root generation was already alive. -/
theorem held_ingress_root (I : Impl) (hG : GraphOk I.desc) (w w' : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (dst : InstId) (label name : String) (t : Template)
    (h : receiveIngress I w dst label = some w')
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  rcases ingress_cover I w w' dst label h with ⟨hros, hp, hlife, hbox, hprio, hpark⟩
  refine held_kept I.desc w w' name (fun s => s = dst ∧ dst ∈ w.roster) hros hp hlife hbox hprio
    hpark ?_
  intro k g s hgen hs hpred
  rcases hs with ⟨hs, hmem⟩
  have hmemS : s ∈ w.roster := by rw [hs]; exact hmem
  have hm : isMember I.desc s t.subtree k = true := by
    rwa [slotPred_root I.desc name k s t ht hsub] at hpred
  have hlive : (w.st s).life = .alive := by
    rw [hs]
    exact ingress_sender I w w' dst label h
  exact root_sender_slot I hG w hF hP hSelf hH hOne hKids hcr name k g t ht hroot hsub hgen s
    hmemS hlive hm

/-- `enqueueOrPark` does not touch a priority queue. -/
theorem enqueue_prio (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).prio = (w.st i).prio := by
  unfold enqueueOrPark
  dsimp only
  cases isCall <;> split <;> (try split) <;> (try split) <;>
    (by_cases hi : i = sender
     · subst hi
       simp [setActor, finishCall, proceed, issueCall, chargeSender, bumpToken]
       repeat' split <;> simp
     · by_cases hd : i = dst
       · subst hd
         simp [setActor, hi, issueCall, chargeSender, bumpToken]
       · simp [setActor, hi, hd])

/-- A box message after `enqueueOrPark` was already there, or it is the message
just enqueued and its sender is `msg.sender`. -/
theorem enqueue_box (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (m : Msg)
    (hm : m ∈ ((enqueueOrPark w D sender dst msg isCall k).st i).box) :
    m ∈ (w.st i).box ∨ m.sender = msg.sender := by
  cases isCall <;>
    (unfold enqueueOrPark at hm
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive] at hm
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom] at hm
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hm
           simp [setActor] at hm
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hm
             try rw [(proceed_fields _ k).2.2.2.2] at hm
             try simp [List.mem_append, List.mem_singleton] at hm
             rcases hm with hm | rfl
             · rw [hi]; exact Or.inl hm
             · exact Or.inr rfl
           · simp [setActor, hi] at hm
             exact Or.inl hm
         · rw [if_neg hsame] at hm
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hm
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hm
             try rw [(proceed_fields _ k).2.2.2.2] at hm
             try simp at hm
             rw [hi]
             exact Or.inl hm
           · by_cases hid : i = dst
             · simp [hid, hlive] at hm
               rw [if_neg hflip] at hm
               simp [List.mem_append, List.mem_singleton] at hm
               rcases hm with hm | rfl
               · rw [hid]; exact Or.inl hm
               · exact Or.inr rfl
             · rw [if_neg hi, if_neg hid] at hm
               exact Or.inl hm
       · simp [hroom] at hm
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hm
           simp [setActor] at hm
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hm
             try rw [(proceed_fields _ k).2.2.2.2] at hm
             try simp at hm
             rw [hi]
             exact Or.inl hm
           · simp [setActor, hi] at hm
             exact Or.inl hm
         · rw [if_neg hsame] at hm
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hm
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hm
             try rw [(proceed_fields _ k).2.2.2.2] at hm
             try simp at hm
             rw [hi]
             exact Or.inl hm
           · by_cases hid : i = dst
             · simp [hid, hlive] at hm
               try rw [if_neg hflip] at hm
               try simp at hm
               rw [hid]
               exact Or.inl hm
             · rw [if_neg hi, if_neg hid] at hm
               exact Or.inl hm
     · rw [if_pos hlive] at hm
       by_cases hi : i = sender
       · simp [hi, setActor, issueCall, finishCall] at hm
         try rw [(proceed_fields _ k).2.2.2.2] at hm
         try rw [(proceed_fields _ (selectCall k _)).2.2.2.2] at hm
         try simp at hm
         rw [hi]
         exact Or.inl hm
       · simp [setActor, hi] at hm
         exact Or.inl hm)

/-- A parked entry after `enqueueOrPark` was already parked, or it is the entry
just stored for this send: its sender is the executor and its message keeps
`msg.sender`. -/
theorem enqueue_park (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (p : Parked)
    (hp : p ∈ ((enqueueOrPark w D sender dst msg isCall k).st i).parked) :
    p ∈ (w.st i).parked ∨ p.sender = sender ∧ p.msg.sender = msg.sender := by
  cases isCall <;>
    (unfold enqueueOrPark at hp
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive] at hp
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom] at hp
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hp
           simp [setActor] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp at hp
             rw [hi]
             exact Or.inl hp
           · simp [setActor, hi] at hp
             exact Or.inl hp
         · rw [if_neg hsame] at hp
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp at hp
             rw [hi]
             exact Or.inl hp
           · by_cases hid : i = dst
             · simp [hid, hlive] at hp
               rw [if_neg hflip] at hp
               simp at hp
             · rw [if_neg hi, if_neg hid] at hp
               exact Or.inl hp
       · simp [hroom] at hp
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hp
           simp [setActor] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall, List.mem_append, List.mem_singleton] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp [List.mem_append, List.mem_singleton] at hp
             rcases hp with hp | rfl
             · rw [hi]; exact Or.inl hp
             · exact Or.inr ⟨rfl, rfl⟩
           · simp [setActor, hi] at hp
             exact Or.inl hp
         · rw [if_neg hsame] at hp
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             rw [hi]
             exact Or.inl hp
           · by_cases hid : i = dst
             · simp [hid, hlive, List.mem_append, List.mem_singleton] at hp
               try rw [if_neg hflip] at hp
               try simp [List.mem_append, List.mem_singleton] at hp
               rcases hp with hp | rfl
               · rw [hid]; exact Or.inl hp
               · exact Or.inr ⟨rfl, rfl⟩
             · rw [if_neg hi, if_neg hid] at hp
               exact Or.inl hp
     · rw [if_pos hlive] at hp
       by_cases hi : i = sender
       · simp [hi, setActor, issueCall, finishCall] at hp
         try rw [(proceed_fields _ k).2.2.2.1] at hp
         try rw [(proceed_fields _ (selectCall k _)).2.2.2.1] at hp
         try simp at hp
         rw [hi]
         exact Or.inl hp
       · simp [setActor, hi] at hp
         exact Or.inl hp)

/-- Equal queues, the same roster and parents, and no resurrection keep every
held key. A crash is the life half: alive afterwards was alive before. -/
theorem held_queues_eq (D : Description) (w w' : World) (name : String)
    (hros : w'.roster = w.roster)
    (hp : ∀ i, (w'.st i).parent = (w.st i).parent)
    (hlife : ∀ i, (w'.st i).life = .alive → (w.st i).life = .alive)
    (hbox : ∀ i, (w'.st i).box = (w.st i).box)
    (hprio : ∀ i, (w'.st i).prio = (w.st i).prio)
    (hpark : ∀ i, (w'.st i).parked = (w.st i).parked) :
    ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name := by
  refine held_kept D w w' name (fun _ => False) hros hp hlife ?_ ?_ ?_ ?_
  · intro i hi m hm
    exact Or.inl ⟨m, by simpa [hbox i] using hm, rfl⟩
  · intro i hi m hm
    exact Or.inl ⟨m, by simpa [hprio i] using hm, rfl⟩
  · intro i hi p hp
    have hmem : p ∈ (w.st i).parked := by simpa [hpark i] using hp
    exact ⟨Or.inl ⟨p, hmem, Or.inl rfl⟩, Or.inl ⟨p, hmem, Or.inr rfl⟩⟩
  · intro _ _ _ _ hs _
    exact False.elim hs

theorem crash_queues (w : World) (i : InstId) :
    ((crashWorld w).st i).box = (w.st i).box ∧ ((crashWorld w).st i).prio = (w.st i).prio ∧
      ((crashWorld w).st i).parked = (w.st i).parked ∧
      ((crashWorld w).st i).parent = (w.st i).parent := by
  simp only [crashWorld]
  by_cases hmem : decide (i ∈ w.roster) = true
  · simp [hmem, crashActor]
    split <;> simp
  · simp [hmem]

theorem held_crash (D : Description) (w : World) (name : String) :
    ∀ k, k ∈ heldKeys D (crashWorld w) name → k ∈ heldKeys D w name := by
  refine held_queues_eq D w (crashWorld w) name rfl (crashWorld_parent w) (crashWorld_prev w) ?_ ?_ ?_
  · intro i; exact (crash_queues w i).1
  · intro i; exact (crash_queues w i).2.1
  · intro i; exact (crash_queues w i).2.2.1

/-- `enqueueOrPark` keeps the roster, parents and lives. A new box or parked
message is `msg`, whose sender is the executor `sender`. Priority mail is
untouched. -/
theorem enqueue_cover (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (hmsg : msg.sender = sender) :
    let w' := enqueueOrPark w D sender dst msg isCall k
    w'.roster = w.roster ∧
      (∀ i, (w'.st i).parent = (w.st i).parent) ∧
      (∀ i, (w'.st i).life = .alive → (w.st i).life = .alive) ∧
      (∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).box →
        (∃ m0, m0 ∈ (w.st i).box ∧ m0.sender = m.sender) ∨
          (∃ p, p ∈ (w.st i).parked ∧ (p.sender = m.sender ∨ p.msg.sender = m.sender)) ∨
          m.sender = sender) ∧
      (∀ i, i ∈ w.roster → ∀ m, m ∈ (w'.st i).prio →
        (∃ m0, m0 ∈ (w.st i).prio ∧ m0.sender = m.sender) ∨ m.sender = sender) ∧
      (∀ i, i ∈ w.roster → ∀ p, p ∈ (w'.st i).parked →
        ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.sender ∨ q.msg.sender = p.sender)) ∨
          p.sender = sender) ∧
          ((∃ q, q ∈ (w.st i).parked ∧ (q.sender = p.msg.sender ∨ q.msg.sender = p.msg.sender)) ∨
            p.msg.sender = sender)) := by
  refine ⟨enqueue_roster w D sender dst msg isCall k, enqueue_parent w D sender dst msg isCall k, ?_, ?_, ?_, ?_⟩
  · intro i h
    exact (enqueue_life w D sender dst msg isCall k i).symm.trans h
  · intro i _ m hm
    rcases enqueue_box w D sender dst msg isCall k i m hm with hm | hs
    · exact Or.inl ⟨m, hm, rfl⟩
    · exact Or.inr (Or.inr (hs.trans hmsg))
  · intro i _ m hm
    exact Or.inl ⟨m, by simpa [enqueue_prio w D sender dst msg isCall k i] using hm, rfl⟩
  · intro i _ p hp
    rcases enqueue_park w D sender dst msg isCall k i p hp with hp | ⟨hse, hms⟩
    · exact ⟨Or.inl ⟨p, hp, Or.inl rfl⟩, Or.inl ⟨p, hp, Or.inr rfl⟩⟩
    · exact ⟨Or.inr hse, Or.inr (hms.trans hmsg)⟩

/-- A send from an actor that is already alive does not grow the held keys of a
template with no subtree. The message counts only when that actor is a
generation of the template. -/
theorem held_enqueue_empty (D : Description) (w : World) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (name : String) (hmsg : msg.sender = sender)
    (hlive : (w.st sender).life = .alive) (hmem : sender ∈ w.roster)
    (hempty : templateSubtree D name = "") :
    ∀ key, key ∈ heldKeys D (enqueueOrPark w D sender dst msg isCall k) name →
      key ∈ heldKeys D w name := by
  rcases enqueue_cover w D sender dst msg isCall k hmsg with ⟨hros, hp, hlife, hbox, hprio, hpark⟩
  refine held_kept D w _ name (fun s => s = sender) hros hp hlife hbox hprio hpark ?_
  intro key _ s _ hs hpred
  have hfrom : fromSlot name key s = true := by
    rwa [slotPred_empty D name key s hempty] at hpred
  have hliveS : (w.st s).life = .alive := by simpa [hs] using hlive
  have hmemS : s ∈ w.roster := by simpa [hs] using hmem
  exact ⟨s, hmemS, hfrom, hliveS⟩

/-- A send from an actor that is already alive does not grow the held keys of a
root template. The actor is a member of the subtree or outside it. A member is
the root or a descendant, so that root generation was already alive. -/
theorem held_enqueue_root (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (sender dst : InstId) (msg : Msg) (isCall : Bool) (k : Cont) (name : String)
    (t : Template) (hmsg : msg.sender = sender)
    (hlive : (w.st sender).life = .alive) (hmem : sender ∈ w.roster)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (enqueueOrPark w I.desc sender dst msg isCall k) name →
      key ∈ heldKeys I.desc w name := by
  rcases enqueue_cover w I.desc sender dst msg isCall k hmsg with ⟨hros, hp, hlife, hbox, hprio, hpark⟩
  refine held_kept I.desc w _ name (fun s => s = sender) hros hp hlife hbox hprio hpark ?_
  intro key g s hgen hs hpred
  have hm : isMember I.desc s t.subtree key = true := by
    rwa [slotPred_root I.desc name key s t ht hsub] at hpred
  have hliveS : (w.st s).life = .alive := by simpa [hs] using hlive
  have hmemS : s ∈ w.roster := by simpa [hs] using hmem
  exact root_sender_slot I hG w hF hP hSelf hH hOne hKids hcr name key g t ht hroot hsub hgen s
    hmemS hliveS hm

/-- `setActor` of an actor that keeps queues, life and parent keeps them for every id. -/
theorem phase_queues (w : World) (id : InstId) (a : Actor) (i : InstId)
    (hb : a.box = (w.st id).box) (hpr : a.prio = (w.st id).prio)
    (hpa : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent)
    (hl : a.life = (w.st id).life) :
    ((setActor w id a).st i).box = (w.st i).box ∧
      ((setActor w id a).st i).prio = (w.st i).prio ∧
      ((setActor w id a).st i).parked = (w.st i).parked ∧
      ((setActor w id a).st i).parent = (w.st i).parent ∧
      ((setActor w id a).st i).life = (w.st i).life := by
  by_cases hi : i = id
  · subst hi
    simp [setActor, hb, hpr, hpa, hpar, hl]
  · simp [setActor, hi]

theorem held_phase (D : Description) (w : World) (id : InstId) (a : Actor) (name : String)
    (hb : a.box = (w.st id).box) (hpr : a.prio = (w.st id).prio)
    (hpa : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent)
    (hl : a.life = (w.st id).life) :
    ∀ k, k ∈ heldKeys D (setActor w id a) name → k ∈ heldKeys D w name := by
  refine held_queues_eq D w _ name (setActor_roster _ _ _) ?_ ?_ ?_ ?_ ?_
  · intro i
    exact (phase_queues w id a i hb hpr hpa hpar hl).2.2.2.1
  · intro i h
    exact ((phase_queues w id a i hb hpr hpa hpar hl).2.2.2.2).symm.trans h
  · intro i
    exact (phase_queues w id a i hb hpr hpa hpar hl).1
  · intro i
    exact (phase_queues w id a i hb hpr hpa hpar hl).2.1
  · intro i
    exact (phase_queues w id a i hb hpr hpa hpar hl).2.2.1

/-- Noting a stale route does not change the actor map, so a following `setActor`
of an unchanged actor keeps every held key. -/
theorem held_noted (D : Description) (w : World) (id dstId : InstId) (dst : String) (a : Actor)
    (name : String) (hb : a.box = (w.st id).box) (hpr : a.prio = (w.st id).prio)
    (hpa : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent)
    (hl : a.life = (w.st id).life) :
    ∀ k, k ∈ heldKeys D (setActor (noteStale w id dst) id a) name → k ∈ heldKeys D w name := by
  have hst : ∀ i, ((noteStale w id dst).st i) = w.st i := fun i => noteStale_st w id dst i
  refine held_queues_eq D w _ name (setActor_roster _ _ _) ?_ ?_ ?_ ?_ ?_
  · intro i
    exact ((phase_queues (noteStale w id dst) id a i
      (hb.trans (by simp [hst id])) (hpr.trans (by simp [hst id]))
      (hpa.trans (by simp [hst id])) (hpar.trans (by simp [hst id]))
      (hl.trans (by simp [hst id]))).2.2.2.1).trans (by simp [hst i])
  · intro i h
    have hq := phase_queues (noteStale w id dst) id a i
      (hb.trans (by simp [hst id])) (hpr.trans (by simp [hst id]))
      (hpa.trans (by simp [hst id])) (hpar.trans (by simp [hst id]))
      (hl.trans (by simp [hst id]))
    exact (hst i ▸ hq.2.2.2.2).symm.trans h
  · intro i
    exact ((phase_queues (noteStale w id dst) id a i
      (hb.trans (by simp [hst id])) (hpr.trans (by simp [hst id]))
      (hpa.trans (by simp [hst id])) (hpar.trans (by simp [hst id]))
      (hl.trans (by simp [hst id]))).1).trans (by simp [hst i])
  · intro i
    exact ((phase_queues (noteStale w id dst) id a i
      (hb.trans (by simp [hst id])) (hpr.trans (by simp [hst id]))
      (hpa.trans (by simp [hst id])) (hpar.trans (by simp [hst id]))
      (hl.trans (by simp [hst id]))).2.1).trans (by simp [hst i])
  · intro i
    exact ((phase_queues (noteStale w id dst) id a i
      (hb.trans (by simp [hst id])) (hpr.trans (by simp [hst id]))
      (hpa.trans (by simp [hst id])) (hpar.trans (by simp [hst id]))
      (hl.trans (by simp [hst id]))).2.2.1).trans (by simp [hst i])

/-- A `send` from an alive actor does not grow the held keys of an empty-subtree
template or of a root template. The route's message is sent by that actor. A
missing route changes no queue. -/
theorem held_send (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (dst label : String) (hint : Nat) (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = .send dst label hint :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  simp only [execRun, hbit, hk] at hkK
  cases hr : route w I.desc id dst with
  | none =>
    simp only [hr, noteStale_st] at hkK
    exact held_noted I.desc w id id dst (proceed (w.st id) (afterHead k)) name
      (proceed_fields _ _).2.2.2.2 (proceed_fields _ _).2.2.1 (proceed_fields _ _).2.2.2.1
      (proceed_fields _ _).2.1 (proceed_fields _ _).1 key hkK
  | some dstId =>
    simp only [hr] at hkK
    let msg : Msg := { label := label, sender := id, callFrom := none }
    cases hkind with
    | inl hempty =>
      exact held_enqueue_empty I.desc w id dstId msg false (afterHead k) name rfl hlive hmem
        hempty key hkK
    | inr hroot =>
      obtain ⟨t, ht, hrootT, hsub⟩ := hroot
      exact held_enqueue_root I hG w hF hP hSelf hH hOne hKids hcr id dstId msg false
        (afterHead k) name t rfl hlive hmem ht hrootT hsub key hkK

/-- An admitted `trySend` is a send of an unreliable copy from the same alive
actor. A missing route, a full lane and a dead target change no queue. -/
theorem held_try (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (dst label : String) (hint : Nat) (onFull onGone : List Eff)
    (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = .trySend dst label hint onFull onGone :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  simp only [execRun, hbit, hk] at hkK
  cases hr : route w I.desc id dst with
  | none =>
    simp only [hr, noteStale_st] at hkK
    exact held_noted I.desc w id id dst
      (proceed (w.st id) { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone })
      name (proceed_fields _ _).2.2.2.2 (proceed_fields _ _).2.2.1 (proceed_fields _ _).2.2.2.1
      (proceed_fields _ _).2.1 (proceed_fields _ _).1 key hkK
  | some dstId =>
    simp only [hr] at hkK
    by_cases hroom :
        ((w.st dstId).life = .alive ∧ (w.st dstId).parked = []) ∧
          (w.st dstId).box.length < capBulk I.desc w.N dstId
    · simp [hroom] at hkK
      let msg : Msg := { label := label, sender := id, callFrom := none, reliable := false }
      cases hkind with
      | inl hempty =>
        exact held_enqueue_empty I.desc w id dstId msg false (afterHead k) name rfl hlive hmem
          hempty key hkK
      | inr hroot =>
        obtain ⟨t, ht, hrootT, hsub⟩ := hroot
        exact held_enqueue_root I hG w hF hP hSelf hH hOne hKids hcr id dstId msg false
          (afterHead k) name t rfl hlive hmem ht hrootT hsub key hkK
    · simp [hroom] at hkK
      by_cases hliveT : (w.st dstId).life = .alive
      · simp [hliveT] at hkK
        exact held_phase I.desc w id
          (proceed (w.st id) { afterHead k with rest := onFull, toState := pickState (afterHead k).toState (afterHead k).toFull })
          name (proceed_fields _ _).2.2.2.2 (proceed_fields _ _).2.2.1
          (proceed_fields _ _).2.2.2.1 (proceed_fields _ _).2.1 (proceed_fields _ _).1 key hkK
      · simp [hliveT] at hkK
        exact held_phase I.desc w id
          (proceed (w.st id) { afterHead k with rest := onGone, toState := pickState (afterHead k).toState (afterHead k).toGone })
          name (proceed_fields _ _).2.2.2.2 (proceed_fields _ _).2.2.1
          (proceed_fields _ _).2.2.2.1 (proceed_fields _ _).2.1 (proceed_fields _ _).1 key hkK

/-- A `call` from an alive actor enqueues one message from that actor, or, when
the role does not resolve, finishes the call without queueing it. -/
theorem held_call (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (dst label : String) (hint : Nat)
    (onNotAdmitted onTimedOut : List Eff) (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = .call dst label hint onNotAdmitted onTimedOut :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  simp only [execRun, hbit, hk] at hkK
  let kWait : Cont := { afterHead k with onNotAdmitted := onNotAdmitted, onTimedOut := onTimedOut }
  cases hr : resolveId I.desc w id dst with
  | none =>
    simp only [hr, noteStale_st] at hkK
    exact held_noted I.desc w id id dst
      (finishCall (issueCall (w.st id)) kWait .notAdmitted) name
      (finishCall_fields _ _ _).2.2.2.2 (finishCall_fields _ _ _).2.2.1
      (finishCall_fields _ _ _).2.2.2.1 (finishCall_fields _ _ _).2.1
      (finishCall_fields _ _ _).1 key hkK
  | some dstId =>
    simp only [hr] at hkK
    let msg : Msg := { label := label, sender := id, callFrom := some id }
    cases hkind with
    | inl hempty =>
      exact held_enqueue_empty I.desc w id dstId msg true kWait name rfl hlive hmem hempty key hkK
    | inr hroot =>
      obtain ⟨t, ht, hrootT, hsub⟩ := hroot
      exact held_enqueue_root I hG w hF hP hSelf hH hOne hKids hcr id dstId msg true kWait
        name t rfl hlive hmem ht hrootT hsub key hkK

theorem upsert_mem (prio : List Msg) (msg m : Msg) (hm : m ∈ upsertPrio prio msg) :
    m ∈ prio ∨ m = msg := by
  unfold upsertPrio at hm
  by_cases h : (prio.any (fun p => p.label == msg.label)) = true
  · simp [h] at hm
    exact Or.inl hm
  · simp [h, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact Or.inl hm
    · exact Or.inr rfl

/-- One actor's priority lane gains messages from a single alive sender. Every
other queue is unchanged, so an empty subtree or a root template gains no held
key. -/
theorem held_one_prio (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (a : Actor) (name : String)
    (hb : a.box = (w.st id).box) (hpa : a.parked = (w.st id).parked)
    (hpar : a.parent = (w.st id).parent) (hl : a.life = (w.st id).life)
    (hpr : ∀ m, m ∈ a.prio →
      (∃ m0, m0 ∈ (w.st id).prio ∧ m0.sender = m.sender) ∨ m.sender = id)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (setActor w id a) name → key ∈ heldKeys I.desc w name := by
  refine held_kept I.desc w _ name (fun s => s = id) (setActor_roster _ _ _) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    by_cases hi : i = id
    · subst hi
      simp [setActor, hpar]
    · simp [setActor, hi]
  · intro i h
    by_cases hi : i = id
    · subst hi
      exact hl.symm.trans (by simpa [setActor] using h)
    · simpa [setActor, hi] using h
  · intro i _ m hm
    by_cases hi : i = id
    · subst hi
      exact Or.inl ⟨m, by simpa [setActor, hb] using hm, rfl⟩
    · exact Or.inl ⟨m, by simpa [setActor, hi] using hm, rfl⟩
  · intro i _ m hm
    by_cases hi : i = id
    · rw [hi]
      exact hpr m (by simpa [setActor, hi] using hm)
    · exact Or.inl ⟨m, by simpa [setActor, hi] using hm, rfl⟩
  · intro i _ p hp
    by_cases hi : i = id
    · rw [hi]
      have hmemP : p ∈ (w.st id).parked := by simpa [setActor, hi, hpa] using hp
      exact ⟨Or.inl ⟨p, hmemP, Or.inl rfl⟩, Or.inl ⟨p, hmemP, Or.inr rfl⟩⟩
    · have hmemP : p ∈ (w.st i).parked := by simpa [setActor, hi] using hp
      exact ⟨Or.inl ⟨p, hmemP, Or.inl rfl⟩, Or.inl ⟨p, hmemP, Or.inr rfl⟩⟩
  · intro key g s hgen hs hpred
    cases hkind with
    | inl hempty =>
      have hfrom : fromSlot name key s = true := by
        rwa [slotPred_empty I.desc name key s hempty] at hpred
      exact ⟨s, by simpa [hs] using hmem, hfrom, by simpa [hs] using hlive⟩
    | inr hroot =>
      obtain ⟨t, ht, hrootT, hsub⟩ := hroot
      have hm : isMember I.desc s t.subtree key = true := by
        rwa [slotPred_root I.desc name key s t ht hsub] at hpred
      exact root_sender_slot I hG w hF hP hSelf hH hOne hKids hcr name key g t ht hrootT hsub
        hgen s (by simpa [hs] using hmem) (by simpa [hs] using hlive) hm

/-- `selfSchedule` either leaves the lane, appends one wake from the running
actor, or crashes without queueing it. -/
theorem held_self (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (label : String) (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = .selfSchedule label :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  simp only [execRun, hbit, hk] at hkK
  by_cases hhas : ((w.st id).prio.any (fun p => p.label == label)) = true
  · simp [hhas] at hkK
    exact held_phase I.desc w id (proceed (w.st id) (afterHead k)) name
      (proceed_fields _ _).2.2.2.2 (proceed_fields _ _).2.2.1 (proceed_fields _ _).2.2.2.1
      (proceed_fields _ _).2.1 (proceed_fields _ _).1 key hkK
  · have hhasF : ((w.st id).prio.any (fun p => p.label == label)) = false := by
      cases hb : (w.st id).prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hhas
    simp [hhasF] at hkK
    by_cases hfit : prioLoad (w.st id).prio < capPrio I.desc w.N id
    · simp [hfit] at hkK
      let msg : Msg :=
        { label := label, sender := id, callFrom := none, reliable := true, mid := (w.st id).nextMid }
      let a := proceed { (w.st id) with prio := upsertPrio (w.st id).prio msg, nextMid := (w.st id).nextMid + 1 } (afterHead k)
      have hpr : ∀ m, m ∈ a.prio →
          (∃ m0, m0 ∈ (w.st id).prio ∧ m0.sender = m.sender) ∨ m.sender = id := by
        intro m hm
        have hm' : m ∈ upsertPrio (w.st id).prio msg := by
          simpa [a, (proceed_fields _ _).2.2.1] using hm
        rcases upsert_mem _ _ _ hm' with hm | rfl
        · exact Or.inl ⟨m, hm, rfl⟩
        · exact Or.inr rfl
      exact held_one_prio I hG w hF hP hSelf hH hOne hKids hcr id a name
        (by simp [a, (proceed_fields _ _).2.2.2.2])
        (by simp [a, (proceed_fields _ _).2.2.2.1])
        (by simp [a, (proceed_fields _ _).2.1])
        (by simp [a, (proceed_fields _ _).1])
        hpr hlive hmem hkind key hkK
    · simp [hfit] at hkK
      exact held_crash I.desc w name key hkK

/-- Priority mail added on top of `w0` is either already there or sent by `writer`.
Box, parked, parent and roster stay put, and a life that is alive afterwards was
alive before. -/
structure PrioExt (w0 w : World) (writer : InstId) : Prop where
  ros : w.roster = w0.roster
  par : ∀ i, (w.st i).parent = (w0.st i).parent
  life : ∀ i, (w.st i).life = .alive → (w0.st i).life = .alive
  box : ∀ i, (w.st i).box = (w0.st i).box
  park : ∀ i, (w.st i).parked = (w0.st i).parked
  prio : ∀ i m, m ∈ (w.st i).prio →
    (∃ m0, m0 ∈ (w0.st i).prio ∧ m0.sender = m.sender) ∨ m.sender = writer

theorem PrioExt.refl (w : World) (writer : InstId) : PrioExt w w writer where
  ros := rfl
  par := fun _ => rfl
  life := fun _ h => h
  box := fun _ => rfl
  park := fun _ => rfl
  prio := fun _ m hm => Or.inl ⟨m, hm, rfl⟩

theorem PrioExt.trans {w0 w w' : World} {writer : InstId}
    (h1 : PrioExt w0 w writer) (h2 : PrioExt w w' writer) : PrioExt w0 w' writer where
  ros := h2.ros.trans h1.ros
  par := fun i => (h2.par i).trans (h1.par i)
  life := fun i h => h1.life i (h2.life i h)
  box := fun i => (h2.box i).trans (h1.box i)
  park := fun i => (h2.park i).trans (h1.park i)
  prio := fun i m hm => by
    rcases h2.prio i m hm with ⟨m0, hm0, hs⟩ | hs
    · rcases h1.prio i m0 hm0 with ⟨m1, hm1, hs1⟩ | hw
      · exact Or.inl ⟨m1, hm1, hs1.trans hs⟩
      · exact Or.inr (hs.symm.trans hw)
    · exact Or.inr hs

theorem offer_ext (D : Description) (w : World) (host : InstId) (msg : Msg) (writer : InstId)
    (hmsg : msg.sender = writer) : PrioExt w (offerPrio D w host msg) writer := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp [hfull]
    exact {
      ros := rfl
      par := crashWorld_parent w
      life := crashWorld_prev w
      box := fun i => (crash_queues w i).1
      park := fun i => (crash_queues w i).2.2.1
      prio := fun i m hm => Or.inl ⟨m, by simpa [(crash_queues w i).2.1] using hm, rfl⟩
    }
  · simp [hfull]
    refine {
      ros := setActor_roster _ _ _
      par := ?_
      life := ?_
      box := ?_
      park := ?_
      prio := ?_
    }
    · intro i
      by_cases hi : i = host
      · rw [hi]; simp [setActor]
      · simp [setActor, hi]
    · intro i h
      by_cases hi : i = host
      · simpa [setActor, hi] using h
      · simpa [setActor, hi] using h
    · intro i
      by_cases hi : i = host
      · rw [hi]; simp [setActor]
      · simp [setActor, hi]
    · intro i
      by_cases hi : i = host
      · rw [hi]; simp [setActor]
      · simp [setActor, hi]
    · intro i m hm
      by_cases hi : i = host
      · simp [setActor, hi, List.mem_append] at hm
        rcases hm with hm | rfl
        · refine Or.inl ⟨m, ?_, rfl⟩
          rw [hi]
          exact hm
        · exact Or.inr hmsg
      · exact Or.inl ⟨m, by simpa [setActor, hi] using hm, rfl⟩

theorem try_ext (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId) :
    PrioExt w (tryWake D w dstId label writer) writer := by
  unfold tryWake
  by_cases hskip :
      ((w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip]
    exact PrioExt.refl _ _
  · simp [hskip]
    exact offer_ext D w dstId _ writer rfl

theorem wake_fold_ext (D : Description) (ids : List InstId) (w0 w : World) (dst label : String)
    (writer : InstId) (h : PrioExt w0 w writer) :
    PrioExt w0 (ids.foldl (fun acc id => tryWake D acc id label writer) w) writer := by
  induction ids generalizing w with
  | nil => simpa using h
  | cons j js ih =>
    rw [List.foldl_cons]
    exact ih _ (h.trans (try_ext D w j label writer))

theorem wake_ext (D : Description) (w : World) (dst label : String) (writer : InstId) :
    PrioExt w (wakeReaders D w dst label writer) writer := by
  unfold wakeReaders readersOf
  exact wake_fold_ext D _ w w dst label writer (PrioExt.refl _ _)

theorem held_prio_ext (I : Impl) (hG : GraphOk I.desc) (w w' : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (writer : InstId) (name : String) (hE : PrioExt w w' writer)
    (hlive : (w.st writer).life = .alive) (hmem : writer ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc w' name → key ∈ heldKeys I.desc w name := by
  refine held_kept I.desc w w' name (fun s => s = writer) hE.ros hE.par hE.life ?_ ?_ ?_ ?_
  · intro i _ m hm
    exact Or.inl ⟨m, by simpa [hE.box i] using hm, rfl⟩
  · intro i _ m hm
    exact hE.prio i m hm
  · intro i _ p hp
    have hmemP : p ∈ (w.st i).parked := by simpa [hE.park i] using hp
    exact ⟨Or.inl ⟨p, hmemP, Or.inl rfl⟩, Or.inl ⟨p, hmemP, Or.inr rfl⟩⟩
  · intro key g s hgen hs hpred
    cases hkind with
    | inl hempty =>
      have hfrom : fromSlot name key s = true := by
        rwa [slotPred_empty I.desc name key s hempty] at hpred
      exact ⟨s, by simpa [hs] using hmem, hfrom, by simpa [hs] using hlive⟩
    | inr hroot =>
      obtain ⟨t, ht, hrootT, hsub⟩ := hroot
      have hm : isMember I.desc s t.subtree key = true := by
        rwa [slotPred_root I.desc name key s t ht hsub] at hpred
      exact root_sender_slot I hG w hF hP hSelf hH hOne hKids hcr name key g t ht hrootT hsub
        hgen s (by simpa [hs] using hmem) (by simpa [hs] using hlive) hm

/-- A cell write wakes readers with a priority message from the writer, or
leaves the queues alone when the cell was already dirty. -/
theorem held_cell (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (dst label : String) (value : Nat) (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = .cell dst label value :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
  simp only [execRun, hbit, hk] at hkK
  let previous := w.cell dst label
  let written : Cell := { value := max previous.value value, dirty := true }
  let w1 := setCell w dst label written
  let base := setActor w1 id (proceed (w1.st id) (afterHead k))
  have hbase : PrioExt w base id := {
    ros := by simp [base, w1, setCell, setActor_roster]
    par := fun i => by
      by_cases hi : i = id
      · rw [hi]; simp [base, w1, setCell, setActor, (proceed_fields _ _).2.1]
      · simp [base, w1, setCell, setActor, hi]
    life := fun i h => by
      by_cases hi : i = id
      · simpa [base, w1, setCell, setActor, hi, (proceed_fields _ _).1] using h
      · simpa [base, w1, setCell, setActor, hi] using h
    box := fun i => by
      by_cases hi : i = id
      · rw [hi]; simp [base, w1, setCell, setActor, (proceed_fields _ _).2.2.2.2]
      · simp [base, w1, setCell, setActor, hi]
    park := fun i => by
      by_cases hi : i = id
      · rw [hi]; simp [base, w1, setCell, setActor, (proceed_fields _ _).2.2.2.1]
      · simp [base, w1, setCell, setActor, hi]
    prio := fun i m hm => by
      by_cases hi : i = id
      · exact Or.inl ⟨m, by simpa [base, w1, setCell, setActor, hi, (proceed_fields _ _).2.2.1] using hm, rfl⟩
      · exact Or.inl ⟨m, by simpa [base, w1, setCell, setActor, hi] using hm, rfl⟩
  }
  by_cases hdirty : previous.dirty = true
  · simp [hdirty, previous, written, w1, base] at hkK
    exact held_prio_ext I hG w base hF hP hSelf hH hOne hKids hcr id name hbase hlive hmem hkind key hkK
  · have hdirtyF : previous.dirty = false := by
      cases hb : previous.dirty with
      | false => rfl
      | true => exact absurd hb hdirty
    simp [hdirtyF, previous, written, w1, base] at hkK
    exact held_prio_ext I hG w _ hF hP hSelf hH hOne hKids hcr id name
      (hbase.trans (wake_ext I.desc base dst label id)) hlive hmem hkind key hkK

/-- Effects that enqueue mail. The sender is the actor that runs. -/
def effectEnqueues (e : Eff) : Bool :=
  match e with
  | .send _ _ _ => true
  | .trySend _ _ _ _ _ => true
  | .call _ _ _ _ _ => true
  | .selfSchedule _ => true
  | .cell _ _ _ => true
  | .reply => false
  | .internal => false
  | .peer _ => false
  | .abort => false
  | .terminate => false
  | .spawn _ => false

/-- Running an enqueueing effect does not grow the held keys of an empty subtree
or of a root template. The executor is alive, and that is the sender. -/
theorem held_exec_enqueue (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (k : Cont) (e : Eff) (es : List Eff) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hk : k.rest = e :: es) (he : effectEnqueues e = true)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  cases e with
  | send dst label hint =>
    exact held_send I hG w hF hP hSelf hH hOne hKids hcr id k dst label hint es name hlive hmem hk hkind
  | trySend dst label hint onFull onGone =>
    exact held_try I hG w hF hP hSelf hH hOne hKids hcr id k dst label hint onFull onGone es name
      hlive hmem hk hkind
  | call dst label hint onNotAdmitted onTimedOut =>
    exact held_call I hG w hF hP hSelf hH hOne hKids hcr id k dst label hint onNotAdmitted onTimedOut
      es name hlive hmem hk hkind
  | selfSchedule label =>
    exact held_self I hG w hF hP hSelf hH hOne hKids hcr id k label es name hlive hmem hk hkind
  | cell dst label value =>
    exact held_cell I hG w hF hP hSelf hH hOne hKids hcr id k dst label value es name hlive hmem hk hkind
  | reply => simp [effectEnqueues] at he
  | internal => simp [effectEnqueues] at he
  | peer _ => simp [effectEnqueues] at he
  | abort => simp [effectEnqueues] at he
  | terminate => simp [effectEnqueues] at he
  | spawn _ => simp [effectEnqueues] at he

/-- An accepted `exec` of an enqueueing effect does not grow those held keys.
`execHead` only runs an alive actor. -/
theorem held_exec_head (I : Impl) (hG : GraphOk I.desc) (w w' : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (name : String) (hmem : id ∈ w.roster)
    (h : execHead I w id = some w')
    (he : match (w.st id).phase with
      | .run k => match k.rest with
        | e :: _ => effectEnqueues e
        | [] => false
      | _ => false)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc w' name → key ∈ heldKeys I.desc w name := by
  intro key hkK
  unfold execHead at h
  by_cases hnot : (w.st id).life ≠ .alive
  · simp [hnot] at h
  · have hlive : (w.st id).life = .alive := Classical.byContradiction fun hne => hnot hne
    simp [hnot] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h he
      cases h
      cases hk : k.rest with
      | nil => simp [hk] at he
      | cons e es =>
        simp [hk] at he
        exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k e es name hlive hmem hk he
          hkind key hkK
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

/-- A priority message after `enqueueTombstone` was already queued, or it is the
child's tombstone. -/
theorem tomb_prio (D : Description) (w : World) (child i : InstId) (m : Msg)
    (hm : m ∈ ((enqueueTombstone D w child).st i).prio) :
    m ∈ (w.st i).prio ∨ m.sender = child := by
  unfold enqueueTombstone at hm
  cases hp : (w.st child).parent with
  | none =>
    simp [hp] at hm
    exact Or.inl hm
  | some parent =>
    simp only [hp] at hm
    by_cases hl : ((w.st parent).life != .alive) = true
    · simp [hl] at hm
      exact Or.inl hm
    · have hlive : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hl
      simp only [hlive, Bool.false_eq_true, ite_false] at hm
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true, crashWorld, crashActor] at hm
        split at hm
        · split at hm <;> exact Or.inl hm
        · exact Or.inl hm
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlabF, Bool.false_eq_true, ite_false, offerPrio] at hm
        split at hm
        · simp [crashWorld, crashActor] at hm
          split at hm
          · split at hm <;> exact Or.inl hm
          · exact Or.inl hm
        · by_cases hip : i = parent
          · simp [setActor, hip, List.mem_append] at hm
            rcases hm with hm | rfl
            · rw [hip]
              exact Or.inl hm
            · exact Or.inr rfl
          · simp [setActor, hip] at hm
            exact Or.inl hm

theorem release_skip_prio (w : World) (id : InstId) (ps : List Parked)
    (h : (w.st id).prio = []) : ((releaseParked w id ps).st id).prio = [] := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using h
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split <;> rw [← releaseParked]
    · exact ih _ h
    · rename_i hskip
      have hne : p.sender ≠ id := by
        intro heq
        simp [heq] at hskip
      exact ih _ (by
        have hdis : id ≠ p.sender := fun heq => hne heq.symm
        simpa [setActor, hdis] using h)

theorem release_victim_prio (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).prio = [] := by
  simp only [releaseWorld]
  exact release_skip_prio _ id a.parked (by simp [setActor])

theorem release_skip_life (w : World) (id : InstId) (ps : List Parked)
    (h : (w.st id).life = .dead) : ((releaseParked w id ps).st id).life = .dead := by
  induction ps generalizing w with
  | nil => simpa [releaseParked] using h
  | cons p ps ih =>
    rw [releaseParked, List.foldl_cons]
    split <;> rw [← releaseParked]
    · exact ih _ h
    · rename_i hskip
      have hne : p.sender ≠ id := by
        intro heq
        simp [heq] at hskip
      exact ih _ (by
        have hdis : id ≠ p.sender := fun heq => hne heq.symm
        simpa [setActor, hdis] using h)

theorem release_victim_life (D : Description) (w : World) (id : InstId) (a : Actor) :
    ((releaseWorld D w id a).st id).life = .dead := by
  simp only [releaseWorld]
  exact release_skip_life _ id a.parked (by simp [setActor])

theorem enqueueTombstone_roster (D : Description) (w : World) (child : InstId) :
    (enqueueTombstone D w child).roster = w.roster := by
  unfold enqueueTombstone
  cases hp : (w.st child).parent with
  | none => rfl
  | some parent =>
    simp only [hp]
    by_cases hl : ((w.st parent).life != .alive) = true
    · simp [hl]
    · have hlive : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hl
      simp only [hlive, Bool.false_eq_true, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp [hlab, crashWorld_roster]
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlabF, Bool.false_eq_true, ite_false, offerPrio]
        split
        · exact crashWorld_roster _
        · exact setActor_roster _ _ _

/-- Sealing one alive actor queues at most that actor's tombstone. Releasing it
only deletes mail. An empty subtree or a root template therefore gains no held key. -/
theorem held_seal (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (name : String)
    (hlive : (w.st id).life = .alive) (hmem : id ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (sealActor I.desc w id (w.st id)) name →
      key ∈ heldKeys I.desc w name := by
  let wR := releaseWorld I.desc w id (w.st id)
  refine held_kept I.desc w _ name (fun s => s = id)
    (by simpa [sealActor, wR] using (enqueueTombstone_roster I.desc wR id).trans (releaseWorld_roster I.desc w id (w.st id)))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact (enqueueTombstone_parent I.desc wR id i).trans (releaseWorld_parent I.desc w id (w.st id) i)
  · intro i h
    have hR := enqueueTombstone_life I.desc wR id i (by simpa [sealActor, wR] using h)
    by_cases hi : i = id
    · unfold wR at hR
      rw [hi, release_victim_life I.desc w id (w.st id)] at hR
      cases hR
    · exact (releaseWorld_life_ne I.desc w id (w.st id) i hi).symm.trans hR
  · intro i _ m hm
    have hbox := (enqueueTombstone_lists I.desc wR id i).1
    have hmR : m ∈ (wR.st i).box := by simpa [sealActor, wR, hbox] using hm
    exact Or.inl ⟨m, (releaseWorld_sub I.desc w id (w.st id) i).1.mem hmR, rfl⟩
  · intro i _ m hm
    rcases tomb_prio I.desc wR id i m (by simpa [sealActor, wR] using hm) with hmR | hs
    · by_cases hi : i = id
      · unfold wR at hmR
        rw [hi, release_victim_prio I.desc w id (w.st id)] at hmR
        simp at hmR
      · exact Or.inl ⟨m, by simpa [← (releaseWorld_prio I.desc w id (w.st id) i hi).1] using hmR, rfl⟩
    · exact Or.inr hs
  · intro i _ p hp
    have hpk := (enqueueTombstone_lists I.desc wR id i).2
    have hpR : p ∈ (wR.st i).parked := by simpa [sealActor, wR, hpk] using hp
    have hold := (releaseWorld_sub I.desc w id (w.st id) i).2.mem hpR
    exact ⟨Or.inl ⟨p, hold, Or.inl rfl⟩, Or.inl ⟨p, hold, Or.inr rfl⟩⟩
  · intro key g s hgen hs hpred
    cases hkind with
    | inl hempty =>
      have hfrom : fromSlot name key s = true := by
        rwa [slotPred_empty I.desc name key s hempty] at hpred
      exact ⟨s, by simpa [hs] using hmem, hfrom, by simpa [hs] using hlive⟩
    | inr hroot =>
      obtain ⟨t, ht, hrootT, hsub⟩ := hroot
      have hm : isMember I.desc s t.subtree key = true := by
        rwa [slotPred_root I.desc name key s t ht hsub] at hpred
      exact root_sender_slot I hG w hF hP hSelf hH hOne hKids hcr name key g t ht hrootT hsub
        hgen s (by simpa [hs] using hmem) (by simpa [hs] using hlive) hm

/-- Releasing an actor only deletes mail and does not bring anyone to life, so
no template gains a held key. -/
theorem held_release (D : Description) (w : World) (id : InstId) (a : Actor) (name : String) :
    ∀ key, key ∈ heldKeys D (releaseWorld D w id a) name → key ∈ heldKeys D w name := by
  refine held_kept D w _ name (fun _ => False) (releaseWorld_roster D w id a)
    (releaseWorld_parent D w id a) ?_ ?_ ?_ ?_ ?_
  · intro i h
    by_cases hi : i = id
    · rw [hi, release_victim_life D w id a] at h
      cases h
    · exact (releaseWorld_life_ne D w id a i hi).symm.trans h
  · intro i _ m hm
    exact Or.inl ⟨m, (releaseWorld_sub D w id a i).1.mem hm, rfl⟩
  · intro i _ m hm
    by_cases hi : i = id
    · rw [hi, release_victim_prio D w id a] at hm
      simp at hm
    · exact Or.inl ⟨m, by simpa [← (releaseWorld_prio D w id a i hi).1] using hm, rfl⟩
  · intro i _ p hp
    have hold := (releaseWorld_sub D w id a i).2.mem hp
    exact ⟨Or.inl ⟨p, hold, Or.inl rfl⟩, Or.inl ⟨p, hold, Or.inr rfl⟩⟩
  · intro _ _ _ _ hs _
    exact False.elim hs

/-- Shutting an actor down queues its tombstone only when it is alive, and that
tombstone is the only new mail. -/
theorem held_shutdown (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hKids : DeadChildless w) (hcr : w.crashed = false)
    (id : InstId) (name : String) (hmem : id ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (shutdownActor I.desc w id) name →
      key ∈ heldKeys I.desc w name := by
  intro key hk
  unfold shutdownActor at hk
  by_cases hbit : ((w.st id).life == .alive) = true
  · have hlive : (w.st id).life = .alive := by simpa [beq_iff_eq] using hbit
    simp [hbit] at hk
    exact held_seal I hG w hF hP hSelf hH hOne hKids hcr id name hlive hmem hkind key hk
  · simp [hbit] at hk
    exact hk

theorem held_steps (D : Description) (ids : List InstId) (w : World) (name : String)
    (step : World → InstId → World)
    (hstep : ∀ acc c, ∀ key, key ∈ heldKeys D (step acc c) name → key ∈ heldKeys D acc name) :
    ∀ key, key ∈ heldKeys D (ids.foldl step w) name → key ∈ heldKeys D w name := by
  induction ids generalizing w with
  | nil =>
    intro key hk
    simpa using hk
  | cons j js ih =>
    intro key hk
    rw [List.foldl_cons] at hk
    exact hstep w j key (ih (step w j) key hk)

/-- Sealing a branch only releases actors. It deletes mail and does not add a
tombstone, so no template gains a held key. -/
theorem held_branch (fuel : Nat) (D : Description) (w : World) (id : InstId) (name : String) :
    ∀ key, key ∈ heldKeys D (sealBranch fuel D w id) name → key ∈ heldKeys D w name := by
  induction fuel generalizing w id with
  | zero =>
    intro key hk
    simpa [sealBranch] using hk
  | succ fuel ih =>
    intro key hk
    simp only [sealBranch] at hk
    let step : World → InstId → World := fun acc c =>
      if isChild acc id c then sealBranch fuel D acc c else acc
    have hfold := held_steps D w.roster w name step
      (by
        intro acc c key hkS
        by_cases hch : isChild acc id c = true
        · simp [hch, step] at hkS
          exact ih acc c key hkS
        · simp [hch, step] at hkS
          exact hkS)
    let sealed := w.roster.foldl step w
    by_cases hlive : ((sealed.st id).life == .alive) = true
    · have hkS : key ∈ heldKeys D (releaseWorld D sealed id (sealed.st id)) name := by
        simpa [step, sealed, hlive] using hk
      exact hfold key (held_release D sealed id (sealed.st id) name key hkS)
    · have hkS : key ∈ heldKeys D sealed name := by
        simpa [step, sealed, hlive] using hk
      exact hfold key hkS

/-- Dropping descendants only seals them. Their tombstones are not queued, and
no template gains a held key. -/
theorem held_drop (D : Description) (w : World) (id : InstId) (name : String) :
    ∀ key, key ∈ heldKeys D (dropDescendants D w id) name → key ∈ heldKeys D w name := by
  unfold dropDescendants
  refine held_steps D w.roster w name
    (fun acc c => if isChild acc id c then sealBranch w.roster.length D acc c else acc) ?_
  intro acc c key hk
  by_cases hch : isChild acc id c = true
  · simp [hch] at hk
    exact held_branch w.roster.length D acc c name key hk
  · simp [hch] at hk
    exact hk

/-- Parents and the roster determine `Parented`. A seal changes neither. -/
theorem parented_frame (D : Description) {w w' : World} (hP : Parented D w)
    (hro : w'.roster = w.roster) (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) :
    Parented D w' := by
  intro id t hmem ht
  have hold := hP id t (by rw [← hro]; exact hmem) ht
  cases hs : t.supervisor with
  | none =>
    rw [hs] at hold
    rw [hpar id]
    exact hold
  | some name =>
    rw [hs] at hold
    obtain ⟨p, hp, hn, hkey⟩ := hold
    refine ⟨p, ?_, hn, hkey⟩
    rw [hpar id]
    exact hp

/-- A parent field copied from a world with no self-parent still has none. -/
theorem noSelf_frame {w w' : World} (h : NoSelfParent w)
    (hpar : ∀ i, (w'.st i).parent = (w.st i).parent) : NoSelfParent w' := by
  intro id
  rw [hpar id]
  exact h id

/-- `dropDescendants` keeps the parent forest. The seal rewrites lives, not links. -/
theorem drop_forest (I : Impl) (w : World) (id : InstId) (hI : Inv I w) :
    ParentForest (dropDescendants I.desc w id) :=
  (dropDescendants_inv I I.desc w id hI).forest

/-- Children are sealed before their parent, so a newly dead actor stays childless.
`dropDescendants_inv` is that transport: `KidsSeal.kids` is the child already dead. -/
theorem drop_childless (I : Impl) (w : World) (id : InstId) (hI : Inv I w) :
    DeadChildless (dropDescendants I.desc w id) :=
  (dropDescendants_inv I I.desc w id hI).seal.childless

/-- The roster is unchanged, so one root per subtree key survives the drop. -/
theorem drop_one (I : Impl) (w : World) (id : InstId) (hOne : OneCohort I.desc w.roster) :
    OneCohort I.desc (dropDescendants I.desc w id).roster :=
  oneCohort_same I.desc (drop_roster I.desc w id) hOne

/-- The recorded parent is unchanged, so a parented world stays parented. -/
theorem drop_parented (I : Impl) (w : World) (id : InstId) (hP : Parented I.desc w) :
    Parented I.desc (dropDescendants I.desc w id) :=
  parented_frame I.desc hP (drop_roster I.desc w id) (fun i => drop_parent I.desc w id i)

/-- No actor points at itself after a drop that does not rewrite parents. -/
theorem drop_noself (I : Impl) (w : World) (id : InstId) (hSelf : NoSelfParent w) :
    NoSelfParent (dropDescendants I.desc w id) :=
  noSelf_frame hSelf (fun i => drop_parent I.desc w id i)

/-- Sealing descendants and then `id` adds only `id`'s tombstone. The post-drop
world still has the forest, the childless lives, and one cohort, so
`held_shutdown` applies there. -/
theorem held_after_drop (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hcr : w.crashed = false)
    (id : InstId) (name : String) (hmem : id ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc
        (shutdownActor I.desc (dropDescendants I.desc w id) id) name →
      key ∈ heldKeys I.desc w name := by
  intro key hk
  have hD := hold_drop_desc I w hH id hcr
  have hmemD : id ∈ (dropDescendants I.desc w id).roster := by
    simpa [drop_roster I.desc w id] using hmem
  exact held_drop I.desc w id name key
    (held_shutdown I hG (dropDescendants I.desc w id) (drop_forest I w id hI)
      (drop_parented I w id hP) (drop_noself I w id hSelf) hD.1 (drop_one I w id hOne)
      (drop_childless I w id hI) hD.2 id name hmemD hkind key hk)

/-- `terminateStage` is a drop followed by the actor's own shutdown. -/
theorem held_stage (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hcr : w.crashed = false)
    (id : InstId) (a : Actor) (name : String) (hmem : id ∈ w.roster)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (terminateStage I.desc w id a) name →
      key ∈ heldKeys I.desc w name := by
  intro key hk
  dsimp only [terminateStage] at hk
  exact held_after_drop I hG w hI hP hSelf hH hOne hcr id name hmem hkind key hk

/-- Aborting seals each live child. A crash kills the rest of the roster, so the
fold stops; otherwise the next child still sees the same bundle. -/
theorem held_abort_children (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hcr : w.crashed = false)
    (parent : InstId) (name : String)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (abortChildren I.desc w parent) name →
      key ∈ heldKeys I.desc w name := by
  unfold abortChildren
  suffices ∀ (ids : List InstId) (acc : World), Inv I acc → Parented I.desc acc →
      NoSelfParent acc → Hold I acc →
      OneCohort I.desc acc.roster → acc.crashed = false →
      (∀ c, c ∈ ids → c ∈ acc.roster) →
      ∀ key, key ∈ heldKeys I.desc (ids.foldl (fun acc child =>
        if isChild acc parent child && (acc.st child).life == .alive then
          shutdownActor I.desc (dropDescendants I.desc acc child) child
        else acc) acc) name → key ∈ heldKeys I.desc acc name by
    exact this w.roster w hI hP hSelf hH hOne hcr (fun _ h => h)
  intro ids
  induction ids with
  | nil =>
    intro acc _ _ _ _ _ _ _ key hk
    simpa using hk
  | cons child cs ih =>
    intro acc hI hP hSelf hH hOne hcr hids key hk
    simp only [List.foldl_cons] at hk
    by_cases hc : (isChild acc parent child && (acc.st child).life == .alive) = true
    · simp only [hc, ite_true] at hk
      have hmem : child ∈ acc.roster := hids child (List.mem_cons.mpr (Or.inl rfl))
      have hone := held_after_drop I hG acc hI hP hSelf hH hOne hcr child name hmem hkind
      let wS := shutdownActor I.desc (dropDescendants I.desc acc child) child
      by_cases hbad : wS.crashed = true
      · have hD := hold_drop_desc I acc hH child hcr
        have hskip := abort_fold_skip I.desc parent cs wS (fun c hcmem => by
          have hmem0 := hids c (List.mem_cons_of_mem child hcmem)
          have hmemD : c ∈ (dropDescendants I.desc acc child).roster := by
            simpa [drop_roster I.desc acc child] using hmem0
          exact shutdown_dead I.desc (dropDescendants I.desc acc child) child hD.2 hbad c hmemD)
        rw [hskip] at hk
        exact hone key hk
      · have hcf : wS.crashed = false := by
          cases hb : wS.crashed with
          | false => rfl
          | true => exact absurd hb hbad
        have hstage : terminateStage I.desc acc child (acc.st child) = wS := by
          simp [terminateStage, wS]
        have hIS : Inv I wS := by
          simpa [hstage] using terminateStage_inv I I.desc acc child (acc.st child) hI
        have hpar : ∀ i, (wS.st i).parent = (acc.st i).parent := by
          intro i
          simpa [wS] using (shutdown_parent I.desc (dropDescendants I.desc acc child) child i).trans
            (drop_parent I.desc acc child i)
        have hro : wS.roster = acc.roster := by
          simpa [wS] using (shutdown_roster I.desc (dropDescendants I.desc acc child) child).trans
            (drop_roster I.desc acc child)
        have hPS := parented_frame I.desc hP hro hpar
        have hSelfS := noSelf_frame hSelf hpar
        have hHS := by
          simpa [hstage] using hold_terminate_stage I acc hH child (acc.st child) hcr
        have hOneS := oneCohort_same I.desc hro hOne
        have hidsS : ∀ c, c ∈ cs → c ∈ wS.roster := by
          intro c hcmem
          have hmem0 := hids c (List.mem_cons_of_mem child hcmem)
          simpa [hro] using hmem0
        exact hone key (ih wS hIS hPS hSelfS hHS hOneS hcf hidsS key hk)
    · have hf : (isChild acc parent child && (acc.st child).life == .alive) = false := by
        cases hb : isChild acc parent child && (acc.st child).life == .alive with
        | false => rfl
        | true => exact absurd hb hc
      simp only [hf] at hk
      exact ih acc hI hP hSelf hH hOne hcr
        (fun c hcmem => hids c (List.mem_cons_of_mem child hcmem)) key hk

/-- `commitCont` installs a continuation. A crashed abort leaves the world, and
a live one only rewrites the parent's phase. -/
theorem held_commit (D : Description) (w : World) (id : InstId) (a : Actor) (name : String)
    (hb : a.box = (w.st id).box) (hpr : a.prio = (w.st id).prio)
    (hpa : a.parked = (w.st id).parked) (hpar : a.parent = (w.st id).parent)
    (hl : a.life = (w.st id).life) :
    ∀ key, key ∈ heldKeys D (commitCont w id a) name → key ∈ heldKeys D w name := by
  intro key hk
  unfold commitCont at hk
  by_cases hcr : w.crashed = true
  · simp only [hcr] at hk
    exact hk
  · have hf : w.crashed = false := by
      cases hbcr : w.crashed with
      | false => rfl
      | true => exact absurd hbcr hcr
    simp only [hf] at hk
    exact held_phase D w id a name hb hpr hpa hpar hl key hk

/-- Abort is not an `effectEnqueues` arm. The new mail is each live child's
tombstone, queued by `held_after_drop`, not a message from the parent. The
parent's continuation adds none. -/
theorem held_abort_run (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hcr : w.crashed = false)
    (id : InstId) (a : Actor) (k : Cont) (es : List Eff) (name : String)
    (hk : k.rest = .abort :: es)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id a k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  by_cases hlive : (a.life == .alive) = true
  · have hgo : (a.life == .alive) = true := hlive
    let k' := afterHead k
    let w' := abortChildren I.desc w id
    have hbase : execRun I w id a k = commitCont w' id (proceed (w'.st id) k') := by
      simp [execRun, hgo, hk, w', k']
    rw [hbase] at hkK
    have hf := proceed_fields (w'.st id) k'
    exact held_abort_children I hG w hI hP hSelf hH hOne hcr id name hkind key
      (held_commit I.desc w' id (proceed (w'.st id) k') name
        hf.2.2.2.2 hf.2.2.1 hf.2.2.2.1 hf.2.1 hf.1 key hkK)
  · have hf : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simpa [execRun, hf] using hkK

/-- Terminate is not an `effectEnqueues` arm. A core crashes and queues nothing.
A per-peer shutdown queues that actor's tombstone, after the drop when the
stage has descendants. -/
theorem held_terminate_run (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hP : Parented I.desc w) (hSelf : NoSelfParent w)
    (hH : Hold I w) (hOne : OneCohort I.desc w.roster) (hcr : w.crashed = false)
    (id : InstId) (a : Actor) (k : Cont) (name : String) (hmem : id ∈ w.roster)
    (hk : ∃ tail, k.rest = .terminate :: tail)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id a k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  by_cases hbit : (a.life == .alive) = true
  · have hlive : a.life = .alive := by simpa [beq_iff_eq] using hbit
    rcases execRun_terminate I w id a k hlive hk with hcrash | hlone | htree | hcascade
    · rw [hcrash] at hkK
      exact held_crash I.desc w name key hkK
    · obtain ⟨_, _, _, _, _, _, _, hr⟩ := hlone
      rw [hr] at hkK
      exact held_shutdown I hG w hI.forest hP hSelf hH hOne hI.seal.childless hcr id name hmem
        hkind key hkK
    · obtain ⟨_, _, _, _, hr⟩ := htree
      rw [hr] at hkK
      exact held_stage I hG w hI hP hSelf hH hOne hcr id a name hmem hkind key hkK
    · obtain ⟨_, _, _, _, _, _, _, hr⟩ := hcascade
      rw [hr] at hkK
      exact held_stage I hG w hI hP hSelf hH hOne hcr id a name hmem hkind key hkK
  · have hf : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd hb hbit
    simpa [execRun, hf] using hkK

/-- `proceed` keeps the queues, the life and the parent, so it adds no held key. -/
theorem held_proceed (D : Description) (w : World) (id : InstId) (k : Cont) (name : String) :
    ∀ key, key ∈ heldKeys D (setActor w id (proceed (w.st id) k)) name →
      key ∈ heldKeys D w name := by
  intro key hk
  have hf := proceed_fields (w.st id) k
  exact held_phase D w id (proceed (w.st id) k) name
    hf.2.2.2.2 hf.2.2.1 hf.2.2.2.1 hf.2.1 hf.1 key hk

/-- A reply resumes the caller and the sender onto continuations already in
their arms. Neither continuation carries mail. -/
theorem held_reply (D : Description) (w : World) (sender : InstId) (k : Cont) (name : String) :
    ∀ key, key ∈ heldKeys D (performReply w sender k) name → key ∈ heldKeys D w name := by
  intro key hk
  unfold performReply at hk
  cases hr : k.replyTo with
  | none =>
    simp [hr] at hk
    exact held_proceed D w sender (afterHead k) name key hk
  | some caller =>
    simp [hr] at hk
    cases hp : (w.st caller).phase with
    | awaitReply dst ck =>
      simp [hp] at hk
      by_cases hmatch : dst = sender ∧ (w.st sender).oweId = some (w.st caller).waitId
      · rw [ite_eq_left hmatch] at hk
        let w1 := setActor w caller (finishCall (w.st caller) ck .reply)
        have hf := finishCall_fields (w.st caller) ck .reply
        have h1 := held_phase D w caller (finishCall (w.st caller) ck .reply) name
          hf.2.2.2.2 hf.2.2.1 hf.2.2.2.1 hf.2.1 hf.1
        exact h1 key (held_proceed D w1 sender (afterHead k) name key hk)
      · rw [ite_eq_right hmatch] at hk
        exact held_proceed D w sender (afterHead k) name key hk
    | idle =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk
    | run _ =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk
    | parked _ _ _ =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk
    | awaitEffect _ =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk
    | awaitPeer _ =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk
    | crashed =>
      simp [hp] at hk
      exact held_proceed D w sender (afterHead k) name key hk

/-- `reply` is not an `effectEnqueues` arm: both actors resume a continuation
they already held. -/
theorem held_exec_reply (I : Impl) (w : World) (id : InstId) (k : Cont) (es : List Eff)
    (name : String) (hk : k.rest = .reply :: es) :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hkK
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp [execRun, hlive, hk] at hkK
    exact held_reply I.desc w id k name key hkK
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simpa [execRun, hf] using hkK

/-- An empty rest, an internal effect and a peer effect only rewrite the
executor's phase. -/
theorem held_exec_phase (I : Impl) (w : World) (id : InstId) (k : Cont) (name : String)
    (hquiet : match k.rest with
      | [] => True
      | .internal :: _ => True
      | .peer _ :: _ => True
      | _ => False) :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id (w.st id) k) name →
      key ∈ heldKeys I.desc w name := by
  intro key hk
  by_cases hlive : ((w.st id).life == .alive) = true
  · cases hkrest : k.rest with
    | nil =>
      simp [execRun, hlive, hkrest] at hk
      exact held_phase I.desc w id { (w.st id) with phase := .idle, typestate := k.toState } name
        rfl rfl rfl rfl rfl key hk
    | cons e es =>
      cases e with
      | internal =>
        simp [execRun, hlive, hkrest] at hk
        exact held_phase I.desc w id
          { (w.st id) with phase := .awaitEffect (afterHead k) } name
          rfl rfl rfl rfl rfl key hk
      | peer onTimeout =>
        simp [execRun, hlive, hkrest] at hk
        exact held_phase I.desc w id
          { (w.st id) with phase := .awaitPeer { afterHead k with onTimeout := onTimeout } } name
          rfl rfl rfl rfl rfl key hk
      | send _ _ _ => simp [hkrest] at hquiet
      | trySend _ _ _ _ _ => simp [hkrest] at hquiet
      | call _ _ _ _ _ => simp [hkrest] at hquiet
      | reply => simp [hkrest] at hquiet
      | selfSchedule _ => simp [hkrest] at hquiet
      | cell _ _ _ => simp [hkrest] at hquiet
      | abort => simp [hkrest] at hquiet
      | terminate => simp [hkrest] at hquiet
      | spawn _ => simp [hkrest] at hquiet
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simpa [execRun, hf] using hk

/-- A parent walk that starts off the fresh id never reads that id's new parent.
No older actor named the fresh id, so the walk agrees with the world before the birth. -/
theorem descends_birth (w w' : World) (fresh : InstId) (fuel : Nat) (anc desc : InstId)
    (hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (hdesc : desc ≠ fresh) :
    descends fuel w' anc desc = descends fuel w anc desc := by
  induction fuel generalizing desc with
  | zero => rfl
  | succ fuel ih =>
    simp only [descends]
    by_cases heq : desc = anc
    · simp [heq]
    · have hbeq : (desc == anc) = false := by simpa [beq_iff_eq] using heq
      simp only [hbeq]
      have hpdesc := hp desc hdesc
      rw [hpdesc]
      cases hpar : (w.st desc).parent with
      | none => rfl
      | some p =>
        have hpne : p ≠ fresh := by
          intro hpf
          exact hno desc (by rw [hpar, hpf])
        by_cases hanc : p = anc
        · simp [hanc]
        · by_cases hself : p = desc
          · simp [hself]
          · simp [hanc, hself]
            exact ih p hpne

/-- Growing the roster only lengthens the parent walk. A host that still survives
the sender survived it before the birth. -/
theorem survives_birth (w w' : World) (fresh sender host : InstId)
    (hlen : w.roster.length ≤ w'.roster.length)
    (hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh)
    (hlife : (w'.st host).life = (w.st host).life) (hhost : host ≠ fresh)
    (h : survivesSender w' sender host = true) : survivesSender w sender host = true := by
  simp only [survivesSender, Bool.and_eq_true] at h ⊢
  refine ⟨by rw [← hlife]; exact h.1, ?_⟩
  cases hsw : sealedTogether w sender host with
  | false => simp
  | true =>
    have hnot : sealedTogether w' sender host = false := by
      cases hs' : sealedTogether w' sender host with
      | false => rfl
      | true => simp [hs'] at h
    simp only [sealedTogether, Bool.or_eq_true] at hsw
    rcases hsw with heq | hd
    · simp [sealedTogether, heq] at hnot
    · have hlong := descends_mono w sender host w.roster.length w'.roster.length hlen hd
      have hsame : descends w'.roster.length w' sender host = true := by
        rw [descends_birth w w' fresh _ sender host hp hno hhost]
        exact hlong
      simp [sealedTogether, hsame] at hnot

theorem bool_any_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) (hp : xs.any p = true) : xs.any q = true := by
  obtain ⟨a, ha, hpa⟩ := (_root_.List.any_eq_true).mp hp
  exact (_root_.List.any_eq_true).mpr ⟨a, ha, h a hpa⟩

theorem holds_slot_empty (w : World) (host : InstId) (name : String) (key : Nat) (a : Actor)
    (hb : a.box = []) (hpr : a.prio = []) (hpa : a.parked = []) :
    actorHoldsSlotMail w host name key a = false := by
  simp [actorHoldsSlotMail, hb, hpr, hpa]

theorem holds_sub_empty (D : Description) (w : World) (host : InstId) (sub : String) (key : Nat)
    (a : Actor) (hb : a.box = []) (hpr : a.prio = []) (hpa : a.parked = []) :
    actorHoldsSubtreeMail D w host sub key a = false := by
  simp [actorHoldsSubtreeMail, hb, hpr, hpa]

/-- An older host holds a slot after the birth only when it held that slot before.
The fresh actor's mailbox is empty, and a host that survives now survived then. -/
theorem holds_slot_birth (w w' : World) (fresh host : InstId) (name : String) (key : Nat)
    (hlen : w.roster.length ≤ w'.roster.length)
    (hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (hhost : host ≠ fresh)
    (hst : w'.st host = w.st host)
    (h : actorHoldsSlotMail w' host name key (w'.st host) = true) :
    actorHoldsSlotMail w host name key (w.st host) = true := by
  rw [hst] at h
  have hlife : (w'.st host).life = (w.st host).life := congrArg Actor.life hst
  have hsurv : ∀ s, survivesSender w' s host = true → survivesSender w s host = true :=
    fun s hs => survives_birth w w' fresh s host hlen hp hno hlife hhost hs
  simp only [actorHoldsSlotMail, Bool.or_eq_true] at h ⊢
  rcases h with hleft | hpark
  · rcases hleft with hbox | hprio
    · exact Or.inl (Or.inl (bool_any_imp _ _ _ (fun m hm => by
        simp only [Bool.and_eq_true] at hm ⊢
        exact ⟨hm.1, hsurv _ hm.2⟩) hbox))
    · exact Or.inl (Or.inr (bool_any_imp _ _ _ (fun m hm => by
        simp only [Bool.and_eq_true] at hm ⊢
        exact ⟨hm.1, hsurv _ hm.2⟩) hprio))
  · exact Or.inr (bool_any_imp _ _ _ (fun p hm => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl ⟨hm.1, hsurv _ hm.2⟩
      · exact Or.inr ⟨hm.1, hsurv _ hm.2⟩) hpark)

theorem holds_sub_birth (D : Description) (w w' : World) (fresh host : InstId) (sub : String)
    (key : Nat) (hlen : w.roster.length ≤ w'.roster.length)
    (hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent)
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (hhost : host ≠ fresh)
    (hst : w'.st host = w.st host)
    (h : actorHoldsSubtreeMail D w' host sub key (w'.st host) = true) :
    actorHoldsSubtreeMail D w host sub key (w.st host) = true := by
  rw [hst] at h
  have hlife : (w'.st host).life = (w.st host).life := congrArg Actor.life hst
  have hsurv : ∀ s, survivesSender w' s host = true → survivesSender w s host = true :=
    fun s hs => survives_birth w w' fresh s host hlen hp hno hlife hhost hs
  simp only [actorHoldsSubtreeMail, Bool.or_eq_true] at h ⊢
  rcases h with hleft | hpark
  · rcases hleft with hbox | hprio
    · exact Or.inl (Or.inl (bool_any_imp _ _ _ (fun m hm => by
        simp only [Bool.and_eq_true] at hm ⊢
        exact ⟨hm.1, hsurv _ hm.2⟩) hbox))
    · exact Or.inl (Or.inr (bool_any_imp _ _ _ (fun m hm => by
        simp only [Bool.and_eq_true] at hm ⊢
        exact ⟨hm.1, hsurv _ hm.2⟩) hprio))
  · exact Or.inr (bool_any_imp _ _ _ (fun p hm => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl ⟨hm.1, hsurv _ hm.2⟩
      · exact Or.inr ⟨hm.1, hsurv _ hm.2⟩) hpark)

/-- Mail held in a slot after one empty actor is appended was held before it.
The new mailbox contributes nothing, and every older host still had the same queues. -/
theorem core_mail_birth (w w' : World) (fresh : InstId) (name : String) (key : Nat)
    (hros : w'.roster = w.roster ++ [fresh])
    (hst : ∀ i, i ≠ fresh → w'.st i = w.st i)
    (hempty : (w'.st fresh).box = [] ∧ (w'.st fresh).prio = [] ∧ (w'.st fresh).parked = [])
    (hno : ∀ i, (w.st i).parent ≠ some fresh)
    (h : slotCoreMail w' name key = true) : slotCoreMail w name key = true := by
  have hlen : w.roster.length ≤ w'.roster.length := by
    rw [hros, List.length_append, List.length_singleton]
    omega
  have hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent :=
    fun i hi => congrArg Actor.parent (hst i hi)
  obtain ⟨host, hmem, hhold⟩ := (_root_.List.any_eq_true).mp h
  have hmem' : host ∈ w.roster ++ [fresh] := by simpa [hros] using hmem
  simp only [List.mem_append, List.mem_singleton] at hmem'
  rcases hmem' with hold | rfl
  · by_cases hhost : host = fresh
    · rw [hhost] at hhold
      simp [holds_slot_empty w' fresh name key (w'.st fresh) hempty.1 hempty.2.1 hempty.2.2] at hhold
    · have hback := holds_slot_birth w w' fresh host name key hlen hp hno hhost (hst host hhost) hhold
      exact (_root_.List.any_eq_true).mpr ⟨host, hold, hback⟩
  · simp [holds_slot_empty w' host name key (w'.st host) hempty.1 hempty.2.1 hempty.2.2] at hhold

theorem sub_mail_birth (D : Description) (w w' : World) (fresh : InstId) (sub : String) (key : Nat)
    (hros : w'.roster = w.roster ++ [fresh])
    (hst : ∀ i, i ≠ fresh → w'.st i = w.st i)
    (hempty : (w'.st fresh).box = [] ∧ (w'.st fresh).prio = [] ∧ (w'.st fresh).parked = [])
    (hno : ∀ i, (w.st i).parent ≠ some fresh)
    (h : subtreeCoreMail D w' sub key = true) : subtreeCoreMail D w sub key = true := by
  have hlen : w.roster.length ≤ w'.roster.length := by
    rw [hros, List.length_append, List.length_singleton]
    omega
  have hp : ∀ i, i ≠ fresh → (w'.st i).parent = (w.st i).parent :=
    fun i hi => congrArg Actor.parent (hst i hi)
  obtain ⟨host, hmem, hhold⟩ := (_root_.List.any_eq_true).mp h
  have hmem' : host ∈ w.roster ++ [fresh] := by simpa [hros] using hmem
  simp only [List.mem_append, List.mem_singleton] at hmem'
  rcases hmem' with hold | rfl
  · by_cases hhost : host = fresh
    · rw [hhost] at hhold
      simp [holds_sub_empty D w' fresh sub key (w'.st fresh) hempty.1 hempty.2.1 hempty.2.2] at hhold
    · have hback := holds_sub_birth D w w' fresh host sub key hlen hp hno hhost
        (hst host hhost) hhold
      exact (_root_.List.any_eq_true).mpr ⟨host, hold, hback⟩
  · simp [holds_sub_empty D w' host sub key (w'.st host) hempty.1 hempty.2.1 hempty.2.2] at hhold

/-- Appending one empty actor does not start holding a slot that was clear. -/
theorem slot_mail_birth (D : Description) (w w' : World) (fresh : InstId) (name : String)
    (hros : w'.roster = w.roster ++ [fresh])
    (hst : ∀ i, i ≠ fresh → w'.st i = w.st i)
    (hempty : (w'.st fresh).box = [] ∧ (w'.st fresh).prio = [] ∧ (w'.st fresh).parked = [])
    (hno : ∀ i, (w.st i).parent ≠ some fresh) (key : Nat)
    (h : slotMailHeld D w' name key = true) : slotMailHeld D w name key = true := by
  simp only [slotMailHeld] at h ⊢
  by_cases hemptySub : (templateSubtree D name == "") = true
  · simp only [hemptySub, ite_true] at h ⊢
    exact core_mail_birth w w' fresh name key hros hst hempty hno h
  · have hf : (templateSubtree D name == "") = false := by
      cases hb : templateSubtree D name == "" with
      | false => rfl
      | true => exact absurd hb hemptySub
    simp only [hf] at h ⊢
    exact sub_mail_birth D w w' fresh (templateSubtree D name) key hros hst hempty hno h

/-- Keys held after a step were held before, so the count does not grow. -/
theorem held_len_of_sub (D : Description) (w w' : World) (name : String)
    (h : ∀ k, k ∈ heldKeys D w' name → k ∈ heldKeys D w name) :
    (heldKeys D w' name).length ≤ (heldKeys D w name).length :=
  nodup_sub_len _ _ (heldKeys_nodup D w' name) h

/-- One empty actor is appended. Its mailbox holds nothing, and no older actor
named it as a parent, so a slot held afterwards was held before or is its key. -/
theorem held_birth_len (D : Description) (w w' : World) (name : String) (id : InstId) (k g : Nat)
    (hF : ParentForest w) (hnew : id ∉ w.roster)
    (hros : w'.roster = w.roster ++ [id]) (hid : id = InstId.peer name k g)
    (hst : ∀ i, i ≠ id → w'.st i = w.st i)
    (hempty : (w'.st id).box = [] ∧ (w'.st id).prio = [] ∧ (w'.st id).parked = []) :
    (heldKeys D w' name).length ≤ (heldKeys D w name).length + 1 := by
  have hno : ∀ i, (w.st i).parent ≠ some id := by
    intro i hp
    exact hnew (hF.hosted i id hp)
  exact held_extend_len D w w' name id k g hros hid hst hempty
    (fun key hmail => slot_mail_birth D w w' id name hros hst hempty hno key hmail)

theorem held_fold_core (D : Description) (w : World) (name : String) :
    ∀ (ids : List InstId) (acc : List Nat),
      (∀ id, id ∈ ids → ∃ n, id = InstId.core n) →
      ids.foldl (fun acc id =>
        match id with
        | .peer n k _ =>
          if n == name && heldAt D w name k && !acc.elem k then acc ++ [k] else acc
        | .core _ => acc) acc = acc := by
  intro ids
  induction ids with
  | nil =>
    intro acc _
    rfl
  | cons id ids ih =>
    intro acc hcore
    have ⟨n, hid⟩ := hcore id (List.mem_cons_self)
    simp only [List.foldl_cons, hid]
    exact ih acc (fun i hi => hcore i (List.mem_cons_of_mem _ hi))

theorem coreRoster_core (D : Description) (id : InstId) (h : id ∈ coreRoster D) :
    ∃ n, id = InstId.core n := by
  unfold coreRoster at h
  obtain ⟨t, ht, hid⟩ := List.mem_filterMap.mp h
  cases hb : t.multiplicity == .one with
  | false => simp [hb] at hid
  | true =>
    simp [hb] at hid
    exact ⟨t.name, hid.symm⟩

/-- The initial roster is cores only, so no per-peer key is held. -/
theorem held_init (I : Impl) (N : Nat) (name : String) :
    heldKeys I.desc (initWorld I N) name = [] := by
  have hro := init_roster I N
  unfold heldKeys
  rw [hro]
  exact held_fold_core I.desc (initWorld I N) name (coreRoster I.desc) []
    (fun id hid => coreRoster_core I.desc id hid)

/-- `placePeer` appends one empty generation of `template`. That is the only
key the birth can add to that template. -/
theorem held_place_len (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (bump : World → World) (hF : ParentForest w)
    (hstB : ∀ u i, (bump u).st i = u.st i) (hrB : ∀ u, (bump u).roster = u.roster) :
    (heldKeys I.desc (placePeer I w template k initial parent bump) template).length ≤
      (heldKeys I.desc w template).length + 1 := by
  let id := InstId.peer template k (maxGen w template k)
  have hst := place_st I w template k initial parent bump hstB
  have hros := place_roster I w template k initial parent bump hrB
  have hempty : ((placePeer I w template k initial parent bump).st id).box = [] ∧
      ((placePeer I w template k initial parent bump).st id).prio = [] ∧
      ((placePeer I w template k initial parent bump).st id).parked = [] := by
    have hid : (placePeer I w template k initial parent bump).st id =
        { bornActor I.desc w template k initial with parent := parent } := by
      simp [id, hst]
    simp [hid, bornActor, withKeyTokens]
  refine held_birth_len I.desc w _ template id k (maxGen w template k) hF (gen_fresh w template k)
    (by simpa [id] using hros) rfl ?_ hempty
  intro i hi
  have h := hst i
  simp [id, hi] at h
  exact h

/-- A scheduler spawn of `template` adds at most one held key of that template. -/
theorem held_spawn_len (I : Impl) (w w' : World) (template : String) (hF : ParentForest w)
    (h : spawn I w template = some w') :
    (heldKeys I.desc w' template).length ≤ (heldKeys I.desc w template).length + 1 := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at h
        cases h
        exact held_place_len I w template (freshKey I.desc w t.subtree) t.initial
          (some (InstId.core name)) (fun u =>
            { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
          hF (fun _ _ => rfl) (fun _ => rfl)
      | none =>
        rw [hsup] at h
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at h
          cases h
          exact held_place_len I w template (w.nextIx template) t.initial none
            (fun u => { u with nextIx := fun n =>
                if n = template then w.nextIx template + 1 else u.nextIx n })
            hF (fun _ _ => rfl) (fun _ => rfl)
        · have hf : (t.subtree == "") = false := by
            cases hb : t.subtree == "" with
            | false => rfl
            | true => exact absurd hb hempty
          rw [hf] at h
          cases h
          exact held_place_len I w template (freshKey I.desc w t.subtree) t.initial none
            (fun u => { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            hF (fun _ _ => rfl) (fun _ => rfl)
    · simp [hmay] at h

/-- An unsupervised spawn is allowed only while the outstanding count is below
`w.N`. Held keys are at most that count, and the birth adds one. -/
theorem held_spawn_lone (I : Impl) (w w' : World) (template : String) (hF : ParentForest w)
    (h : spawn I w template = some w')
    (hlone : loneOutstanding I.desc w template < w.N) :
    (heldKeys I.desc w' template).length ≤ w.N := by
  have hpre := held_le_lone I.desc w template
  have hplus := held_spawn_len I w w' template hF h
  omega

/-- Admitting one empty actor adds at most its own key. -/
theorem held_admit_len (I : Impl) (w : World) (id : InstId) (born : Actor) (name : String)
    (k g : Nat) (hF : ParentForest w) (hnew : id ∉ w.roster) (hid : id = InstId.peer name k g)
    (hempty : born.box = [] ∧ born.prio = [] ∧ born.parked = []) :
    (heldKeys I.desc (admitBorn I w id born) name).length ≤
      (heldKeys I.desc w name).length + 1 := by
  refine held_birth_len I.desc w _ name id k g hF hnew (admit_roster I w id born) hid ?_ ?_
  · intro i hi
    exact admit_st_other I w id i born hi
  · have hself := admit_st_self I w id born
    exact ⟨by simp [hself, hempty.1], by simp [hself, hempty.2.1], by simp [hself, hempty.2.2]⟩

/-- A per-peer parent births its child at its own key, or the step is the
identity. Either way that child's held keys grow by at most one. -/
theorem held_child_len (I : Impl) (w w' : World) (parent : InstId) (child : String)
    (hF : ParentForest w) (h : spawnChild I w parent child = some w') :
    (heldKeys I.desc w' child).length ≤ (heldKeys I.desc w child).length + 1 := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = true
    · simp only [hgo, ite_true] at h
      cases parent with
      | core _ => simp at h
      | peer pn pk pg =>
        by_cases hblk : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = true
        · simp [hblk] at h
          cases h
          exact Nat.le_succ _
        · have hf : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblk
          simp only [hf] at h
          cases h
          let id := InstId.peer child pk (maxGen w child pk)
          let born :=
            { bornActor I.desc w child pk t.initial with parent := some (InstId.peer pn pk pg) }
          exact held_admit_len I w id born child pk (maxGen w child pk) hF (gen_fresh w child pk)
            rfl ⟨by simp [born, bornActor, withKeyTokens], by simp [born, bornActor, withKeyTokens],
              by simp [born, bornActor, withKeyTokens]⟩
    · have hf :
          (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf] at h
      by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hstay, ite_true] at h
        cases h
        exact Nat.le_succ _
      · have hstayF :
            (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hstay
        simp [hstayF] at h

/-- In a reachable world, ingress does not grow the held keys of a template
that is its own counted root: an empty subtree, or a nonempty root template. -/
theorem held_ingress_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w w' : World) (hR : Reachable I N w) (dst : InstId) (label name : String)
    (h : apply I (.ingress dst label) w = some w')
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ k, k ∈ heldKeys I.desc w' name → k ∈ heldKeys I.desc w name := by
  obtain ⟨hcr, hstep⟩ := apply_step I (.ingress dst label) w w' h
  simp only [stepWorld] at hstep
  cases hkind with
  | inl hempty =>
    exact held_ingress_empty I w w' dst label name hstep hempty
  | inr hroot =>
    obtain ⟨t, ht, hroot, hsub⟩ := hroot
    have hI := inv_reachable I N w hL hR
    exact held_ingress_root I hG w w' hI.forest (lane_birth I hL hG N w hR).parented
      (lane_birth I hL hG N w hR).noSelf (hold_reach I N w hG hR)
      (oneCohort_reachable I hG N w hR) hI.seal.childless hcr dst label name t hstep ht hroot hsub

/-- The population bound is fixed at `initWorld`. No step writes it. -/
theorem offerPrio_N (D : Description) (w : World) (host : InstId) (msg : Msg) :
    (offerPrio D w host msg).N = w.N := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp [hfull, crashWorld]
  · have hf : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = false := by
      cases hb : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) with
      | false => rfl
      | true => exact absurd hb hfull
    simp [hf, setActor]

theorem tryWake_N (D : Description) (w : World) (dstId : InstId) (label : String) (writer : InstId) :
    (tryWake D w dstId label writer).N = w.N := by
  unfold tryWake
  by_cases hskip : ((w.st dstId).life != .alive ||
      (w.st dstId).prio.any (fun p => p.label == label)) = true
  · simp [hskip]
  · have hf : ((w.st dstId).life != .alive ||
        (w.st dstId).prio.any (fun p => p.label == label)) = false := by
      cases hb : (w.st dstId).life != .alive || (w.st dstId).prio.any (fun p => p.label == label) with
      | false => rfl
      | true => exact absurd hb hskip
    simp [hf, offerPrio_N]

theorem wakeReaders_N (D : Description) (w : World) (dst label : String) (writer : InstId) :
    (wakeReaders D w dst label writer).N = w.N := by
  unfold wakeReaders
  suffices ∀ (ids : List InstId) (acc : World),
      (ids.foldl (fun acc id => tryWake D acc id label writer) acc).N = acc.N by
    exact this (readersOf w dst) w
  intro ids
  induction ids with
  | nil =>
    intro acc
    simp
  | cons id ids ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, tryWake_N]

theorem enqueueTombstone_N (D : Description) (w : World) (child : InstId) :
    (enqueueTombstone D w child).N = w.N := by
  unfold enqueueTombstone
  cases hp : (w.st child).parent with
  | none => rfl
  | some parent =>
    by_cases hdead : ((w.st parent).life != .alive) = true
    · simp [hdead]
    · have hf : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hdead
      simp only [hf]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp [hlab, crashWorld]
      · have hlf : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlf]
        exact offerPrio_N D w parent (tombstoneMsg D (w.st parent) child)

theorem releaseWorld_N (D : Description) (w : World) (id : InstId) (a : Actor) :
    (releaseWorld D w id a).N = w.N := by
  unfold releaseWorld
  let w1 := readCells D w id
  let w2 := refundMsgs w1 (tname id) a.box
  let w3 := refundParked w2 (tname id) a.parked
  let w4 := releaseOutbound w3 id
  let dead : Actor :=
    { w4.st id with life := .dead, phase := .idle, box := [], prio := [], parked := [] }
  have h1n : w1.N = w.N := cellsN D w id
  have h2n : w2.N = w1.N := refundMsgs_N w1 (tname id) a.box
  have h3n : w3.N = w2.N := refundParked_N w2 (tname id) a.parked
  have h4n : w4.N = w3.N := (releaseOutbound_prio w3 id id).2
  have h5n : (setActor w4 id dead).N = w4.N := rfl
  have h6n : (releaseParked (setActor w4 id dead) id a.parked).N = (setActor w4 id dead).N :=
    (releaseParked_prio (setActor w4 id dead) id a.parked id).2
  exact h6n.trans (h5n.trans (h4n.trans (h3n.trans (h2n.trans h1n))))

theorem sealActor_N (D : Description) (w : World) (id : InstId) (a : Actor) :
    (sealActor D w id a).N = w.N := by
  unfold sealActor
  exact (enqueueTombstone_N D (releaseWorld D w id a) id).trans (releaseWorld_N D w id a)

theorem shutdownActor_N (D : Description) (w : World) (id : InstId) :
    (shutdownActor D w id).N = w.N := by
  unfold shutdownActor
  by_cases hlive : ((w.st id).life == .alive) = true
  · simp only [hlive]
    exact sealActor_N D w id (w.st id)
  · have hf : ((w.st id).life == .alive) = false := by
      cases hb : (w.st id).life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [hf]

theorem sealBranch_N (fuel : Nat) (D : Description) (w : World) (id : InstId) :
    (sealBranch fuel D w id).N = w.N := by
  induction fuel generalizing w id with
  | zero =>
    simp [sealBranch]
  | succ fuel ih =>
    simp only [sealBranch]
    let step (w0 : World) (child : InstId) : World :=
      if isChild w0 id child then sealBranch fuel D w0 child else w0
    have hfold : ∀ (ids : List InstId) (acc : World), (ids.foldl step acc).N = acc.N := by
      intro ids
      induction ids with
      | nil =>
        intro acc
        simp
      | cons child ids ihids =>
        intro acc
        simp only [List.foldl_cons, step]
        by_cases hc : isChild acc id child = true
        · simp only [hc, ite_true]
          rw [ihids, ih]
        · have hf : isChild acc id child = false := by
            cases hb : isChild acc id child with
            | false => rfl
            | true => exact absurd hb hc
          simp only [hf]
          exact ihids acc
    let sealed := w.roster.foldl step w
    have hmid : sealed.N = w.N := hfold w.roster w
    change (if (sealed.st id).life == .alive then
      releaseWorld D sealed id (sealed.st id) else sealed).N = w.N
    by_cases hgo : ((sealed.st id).life == .alive) = true
    · simp only [hgo, ite_true]
      exact (releaseWorld_N D sealed id (sealed.st id)).trans hmid
    · have hf : ((sealed.st id).life == .alive) = false := by
        cases hb : (sealed.st id).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf]
      exact hmid

theorem dropDescendants_N (D : Description) (w : World) (id : InstId) :
    (dropDescendants D w id).N = w.N := by
  unfold dropDescendants
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 id child then sealBranch w.roster.length D w0 child else w0
  have hfold : ∀ (ids : List InstId) (acc : World), (ids.foldl step acc).N = acc.N := by
    intro ids
    induction ids with
    | nil =>
      intro acc
      simp
    | cons child ids ih =>
      intro acc
      simp only [List.foldl_cons, step]
      by_cases hc : isChild acc id child = true
      · simp only [hc, ite_true]
        rw [ih, sealBranch_N]
      · have hf : isChild acc id child = false := by
          cases hb : isChild acc id child with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih acc
  exact hfold w.roster w

theorem terminateStage_N (D : Description) (w : World) (id : InstId) (a : Actor) :
    (terminateStage D w id a).N = w.N := by
  unfold terminateStage
  exact (shutdownActor_N D (dropDescendants D w id) id).trans (dropDescendants_N D w id)

theorem abortChildren_N (D : Description) (w : World) (parent : InstId) :
    (abortChildren D w parent).N = w.N := by
  unfold abortChildren
  let step (w0 : World) (child : InstId) : World :=
    if isChild w0 parent child && (w0.st child).life == .alive then
      shutdownActor D (dropDescendants D w0 child) child
    else w0
  have hfold : ∀ (ids : List InstId) (acc : World), (ids.foldl step acc).N = acc.N := by
    intro ids
    induction ids with
    | nil =>
      intro acc
      simp
    | cons child ids ih =>
      intro acc
      simp only [List.foldl_cons, step]
      by_cases hc : (isChild acc parent child && (acc.st child).life == .alive) = true
      · simp only [hc, ite_true]
        rw [ih, shutdownActor_N, dropDescendants_N]
      · have hf : (isChild acc parent child && (acc.st child).life == .alive) = false := by
          cases hb : isChild acc parent child && (acc.st child).life == .alive with
          | false => rfl
          | true => exact absurd hb hc
        simp only [hf]
        exact ih acc
  exact hfold w.roster w

theorem commitCont_N (w : World) (id : InstId) (next : Actor) :
    (commitCont w id next).N = w.N := by
  unfold commitCont
  by_cases hcr : w.crashed = true
  · simp [hcr]
  · have hf : w.crashed = false := by
      cases hb : w.crashed with
      | false => rfl
      | true => exact absurd hb hcr
    simp [hf, setActor]

theorem performReply_N (w : World) (sender : InstId) (k : Cont) :
    (performReply w sender k).N = w.N := by
  unfold performReply
  dsimp
  split <;> (try split) <;> (try split) <;> rfl

theorem admit_N (I : Impl) (w : World) (id : InstId) (a : Actor) :
    (admitBorn I w id a).N = w.N := by
  unfold admitBorn
  rw [readCells_N]
  simp [setActor]

/-- A child birth is `admitBorn` or the identity. Neither changes the population bound. -/
theorem spawnChild_N (I : Impl) (w w' : World) (parent : InstId) (child : String)
    (h : spawnChild I w parent child = some w') : w'.N = w.N := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = true
    · simp only [hgo, ite_true] at h
      cases parent with
      | core _ => simp at h
      | peer pn pk pg =>
        by_cases hblk : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = true
        · simp [hblk] at h
          cases h
          rfl
        · have hf : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblk
          simp only [hf] at h
          cases h
          exact admit_N I w _ _
    · have hf :
          (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf] at h
      by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hstay, ite_true] at h
        cases h
        rfl
      · have hstayF :
            (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hstay
        simp [hstayF] at h

theorem spawn_N (I : Impl) (w w' : World) (template : String)
    (h : spawn I w template = some w') : w'.N = w.N := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some name =>
        rw [hsup] at h
        cases h
        exact place_N I w template (freshKey I.desc w t.subtree) t.initial
          (some (InstId.core name)) (fun u =>
            { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
          (fun _ => rfl)
      | none =>
        rw [hsup] at h
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at h
          cases h
          exact place_N I w template (w.nextIx template) t.initial none
            (fun u => { u with nextIx := fun n =>
                if n = template then w.nextIx template + 1 else u.nextIx n })
            (fun _ => rfl)
        · have hf : (t.subtree == "") = false := by
            cases hb : t.subtree == "" with
            | false => rfl
            | true => exact absurd hb hempty
          rw [hf] at h
          cases h
          exact place_N I w template (freshKey I.desc w t.subtree) t.initial none
            (fun u => { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            (fun _ => rfl)
    · simp [hmay] at h

theorem execRun_N (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont) :
    (execRun I w id a k).N = w.N := by
  by_cases hlive : (a.life == .alive) = true
  · cases hk : k.rest with
    | nil => simp [execRun, hlive, hk, setActor]
    | cons e es =>
      cases e with
      | send dst label hint =>
        cases hr : route w I.desc id dst with
        | none => simp [execRun, hlive, hk, hr, setActor, noteStale]
        | some dstId => simp [execRun, hlive, hk, hr, mail_N]
      | trySend dst label hint onFull onGone =>
        cases hr : route w I.desc id dst with
        | none => simp [execRun, hlive, hk, hr, setActor, noteStale]
        | some dstId =>
          by_cases hroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
              decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = true
          · simp [execRun, hlive, hk, hr, hroom, mail_N]
          · have hfroom : ((w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
                decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = false := by
              cases hb : (w.st dstId).life == .alive && decide ((w.st dstId).parked = []) &&
                  decide ((w.st dstId).box.length < capBulk I.desc w.N dstId) with
              | false => rfl
              | true => exact absurd hb hroom
            by_cases haliveT : ((w.st dstId).life == .alive) = true
            · have hrest : (decide ((w.st dstId).parked = []) &&
                  decide ((w.st dstId).box.length < capBulk I.desc w.N dstId)) = false := by
                cases hb1 : decide ((w.st dstId).parked = []) <;>
                  cases hb2 : decide ((w.st dstId).box.length < capBulk I.desc w.N dstId) <;>
                  simp [haliveT, hb1, hb2] at hfroom <;> rfl
              simp [execRun, hlive, hk, hr, haliveT, hrest, setActor]
            · have hdead : ((w.st dstId).life == .alive) = false := by
                cases hb : (w.st dstId).life == .alive with
                | false => rfl
                | true => exact absurd hb haliveT
              simp [execRun, hlive, hk, hr, hdead, setActor]
      | call dst label hint onNotAdmitted onTimedOut =>
        cases hr : resolveId I.desc w id dst with
        | none => simp [execRun, hlive, hk, hr, setActor, noteStale]
        | some dstId => simp [execRun, hlive, hk, hr, mail_N]
      | reply => simp [execRun, hlive, hk, performReply_N]
      | selfSchedule label =>
        by_cases hany : (a.prio.any (fun p => p.label == label)) = true
        · simp [execRun, hlive, hk, hany, setActor]
        · have hfany : (a.prio.any (fun p => p.label == label)) = false := by
            cases hb : a.prio.any (fun p => p.label == label) with
            | false => rfl
            | true => exact absurd hb hany
          by_cases hroom : prioLoad a.prio < capPrio I.desc w.N id
          · simp [execRun, hlive, hk, hfany, hroom, setActor]
          · simp [execRun, hlive, hk, hfany, hroom, crashWorld]
      | cell dst label value =>
        by_cases hdirty : (w.cell dst label).dirty = true
        · simp [execRun, hlive, hk, hdirty, setCell, setActor]
        · have hf : (w.cell dst label).dirty = false := by
            cases hb : (w.cell dst label).dirty with
            | false => rfl
            | true => exact absurd hb hdirty
          simp [execRun, hlive, hk, hf, setCell, setActor, wakeReaders_N]
      | internal => simp [execRun, hlive, hk, setActor]
      | peer _ => simp [execRun, hlive, hk, setActor]
      | abort => simp [execRun, hlive, hk, abortChildren_N, commitCont_N]
      | spawn child =>
        cases hs : spawnChild I w id child with
        | none => simp [execRun, hlive, hk, hs, crashWorld]
        | some w1 =>
          have h1 := spawnChild_N I w w1 id child hs
          by_cases hcr : w1.crashed = true
          · simp [execRun, hlive, hk, hs, commitCont, hcr, h1]
          · have hcf : w1.crashed = false := by
              cases hb : w1.crashed with
              | false => rfl
              | true => exact absurd hb hcr
            simp [execRun, hlive, hk, hs, commitCont, hcf, h1, setActor]
      | terminate =>
        have hlive' : a.life = .alive := by simpa [beq_iff_eq] using hlive
        rcases execRun_terminate I w id a k hlive' ⟨es, hk⟩ with hcrash | hlone | htree | hcascade
        · rw [hcrash]
          simp [crashWorld]
        · obtain ⟨_, _, _, _, _, _, _, hr⟩ := hlone
          rw [hr]
          exact shutdownActor_N I.desc w id
        · obtain ⟨_, _, _, _, hr⟩ := htree
          rw [hr]
          exact terminateStage_N I.desc w id a
        · obtain ⟨_, _, _, _, _, _, _, hr⟩ := hcascade
          rw [hr]
          exact terminateStage_N I.desc w id a
  · have hf : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [execRun, hf]

theorem execHead_N (I : Impl) (w w' : World) (id : InstId)
    (h : execHead I w id = some w') : w'.N = w.N := by
  unfold execHead at h
  by_cases hnot : (w.st id).life ≠ .alive
  · simp [hnot] at h
  · simp [hnot] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      exact execRun_N I w id (w.st id) k
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem receiveBulk_N (I : Impl) (w w' : World) (id : InstId)
    (h : receiveBulk I w id = some w') : w'.N = w.N := by
  unfold receiveBulk at h
  dsimp at h
  split at h
  · simp at h
  · cases hbox : (w.st id).box with
    | nil =>
      cases hpark : (w.st id).parked with
      | nil => simp [hbox, hpark] at h
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with parked := ps }) p.msg with
        | none =>
          simp only [hbox] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hbox] at hd
          rw [hd] at h
          have hN := deliver_N I w id _ p.msg w1 a' hd
          cases h
          simp [setActor, creditLive_N, hN]
    | cons m ms =>
      cases hpark : (w.st id).parked with
      | nil =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          have hN := deliver_N I w id _ m w1 a' hd
          cases h
          simp [setActor, creditLive_N, hN]
      | cons p ps =>
        simp only [hbox, hpark] at h
        cases hd : deliver I w id ({ (w.st id) with box := ms }) m with
        | none =>
          simp only [hpark] at hd
          rw [hd] at h
          simp at h
        | some pair =>
          obtain ⟨w1, a'⟩ := pair
          simp only [hpark] at hd
          rw [hd] at h
          have hN := deliver_N I w id _ m w1 a' hd
          cases h
          simp [setActor, creditLive_N, hN]

theorem receivePrio_N (I : Impl) (w w' : World) (id : InstId)
    (h : receivePrio I w id = some w') : w'.N = w.N := by
  obtain ⟨_m, pre, suf, w1, a1, _, _, _, _, hdel, hw'⟩ := receivePrio_spec I w w' id h
  have hN := deliver_N I w id { (w.st id) with prio := pre ++ suf } _m w1 a1 hdel
  rw [hw']
  simp [setActor, hN]

theorem finish_N (I : Impl) (w w' : World) (id : InstId)
    (h : finishWait I w id = some w') : w'.N = w.N := by
  obtain ⟨_k, _, hw⟩ := finish_proceed I w w' id h
  rw [hw]
  rfl

theorem ingress_N (I : Impl) (w w' : World) (dst : InstId) (label : String)
    (h : receiveIngress I w dst label = some w') : w'.N = w.N :=
  (ingress_phase I w w' dst label dst h).2.2.2.2.2.1

theorem timeout_N (w w' : World) (id : InstId) (h : callTimeout w id = some w') : w'.N = w.N := by
  dsimp [callTimeout] at h
  split at h
  · simp at h
  · cases hph : (w.st id).phase with
    | awaitReply dst k =>
      simp [hph] at h
      cases h
      rfl
    | parked dst isCall k =>
      simp [hph] at h
      cases isCall with
      | false => simp at h
      | true =>
        cases h
        simp [setActor, refundCall_N]
    | awaitPeer k =>
      simp [hph] at h
      cases h
      rfl
    | idle => simp [hph] at h
    | run _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | crashed => simp [hph] at h

theorem step_N (I : Impl) (a : Action) (w w' : World) (h : stepWorld I a w = some w') :
    w'.N = w.N := by
  cases a with
  | recvBulk s =>
    simp only [stepWorld] at h
    exact receiveBulk_N I w w' s h
  | recvPrio s =>
    simp only [stepWorld] at h
    exact receivePrio_N I w w' s h
  | exec s =>
    simp only [stepWorld] at h
    exact execHead_N I w w' s h
  | finish s =>
    simp only [stepWorld] at h
    exact finish_N I w w' s h
  | spawn template =>
    simp only [stepWorld] at h
    exact spawn_N I w w' template h
  | ingress dst label =>
    simp only [stepWorld] at h
    exact ingress_N I w w' dst label h
  | callTimeout s =>
    simp only [stepWorld] at h
    exact timeout_N w w' s h
  | stutter =>
    simp only [stepWorld] at h
    split at h
    · cases h
    · cases h
      rfl

/-- Every world reachable at population `N` still has that population. -/
theorem reach_N (I : Impl) (N : Nat) (w : World) (hR : Reachable I N w) : w.N = N := by
  induction hR with
  | init => exact init_N I N
  | step w w' a prev ha ih =>
    exact (step_N I a w w' (apply_step I a w w' ha).2).trans ih

/-! A core-supervised root's held keys are the generations `rootOutstanding`
counts: alive, or a tombstone still on the live core. -/

/-- One queued subtree message, with the sender `slotMailHeld` is looking at. -/
theorem subtree_hold_sender (D : Description) (w : World) (sub : String) (k : Nat)
    (h : subtreeCoreMail D w sub k = true) :
    ∃ host sender, host ∈ w.roster ∧ isMember D sender sub k = true ∧
      survivesSender w sender host = true ∧
      ((∃ m, m ∈ (w.st host).box ∧ m.sender = sender) ∨
        (∃ m, m ∈ (w.st host).prio ∧ m.sender = sender) ∨
        (∃ p, p ∈ (w.st host).parked ∧ (p.sender = sender ∨ p.msg.sender = sender))) := by
  unfold subtreeCoreMail at h
  obtain ⟨host, hhost, hhold⟩ := _root_.List.any_eq_true.mp h
  unfold actorHoldsSubtreeMail at hhold
  simp only [fromSubtree, Bool.or_eq_true] at hhold
  rcases hhold with (hbox | hprio) | hpark
  · obtain ⟨m, hm, hheld⟩ := _root_.List.any_eq_true.mp hbox
    simp only [Bool.and_eq_true] at hheld
    exact ⟨host, m.sender, hhost, hheld.1, hheld.2, Or.inl ⟨m, hm, rfl⟩⟩
  · obtain ⟨m, hm, hheld⟩ := _root_.List.any_eq_true.mp hprio
    simp only [Bool.and_eq_true] at hheld
    exact ⟨host, m.sender, hhost, hheld.1, hheld.2, Or.inr (Or.inl ⟨m, hm, rfl⟩)⟩
  · obtain ⟨p, hp, hheld⟩ := _root_.List.any_eq_true.mp hpark
    simp only [Bool.or_eq_true] at hheld
    rcases hheld with hheld | hheld
    · simp only [Bool.and_eq_true] at hheld
      exact ⟨host, p.sender, hhost, hheld.1, hheld.2, Or.inr (Or.inr ⟨p, hp, Or.inl rfl⟩)⟩
    · simp only [Bool.and_eq_true] at hheld
      exact ⟨host, p.msg.sender, hhost, hheld.1, hheld.2, Or.inr (Or.inr ⟨p, hp, Or.inr rfl⟩)⟩

/-- A core-supervised root is wired to that core. `rootOf` says the supervisor
is multiplicity one, and a multiplicity-one roster actor is a core. -/
theorem root_core_parent (I : Impl) (w : World) (hF : ParentForest w) (hP : Parented I.desc w)
    (hH : Hold I w) (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hmem : InstId.peer name k g ∈ w.roster) (sup : String) (hsup : t.supervisor = some sup) :
    (w.st (InstId.peer name k g)).parent = some (InstId.core sup) := by
  have hp := hP (InstId.peer name k g) t hmem (by simpa [tname] using ht)
  rw [hsup] at hp
  obtain ⟨p, hpar, htn, _⟩ := hp
  have hmemP : p ∈ w.roster := hF.hosted _ _ hpar
  obtain ⟨tp, htp, hrole⟩ := hH.role p hmemP
  simp only [rootOf, hsup] at hroot
  cases htS : templateOf I.desc sup with
  | none => simp [htS] at hroot
  | some tS =>
    simp only [htS] at hroot
    have hone : tS.multiplicity = .one := by
      cases hmul : tS.multiplicity with
      | one => rfl
      | perPeer =>
        rw [hmul] at hroot
        have hbeq : (Multiplicity.perPeer == Multiplicity.one) = false := rfl
        rw [hbeq] at hroot
        cases hroot
    have htp' : templateOf I.desc (tname p) = some tp := htp
    rw [htn] at htp'
    have hsame : tp = tS := by
      injection htp'.symm.trans htS
    cases p with
    | core n =>
      have hn : n = sup := by simpa [tname] using htn
      simpa [hn] using hpar
    | peer n pk pg =>
      have hbad : tp.multiplicity = .perPeer := by simpa [tmb_role] using hrole
      rw [hsame, hone] at hbad
      cases hbad

/-- The first parent step of a strict-ancestor chain is the recorded parent. -/
theorem parent_step (w : World) (sender host root : InstId)
    (hpar : (w.st sender).parent = some host) (hs : StrictAncestor w sender root) :
    host = root ∨ StrictAncestor w host root := by
  cases hs with
  | edge he =>
    left
    have hp := he.1
    rw [hpar] at hp
    injection hp
  | tail he hrest =>
    right
    have hp := he.1
    rw [hpar] at hp
    injection hp with hmid
    simpa [hmid] using hrest

/-- A dead core-supervised root whose subtree mail is still held has its
tombstone on the live core. Program mail is `mailInFlight`, and
`member_mail_tomb` turns that into the tombstone. A tombstone already on a
priority lane sits on the dead sender's parent (`BirthInv.tombOnParent`): the
parent of a descendant is dead with the root, so the only live host is the
core. Parked mail from that sender is either still blocking, which keeps the
sender alive, or halted, which `ParkedFromLive` has already dropped. -/
theorem dead_root_tomb (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hB : BirthInv I.desc w) (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hcr : w.crashed = false) (name : String) (k g : Nat) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (hmem : InstId.peer name k g ∈ w.roster)
    (hdead : (w.st (InstId.peer name k g)).life = .dead)
    (hmail : slotMailHeld I.desc w name k = true) (sup : String) (hsup : t.supervisor = some sup)
    (hlive : (w.st (InstId.core sup)).life = .alive) :
    slotTombstoneQueued w (InstId.core sup) name k = true := by
  have hS : SemInv I w := hI.1
  have hM : MailInv w := hI.2.1
  have hF : ParentForest w := hI.forest
  have hSeal : SealInv w := hI.seal
  have hpar :=
    root_core_parent I w hF hB.parented hH name k g t ht hroot hmem sup hsup
  have hne : (t.subtree == "") = false := by simpa [beq_iff_eq] using hsub
  have hmailS : subtreeCoreMail I.desc w t.subtree k = true := by
    simpa [slotMailHeld, templateSubtree, ht, hne] using hmail
  obtain ⟨host, sender, hhost, hfrom, hsurv, hwhere⟩ := subtree_hold_sender I.desc w t.subtree k hmailS
  have hhostLive : (w.st host).life = .alive := by
    simp only [survivesSender, Bool.and_eq_true] at hsurv
    exact (beq_iff_eq).mp hsurv.1
  have hrootLive : (w.st sender).life = .alive → False := by
    intro hliveS
    have hmemS : sender ∈ w.roster := hS.rostered sender hliveS
    cases member_root_id I hG w hF hB.parented hB.noSelf hH hOne name k g t ht hroot hsub hmem
        sender hmemS hfrom with
    | inl heq =>
      have hdeadS : (w.st sender).life = .dead := by simpa [heq] using hdead
      exact life_dead_ne_alive (hdeadS.symm.trans hliveS)
    | inr hs =>
      exact life_dead_ne_alive (hdead.symm.trans (ancestor_alive w hSeal.childless hcr hs hliveS))
  have hflight (hmemS : sender ∈ w.roster) (m : Msg) (hm : m ∈ (w.st host).box ∨ m ∈ (w.st host).prio)
      (htomb : m.tombstone = false) (hsend : m.sender = sender) : mailInFlight w sender = true := by
    exact flight_of_msg w sender host m hhost hhostLive htomb
      (by simp [sealedTogether, hsend]) (by simpa [hsend] using hm)
  rcases hwhere with hbox | hprio | hpark
  · obtain ⟨m, hm, hsend⟩ := hbox
    have hmemS := hSeal.hostedMail host m (Or.inl hm)
    rw [hsend] at hmemS
    exact member_mail_tomb I hG w hF hB.parented hB.noSelf hH hOne hSeal.chain hcr name k g t
      ht hroot hsub hmem hdead (InstId.core sup) hpar hlive sender hmemS hfrom
      (hflight hmemS m (Or.inl hm) (hB.plainBox host m hm) hsend)
  · obtain ⟨m, hm, hsend⟩ := hprio
    have hmemS := hSeal.hostedMail host m (Or.inr hm)
    rw [hsend] at hmemS
    by_cases htom : m.tombstone = true
    · have hon := hB.tombOnParent host m hm htom
      cases sender with
      | core _ => simp [isMember] at hfrom
      | peer sn sk sg =>
        simp only [hsend] at hon
        obtain ⟨_, hparentS, _⟩ := hon
        cases member_root_id I hG w hF hB.parented hB.noSelf hH hOne name k g t ht hroot hsub hmem
            (.peer sn sk sg) hmemS hfrom with
        | inl heq =>
          have hhostId : host = InstId.core sup := by
            have hparentR : (w.st (InstId.peer name k g)).parent = some host := by
              simpa [heq] using hparentS
            rw [hpar] at hparentR
            injection hparentR with hhostId
            exact hhostId.symm
          have hqueued := holds_slot w host name k g
            ⟨m, hm, htom, by simpa [heq] using hsend⟩
          simpa [hhostId] using hqueued
        | inr hs =>
          cases parent_step w (.peer sn sk sg) host (InstId.peer name k g) hparentS hs with
          | inl hhostR =>
            exact False.elim (life_dead_ne_alive
              (hdead.symm.trans (by simpa [hhostR] using hhostLive)))
          | inr hrest =>
            exact False.elim (life_dead_ne_alive
              (hdead.symm.trans (ancestor_alive w hSeal.childless hcr hrest hhostLive)))
    · have hplain : m.tombstone = false := by
        cases htomb : m.tombstone with
        | false => rfl
        | true => exact absurd htomb htom
      exact member_mail_tomb I hG w hF hB.parented hB.noSelf hH hOne hSeal.chain hcr name k g t
        ht hroot hsub hmem hdead (InstId.core sup) hpar hlive sender hmemS hfrom
        (hflight hmemS m (Or.inr hm) hplain hsend)
  · obtain ⟨p, hp, hwho⟩ := hpark
    have hps : p.sender = sender := by
      rcases hwho with hwho | hwho
      · exact hwho
      · exact (hSeal.parkedFrom host p hp).trans hwho
    rcases hM.fwd host p hp with ⟨_, hph⟩ | hhalt
    · rw [hps] at hph
      have hliveS : (w.st sender).life = .alive := by
        apply Classical.byContradiction
        intro hne
        rcases hS.idleOff sender hne with hidle | hcrash
        · rw [hph] at hidle
          cases hidle
        · rw [hph] at hcrash
          cases hcrash
      exact False.elim (hrootLive hliveS)
    · exact False.elim (hSeal.liveParked host p hhostLive hp (by
        simpa [Halted, hps] using hhalt))

/-- A bit that implies another bit is counted no more often. -/
theorem fold_count_le (b1 b2 : InstId → Bool) :
    ∀ (ids : List InstId),
      (∀ id, id ∈ ids → b1 id = true → b2 id = true) →
      ∀ n, ids.foldl (fun n id => if b1 id = true then n + 1 else n) n ≤
        ids.foldl (fun n id => if b2 id = true then n + 1 else n) n := by
  intro ids
  induction ids with
  | nil =>
    intro _ n
    simp
  | cons id ids ih =>
    intro h n
    simp only [List.foldl_cons]
    have hhead := h id (List.Mem.head _)
    have htail : ∀ id', id' ∈ ids → b1 id' = true → b2 id' = true :=
      fun id' hmem => h id' (List.Mem.tail _ hmem)
    by_cases hb : b1 id = true
    · have hb2 := hhead hb
      rw [ite_eq_left hb, ite_eq_left hb2]
      exact ih htail (n + 1)
    · rw [ite_eq_right hb]
      by_cases hb2 : b2 id = true
      · rw [ite_eq_left hb2]
        have htailLe := ih htail n
        have hshift := step_shift b2 ids n 1
        rw [hshift]
        exact Nat.le_trans htailLe (Nat.le_succ _)
      · rw [ite_eq_right hb2]
        exact ih htail n

/-- A generation that holds a core-supervised root's key is alive, or the core
still has its tombstone. A dead generation's held mail is that tombstone
(`dead_root_tomb`). -/
theorem lone_implies_root (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hB : BirthInv I.desc w) (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hcr : w.crashed = false) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (sup : String) (hsup : t.supervisor = some sup)
    (hlive : (w.st (InstId.core sup)).life = .alive) (id : InstId) (hmem : id ∈ w.roster)
    (hb : loneBit I.desc w name id = true) : rootBit I.desc w sup name id = true := by
  cases id with
  | core _ => simp [loneBit] at hb
  | peer child key gen =>
    simp only [loneBit, Bool.and_eq_true] at hb
    have heq : child = name := by simpa [beq_iff_eq] using hb.1
    rw [heq] at hmem hb
    by_cases hliveId : (w.st (InstId.peer name key gen)).life = .alive
    · have hbA : ((w.st (InstId.peer name key gen)).life == .alive) = true := by
        simpa [beq_iff_eq] using hliveId
      simp [rootBit, heq, hbA]
    · have hflag := hb.2
      have hmail : slotMailHeld I.desc w name key = true := by
        cases hbb : (w.st (InstId.peer name key gen)).life == .alive with
        | true => exact absurd ((beq_iff_eq).mp hbb) hliveId
        | false =>
          rw [hbb, Bool.false_or] at hflag
          exact hflag
      have hdead : (w.st (InstId.peer name key gen)).life = .dead := by
        cases hl : (w.st (InstId.peer name key gen)).life with
        | alive => exact absurd hl hliveId
        | absent => exact absurd hl (hB.present _ hmem)
        | dead => rfl
      have htomb := dead_root_tomb I hG w hI hB hH hOne hcr name key gen t ht hroot hsub hmem
        hdead hmail sup hsup hlive
      simp [rootBit, heq, htomb]

theorem bitKeys_le_root (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hB : BirthInv I.desc w) (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hcr : w.crashed = false) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (sup : String) (hsup : t.supervisor = some sup)
    (hlive : (w.st (InstId.core sup)).life = .alive) :
    (bitKeys I.desc w name).length ≤ rootOutstanding I.desc w sup name := by
  have hcard := card_go (loneBit I.desc w name) (bitKey name) w.roster [] (by simp)
  have himp : ∀ id, id ∈ w.roster →
      loneBit I.desc w name id = true → rootBit I.desc w sup name id = true :=
    fun id hmem hb =>
      lone_implies_root I hG w hI hB hH hOne hcr name t ht hroot hsub sup hsup hlive id hmem hb
  have hcount :=
    fold_count_le (loneBit I.desc w name) (rootBit I.desc w sup name) w.roster himp 0
  have hfold : rootOutstanding I.desc w sup name =
      w.roster.foldl (fun n id => if rootBit I.desc w sup name id = true then n + 1 else n) 0 := by
    rw [root_filter]
    exact (fold_count (rootBit I.desc w sup name) w.roster).symm
  have hlen : (bitKeys I.desc w name).length ≤
      w.roster.foldl (fun n id => if loneBit I.desc w name id = true then n + 1 else n) 0 := by
    simpa [bitKeys, Nat.zero_add] using hcard
  exact Nat.le_trans hlen (by simpa [hfold] using hcount)

/-- Held keys of a core-supervised root are at most the generations that root's
core still counts: each held key has a generation that is alive or whose
tombstone is queued. The core is the live supervisor `maySpawnRoot` checks. -/
theorem held_le_root (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hI : Inv I w) (hB : BirthInv I.desc w) (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hcr : w.crashed = false) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (sup : String) (hsup : t.supervisor = some sup)
    (hlive : (w.st (InstId.core sup)).life = .alive) :
    (heldKeys I.desc w name).length ≤ rootOutstanding I.desc w sup name :=
  Nat.le_trans (held_le_bit I.desc w name)
    (bitKeys_le_root I hG w hI hB hH hOne hcr name t ht hroot hsub sup hsup hlive)

/-- In a reachable world the same count holds. `lane_birth` is the copy of
`birth_reachable` this file can see. -/
theorem held_le_root_reachable (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hcr : w.crashed = false) (name : String) (t : Template)
    (ht : templateOf I.desc name = some t) (hroot : rootOf I.desc t = true)
    (hsub : t.subtree ≠ "") (sup : String) (hsup : t.supervisor = some sup)
    (hlive : (w.st (InstId.core sup)).life = .alive) :
    (heldKeys I.desc w name).length ≤ rootOutstanding I.desc w sup name :=
  held_le_root I hG w (inv_reachable I N w hL hR) (lane_birth I hL hG N w hR)
    (hold_reach I N w hG hR) (oneCohort_reachable I hG N w hR) hcr name t ht hroot hsub sup hsup
    hlive

/-! A per-peer child's held keys are its parent's. `birth_supervised` says
`GraphOk` gives that child a nonempty subtree, so there is no empty-subtree
child whose mail could outlive the parent. A core supervisor makes the template
itself the subtree root, counted by `rootOutstanding`. -/

/-- A per-peer supervisor is the peer at this actor's own key. -/
theorem peer_parent (I : Impl) (w : World) (hF : ParentForest w) (hP : Parented I.desc w)
    (hH : Hold I w) (child : String) (k g : Nat) (t ts : Template) (supName : String)
    (hmem : InstId.peer child k g ∈ w.roster) (ht : templateOf I.desc child = some t)
    (hsup : t.supervisor = some supName) (hts : templateOf I.desc supName = some ts)
    (hmul : ts.multiplicity = .perPeer) :
    ∃ gP, InstId.peer supName k gP ∈ w.roster ∧
      (w.st (InstId.peer child k g)).parent = some (InstId.peer supName k gP) := by
  have hp := hP (InstId.peer child k g) t hmem (by simpa [tname] using ht)
  rw [hsup] at hp
  obtain ⟨p, hpar, htn, hrest⟩ := hp
  have hmemP : p ∈ w.roster := hF.hosted _ _ hpar
  cases p with
  | core n =>
    obtain ⟨tp, htp, hrole⟩ := hH.role (.core n) hmemP
    have htp' : templateOf I.desc n = some tp := by simpa [tname] using htp
    have hn : n = supName := by simpa [tname] using htn
    rw [hn] at htp'
    have hsame : tp = ts := by injection htp'.symm.trans hts
    have hone : ts.multiplicity = .one := by
      simpa [tmb_role, hsame] using hrole
    cases hone.symm.trans hmul
  | peer n pk pg =>
    have hn : n = supName := by simpa [tname] using htn
    have hkeyEq : memberKey (InstId.peer child k g) = some pk := hrest
    simp [memberKey] at hkeyEq
    have hpk : pk = k := hkeyEq.symm
    exact ⟨pg, by simpa [hn, hpk] using hmemP, by simpa [hn, hpk] using hpar⟩

/-- Two templates of one nonempty subtree hold a key for the same mail. -/
theorem slot_mail_same (D : Description) (w : World) (name1 name2 sub : String) (k : Nat)
    (h1 : templateSubtree D name1 = sub) (h2 : templateSubtree D name2 = sub) (hne : sub ≠ "") :
    slotMailHeld D w name1 k = slotMailHeld D w name2 k := by
  have hneB : (sub == "") = false := by simpa [beq_iff_eq] using hne
  simp [slotMailHeld, h1, h2, hneB]

/-- A key held by a per-peer child is held by its per-peer parent. The parent
is the peer at the same key. Alive children keep that parent alive; held mail
is the shared subtree's mail, so it holds the parent's key as well. -/
theorem held_in_parent (I : Impl) (hG : GraphOk I.desc) (w : World) (hcr : w.crashed = false)
    (hP : Parented I.desc w) (hF : ParentForest w) (hH : Hold I w) (hKids : DeadChildless w)
    (child supName : String) (t ts : Template) (ht : templateOf I.desc child = some t)
    (hts : templateOf I.desc supName = some ts) (hsup : t.supervisor = some supName)
    (hmul : ts.multiplicity = .perPeer) (k : Nat) (hk : k ∈ heldKeys I.desc w child) :
    k ∈ heldKeys I.desc w supName := by
  obtain ⟨id, hid, hbit, hkey⟩ := (heldKeys_mem I.desc w child k).mp hk
  cases id with
  | core _ => simp [heldBit] at hbit
  | peer n key g =>
    simp only [heldBit, Bool.and_eq_true] at hbit
    simp only [bitKey] at hkey
    have hn : n = child := by simpa [beq_iff_eq] using hbit.1
    rw [hn] at hid hbit
    rw [hkey] at hid
    have hheld : heldAt I.desc w child k = true := by simpa [hkey] using hbit.2
    have hmulC : t.multiplicity = .perPeer :=
      member_per I.desc hG child t ht (birth_supervised I.desc hG child t ht supName hsup)
    have hshare :=
      per_sup_same I.desc hG child t ht hmulC supName hsup ts hts hmul
    obtain ⟨gP, hmemP, _⟩ :=
      peer_parent I w hF hP hH child k g t ts supName hid ht hsup hts hmul
    by_cases hmail : slotMailHeld I.desc w child k = true
    · have hsubC : templateSubtree I.desc child = t.subtree := by simp [templateSubtree, ht]
      have hsubP : templateSubtree I.desc supName = ts.subtree := by simp [templateSubtree, hts]
      have hmailP : slotMailHeld I.desc w supName k = true := by
        rw [← slot_mail_same I.desc w child supName t.subtree k hsubC
          (by rw [hsubP, hshare.1]) (birth_supervised I.desc hG child t ht supName hsup)]
        exact hmail
      have hparentHeld : heldAt I.desc w supName k = true := by
        unfold heldAt
        apply _root_.List.any_eq_true.mpr
        refine ⟨InstId.peer supName k gP, hmemP, ?_⟩
        simp [hmailP]
      exact (heldKeys_mem I.desc w supName k).mpr
        ⟨InstId.peer supName k gP, hmemP, by simp [heldBit, hparentHeld], by simp [bitKey]⟩
    · unfold heldAt at hheld
      obtain ⟨idA, hidA, hbA⟩ := _root_.List.any_eq_true.mp hheld
      cases idA with
      | core _ => simp at hbA
      | peer nA kA gA =>
        simp only [Bool.and_eq_true] at hbA
        have hnA : nA = child := by simpa [beq_iff_eq] using hbA.1.1
        have hkA : kA = k := by simpa [beq_iff_eq] using hbA.1.2
        rw [hnA, hkA] at hidA hbA
        have hliveA : (w.st (InstId.peer child k gA)).life = .alive := by
          cases hbb : (w.st (InstId.peer child k gA)).life == .alive with
          | true => exact (beq_iff_eq).mp hbb
          | false =>
            rw [hbb, Bool.false_or] at hbA
            exact absurd hbA.2 hmail
        obtain ⟨gL, hmemL, hparL⟩ :=
          peer_parent I w hF hP hH child k gA t ts supName hidA ht hsup hts hmul
        have hparentLive := kids_alive w hKids hcr _ _ hliveA hparL
        have hparentHeld : heldAt I.desc w supName k = true := by
          unfold heldAt
          apply _root_.List.any_eq_true.mpr
          refine ⟨InstId.peer supName k gL, hmemL, ?_⟩
          simp [hparentLive]
        exact (heldKeys_mem I.desc w supName k).mpr
          ⟨InstId.peer supName k gL, hmemL, by simp [heldBit, hparentHeld], by simp [bitKey]⟩

/-- Birthing one template does not hold a new key of another. The fresh actor's
mailbox is empty and no older actor names it as a parent, so `slot_mail_birth`
says every other template's mail was already held. -/
theorem held_birth_other (D : Description) (w w' : World) (name : String) (fresh : InstId)
    (hF : ParentForest w) (hnew : fresh ∉ w.roster) (hrosEq : w'.roster = w.roster ++ [fresh])
    (hst : ∀ i, i ≠ fresh → w'.st i = w.st i)
    (hempty : (w'.st fresh).box = [] ∧ (w'.st fresh).prio = [] ∧ (w'.st fresh).parked = [])
    (hother : tname fresh ≠ name) :
    ∀ key, key ∈ heldKeys D w' name → key ∈ heldKeys D w name := by
  have hno : ∀ i, (w.st i).parent ≠ some fresh := by
    intro i hp
    exact hnew (hF.hosted i fresh hp)
  refine held_sub D w w' name ?_ ?_ ?_
  · intro id hid hname
    have hmem : id ∈ w.roster ++ [fresh] := by simpa [hrosEq] using hid
    rcases List.mem_append.mp hmem with hold | hfresh
    · exact hold
    · simp at hfresh
      exact absurd (by simpa [hfresh] using hname) hother
  · intro id hid hlive
    have hne : id ≠ fresh := by
      intro heq
      exact hnew (heq ▸ hid)
    rw [hst id hne] at hlive
    exact hlive
  · intro key hmail
    exact Or.inl (slot_mail_birth D w w' fresh name hrosEq hst hempty hno key hmail)

/-- A child birth does not grow a different template's held keys. An identity
birth, including a blocked respawn, leaves every key where it was. -/
theorem held_child_other (I : Impl) (w w' : World) (parent : InstId) (child name : String)
    (hF : ParentForest w) (hother : child ≠ name) (h : spawnChild I w parent child = some w') :
    ∀ key, key ∈ heldKeys I.desc w' name → key ∈ heldKeys I.desc w name := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hgo :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = true
    · simp only [hgo, ite_true] at h
      cases parent with
      | core _ => simp at h
      | peer pn pk pg =>
        by_cases hblk : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = true
        · simp [hblk] at h
          cases h
          intro key hk
          exact hk
        · have hf : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pn pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblk
          simp only [hf] at h
          cases h
          let id := InstId.peer child pk (maxGen w child pk)
          let born :=
            { bornActor I.desc w child pk t.initial with parent := some (InstId.peer pn pk pg) }
          have hotherName : tname id ≠ name := by simp [id, tname, hother]
          refine held_birth_other I.desc w _ name id hF (gen_fresh w child pk)
            (admit_roster I w id born) ?_ ?_ hotherName
          · intro i hi
            exact admit_st_other I w id i born hi
          · have hself := admit_st_self I w id born
            rw [hself]
            simp [born, bornActor, withKeyTokens]
    · have hf :
          (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hgo
      simp only [hf] at h
      by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · simp only [hstay, ite_true] at h
        cases h
        intro key hk
        exact hk
      · have hstayF :
            (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hstay
        simp [hstayF] at h

/-- An executed `spawn` is `spawnChild` and then the parent's continuation.
Birthing `child` does not grow another template's held keys, and the
continuation only rewrites the parent's phase. A refused spawn crashes, which
drops no key into a new slot. -/
theorem held_spawn_run (I : Impl) (w : World) (id : InstId) (a : Actor) (k : Cont)
    (es : List Eff) (child name : String) (hF : ParentForest w)
    (hk : k.rest = .spawn child :: es) (hother : child ≠ name) :
    ∀ key, key ∈ heldKeys I.desc (execRun I w id a k) name → key ∈ heldKeys I.desc w name := by
  intro key hmem
  by_cases hlive : (a.life == .alive) = true
  · simp only [execRun, hlive, hk] at hmem
    cases hs : spawnChild I w id child with
    | none =>
      simp only [hs] at hmem
      exact held_crash I.desc w name key hmem
    | some w1 =>
      simp only [hs] at hmem
      have hp := proceed_fields (w1.st id) (afterHead k)
      exact held_child_other I w w1 id child name hF hother hs key
        (held_commit I.desc w1 id (proceed (w1.st id) (afterHead k)) name
          hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1 hp.2.1 hp.1 key hmem)
  · have hf : (a.life == .alive) = false := by
      cases hb : a.life == .alive with
      | false => rfl
      | true => exact absurd hb hlive
    simp [execRun, hf] at hmem
    exact hmem

/-- An empty subtree names no supervisor, so the template is a root.
`birth_supervised` is the checker fact: a supervisor without a subtree is rejected. -/
theorem empty_is_root (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (hempty : t.subtree = "") : rootOf D t = true := by
  cases hsup : t.supervisor with
  | none => simp [rootOf, hsup]
  | some n => exact absurd hempty (birth_supervised D hG name t ht n hsup)

/-- `spawnChild` does not birth a root. A root's supervisor is absent or a core,
and a peer executor is not that core. The result is the world unchanged. -/
theorem spawn_root_same (I : Impl) (w w' : World) (hH : Hold I w) (parent : InstId)
    (child : String) (hmem : parent ∈ w.roster) (h : spawnChild I w parent child = some w')
    (t : Template) (ht : templateOf I.desc child = some t) (hroot : rootOf I.desc t = true) :
    w' = w := by
  unfold spawnChild at h
  simp only [ht] at h
  by_cases hgo :
      (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
  · simp only [hgo, ite_true] at h
    cases parent with
    | core _ => simp at h
    | peer pn pk pg =>
      simp only [Bool.and_eq_true] at hgo
      have hnamed : t.supervisor = some pn := by
        simpa [tname] using sup_is pn t.supervisor hgo.1.2
      simp only [rootOf, hnamed] at hroot
      cases hts : templateOf I.desc pn with
      | none => simp [hts] at hroot
      | some ts =>
        simp only [hts] at hroot
        have hone : ts.multiplicity = .one := by
          cases hmul : ts.multiplicity with
          | one => rfl
          | perPeer =>
            rw [hmul] at hroot
            have hbeq : (Multiplicity.perPeer == Multiplicity.one) = false := rfl
            rw [hbeq] at hroot
            cases hroot
        obtain ⟨tp, htp, hrole⟩ := hH.role (InstId.peer pn pk pg) hmem
        have htp' : templateOf I.desc pn = some tp := by simpa [tname] using htp
        have hsame : tp = ts := by injection htp'.symm.trans hts
        have hper : tp.multiplicity = .perPeer := by simpa [tmb_role] using hrole
        rw [hsame, hone] at hper
        cases hper
  · have hf :
        (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = false := by
      cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive with
      | false => rfl
      | true => exact absurd hb hgo
    simp only [hf] at h
    by_cases hstay : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
    · simp only [hstay, ite_true] at h
      cases h
      rfl
    · have hstayF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
        | false => rfl
        | true => exact absurd hb hstay
      simp [hstayF] at h

/-- Placing a generation of one template does not hold a new key of another. -/
theorem held_place_other (I : Impl) (w : World) (template name : String) (k : Nat)
    (initial : String) (parent : Option InstId) (bump : World → World) (hF : ParentForest w)
    (hstB : ∀ u i, (bump u).st i = u.st i) (hrB : ∀ u, (bump u).roster = u.roster)
    (hother : template ≠ name) :
    ∀ key, key ∈ heldKeys I.desc (placePeer I w template k initial parent bump) name →
      key ∈ heldKeys I.desc w name := by
  let id := InstId.peer template k (maxGen w template k)
  have hst := place_st I w template k initial parent bump hstB
  have hros := place_roster I w template k initial parent bump hrB
  have hempty : ((placePeer I w template k initial parent bump).st id).box = [] ∧
      ((placePeer I w template k initial parent bump).st id).prio = [] ∧
      ((placePeer I w template k initial parent bump).st id).parked = [] := by
    have hid : (placePeer I w template k initial parent bump).st id =
        { bornActor I.desc w template k initial with parent := parent } := by
      simp [id, hst]
    simp [hid, bornActor, withKeyTokens]
  have hotherName : tname id ≠ name := by simp [id, tname, hother]
  refine held_birth_other I.desc w _ name id hF (gen_fresh w template k)
    (by simpa [id] using hros) ?_ hempty hotherName
  intro i hi
  have h := hst i
  simp [id, hi] at h
  exact h

/-- A scheduler spawn of another template does not grow this template's held keys. -/
theorem held_spawn_other (I : Impl) (w w' : World) (template name : String) (hF : ParentForest w)
    (hother : template ≠ name) (h : spawn I w template = some w') :
    ∀ key, key ∈ heldKeys I.desc w' name → key ∈ heldKeys I.desc w name := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · simp only [hmay, ite_true] at h
      cases hsup : t.supervisor with
      | some sname =>
        rw [hsup] at h
        cases h
        exact held_place_other I w template name (freshKey I.desc w t.subtree) t.initial
          (some (InstId.core sname)) (fun u =>
            { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
          hF (fun _ _ => rfl) (fun _ => rfl) hother
      | none =>
        rw [hsup] at h
        by_cases hempty : (t.subtree == "") = true
        · rw [hempty] at h
          cases h
          exact held_place_other I w template name (w.nextIx template) t.initial none
            (fun u => { u with nextIx := fun n =>
                if n = template then w.nextIx template + 1 else u.nextIx n })
            hF (fun _ _ => rfl) (fun _ => rfl) hother
        · have hf : (t.subtree == "") = false := by
            cases hb : t.subtree == "" with
            | false => rfl
            | true => exact absurd hb hempty
          rw [hf] at h
          cases h
          exact held_place_other I w template name (freshKey I.desc w t.subtree) t.initial none
            (fun u => { u with nextKey := fun s =>
                if s = t.subtree then freshKey I.desc w t.subtree + 1 else u.nextKey s })
            hF (fun _ _ => rfl) (fun _ => rfl) hother
    · simp [hmay] at h

/-- A spawn that returns a world was allowed by `maySpawnRoot`. -/
theorem spawn_may (I : Impl) (w w' : World) (template : String) (h : spawn I w template = some w') :
    ∃ t, templateOf I.desc template = some t ∧ maySpawnRoot I.desc w template t = true := by
  unfold spawn at h
  cases ht : templateOf I.desc template with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hmay : maySpawnRoot I.desc w template t = true
    · exact ⟨t, rfl, hmay⟩
    · simp [hmay] at h

/-- Spawning a root stays within `w.N`. An unsupervised root is bounded by
`loneOutstanding`. A core-supervised root is bounded by `rootOutstanding`, and
the live core is what `maySpawnRoot` checks. -/
theorem held_spawn_bound (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w w' : World) (hR : Reachable I N w) (hcr : w.crashed = false) (template : String)
    (h : spawn I w template = some w') :
    (heldKeys I.desc w' template).length ≤ w.N := by
  obtain ⟨t, ht, hmay⟩ := spawn_may I w w' template h
  have hF : ParentForest w := (inv_reachable I N w hL hR).forest
  unfold maySpawnRoot at hmay
  simp only [Bool.and_eq_true] at hmay
  cases hsup : t.supervisor with
  | none =>
    rw [hsup] at hmay
    have hlt : loneOutstanding I.desc w template < w.N := of_decide_eq_true hmay.2
    exact held_spawn_lone I w w' template hF h hlt
  | some sup =>
    rw [hsup] at hmay
    have hlt : rootOutstanding I.desc w sup template < w.N := of_decide_eq_true hmay.2
    have hlive : (w.st (InstId.core sup)).life = .alive := by
      have hsupLive := hmay.1.2
      unfold supervisorLive at hsupLive
      simp only [hsup] at hsupLive
      cases hts : templateOf I.desc sup with
      | none => simp [hts] at hsupLive
      | some ts =>
        simp only [hts] at hsupLive
        cases hmul : ts.multiplicity with
        | perPeer => simp [hmul] at hsupLive
        | one =>
          simp only [hmul] at hsupLive
          exact (beq_iff_eq).mp hsupLive
    have hroot : rootOf I.desc t = true := hmay.1.1.2
    have hsub : t.subtree ≠ "" := birth_supervised I.desc hG template t ht sup hsup
    have hpre := held_le_root_reachable I hL hG N w hR hcr template t ht hroot hsub sup hsup hlive
    have hplus := held_spawn_len I w w' template hF h
    omega

/-- An accepted `exec` does not grow the held keys of an empty subtree or of a
root. Enqueueing effects, abort, terminate, phase effects and a refused root
spawn are the arms; a child birth is a different template and adds none here. -/
theorem held_exec_keep (I : Impl) (hG : GraphOk I.desc) (w w' : World)
    (hI : Inv I w) (hB : BirthInv I.desc w) (hH : Hold I w) (hOne : OneCohort I.desc w.roster)
    (hcr : w.crashed = false) (id : InstId) (name : String) (hmem : id ∈ w.roster)
    (h : execHead I w id = some w')
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    ∀ key, key ∈ heldKeys I.desc w' name → key ∈ heldKeys I.desc w name := by
  intro key hkK
  have hF : ParentForest w := hI.forest
  have hP : Parented I.desc w := hB.parented
  have hSelf : NoSelfParent w := hB.noSelf
  have hKids : DeadChildless w := hI.seal.childless
  unfold execHead at h
  by_cases hnot : (w.st id).life ≠ .alive
  · simp [hnot] at h
  · have hlive : (w.st id).life = .alive := Classical.byContradiction fun hne => hnot hne
    have hbit : ((w.st id).life == .alive) = true := by simpa [beq_iff_eq] using hlive
    simp [hnot] at h
    cases hph : (w.st id).phase with
    | run k =>
      simp [hph] at h
      cases h
      cases hk : k.rest with
      | nil =>
        exact held_exec_phase I w id k name (by simp [hk]) key hkK
      | cons e es =>
        cases e with
        | send dst label hint =>
          exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k (.send dst label hint)
            es name hlive hmem hk (by simp [effectEnqueues]) hkind key hkK
        | trySend dst label hint onFull onGone =>
          exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k
            (.trySend dst label hint onFull onGone) es name hlive hmem hk
            (by simp [effectEnqueues]) hkind key hkK
        | call dst label hint onNotAdmitted onTimedOut =>
          exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k
            (.call dst label hint onNotAdmitted onTimedOut) es name hlive hmem hk
            (by simp [effectEnqueues]) hkind key hkK
        | selfSchedule label =>
          exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k (.selfSchedule label)
            es name hlive hmem hk (by simp [effectEnqueues]) hkind key hkK
        | cell dst label value =>
          exact held_exec_enqueue I hG w hF hP hSelf hH hOne hKids hcr id k (.cell dst label value)
            es name hlive hmem hk (by simp [effectEnqueues]) hkind key hkK
        | reply =>
          exact held_exec_reply I w id k es name hk key hkK
        | internal =>
          exact held_exec_phase I w id k name (by simp [hk]) key hkK
        | peer n =>
          exact held_exec_phase I w id k name (by simp [hk]) key hkK
        | abort =>
          exact held_abort_run I hG w hI hP hSelf hH hOne hcr id (w.st id) k es name hk hkind key hkK
        | terminate =>
          exact held_terminate_run I hG w hI hP hSelf hH hOne hcr id (w.st id) k name hmem
            ⟨es, hk⟩ hkind key hkK
        | spawn child =>
          by_cases hsame : child = name
          · have hkN : k.rest = .spawn name :: es := by simpa [hsame] using hk
            cases hs : spawnChild I w id name with
            | none =>
              simp [execRun, hbit, hkN, hs] at hkK
              exact held_crash I.desc w name key hkK
            | some w1 =>
              cases htc : templateOf I.desc name with
              | none => simp [spawnChild, htc] at hs
              | some t =>
                have hrootT : rootOf I.desc t = true := by
                  cases hkind with
                  | inl hempty =>
                    have hemptyT : t.subtree = "" := by
                      simp [templateSubtree, htc] at hempty
                      exact hempty
                    exact empty_is_root I.desc hG name t htc hemptyT
                  | inr hr =>
                    obtain ⟨t', ht', hroot', _⟩ := hr
                    have hteq : t' = t := by injection ht'.symm.trans htc
                    simpa [hteq] using hroot'
                have hw := spawn_root_same I w w1 hH id name hmem hs t htc hrootT
                simp [execRun, hbit, hkN, hs, hw] at hkK
                have hp := proceed_fields (w.st id) (afterHead k)
                exact held_commit I.desc w id (proceed (w.st id) (afterHead k)) name
                  hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1 hp.2.1 hp.1 key hkK
          · exact held_spawn_run I w id (w.st id) k es child name hF hk hsame key hkK
    | idle => simp [hph] at h
    | parked _ _ _ => simp [hph] at h
    | awaitReply _ _ => simp [hph] at h
    | awaitEffect _ => simp [hph] at h
    | awaitPeer _ => simp [hph] at h
    | crashed => simp [hph] at h

/-- A reachable world holds at most `N` keys of an empty subtree or of a root.
A non-birth step adds none. Spawning this root is allowed only while its
outstanding count is below `N`, and spawning anything else does not touch it. -/
theorem held_le_N (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (name : String)
    (hkind : templateSubtree I.desc name = "" ∨
      ∃ t, templateOf I.desc name = some t ∧ rootOf I.desc t = true ∧ t.subtree ≠ "") :
    (heldKeys I.desc w name).length ≤ N := by
  induction hR with
  | init =>
    rw [held_init]
    simp
  | step w w' a hprev ha ih =>
    have hcr : w.crashed = false := (apply_step I a w w' ha).1
    have hstep := (apply_step I a w w' ha).2
    have hI := inv_reachable I N w hL hprev
    have hB := lane_birth I hL hG N w hprev
    have hH := hold_reach I N w hG hprev
    have hOne := oneCohort_reachable I hG N w hprev
    cases a with
    | recvBulk s =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name (held_receive I w w' s name hstep)) ih
    | recvPrio s =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name (held_prio I w w' s name hstep)) ih
    | finish s =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name (held_finish I w w' s name hstep)) ih
    | callTimeout s =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name (held_timeout I w w' s name hstep)) ih
    | stutter =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name (held_stutter I w w' name hstep)) ih
    | ingress dst label =>
      exact Nat.le_trans (held_len_of_sub I.desc w w' name
        (held_ingress_reachable I hL hG N w w' hprev dst label name ha hkind)) ih
    | exec s =>
      simp only [stepWorld] at hstep
      exact Nat.le_trans (held_len_of_sub I.desc w w' name
        (held_exec_keep I hG w w' hI hB hH hOne hcr s name
          (hI.1.rostered s (by
            unfold execHead at hstep
            by_cases hnot : (w.st s).life ≠ .alive
            · simp [hnot] at hstep
            · exact Classical.byContradiction fun hne => hnot hne))
          hstep hkind)) ih
    | spawn template =>
      simp only [stepWorld] at hstep
      by_cases hsame : template = name
      · rw [hsame] at hstep
        have hbound := held_spawn_bound I hL hG N w w' hprev hcr name hstep
        simpa [reach_N I N w hprev] using hbound
      · exact Nat.le_trans (held_len_of_sub I.desc w w' name
          (held_spawn_other I w w' template name hI.forest hsame hstep)) ih

/-- A per-peer child's held keys are among its parent's, so a parent inside
the population bound keeps the child inside it. Climb to the subtree root,
which `held_le_N` bounds, one supervisor at a time. -/
theorem held_of_parent (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hcr : w.crashed = false)
    (child supName : String) (t ts : Template) (ht : templateOf I.desc child = some t)
    (hts : templateOf I.desc supName = some ts) (hsup : t.supervisor = some supName)
    (hmul : ts.multiplicity = .perPeer)
    (hparent : (heldKeys I.desc w supName).length ≤ N) :
    (heldKeys I.desc w child).length ≤ N := by
  have hI := inv_reachable I N w hL hR
  have hB := lane_birth I hL hG N w hR
  exact Nat.le_trans (nodup_sub_len _ _ (heldKeys_nodup I.desc w child)
    (fun k hk => held_in_parent I hG w hcr hB.parented hI.forest (hold_reach I N w hG hR)
      hI.seal.childless child supName t ts ht hts hsup hmul k hk)) hparent


/-! Held keys of every per-peer template sit under one population root.
`held_le_N` bounds an empty subtree and a `rootOf` template. A child climbs
to that root along `supStep`: `held_in_parent` keeps each held key, so the
child's list is no longer than the root's. -/

/-- The next per-peer supervisor. An empty subtree and a `rootOf` template
are population roots, and the step stops there. -/
def supStep (D : Description) (name : String) : Option String :=
  match templateOf D name with
  | none => none
  | some t =>
    if decide (t.subtree = "") || rootOf D t then none else t.supervisor

/-- `n` supervisor steps from `name`. `none` once a step has already stopped. -/
def nthSup (D : Description) (name : String) : Nat → Option String
  | 0 => some name
  | n + 1 => (nthSup D name n).bind (supStep D)

theorem nthSup_shift (D : Description) (name sup : String)
    (h : supStep D name = some sup) : ∀ n, nthSup D name (n + 1) = nthSup D sup n := by
  intro n
  induction n with
  | zero =>
    change supStep D name = some sup
    exact h
  | succ n ih =>
    change (nthSup D name (n + 1)).bind (supStep D) =
      (nthSup D sup n).bind (supStep D)
    rw [ih]

/-- A real step names a per-peer supervisor of a nonempty, non-root template. -/
theorem supStep_child (D : Description) (hG : GraphOk D) (name sup : String)
    (h : supStep D name = some sup) :
    ∃ t ts, templateOf D name = some t ∧ templateOf D sup = some ts ∧
      t.supervisor = some sup ∧ ts.multiplicity = .perPeer ∧ t.subtree ≠ "" ∧
      rootOf D t = false ∧ ts.subtree = t.subtree := by
  unfold supStep at h
  cases ht : templateOf D name with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    have hcond : (decide (t.subtree = "") || rootOf D t) = false := by
      by_cases hbit : (decide (t.subtree = "") || rootOf D t) = true
      · simp [hbit] at h
      · cases hb : decide (t.subtree = "") || rootOf D t
        · rfl
        · exact absurd hb hbit
    simp only [hcond, ite_false] at h
    have hempty : t.subtree ≠ "" := by
      intro he
      have hd : decide (t.subtree = "") = true := decide_eq_true he
      simp [hd] at hcond
    have hrootF : rootOf D t = false := by
      cases hb : rootOf D t with
      | false => rfl
      | true => simp [hb] at hcond
    obtain ⟨supName, ts, hsup, hts, hper, hsame, _⟩ :=
      member_sup D hG name t ht hempty hrootF
    have hnames : supName = sup := by
      injection hsup.symm.trans h
    refine ⟨t, ts, rfl, ?_, ?_, hper, hempty, hrootF, hsame⟩
    · simpa [hnames] using hts
    · simpa [hnames] using hsup

/-- Stopping is the population root `held_le_N` takes: an empty subtree, or
`rootOf` on a nonempty one. -/
theorem supStep_stop (D : Description) (hG : GraphOk D) (name : String) (t : Template)
    (ht : templateOf D name = some t) (h : supStep D name = none) :
    t.subtree = "" ∨ rootOf D t = true ∧ t.subtree ≠ "" := by
  unfold supStep at h
  simp only [ht] at h
  by_cases hempty : t.subtree = ""
  · exact Or.inl hempty
  · by_cases hroot : rootOf D t = true
    · exact Or.inr ⟨hroot, hempty⟩
    · have hrootF : rootOf D t = false := by
        cases hb : rootOf D t with
        | false => rfl
        | true => exact absurd hb hroot
      have hd : decide (t.subtree = "") = false := decide_eq_false hempty
      simp only [hd, hrootF, Bool.false_or, ite_false] at h
      obtain ⟨_, _, hsup, _⟩ := member_sup D hG name t ht hempty hrootF
      rw [hsup] at h
      cases h

/-- No roster peer carries a name the description does not declare, so that
name holds no key. -/
theorem held_absent (I : Impl) (w : World) (hH : Hold I w) (name : String)
    (ht : templateOf I.desc name = none) : heldKeys I.desc w name = [] := by
  cases hkeys : heldKeys I.desc w name with
  | nil => rfl
  | cons k _ =>
    have hk : k ∈ heldKeys I.desc w name := by simp [hkeys]
    obtain ⟨who, hid, hbit, _⟩ := (heldKeys_mem I.desc w name k).mp hk
    cases hwho : who with
    | core _ =>
      rw [hwho] at hbit
      simp [heldBit] at hbit
    | peer n _ _ =>
      rw [hwho] at hbit
      simp only [heldBit, Bool.and_eq_true] at hbit
      have hn : n = name := by simpa [beq_iff_eq] using hbit.1
      obtain ⟨_, ht', _⟩ := hH.role who hid
      rw [hwho] at ht'
      simp [tname, hn, ht] at ht'

/-- A held key stays held at every supervisor along `nthSup`. Each step is
`held_in_parent`. -/
theorem held_along (I : Impl) (hG : GraphOk I.desc) (w : World) (hcr : w.crashed = false)
    (hP : Parented I.desc w) (hF : ParentForest w) (hH : Hold I w) (hKids : DeadChildless w)
    (name : String) (n : Nat) (s : String) (hs : nthSup I.desc name n = some s) (k : Nat)
    (hk : k ∈ heldKeys I.desc w name) : k ∈ heldKeys I.desc w s := by
  induction n generalizing s with
  | zero =>
    simp [nthSup] at hs
    simpa [hs] using hk
  | succ n ih =>
    simp only [nthSup] at hs
    cases hmid : nthSup I.desc name n with
    | none => simp [hmid, Option.bind] at hs
    | some mid =>
      simp [hmid, Option.bind] at hs
      obtain ⟨t, ts, ht, hts, hsup, hmul, _, _, _⟩ :=
        supStep_child I.desc hG mid s hs
      exact held_in_parent I hG w hcr hP hF hH hKids mid s t ts ht hts hsup hmul k
        (ih mid hmid)

/-- The recorded parent chain of a roster actor reaches a population root.
The step is well-founded, so a supervisor cycle is not a populated chain. -/
theorem chain_hits (I : Impl) (hG : GraphOk I.desc) (w : World)
    (hF : ParentForest w) (hP : Parented I.desc w) (hSelf : NoSelfParent w) (hH : Hold I w)
    (id : InstId) (hid : id ∈ w.roster) :
    ∃ n root t, nthSup I.desc (tname id) n = some root ∧
      templateOf I.desc root = some t ∧ supStep I.desc root = none ∧
      (t.subtree = "" ∨ rootOf I.desc t = true ∧ t.subtree ≠ "") := by
  let C : InstId → Prop := fun id =>
    id ∈ w.roster →
      ∃ n root t, nthSup I.desc (tname id) n = some root ∧
        templateOf I.desc root = some t ∧ supStep I.desc root = none ∧
        (t.subtree = "" ∨ rootOf I.desc t = true ∧ t.subtree ≠ "")
  have hstep : ∀ id, (∀ parent, ParentEdge w id parent → C parent) → C id := by
    intro id ih hid
    obtain ⟨tRole, htRole, hmulRole⟩ := hH.role id hid
    have htRole' : templateOf I.desc (tname id) = some tRole := by simpa [tname] using htRole
    by_cases hstop : supStep I.desc (tname id) = none
    · exact ⟨0, tname id, tRole, by simp [nthSup], htRole', hstop,
        supStep_stop I.desc hG (tname id) tRole htRole' hstop⟩
    · have hsome : ∃ sup, supStep I.desc (tname id) = some sup := by
        cases hsb : supStep I.desc (tname id) with
        | none => exact absurd hsb hstop
        | some sup => exact ⟨sup, rfl⟩
      obtain ⟨sup, hstepS⟩ := hsome
      obtain ⟨t0, ts, ht0, hts, hsup, hper, hsub, _, _⟩ :=
        supStep_child I.desc hG (tname id) sup hstepS
      have hsame : t0 = tRole := by
        injection ht0.symm.trans htRole'
      rw [hsame] at hsub hsup
      have hchildPer : tRole.multiplicity = .perPeer :=
        member_per I.desc hG (tname id) tRole htRole' hsub
      cases id with
      | core _ =>
        simp [tmb_role] at hmulRole
        cases hchildPer.symm.trans hmulRole
      | peer n key g =>
        have hmem : InstId.peer n key g ∈ w.roster := hid
        have htPeer : templateOf I.desc n = some tRole := by simpa [tname] using htRole'
        have hsupN : tRole.supervisor = some sup := hsup
        obtain ⟨gP, _, hpar⟩ :=
          peer_parent I w hF hP hH n key g tRole ts sup hmem htPeer hsupN hts hper
        have hhosted := hF.hosted _ _ hpar
        have hne : InstId.peer n key g ≠ InstId.peer sup key gP := by
          intro heq
          apply hSelf (InstId.peer n key g)
          rw [hpar, heq]
        have hparent := ih (InstId.peer sup key gP) ⟨hpar, hne⟩ hhosted
        obtain ⟨nSteps, root, tr, hnth, htr, hstopR, hkind⟩ := hparent
        refine ⟨nSteps + 1, root, tr, ?_, htr, hstopR, hkind⟩
        have hstepN : supStep I.desc n = some sup := by simpa [tname] using hstepS
        simp only [tname]
        rw [nthSup_shift I.desc n sup hstepN nSteps]
        simpa [tname] using hnth
  exact (hF.wf).fix hstep id hid

/-- Every template name holds at most `N` keys. A population root is
`held_le_N`. Any other per-peer name climbs to that root, and the held keys
are a sublist of the root's. -/
theorem held_le_sender (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat)
    (w : World) (hR : Reachable I N w) (hcr : w.crashed = false) (name : String) :
    (heldKeys I.desc w name).length ≤ N := by
  have hI := inv_reachable I N w hL hR
  have hB := lane_birth I hL hG N w hR
  have hH := hold_reach I N w hG hR
  cases ht : templateOf I.desc name with
  | none =>
    rw [held_absent I w hH name ht]
    exact Nat.zero_le _
  | some t =>
    by_cases hstop : supStep I.desc name = none
    · exact held_le_N I hL hG N w hR name (by
        cases supStep_stop I.desc hG name t ht hstop with
        | inl hempty => exact Or.inl (by simp [templateSubtree, ht, hempty])
        | inr hr => exact Or.inr ⟨t, ht, hr.1, hr.2⟩)
    · by_cases hzero : (heldKeys I.desc w name).length = 0
      · rw [hzero]
        exact Nat.zero_le _
      · cases hkeys : heldKeys I.desc w name with
        | nil => simp [hkeys] at hzero
        | cons k _ =>
          have hk : k ∈ heldKeys I.desc w name := by simp [hkeys]
          obtain ⟨who, hid, hbit, _⟩ := (heldKeys_mem I.desc w name k).mp hk
          cases hwho : who with
          | core _ =>
            rw [hwho] at hbit
            simp [heldBit] at hbit
          | peer n _ _ =>
            rw [hwho] at hbit
            simp only [heldBit, Bool.and_eq_true] at hbit
            have hn : n = name := by simpa [beq_iff_eq] using hbit.1
            obtain ⟨nSteps, root, tr, hnth, htr, _, hkind⟩ :=
              chain_hits I hG w hI.forest hB.parented hB.noSelf hH who hid
            have hnth' : nthSup I.desc name nSteps = some root := by
              simpa [tname, hwho, hn] using hnth
            have hsub : ∀ key, key ∈ heldKeys I.desc w name → key ∈ heldKeys I.desc w root :=
              fun key hkey => held_along I hG w hcr hB.parented hI.forest hH hI.seal.childless
                name nSteps root hnth' key hkey
            have hlen := nodup_sub_len _ _ (heldKeys_nodup I.desc w name) hsub
            have hrootKind : templateSubtree I.desc root = "" ∨
                ∃ t, templateOf I.desc root = some t ∧ rootOf I.desc t = true ∧
                  t.subtree ≠ "" := by
              cases hkind with
              | inl hempty => exact Or.inl (by simp [templateSubtree, htr, hempty])
              | inr hr => exact Or.inr ⟨tr, htr, hr.1, hr.2⟩
            have hle : (heldKeys I.desc w name).length ≤ N :=
              Nat.le_trans hlen (held_le_N I hL hG N w hR root hrootKind)
            simpa [hkeys] using hle

/-- A live host is not sealed with a sender that is no longer alive. A dead
parent has no live child, so the host cannot sit under that sender. -/
theorem unsealed_of_dead (w : World) (hKids : DeadChildless w) (hcr : w.crashed = false)
    (sender host : InstId) (hlive : (w.st host).life = .alive)
    (hdead : (w.st sender).life ≠ .alive) : sealedTogether w sender host = false := by
  have hne : sender ≠ host := by
    intro heq
    exact hdead (heq ▸ hlive)
  have hbb : (sender == host) = false := by simpa [beq_iff_eq] using hne
  have hd : descends w.roster.length w sender host = false := by
    cases hb : descends w.roster.length w sender host with
    | false => rfl
    | true =>
      exact absurd (ancestor_alive w hKids hcr (strict_of_descends w _ sender host hb) hlive) hdead
  simp [sealedTogether, hbb, hd]

/-- Mail from a peer, sitting in a live host, holds that peer's key. The
sender is alive, or the host survived it and `slotMailHeld` still sees the
message. -/
theorem box_key_held (I : Impl) (w : World) (hO : OccInv I w) (hKids : DeadChildless w)
    (hcr : w.crashed = false) (host : InstId) (hlive : (w.st host).life = .alive)
    (m : Msg) (hm : m ∈ (w.st host).box) (name : String) (k g : Nat)
    (hs : m.sender = InstId.peer name k g) : k ∈ heldKeys I.desc w name := by
  have hsend := hO.sentFrom host m hm
  have hmemS : InstId.peer name k g ∈ w.roster := by simpa [hs] using hsend
  have hhost := hO.aliveIn host hlive
  by_cases hl : (w.st (InstId.peer name k g)).life = .alive
  · have hheld : heldAt I.desc w name k = true := by
      unfold heldAt
      refine (_root_.List.any_eq_true).mpr ⟨InstId.peer name k g, hmemS, ?_⟩
      simp [hl]
    exact (heldKeys_mem I.desc w name k).mpr
      ⟨InstId.peer name k g, hmemS, by simp [heldBit, hheld], by simp [bitKey]⟩
  · have hunseal := unsealed_of_dead w hKids hcr (InstId.peer name k g) host hlive hl
    have hsurv : survivesSender w (InstId.peer name k g) host = true := by
      have hlB : ((w.st host).life == .alive) = true := by simpa [beq_iff_eq] using hlive
      simp [survivesSender, hlB, hunseal]
    have hslot : slotMailHeld I.desc w name k = true := by
      by_cases hempty : templateSubtree I.desc name = ""
      · have hb : (templateSubtree I.desc name == "") = true := by
          simpa [beq_iff_eq] using hempty
        simp only [slotMailHeld, hb, ite_true, slotCoreMail]
        refine (_root_.List.any_eq_true).mpr ⟨host, hhost, ?_⟩
        simp only [actorHoldsSlotMail, Bool.or_eq_true]
        refine Or.inl (Or.inl ?_)
        refine (_root_.List.any_eq_true).mpr ⟨m, hm, ?_⟩
        simp [hs, fromSlot, hsurv]
      · have hb : (templateSubtree I.desc name == "") = false := by
          simpa [beq_iff_eq] using hempty
        cases ht : templateOf I.desc name with
        | none => simp [templateSubtree, ht] at hempty
        | some t =>
          have htree : t.subtree ≠ "" := by
            simp [templateSubtree, ht] at hempty
            exact hempty
          have hmember := member_of_key I.desc (InstId.peer name k g) t k
            (by simpa [tname] using ht) htree (by simp [memberKey])
          have hsubEq : templateSubtree I.desc name = t.subtree := by simp [templateSubtree, ht]
          simp only [slotMailHeld, hb, ite_false, subtreeCoreMail]
          refine (_root_.List.any_eq_true).mpr ⟨host, hhost, ?_⟩
          simp only [actorHoldsSubtreeMail, Bool.or_eq_true]
          refine Or.inl (Or.inl ?_)
          refine (_root_.List.any_eq_true).mpr ⟨m, hm, ?_⟩
          simp [fromSubtree, hs, hsurv, hsubEq, hmember]
    have hheld : heldAt I.desc w name k = true := by
      unfold heldAt
      refine (_root_.List.any_eq_true).mpr ⟨InstId.peer name k g, hmemS, ?_⟩
      simp [hslot]
    exact (heldKeys_mem I.desc w name k).mpr
      ⟨InstId.peer name k g, hmemS, by simp [heldBit, hheld], by simp [bitKey]⟩

/-- The live generation of a key holds that key, before it has sent. -/
theorem alive_held (D : Description) (w : World) (name : String) (k g : Nat)
    (hmem : InstId.peer name k g ∈ w.roster)
    (hl : (w.st (InstId.peer name k g)).life = .alive) : k ∈ heldKeys D w name := by
  have hheld : heldAt D w name k = true := by
    unfold heldAt
    refine (_root_.List.any_eq_true).mpr ⟨InstId.peer name k g, hmem, ?_⟩
    simp [hl]
  exact (heldKeys_mem D w name k).mpr
    ⟨InstId.peer name k g, hmem, by simp [heldBit, hheld], by simp [bitKey]⟩

/-- Messages in one host's box from one key. -/
def keyLen (name : String) (k : Nat) (ms : List Msg) : Nat :=
  (ms.filter (keyPred name k)).length

theorem keyLen_yes (name : String) (k : Nat) (m : Msg) (ms : List Msg)
    (h : keyPred name k m = true) : keyLen name k (m :: ms) = keyLen name k ms + 1 := by
  simp [keyLen, List.filter, h, Nat.add_comm]

theorem keyLen_no (name : String) (k : Nat) (m : Msg) (ms : List Msg)
    (h : keyPred name k m = false) : keyLen name k (m :: ms) = keyLen name k ms := by
  simp [keyLen, List.filter, h]

theorem keyLen_le_queued (w : World) (hnd : w.roster.Nodup) (name : String) (k : Nat)
    (host : InstId) (hmem : host ∈ w.roster) :
    keyLen name k (w.st host).box ≤ queuedFromKey w name k (tname host) := by
  simpa [keyLen] using share_ge_box w name k (tname host) host hmem hnd rfl

/-- One key, summed across the keys a template still holds. -/
def sumKey (name : String) : List Nat → List Msg → Nat
  | [], _ => 0
  | k :: ks, ms => keyLen name k ms + sumKey name ks ms

theorem sumKey_le_mul (name : String) (keys : List Nat) (ms : List Msg) (B : Nat)
    (hle : ∀ k ∈ keys, keyLen name k ms ≤ B) : sumKey name keys ms ≤ keys.length * B := by
  induction keys with
  | nil => simp [sumKey]
  | cons k ks ih =>
    have hhead := hle k (List.Mem.head _)
    have htail := ih (fun k' hk' => hle k' (List.Mem.tail _ hk'))
    simp only [sumKey, List.length_cons]
    have hmul : (ks.length + 1) * B = B + ks.length * B := by
      rw [Nat.succ_mul, Nat.add_comm]
    omega

theorem keyPred_from (name : String) (k : Nat) (m : Msg) (h : keyPred name k m = true) :
    fromName name m = true := by
  cases hsend : m.sender with
  | core _ => simp [keyPred, hsend] at h
  | peer n _ _ =>
    simp [keyPred, fromName, hsend] at h ⊢
    exact h.1

theorem keyPred_only (name : String) (k k' : Nat) (m : Msg)
    (hk : keyPred name k m = true) (hk' : keyPred name k' m = true) : k = k' := by
  cases hsend : m.sender with
  | core _ => simp [keyPred, hsend] at hk
  | peer _ key _ =>
    simp [keyPred, hsend, Bool.and_eq_true, beq_iff_eq] at hk hk'
    exact hk.2.symm.trans hk'.2

theorem sumKey_preds_miss (name : String) (m : Msg) (ms : List Msg) :
    ∀ keys, (∀ k ∈ keys, keyPred name k m = false) →
      sumKey name keys (m :: ms) = sumKey name keys ms := by
  intro keys
  induction keys with
  | nil =>
    intro _
    simp [sumKey]
  | cons k ks ih =>
    intro h
    simp only [sumKey]
    rw [keyLen_no name k m ms (h k (List.Mem.head _))]
    rw [ih (fun k' hk' => h k' (List.Mem.tail _ hk'))]

theorem sumKey_hit (name : String) (keys : List Nat) (k : Nat) (m : Msg) (ms : List Msg)
    (hmem : k ∈ keys) (hnd : keys.Nodup) (hyes : keyPred name k m = true)
    (hno : ∀ k' ∈ keys, k' ≠ k → keyPred name k' m = false) :
    sumKey name keys (m :: ms) = sumKey name keys ms + 1 := by
  induction keys with
  | nil => cases hmem
  | cons head tail ih =>
    have hcons := (List.nodup_cons).mp hnd
    simp only [sumKey]
    rcases List.mem_cons.mp hmem with rfl | htail
    · rw [keyLen_yes name k m ms hyes]
      rw [sumKey_preds_miss name m ms tail (fun k' hk' =>
        hno k' (List.Mem.tail _ hk') (fun hsame => hcons.1 (by simpa [hsame] using hk')))]
      omega
    · have hhead : keyPred name head m = false :=
        hno head (List.Mem.head _) (fun hsame => hcons.1 (by simpa [hsame] using htail))
      rw [keyLen_no name head m ms hhead]
      rw [ih htail hcons.2 (fun k' hk' hne => hno k' (List.Mem.tail _ hk') hne)]
      omega

theorem sumKey_slack (name : String) (keys : List Nat) (ms : List Msg) (s : Nat) (B : Nat)
    (hs : s ∈ keys) (hnd : keys.Nodup) (hle : ∀ k ∈ keys, keyLen name k ms ≤ B)
    (hextra : keyLen name s ms + 1 ≤ B) : sumKey name keys ms + 1 ≤ keys.length * B := by
  induction keys with
  | nil => cases hs
  | cons k ks ih =>
    have hcons := (List.nodup_cons).mp hnd
    simp only [sumKey, List.length_cons]
    rcases List.mem_cons.mp hs with rfl | htail
    · have htailLe := sumKey_le_mul name ks ms B
        (fun k' hk' => hle k' (List.Mem.tail _ hk'))
      have hmul : (ks.length + 1) * B = B + ks.length * B := by
        rw [Nat.succ_mul, Nat.add_comm]
      omega
    · have ih' := ih htail hcons.2 (fun k' hk' => hle k' (List.Mem.tail _ hk'))
      have hhead := hle k (List.Mem.head _)
      have hmul : (ks.length + 1) * B = B + ks.length * B := by
        rw [Nat.succ_mul, Nat.add_comm]
      omega

theorem nameLen_le_sumKey (name : String) (keys : List Nat) (ms : List Msg) (hnd : keys.Nodup)
    (hpick : ∀ m ∈ ms, fromName name m = true → ∃ k, k ∈ keys ∧ keyPred name k m = true) :
    nameLen name ms ≤ sumKey name keys ms := by
  induction ms with
  | nil => simp [nameLen]
  | cons m ms ih =>
    by_cases hyes : fromName name m = true
    · obtain ⟨k, hk, hpred⟩ := hpick m (List.Mem.head _) hyes
      have honly : ∀ k' ∈ keys, k' ≠ k → keyPred name k' m = false := by
        intro k' hk' hne
        cases hp : keyPred name k' m with
        | false => rfl
        | true => exact absurd (keyPred_only name k' k m hp hpred) hne
      rw [nameLen_yes name m ms hyes, sumKey_hit name keys k m ms hk hnd hpred honly]
      exact Nat.add_le_add_right (ih (fun m' hm' => hpick m' (List.Mem.tail _ hm'))) 1
    · have hno : fromName name m = false := by
        cases hb : fromName name m with
        | false => rfl
        | true => exact absurd hb hyes
      have hmiss : sumKey name keys (m :: ms) = sumKey name keys ms := by
        refine sumKey_preds_miss name m ms keys ?_
        intro k hk
        cases hp : keyPred name k m with
        | false => rfl
        | true =>
          exact False.elim ((Bool.eq_false_iff.mp hno) (keyPred_from name k m hp))
      rw [nameLen_no name m ms hno, hmiss]
      exact ih (fun m' hm' => hpick m' (List.Mem.tail _ hm'))

/-- Messages of one peer name in a live box are at most one budget per held key. -/
theorem name_le_held (I : Impl) (w : World) (hO : OccInv I w) (hKids : DeadChildless w)
    (hcr : w.crashed = false) (host : InstId) (hlive : (w.st host).life = .alive)
    (name : String) :
    nameLen name (w.st host).box ≤
      (heldKeys I.desc w name).length * budget I.desc name (tname host) := by
  have hmemH := hO.aliveIn host hlive
  have hpick : ∀ m ∈ (w.st host).box, fromName name m = true →
      ∃ k, k ∈ heldKeys I.desc w name ∧ keyPred name k m = true := by
    intro m hm hyes
    cases hsend : m.sender with
    | core _ => simp [fromName, hsend] at hyes
    | peer n k g =>
      simp only [fromName, hsend, beq_iff_eq] at hyes
      have hsend' : m.sender = InstId.peer name k g := by simpa [hyes] using hsend
      have hpred : keyPred name k m = true := by simp [keyPred, hsend']
      exact ⟨k, box_key_held I w hO hKids hcr host hlive m hm name k g hsend', hpred⟩
  exact Nat.le_trans
    (nameLen_le_sumKey name (heldKeys I.desc w name) (w.st host).box
      (heldKeys_nodup I.desc w name) hpick)
    (sumKey_le_mul name (heldKeys I.desc w name) (w.st host).box _
      (fun k _ => Nat.le_trans (keyLen_le_queued w hO.nodup name k host hmemH)
        (key_queued_le I w hO name k (tname host))))

/-- Workaround `lane_succ_le`: `queued_succ_le` is stated in `Inv2`, which
imports this file. One token still in hand leaves room for one more queued
message inside the same budget. -/
theorem lane_succ_le (budget queued : Nat) (tokens : Int)
    (hsum : tokens + (queued : Int) = (budget : Int)) (htok : (1 : Int) ≤ tokens) :
    queued + 1 ≤ budget := by
  omega

/-- Workaround `lane_gap`: `peer_send_gap` is stated in `Inv2`. The live
generation's tokens plus mail already queued are the budget, and `tokenHold`
is still at least one. -/
theorem lane_gap (I : Impl) (w : World) (hO : OccInv I w) (name : String) (key : Nat)
    (sender : InstId) (dst : String) (hlive : findLive w name key = some sender)
    (hlife : (w.st sender).life = .alive)
    (hhold : 1 ≤ tokenHold I.desc name dst (w.st sender)) :
    queuedFromKey w name key dst + 1 ≤ budget I.desc name dst := by
  have htn := (findLive_spec w name key sender hlive).1
  have hS := hO.slack sender dst hlife
  have hcast : ((1 : Nat) : Int) ≤ (tokenHold I.desc name dst (w.st sender) : Int) :=
    Int.ofNat_le.mpr hhold
  rw [htn] at hS
  exact lane_succ_le _ _ _ (hO.balance.1.1 name key sender dst hlive) (Int.le_trans hcast hS)

/-- One more message from the live generation of `name` at `k` still fits in
the keys that generation's template holds. -/
theorem peer_name_succ (I : Impl) (w : World) (hO : OccInv I w) (hKids : DeadChildless w)
    (hcr : w.crashed = false) (host : InstId) (hlive : (w.st host).life = .alive)
    (name : String) (k g : Nat) (sender : InstId) (hsender : sender = InstId.peer name k g)
    (hmemS : sender ∈ w.roster) (hlife : (w.st sender).life = .alive)
    (hhold : 1 ≤ tokenHold I.desc name (tname host) (w.st sender)) :
    nameLen name (w.st host).box + 1 ≤
      (heldKeys I.desc w name).length * budget I.desc name (tname host) := by
  have hmemH := hO.aliveIn host hlive
  have hmemP : InstId.peer name k g ∈ w.roster := by simpa [hsender] using hmemS
  have hliveP : (w.st (InstId.peer name k g)).life = .alive := by simpa [hsender] using hlife
  have hfind := findLive_of_alive w hO.indexed name k g hmemP hliveP
  have hfindS : findLive w name k = some sender := by simpa [hsender] using hfind
  have hgap := lane_gap I w hO name k sender (tname host) hfindS hlife hhold
  have hextra : keyLen name k (w.st host).box + 1 ≤ budget I.desc name (tname host) :=
    Nat.le_trans (Nat.add_le_add_right (keyLen_le_queued w hO.nodup name k host hmemH) 1) hgap
  have hkey := alive_held I.desc w name k g hmemP hliveP
  have hkeys : ∀ key ∈ heldKeys I.desc w name,
      keyLen name key (w.st host).box ≤ budget I.desc name (tname host) := by
    intro key _
    exact Nat.le_trans (keyLen_le_queued w hO.nodup name key host hmemH)
      (key_queued_le I w hO name key (tname host))
  have hsum := sumKey_slack name (heldKeys I.desc w name) (w.st host).box k _
    hkey (heldKeys_nodup I.desc w name) hkeys hextra
  have hpick : ∀ m ∈ (w.st host).box, fromName name m = true →
      ∃ key, key ∈ heldKeys I.desc w name ∧ keyPred name key m = true := by
    intro m hm hyes
    cases hsend : m.sender with
    | core _ => simp [fromName, hsend] at hyes
    | peer n key gen =>
      simp only [fromName, hsend, beq_iff_eq] at hyes
      have hsend' : m.sender = InstId.peer name key gen := by simpa [hyes] using hsend
      exact ⟨key, box_key_held I w hO hKids hcr host hlive m hm name key gen hsend',
        by simp [keyPred, hsend']⟩
  have hname := nameLen_le_sumKey name (heldKeys I.desc w name) (w.st host).box
    (heldKeys_nodup I.desc w name) hpick
  exact Nat.le_trans (Nat.add_le_add_right hname 1) hsum

/-- Messages from one core. -/
def coreLen (name : String) (ms : List Msg) : Nat :=
  (ms.filter (fun m => m.sender == InstId.core name)).length

theorem coreLen_yes (name : String) (m : Msg) (ms : List Msg)
    (h : m.sender = InstId.core name) : coreLen name (m :: ms) = coreLen name ms + 1 := by
  have hb : (m.sender == InstId.core name) = true := by simpa [beq_iff_eq] using h
  simp [coreLen, List.filter, hb, Nat.add_comm]

theorem coreLen_no (name : String) (m : Msg) (ms : List Msg) (h : m.sender ≠ InstId.core name) :
    coreLen name (m :: ms) = coreLen name ms := by
  have hb : (m.sender == InstId.core name) = false := by simpa [beq_iff_eq] using h
  simp [coreLen, List.filter, hb]

theorem coreLen_count (name : String) : ∀ ms, coreLen name ms = countFrom (InstId.core name) ms := by
  intro ms
  induction ms with
  | nil => simp [coreLen, countFrom]
  | cons m ms ih =>
    by_cases hs : m.sender = InstId.core name
    · rw [coreLen_yes name m ms hs, ih]
      simp [countFrom, hs, Nat.add_comm]
    · rw [coreLen_no name m ms hs, ih]
      simp [countFrom, hs]

theorem coreLen_out (name : String) (ms : List Msg)
    (h : ∀ m ∈ ms, m.sender ≠ InstId.core name) : coreLen name ms = 0 := by
  induction ms with
  | nil => simp [coreLen]
  | cons m ms ih =>
    rw [coreLen_no name m ms (h m (List.Mem.head _))]
    exact ih (fun m' hm' => h m' (List.Mem.tail _ hm'))

theorem coreLen_le_owed_host (w : World) (host : InstId) (name dst : String)
    (hmem : host ∈ w.roster) (hnd : w.roster.Nodup) (hdst : tname host = dst) :
    coreLen name (w.st host).box ≤ owed w.st dst (InstId.core name) w.roster := by
  rw [coreLen_count]
  exact Nat.le_trans (Nat.le_add_right _ _)
    (owed_ge_here w.st dst (InstId.core name) host w.roster hnd hmem hdst)

/-- A core's mail on one host is inside its budget. An absent core has sent
nothing. A live core's tokens are the rest of the same account. -/
theorem core_le_budget (I : Impl) (w : World) (hO : OccInv I w) (hcr : w.crashed = false)
    (name dst : String) (host : InstId) (hmemH : host ∈ w.roster) (hdst : tname host = dst) :
    coreLen name (w.st host).box ≤ budget I.desc name dst := by
  by_cases hmem : InstId.core name ∈ w.roster
  · have hhere := coreLen_le_owed_host w host name dst hmemH hO.nodup hdst
    by_cases hl : (w.st (InstId.core name)).life = .alive
    · have hbal := hO.balance.1.2 name dst hl hmem
      have hS := hO.slack (InstId.core name) dst hl
      have h0 : (0 : Int) ≤ (w.st (InstId.core name)).tokens dst :=
        Int.le_trans (Int.natCast_nonneg _) hS
      have howed : (owed w.st dst (InstId.core name) w.roster : Int) ≤
          (budget I.desc name dst : Int) := by omega
      exact Nat.le_trans hhere (Int.ofNat_le.mp howed)
    · exact Nat.le_trans hhere
        (Int.ofNat_le.mp (hO.quiet hcr (InstId.core name) dst hmem hl))
  · have hnone : ∀ m ∈ (w.st host).box, m.sender ≠ InstId.core name := by
      intro m hm heq
      have hsend := hO.sentFrom host m hm
      rw [heq] at hsend
      exact hmem hsend
    rw [coreLen_out name (w.st host).box hnone]
    exact Nat.zero_le _

/-- One more message from a live core still fits in that core's budget. -/
theorem core_succ (I : Impl) (w : World) (hO : OccInv I w) (name dst : String)
    (host : InstId) (hmemH : host ∈ w.roster) (hdst : tname host = dst)
    (hl : (w.st (InstId.core name)).life = .alive) (hmem : InstId.core name ∈ w.roster)
    (hhold : 1 ≤ tokenHold I.desc name dst (w.st (InstId.core name))) :
    coreLen name (w.st host).box + 1 ≤ budget I.desc name dst := by
  have hhere := coreLen_le_owed_host w host name dst hmemH hO.nodup hdst
  have hbal := hO.balance.1.2 name dst hl hmem
  have hS := hO.slack (InstId.core name) dst hl
  have h1 : (1 : Int) ≤ (w.st (InstId.core name)).tokens dst :=
    Int.le_trans (Int.ofNat_le.mpr hhold) hS
  exact Nat.le_trans (Nat.add_le_add_right hhere 1)
    (lane_succ_le _ _ _ hbal h1)

/-- What `name` contributes to a box: peer messages when the template is
per-peer, core messages when it is one actor. -/
def srcLen (D : Description) (name : String) (ms : List Msg) : Nat :=
  match templateOf D name with
  | none => 0
  | some t =>
    if t.multiplicity == .perPeer then nameLen name ms else coreLen name ms

/-- `name` is the template that sent `m`, with the multiplicity that template
declares. -/
def hits (D : Description) (name : String) (m : Msg) : Bool :=
  match m.sender with
  | .peer n _ _ =>
    n == name &&
      match templateOf D name with
      | some t => t.multiplicity == .perPeer
      | none => false
  | .core n =>
    n == name &&
      match templateOf D name with
      | some t => !(t.multiplicity == .perPeer)
      | none => false

theorem hits_of_from (D : Description) (name : String) (t : Template) (m : Msg)
    (ht : templateOf D name = some t) (hmul : t.multiplicity = .perPeer)
    (hf : fromName name m = true) : hits D name m = true := by
  have hbeq : (t.multiplicity == .perPeer) = true := by
    rw [hmul]
    decide
  cases hsend : m.sender with
  | core _ => simp [fromName, hsend] at hf
  | peer n _ _ =>
    simp only [fromName, hsend, beq_iff_eq] at hf
    simp [hits, hsend, hf, ht, hbeq, beq_iff_eq]

theorem hits_of_core (D : Description) (name : String) (t : Template) (m : Msg)
    (ht : templateOf D name = some t) (hmul : t.multiplicity = .one)
    (hs : m.sender = InstId.core name) : hits D name m = true := by
  have hbeq : (t.multiplicity == .perPeer) = false := by
    rw [hmul]
    decide
  simp [hits, hs, ht, hbeq]

theorem srcLen_yes (D : Description) (name : String) (m : Msg) (ms : List Msg)
    (h : hits D name m = true) : srcLen D name (m :: ms) = srcLen D name ms + 1 := by
  cases hsend : m.sender with
  | peer n _ _ =>
    simp only [hits, hsend, Bool.and_eq_true] at h
    cases ht : templateOf D name with
    | none => simp [ht] at h
    | some t =>
      simp only [ht] at h
      have hfrom : fromName name m = true := by simp [fromName, hsend, h.1]
      simp [srcLen, ht, h.2, nameLen_yes name m ms hfrom]
  | core n =>
    simp only [hits, hsend, Bool.and_eq_true] at h
    cases ht : templateOf D name with
    | none => simp [ht] at h
    | some t =>
      simp only [ht] at h
      have hnot : (t.multiplicity == .perPeer) = false := by
        cases hb : t.multiplicity == .perPeer with
        | false => rfl
        | true => simp [hb] at h
      have hn : n = name := by simpa [beq_iff_eq] using h.1
      have hs : m.sender = InstId.core name := by simp [hsend, hn]
      simp [srcLen, ht, hnot, coreLen_yes name m ms hs]

theorem srcLen_no (D : Description) (name : String) (m : Msg) (ms : List Msg)
    (h : hits D name m = false) : srcLen D name (m :: ms) = srcLen D name ms := by
  cases ht : templateOf D name with
  | none => simp [srcLen, ht]
  | some t =>
    cases hm : t.multiplicity with
    | perPeer =>
      have hbeq : (t.multiplicity == .perPeer) = true := by
        rw [hm]
        decide
      have hfrom : fromName name m = false := by
        cases hf : fromName name m with
        | false => rfl
        | true =>
          simp [hits_of_from D name t m ht hm hf] at h
      simp [srcLen, ht, hbeq, nameLen_no name m ms hfrom]
    | one =>
      have hbeq : (t.multiplicity == .perPeer) = false := by
        rw [hm]
        decide
      have hs : m.sender ≠ InstId.core name := by
        intro heq
        simp [hits_of_core D name t m ht hm heq] at h
      simp [srcLen, ht, hbeq, coreLen_no name m ms hs]

/-- Sum of `srcLen` over the description's template names. -/
def sumSrc (D : Description) (ms : List Msg) : List String → Nat
  | [] => 0
  | name :: names => srcLen D name ms + sumSrc D ms names

theorem sumSrc_cons (D : Description) (ms : List Msg) (name : String) (names : List String) :
    sumSrc D ms (name :: names) = srcLen D name ms + sumSrc D ms names := rfl

theorem sumSrc_skip (D : Description) (m : Msg) (ms : List Msg) :
    ∀ names, (∀ name ∈ names, hits D name m = false) →
      sumSrc D (m :: ms) names = sumSrc D ms names := by
  intro names
  induction names with
  | nil =>
    intro _
    simp [sumSrc]
  | cons name names ih =>
    intro hno
    rw [sumSrc_cons, sumSrc_cons, srcLen_no D name m ms (hno name (List.Mem.head _))]
    rw [ih (fun name' hmem => hno name' (List.Mem.tail _ hmem))]

theorem sumSrc_step (D : Description) (names : List String) (name : String) (m : Msg)
    (ms : List Msg) (hmem : name ∈ names) (hnd : names.Nodup) (hyes : hits D name m = true)
    (hno : ∀ name' ∈ names, name' ≠ name → hits D name' m = false) :
    sumSrc D (m :: ms) names = sumSrc D ms names + 1 := by
  induction names with
  | nil => cases hmem
  | cons head tail ih =>
    have hcons := (List.nodup_cons).mp hnd
    rcases List.mem_cons.mp hmem with rfl | htail
    · rw [sumSrc_cons, sumSrc_cons, srcLen_yes D name m ms hyes]
      rw [sumSrc_skip D m ms tail (fun name' hmem' =>
        hno name' (List.Mem.tail _ hmem') (fun hsame => hcons.1 (by simpa [hsame] using hmem')))]
      omega
    · have hhead : hits D head m = false :=
        hno head (List.Mem.head _) (fun hsame => hcons.1 (by simpa [hsame] using htail))
      rw [sumSrc_cons, sumSrc_cons, srcLen_no D head m ms hhead]
      rw [ih htail hcons.2 (fun name' hmem' hne => hno name' (List.Mem.tail _ hmem') hne)]
      omega

theorem length_le_src (D : Description) (names : List String) (ms : List Msg) (hnd : names.Nodup)
    (hmem : ∀ m ∈ ms, ∃ name ∈ names, hits D name m = true)
    (hno : ∀ m ∈ ms, ∀ name' ∈ names, ∀ name ∈ names, hits D name m = true →
      name' ≠ name → hits D name' m = false) :
    ms.length ≤ sumSrc D ms names := by
  induction ms with
  | nil =>
    simp [sumSrc]
  | cons m ms ih =>
    obtain ⟨name, hname, hyes⟩ := hmem m (List.Mem.head _)
    have hstep := sumSrc_step D names name m ms hname hnd hyes
      (fun name' hmem' hne => hno m (List.Mem.head _) name' hmem' name hname hyes hne)
    have htail := ih (fun m' hm' => hmem m' (List.Mem.tail _ hm'))
      (fun m' hm' => hno m' (List.Mem.tail _ hm'))
    simp only [List.length_cons]
    rw [hstep]
    omega

theorem hits_only (D : Description) (m : Msg) (name name' : String)
    (h : hits D name m = true) (hne : name' ≠ name) : hits D name' m = false := by
  cases hsend : m.sender with
  | peer n _ _ =>
    simp only [hits, hsend, Bool.and_eq_true] at h
    have hn : n = name := by simpa [beq_iff_eq] using h.1
    have hne' : n ≠ name' := fun heq => hne (heq.symm.trans hn)
    have hbb : (n == name') = false := by simpa [beq_iff_eq] using hne'
    simp [hits, hsend, hbb]
  | core n =>
    simp only [hits, hsend, Bool.and_eq_true] at h
    have hn : n = name := by simpa [beq_iff_eq] using h.1
    have hne' : n ≠ name' := fun heq => hne (heq.symm.trans hn)
    have hbb : (n == name') = false := by simpa [beq_iff_eq] using hne'
    simp [hits, hsend, hbb]

theorem hits_shaped (D : Description) (id : InstId) (m : Msg) (hs : m.sender = id)
    (hshape : shapeOk D id) : hits D (tname id) m = true := by
  obtain ⟨t, ht, hmul⟩ := hshape
  cases hm : t.multiplicity with
  | perPeer =>
    have hbeq : (t.multiplicity == .perPeer) = true := by
      rw [hm]
      decide
    have hex : ∃ k g, id = InstId.peer t.name k g := by simpa [hm] using hmul
    obtain ⟨k, g, hid⟩ := hex
    subst hid
    simp only [tname] at ht ⊢
    simp [hits, hs, ht, hbeq]
  | one =>
    have hbeq : (t.multiplicity == .perPeer) = false := by
      rw [hm]
      decide
    have hid : id = InstId.core t.name := by simpa [hm] using hmul
    subst hid
    simp only [tname] at ht ⊢
    simp [hits, hs, ht, hbeq]

/-- The charge `nameCover` gives `name`: `N` budgets for a per-peer template
and one budget for a core. -/
def popBudget (D : Description) (dst name : String) (n : Nat) : Nat :=
  match templateOf D name with
  | none => 0
  | some t => popFactor n t * budget D name dst

theorem nameCover_cons (D : Description) (dst : String) (n : Nat) (name : String)
    (names : List String) :
    nameCover D dst n (name :: names) = popBudget D dst name n + nameCover D dst n names := by
  simp [nameCover, popBudget]

theorem sumSrc_le_cover (D : Description) (dst : String) (n : Nat) (ms : List Msg) :
    ∀ names, (∀ name ∈ names, srcLen D name ms ≤ popBudget D dst name n) →
      sumSrc D ms names ≤ nameCover D dst n names := by
  intro names
  induction names with
  | nil =>
    intro _
    simp [sumSrc, nameCover]
  | cons name names ih =>
    intro hle
    rw [sumSrc_cons, nameCover_cons]
    exact Nat.add_le_add (hle name (List.Mem.head _))
      (ih (fun name' hmem => hle name' (List.Mem.tail _ hmem)))

theorem sumSrc_cover_slack (D : Description) (dst : String) (n : Nat) (ms : List Msg)
    (names : List String) (s : String) (hs : s ∈ names) (hnd : names.Nodup)
    (hle : ∀ name ∈ names, srcLen D name ms ≤ popBudget D dst name n)
    (hextra : srcLen D s ms + 1 ≤ popBudget D dst s n) :
    sumSrc D ms names + 1 ≤ nameCover D dst n names := by
  induction names with
  | nil => cases hs
  | cons name names ih =>
    have hcons := (List.nodup_cons).mp hnd
    rw [sumSrc_cons, nameCover_cons]
    rcases List.mem_cons.mp hs with rfl | htail
    · have htailLe := sumSrc_le_cover D dst n ms names
        (fun name' hmem => hle name' (List.Mem.tail _ hmem))
      omega
    · have ih' := ih htail hcons.2 (fun name' hmem => hle name' (List.Mem.tail _ hmem))
      have hhead := hle name (List.Mem.head _)
      omega

theorem src_bound (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (hcr : w.crashed = false) (host : InstId)
    (hlive : (w.st host).life = .alive) (name : String) :
    srcLen I.desc name (w.st host).box ≤ popBudget I.desc (tname host) name w.N := by
  have hI := inv_reachable I N w hL hR
  cases ht : templateOf I.desc name with
  | none => simp [srcLen, popBudget, ht]
  | some t =>
    cases hm : t.multiplicity with
    | perPeer =>
      have hbeq : (t.multiplicity == .perPeer) = true := by
        rw [hm]
        decide
      simp only [srcLen, popBudget, ht, hbeq, ite_true]
      have hname := name_le_held I w hO hI.seal.childless hcr host hlive name
      have hfac : popFactor w.N t = w.N := by
        unfold popFactor
        rw [hbeq]
        simp
      rw [hfac, reach_N I N w hR]
      exact Nat.le_trans hname
        (Nat.mul_le_mul_right _ (held_le_sender I hL hG N w hR hcr name))
    | one =>
      have hbeq : (t.multiplicity == .perPeer) = false := by
        rw [hm]
        decide
      simp only [srcLen, popBudget, ht, hbeq, ite_false]
      have hfac : popFactor w.N t = 1 := by
        unfold popFactor
        rw [hbeq]
        simp
      rw [hfac, Nat.one_mul]
      exact core_le_budget I w hO hcr name (tname host) host (hO.aliveIn host hlive) rfl

/-- The sender that still holds a token is one under its own charge. -/
theorem src_succ (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (hcr : w.crashed = false) (host sender : InstId)
    (hlive : (w.st host).life = .alive) (hlife : (w.st sender).life = .alive)
    (hhold : 1 ≤ tokenHold I.desc (tname sender) (tname host) (w.st sender)) :
    srcLen I.desc (tname sender) (w.st host).box + 1 ≤
      popBudget I.desc (tname host) (tname sender) w.N := by
  have hI := inv_reachable I N w hL hR
  have hmemS := hO.aliveIn sender hlife
  obtain ⟨t, ht, hmul⟩ := hO.shaped sender hmemS
  have htn : t.name = tname sender := (templateOf_mem I.desc (tname sender) t ht).2
  have htname : templateOf I.desc (tname sender) = some t := by simpa [htn] using ht
  cases hm : t.multiplicity with
  | perPeer =>
    have hbeq : (t.multiplicity == .perPeer) = true := by
      rw [hm]
      decide
    simp only [srcLen, popBudget, htname, hbeq, ite_true]
    have hex : ∃ k g, sender = InstId.peer t.name k g := by simpa [hm] using hmul
    obtain ⟨k, g, hsender⟩ := hex
    have hpeer : sender = InstId.peer (tname sender) k g := by simpa [htn] using hsender
    have hlen := peer_name_succ I w hO hI.seal.childless hcr host hlive (tname sender) k g
      sender hpeer hmemS hlife hhold
    have hfac : popFactor w.N t = w.N := by
      unfold popFactor
      rw [hbeq]
      simp
    rw [hfac, reach_N I N w hR]
    exact Nat.le_trans hlen
      (Nat.mul_le_mul_right _ (held_le_sender I hL hG N w hR hcr (tname sender)))
  | one =>
    have hbeq : (t.multiplicity == .perPeer) = false := by
      rw [hm]
      decide
    simp only [srcLen, popBudget, htname, hbeq, ite_false]
    have hfac : popFactor w.N t = 1 := by
      unfold popFactor
      rw [hbeq]
      simp
    rw [hfac, Nat.one_mul]
    have hid : sender = InstId.core t.name := by simpa [hm] using hmul
    have hcore : sender = InstId.core (tname sender) := by simpa [htn] using hid
    have hhold' : 1 ≤ tokenHold I.desc (tname sender) (tname host)
        (w.st (InstId.core (tname sender))) := by
      rw [← hcore]
      exact hhold
    have hl' : (w.st (InstId.core (tname sender))).life = .alive := by
      rw [← hcore]
      exact hlife
    have hmemC : InstId.core (tname sender) ∈ w.roster := by
      rw [← hcore]
      exact hmemS
    exact core_succ I w hO (tname sender) (tname host) host (hO.aliveIn host hlive) rfl
      hl' hmemC hhold'

/-- A live Lemma-1 mailbox has room for one more message from a sender that
still holds a token. Each per-peer template is charged `N` budgets, one per
held key, and each core is charged one. `nameCover` puts that sum under
`totalOcc.eval`, and Lemma 1 puts the evaluation under `capBulk`. -/
theorem l1_box_room (I : Impl) (hL : LocalOk I) (hG : GraphOk I.desc) (N : Nat) (w : World)
    (hR : Reachable I N w) (hO : OccInv I w) (hcr : w.crashed = false) (host sender : InstId)
    (hlive : (w.st host).life = .alive) (hl1 : l1 I.desc (tname host) = true)
    (hlife : (w.st sender).life = .alive)
    (hhold : 1 ≤ tokenHold I.desc (tname sender) (tname host) (w.st sender)) :
    (w.st host).box.length + 1 ≤ capBulk I.desc w.N host := by
  let names := I.desc.templates.map (·.name)
  have hnd := birth_names I.desc hG
  have hpick : ∀ m ∈ (w.st host).box, ∃ name ∈ names, hits I.desc name m = true := by
    intro m hm
    have hsend := hO.sentFrom host m hm
    have hshape := hO.shaped m.sender hsend
    refine ⟨tname m.sender, ?_, hits_shaped I.desc m.sender m rfl hshape⟩
    obtain ⟨t, ht, _⟩ := hshape
    exact List.mem_map.mpr ⟨t, (templateOf_mem I.desc (tname m.sender) t ht).1,
      (templateOf_mem I.desc (tname m.sender) t ht).2⟩
  have honly : ∀ m ∈ (w.st host).box, ∀ name' ∈ names, ∀ name ∈ names,
      hits I.desc name m = true → name' ≠ name → hits I.desc name' m = false := by
    intro m _ name' _ name _ hyes hne
    exact hits_only I.desc m name name' hyes hne
  have hlen := length_le_src I.desc names (w.st host).box hnd hpick honly
  have hmemS := hO.aliveIn sender hlife
  obtain ⟨tS, htS, _⟩ := hO.shaped sender hmemS
  have hsName : tname sender ∈ names :=
    List.mem_map.mpr ⟨tS, (templateOf_mem I.desc (tname sender) tS htS).1,
      (templateOf_mem I.desc (tname sender) tS htS).2⟩
  have hle : ∀ name ∈ names, srcLen I.desc name (w.st host).box ≤
      popBudget I.desc (tname host) name w.N := by
    intro name _
    exact src_bound I hL hG N w hR hO hcr host hlive name
  have hextra := src_succ I hL hG N w hR hO hcr host sender hlive hlife hhold
  have hsum := sumSrc_cover_slack I.desc (tname host) w.N (w.st host).box names (tname sender)
    hsName hnd hle hextra
  have hocc := name_cover_le I hL hG (tname host) w.N
  have hcap := cap_of_l1 I.desc host w.N hl1
  exact Nat.le_trans (Nat.add_le_add_right hlen 1) (Nat.le_trans hsum (Nat.le_trans hocc hcap))

/-- `offerPrio` writes the priority lane, or crashes and copies every queue. -/
theorem offerPrio_parked (D : Description) (w : World) (host : InstId) (msg : Msg) (i : InstId) :
    ((offerPrio D w host msg).st i).parked = (w.st i).parked := by
  unfold offerPrio
  by_cases hfull : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = true
  · simp only [hfull, ite_true]
    exact (crash_queues w i).2.2.1
  · have hfullF : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) = false := by
      cases hb : decide (prioLoad (w.st host).prio ≥ capPrio D w.N host) with
      | false => rfl
      | true => exact absurd hb hfull
    simp only [hfullF, ite_false]
    by_cases hi : i = host
    · simp [setActor, hi]
    · simp [setActor, hi]

/-- A tombstone is a priority message, a dropped delivery, or a crash.
None of the three writes a parked list. -/
theorem enqueueTombstone_parked (D : Description) (w : World) (child i : InstId) :
    ((enqueueTombstone D w child).st i).parked = (w.st i).parked := by
  unfold enqueueTombstone
  cases hpar : (w.st child).parent with
  | none => simp [hpar]
  | some parent =>
    simp only [hpar]
    by_cases hlive : ((w.st parent).life != .alive) = true
    · simp [hlive]
    · have hliveF : ((w.st parent).life != .alive) = false := by
        cases hb : (w.st parent).life != .alive with
        | false => rfl
        | true => exact absurd hb hlive
      simp only [hliveF, ite_false]
      by_cases hlab : ((tombstoneMsg D (w.st parent) child).label == "") = true
      · simp only [hlab, ite_true]
        exact (crash_queues w i).2.2.1
      · have hlabF : ((tombstoneMsg D (w.st parent) child).label == "") = false := by
          cases hb : (tombstoneMsg D (w.st parent) child).label == "" with
          | false => rfl
          | true => exact absurd hb hlab
        simp only [hlabF, ite_false]
        exact offerPrio_parked D w parent (tombstoneMsg D (w.st parent) child) i

theorem set_proceed_parked (w : World) (id i : InstId) (k : Cont) (a : Actor)
    (hpa : a.parked = (w.st id).parked) :
    ((setActor w id (proceed a k)).st i).parked = (w.st i).parked := by
  by_cases hi : i = id
  · simp [setActor, hi, proceed_fields, hpa]
  · simp [setActor, hi]

theorem set_finish_parked (w : World) (id i : InstId) (k : Cont) (r : CallResult) (a : Actor)
    (hpa : a.parked = (w.st id).parked) :
    ((setActor w id (finishCall a k r)).st i).parked = (w.st i).parked := by
  by_cases hi : i = id
  · simp [setActor, hi, finishCall_fields, hpa]
  · simp [setActor, hi]

/-- A reply writes a continuation. The parked lists stay. -/
theorem performReply_parked (w : World) (sender i : InstId) (k : Cont) :
    ((performReply w sender k).st i).parked = (w.st i).parked := by
  cases hr : k.replyTo with
  | none =>
    simp only [performReply, hr]
    exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
  | some caller =>
    simp only [performReply, hr]
    cases hph : (w.st caller).phase with
    | awaitReply dst ck =>
      simp only [hph]
      by_cases hmatch : (decide (dst = sender) &&
          decide ((w.st sender).oweId = some (w.st caller).waitId)) = true
      · simp only [hmatch, ite_true]
        let w1 := setActor w caller (finishCall (w.st caller) ck .reply)
        have h1 : ∀ j, (w1.st j).parked = (w.st j).parked :=
          fun j => set_finish_parked w caller j ck .reply (w.st caller) rfl
        exact (set_proceed_parked w1 sender i (afterHead k) (w1.st sender) rfl).trans (h1 i)
      · have hmatchF : (decide (dst = sender) &&
            decide ((w.st sender).oweId = some (w.st caller).waitId)) = false := by
          cases hb : decide (dst = sender) &&
              decide ((w.st sender).oweId = some (w.st caller).waitId) with
          | false => rfl
          | true => exact absurd hb hmatch
        simp only [hmatchF, ite_false]
        exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | idle =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | run _ =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | parked _ _ _ =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | awaitEffect _ =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | awaitPeer _ =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl
    | crashed =>
      simp only [hph]
      exact set_proceed_parked w sender i (afterHead k) (w.st sender) rfl

theorem tryWake_parked (D : Description) (w : World) (dstId : InstId) (label : String)
    (writer i : InstId) : ((tryWake D w dstId label writer).st i).parked = (w.st i).parked := by
  simp only [tryWake]
  split
  · rfl
  · exact offerPrio_parked D w dstId _ i

theorem wakeFold_parked (D : Description) (writer : InstId) (label : String) :
    ∀ (ids : List InstId) (w : World) (i : InstId),
      ((ids.foldl (fun w id => tryWake D w id label writer) w).st i).parked = (w.st i).parked := by
  intro ids
  induction ids with
  | nil => intro _ _; rfl
  | cons hd tl ih =>
    intro w i
    simp only [List.foldl_cons]
    rw [ih, tryWake_parked]

theorem wakeReaders_parked (D : Description) (w : World) (dst label : String) (writer i : InstId) :
    ((wakeReaders D w dst label writer).st i).parked = (w.st i).parked := by
  simp only [wakeReaders, readersOf]
  exact wakeFold_parked D writer label (w.roster.filter fun id =>
    tname id == dst && (w.st id).life == .alive) w i

/-- Installing one born peer replaces that id's actor with an empty mailbox
and leaves every other parked list alone. `next` is a key or index bump. -/
theorem placePeer_park (I : Impl) (w : World) (template : String) (k : Nat) (initial : String)
    (parent : Option InstId) (next : World → World)
    (hst : ∀ (u : World) (j : InstId), ((next u).st j) = u.st j) (i : InstId) :
    ((placePeer I w template k initial parent next).st i).parked = (w.st i).parked ∨
      ((placePeer I w template k initial parent next).st i).parked = [] := by
  let bornId := InstId.peer template k (maxGen w template k)
  let born := { bornActor I.desc w template k initial with parent := parent }
  let w0 := { w with roster := w.roster ++ [bornId] }
  let w1 := next w0
  have hbase : placePeer I w template k initial parent next =
      readCells I.desc (setActor w1 bornId born) bornId := by
    simp [placePeer, bornId, born, w0, w1]
  rw [hbase, cellsSt]
  by_cases hi : i = bornId
  · exact Or.inr (by simp [setActor, hi, born, bornActor, withKeyTokens])
  · exact Or.inl (by rw [setActor_other w1 bornId i born hi, hst w0 i])

/-- A child birth is a no-op, or it installs one empty actor. -/
theorem spawnChild_park (I : Impl) (w w' : World) (parent : InstId) (child : String) (i : InstId)
    (h : spawnChild I w parent child = some w') :
    (w'.st i).parked = (w.st i).parked ∨ (w'.st i).parked = [] := by
  unfold spawnChild at h
  cases ht : templateOf I.desc child with
  | none => simp [ht] at h
  | some t =>
    simp only [ht] at h
    by_cases hcond : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
        (w.st parent).life == .alive) = true
    · rw [hcond] at h
      rw [ite_eq_left (by decide : true = true)] at h
      cases parent with
      | core _ => simp at h
      | peer pname pk pg =>
        dsimp only at h
        by_cases hblock : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = true
        · rw [hblock] at h
          rw [ite_eq_left (by decide : true = true)] at h
          cases h
          exact Or.inl rfl
        · have hblockF : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk = false := by
            cases hb : slotRespawnBlocked I.desc w (InstId.peer pname pk pg) child pk with
            | false => rfl
            | true => exact absurd hb hblock
          rw [hblockF] at h
          rw [ite_eq_right (by decide : ¬ false = true)] at h
          injection h with hw
          subst hw
          let bornId := InstId.peer child pk (maxGen w child pk)
          by_cases hnew : i = bornId
          · exact Or.inr (by
              unfold bornId at hnew
              simp [hnew, admitBorn, cellsSt, setActor, bornActor, withKeyTokens])
          · exact Or.inl (by
              unfold bornId at hnew
              simp [admitBorn, cellsSt, setActor, hnew])
    · have hcondF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
          (w.st parent).life == .alive) = false := by
        cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) &&
            (w.st parent).life == .alive with
        | false => rfl
        | true => exact absurd hb hcond
      rw [hcondF] at h
      rw [ite_eq_right (by decide : ¬ false = true)] at h
      by_cases hsup : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = true
      · rw [hsup] at h
        rw [ite_eq_left (by decide : true = true)] at h
        cases h
        exact Or.inl rfl
      · have hsupF : (t.multiplicity == .perPeer && supNamed t.supervisor (tname parent)) = false := by
          cases hb : t.multiplicity == .perPeer && supNamed t.supervisor (tname parent) with
          | false => rfl
          | true => exact absurd hb hsup
        rw [hsupF] at h
        rw [ite_eq_right (by decide : ¬ false = true)] at h
        simp at h

/-- A parked entry that was not already queued was stored on the live
destination, and that destination had no room. -/
theorem enqueue_fresh (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (p : Parked)
    (hp : p ∈ ((enqueueOrPark w D sender dst msg isCall k).st i).parked) :
    p ∈ (w.st i).parked ∨
      i = dst ∧ (w.st dst).life = .alive ∧
        ¬((w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst) := by
  cases isCall <;>
    (unfold enqueueOrPark at hp
     by_cases hlive : (w.st dst).life = .alive
     · simp [hlive] at hp
       by_cases hroom : (w.st dst).parked = [] ∧ (w.st dst).box.length < capBulk D w.N dst
       · simp [hroom] at hp
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hp
           simp [setActor] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp at hp
             rw [hi]
             exact Or.inl hp
           · simp [setActor, hi] at hp
             exact Or.inl hp
         · rw [if_neg hsame] at hp
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp at hp
             rw [hi]
             exact Or.inl hp
           · by_cases hid : i = dst
             · simp [hid, hlive] at hp
               rw [if_neg hflip] at hp
               simp at hp
             · rw [if_neg hi, if_neg hid] at hp
               exact Or.inl hp
       · simp [hroom] at hp
         by_cases hsame : sender = dst
         · rw [if_pos hsame] at hp
           simp [setActor] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall, List.mem_append, List.mem_singleton] at hp
             try rw [(proceed_fields _ k).2.2.2.1] at hp
             try simp [List.mem_append, List.mem_singleton] at hp
             rcases hp with hp | rfl
             · rw [hi]; exact Or.inl hp
             · exact Or.inr ⟨hi.trans hsame, hlive, hroom⟩
           · simp [setActor, hi] at hp
             exact Or.inl hp
         · rw [if_neg hsame] at hp
           have hflip : dst ≠ sender := fun h => hsame h.symm
           simp [setActor, hflip] at hp
           by_cases hi : i = sender
           · simp [hi, chargeSender, bumpToken, issueCall] at hp
             rw [hi]
             exact Or.inl hp
           · by_cases hid : i = dst
             · simp [hid, hlive, List.mem_append, List.mem_singleton] at hp
               try rw [if_neg hflip] at hp
               try simp [List.mem_append, List.mem_singleton] at hp
               rcases hp with hp | rfl
               · rw [hid]; exact Or.inl hp
               · exact Or.inr ⟨hid, hlive, hroom⟩
             · rw [if_neg hi, if_neg hid] at hp
               exact Or.inl hp
     · rw [if_pos hlive] at hp
       by_cases hi : i = sender
       · simp [hi, setActor, issueCall, finishCall] at hp
         try rw [(proceed_fields _ k).2.2.2.1] at hp
         try rw [(proceed_fields _ (selectCall k _)).2.2.2.1] at hp
         try simp at hp
         rw [hi]
         exact Or.inl hp
       · simp [setActor, hi] at hp
         exact Or.inl hp)

/-- Parked mail after `enqueueOrPark` on an id that started empty. An alive
Lemma-1 destination has room, so the fresh entry is not stored there. -/
theorem enqueue_l1_park (w : World) (D : Description) (sender dst : InstId) (msg : Msg)
    (isCall : Bool) (k : Cont) (i : InstId) (hempty : (w.st i).parked = [])
    (hl1 : l1 D (tname i) = true)
    (hlen : l1 D (tname dst) = true → (w.st dst).life = .alive →
      (w.st dst).box.length < capBulk D w.N dst) :
    ((enqueueOrPark w D sender dst msg isCall k).st i).parked = [] := by
  cases hpark : ((enqueueOrPark w D sender dst msg isCall k).st i).parked with
  | nil => rfl
  | cons p _ =>
    have hp : p ∈ ((enqueueOrPark w D sender dst msg isCall k).st i).parked := by simp [hpark]
    rcases enqueue_fresh w D sender dst msg isCall k i p hp with h | ⟨heq, hlive, hnot⟩
    · simp [hempty] at h
    · subst heq
      exact absurd ⟨hempty, hlen hl1 hlive⟩ hnot

end Deadlock
