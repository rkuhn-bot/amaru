import Deadlock.Counterexample
import Std.Data.HashSet
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen10f
open Deadlock
/-! Explorer with crash classification. `#eval` only. -/
def idS : InstId → String
  | .core n => n
  | .peer n k g => s!"{n}@{k}.{g}"
def lifeS : Life → String
  | .absent => "a" | .alive => "L" | .shuttingDown => "s" | .dead => "d"
def phT : Phase → String
  | .idle => "i" | .run k => s!"r{k.rest.length}" | .parked _ _ k => s!"p{k.rest.length}"
  | .awaitReply _ k => s!"w{k.rest.length}" | .awaitEffect _ => "e" | .awaitPeer _ => "P" | .crashed => "X"
def fp (w : World) : String :=
  String.intercalate "|" (w.roster.map fun id =>
    let a := w.st id
    s!"{idS id}:{lifeS a.life}:{a.typestate}:{a.pendingTombstone}:{(a.box.map (·.label))}:{(a.prio.map (·.label))}:{phT a.phase}")
def ingressLabels (D : Description) : List (String × String) :=
  ((D.edges.filter (·.ingress)).map fun e => (e.dst, e.label)).eraseDups
def candidates (I : Impl) (w : World) : List Action :=
  (w.roster.flatMap fun id =>
    [Action.recvBulk id, .recvPrio id, .exec id, .finish id] ++
    (((ingressLabels I.desc).filter (fun (p : String × String) => p.1 == tname id)).map
      (fun (p : String × String) => Action.ingress id p.2))) ++
  (I.desc.templates.filter (fun t => rootOf I.desc t && t.multiplicity == .perPeer)).map (fun t => Action.spawn t.name)

/-- Why the step from `w` by `a` crashed. -/
def classify (I : Impl) (w : World) (a : Action) : String :=
  match a with
  | .exec id =>
    let x := w.st id
    if x.life == .shuttingDown && x.pendingTombstone then
      match x.parent with
      | some p =>
        if (w.st p).life != .alive then s!"deadParentCrash({idS p} for {idS id})"
        else if (tombstoneMsg I.desc (w.st p) id).label == "" then s!"emptyLabel({idS p} for {idS id})"
        else if (w.st p).prio.length ≥ capPrio I.desc w.N p then s!"overflow({idS p} len {(w.st p).prio.length} for {idS id})"
        else "seal-other"
      | none => "seal-noparent"
    else
      match x.phase with
      | .run k => match k.rest with
        | e :: _ => s!"exec-other({idS id} {(repr e).pretty})"
        | [] => "exec-other"
      | _ => "exec-other"
  | _ => "other"

/-- E1 detector: `id` is about to run `.spawn c` as a per-peer parent at key k,
and the slot (c, k) is held by an occupant that `id` did not wire. -/
def orphanBlock (w : World) (id : InstId) : Option String :=
  match id, (w.st id).phase with
  | .peer _ k _, .run kk =>
    match kk.rest with
    | .spawn c :: _ =>
      if (w.st id).life == .alive &&
        w.roster.any (fun o => match o with
          | .peer n k' _ => n == c && k' == k && ((w.st o).life == .alive || (w.st o).life == .shuttingDown) &&
              (w.st o).parent != some id
          | .core _ => false)
      then some s!"orphanBlock({idS id} spawn {c})" else none
    | _ => none
  | _, _ => none

structure Hit where
  kind : String
  trace : List Action

partial def dfs (I : Impl) (ap : Action → World → Option World) (depth : Nat) (w : World)
    (trace : List Action) (seen : Std.HashSet String) : Std.HashSet String × Option Hit :=
  if depth == 0 then (seen, none) else
  (candidates I w).foldl (fun (acc : Std.HashSet String × Option Hit) a =>
    match acc with
    | (s, some h) => (s, some h)
    | (s, none) =>
      match ap a w with
      | none => (s, none)
      | some w' =>
        if w'.crashed then (s, some ⟨classify I w a, (a :: trace).reverse⟩) else
        let f := fp w' ++ s!"/{depth}"
        if s.contains f then (s, none)
        else dfs I ap (depth - 1) w' (a :: trace) (s.insert f)) (seen, none)

/-- Breadth-first, global visited set (fingerprint). Returns the first crash. -/
def search (I : Impl) (ap : Action → World → Option World) (N depth : Nat) (detectOrphan : Bool := true) : Option Hit := Id.run do
  let mut frontier : List (World × List Action) := [(initWorld I N, [])]
  let mut seen : Std.HashSet String := {}
  for _ in List.range depth do
    let mut next : List (World × List Action) := []
    for (w, tr) in frontier do
      for a in candidates I w do
        match ap a w with
        | none => pure ()
        | some w' =>
          if w'.crashed then return some ⟨classify I w a, (a :: tr).reverse⟩
          match a with
          | .exec id => match orphanBlock w id with
            | some k => if detectOrphan then return some ⟨k, (a :: tr).reverse⟩
            | none => pure ()
          | _ => pure ()
          let f := fp w'
          if !seen.contains f then
            seen := seen.insert f
            next := (w', a :: tr) :: next
    frontier := next
  return none

def stateCount (I : Impl) (ap : Action → World → Option World) (N depth : Nat) : Nat := Id.run do
  let mut frontier : List World := [initWorld I N]
  let mut seen : Std.HashSet String := {}
  for _ in List.range depth do
    let mut next : List World := []
    for w in frontier do
      for a in candidates I w do
        match ap a w with
        | none => pure ()
        | some w' =>
          let f := fp w'
          if !w'.crashed && !seen.contains f then
            seen := seen.insert f
            next := w' :: next
    frontier := next
  return seen.size

/-! Random restart designs: root R (subtree S), child C, optional grandchild G. -/
def bigC : Affine := { a := 16, b := 8 }
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
def pick {α} [Inhabited α] (xs : List α) (s : Nat) : α := xs.getD ((s / 65536) % xs.length) default

def rStates : List String := ["boot", "up", "down"]
def rLabels : List String := ["Go", "Kill", "dead/C"]
def rProgs : List (List Eff) := [[], [], [.spawn "C"], [.terminate], [.abort], [.abort, .spawn "C"]]
def cProgs (g : Bool) : List (List Eff) := if g then [[], [.terminate], [.spawn "G"], [.abort]] else [[], [.terminate]]

def fzR (capR : Nat) : Template :=
  { tpl "R" 8 rStates "boot" with subtree := "S", capacity := bigC, priorityCapacity := Affine.ofNat capR, terminable := true }
def fzC : Template :=
  { tpl "C" 8 ["idle"] "idle" with terminable := true, subtree := "S", supervisor := some "R", tombstone := "dead/C", capacity := bigC, priorityCapacity := Affine.ofNat 2 }
def fzG : Template :=
  { tpl "G" 8 ["idle"] "idle" with terminable := true, subtree := "S", supervisor := some "C", tombstone := "dead/G", capacity := bigC }

def mkImpl (seed0 : Nat) : Impl := Id.run do
  let mut s := lcg seed0
  let withG := (s / 65536) % 2 == 0
  s := lcg s; let capR := 1 + (s / 65536) % 2
  let mut trs : List Transition := []
  for st in rStates do
    for l in rLabels do
      s := lcg s; let p := pick rProgs s
      s := lcg s; let to := pick rStates s
      trs := trs ++ [tr "R" st l to p]
  for l in ["Die", "Go", "dead/G"] do
    s := lcg s; let p := pick (cProgs withG) s
    trs := trs ++ [tr "C" "idle" l "idle" p]
  if withG then trs := trs ++ [tr "G" "idle" "Die" "idle" [.terminate]]
  let edges := (rStates.flatMap fun st => rLabels.map fun l => ing "R" st l) ++
    (["Die", "Go", "dead/G"].map fun l => ing "C" "idle" l) ++ (if withG then [ing "G" "idle" "Die"] else [])
  let D : Description :=
    { name := "fz", freshNames := true,
      templates := [fzR capR, fzC] ++ (if withG then [fzG] else []),
      edges := edges, compatibility := .all,
      steps := trs.map fun t => step t.template t.fromState t.label t.toState }
  return { desc := D, transitions := trs }

def valid (I : Impl) : Bool :=
  checkBool I.desc && localOkB I &&
    I.desc.templates.all fun t => prioSized I.desc t.name (prioSenderBound I t.name)

def actS : Action → String
  | .spawn t => s!"spawn {t}" | .ingress d l => s!"in {idS d} {l}" | .recvBulk s => s!"rb {idS s}"
  | .recvPrio s => s!"rp {idS s}" | .exec s => s!"ex {idS s}" | .finish s => s!"fin {idS s}"
  | .callTimeout s => s!"to {idS s}" | .stutter => "stutter"

def rT20 : Template :=
  { tpl "R" 8 ["boot", "up"] "boot" with
      subtree := "S", capacity := { a := 8, b := 4 }, priorityCapacity := Affine.ofNat 1, terminable := true }
def kDesc0 : Description where
  name := "late-seal"
  freshNames := true
  templates := [rT20, cT]
  edges := [ing "R" "boot" "Go", ing "R" "up" "Go", ing "R" "up" "Kill", ing "R" "boot" "Kill", ing "R" "boot" "dead/C",
            ing "R" "up" "dead/C", ing "C" "idle" "Die"]
  compatibility := .all
  steps := [step "R" "boot" "Go" "up", step "R" "up" "Go" "up", step "R" "up" "Kill" "up", step "R" "boot" "Kill" "boot",
            step "R" "boot" "dead/C" "boot", step "R" "up" "dead/C" "up", step "C" "idle" "Die" "idle"]
def kImpl0 : Impl where
  desc := kDesc0
  transitions :=
    [tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "up" "Go" "up" [],
     tr "R" "up" "Kill" "up" [.terminate], tr "R" "boot" "Kill" "boot" [],
     tr "R" "boot" "dead/C" "boot" [], tr "R" "up" "dead/C" "up" [],
     tr "C" "idle" "Die" "idle" [.terminate]]


def fuzzA (n start N depth : Nat) (orph : Bool) : String := Id.run do
  let mut ok := 0
  let mut kinds : List (String × Nat) := []
  let mut ex : List String := []
  for i in List.range n do
    let I := mkImpl (start + i * 7919)
    if valid I then
      ok := ok + 1
      match search I (apply I) N depth orph with
      | some h =>
        let k := (h.kind.splitOn "(").head!
        kinds := match kinds.find? (·.1 == k) with
          | some _ => kinds.map fun (a, c) => if a == k then (a, c + 1) else (a, c)
          | none => kinds ++ [(k, 1)]
        if ex.length < 3 then
          ex := ex ++ [s!"seed {start + i * 7919}: {h.kind}: {h.trace.map actS}"]
      | none => pure ()
  return s!"orph={orph}: valid {ok} of {n}, hits {kinds}, examples {ex}"
def ingL2 (t st l : String) : Edge := ing t st l
def gR : Template := { tpl "R" 4 ["boot", "up"] "boot" with
  multiplicity := .perPeer, subtree := "S", terminable := true, capacity := { a := 4, b := 4 } }
def gC : Template := { tpl "C" 4 ["idle", "has"] "idle" with
  multiplicity := .perPeer, subtree := "S", supervisor := some "R", terminable := true,
  tombstone := "dead/C", capacity := { a := 8, b := 8 } }
def gG : Template := { tpl "G" 4 ["idle"] "idle" with
  multiplicity := .perPeer, subtree := "S", supervisor := some "C", terminable := true,
  tombstone := "dead/G", capacity := { a := 4, b := 4 } }
def gDesc : Description where
  name := "orphan-grandchild"
  freshNames := true
  templates := [gR, gC, gG]
  edges := [ingL2 "R" "boot" "Go", ingL2 "R" "boot" "dead/C", ingL2 "R" "up" "Go", ingL2 "R" "up" "dead/C", ingL2 "C" "idle" "Go", ingL2 "C" "has" "Go",
            ingL2 "C" "idle" "Die", ingL2 "C" "has" "Die", ingL2 "C" "idle" "dead/G", ingL2 "C" "has" "dead/G",
            ingL2 "G" "idle" "Die"]
  compatibility := .all
  steps := [step "R" "boot" "Go" "up", step "R" "boot" "dead/C" "boot", step "R" "up" "Go" "up", step "R" "up" "dead/C" "up",
            step "C" "idle" "Go" "has", step "C" "has" "Go" "has",
            step "C" "idle" "Die" "idle", step "C" "has" "Die" "has",
            step "C" "idle" "dead/G" "idle", step "C" "has" "dead/G" "has",
            step "G" "idle" "Die" "idle"]
def gImpl : Impl where
  desc := gDesc
  transitions := [tr "R" "boot" "Go" "up" [.spawn "C"], tr "R" "boot" "dead/C" "boot" [],
                  tr "R" "up" "Go" "up" [], tr "R" "up" "dead/C" "up" [.spawn "C"],
                  tr "C" "idle" "Go" "has" [.spawn "G"], tr "C" "has" "Go" "has" [],
                  tr "C" "idle" "Die" "idle" [.terminate], tr "C" "has" "Die" "has" [.terminate],
                  tr "C" "idle" "dead/G" "idle" [], tr "C" "has" "dead/G" "has" [],
                  tr "G" "idle" "Die" "idle" [.terminate]]


end Deadlock.Helen10f
open Deadlock Deadlock.Helen10f

#eval (search kImpl0 (apply kImpl0) 2 12 false).map fun h => (h.kind, h.trace.map actS)
#eval stateCount kImpl0 (apply kImpl0) 2 12
#eval (search gImpl (apply gImpl) 1 18 true).map fun h => (h.kind, h.trace.map actS)
