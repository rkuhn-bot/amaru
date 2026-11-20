import Deadlock.Semantics
import Deadlock.Local
import Std.Data.HashSet
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen8f
open Deadlock

/-! Round 8, N11/N12. Section A: my ORIGINAL R7b/R7d designs, copied verbatim
from /workspace/lean-review-e5f48c/formal/deadlock/Helen/R7b.lean:8-84 and
R7d.lean:44-80 (definitions only, no API change was needed). -/
/-! Copied verbatim from Examples.lean:8-33 (Examples cannot be imported beside
Semantics: both declare `Deadlock.overflowDesc`). -/
def tpl (name : String) (cap : Nat) (states : List String) (initial : String) (mustFit : Bool) : Template where
  name := name
  multiplicity := .one
  capacity := .ofNat cap
  priorityCapacity := .ofNat 4
  priorityBound := .ofNat 1
  states := states
  initial := initial
  terminable := false
  untimedPeer := false
  mustFit := mustFit

def sendEdge (src ss dst label : String) (occ : Nat) : Edge where
  src := src
  srcState := ss
  dst := dst
  kind := .blocking
  reliability := .reliable
  effect := .send
  label := label
  scope := .intra
  occupancy := .ofNat occ
  repliesInDequeue := false
  ingress := false
  ingressLegal := none
  cell := .none

def tr (t f l to : String) (p : List Eff) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := false, release := 1 }

def runAt (I : Impl) (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply I a)) (some (initWorld I N))


/-! ## N1 variant: a branch lands in a typestate whose floor is higher than `toState`'s.
`sendsOk` checks the program against `toState` only. -/

def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def landDesc (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Description where
  name := "branch-landing"
  freshNames := true
  templates := [tpl "A" cap ["idle", "w", "miss"] "idle" true]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" occW, sendEdge "A" "miss" "A" "M" occM]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "miss", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "A", fromState := "miss", toState := "miss", label := "M" }]

def landImpl (cap : Nat) (occW : Nat := 1) (occM : Nat := 0) : Impl where
  desc := landDesc cap occW occM
  transitions := [{ tr "A" "idle" "Go" "w" [.peer [.send "A" "M" 0]] with toTimeout := "miss" },
                  tr "A" "w" "Go" "w" [],
                  tr "A" "miss" "Go" "w" (List.replicate (occW + 1) (.send "A" "M" 0)),
                  tr "A" "idle" "M" "idle" [],
                  tr "A" "w" "M" "w" [],
                  tr "A" "miss" "M" "miss" []]

def Ac : InstId := .core "A"

def landActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .callTimeout Ac, .exec Ac,
   .recvBulk Ac, .exec Ac, .exec Ac, .exec Ac]

def snap (w : World) : String × Nat × Nat × Nat × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | _ => 3)

def LI : Impl := landImpl 4 2 0

namespace PC
def ingA (st : String) : Edge :=
  { (sendEdge "A" st "A" "Go" 1) with effect := .trySend, kind := .nonBlocking, ingress := true, ingressLegal := some (Affine.ofNat 1) }

def pcDesc (capA capB k : Nat) : Description where
  name := "parked-call"
  freshNames := true
  templates := [tpl "A" capA ["idle", "w"] "idle" true, tpl "B" capB ["idle"] "idle" false]
  edges := [ingA "idle", ingA "w", sendEdge "A" "w" "A" "M" k,
            { (sendEdge "A" "w" "B" "Q" 1) with effect := .call, repliesInDequeue := true }]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "w", label := "Go" },
            { template := "A", fromState := "w", toState := "w", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "A", fromState := "w", toState := "w", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Q" }]

def trc (t f l to : String) (p : List Eff) (c : Bool) : Transition :=
  { template := t, fromState := f, label := l, program := p, toState := to, acceptsCall := c, release := 1 }

def pcImpl (capA capB k : Nat) : Impl where
  desc := pcDesc capA capB k
  transitions := [trc "A" "idle" "Go" "w" [.call "B" "Q" 0 [] (List.replicate k (.send "A" "M" 0))] false,
                  trc "A" "w" "Go" "w" [] false,
                  trc "A" "idle" "M" "idle" [] false,
                  trc "A" "w" "M" "w" [] false,
                  trc "B" "idle" "Q" "idle" [.reply] true]

def Ac : InstId := .core "A"
def Bc : InstId := .core "B"

def snap (w : World) : String × Nat × Nat × Nat × Nat :=
  ((w.st Ac).typestate, (w.st Ac).box.length, (w.st Ac).parked.length, (w.st Ac).tokens "A",
   match (w.st Ac).phase with | .parked _ _ _ => 1 | .idle => 0 | .run _ => 2 | .awaitReply _ _ => 4 | _ => 3)
def pcActs : List Action :=
  [.ingress Ac "Go", .recvBulk Ac, .exec Ac, .ingress Ac "Go", .ingress Ac "Go", .ingress Ac "Go",
   .recvBulk Bc, .callTimeout Ac, .exec Ac, .exec Ac, .exec Bc]
def PI : Impl := pcImpl 4 0 2
end PC

/-! Section S: bounded explorer (copied from Helen/R8Search.lean). -/
def idS : InstId → String
  | .core n => n
  | .peer n k g => s!"{n}@{k}.{g}"

def lifeS : Life → String
  | .absent => "a" | .alive => "L" | .shuttingDown => "s" | .dead => "d"

def phS (p : Phase) : String :=
  match p with
  | .idle => "i"
  | .run k => s!"r{k.rest.length}{k.toState}"
  | .parked d c k => s!"p{idS d}{c}{k.rest.length}{k.toState}"
  | .awaitReply d k => s!"w{idS d}{k.rest.length}"
  | .awaitEffect k => s!"e{k.rest.length}"
  | .awaitPeer k => s!"P{k.rest.length}"
  | .crashed => "X"

def fp (w : World) : String :=
  String.intercalate "|" (w.roster.map fun id =>
    let a := w.st id
    s!"{idS id}:{lifeS a.life}:{a.typestate}:{phS a.phase}:{(a.box.map (·.label))}:{(a.prio.map (·.label))}:{a.parked.length}:{a.tokens (tname id)}")
  ++ s!"#{w.crashed}"

def ingressLabels (D : Description) : List (String × String) :=
  (D.edges.filter (·.ingress)).map fun e => (e.dst, e.label)

def candidates (I : Impl) (w : World) : List Action :=
  (w.roster.flatMap fun id =>
    [Action.recvBulk id, .recvPrio id, .exec id, .finish id, .callTimeout id] ++
    (((ingressLabels I.desc).filter (fun (p : String × String) => p.1 == tname id)).eraseDups.map (fun (p : String × String) => Action.ingress id p.2))) ++
  I.desc.templates.map (fun t => Action.spawn t.name)

/-- A self-park: a blocking send or call parked on the actor's own box. Nobody
else can drain it, so the actor is stuck forever. -/
def selfPark (w : World) : Option InstId :=
  w.roster.find? fun id => match (w.st id).phase with
    | .parked d _ _ => d == id && (w.st id).life == .alive
    | _ => false

def overrun (I : Impl) (w : World) : Option InstId :=
  w.roster.find? fun id => (w.st id).box.length > capBulk I.desc w.N id

structure Hit where
  kind : String
  trace : List Action

partial def dfs (I : Impl) (depth : Nat) (w : World) (trace : List Action)
    (seen : Std.HashSet String) : Std.HashSet String × Option Hit :=
  if w.crashed then (seen, none) else
  match selfPark w with
  | some id => (seen, some ⟨s!"selfPark {idS id}", trace.reverse⟩)
  | none =>
  match overrun I w with
  | some id => (seen, some ⟨s!"overrun {idS id}", trace.reverse⟩)
  | none =>
  if depth == 0 then (seen, none) else
  (candidates I w).foldl (fun (acc : Std.HashSet String × Option Hit) a =>
    match acc with
    | (s, some h) => (s, some h)
    | (s, none) =>
      match apply I a w with
      | none => (s, none)
      | some w' =>
        let f := fp w' ++ s!"/{depth}"
        if s.contains f then (s, none)
        else dfs I (depth - 1) w' (a :: trace) (s.insert f)) (seen, none)

def search (I : Impl) (N depth : Nat) : Option Hit :=
  (dfs I depth (initWorld I N) [] {}).2

def showHit : Option Hit → String
  | none => "no hit"
  | some h => s!"{h.kind}: {repr h.trace}"


/-! Section F: random single-core designs (A self-sends, optional call to core B).
Each sample that passes `checkBool` and `localOkB` is explored for a self-park
or a bulk overrun. -/

def S : List String := ["idle", "w", "m"]
def sA : Eff := .send "A" "M" 0
def progs : List (List Eff) :=
  [[], [sA], [sA, sA], [.peer [sA]], [.peer []], [.call "B" "Q" 0 [] [sA]],
   [.call "B" "Q" 0 [sA] []], [.call "B" "Q" 0 [] [sA, sA]], [.trySend "A" "M" 0 [sA] []],
   [.peer [.peer [sA]]], [.call "B" "Q" 0 [] [.peer [sA]]], [sA, .peer [sA]],
   [.call "B" "Q" 0 [.peer [sA]] [sA]], [.trySend "A" "M" 0 [] [sA]], [.peer [sA, sA]],
   [.call "B" "Q" 0 [] [.call "B" "Q" 0 [] [sA]]], [.trySend "A" "M" 0 [.peer [sA]] [sA]]]

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
def pick {α} [Inhabited α] (xs : List α) (s : Nat) : α := xs.getD ((s / 65536) % xs.length) default

structure Gen where
  seed : Nat
  impl : Impl

def mkImpl (seed0 : Nat) : Impl := Id.run do
  let mut s := seed0
  let mut edges : List Edge := []
  let mut trs : List Transition := []
  let mut steps : List CompatStep := []
  s := lcg s; let capB := (s / 65536) % 2
  for st in S do
    s := lcg s; let occ := (s / 65536) % 4
    s := lcg s; let occC := (s / 65536) % 2
    s := lcg s; let _occT := (s / 65536) % 2
    edges := edges ++ [ingA st, sendEdge "A" st "A" "M" occ,
      { (sendEdge "A" st "B" "Q" occC) with effect := .call, repliesInDequeue := true }]
    for l in ["Go", "M"] do
      s := lcg s; let p := pick progs s
      s := lcg s; let to := pick S s
      s := lcg s; let tT := pick ("" :: S) s
      s := lcg s; let tO := pick ("" :: S) s
      s := lcg s; let tN := pick ("" :: S) s
      s := lcg s; let tF := pick ("" :: S) s
      trs := trs ++ [{ tr "A" st l to p with toTimeout := tT, toTimedOut := tO, toNotAdmitted := tN, toFull := tF }]
      for t2 in [to, tT, tO, tN, tF] do
        if t2 != "" then steps := steps ++ [{ template := "A", fromState := st, toState := t2, label := l }]
  steps := steps ++ [{ template := "B", fromState := "idle", toState := "idle", label := "Q" }]
  trs := trs ++ [{ tr "B" "idle" "Q" "idle" [.reply] with acceptsCall := true }]
  s := lcg s
  let occSum := (edges.filter (fun e => e.dst == "A")).foldl (fun n e => n + e.occupancy.eval 0) 0
  let capA := occSum + (s / 65536) % 2
  let D : Description :=
    { name := "fuzz", freshNames := true,
      templates := [tpl "A" capA S "idle" true, tpl "B" capB ["idle"] "idle" false],
      edges := edges, compatibility := .all, steps := steps.eraseDups }
  let I0 : Impl := { desc := D, transitions := trs }
  let trs' := trs.map fun t => if t.template == "A" && !(transitionOk I0 t) then { t with program := [] } else t
  return { desc := D, transitions := trs' }

def fuzz (n start depth : Nat) : Nat × Nat × List String := Id.run do
  let mut ok := 0
  let mut tried := 0
  let mut hits : List String := []
  for i in List.range n do
    let I := mkImpl (start + i * 7919)
    tried := tried + 1
    if checkBool I.desc && localOkB I then
      ok := ok + 1
      match search I 0 depth with
      | some h => hits := hits ++ [s!"seed {start + i * 7919}: {h.kind}"]
      | none => pure ()
  return (tried, ok, hits.take 5)

end Deadlock.Helen8f
open Deadlock Deadlock.Helen8f
#eval fuzz 60000 7 16
#eval ((List.range 3000).map (fun i => mkImpl (7 + i*7919))).countP (fun I => localOkB I && I.transitions.any (fun t => t.template == "A" && t.program != []))
#eval ((List.range 2000).map (fun i => mkImpl (1 + i*7919))).countP (fun I => checkBool I.desc)
#eval ((List.range 2000).map (fun i => mkImpl (1 + i*7919))).countP (fun I => localOkB I)
