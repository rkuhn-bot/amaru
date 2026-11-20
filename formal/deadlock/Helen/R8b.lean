import Deadlock.Semantics
import Deadlock.Local
import Std.Data.HashSet
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen8b
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

/-! Section A: the original designs under 25fc0d224. -/

/-- N11 original (`landImpl 4 2 0`): `LocalOk` now rejects it. -/
theorem orig_land_rejected : ¬ LocalOk LI := by unfold LocalOk; decide
theorem orig_land_rejectedB : localOkB LI = false := by decide
theorem orig_land_graph_still : checkBool (landDesc 4 2 0) = true := by decide

/-- N12 original (`pcImpl 4 0 2`): `LocalOk` still ACCEPTS it. The fix is the
runtime ingress gate: the original trace is now refused at its fifth action. -/
theorem orig_pc_still_local : LocalOk PC.PI := by unfold LocalOk; decide
theorem orig_pc_trace_refused : runAt PC.PI 0 PC.pcActs = none ∧
    (runAt PC.PI 0 (PC.pcActs.take 4)).isSome = true ∧
    runAt PC.PI 0 (PC.pcActs.take 5) = none := by decide

end Deadlock.Helen8b
open Deadlock Deadlock.Helen8b
#eval showHit (search LI 0 14)
#eval showHit (search PC.PI 0 16)
#eval (Id.run do
  let mut out : List String := []
  for capA in [1,2,3,4,5,6] do
    for capB in [0,1] do
      for k in [0,1,2,3] do
        let I := PC.pcImpl capA capB k
        if checkBool I.desc && localOkB I then
          out := out ++ [s!"pc {capA} {capB} {k}: {showHit (search I 0 14)}"]
  return out)
#eval (Id.run do
  let mut out : List String := []
  for cap in [1,2,3,4,5,6] do
    for occW in [0,1,2,3] do
      for occM in [0,1,2] do
        let I := landImpl cap occW occM
        if checkBool I.desc && localOkB I then
          out := out ++ [s!"land {cap} {occW} {occM}: {showHit (search I 0 14)}"]
  return out)
#print axioms Deadlock.Helen8b.orig_land_rejected
#print axioms Deadlock.Helen8b.orig_land_rejectedB
#print axioms Deadlock.Helen8b.orig_pc_still_local
#print axioms Deadlock.Helen8b.orig_pc_trace_refused
#eval localIssues LI
