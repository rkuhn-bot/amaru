import Deadlock.Semantics
import Deadlock.Local
import Std.Data.HashSet
set_option autoImplicit false
namespace Deadlock.Helen8S
open Deadlock

/-! A bounded explorer over `apply`. Used only with `#eval` to find traces; every
trace it finds is then replayed `by decide` in the R8 probe files. -/

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

end Deadlock.Helen8S
