import Deadlock
namespace Deadlock.Helen
open Deadlock
def ing (t label : String) : Edge where
  src := t
  srcState := "idle"
  dst := t
  kind := .nonBlocking
  reliability := .reliable
  effect := .trySend
  label := label
  scope := .intra
  occupancy := .ofNat 1
  repliesInDequeue := false
  ingress := true
  ingressLegal := some (Affine.ofNat 1)
  cell := .none

def tr (t label : String) (p : List Eff) : Transition :=
  { template := t, fromState := "idle", label := label, program := p, toState := "idle",
    acceptsCall := false, release := 1 }

def cycDesc : Description where
  name := "cycle-plus-clock"
  freshNames := true
  templates := [tpl "A" 1 ["idle"] "idle" false, tpl "B" 1 ["idle"] "idle" false,
                tpl "C" 1 ["idle"] "idle" true]
  edges := [ing "A" "Go", ing "B" "Go", ing "C" "Tick",
            sendEdge "A" "idle" "B" "M" 2, sendEdge "B" "idle" "A" "M" 2]
  compatibility := .all
  steps := [{ template := "A", fromState := "idle", toState := "idle", label := "Go" },
            { template := "A", fromState := "idle", toState := "idle", label := "M" },
            { template := "B", fromState := "idle", toState := "idle", label := "Go" },
            { template := "B", fromState := "idle", toState := "idle", label := "M" },
            { template := "C", fromState := "idle", toState := "idle", label := "Tick" }]

def cycImpl : Impl where
  desc := cycDesc
  transitions := [tr "A" "Go" [.send "B" "M" 0, .send "B" "M" 0], tr "A" "M" [],
                  tr "B" "Go" [.send "A" "M" 0, .send "A" "M" 0], tr "B" "M" [],
                  tr "C" "Tick" []]

def A : InstId := .core "A"
def B : InstId := .core "B"
def C : InstId := .core "C"

def cycActs : List Action :=
  [.ingress A "Go", .ingress B "Go", .recvBulk A, .recvBulk B,
   .exec A, .exec B, .exec A, .exec B]

def after (acts : List Action) : Option World := runFrom cycImpl (some (initWorld cycImpl 0)) acts

def tag (w : Option World) (x : InstId) : Nat :=
  match w with
  | none => 0
  | some w => match (w.st x).phase with
    | .parked d false _ => if d = A then 10 else if d = B then 11 else 1
    | .idle => 2 | .run _ => 3 | _ => 0

def parkClockDesc : Description :=
  { parkDesc with
    templates := parkDesc.templates ++ [tpl "clock" 1 ["idle"] "idle" true]
    edges := parkDesc.edges ++ [ing "clock" "Tick"]
    steps := parkDesc.steps ++ [{ template := "clock", fromState := "idle", toState := "idle", label := "Tick" }] }

def parkClockImpl : Impl where
  desc := parkClockDesc
  transitions := parkImpl.transitions ++ [tr "clock" "Tick" []]


def ph : Phase → String
  | .idle => "idle" | .run k => s!"run{k.rest.length}" | .parked d c _ => s!"parked({repr d},{c})"
  | .awaitReply _ _ => "await" | .awaitEffect _ => "eff" | .awaitPeer _ => "peer" | .crashed => "crash"
def show1 (I : Impl) (ids : List InstId) (w : Option World) : String :=
  match w with | none => "NONE" | some w => String.intercalate " | " (ids.map fun i => s!"{repr i}:{ph (w.st i).phase} box{(w.st i).box.length} park{(w.st i).parked.length} tok{(w.st i).tokens (tname i)} ty{(w.st i).typestate}")
#eval (List.range (cycActs.length+1)).map fun n => show1 cycImpl [A,B,C] (after (cycActs.take n))
#eval render parkClockDesc
#eval render cycDesc
