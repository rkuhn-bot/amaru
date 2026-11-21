import Deadlock.Semantics
import Deadlock.Local
import Deadlock.Graph
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Deadlock.Helen10d
open Deadlock

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
def ing (t st : String) : Edge :=
  { (sendEdge t st t "Go" 1) with effect := .trySend, kind := .nonBlocking, reliability := .reliable, ingress := true, occupancy := { a := 1, b := 0 }, ingressLegal := some (Affine.ofNat 1) }
def step (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }

/-- Branch R8c mailDesc, unchanged. -/
def ingL (t st l : String) : Edge := { ing t st with label := l }
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
/-! ## E4: dead-key mail fills two cores that send to each other. -/
def coreT (n : String) : Template := { tpl n 4 ["idle", "sent"] "idle" true with capacity := { a := 1, b := 3 } }
def dR : Template := { tpl "R" 4 ["boot", "up"] "boot" true with
  multiplicity := .perPeer, subtree := "S", terminable := true, capacity := { a := 4, b := 4 } }
def dX : Template := { tpl "X" 4 ["idle", "sent"] "idle" true with
  multiplicity := .perPeer, subtree := "S", supervisor := some "R", tombstone := "dead/X", capacity := { a := 4, b := 4 } }
def snd (s ss d l : String) (a b : Nat) : Edge := { (sendEdge s ss d l 0) with occupancy := { a := a, b := b } }
def labelsH : List String := ["Ping", "P", "M"]
def dDesc : Description where
  name := "dead-key-deadlock"
  freshNames := true
  templates := [coreT "H", coreT "K", dR, dX]
  edges := [ingL "R" "boot" "Go", ingL "R" "up" "Go", ingL "R" "boot" "Kill", ingL "R" "up" "Kill",
            ingL "X" "idle" "Go", ingL "X" "sent" "Go",
            { ingL "H" "idle" "Ping" with occupancy := { a := 0, b := 1 } },
            { ingL "K" "idle" "Ping" with occupancy := { a := 0, b := 1 } },
            { ingL "H" "sent" "Ping" with occupancy := { a := 0, b := 1 } },
            { ingL "K" "sent" "Ping" with occupancy := { a := 0, b := 1 } },
            snd "H" "sent" "K" "P" 0 1, snd "K" "sent" "H" "P" 0 1,
            snd "X" "sent" "K" "M" 1 0, snd "X" "sent" "H" "M" 1 0]
  compatibility := .all
  steps := [step "R" "boot" "dead/X" "boot", step "R" "up" "dead/X" "up", step "R" "boot" "Go" "up", step "R" "up" "Go" "up", step "R" "boot" "Kill" "boot", step "R" "up" "Kill" "up",
            step "X" "idle" "Go" "sent", step "X" "sent" "Go" "sent"] ++
           (["H", "K"].flatMap fun c => [step c "idle" "Ping" "sent", step c "sent" "Ping" "sent",
              step c "idle" "P" "idle", step c "sent" "P" "sent", step c "idle" "M" "idle", step c "sent" "M" "sent"])
def other (c : String) : String := if c == "H" then "K" else "H"
def dImpl : Impl where
  desc := dDesc
  transitions := [tr "R" "boot" "dead/X" "boot" [], tr "R" "up" "dead/X" "up" [], tr "R" "boot" "Go" "up" [.spawn "X"], tr "R" "up" "Go" "up" [],
                  tr "R" "boot" "Kill" "boot" [], tr "R" "up" "Kill" "up" [.terminate],
                  tr "X" "idle" "Go" "sent" [.send "K" "M" 0, .send "H" "M" 0], tr "X" "sent" "Go" "sent" []] ++
    (["H", "K"].flatMap fun c => [tr c "idle" "Ping" "sent" [.send (other c) "P" 0], tr c "sent" "Ping" "sent" [],
       tr c "idle" "P" "idle" [], tr c "sent" "P" "sent" [], tr c "idle" "M" "idle" [], tr c "sent" "M" "sent" []])

#eval render dDesc
#eval localIssues dImpl
#eval (l1 dDesc "H", l1 dDesc "K", capBulk dDesc 2 (.core "H"))

def Rk (k : Nat) : InstId := .peer "R" k 0
def Xk (k : Nat) : InstId := .peer "X" k 0
def Hc : InstId := .core "H"
def Kc : InstId := .core "K"
def gen (k : Nat) : List Action :=
  [.spawn "R", .ingress (Rk k) "Go", .recvBulk (Rk k), .exec (Rk k), .ingress (Xk k) "Go", .recvBulk (Xk k),
   .exec (Xk k), .exec (Xk k), .ingress (Rk k) "Kill", .recvBulk (Rk k), .exec (Rk k), .exec (Rk k)]
def lastGen : List Action :=
  [.spawn "R", .ingress (Rk 4) "Go", .recvBulk (Rk 4), .exec (Rk 4), .ingress (Xk 4) "Go", .recvBulk (Xk 4), .exec (Xk 4)]
def dActs : List Action :=
  [.ingress Hc "Ping", .ingress Kc "Ping"] ++ gen 0 ++ gen 1 ++ gen 2 ++ gen 3 ++ lastGen ++
  [.recvBulk Hc, .exec Hc, .recvBulk Kc, .exec (Xk 4), .exec Kc]
def phS (p : Phase) : String :=
  match p with
  | .idle => "idle" | .run _ => "run" | .parked d _ _ => s!"parked→{tname d}" | .awaitReply _ _ => "await"
  | .awaitEffect _ => "eff" | .awaitPeer _ => "peer" | .crashed => "crashed"
def dSnap (w : World) :=
  (w.crashed, (w.st Hc).box.length, phS (w.st Hc).phase, (w.st Kc).box.length, phS (w.st Kc).phase,
   (w.st Hc).parked.length, (w.st Kc).parked.length,
   ((w.st Hc).box.map fun m => tname m.sender ++ "@" ++ toString (memberKey m.sender) ++ ":" ++ m.label),
   (List.range 5).map fun k => (w.st (Xk k)).life == .alive)
#eval (List.range (dActs.length + 1)).filterMap fun n =>
  if n + 7 < dActs.length then none else (runAt dImpl 2 (dActs.take n)).map fun w => (n, dSnap w)
-- Every action the runtime could take on the final world.
#eval (runAt dImpl 2 dActs).map fun w =>
  (w.roster.filterMap fun id =>
    let acts := [Action.recvBulk id, .recvPrio id, .exec id, .finish id, .callTimeout id]
    let en := acts.filter fun a => (apply dImpl a w).isSome
    if en.isEmpty then none else some (toString (repr id).pretty, en.length),
   runtimeBusy dImpl w, (apply dImpl .stutter w).isSome)
end Deadlock.Helen10d
