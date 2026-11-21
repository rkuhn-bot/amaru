import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12s
open Deadlock Deadlock.Outlive
/-! Pool child C under core M births X. X mails pool siblings A and B, then
C terminates. M's tombstone stays queued while that mail sits in a live
queue. Once A and B have taken it, the handler births the next C. -/
def pool (name : String) (cap : Affine) (states : List String) (init : String) : Template :=
  let base := core name
  { base with multiplicity := .perPeer, slots := 1, supervisor := some "M", tombstone := ("dead/" ++ name), subtree := "pw", capacity := cap, states := states, initial := init, terminable := true }
def tA : Template := pool "A" { a := 4, b := 1 } ["idle", "sent"] "idle"
def tB : Template := pool "B" { a := 4, b := 1 } ["idle", "sent"] "idle"
def tC : Template := pool "C" { a := 2, b := 1 } ["idle", "up"] "idle"
def tXp : Template := { tX with subtree := "pw", supervisor := some "C", capacity := { a := 2, b := 1 } }
def tM : Template :=
  let base := core "M"
  { base with states := ["boot", "up"], initial := "boot", capacity := { a := 0, b := 4 }, priorityCapacity := { a := 0, b := 4 }, priorityBound := { a := 0, b := 4 } }
def ingE (t st l : String) (occ : Affine) : Edge := { go t st with label := l, occupancy := occ }
def st (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }
def sDesc : Description where
  name := "pool-subtree-outlive"
  freshNames := true
  templates := [tM, tA, tB, tC, tXp]
  edges := [ingE "M" "boot" "Go" { a := 0, b := 1 }, ingE "M" "up" "Go" { a := 0, b := 1 },
            ingE "A" "idle" "Ping" { a := 1, b := 0 }, ingE "A" "sent" "Ping" { a := 1, b := 0 },
            ingE "B" "idle" "Ping" { a := 1, b := 0 }, ingE "B" "sent" "Ping" { a := 1, b := 0 },
            ingE "C" "idle" "Go" { a := 1, b := 0 }, ingE "C" "up" "Go" { a := 1, b := 0 },
            ingE "X" "idle" "Go" { a := 1, b := 0 }, ingE "X" "sent" "Go" { a := 1, b := 0 },
            blk "A" "sent" "B" "P" .intra { a := 1, b := 0 }, blk "B" "sent" "A" "P" .intra { a := 1, b := 0 },
            blk "X" "sent" "A" "M" .intra { a := 1, b := 0 }, blk "X" "sent" "B" "M" .intra { a := 1, b := 0 }]
  compatibility := .all
  steps := [st "M" "boot" "Go" "up", st "M" "up" "Go" "up"] ++
    (["A", "B", "C"].flatMap fun c => [st "M" "boot" ("dead/" ++ c) "boot", st "M" "up" ("dead/" ++ c) "up"]) ++
    (["A", "B"].flatMap fun c => [st c "idle" "Ping" "sent", st c "sent" "Ping" "sent", st c "idle" "P" "idle",
       st c "sent" "P" "sent", st c "idle" "M" "idle", st c "sent" "M" "sent"]) ++
    [st "C" "idle" "Go" "up", st "C" "up" "Go" "up", st "C" "idle" "dead/X" "idle", st "C" "up" "dead/X" "up",
     st "X" "idle" "Go" "sent", st "X" "sent" "Go" "sent"]
def other (c : String) : String := if c == "A" then "B" else "A"
def sImpl : Impl where
  desc := sDesc
  transitions := [tr "M" "boot" "Go" "up" [.spawn "A", .spawn "B", .spawn "C"], tr "M" "up" "Go" "up" [],
      tr "M" "boot" "dead/A" "boot" [], tr "M" "boot" "dead/B" "boot" [], tr "M" "boot" "dead/C" "boot" [],
      tr "M" "up" "dead/A" "up" [], tr "M" "up" "dead/B" "up" [], tr "M" "up" "dead/C" "up" [.spawn "C"]] ++
    (["A", "B"].flatMap fun c => [tr c "idle" "Ping" "sent" [.send (other c) "P" 0], tr c "sent" "Ping" "sent" [],
       tr c "idle" "P" "idle" [], tr c "sent" "P" "sent" [], tr c "idle" "M" "idle" [], tr c "sent" "M" "sent" []]) ++
    [tr "C" "idle" "Go" "up" [.spawn "X"], tr "C" "up" "Go" "up" [.terminate],
     tr "C" "idle" "dead/X" "idle" [], tr "C" "up" "dead/X" "up" [],
     tr "X" "idle" "Go" "sent" [.send "A" "M" 0, .send "B" "M" 0], tr "X" "sent" "Go" "sent" []]
#eval (render sDesc, localIssues sImpl, l1 sDesc "A", l1 sDesc "B")

def run (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply sImpl a)) (some (initWorld sImpl N))
def Mc : InstId := .core "M"
def A0 : InstId := .peer "A" 0 0
def B0 : InstId := .peer "B" 0 0
def Cg (g : Nat) : InstId := .peer "C" 0 g
def Xg (g : Nat) : InstId := .peer "X" 0 g
def boot : List Action := [.ingress Mc "Go", .recvBulk Mc, .exec Mc, .exec Mc, .exec Mc, .ingress A0 "Ping", .ingress B0 "Ping"]
def churn (g : Nat) : List Action :=
  [.ingress (Cg g) "Go", .recvBulk (Cg g), .exec (Cg g),
   .ingress (Xg g) "Go", .recvBulk (Xg g), .exec (Xg g), .exec (Xg g),
   .ingress (Cg g) "Go", .recvBulk (Cg g), .exec (Cg g), .exec (Cg g),
   .recvPrio Mc, .exec Mc]
def last : List Action :=
  [.ingress (Cg 4) "Go", .recvBulk (Cg 4), .exec (Cg 4), .ingress (Xg 4) "Go", .recvBulk (Xg 4), .exec (Xg 4)]
def fin : List Action := [.recvBulk B0, .exec B0, .recvBulk A0, .exec (Xg 4), .exec A0]
def acts : List Action := boot ++ churn 0 ++ churn 1 ++ churn 2 ++ churn 3 ++ last ++ fin
def phS (p : Phase) : String :=
  match p with
  | .idle => "idle" | .run _ => "run" | .parked d _ _ => s!"parked→{tname d}" | .awaitReply _ _ => "await"
  | .awaitEffect _ => "eff" | .awaitPeer _ => "peer" | .crashed => "crashed"
def snap (w : World) :=
  (w.crashed, (w.st A0).box.length, phS (w.st A0).phase, (w.st B0).box.length, phS (w.st B0).phase,
   (w.st A0).parked.length, (w.st B0).parked.length, (List.range 5).map fun g => (w.st (Xg g)).life == .alive)
#eval (List.range (acts.length + 1)).filterMap fun n =>
  if n + 6 < acts.length then none else (run 1 (acts.take n)).map fun w => (n, snap w)
#eval (List.range (acts.length + 1)).find? fun n => (run 1 (acts.take n)).isNone
#eval (run 1 acts).map fun w =>
  (w.roster.filterMap fun id =>
    let as := [Action.recvBulk id, .recvPrio id, .exec id, .finish id, .callTimeout id]
    let en := as.filter fun a => (apply sImpl a w).isSome
    if en.isEmpty then none else some (toString (repr id).pretty, en.length),
   runtimeBusy sImpl w, (apply sImpl .stutter w).isSome, (w.st A0).box.map fun m => tname m.sender ++ "." ++ m.label)

def seal0 : List Action := boot ++
  [.ingress (Cg 0) "Go", .recvBulk (Cg 0), .exec (Cg 0),
   .ingress (Xg 0) "Go", .recvBulk (Xg 0), .exec (Xg 0), .exec (Xg 0),
   .ingress (Cg 0) "Go", .recvBulk (Cg 0), .exec (Cg 0), .exec (Cg 0)]
def drainX : List Action :=
  [.recvBulk A0, .exec A0, .recvBulk A0, .recvBulk B0, .exec B0, .recvBulk B0]

/-- While M sits on A and B, the core cannot receive C's tombstone and the
next generation is absent. Once both have taken M, the receive is enabled,
and the handler births C at generation 1. -/
theorem pool_sub_respawn_enabled :
    (match run 1 seal0 with
      | none => false
      | some w =>
        mailInFlight w (Cg 0) &&
          decide ((apply sImpl (.recvPrio Mc) w).isNone) &&
          ((w.st (Cg 0)).life == .dead) &&
          ((w.st (Cg 1)).life == .absent) &&
          (w.st A0).box.any (fun m => m.label == "M") &&
          (w.st B0).box.any (fun m => m.label == "M")) = true ∧
      (match run 1 (seal0 ++ drainX) with
        | none => false
        | some w =>
          !(mailInFlight w (Cg 0)) &&
            decide ((apply sImpl (.recvPrio Mc) w).isSome) &&
            ((w.st (Cg 1)).life == .absent)) = true ∧
      (match run 1 (seal0 ++ drainX ++ [.recvPrio Mc, .exec Mc]) with
        | none => false
        | some w =>
          !(mailInFlight w (Cg 0)) &&
            ((w.st (Cg 1)).life == .alive) &&
            decide (maxGen w "C" 0 = 2)) = true := by
  decide

end Deadlock.Helen12s
