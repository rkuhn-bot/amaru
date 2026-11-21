import Deadlock.Outlive
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Deadlock.Helen12c
open Deadlock Deadlock.Outlive
/-! E4 inside one per-peer subtree, no core and no pool: root R births hosts
A, B and a terminable child X. X mails A and B, terminates, and R's `dead/X`
handler tries to re-spawn X. That mail sits on A and B, which are not sealed
with X, so the respawn is a no-op and the later schedule is refused. -/
def child (name : String) (cap : Affine) (states : List String) (term : Bool) : Template :=
  let base := core name
  { base with multiplicity := .perPeer, supervisor := some "R", tombstone := ("dead/" ++ name), subtree := "s", capacity := cap, states := states, initial := "idle", terminable := term }
def tA : Template := child "A" { a := 4, b := 1 } ["idle", "sent"] false
def tB : Template := child "B" { a := 4, b := 1 } ["idle", "sent"] false
def tXc : Template := child "X" { a := 2, b := 1 } ["idle", "sent"] true
def tRr : Template :=
  let base := core "R"
  { base with multiplicity := .perPeer, subtree := "s", states := ["boot", "up"], initial := "boot", capacity := { a := 2, b := 1 }, priorityCapacity := { a := 0, b := 4 }, priorityBound := { a := 0, b := 4 }, terminable := true }
def ingE (t st l : String) : Edge := { go t st with label := l, occupancy := { a := 1, b := 0 } }
def st (t f l to : String) : CompatStep := { template := t, fromState := f, toState := to, label := l }
def cDesc : Description where
  name := "child-subtree-outlive"
  freshNames := true
  templates := [tRr, tA, tB, tXc]
  edges := [ingE "R" "boot" "Go", ingE "R" "up" "Go",
            ingE "A" "idle" "Ping", ingE "A" "sent" "Ping", ingE "B" "idle" "Ping", ingE "B" "sent" "Ping",
            ingE "X" "idle" "Go", ingE "X" "sent" "Go",
            blk "A" "sent" "B" "P" .intra { a := 1, b := 0 }, blk "B" "sent" "A" "P" .intra { a := 1, b := 0 },
            blk "X" "sent" "A" "M" .intra { a := 1, b := 0 }, blk "X" "sent" "B" "M" .intra { a := 1, b := 0 }]
  compatibility := .all
  steps := [st "R" "boot" "Go" "up", st "R" "up" "Go" "up"] ++
    (["A", "B", "X"].flatMap fun c => [st "R" "boot" ("dead/" ++ c) "boot", st "R" "up" ("dead/" ++ c) "up"]) ++
    (["A", "B"].flatMap fun c => [st c "idle" "Ping" "sent", st c "sent" "Ping" "sent", st c "idle" "P" "idle",
       st c "sent" "P" "sent", st c "idle" "M" "idle", st c "sent" "M" "sent"]) ++
    [st "X" "idle" "Go" "sent", st "X" "sent" "Go" "sent"]
def other (c : String) : String := if c == "A" then "B" else "A"
def cImpl : Impl where
  desc := cDesc
  transitions := [tr "R" "boot" "Go" "up" [.spawn "A", .spawn "B", .spawn "X"], tr "R" "up" "Go" "up" [],
      tr "R" "boot" "dead/A" "boot" [], tr "R" "boot" "dead/B" "boot" [], tr "R" "boot" "dead/X" "boot" [],
      tr "R" "up" "dead/A" "up" [], tr "R" "up" "dead/B" "up" [], tr "R" "up" "dead/X" "up" [.spawn "X"]] ++
    (["A", "B"].flatMap fun c => [tr c "idle" "Ping" "sent" [.send (other c) "P" 0], tr c "sent" "Ping" "sent" [],
       tr c "idle" "P" "idle" [], tr c "sent" "P" "sent" [], tr c "idle" "M" "idle" [], tr c "sent" "M" "sent" []]) ++
    [tr "X" "idle" "Go" "sent" [.send "A" "M" 0, .send "B" "M" 0], tr "X" "sent" "Go" "sent" [.terminate]]
#eval (render cDesc, localIssues cImpl, l1 cDesc "A", l1 cDesc "B")
def run (N : Nat) (acts : List Action) : Option World :=
  acts.foldl (fun w a => w.bind (apply cImpl a)) (some (initWorld cImpl N))
def R0 : InstId := .peer "R" 0 0
def A0 : InstId := .peer "A" 0 0
def B0 : InstId := .peer "B" 0 0
def Xg (g : Nat) : InstId := .peer "X" 0 g
def boot : List Action := [.spawn "R", .ingress R0 "Go", .recvBulk R0, .exec R0, .exec R0, .exec R0,
  .ingress A0 "Ping", .ingress B0 "Ping"]
def churn (g : Nat) : List Action :=
  [.ingress (Xg g) "Go", .recvBulk (Xg g), .exec (Xg g), .exec (Xg g),
   .ingress (Xg g) "Go", .recvBulk (Xg g), .exec (Xg g), .exec (Xg g),
   .recvPrio R0, .exec R0]
def last : List Action := [.ingress (Xg 4) "Go", .recvBulk (Xg 4), .exec (Xg 4)]
def fin : List Action := [.recvBulk B0, .exec B0, .recvBulk A0, .exec (Xg 4), .exec A0]
def acts : List Action := boot ++ churn 0 ++ churn 1 ++ churn 2 ++ churn 3 ++ last ++ fin
def lifeTag (l : Life) : Nat := match l with | .absent => 0 | .alive => 1 | .shuttingDown => 2 | .dead => 3
def phS (p : Phase) : String :=
  match p with
  | .idle => "idle" | .run _ => "run" | .parked d _ _ => s!"parked→{tname d}" | .awaitReply _ _ => "await"
  | .awaitEffect _ => "eff" | .awaitPeer _ => "peer" | .crashed => "crashed"
def snap (w : World) :=
  (w.crashed, (w.st A0).box.length, phS (w.st A0).phase, (w.st B0).box.length, phS (w.st B0).phase,
   (w.st A0).parked.length, (w.st B0).parked.length, (List.range 5).map fun g => lifeTag (w.st (Xg g)).life)
#eval (List.range (acts.length + 1)).find? fun n => (run 1 (acts.take n)).isNone
#eval (List.range (acts.length + 1)).filterMap fun n =>
  if n + 6 < acts.length then none else (run 1 (acts.take n)).map fun w => (n, snap w)
#eval (run 1 acts).map fun w =>
  (w.roster.filterMap fun id =>
    let as := [Action.recvBulk id, .recvPrio id, .exec id, .finish id, .callTimeout id]
    let en := as.filter fun a => (apply cImpl a w).isSome
    if en.isEmpty then none else some (toString (repr id).pretty, en.length),
   runtimeBusy cImpl w, (apply cImpl .stutter w).isSome, (w.st A0).box.map fun m => toString (repr m.sender).pretty ++ ":" ++ m.label)

/-- After X's mail is on A and B, R's respawn does not birth the next
generation. The later schedule, which addresses that generation, is refused. -/
theorem child_sub_refused :
    (match run 1 (boot ++ churn 0) with
      | none => false
      | some w =>
        slotMailHeld cDesc w "X" 0 &&
          decide (maxGen w "X" 0 = 1) &&
          ((w.st (Xg 1)).life == .absent) &&
          (w.st A0).box.any (fun m => m.label == "M") &&
          (w.st B0).box.any (fun m => m.label == "M")) = true ∧
      run 1 (boot ++ churn 0 ++ [.ingress (Xg 1) "Go"]) = none ∧
      run 1 acts = none := by
  decide

end Deadlock.Helen12c
