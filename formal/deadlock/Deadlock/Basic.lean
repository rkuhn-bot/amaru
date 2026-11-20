/-
Finite descriptions of actor-network wait graphs.

Affine forms `a * N + b` are the occupancy and capacity language. `N` is the
number of instances of every per-peer template. A comparison of coefficients is
exactly the comparison of the evaluated forms for every `N`.
-/

namespace Deadlock

/-- `a * N + b`. -/
structure Affine where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Affine

def zero : Affine := { a := 0, b := 0 }

def ofNat (n : Nat) : Affine := { a := 0, b := n }

def eval (x : Affine) (n : Nat) : Nat := x.a * n + x.b

def add (x y : Affine) : Affine := { a := x.a + y.a, b := x.b + y.b }

def leB (x y : Affine) : Bool := x.a ≤ y.a && x.b ≤ y.b

def toString (x : Affine) : String := s!"{x.a}*N+{x.b}"

theorem leB_iff (x y : Affine) : leB x y = true ↔ x.a ≤ y.a ∧ x.b ≤ y.b := by
  simp only [leB, Bool.and_eq_true, decide_eq_true_eq]

theorem eval_le_of_coeff (x y : Affine) (ha : x.a ≤ y.a) (hb : x.b ≤ y.b) (n : Nat) :
    x.eval n ≤ y.eval n := by
  unfold eval
  exact Nat.add_le_add (Nat.mul_le_mul_right n ha) hb

theorem eval_le_of_leB (x y : Affine) (h : leB x y = true) (n : Nat) :
    x.eval n ≤ y.eval n := by
  have hc := (leB_iff x y).mp h
  exact eval_le_of_coeff x y hc.1 hc.2 n

theorem coeff_of_eval_le (x y : Affine) (h : ∀ n, x.eval n ≤ y.eval n) :
    x.a ≤ y.a ∧ x.b ≤ y.b := by
  have hb : x.b ≤ y.b := by
    have := h 0
    simp only [eval, Nat.mul_zero, Nat.zero_add] at this
    exact this
  refine ⟨?_, hb⟩
  apply Nat.le_of_not_gt
  intro hgt
  have ha : y.a + 1 ≤ x.a := Nat.succ_le_of_lt hgt
  let n : Nat := y.b + x.b + 1
  have hn := h n
  unfold eval at hn
  have hmul : (y.a + 1) * n ≤ x.a * n := Nat.mul_le_mul_right n ha
  have expand : (y.a + 1) * n = y.a * n + n := Nat.succ_mul y.a n
  rw [expand] at hmul
  have hsum : y.a * n + n + x.b ≤ y.a * n + y.b :=
    Nat.le_trans (Nat.add_le_add_right hmul x.b) hn
  have hsum' : y.a * n + (n + x.b) ≤ y.a * n + y.b := by
    simpa [Nat.add_assoc] using hsum
  have htail : n + x.b ≤ y.b := Nat.le_of_add_le_add_left hsum'
  have eq : n + x.b = y.b + (x.b + 1 + x.b) := by
    simp only [n, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hpos : 0 < x.b + 1 + x.b := by omega
  have hlt : y.b < y.b + (x.b + 1 + x.b) := Nat.lt_add_of_pos_right hpos
  have hlt' : y.b < n + x.b := by simpa [eq] using hlt
  exact Nat.not_le_of_gt hlt' htail

theorem leB_iff_forall_eval (x y : Affine) :
    leB x y = true ↔ ∀ n, x.eval n ≤ y.eval n := by
  constructor
  · intro h n
    exact eval_le_of_leB x y h n
  · intro h
    exact (leB_iff x y).mpr (coeff_of_eval_le x y h)

end Affine

inductive Multiplicity where
  | one
  | perPeer
  deriving DecidableEq, Repr, Inhabited, BEq

inductive EdgeKind where
  | blocking
  | nonBlocking
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Reliability where
  | reliable
  | superseding
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Effect classes that appear on a described edge. -/
inductive EffectKind where
  | send
  | trySend
  | call
  | reply
  | selfSchedule
  | cell
  | internal
  | peer
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Scope where
  | intra
  | cross
  | coreInst
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Lemma 2 side conditions (i)–(v), plus the dirty-bit coalesced wake. -/
structure CellFlags where
  singleWriter : Bool
  orderMonotone : Bool
  noPerMessageObligation : Bool
  visibility : Bool
  readPoints : Bool
  idempotent : Bool
  dirtyBit : Bool
  deriving DecidableEq, Repr, Inhabited, BEq

namespace CellFlags

def ok (c : CellFlags) : Bool :=
  c.singleWriter && c.orderMonotone && c.noPerMessageObligation &&
    c.visibility && c.readPoints && c.idempotent && c.dirtyBit

def none : CellFlags := default

end CellFlags

structure Template where
  name : String
  multiplicity : Multiplicity
  capacity : Affine
  priorityCapacity : Affine
  priorityBound : Affine
  states : List String
  initial : String
  terminable : Bool
  untimedPeer : Bool
  /-- When true, this mailbox must satisfy occupancy ≤ capacity (credit). When false, a
  violated bound does not by itself fail the check: blocking sends stay residual and
  must be ordered by the state graph. Default in the JSON schema is true. -/
  mustFit : Bool
  /-- Roles that share a nonempty name die together. Empty means a lone actor. -/
  subtree : String := ""
  /-- An `awaitPeer` on this role is the timeout that kills `subtree`. -/
  timeoutKills : Bool := false
  /-- Permanent core that receives the one tombstone when `subtree` is killed.
  A per-peer template may name another member of its own subtree. -/
  supervisor : String := ""
  /-- Label the supervisor handles when this child terminates. One label per
  child template, chosen when the parent is wired. Empty means no tombstone. -/
  tombstone : String := ""
  deriving DecidableEq, Repr, Inhabited, BEq

structure Edge where
  src : String
  srcState : String
  dst : String
  kind : EdgeKind
  reliability : Reliability
  effect : EffectKind
  label : String
  scope : Scope
  occupancy : Affine
  repliesInDequeue : Bool
  ingress : Bool
  ingressLegal : Option Affine
  cell : CellFlags
  deriving DecidableEq, Repr, Inhabited, BEq

/-- One quadruple of the legacy pairwise relation: while `src` is blocked in `srcState`,
`dst` is allowed to be in `dstState`. New descriptions use `CompatGroup` instead. -/
structure Allowed where
  src : String
  srcState : String
  dst : String
  dstState : String
  deriving DecidableEq, Repr, Inhabited, BEq

/-- One coordinate of an allowed tuple: the role is a template name. -/
structure RoleState where
  role : String
  state : String
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A group of interacting templates and the tuples that may co-occur.
`roles` has length at least 2. Each list in `allowed` assigns every role a state.
The list is untrusted; `compatFails` checks that it is an inductive invariant. -/
structure CompatGroup where
  name : String
  roles : List String
  allowed : List (List RoleState)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A cell write a program performs: template `src` in `srcState` writes label
`label` of template `dst`. It is legal only as a declared cell edge. -/
structure CellEffect where
  src : String
  srcState : String
  dst : String
  label : String
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A typestate step the relation must be closed under. Program transitions are
listed by the exporter. Restart and terminate are added by the checker. -/
structure CompatStep where
  template : String
  fromState : String
  toState : String
  label : String
  deriving DecidableEq, Repr, Inhabited, BEq

inductive CompatMode where
  | all
  | explicit (pairs : List Allowed)
  | groups (gs : List CompatGroup)
  deriving DecidableEq, Repr, Inhabited, BEq

structure Description where
  name : String
  freshNames : Bool
  templates : List Template
  edges : List Edge
  compatibility : CompatMode
  /-- Typestate steps the compatibility check closes under. Empty for `all`
  and for the legacy pairwise format. -/
  steps : List CompatStep
  /-- Cell writes named by the exporter. Each must be a declared cell edge.
  Empty when the graph does not list programs. -/
  cellEffects : List CellEffect := []
  deriving DecidableEq, Repr, Inhabited, BEq

structure Node where
  template : String
  state : String
  deriving DecidableEq, Repr, Inhabited, BEq

def alistGet {α β} [DecidableEq α] (xs : List (α × β)) (a : α) : Option β :=
  xs.findSome? fun p => if p.1 = a then some p.2 else none

def dedup {α} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.elem x then acc else acc ++ [x]) []

def enum {α} (xs : List α) : List (Nat × α) :=
  (List.range xs.length).zip xs

def templateOf (D : Description) (name : String) : Option Template :=
  D.templates.findSome? fun t => if t.name == name then some t else none

def statesOf (D : Description) (name : String) : List String :=
  match templateOf D name with
  | some t => t.states
  | none => []

def totalOcc (D : Description) (dst : String) : Affine :=
  D.edges.foldl (fun acc e => if e.dst == dst then acc.add e.occupancy else acc) Affine.zero

def occExcept (D : Description) (dst : String) (idx : Nat) : Affine :=
  (enum D.edges).foldl (fun acc (i, e) =>
    if e.dst == dst && i != idx then acc.add e.occupancy else acc) Affine.zero

/-- Lemma 1: every producer bound into `dst`, summed, fits in the concrete capacity for every `N`. -/
def l1 (D : Description) (dst : String) : Bool :=
  match templateOf D dst with
  | none => false
  | some t => Affine.leB (totalOcc D dst) t.capacity

def hasTemplate (D : Description) (name : String) : Bool :=
  D.templates.any fun t => t.name == name

def stateMem (D : Description) (name state : String) : Bool :=
  (statesOf D name).elem state

end Deadlock
