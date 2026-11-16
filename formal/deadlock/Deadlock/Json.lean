import Deadlock.Graph

set_option autoImplicit false

namespace Deadlock

inductive JVal where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List JVal)
  | obj (fs : List (String × JVal))
  deriving Repr

def jget (v : JVal) (k : String) : Option JVal :=
  match v with
  | .obj fs => fs.findSome? fun p => if p.1 == k then some p.2 else none
  | _ => none

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

private def ofChars (cs : List Char) : String :=
  cs.foldl (fun s c => s.push c) ""

private def parseNat : List Char → Option (Nat × List Char)
  | c :: cs =>
    if c.isDigit then
      let rec go (acc : Nat) : List Char → Nat × List Char
        | d :: ds =>
          if d.isDigit then go (acc * 10 + (d.toNat - '0'.toNat)) ds
          else (acc, d :: ds)
        | [] => (acc, [])
      some (go (c.toNat - '0'.toNat) cs)
    else
      none
  | [] => none

private def parseString : List Char → Except String (String × List Char)
  | [] => .error "unterminated string"
  | '\\' :: 'n' :: rest => do
    let (s, rest) ← parseString rest
    return (ofChars ['\n'] ++ s, rest)
  | '\\' :: '"' :: rest => do
    let (s, rest) ← parseString rest
    return ("\"" ++ s, rest)
  | '\\' :: '\\' :: rest => do
    let (s, rest) ← parseString rest
    return ("\\" ++ s, rest)
  | '\\' :: '/' :: rest => do
    let (s, rest) ← parseString rest
    return ("/" ++ s, rest)
  | '\\' :: _ :: _ => .error "unsupported string escape"
  | '"' :: rest => .ok ("", rest)
  | c :: rest => do
    let (s, rest) ← parseString rest
    return (ofChars [c] ++ s, rest)

/-- Fuel decreases on every nested value, so the parser is total. -/
private partial def parseValue (fuel : Nat) (cs : List Char) : Except String (JVal × List Char) :=
  if fuel = 0 then .error "json exceeded size bound"
  else
    match skipWs cs with
    | [] => .error "expected json value"
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
    | '"' :: rest => do
      let (s, rest) ← parseString rest
      return (.str s, rest)
    | '[' :: rest => parseArr (fuel - 1) rest []
    | '{' :: rest => parseObj (fuel - 1) rest []
    | c :: rest =>
      if c.isDigit then
        match parseNat (c :: rest) with
        | some (n, rest) => .ok (.num n, rest)
        | none => .error "expected number"
      else
        .error s!"unexpected character {c}"
where
  parseArr (fuel : Nat) (cs : List Char) (acc : List JVal) : Except String (JVal × List Char) :=
    if fuel = 0 then .error "json exceeded size bound"
    else
      match skipWs cs with
      | [] => .error "unterminated array"
      | ']' :: rest => .ok (.arr acc.reverse, rest)
      | ',' :: rest =>
        if acc.isEmpty then .error "leading comma in array" else parseArr (fuel - 1) rest acc
      | _ => do
        let (v, rest) ← parseValue (fuel - 1) cs
        match skipWs rest with
        | ',' :: rest => parseArr (fuel - 1) rest (v :: acc)
        | ']' :: rest => .ok (.arr (v :: acc).reverse, rest)
        | _ => .error "expected ',' or ']' in array"
  parseObj (fuel : Nat) (cs : List Char) (acc : List (String × JVal)) :
      Except String (JVal × List Char) :=
    if fuel = 0 then .error "json exceeded size bound"
    else
      match skipWs cs with
      | [] => .error "unterminated object"
      | '}' :: rest => .ok (.obj acc.reverse, rest)
      | ',' :: rest =>
        if acc.isEmpty then .error "leading comma in object" else parseObj (fuel - 1) rest acc
      | '"' :: rest => do
        let (key, rest) ← parseString rest
        match skipWs rest with
        | ':' :: rest =>
          let (v, rest) ← parseValue (fuel - 1) rest
          match skipWs rest with
          | ',' :: rest => parseObj (fuel - 1) rest ((key, v) :: acc)
          | '}' :: rest => .ok (.obj ((key, v) :: acc).reverse, rest)
          | _ => .error "expected ',' or '}' in object"
        | _ => .error "expected ':' after object key"
      | c :: _ => .error s!"expected string key, found {c}"

def parseJson (s : String) : Except String JVal := do
  let (v, rest) ← parseValue (s.length + 1) s.toList
  if (skipWs rest).isEmpty then return v else throw "trailing json input"

private def field (v : JVal) (k : String) : Except String JVal :=
  match jget v k with
  | some x => .ok x
  | none => .error s!"missing field {k}"

private def asString (v : JVal) (what : String) : Except String String :=
  match v with
  | .str s => .ok s
  | _ => .error s!"{what} must be a string"

private def asBool (v : JVal) (what : String) : Except String Bool :=
  match v with
  | .bool b => .ok b
  | _ => .error s!"{what} must be a boolean"

private def asArr (v : JVal) (what : String) : Except String (List JVal) :=
  match v with
  | .arr xs => .ok xs
  | _ => .error s!"{what} must be an array"

private def decodeAffine (v : JVal) : Except String Affine :=
  match v with
  | .num n => .ok (.ofNat n)
  | .obj _ => do
    let a ← match jget v "a" with
      | some (.num n) => pure n
      | _ => throw "affine.a must be a number"
    let b ← match jget v "b" with
      | some (.num n) => pure n
      | _ => throw "affine.b must be a number"
    return { a := a, b := b }
  | _ => .error "capacity, bound, and occupancy must be a number or {\"a\", \"b\"}"

private def decodeMult (s : String) : Except String Multiplicity :=
  match s with
  | "one" => .ok .one
  | "perPeer" => .ok .perPeer
  | _ => .error s!"unknown multiplicity {s}"

private def decodeKind (s : String) : Except String EdgeKind :=
  match s with
  | "blocking" => .ok .blocking
  | "nonBlocking" => .ok .nonBlocking
  | _ => .error s!"unknown edge kind {s}"

private def decodeRel (s : String) : Except String Reliability :=
  match s with
  | "reliable" => .ok .reliable
  | "superseding" => .ok .superseding
  | _ => .error s!"unknown reliability {s}"

private def decodeEffect (s : String) : Except String EffectKind :=
  match s with
  | "send" => .ok .send
  | "trySend" => .ok .trySend
  | "call" => .ok .call
  | "reply" => .ok .reply
  | "selfSchedule" => .ok .selfSchedule
  | "cell" => .ok .cell
  | "internal" => .ok .internal
  | "peer" => .ok .peer
  | _ => .error s!"unknown effect {s}"

private def decodeScope (s : String) : Except String Scope :=
  match s with
  | "intra" => .ok .intra
  | "cross" => .ok .cross
  | "coreInst" => .ok .coreInst
  | _ => .error s!"unknown scope {s}"

private def decodeBoolField (v : JVal) (k : String) (default : Bool) : Except String Bool :=
  match jget v k with
  | none => .ok default
  | some x => asBool x k

private def decodeCell (v : JVal) : Except String CellFlags := do
  match jget v "cell" with
  | none => return .none
  | some c =>
    return {
      singleWriter := ← decodeBoolField c "singleWriter" false
      orderMonotone := ← decodeBoolField c "orderMonotone" false
      noPerMessageObligation := ← decodeBoolField c "noPerMessageObligation" false
      visibility := ← decodeBoolField c "visibility" false
      readPoints := ← decodeBoolField c "readPoints" false
      idempotent := ← decodeBoolField c "idempotent" false
      dirtyBit := ← decodeBoolField c "dirtyBit" false
    }

private def decodeTemplate (v : JVal) : Except String Template := do
  let name ← asString (← field v "name") "template.name"
  let mult ← decodeMult (← asString (← field v "multiplicity") "multiplicity")
  let capacity ← decodeAffine (← field v "capacity")
  let priorityCapacity ← decodeAffine (← field v "priorityCapacity")
  let priorityBound ← decodeAffine (← field v "priorityBound")
  let states ← (← asArr (← field v "states") "states").mapM fun s => asString s "state"
  let initial ← asString (← field v "initial") "initial"
  let terminable ← decodeBoolField v "terminable" false
  let untimedPeer ← decodeBoolField v "untimedPeer" false
  let mustFit ← decodeBoolField v "mustFit" true
  return {
    name, multiplicity := mult, capacity, priorityCapacity, priorityBound, states, initial,
    terminable, untimedPeer, mustFit
  }

private def decodeEdge (v : JVal) : Except String Edge := do
  let src ← asString (← field v "src") "src"
  let srcState ← asString (← field v "srcState") "srcState"
  let dst ← asString (← field v "dst") "dst"
  let kind ← decodeKind (← asString (← field v "kind") "kind")
  let reliability ← decodeRel (← asString (← field v "reliability") "reliability")
  let effect ← decodeEffect (← asString (← field v "effect") "effect")
  let label ← asString (← field v "label") "label"
  let scope ← decodeScope (← asString (← field v "scope") "scope")
  let occupancy ← decodeAffine (← field v "occupancy")
  let repliesInDequeue ← decodeBoolField v "repliesInDequeue" false
  let ingress ← decodeBoolField v "ingress" false
  let ingressLegal ← match jget v "ingressLegal" with
    | none => pure none
    | some .null => pure none
    | some x => do
      let a ← decodeAffine x
      pure (some a)
  let cell ← decodeCell v
  return {
    src, srcState, dst, kind, reliability, effect, label, scope, occupancy,
    repliesInDequeue, ingress, ingressLegal, cell
  }

private def decodeAllowed (v : JVal) : Except String Allowed := do
  return {
    src := ← asString (← field v "src") "allowed.src"
    srcState := ← asString (← field v "srcState") "allowed.srcState"
    dst := ← asString (← field v "dst") "allowed.dst"
    dstState := ← asString (← field v "dstState") "allowed.dstState"
  }

private def decodeRoleState (v : JVal) : Except String RoleState := do
  return {
    role := ← asString (← field v "role") "role"
    state := ← asString (← field v "state") "state"
  }

private def decodeGroup (v : JVal) : Except String CompatGroup := do
  let name ← asString (← field v "name") "group.name"
  let roles ← (← asArr (← field v "roles") "roles").mapM fun s => asString s "role"
  let raw ← asArr (← field v "allowed") "allowed"
  let allowed ← raw.mapM fun tup => do
    let xs ← asArr tup "tuple"
    xs.mapM decodeRoleState
  return { name, roles, allowed }

private def decodeGroups (v : JVal) : Except String CompatMode := do
  let groups ← (← asArr (← field v "groups") "groups").mapM decodeGroup
  return .groups groups

private def decodeCellEffect (v : JVal) : Except String CellEffect := do
  return {
    src := ← asString (← field v "src") "cellEffect.src"
    srcState := ← asString (← field v "srcState") "cellEffect.srcState"
    dst := ← asString (← field v "dst") "cellEffect.dst"
    label := ← asString (← field v "label") "cellEffect.label"
  }

private def decodeStep (v : JVal) : Except String CompatStep := do
  return {
    template := ← asString (← field v "template") "transition.template"
    fromState := ← asString (← field v "from") "transition.from"
    toState := ← asString (← field v "to") "transition.to"
    label := ← asString (← field v "label") "transition.label"
  }

def decodeDescription (v : JVal) : Except String Description := do
  match jget v "schema" with
  | some (.str "amaru-deadlock-graph/v1") => pure ()
  | _ => throw "schema must be \"amaru-deadlock-graph/v1\""
  let name ← asString (← field v "name") "name"
  let freshNames ← asBool (← field v "freshNames") "freshNames"
  let templates ← (← asArr (← field v "templates") "templates").mapM decodeTemplate
  let edges ← (← asArr (← field v "edges") "edges").mapM decodeEdge
  let compatibility ← match jget v "compatibility" with
    | none => pure CompatMode.all
    | some (.str "all") => pure CompatMode.all
    | some (.str "explicit") => do
      let pairs ← (← asArr (← field v "allowed") "allowed").mapM decodeAllowed
      pure (.explicit pairs)
    | some (.obj fs) => decodeGroups (.obj fs)
    | _ => throw "compatibility must be \"all\", \"explicit\", or {\"groups\": ...}"
  let steps ← match jget v "transitions" with
    | none => pure []
    | some xs => (← asArr xs "transitions").mapM decodeStep
  let cellEffects ← match jget v "cellEffects" with
    | none => pure []
    | some xs => (← asArr xs "cellEffects").mapM decodeCellEffect
  return { name, freshNames, templates, edges, compatibility, steps, cellEffects }

def parseDescription (s : String) : Except String Description := do
  decodeDescription (← parseJson s)

end Deadlock
