import Deadlock.Json

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Deadlock.parseDescription text with
    | .error e =>
      IO.eprintln e
      return 2
    | .ok d =>
      let report := Deadlock.render d
      IO.println report
      return if report == "pass" then 0 else 1
  | _ =>
    IO.eprintln "usage: check graph.json"
    return 2
