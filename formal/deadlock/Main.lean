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
  | [graph, tracePath] =>
    let graphText ← IO.FS.readFile graph
    let traceText ← IO.FS.readFile tracePath
    match Deadlock.parseWiring graphText with
    | .error e =>
      IO.eprintln e
      return 2
    | .ok w =>
      match Deadlock.parseTrace traceText with
      | .error e =>
        IO.eprintln e
        return 2
      | .ok trace =>
        match Deadlock.replayTrace (Deadlock.wiringImpl w) trace with
        | .ok () =>
          IO.println "pass"
          return 0
        | .error e =>
          IO.eprintln e
          return 1
  | _ =>
    IO.eprintln "usage: check graph.json [trace.json]"
    return 2
