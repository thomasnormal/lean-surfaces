import LeanModels.Spice.Json
import LeanModels.Spice.Semantics
import LeanModels.Spice.Solve

open LeanModels.Spice

private def printRat (name : String) (value : Rat) : IO Unit :=
  IO.println s!"{name}\t{value.num}\t{value.den}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: Runner <netlist.json> <node|@branch>..."
      pure 2
  | path :: probes =>
      let text ← IO.FS.readFile path
      match loadNetlistString text with
      | .error error =>
          IO.eprintln s!"ingest error: {error}"
          pure 1
      | .ok netlist =>
          match flatten netlist with
          | .error error =>
              IO.eprintln s!"flatten error: {repr error}"
              pure 1
          | .ok flat =>
              match solve flat with
              | .error error =>
                  IO.eprintln s!"solve error: {error.describe}"
                  pure 1
              | .ok assignment =>
                  for probe in probes do
                    if probe.startsWith "@" then
                      printRat probe (assignment.cur (probe.drop 1).toString)
                    else
                      printRat probe (assignment.volt probe)
                  pure 0
