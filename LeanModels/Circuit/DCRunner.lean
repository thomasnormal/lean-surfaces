import LeanModels.Circuit.Spice

open LeanModels.Circuit

private def printRat (name : String) (value : Rat) : IO Unit :=
  IO.println s!"{name}\t{value.num}\t{value.den}"

/-- Command-line bridge used only by differential harnesses. The parser and
exact solver are the same definitions used by `load_circuit`. -/
def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [] =>
      IO.eprintln "usage: DCRunner <deck.cir> <node>..."
      return 2
  | path :: probes =>
      let contents ← IO.FS.readFile path
      let circuit ← match Spice.parseAndElaborate contents with
        | .ok circuit => pure circuit
        | .error error =>
            IO.eprintln s!"frontend error: {error}"
            return 1
      let dc ← match circuit.toDCCircuit with
        | .ok dc => pure dc
        | .error error =>
            IO.eprintln s!"exact DC view error: {repr error}"
            return 1
      let solution ← match solveDC dc with
        | .ok solution => pure solution
        | .error error =>
            IO.eprintln s!"solve error: {repr error}"
            return 1
      for probe in probes do
        if probe.startsWith "@" then
          let name := (probe.drop 1).toString
          match circuit.device? name with
          | some device =>
              printRat probe (solution.assignment.current device)
          | none =>
              IO.eprintln s!"unknown device: {name}"
              return 1
        else
          match circuit.node? probe with
          | some node =>
              printRat probe (solution.assignment.voltage node)
          | none =>
              IO.eprintln s!"unknown node: {probe}"
              return 1
      return 0
