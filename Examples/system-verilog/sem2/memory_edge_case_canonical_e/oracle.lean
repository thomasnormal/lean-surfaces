import Examples.«system-verilog».sem2.memory_edge_case_canonical_e.agree

open Examples.«system-verilog».sem2.memory_edge_case_canonical_e

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for ((q0, q1, hit), i) in rows.zipIdx do
        IO.println s!"ROW i={i} q0={q0} q1={q1} hit={hit}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
