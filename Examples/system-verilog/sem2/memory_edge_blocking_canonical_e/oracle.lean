import Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e.agree

open Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for ((mem0, mem1, delayed, marker), i) in rows.zipIdx do
        IO.println s!"ROW i={i} mem0={mem0} mem1={mem1} delayed={delayed} marker={marker}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
