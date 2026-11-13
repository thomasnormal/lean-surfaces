import Examples.«system-verilog».sem2.generate_memory_canonical_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.generate_memory_canonical_e

def emit (w n : Int) : IO Unit := do
  match outputs w n with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println s!"ROW W={w} N={n} i={i} q={row}"
  | .timeout => throw (IO.userError s!"E timed out at W={w}, N={n}")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emit 4 2
  emit 4 1
