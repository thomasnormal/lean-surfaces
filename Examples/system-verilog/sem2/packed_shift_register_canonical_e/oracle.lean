import Examples.«system-verilog».sem2.packed_shift_register_canonical_e.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.packed_shift_register_canonical_e

def emit (n : Int) : IO Unit := do
  match outputs n with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println ("ROW N=" ++ toString n ++ " i=" ++ toString i ++ " q=" ++ row)
  | .timeout => throw (IO.userError "ordinary E timed out")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emit 4
  emit 8
