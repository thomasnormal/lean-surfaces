import Examples.«system-verilog».sem2.parameterized_size_cast_canonical_e.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.parameterized_size_cast_canonical_e

def emit (w : Int) : IO Unit := do
  match outputs w with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println ("ROW W=" ++ toString w ++ " i=" ++ toString i ++ " y=" ++ row)
  | .timeout => throw (IO.userError "ordinary E timed out")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emit 2
  emit 12
