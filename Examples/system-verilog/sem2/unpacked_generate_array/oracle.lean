import Examples.«system-verilog».sem2.unpacked_generate_array.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.unpacked_generate_array.agree

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println s!"ROW i={i} y={row}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError s!"E refusal: {msg}")
