import Examples.«system-verilog».sem2.memory_shape_d_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.memory_shape_d_e

def main : IO Unit := do
  match outputs with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println s!"ROW i={i} q={row.1} selected={row.2}"
  | .error msg => throw (IO.userError msg)
