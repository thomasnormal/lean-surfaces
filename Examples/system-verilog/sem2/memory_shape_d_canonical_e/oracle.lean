import Examples.«system-verilog».sem2.memory_shape_d_canonical_e.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.memory_shape_d_canonical_e

def emitPoint (w : Int) : IO Unit := do
  match outputs w with
  | .ok rows => for (row, i) in rows.zipIdx do
      IO.println s!"ROW W={w} i={i} q={row.1} selected={row.2}"
  | .timeout => throw (IO.userError s!"E timed out at W={w}")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emitPoint 4
  emitPoint 8
