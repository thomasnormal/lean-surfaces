import Examples.«system-verilog».sem2.memory_shape_a_canonical_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.memory_shape_a_canonical_e

def emitPoint (w p : Int) : IO Unit := do
  match outputs w p with
  | .ok rows =>
      for (row, i) in rows.zipIdx do
        IO.println s!"ROW W={w} P={p} i={i} q={row.1} selected={row.2}"
  | .timeout => throw (IO.userError s!"E timed out at W={w}, P={p}")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := do
  emitPoint 4 3
  emitPoint 8 5
