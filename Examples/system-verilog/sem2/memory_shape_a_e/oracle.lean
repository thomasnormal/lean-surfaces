import Examples.«system-verilog».sem2.memory_shape_a_e.agree
open LeanModels.Sv
open Examples.«system-verilog».sem2.memory_shape_a_e
def main : IO Unit := do
  for (args, tag) in [([4,3], "W=4,P=3"), ([8,5], "W=8,P=5")] do
    match outputs args with
    | .ok rows => for (row, i) in rows.zipIdx do IO.println s!"ROW {tag} i={i} q={row.1} selected={row.2}"
    | .error msg => throw (IO.userError msg)
