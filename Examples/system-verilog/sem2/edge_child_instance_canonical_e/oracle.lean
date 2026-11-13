import Examples.«system-verilog».sem2.edge_child_instance_canonical_e.agree
open LeanModels.Sv
open Examples.«system-verilog».sem2.edge_child_instance_canonical_e
def main : IO Unit := do
 match outputs with
 | .ok rows => for (row,i) in rows.zipIdx do IO.println s!"ROW i={i} y={row}"
 | .timeout => throw (IO.userError "E timed out")
 | .unsupported msg => IO.println s!"E_REFUSAL {msg}"
