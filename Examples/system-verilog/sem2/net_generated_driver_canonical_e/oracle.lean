import Examples.«system-verilog».sem2.net_generated_driver_canonical_e.agree
open LeanModels.Sv
open Examples.«system-verilog».sem2.net_generated_driver_canonical_e
def main : IO Unit := do
 match outputs with
 | .ok rows => for (row,i) in rows.zipIdx do IO.println s!"ROW i={i} q={row.1} z_out={row.2}"
 | .timeout => throw (IO.userError "E timed out")
 | .unsupported msg => throw (IO.userError msg)
