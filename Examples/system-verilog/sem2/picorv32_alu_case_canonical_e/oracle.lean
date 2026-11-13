import Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e
def main : IO Unit := do
  match outputs with
  | .ok rows => for (row, i) in rows.zipIdx do IO.println s!"ROW {i} alu_out={row}"
  | .timeout => throw (IO.userError "E timed out")
  | .unsupported msg => throw (IO.userError msg)
