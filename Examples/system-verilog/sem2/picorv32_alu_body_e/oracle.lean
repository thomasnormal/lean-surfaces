import Examples.«system-verilog».sem2.picorv32_alu_body_e.agree

open Examples.«system-verilog».sem2.picorv32_alu_body_e.agree

private def names : List String :=
  ["first", "add_5_3", "sub_5_3", "sra_neg", "shr_neg", "xz", "srai_flag"]

private def emit : List String → List (Option (List String)) → IO Unit
  | [], [] => pure ()
  | name :: names, some row :: rows => do
      IO.println ("ROW " ++ name ++ " " ++ String.intercalate " " row)
      emit names rows
  | _, _ => throw (IO.userError "E trace has the wrong number of rows")

def main : IO Unit := emit names traceRows
