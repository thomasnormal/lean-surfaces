import Examples.«system-verilog».sem2.explicit_cast_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.explicit_cast_e
def main : IO Unit := do
  match design8, design2 with
  | .ok a, .ok b => for (v,i) in (rows a ++ rows b).zipIdx do IO.println ("ROW " ++ toString i ++ " y=" ++ v)
  | _, _ => throw (IO.userError "design")
