import Examples.«system-verilog».sem2.explicit_cast_signed_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.explicit_cast_signed_e
def main : IO Unit := do match d8,d2 with | .ok a,.ok b => for (v,i) in (rows a ++ rows b).zipIdx do IO.println ("ROW "++toString i++" ys="++v.1++" yb="++v.2) | _,_ => throw (IO.userError "design")
