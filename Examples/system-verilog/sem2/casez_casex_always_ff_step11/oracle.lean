import Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree
open Examples.«system-verilog».sem2.casez_casex_always_ff_step11.agree

def main : IO Unit := do
  let initial := Config1.init wildcardEdge
  let some rows := trace wildcardEdge wildcardNames initial wildcardInputs
    | throw (IO.userError "wild: E refused or exhausted the test budget")
  for row in showRow wildcardEdge wildcardNames initial :: rows do
    IO.println s!"ROW wild {String.intercalate " " row}"
