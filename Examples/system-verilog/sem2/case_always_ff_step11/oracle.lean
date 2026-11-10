import Examples.«system-verilog».sem2.case_always_ff_step11.agree

open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.case_always_ff_step11.agree

private def emit (tag : String) (e : Elab1) (names : List String)
    (entries : List SvState) : IO Unit := do
  let initial := Config1.init e
  let some rows := trace e names initial entries
    | throw (IO.userError s!"{tag}: E refused or exhausted the test budget")
  for row in showRow e names initial :: rows do
    IO.println s!"ROW {tag} {String.intercalate " " row}"

def main : IO Unit := do
  emit "plain" edge ["q", "q_default"] inputs
  emit "order" orderEdge orderNames orderInputs
