import Examples.«system-verilog».sem2.param_mem_child_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.param_mem_child_e
def emit (tag : String) (d : MemEDesign) : IO Unit := do
  match runRows d d.init stimuli with
  | .ok states => for (s, i) in states.zipIdx do
      IO.println ("ROW " ++ tag ++ "_" ++ toString i ++ " q=" ++ SvState.showSignal s.scalar "q")
  | .error msg => throw (IO.userError msg)
def main : IO Unit := do
  match design4 with | .ok d => emit "P4" d | .timeout => throw (IO.userError "P4 timeout") | .unsupported e => throw (IO.userError e)
  match design2 with | .ok d => emit "P2" d | .timeout => throw (IO.userError "P2 timeout") | .unsupported e => throw (IO.userError e)
