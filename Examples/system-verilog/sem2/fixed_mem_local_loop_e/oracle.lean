import Examples.«system-verilog».sem2.fixed_mem_local_loop_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.fixed_mem_local_loop_e
def emit (tag : String) (d : MemEDesign) (rows : List SvState) : IO Unit := do
  match runRows d d.init rows with
  | .ok states => for (s, i) in states.zipIdx do
      IO.println ("ROW " ++ tag ++ "_" ++ toString i ++ " q=" ++ SvState.showSignal s.scalar "q")
  | .error msg => throw (IO.userError msg)
def main : IO Unit := do
  match design8 with | .ok d => emit "W8" d stimuli8 | .timeout => throw (IO.userError "W8 timeout") | .unsupported e => throw (IO.userError e)
  match design4 with | .ok d => emit "W4" d stimuli4 | .timeout => throw (IO.userError "W4 timeout") | .unsupported e => throw (IO.userError e)
