import Examples.«system-verilog».sem2.param_mem_shift_e.agree
open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.param_mem_shift_e

def emit (tag : String) (d : MemEDesign) (rows : List SvState) : IO Unit :=
  match runRows d d.init rows with
  | .ok states => for (s, i) in states.zipIdx do
      let q := SvState.showSignal s.scalar "q"
      IO.println s!"ROW {tag}_{i} q={q}"
  | .error msg => throw (IO.userError msg)

 def main : IO Unit := do
  match design with
  | .ok d => emit "P4" d stimuli
  | .timeout => throw (IO.userError "P4 timeout")
  | .unsupported e => throw (IO.userError e)
  match design2 with
  | .ok d => emit "P2" d stimuli
  | .timeout => throw (IO.userError "P2 timeout")
  | .unsupported e => throw (IO.userError e)
