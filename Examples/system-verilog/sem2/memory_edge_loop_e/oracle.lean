import Examples.«system-verilog».sem2.memory_edge_loop_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.memory_edge_loop_e

def emitRows : IO Unit := do
  match design with
  | .ok d =>
      match runRows d d.initial stimulus with
      | .ok states =>
          for (s, i) in states.zipIdx do
            let q := SvState.showSignal (CoreMemState.view d s) "q"
            IO.println s!"ROW {i} q={q}"
      | .timeout => throw (IO.userError "E memory execution timed out")
      | .unsupported msg => throw (IO.userError msg)
  | .timeout => throw (IO.userError "E memory admission timed out")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := emitRows
