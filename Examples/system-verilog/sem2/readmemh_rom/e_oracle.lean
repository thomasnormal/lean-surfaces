import Examples.«system-verilog».sem2.readmemh_rom.e_agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.readmemh_rom.e_agree

def emitRows : IO Unit := do
  match design with
  | .ok d =>
      match d.timeZero with
      | .ok s =>
          match runRows d s stimulus with
          | .ok states =>
              for (state, index) in states.zipIdx do
                let q := SvState.showSignal state.scalar "q"
                IO.println s!"ROW {index} q={q}"
          | .error msg => throw (IO.userError msg)
      | .error msg => throw (IO.userError msg)
  | .timeout => throw (IO.userError "E readmemh admission timed out")
  | .unsupported msg => throw (IO.userError msg)

def main : IO Unit := emitRows
