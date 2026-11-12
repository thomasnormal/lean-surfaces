import Examples.«system-verilog».sem2.hierarchy_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel
open Examples.«system-verilog».sem2.hierarchy_e

def emitRows : IO Unit := do
  let cases := ["00000000", "00000001", "10100101", "11110000", "xxxxxxxx"]
  for (a, i) in cases.zipIdx do
    match run a with
    | some y => IO.println s!"ROW {i} y={y}"
    | none => throw (IO.userError "E hierarchy execution refused or timed out")

def main : IO Unit := emitRows
