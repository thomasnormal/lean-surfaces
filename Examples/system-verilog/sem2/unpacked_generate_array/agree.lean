import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Ordinary canonical-E performance receipt for a parameter-dependent unpacked
array. Fixed cell selections remain source-shaped native memory operations;
the receipt does not use MemCycle or a second store. -/

namespace Examples.«system-verilog».sem2.unpacked_generate_array.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unpackedGenerateArray from
  "Examples/system-verilog/sem2/unpacked_generate_array/unpacked_generate_array.sv.json"

def stimuli : List SvState := [
  [],
  [("x", LVec.ofNat 8 0)],
  [("x", LVec.ofNat 8 0xa5)],
  [("x", LVec.ofNat 8 0xff)],
  [("x", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 0x3c)],
  [("x", LVec.ofNat 8 1)]
]

def outputs : Res (List String) := do
  let d ← unpackedGenerateArray.e 8 2
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match unpackedGenerateArray.e 8 2 with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false
#guard match outputs with
  | .ok ["xxxxxxxx", "00000000", "10100101", "11111111", "xxxxxxxx", "zzzzzzzz", "00111100", "00000001"] => true
  | _ => false

end Examples.«system-verilog».sem2.unpacked_generate_array.agree
