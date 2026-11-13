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

def rows : Res (List CoreMemState) := do
  let d ← unpackedGenerateArray.e 8 2
  runCoreMemRows d d.initial [[], [], [], [], [], [], [], []]

#guard match unpackedGenerateArray.e 8 2 with
  | .ok d => d.memories.size == 1 && d.processes.size == 3
  | _ => false
#guard match rows with | .ok states => states.length == 8 | _ => false

end Examples.«system-verilog».sem2.unpacked_generate_array.agree
