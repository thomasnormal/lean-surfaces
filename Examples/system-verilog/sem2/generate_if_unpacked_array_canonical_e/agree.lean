import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.generate_if_unpacked_array_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 generateIfUnpackedArray from
  "Examples/system-verilog/sem2/generate_if_unpacked_array_canonical_e/generate_if_unpacked_array_canonical_e.sv.json"

def stimuli : List SvState := [
  [],
  [("x", LVec.ofNat 8 0)],
  [("x", LVec.ofNat 8 0xa5)],
  [("x", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 0x3c)],
  [("x", LVec.ofNat 8 0xff)],
  [("x", LVec.ofNat 8 1)]
]

def outputs (N : Nat) : Res (List String) := do
  let d ← generateIfUnpackedArray.e N
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#guard match generateIfUnpackedArray.e 1 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false
#guard match generateIfUnpackedArray.e 2 with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false
#guard match outputs 1 with
  | .ok ["xxxxxxxx", "00000000", "10100101", "xxxxxxxx", "zzzzzzzz", "00111100", "11111111", "00000001"] => true
  | _ => false
#guard match outputs 2 with
  | .ok ["xxxxxxxx", "00000000", "10100101", "xxxxxxxx", "zzzzzzzz", "00111100", "11111111", "00000001"] => true
  | _ => false

end Examples.«system-verilog».sem2.generate_if_unpacked_array_canonical_e
