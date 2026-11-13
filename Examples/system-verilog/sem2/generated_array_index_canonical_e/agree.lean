import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generated_array_index_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 generatedArrayIndex from
  "Examples/system-verilog/sem2/generated_array_index_canonical_e/generated_array_index_canonical_e.sv.json"

def stimuli : List SvState := [
  [],
  [("x", LVec.ofNat 8 0)],
  [("x", LVec.ofNat 8 0xa5)],
  [("x", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz")],
  [("x", LVec.ofNat 8 0x3c)],
  [("x", LVec.ofNat 8 0xff)],
  [("x", LVec.ofNat 8 0)],
  [("x", LVec.ofNat 8 1)]
]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem generatedArrayIndex.pdesign []
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match PDesign.instantiateCoreMem generatedArrayIndex.pdesign [] with
  | .ok d => d.memories.size == 1 && d.processes.size == 5 &&
      match d.processes[0]? with
      | some (CoreMemProc.assign (.ident "y") (.arrayElem "slot" [(.int 0)])) => true
      | _ => false
  | _ => false
#guard match outputs with
  | .ok ["xxxxxxxx", "00000000", "10100101", "xxxxxxxx", "zzzzzzzz",
      "00111100", "11111111", "00000000", "00000001"] => true
  | _ => false
end Examples.«system-verilog».sem2.generated_array_index_canonical_e
