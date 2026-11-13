import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.generated_array_index_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 generatedArrayIndex from
  "Examples/system-verilog/sem2/generated_array_index_canonical_e/generated_array_index_canonical_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem generatedArrayIndex.pdesign []
  let rows ← runCoreMemRows d d.initial [[("x", LVec.ofNat 8 0)], [("x", LVec.ofNat 8 0xa5)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match outputs with
  | .unsupported "ElementSelect:default-point-index: slot[i] = x" => true
  | _ => false
end Examples.«system-verilog».sem2.generated_array_index_canonical_e
