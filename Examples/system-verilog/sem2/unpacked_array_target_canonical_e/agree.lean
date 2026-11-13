import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.unpacked_array_target_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 unpackedArrayTarget from
  "Examples/system-verilog/sem2/unpacked_array_target_canonical_e/unpacked_array_target_canonical_e.sv.json"
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem unpackedArrayTarget.pdesign []
  let rows ← runCoreMemRows d d.initial [[("x", LVec.ofNat 8 0), ("idx", LVec.ofNat 1 0)], [("x", LVec.ofNat 8 0xa5), ("idx", LVec.ofNat 1 0)]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard unpackedArrayTarget.pdesign.processes.any fun p => match p with
  | .alwaysComb (.block (.unsupported "AssignmentExpression:target" _ :: _)) => true
  | _ => false
#guard match outputs with
  | .unsupported "9.2.2.2: always_comb is outside this memory edge slice" => true
  | _ => false
end Examples.«system-verilog».sem2.unpacked_array_target_canonical_e
