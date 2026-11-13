import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_shape_c_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeC from
  "Examples/system-verilog/sem2/memory_shape_c_canonical_e/memory_shape_c_canonical_e.sv.json"
def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("a[0]", LVec.ofNat 4 1), ("a[1]", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 1), ("a[0]", LVec.ofNat 4 1), ("a[1]", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 0), ("a[0]", LVec.ofNat 4 3), ("a[1]", LVec.ofNat 4 4)],
   [("clk", LVec.ofNat 1 1), ("a[0]", LVec.ofNat 4 3), ("a[1]", LVec.ofNat 4 4)]]
def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem memoryShapeC.pdesign [4, 2]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard match PDesign.instantiateCoreMem memoryShapeC.pdesign [4,2] with
  | .ok d => d.memories.size == 2 && d.processes.size == 3
  | _ => false
#guard match outputs with
  | .ok rows => rows == ["xxxx", "0001", "0001", "0011"]
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_c_canonical_e
