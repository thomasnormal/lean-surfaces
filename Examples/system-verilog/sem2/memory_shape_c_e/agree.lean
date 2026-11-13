import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_shape_c_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeC from
  "Examples/system-verilog/sem2/memory_shape_c_e/memory_shape_c_e.sv.json"
def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("a[0]", LVec.ofNat 4 1), ("a[1]", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 1), ("a[0]", LVec.ofNat 4 1), ("a[1]", LVec.ofNat 4 2)],
   [("clk", LVec.ofNat 1 0), ("a[0]", LVec.ofNat 4 3), ("a[1]", LVec.ofNat 4 4)],
   [("clk", LVec.ofNat 1 1), ("a[0]", LVec.ofNat 4 3), ("a[1]", LVec.ofNat 4 4)]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
def refusal : Bool :=
  match MemEDesign.ofPDesign memoryShapeC.pdesign [4,2] with
  | .unsupported msg => msg.contains "generate items"
  | _ => false
#guard refusal
#guard match LeanModels.Sv.Kernel.PDesign.instantiateCoreMem memoryShapeC.pdesign [4, 2] with
  | .ok d => d.processes.size == 3
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_c_e
