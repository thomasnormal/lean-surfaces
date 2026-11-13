import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.memory_shape_a_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeA from
  "Examples/system-verilog/sem2/memory_shape_a_e/memory_shape_a_e.sv.json"
def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 0), ("idx", LVec.ofNat 3 0)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 1), ("idx", LVec.ofNat 3 0)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 2), ("idx", LVec.ofNat 3 1)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 2), ("idx", LVec.ofNat 3 1)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 4), ("idx", LVec.ofNat 3 2)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 8 4), ("idx", LVec.ofNat 3 2)],
   [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 8 8), ("idx", LVec.ofNat 3 7)]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do let s' ← d.step s row; let tail ← runRows d s' rest; .ok (s' :: tail)
def outputs (args : List Int) : Except String (List (String × String)) := do
  let d ← match MemEDesign.ofPDesign memoryShapeA.pdesign args with
    | .ok d => .ok d | .timeout => .error "E memory admission timed out" | .unsupported msg => .error msg
  let rows ← runRows d d.init stimulus
  .ok (rows.map fun s => (SvState.showSignal s.scalar "q", SvState.showSignal s.scalar "selected"))
#guard (match outputs [4,3] with | .ok r => r.length == 7 | _ => false)
#guard (match outputs [8,5] with | .ok r => r.length == 7 | _ => false)
end Examples.«system-verilog».sem2.memory_shape_a_e
