import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE
namespace Examples.«system-verilog».sem2.packed_shift_mem_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 packedShiftMem from
  "Examples/system-verilog/sem2/packed_shift_mem_e/packed_shift_mem_e.sv.json"
def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("v", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("v", LVec.ofNat 1 1)]]
def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List String)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (SvState.showSignal s'.scalar "q" :: tail)
def outputs (n : Int) : Except String (List String) := do
  let d ← match MemEDesign.ofPDesign packedShiftMem.pdesign [n] with
    | .ok d => .ok d | .timeout => .error "timeout" | .unsupported m => .error m
  runRows d d.init stimulus
#guard match outputs 4 with | .ok r => r.length == 4 | _ => false
#guard match outputs 8 with | .ok r => r.length == 4 | _ => false
end Examples.«system-verilog».sem2.packed_shift_mem_e
