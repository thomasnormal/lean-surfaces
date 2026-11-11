/- Clean-room E memory witness: canonical parameter-bound clocked loops retain
   their source loop and issue one cell NBA per trip before commit. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

namespace Examples.«system-verilog».sem2.memory_edge_loop_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 memoryEdgeLoop from
  "Examples/system-verilog/sem2/memory_edge_loop_e/memory_edge_loop_e.sv.json"

def design : Res MemEDesign :=
  MemEDesign.ofPDesign memoryEdgeLoop.pdesign [8, 4]

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3)],
   [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
   [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)]]

def runRows (d : MemEDesign) (s : MemEState) : List SvState → Except String (List MemEState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

#guard match design with
  | .ok d => d.memDecls.length == 1 && d.processes.length == 2
  | _ => false

#guard match design with
  | .ok d =>
      match runRows d d.init stimulus with
      | .ok [s0, s1, s2, s3, s4] =>
          SvState.lookup s0.scalar "q" == some (LVec.ofNat 8 0) &&
          SvState.lookup s1.scalar "q" == some (LVec.ofNat 8 0) &&
          SvState.lookup s2.scalar "q" == some (LVec.ofNat 8 17) &&
          SvState.lookup s3.scalar "q" == some (LVec.ofNat 8 17) &&
          SvState.lookup s4.scalar "q" == some (LVec.ofNat 8 34)
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.memory_edge_loop_e
