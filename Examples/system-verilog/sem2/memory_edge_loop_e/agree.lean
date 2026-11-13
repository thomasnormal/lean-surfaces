import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.memory_edge_loop_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 memoryEdgeLoop from
  "Examples/system-verilog/sem2/memory_edge_loop_e/memory_edge_loop_e.sv.json"

def design : Res CoreMemDesign :=
  PDesign.instantiateCoreMem memoryEdgeLoop.pdesign [8, 4]

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 0), ("d", LVec.ofNat 8 3)],
   [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 17)],
   [("clk", LVec.ofNat 1 0), ("rstn", LVec.lit "x"), ("d", LVec.ofNat 8 34)],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.ofNat 8 34)],
   [("clk", LVec.lit "x"), ("rstn", LVec.ofNat 1 1), ("d", LVec.lit "xxxxxxxx")],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.lit "xxxxxxxx")],
   [("clk", LVec.ofNat 1 0), ("rstn", LVec.ofNat 1 1), ("d", LVec.lit "zzzzzzzz")],
   [("clk", LVec.ofNat 1 1), ("rstn", LVec.ofNat 1 1), ("d", LVec.lit "zzzzzzzz")]]

def runRows (d : CoreMemDesign) (s : CoreMemState) : List SvState → Res (List CoreMemState)
  | [] => .ok []
  | row :: rest => do
      let s' ← d.step s row
      let tail ← runRows d s' rest
      .ok (s' :: tail)

#guard match design with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false

#guard match design with
  | .ok d =>
      match runRows d d.initial stimulus with
      | .ok [s0, s1, s2, s3, s4, s5, s6, s7, s8] =>
          (SvState.showSignal (CoreMemState.view d s0) "q" == "00000000") &&
          (SvState.showSignal (CoreMemState.view d s1) "q" == "00000000") &&
          (SvState.showSignal (CoreMemState.view d s2) "q" == "00010001") &&
          (SvState.showSignal (CoreMemState.view d s3) "q" == "00100010") &&
          (SvState.showSignal (CoreMemState.view d s4) "q" == "00100010") &&
          (SvState.showSignal (CoreMemState.view d s5) "q" == "00100010") &&
          (SvState.showSignal (CoreMemState.view d s6) "q" == "xxxxxxxx") &&
          (SvState.showSignal (CoreMemState.view d s7) "q" == "xxxxxxxx") &&
          (SvState.showSignal (CoreMemState.view d s8) "q" == "zzzzzzzz")
      | _ => false
  | _ => false

end Examples.«system-verilog».sem2.memory_edge_loop_e
