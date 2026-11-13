import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.always_comb_memory_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 alwaysCombMemory from
  "Examples/system-verilog/sem2/always_comb_memory_canonical_e/always_comb_memory_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem alwaysCombMemory.pdesign [4] with
  | .ok d => d.processes.toList.any (fun p => match p with | .comb _ => true | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0)],
   [("clk", LVec.ofNat 1 1), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 5)],
   [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 1), ("d", LVec.ofNat 4 9)],
   [("clk", LVec.ofNat 1 0), ("en", LVec.ofNat 1 0), ("d", LVec.ofNat 4 9)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem alwaysCombMemory.pdesign [4]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match outputs with
  | .ok ["xxxx", "0101", "1001", "0101"] => true
  | _ => false

#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.always_comb_memory_canonical_e
