import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.always_comb_case_memory_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 alwaysCombCaseMemory from
  "Examples/system-verilog/sem2/always_comb_case_memory_canonical_e/always_comb_case_memory_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem alwaysCombCaseMemory.pdesign [4] with
  | .ok d => d.processes.toList.any (fun p => match p with | .comb (.block [.caseStmt ..]) => true | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("sel", LVec.ofNat 2 0), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofNat 2 1), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofNat 2 2), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofNat 2 2), ("d", LVec.ofNat 4 5)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem alwaysCombCaseMemory.pdesign [4]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match outputs with
  | .ok ["0011", "0111", "1100", "0101"] => true
  | _ => false

#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.always_comb_case_memory_canonical_e
