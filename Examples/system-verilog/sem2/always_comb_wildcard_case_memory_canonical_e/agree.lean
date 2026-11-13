import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.always_comb_wildcard_case_memory_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 alwaysCombWildcardCaseMemory from "Examples/system-verilog/sem2/always_comb_wildcard_case_memory_canonical_e/always_comb_wildcard_case_memory_canonical_e.sv.json"
#guard match PDesign.instantiateCoreMem alwaysCombWildcardCaseMemory.pdesign [4] with
  | .ok d => d.processes.toList.any (fun p => match p with | .comb (.block (_ :: _)) => true | _ => false)
  | _ => false
private def stimulus : List SvState :=
  [[("sel", LVec.ofString? "00" |>.get!), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofString? "10" |>.get!), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofString? "x0" |>.get!), ("d", LVec.ofNat 4 12)],
   [("sel", LVec.ofString? "zz" |>.get!), ("d", LVec.ofNat 4 5)]]
def outputs : Res (List (String × String)) := do
  let d ← PDesign.instantiateCoreMem alwaysCombWildcardCaseMemory.pdesign [4]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "qz",
     SvState.showSignal (CoreMemState.view d s) "qx"))
#guard match outputs with
  | .ok [("0011", "0011"), ("0111", "0111"), ("1100", "0011"), ("0011", "0011")] => true
  | _ => false
#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.always_comb_wildcard_case_memory_canonical_e
