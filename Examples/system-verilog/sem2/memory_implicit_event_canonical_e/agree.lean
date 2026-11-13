import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_implicit_event_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 memoryImplicit from
  "Examples/system-verilog/sem2/memory_implicit_event_canonical_e/memory_implicit_event_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem memoryImplicit.pdesign [4,2] with
  | .ok d => d.processes.toList.any (fun p => match p with | .implicit _ => true | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("d", LVec.ofNat 4 0), ("idx", LVec.ofNat 2 0)],
   [("d", LVec.ofNat 4 3), ("idx", LVec.ofNat 2 0)],
   [("d", LVec.ofNat 4 3), ("idx", LVec.ofNat 2 1)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem memoryImplicit.pdesign [4,2]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match outputs with
  | .ok ["0101", "0110", "1010"] => true
  | _ => false

#print axioms CoreMemDesign.step
end Examples.«system-verilog».sem2.memory_implicit_event_canonical_e
