import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 ordinaryStorage from "Examples/system-verilog/sem2/parameterized_unpacked_storage_ordinary_e/parameterized_unpacked_storage_ordinary_e.sv.json"
#guard match ordinaryStorage.sem 2 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
#guard match ordinaryStorage.e 2 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
private def stimulus : List SvState := [[("x", LVec.ofNat 8 16)], [("x", LVec.ofNat 8 165)]]
def outputs : Res (List String) := do
  let d ← ordinaryStorage.e 2
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard outputs == .ok ["00010000", "10100101"]
end Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e
