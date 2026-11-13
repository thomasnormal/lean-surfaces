import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 ordinaryStorage from "Examples/system-verilog/sem2/parameterized_unpacked_storage_ordinary_e/parameterized_unpacked_storage_ordinary_e.sv.json"
private def stimulus : List SvState := [
  [("x", LVec.ofNat 8 0)], [("x", LVec.ofNat 8 1)],
  [("x", LVec.ofNat 8 16)], [("x", LVec.ofNat 8 165)],
  [("x", LVec.ofNat 8 255)], [("x", LVec.lit "xxxxxxxx")],
  [("x", LVec.lit "zzzzzzzz")], [("x", LVec.ofNat 8 90)]]
def outputs (n : Nat) : Res (List String) := do
  let d ← ordinaryStorage.e n
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match ordinaryStorage.sem 1 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
#guard match ordinaryStorage.sem 2 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
#guard match ordinaryStorage.e 1 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
#guard match ordinaryStorage.e 2 with | .ok d => d.memories.size == 1 && d.processes.size == 2 | _ => false
#guard outputs 1 == .ok ["00000000", "00000001", "00010000", "10100101", "11111111", "xxxxxxxx", "zzzzzzzz", "01011010"]
#guard outputs 2 == .ok ["00000000", "00000001", "00010000", "10100101", "11111111", "xxxxxxxx", "zzzzzzzz", "01011010"]
end Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e
