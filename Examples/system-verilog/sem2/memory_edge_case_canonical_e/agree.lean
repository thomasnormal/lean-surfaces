import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.memory_edge_case_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryEdgeCase
  from "Examples/system-verilog/sem2/memory_edge_case_canonical_e/memory_edge_case_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem memoryEdgeCase.pdesign [4] with
  | .ok d =>
      d.memories.size == 1 &&
      d.processes.toList.any (fun p => match p with
        | .edge { body := .block [.caseStmt ..], .. } => true
        | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("sel", LVec.ofNat 2 0), ("d", LVec.ofNat 4 3)],
   [("clk", LVec.ofNat 1 1), ("sel", LVec.ofNat 2 0), ("d", LVec.ofNat 4 10)]]

def outputs : Res (List (String × String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryEdgeCase.pdesign [4]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "q0",
     SvState.showSignal (CoreMemState.view d s) "q1",
     SvState.showSignal (CoreMemState.view d s) "hit"))

#guard match outputs with
  | .ok [("0001", "0010", "xxxx"),
        ("1010", "0010", "xxxx")] => true
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.memory_edge_case_canonical_e
