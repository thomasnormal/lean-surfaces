import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.memory_edge_casez_casex_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryEdgeCasezCasex
  from "Examples/system-verilog/sem2/memory_edge_casez_casex_canonical_e/memory_edge_casez_casex_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem memoryEdgeCasezCasex.pdesign [4, 2] with
  | .ok d =>
      d.memories.size == 1 &&
      d.processes.toList.any (fun p => match p with
        | .edge { body := .block body, .. } =>
            body.any (fun stmt => match stmt with
              | .caseStmt _ _ _ .casez _ => true
              | _ => false) &&
            body.any (fun stmt => match stmt with
              | .caseStmt _ _ _ .casex _ => true
              | _ => false)
        | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("sel", ⟨#[.lx, .lx, .lx, .lx]⟩), ("d", ⟨#[.lx, .lx, .lx, .lx]⟩)],
   [("clk", LVec.ofNat 1 1), ("sel", ⟨#[.lz, .lx, .l1, .l0]⟩), ("d", .ofNat 4 7)]]

def outputs : Res (List (String × String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryEdgeCasezCasex.pdesign [4, 2]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "qz",
     SvState.showSignal (CoreMemState.view d s) "qx",
     SvState.showSignal (CoreMemState.view d s) "plain"))

#guard match outputs with
  | .ok [("0001", "0010", "0000"),
        ("0001", "0100", "0000")] => true
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.memory_edge_casez_casex_canonical_e
