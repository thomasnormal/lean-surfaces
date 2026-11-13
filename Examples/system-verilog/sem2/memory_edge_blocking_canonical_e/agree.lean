import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryEdgeBlocking
  from "Examples/system-verilog/sem2/memory_edge_blocking_canonical_e/memory_edge_blocking_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem memoryEdgeBlocking.pdesign [4, 2] with
  | .ok d =>
      d.memories.size == 1 &&
      d.processes.toList.any (fun p => match p with
        | .edge { style := .alwaysPlain, body := .block (_ :: _), .. } => true
        | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 3)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 10)]]

def outputs : Res (List (String × String × String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryEdgeBlocking.pdesign [4, 2]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "mem0",
     SvState.showSignal (CoreMemState.view d s) "mem1",
     SvState.showSignal (CoreMemState.view d s) "delayed",
     SvState.showSignal (CoreMemState.view d s) "marker"))

#guard match outputs with
  | .ok [("0001", "0010", "0000", "0000"),
        ("1010", "1010", "1010", "0000")] => true
  | _ => false

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e
