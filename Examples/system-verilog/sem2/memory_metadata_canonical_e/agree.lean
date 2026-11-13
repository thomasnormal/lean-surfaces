import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for inert module metadata beside a source-shaped memory.

The empty input-only task is retained as metadata and its call is an empty
statement.  The unsized x/z marker is retained on the assignment expression;
the canonical width-directed literal rule supplies the all-x memory value.
-/
namespace Examples.«system-verilog».sem2.memory_metadata_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryMetadata
  from "Examples/system-verilog/sem2/memory_metadata_canonical_e/memory_metadata_canonical_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem memoryMetadata.pdesign [4]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard memoryMetadata.pdesign.others.map Prod.fst ==
  ["SubroutineSymbol:empty-task"]

#guard coreMemAllowedOther
  ("SubroutineSymbol:empty-task", "task empty_statement; begin end endtask")
#guard coreMemAllowedOther
  ("IntegerLiteral:unsized-xz-parametric", "'bx")
#guard coreMemAllowedOther
  ("ConversionExpression:xz-literal-parametric", "'bx")
#guard !coreMemAllowedOther ("NetSymbol:net-z", "w")

#guard match PDesign.instantiateCoreMem memoryMetadata.pdesign [4] with
  | .ok d => d.memories.size == 1 && d.processes.size == 2
  | _ => false

#guard match outputs with
  | .ok ["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"] => true
  | _ => false

end Examples.«system-verilog».sem2.memory_metadata_canonical_e
