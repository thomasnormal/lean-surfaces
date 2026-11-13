import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem

/-! Canonical E receipt for one parameterized child containing unpacked
storage. Module elaboration is retained as source-shaped hierarchy; the child
memory remains one `MemState` declaration and port connections are assignments
in the same canonical executor. -/
namespace Examples.«system-verilog».sem2.memory_shape_b_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 memoryShapeB
  from "Examples/system-verilog/sem2/memory_shape_b_canonical_e/memory_shape_b_canonical_e.sv.json"

#check memoryShapeB.e

def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0)]]

def design : Res CoreMemDesign :=
  CoreMemDesign.ofHierarchy memoryShapeB.pdesign memoryShapeB.plib [4, 3]

def outputs : Res (List String) := do
  let d ← design
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match design with
  | .ok d => d.memories.size == 1 && d.processes.size == 5
  | _ => false
end Examples.«system-verilog».sem2.memory_shape_b_canonical_e
