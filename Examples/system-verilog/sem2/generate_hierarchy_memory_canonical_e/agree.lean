import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.generate_hierarchy_memory_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 generateHierarchyMemory from
  "Examples/system-verilog/sem2/generate_hierarchy_memory_canonical_e/generate_hierarchy_memory_canonical_e.sv.json"
def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 0)]]
def outputs : Res (List String) := do
  let d ← CoreMemDesign.ofHierarchy generateHierarchyMemory.pdesign generateHierarchyMemory.plib [1,4]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q0")
end Examples.«system-verilog».sem2.generate_hierarchy_memory_canonical_e
