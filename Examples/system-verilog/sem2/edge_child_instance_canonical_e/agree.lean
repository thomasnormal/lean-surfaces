import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.edge_child_instance_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 edgeParent from
  "Examples/system-verilog/sem2/edge_child_instance_canonical_e/edge_child_instance_canonical_e.sv.json"
def stimuli : List SvState := [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 1 0)]]
def outputs : Res (List String) := do
  let d ← edgeParent.e
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
def outputsEight : Res (List String) := do
  let d ← edgeParent.e
  let rows ← runCoreMemRows d d.initial
    (stimuli ++ [[], [], [], [], [], []])
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard match edgeParent.e with
  | .ok d => d.memories.size == 0 && d.processes.size == 5
  | _ => false
#guard outputs == .ok ["x", "0"]
#guard outputsEight == .ok ["x", "0", "0", "0", "0", "0", "0", "0"]
end Examples.«system-verilog».sem2.edge_child_instance_canonical_e
