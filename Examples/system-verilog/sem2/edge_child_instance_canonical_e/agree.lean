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
  let d ← PDesign.instantiateCoreMem edgeParent.pdesign []
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")
#guard edgeParent.pdesign.generates.any fun g => match g with | .inst i => i.module == "edge_child_canonical_e" | _ => false
#guard match outputs with
  | .unsupported "Instance: module instance 'u_child' of 'edge_child_canonical_e' outside the canonical E memory route" => true
  | _ => false
end Examples.«system-verilog».sem2.edge_child_instance_canonical_e
