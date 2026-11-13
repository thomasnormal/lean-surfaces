import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.net_generated_driver_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 netGeneratedDriver from
  "Examples/system-verilog/sem2/net_generated_driver_canonical_e/net_generated_driver_canonical_e.sv.json"
def stimuli : List SvState := [[("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)]]
def outputs : Res (List (String × String)) := do
  let d ← PDesign.instantiateCoreMem netGeneratedDriver.pdesign [1]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => (SvState.showSignal (CoreMemState.view d s) "q", SvState.showSignal (CoreMemState.view d s) "z_out"))
#guard match PDesign.instantiateCoreMem netGeneratedDriver.pdesign [1] with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "z" && x.isNet && x.init == some (LVec.replicate 1 .lz))
  | _ => false
#guard match outputs with
  | .ok rows => rows == [("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "0"), ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "0")]
  | _ => false
end Examples.«system-verilog».sem2.net_generated_driver_canonical_e
