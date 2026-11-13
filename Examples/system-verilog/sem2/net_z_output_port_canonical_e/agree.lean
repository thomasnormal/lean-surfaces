import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.net_z_output_port_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 netZOutput from
  "Examples/system-verilog/sem2/net_z_output_port_canonical_e/net_z_output_port_canonical_e.sv.json"
def stimuli : List SvState := [[("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)]]
def outputs : Res (List (String × String)) := do
  let d ← PDesign.instantiateCoreMem netZOutput.pdesign [4]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => (SvState.showSignal (CoreMemState.view d s) "q",
    SvState.showSignal (CoreMemState.view d s) "z_out"))
#guard netZOutput.pdesign.others.any (fun e => e.1 == "PortSymbol:net-z" && e.2 == "z_out")
#guard netZOutput.pdesign.netMetadata.any (fun md => md.name == "z_out" && md.width == 1 && md.driverReason == some "no driver: the net reads z")
#guard match PDesign.instantiateCoreMem netZOutput.pdesign [4] with
  | .ok d => d.scalar.decls.toList.any (fun x => x.name == "z_out" && x.isNet && x.isOutput && x.init == some (LVec.replicate 1 .lz))
  | _ => false
#guard match outputs with
  | .ok rows => rows == [("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "z"), ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "z")]
  | _ => false
end Examples.«system-verilog».sem2.net_z_output_port_canonical_e
