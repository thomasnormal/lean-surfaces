import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.extractor_options_e
open LeanModels.Sv
load_design_sv2 enabled from "Examples/system-verilog/sem2/extractor_options_e/enabled.json"
load_design_sv2 disabled from "Examples/system-verilog/sem2/extractor_options_e/disabled.json"
#guard enabled.pdesign.processes.length == 2
#guard disabled.pdesign.processes.length == 1
#guard match enabled.pdesign.processes.head? with
  | some (.initial (.unsupported "SysCall:$error" _)) => true
  | _ => false
#guard match disabled.pdesign.processes.head? with
  | some (.assign "y" (.lit _)) => true
  | _ => false
end Examples.«system-verilog».sem2.extractor_options_e
