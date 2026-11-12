import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.untyped_localparam_refuse
open LeanModels.Sv
load_design_sv2 untypedLocalparamRefuse from
  "Examples/system-verilog/sem2/untyped_localparam_refuse/untyped_localparam_refuse.sv.json"
#guard match untypedLocalparamRefuse.pdesign.instantiate2 [] with
  | .unsupported msg => msg.contains "Constant:untyped-width"
  | _ => false
#guard match untypedLocalparamRefuse.pdesign.instantiate2 [8] with
  | .unsupported msg => msg.contains "Constant:untyped-width"
  | _ => false
end Examples.«system-verilog».sem2.untyped_localparam_refuse
