import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.assign_target_e
open LeanModels.Sv
load_design_sv2 assignTargetE from
  "Examples/system-verilog/sem2/assign_target_e/assign_target_e.sv.json"
#guard assignTargetE.pdesign.others == []
#guard match assignTargetE.sem.processes.toList with
  | [.assign (.ident "missing") (.ident "x"), .assign (.ident "y") (.ident "x")] => true
  | _ => false
end Examples.«system-verilog».sem2.assign_target_e
