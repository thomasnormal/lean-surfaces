import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.generate_parameter_e
open LeanModels.Sv
load_design_sv2 generateParameterE from
  "Examples/system-verilog/sem2/generate_parameter_e/generate_parameter_e.sv.json"
#guard generateParameterE.pdesign.others == []
#guard match (generateParameterE.sem 8).processes.toList with
  | [.assign (.ident "y") (.ident "x")] => true
  | _ => false
#guard match (generateParameterE.sem 4).processes.toList with
  | [.assign (.ident "y") (.unary .lnot (.ident "x"))] => true
  | _ => false
end Examples.«system-verilog».sem2.generate_parameter_e
