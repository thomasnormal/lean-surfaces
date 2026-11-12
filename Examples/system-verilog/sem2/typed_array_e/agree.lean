import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.typed_array_e
open LeanModels.Sv
load_design_sv2 typedArrayE from
  "Examples/system-verilog/sem2/typed_array_e/typed_array_e.sv.json"
#guard match typedArrayE.pdesign.processes with
  | [.assign "y" _] => true
  | _ => false
#guard typedArrayE.pdesign.others == [("NetSymbol:type", "values [0:3]")]
#guard match typedArrayE.sem.processes.toList with
  | [.assign (.ident "y") _, .unsupported "NetSymbol:type" "values [0:3]"] => true
  | _ => false
end Examples.«system-verilog».sem2.typed_array_e
