import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.invalid_continuous_assign_e
open LeanModels.Sv
load_design_sv2 invalidContinuousAssignE from
  "Examples/system-verilog/sem2/invalid_continuous_assign_e/invalid_continuous_assign_e.sv.json"
#guard invalidContinuousAssignE.pdesign.others ==
  [("SlangError:UndeclaredIdentifier", "invalid_continuous_assign_e.sv:2: use of undeclared identifier 'missing'")]
#guard match invalidContinuousAssignE.pdesign.processes with
  | [.unsupported "ContinuousAssignSymbol:InvalidExpression" _] => true
  | _ => false
end Examples.«system-verilog».sem2.invalid_continuous_assign_e
