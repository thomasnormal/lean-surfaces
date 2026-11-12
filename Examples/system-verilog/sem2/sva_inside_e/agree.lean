import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.sva_inside_e
open LeanModels.Sv
load_design_sv2 svaInsideE from "Examples/system-verilog/sem2/sva_inside_e/sva_inside_e.sv.json"
#guard match svaInsideE.pdesign.properties with
  | [{ ast := some { property := .always (.atom (.expr (.binary .ceq (.ident "a") (.lit (.ofNat 4 1))))), .. }, .. }] => true
  | _ => false
end Examples.«system-verilog».sem2.sva_inside_e
