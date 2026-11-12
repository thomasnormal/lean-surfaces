import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.int32_const_add_unary_e
open LeanModels.Sv
load_design_sv2 int32ConstAddUnaryE from
  "Examples/system-verilog/sem2/int32_const_add_unary_e/int32_const_add_unary_e.sv.json"
private def row (m : PDesign) (n : Int) : Bool :=
  match m.instantiate2 [n] with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "add_mod_out") (.lit a),
       .assign (.ident "unary_min_out") (.lit u)] =>
        a.toInt? == some (-47) && u.toInt? == some (-2147483648)
    | _ => false
  | _ => false
#guard row int32ConstAddUnaryE.pdesign 2
#guard match int32ConstAddUnaryE.pdesign.instantiate2 [3] with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "add_mod_out") (.lit a), .assign (.ident "unary_min_out") (.lit u)] =>
        a.toInt? == some (-46) && u.toInt? == some (-2147483648)
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.int32_const_add_unary_e
