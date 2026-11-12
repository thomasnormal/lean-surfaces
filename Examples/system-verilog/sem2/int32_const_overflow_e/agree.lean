import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.int32_const_overflow_e
open LeanModels.Sv
load_design_sv2 int32ConstOverflowE from
  "Examples/system-verilog/sem2/int32_const_overflow_e/int32_const_overflow_e.sv.json"
#guard match (int32ConstOverflowE.pdesign.instantiate2 [10000]) with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "k_out") (.lit k), .assign (.ident "s_out") (.lit s),
       .assign (.ident "a_out") (.lit a), .assign (.ident "u_out") (.lit u)] =>
        k == LVec.ofNat 32 1410 && s == LVec.ofNat 32 0 &&
        a == LVec.ofInt 32 (-649) && u == LVec.ofInt 32 (-2147483648)
    | _ => false
  | _ => false
#guard match (int32ConstOverflowE.pdesign.instantiate2 [8]) with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "k_out") (.lit k), .assign (.ident "s_out") (.lit s),
       .assign (.ident "a_out") (.lit a), .assign (.ident "u_out") (.lit u)] =>
        k == LVec.ofNat 32 8 && s == LVec.ofNat 32 0 &&
        a == LVec.ofInt 32 (-641) && u == LVec.ofInt 32 (-2147483648)
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.int32_const_overflow_e
