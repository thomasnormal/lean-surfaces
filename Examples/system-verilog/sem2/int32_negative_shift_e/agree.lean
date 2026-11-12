import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.int32_negative_shift_e
open LeanModels.Sv
load_design_sv2 int32NegativeShiftE from
  "Examples/system-verilog/sem2/int32_negative_shift_e/int32_negative_shift_e.sv.json"
#guard match int32NegativeShiftE.pdesign.instantiate2 [] with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "left_zero") (.lit l), .assign (.ident "right_arith") (.lit r)] =>
        l == LVec.ofNat 32 0 && r == LVec.ofNat 32 0x7ffffffc
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.int32_negative_shift_e
