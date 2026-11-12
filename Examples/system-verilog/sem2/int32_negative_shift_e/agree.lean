import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.int32_negative_shift_e
open LeanModels.Sv
load_design_sv2 int32NegativeShiftE from
  "Examples/system-verilog/sem2/int32_negative_shift_e/int32_negative_shift_e.sv.json"
def row (n : Int) (lp ap : Nat) : Bool :=
  match int32NegativeShiftE.pdesign.instantiate2 [n] with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "left_zero") (.lit l),
       .assign (.ident "logical_right") (.lit r),
       .assign (.ident "arithmetic_right") (.lit a),
       .assign (.ident "logical_param") (.lit p),
       .assign (.ident "arithmetic_param") (.lit q)] =>
        l == LVec.ofNat 32 0 && r == LVec.ofNat 32 0x7ffffffc &&
        a == LVec.ofInt 32 (-4) && p == LVec.ofNat 32 lp &&
        q == LVec.ofInt 32 (-(ap : Int))
    | _ => false
  | _ => false
#guard row 8 0x7ffffffc 4
#guard row 16 0x7ffffff8 8
end Examples.«system-verilog».sem2.int32_negative_shift_e
