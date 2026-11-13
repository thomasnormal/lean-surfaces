import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.int32_ashr_huge_e
open LeanModels.Sv
load_design_sv2 int32AshrHugeE from
  "Examples/system-verilog/sem2/int32_ashr_huge_e/int32_ashr_huge_e.sv.json"
def row (n : Int) : Bool :=
  match int32AshrHugeE.pdesign.instantiate2 [n] with
  | .ok d => match d.processes.toList with
    | [.assign (.ident "negative_amount") (.lit a),
       .assign (.ident "width_amount") (.lit b),
       .assign (.ident "one_amount") (.lit c),
       .assign (.ident "parameter_amount") (.lit d)] =>
        a == LVec.ofInt 32 (-1) && b == LVec.ofInt 32 (-1) &&
        c == LVec.ofInt 32 (-1) && d == LVec.ofInt 32 (-1)
    | _ => false
  | _ => false
#guard row 8
#guard row 16
end Examples.«system-verilog».sem2.int32_ashr_huge_e
