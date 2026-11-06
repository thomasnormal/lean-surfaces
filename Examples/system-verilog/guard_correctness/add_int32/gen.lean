import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».guard_correctness.add_int32.gen
open LeanModels.Sv
load_design_sv2 add_int32 from "Examples/system-verilog/guard_correctness/add_int32/add_int32.sv.json"
#guard add_int32.pdesign.int32Agrees [16]
#guard add_int32.pdesign.int32Agrees [5]

private def hasInvertedSum (m : Design2) : Bool :=
  m.processes.toList.any fun p => match p with
    | .assign (.ident "s") (.unary .bnot (.ident "sr")) => true
    | _ => false

private def hasPlainSum (m : Design2) : Bool :=
  m.processes.toList.any fun p => match p with
    | .assign (.ident "s") (.ident "sr") => true
    | _ => false

-- The semantic family uses exact signed-32 `int` arithmetic at every point:
-- `M` wraps negative at N=5, selecting the inversion arm, while N=16 keeps it.
#guard hasPlainSum (add_int32.pdesign.instantiateD2 [16])
#guard hasInvertedSum (add_int32.pdesign.instantiateD2 [5])
end Examples.«system-verilog».guard_correctness.add_int32.gen
