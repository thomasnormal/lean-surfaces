import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemCycle

/-! Clean-room F4 memory witness: a parameter-dependent unpacked array
remains source-shaped in the memory E route. Fixed cell selections emitted as
identifiers by the frontend are retained as array-cell operations at the
memory boundary; no generate or storage flattening is performed. -/

namespace Examples.«system-verilog».sem2.unpacked_generate_array.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 unpackedGenerateArray from
  "Examples/system-verilog/sem2/unpacked_generate_array/unpacked_generate_array.sv.json"

private def memD : MemDesign2 :=
  unpackedGenerateArray.pdesign.instantiateMemD2 [8, 2]

#guard memD.memDecls.length == 1
#guard match memD.processes with
  | [.assignL (.arrayElem "stage" [.int 0]) (.ident "x"),
      .assignL (.arrayElem "stage" [.int 1]) (.arrayElem "stage" [.int 0]),
      .assign "y" (.arrayElem "stage" [.int 1])] => true
  | _ => false

#guard match runMem2 memD 64
    [[("x", LVec.lit "00001111")], [("x", LVec.lit "10100101")]] with
  | .ok [s0, s1] =>
      SvState.lookup s0 "y" == some (LVec.lit "00001111") &&
      SvState.lookup s1 "y" == some (LVec.lit "10100101")
  | _ => false

end Examples.«system-verilog».sem2.unpacked_generate_array.agree
