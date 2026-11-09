import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.function_generate_case.proof

open LeanModels.Sv

load_design_sv2 functionGenerateCase
  from "Examples/system-verilog/sem2/function_generate_case/function_generate_case.sv.json"

#guard !functionGenerateCase.sem.hasUnsupported
#guard (run2 functionGenerateCase.sem σ_src 512 [
    [("a", .ofNat 20 0), ("y", .xVec 20)],
    [("a", .ofNat 20 1), ("y", .xVec 20)],
    [("a", .ofNat 20 74565), ("y", .xVec 20)]
  ]).toOption == some [
    [("a", .ofNat 20 0), ("y", .ofNat 20 1048575)],
    [("a", .ofNat 20 1), ("y", .ofNat 20 1048544)],
    [("a", .ofNat 20 74565), ("y", .ofNat 20 0)]
  ]

end Examples.«system-verilog».sem2.function_generate_case.proof
