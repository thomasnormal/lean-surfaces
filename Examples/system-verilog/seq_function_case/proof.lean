import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function_case.proof

open LeanModels.Sv

load_design_sv2 functionCase from "Examples/system-verilog/seq_function_case/function_case_eval.sv.json"

#guard !functionCase.sem.hasUnsupported
#guard functionCase.sem.processes.toList.any fun p => match p with
  | .assign (.ident "y") (.ternary _ _ _) => true
  | _ => false

#guard (run2 functionCase.sem σ_src 256 [
    [("a", .ofNat 4 0), ("y", .xVec 4)],
    [("a", .ofNat 4 1), ("y", .xVec 4)],
    [("a", .ofNat 4 12), ("y", .xVec 4)]
  ]).toOption == some [
    [("a", .ofNat 4 0), ("y", .ofNat 4 3)],
    [("a", .ofNat 4 1), ("y", .ofNat 4 12)],
    [("a", .ofNat 4 12), ("y", .ofNat 4 12)]
  ]

end Examples.«system-verilog».seq_function_case.proof
