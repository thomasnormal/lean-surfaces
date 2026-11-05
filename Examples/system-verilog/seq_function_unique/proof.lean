import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function_unique.proof

open LeanModels.Sv

load_design_sv2 functionUnique from "Examples/system-verilog/seq_function_unique/function_unique_case_eval.sv.json"

#guard !functionUnique.sem.hasUnsupported
#guard functionUnique.sem.processes.toList.any fun p => match p with
  | .assign (.ident "y") (.ternary _ _ _) => true
  | _ => false

#guard (run2 functionUnique.sem σ_src 256 [
    [("a", .ofNat 4 0), ("y", .xVec 4)],
    [("a", .ofNat 4 1), ("y", .xVec 4)],
    [("a", .ofNat 4 12), ("y", .xVec 4)]
  ]).toOption == some [
    [("a", .ofNat 4 0), ("y", .ofNat 4 3)],
    [("a", .ofNat 4 1), ("y", .ofNat 4 4)],
    [("a", .ofNat 4 12), ("y", .ofNat 4 12)]
  ]

end Examples.«system-verilog».seq_function_unique.proof
