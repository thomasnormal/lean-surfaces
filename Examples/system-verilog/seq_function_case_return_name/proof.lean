import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».seq_function_case_return_name.proof
open LeanModels.Sv
load_design_sv2 functionCaseReturnName from "Examples/system-verilog/seq_function_case_return_name/function_case_return_name.sv.json"
#guard !functionCaseReturnName.sem.hasUnsupported
#guard functionCaseReturnName.sem.processes.toList.any fun p => match p with
  | .assign (.ident "y") (.ternary _ _ (.lit v)) => v == .xVec 4
  | _ => false
#guard (run2 functionCaseReturnName.sem σ_src 256 [
    [("a", .ofNat 4 0), ("y", .xVec 4)],
    [("a", .ofNat 4 1), ("y", .xVec 4)]
  ]).toOption == some [
    [("a", .ofNat 4 0), ("y", .ofNat 4 3)],
    [("a", .ofNat 4 1), ("y", .xVec 4)]
  ]
end Examples.«system-verilog».seq_function_case_return_name.proof
