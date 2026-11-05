import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».seq_function.proof

open LeanModels.Sv

load_design_sv2 functionEval from "Examples/system-verilog/seq_function/function_call_eval.sv.json"

#guard !functionEval.sem.hasUnsupported
#guard functionEval.sem.processes.toList.any fun p => match p with
  | .assign (.ident "y") (.binary .add (.ident "a") (.lit v)) => v == .ofNat 4 1
  | _ => false

end Examples.«system-verilog».seq_function.proof
