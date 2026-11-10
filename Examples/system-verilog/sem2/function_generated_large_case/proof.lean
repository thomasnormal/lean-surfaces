import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.function_generated_large_case.proof

open LeanModels.Sv

load_design_sv2 functionGeneratedLargeCase
  from "Examples/system-verilog/sem2/function_generated_large_case/function_generated_large_case.sv.json"

#guard !functionGeneratedLargeCase.sem.hasUnsupported

-- The differential row runs this flat combinational design through E-core-0;
-- the source envelope itself has no unsupported process or call boundary.
#guard functionGeneratedLargeCase.sem.processes.toList.all fun p =>
  match p with
  | .assign _ _ => true
  | _ => false

end Examples.«system-verilog».sem2.function_generated_large_case.proof
