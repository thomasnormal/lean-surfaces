import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.RunEArray

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

open LeanModels.Sv.Kernel

private def eInputs : List SvState :=
  [[("a", .ofNat 65 0), ("y", .xVec 65)],
   [("a", .ofNat 65 1), ("y", .xVec 65)],
   [("a", .ofNat 65 ((2 : Nat) ^ 65 - 1)), ("y", .xVec 65)]]

private def eExpected : List SvState :=
  [[("a", .ofNat 65 0), ("y", .ofNat 65 ((2 : Nat) ^ 65 - 1))],
   [("a", .ofNat 65 1), ("y", .ofNat 65 ((2 : Nat) ^ 65 - 2))],
   [("a", .ofNat 65 ((2 : Nat) ^ 65 - 1)), ("y", .ofNat 65 0)]]

#guard match runE0Array (Elab.ofDesign2 functionGeneratedLargeCase.sem)
    σ_src 1000 eInputs with
  | .ok rows => rows.map (fun row : E0Row => (Elab.ofDesign2 functionGeneratedLargeCase.sem).view row.2.store) == eExpected
  | _ => false

end Examples.«system-verilog».sem2.function_generated_large_case.proof
