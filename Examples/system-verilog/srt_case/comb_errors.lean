import Examples.«system-verilog».srt_case.gen
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».srt_case.gen
namespace Examples.«system-verilog».srt_case.comb_errors
example (N : Nat) (_hN : 1 ≤ N) : ∃ d', (srt_case.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure
  all_goals (intros; omega)

example (W : Nat) (hW : 1 ≤ W) : ∃ d', (shift_param.sem W).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure
  all_goals (intros; omega)
end Examples.«system-verilog».srt_case.comb_errors
