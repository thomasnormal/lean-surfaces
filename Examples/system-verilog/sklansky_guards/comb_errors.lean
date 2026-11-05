import Examples.«system-verilog».sklansky_guards.gen
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».sklansky_guards.gen
namespace Examples.«system-verilog».sklansky_guards.comb_errors
/--
error: sv_structure: outside the supported fragment — conditional generate inside a generate loop: GuardEval obligation (the selected arm depends on reached genvar values)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (guarded.sem N) := by
  sv_structure
end Examples.«system-verilog».sklansky_guards.comb_errors
