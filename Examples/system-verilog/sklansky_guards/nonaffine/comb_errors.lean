import Examples.«system-verilog».sklansky_guards.nonaffine.gen
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».sklansky_guards.nonaffine.gen
namespace Examples.«system-verilog».sklansky_guards.nonaffine.comb_errors
/--
error: sv_structure: outside the supported fragment — site `g_bit#0`: read `a[…]` has a non-affine (dynamic or nonlinear) index
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (nonaffine.sem N) := by
  sv_structure
end Examples.«system-verilog».sklansky_guards.nonaffine.comb_errors
