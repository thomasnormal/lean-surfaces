import Examples.«system-verilog».gen_tri.gen
import LeanModels.Sv.CombViewTactic

/-!
# A generate bound that is not affine (`Examples/system-verilog/gen_tri/neg`)

`gen_sq_bound`: the bound `j < i * i + 1` multiplies two genvars; the summary reads a bound only as an affine form in the
parameters and the enclosing genvars, and refuses this one.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_tri.gen

namespace Examples.«system-verilog».gen_tri.comb_errors

/--
error: sv_structure: outside the supported fragment — generate bound is not affine in the parameters and the enclosing genvars
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (gen_sq_bound.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_tri.comb_errors
