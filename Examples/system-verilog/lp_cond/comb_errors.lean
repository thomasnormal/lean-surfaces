import Examples.«system-verilog».lp_cond.gen
import LeanModels.Sv.CombViewTactic

/-!
# Comparisons in localparams outside the condition of `?:`

`lp_cmp_num`: `C = (N > 2) + 1` uses a comparison as a number (the envelope converts its 1-bit result to the width of
the sum, `Resize`); the summary reads a comparison only as the condition of `?:` (`CE.cmpOk`), and refuses it naming the
conversion.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_cond.gen

namespace Examples.«system-verilog».lp_cond.comb_errors

/--
error: sv_structure: outside the supported fragment — localparam `C`: an operand converted to the width of its expression (the envelope's `Resize`: a comparison or another 1-bit value used as a number, `(N > 2) + 1`, or a sized operand) is outside the v1 fragment (a comparison is read only as the condition of `?:`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (lp_cmp_num.sem N) := by
  sv_structure

end Examples.«system-verilog».lp_cond.comb_errors
