import Examples.«system-verilog».lp_pow.gen
import LeanModels.Sv.CombViewTactic

/-!
# `**` in localparams at the edges of the reading

* `lp_pow_neg`: `Z = 2 ** (N - 5)` has a negative exponent where `N < 5`, which the instantiation refuses
  (`evalIntExactRec`); a statement for every `N ≥ 1` is refused naming the decision on the exponent's sign, and with
  `N ≥ 5` it is read.
* `lp_pow_wide`: `Z = 2 ** N` is no `int` from `N = 31` on (the instantiation wraps it, the summary's `2 ^ N` is
  unbounded): refused without a bound of `N`, read for `N ≤ 30`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_pow.gen

namespace Examples.«system-verilog».lp_pow.comb_errors

/--
error: sv_structure: the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter: the instantiation decides `Int.ofNat
      N -
    5 <
  0` at a symbolic parameter (the sign test of `$clog2`'s argument or of a shift amount, a divisor's test for zero, ...; every value in it is wrapped to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not decide it from the hypotheses in context (a theorem at a symbolic parameter needs premises that fix the decision and keep the values in it in range, e.g. `N < 2147483647` for `$clog2(N + 1)`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (lp_pow_neg.sem N) := by
  sv_structure

theorem lp_pow_neg_comb (N : Nat) (hN : 5 ≤ N) (hR : (N : Int) < 30) : CombDesign (lp_pow_neg.sem N) := by
  sv_structure
  all_goals (intros; omega)

/--
error: sv_structure: the parameter values could not be read off the instantiation environment: at a symbolic parameter the instantiation holds `Z` at its exact 32-bit `int` value, `2 ^
  (Int.ofNat
      N).toNat` wrapped to 32 bits at every step, which is the summary's `2 ^
  (Int.ofNat
      N).toNat` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (lp_pow_wide.sem N) := by
  sv_structure

theorem lp_pow_wide_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 31) : CombDesign (lp_pow_wide.sem N) := by
  sv_structure
  all_goals (intros; omega)

/--
info: 'Examples.«system-verilog».lp_pow.comb_errors.lp_pow_wide_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lp_pow_wide_comb

end Examples.«system-verilog».lp_pow.comb_errors
