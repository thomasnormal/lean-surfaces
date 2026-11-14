import Examples.«system-verilog».gen_if.gen
import LeanModels.Sv.CombViewTactic

/-!
# Generate conditions outside the guard fragment, and a guard's 32-bit obligation (`Examples/system-verilog/gen_if/neg`)

* `gen_if_bit`: `(i & 1) == 0` tests a bit of the genvar; a guard is a comparison of affine forms, so the condition is
  refused, naming the fragment.
* `gen_if_wide`: `i + N * 1024 > 0` is read, but the instantiation evaluates its operands at the signed 32-bit type
  (`N * 1024` wraps at `N = 2097152`), so the value of every subterm is owed in that range at every iteration: up to
  `i + N * 1024 < 1025 * N`. Under `N < 2147483647` alone that obligation is false (`omega` finds `N = 2097151`,
  `i = 1024`); under `N < 2000000` it holds and the design is proved.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_if.gen

namespace Examples.«system-verilog».gen_if.comb_errors

/--
error: sv_structure: outside the supported fragment — conditional generate inside a generate loop: the condition is outside the v1 fragment (a signed comparison `s< s<= s> s>=`, or `==`, `!=`, of two affine forms in the parameters and the enclosing genvars: integer literals, `+`, `-`, `*` by a constant)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_if_bit.sem N) := by
  sv_structure

/-- With a bound that keeps `i + N * 1024` an `int`, the design is read and its obligations close. -/
theorem gen_if_wide_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2000000) : CombDesign (gen_if_wide.sem N) := by
  sv_structure
  all_goals (intros; omega)

end Examples.«system-verilog».gen_if.comb_errors
