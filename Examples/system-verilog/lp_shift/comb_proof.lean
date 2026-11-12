import Examples.«system-verilog».lp_shift.gen
import LeanModels.Sv.CombEqTactic

/-!
# Localparams defined by shifts, read by `sv_structure`

At a symbolic parameter the instantiation computes a shift of an `int` localparam by deciding the sign of the amount
(`evalInt` refuses a negative one) and multiplies by a power of two; `sv_structure` decides the sign by `omega` from the
premises, and places the value in the 32-bit range with the bounds of the power (`2 ^ (K - 1) ≤ 2 ^ 31` from `K ≤ 32`).
A premise that the value is an `int` is part of every statement: `S = N << 1` is `2 * N` only while `2 * N < 2^31`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_shift.gen

namespace Examples.«system-verilog».lp_shift.comb_proof

/-- The ripple adder with an unused `S = N << 1` (the former negative fixture): a combinational design. -/
theorem lp_shl_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 1073741824) : CombDesign (lp_shift.sem N) := by
  sv_structure
  all_goals (intros; omega)

/-- `M = N << 1`, `H = M >> 1`, `Q = (N <<< 2) >>> 2` as a width and select bounds, and `P = (1 << (K - 1)) - 1` by a
parameter amount: a combinational design wherever every value is an `int`. The obligations read `Q` as the arithmetic
shift of the 32-bit value of `N <<< 2` (`canonInt 32 true (N * 4) / 4`), which `canonInt32_of_bounds` removes where
`4 * N` is an `int`. -/
theorem lp_shifts_comb (N K : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 536870912) (hK : 1 ≤ K) (hK' : K ≤ 32) :
    CombDesign (lp_shifts.sem N K) := by
  sv_structure
  -- `Q`'s value is the arithmetic shift of the 32-bit value of `N <<< 2` (`canonInt 32 true`), an `int` here
  all_goals (intros; (try simp (disch := omega) only [canonInt32_of_bounds] at *); omega)

/-- info: 'Examples.«system-verilog».lp_shift.comb_proof.lp_shifts_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_shifts_comb

end Examples.«system-verilog».lp_shift.comb_proof
