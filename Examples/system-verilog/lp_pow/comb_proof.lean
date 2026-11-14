import Examples.«system-verilog».lp_pow.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on localparams defined by `**` (`Examples/system-verilog/lp_pow`)

`P = 2 ** L` with `L = $clog2(N + 1)` is a declared width (`logic [P-1:0] w`) and in a generate bound (`i < P - N`);
`T = 3 ** 2` (a 2-state `int`, squashed by the elaborator) is a width and a bound. At a symbolic `N` the parameter stage
decides the sign of each exponent (`omega`, from the `$clog2` facts), and the agreement of the summary with the
instantiation (`hag`) places `2 ^ clog2 (N + 1)` in the 32-bit range from a NUMERIC bound of the `$clog2` atom
(`clog2_le_of_le_two_pow`: `clog2 (N + 1) ≤ 28` from `N < 2^28`) and the bound of the power it gives (`addPowFacts`).
The obligations hold the power `2 ^ clog2 (N + 1)` as an atom; the two facts about it a player needs are
`le_two_pow_clog2_int` (`N + 1 ≤ 2 ^ clog2 (N + 1)`) and `two_pow_clog2_lt_int` (`2 ^ clog2 (N + 1) < 2 (N + 1)`).

The range premise `N < 2^28` keeps `P` an `int` (`2 ^ clog2 (N + 1)` is at most `2N + 1`), and the generate fuel bound
(`4 * N + 60` iterations) holds of `P - N`.

Build: `lake build Examples.«system-verilog».lp_pow.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_pow.gen

namespace Examples.«system-verilog».lp_pow.comb_proof

/-- The structure of `lp_pow`, at every `N` below `2^28`. -/
theorem lp_pow_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 268435456) : CombDesign (lp_pow.sem N) := by
  sv_structure
  all_goals
    intros
    have h1 := le_two_pow_clog2_int (N + 1)
    have h2 := two_pow_clog2_lt_int (N + 1) (by omega)
    omega

/--
info: 'Examples.«system-verilog».lp_pow.comb_proof.lp_pow_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lp_pow_comb

end Examples.«system-verilog».lp_pow.comb_proof
