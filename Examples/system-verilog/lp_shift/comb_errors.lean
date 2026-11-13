import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# Shifts in localparams at the edges of the reading: what the tactics refuse, and what they read

The instantiation's shifts of an `int` follow IEEE 1800-2023 §11.4.10 (`evalIntExactRec`, master 853147a63): the amount
is unsigned, so a negative one shifts every bit out (0), and `>>` shifts the 32-bit pattern with zeros. The summary reads
the same (`CE.eval`), except where its unbounded value is no `int`, and except for one case of the instantiation.

* `lp_shl_neg`: `S = 1 << (N - 2)`, a negative amount at `N = 1`, where `S` is 0 and the summary's value `2^(2^32-1)` is
  no `int`: a statement for every `N ≥ 1` is refused, naming the decision the instantiation takes on the amount's sign;
  with `N ≥ 2` it is read.
* `lp_shl_wide`: `S = 1 << N` is 0 in an `int` from `N = 32` on (every bit shifted out), but the summary reads the
  definition as `2^N`, which is not an `int` there: refused at `N = 40` and for every `N` without a bound, read for
  `N ≤ 30`.
* `lp_shr_neg`: `S = (N - 16) >> 1` shifts a negative `int` where `N < 16`; both readings shift its 32-bit pattern with
  zeros (`-8 >> 1` is 2147483644; local Icarus Verilog 12.0 and Verilator 5.042 print it at `N = 8`, and 2147483640 at
  `N = 1`, provisional rows): read for every `N ≥ 1` (`lp_shr_neg_comb`; until master 853147a63 the instantiation divided
  toward zero, -4, and this was a refusal).
* `lp_ashr_neg`: `S = (N - 16) >>> (N - 9)`, a negative `int` shifted by a negative amount where `N < 9`: -1 under
  §11.4.10 (the sign bit fills every position; the local simulators print -1 at `N = 8`), 0 in the instantiation, which
  gives 0 for every negative amount. The readings part, and the tactics refuse there, naming the `>>>` (a finding for the
  semantics owners); with the operand or the amount non-negative (`N ≥ 9`) it is read.
* `localparam_shift` (the clean-room repro, `../localparam_shift.sv`): `sv_structure` and `sv_equations` read `BIAS` as a
  value (`comb_proof.lean`, `localparam_shift_correct`); it is no longer a negative test.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».lp_shift.neg

load_design_sv2 lp_shl_neg from "Examples/system-verilog/lp_shift/neg/lp_shl_neg.sv.json"
load_design_sv2 lp_shl_wide from "Examples/system-verilog/lp_shift/neg/lp_shl_wide.sv.json"
load_design_sv2 lp_shr_neg from "Examples/system-verilog/lp_shift/neg/lp_shr_neg.sv.json"
load_design_sv2 lp_ashr_neg from "Examples/system-verilog/lp_shift/neg/lp_ashr_neg.sv.json"

-- The instantiation's values at `N = 8`: `(N - 16) >> 1` is the pattern of -8 shifted with a zero, 2147483644 (IEEE
-- 1800-2023 §11.4.10; the local simulators agree); `(N - 16) >>> (N - 9)` is 0, where IEEE and the local simulators give -1.
#guard ((lp_shr_neg.pdesign.paramEnv2 [8]).toOption.map fun e => e.intVal? "S") == some (some 2147483644)
#guard ((lp_ashr_neg.pdesign.paramEnv2 [8]).toOption.map fun e => e.intVal? "S") == some (some 0)

/--
error: sv_structure: the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter: the instantiation decides `Int.ofNat
      N -
    2 <
  0` at a symbolic parameter (the sign test of `$clog2`'s argument or of a shift amount, a divisor's test for zero, ...; every value in it is wrapped to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not decide it from the hypotheses in context (a theorem at a symbolic parameter needs premises that fix the decision and keep the values in it in range, e.g. `N < 2147483647` for `$clog2(N + 1)`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shl_neg.sem N) := by
  sv_structure

example (N : Nat) (hN : 2 ≤ N) (hN' : N ≤ 32) : CombDesign (lp_shl_neg.sem N) := by
  sv_structure
  all_goals (intros; omega)

/--
error: sv_structure: the parameter values could not be read off the instantiation environment: at a symbolic parameter the instantiation holds `S` at its exact 32-bit `int` value, `1 *
  2 ^
    (Int.ofNat
        N).toNat` wrapped to 32 bits at every step, which is the summary's `1 *
  2 ^
    (Int.ofNat N %
        4294967296).toNat` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shl_wide.sem N) := by
  sv_structure

/--
error: sv_structure: the parameter values could not be read off the instantiation environment: the localparam `S` is the 32-bit `int` 0 in the instantiation, and the summary's value of its definition is 1099511627776: the value of the definition `1 << N` is 1099511627776 at these parameters, outside the signed 32-bit range [-2147483648, 2147483647]: the instantiation's value is its 32-bit wrap 0 (IEEE 1800-2023 §11.4, §11.6.1, §11.8.1: every result of an `int` expression is 32 bits wide), and the summary reads the unbounded value, so a localparam whose value leaves the range is outside the fragment
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (lp_shl_wide.sem 40) := by
  sv_structure

example (N : Nat) (hN' : N ≤ 30) : CombDesign (lp_shl_wide.sem N) := by
  sv_structure
  all_goals (intros; omega)

/-- `(N - 16) >> 1` for every `N ≥ 1`: the instantiation's value of `S` is `if N - 16 < 0 then N - 16 + 2^32 else N - 16`
(the 32-bit pattern) divided by 2, the summary's `(N - 16) % 2^32 / 2`, which `sv_structure` shows to be the same number
(`shr_pattern_of_bounds`). -/
theorem lp_shr_neg_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shr_neg.sem N) := by
  sv_structure

/-- info: 'Examples.«system-verilog».lp_shift.neg.lp_shr_neg_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_shr_neg_comb

example (N : Nat) (hN : 16 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shr_neg.sem N) := by
  sv_structure
  all_goals (intros; omega)

-- `>>>` of a negative `int` by a negative amount (`N ≤ 8`): -1 under IEEE 1800-2023 §11.4.10, 0 in the instantiation
/--
error: sv_structure: the parameter values could not be read off the instantiation environment: at a symbolic parameter the instantiation holds `S` at its exact 32-bit `int` value, `0` wrapped to 32 bits at every step, which is the summary's `canonInt
    32 true (Int.ofNat N - 16) /
  2 ^
    ((Int.ofNat N - 9) %
        4294967296).toNat` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10) (the definition has a `>>>`: of a negative `int` by a negative amount it is -1 under IEEE 1800-2023 §11.4.10, every bit shifted out and the sign bit filled in, and 0 in the instantiation, `evalIntExactRec`; a statement needs premises that keep its amount or its operand non-negative; the semantics owners have the finding)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hN' : N ≤ 8) : CombDesign (lp_ashr_neg.sem N) := by
  sv_structure

/-- A non-negative amount (`9 ≤ N`), the operand negative below `N = 16`: the arithmetic shift rounds down in both
readings. -/
example (N : Nat) (hN : 9 ≤ N) (hN' : N < 16) : CombDesign (lp_ashr_neg.sem N) := by
  sv_structure

example (N : Nat) (hN : 16 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_ashr_neg.sem N) := by
  sv_structure

end Examples.«system-verilog».lp_shift.neg
