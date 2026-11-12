import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# Negative tests: shifts in localparams the tactics do not read

* `lp_shl_neg`: `S = 1 << (N - 2)`, a negative amount at `N = 1`, which the instantiation refuses: a statement for every
  `N ≥ 1` is refused, naming the decision; with `N ≥ 2` it is read.
* `lp_shl_wide`: `S = 1 << N` is 0 in an `int` from `N = 32` on (every bit shifted out), but the summary reads the
  definition as `2^N`, which is not an `int` there: refused at `N = 40` and for every `N` without a bound, read for
  `N ≤ 30`.
* `lp_shr_neg`: `S = (N - 16) >> 1` shifts a negative `int` where `N < 16`. IEEE 1800-2023 §11.4.10 fills its 32-bit
  pattern with zeros (`-8 >> 1` is 2147483644), the instantiation divides toward zero (-4, `evalIntExact`; at the default
  point the loader's slang cross-check refuses the design for it), so the two readings part: refused for every `N ≥ 1`,
  read for `N ≥ 16`.
* `localparam_shift` (the clean-room repro, `../localparam_shift.sv`): `sv_structure` reads `BIAS` as a value
  (`comb_proof.lean`); `sv_equations` does not yet, and says so.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».lp_shift.neg

load_design_sv2 lp_shl_neg from "Examples/system-verilog/lp_shift/neg/lp_shl_neg.sv.json"
load_design_sv2 lp_shl_wide from "Examples/system-verilog/lp_shift/neg/lp_shl_wide.sv.json"
load_design_sv2 lp_shr_neg from "Examples/system-verilog/lp_shift/neg/lp_shr_neg.sv.json"
load_design_sv2 localparam_shift from "Examples/system-verilog/lp_shift/localparam_shift.sv.json"

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
        4294967296).toNat` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10, and the left operand of `>>` must not be negative, where the instantiation's reading is not the logical shift)
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

/--
error: sv_structure: the parameter values could not be read off the instantiation environment: at a symbolic parameter the instantiation holds `S` at its exact 32-bit `int` value, `(Int.ofNat
        N -
      16).tdiv
  (2 ^
    Int.toNat
      1)` wrapped to 32 bits at every step, which is the summary's `(Int.ofNat N - 16) % 4294967296 /
  2 ^
    (1 %
        4294967296).toNat` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10, and the left operand of `>>` must not be negative, where the instantiation's reading is not the logical shift)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shr_neg.sem N) := by
  sv_structure

example (N : Nat) (hN : 16 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (lp_shr_neg.sem N) := by
  sv_structure
  all_goals (intros; omega)

/--
error: sv_equations: a right-hand side reads the parameter or localparam `BIAS` as a value (the conversion marker `Resize` of a signed `int` in an unsigned context, IEEE 1800-2023 §11.8.2): `sv_structure` reads it, the equations do not yet (the marker's lowering depends on the constant's own width, `selfWidth2`, which the summary does not carry)
-/
#guard_msgs (whitespace := lax) in
example : localparam_shift.sem 8 ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st → True := by
  obtain ⟨hc, ha⟩ : CombDesign (localparam_shift.sem 8) ∧ Acyclic (localparam_shift.sem 8) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  sv_equations

end Examples.«system-verilog».lp_shift.neg
