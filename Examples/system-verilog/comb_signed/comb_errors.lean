import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.CombProcTactic

/-!
# Signed reads: what stays refused, and why

The tactics read a signed signal as the same bits wherever it is a whole operand of a continuous assign, and a signed
comparison of two signed signals declared with the same dimensions as the two's-complement order (`comb_proof.lean`).
The constructs whose meaning signedness changes and that they do not read yet are refused, each with its reason:

* `neg/sg_asr.sv`: an arithmetic shift right `a >>> 1` (it fills with the sign bit);
* `neg/sg_sel.sv`: a select of a signed signal `a[W-1]` (read through the unsigned twin only as a whole operand);
* `neg/sg_cmp_dims.sv`: a signed comparison of `logic signed [W-1:0] a` and `logic signed [7:0] b` (equal widths at
  `W = 8` only; elsewhere the narrower operand is sign-extended, IEEE 1800-2023 §11.8.2);
* `neg/sg_cmp_self.sv`: a signed comparison as an operand of `&&` (a self-determined position);
* `neg/sg_cmp_opd.sv`: a signed comparison whose operand is an expression `a + b`, not a whole signed signal;
* `neg/sg_cmp_proc.sv`: a signed comparison inside `always_comb`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_signed.comb_errors

load_design_sv2 sg_asr from "Examples/system-verilog/comb_signed/neg/sg_asr.sv.json"
load_design_sv2 sg_sel from "Examples/system-verilog/comb_signed/neg/sg_sel.sv.json"
load_design_sv2 sg_cmp_dims from "Examples/system-verilog/comb_signed/neg/sg_cmp_dims.sv.json"
load_design_sv2 sg_cmp_self from "Examples/system-verilog/comb_signed/neg/sg_cmp_self.sv.json"
load_design_sv2 sg_cmp_opd from "Examples/system-verilog/comb_signed/neg/sg_cmp_opd.sv.json"
load_design_sv2 sg_cmp_proc from "Examples/system-verilog/comb_signed/neg/sg_cmp_proc.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an arithmetic shift right `>>>` (it fills with the sign bit of a signed operand, which the fragment does not model; it has the logical shifts `<<` and unsigned `>>`)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_asr.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a select of the signed signal `a` (outside the v1 fragment: the tactics read a signed signal through its unsigned twin only as a whole operand)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_sel.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison of two signals whose declared packed dimensions differ (the narrower operand would be sign-extended at some parameter point, which the fragment does not model: it reads a signed comparison of two signed signals declared with the same dimensions)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp_dims.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison in a self-determined position (an operand of `&&`, `||`, `!`, a reduction, or the condition of `?:`): the fragment reads a signed comparison as a right-hand side or an operand of the word-level operators, not here
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp_self.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an operand of a signed comparison that is not a whole signed signal (the fragment reads a signed comparison of two signed signals declared with the same dimensions; a select, a constant or an operation as an operand is outside it)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp_opd.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison in an `always_comb` leaf (the procedural route does not read signed comparisons yet; the fragment reads them in a continuous assign)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    ∃ d', (sg_cmp_proc.sem W).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

end Examples.«system-verilog».comb_signed.comb_errors
