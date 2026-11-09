import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.CombProcTactic

/-!
# Signed reads: what stays refused, and why

The tactics read a signed signal as the same bits wherever it is a whole operand of a continuous assign, and a signed
comparison of two signed signals declared with the same dimensions as the two's-complement order (`comb_proof.lean`).
The constructs whose meaning signedness changes and that they do not read yet are refused, each with its reason:

* `neg/sg_sel_shift.sv`: a part select of a signed signal as the operand of a shift;
* `neg/sg_sel_proc.sv`: a bit select of a signed signal inside `always_comb`;
* `neg/sg_cmp_dims.sv`: a signed comparison of `logic signed [W-1:0] a` and `logic signed [7:0] b` (equal widths at
  `W = 8` only; elsewhere the narrower operand is sign-extended, IEEE 1800-2023 §11.8.2);
* `neg/sg_cmp_self.sv`: a signed comparison as an operand of `&&` (a self-determined position);
* `neg/sg_cmp_opd.sv`: a signed comparison whose operand is an expression `a + b`, not a whole signed signal;
* `neg/sg_cmp_proc.sv`: a signed comparison inside `always_comb`;
* `neg/sg_asr_amt.sv`: an arithmetic shift right by a signed amount `a >>> b`;
* `neg/sg_asr_self.sv`: an arithmetic shift right as an operand of `&&`;
* `neg/sg_asr_wide.sv`: an arithmetic shift right into a target wider than its operand (sign extension before the shift);
* `neg/asr_unsigned.sv`: `>>>` of an unsigned operand.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_signed.comb_errors

load_design_sv2 sg_sel_shift from "Examples/system-verilog/comb_signed/neg/sg_sel_shift.sv.json"
load_design_sv2 sg_sel_proc from "Examples/system-verilog/comb_signed/neg/sg_sel_proc.sv.json"
load_design_sv2 sg_cmp_dims from "Examples/system-verilog/comb_signed/neg/sg_cmp_dims.sv.json"
load_design_sv2 sg_cmp_self from "Examples/system-verilog/comb_signed/neg/sg_cmp_self.sv.json"
load_design_sv2 sg_cmp_opd from "Examples/system-verilog/comb_signed/neg/sg_cmp_opd.sv.json"
load_design_sv2 sg_cmp_proc from "Examples/system-verilog/comb_signed/neg/sg_cmp_proc.sv.json"
load_design_sv2 sg_asr_amt from "Examples/system-verilog/comb_signed/neg/sg_asr_amt.sv.json"
load_design_sv2 sg_asr_self from "Examples/system-verilog/comb_signed/neg/sg_asr_self.sv.json"
load_design_sv2 sg_asr_wide from "Examples/system-verilog/comb_signed/neg/sg_asr_wide.sv.json"
load_design_sv2 asr_unsigned from "Examples/system-verilog/comb_signed/neg/asr_unsigned.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a select of the signed signal `a` in a position the tactics do not read through the unsigned twin (they read a select of a signed signal, an unsigned value, IEEE 1800-2023 §11.8.1, where it is an operand of a continuous assign; a shift operand, an index and an `always_comb` body are outside the fragment)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_sel_shift.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a select of the signed signal `a` in a position the tactics do not read through the unsigned twin (they read a select of a signed signal, an unsigned value, IEEE 1800-2023 §11.8.1, where it is an operand of a continuous assign; a shift operand, an index and an `always_comb` body are outside the fragment)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    ∃ d', (sg_sel_proc.sem W).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
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

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed shift amount `b` (outside the fragment: it reads the amount of a shift as an unsigned signal access, sized literal or constant; IEEE 1800-2023 §11.4.10 treats the amount as unsigned, so write it into an unsigned signal first)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_asr_amt.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an arithmetic shift right `>>>` in a self-determined position (an operand of `&&`, `||`, `!`, a reduction, a comparison or the condition of `?:`): the fragment reads `>>>` of a signed operand as a right-hand side or an operand of the word-level operators, not here
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_asr_self.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed operand `a` of a shift, sign-extended to a wider context (outside the fragment: it reads a shift of a signed signal into a target of the signal's own width)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_asr_wide.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `u>>>` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the four signed comparisons of two signed signals, the run-time shifts `<<` and `>>`, the arithmetic shift `>>>` of a signed operand and the logical `&&`, `||`; `<<<`, `>>>` of an unsigned operand, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (asr_unsigned.sem W) := by
  sv_structure

end Examples.«system-verilog».comb_signed.comb_errors
